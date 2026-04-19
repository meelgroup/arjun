/*
 Arjun - AIG Rewriting System

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#include "aig_rewrite.h"
#include "time_mem.h"
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <cassert>
#include <functional>
#include <unordered_set>

using namespace ArjunNS;
using std::vector;
using std::map;
using std::set;
using std::cout;
using std::endl;


void AIGRewriteStats::print(int verb) const {
    if (verb < 1) return;
    cout << "c o [aig-rewrite] nodes: " << nodes_before << " -> " << nodes_after
         << " (" << std::fixed << std::setprecision(1)
         << (nodes_before > 0 ? (1.0 - (double)nodes_after / nodes_before) * 100.0 : 0.0) << "% reduction)"
         << "  passes: " << total_passes
         << "  const_prop: " << const_prop
         << "  complement: " << complement_elim
         << "  idempotent: " << idempotent_elim
         << "  absorption: " << absorption
         << "  distrib: " << and_or_distrib
         << "  hash_hits: " << structural_hash_hits
         << endl;
}

void AIGRewriteStats::clear() { *this = AIGRewriteStats(); }

// ========== Helper functions ==========

bool AIGRewriter::is_complement(const aig_ptr& a, const aig_ptr& b) const {
    if (!a || !b) return false;
    // Literal complement: same var, opposite neg
    if (a->type == AIGT::t_lit && b->type == AIGT::t_lit)
        return a->var == b->var && a->neg != b->neg;
    // Structural complement: a = NOT(b) or b = NOT(a)
    // NOT(x) is AND(x, x, neg=true)
    if (a->type == AIGT::t_and && a->neg && a->l == a->r && a->l == b) return true;
    if (b->type == AIGT::t_and && b->neg && b->l == b->r && b->l == a) return true;
    // Also check: a->neg != b->neg and same structure otherwise
    if (a->type == AIGT::t_and && b->type == AIGT::t_and &&
        a->l == b->l && a->r == b->r && a->neg != b->neg) return true;
    return false;
}

aig_ptr AIGRewriter::strip_not(const aig_ptr& a) const {
    if (!a) return nullptr;
    if (a->type == AIGT::t_and && a->neg && a->l == a->r) return a->l;
    return a;
}

bool AIGRewriter::is_or(const aig_ptr& a) const {
    // OR(a,b) = AND(NOT(a), NOT(b), neg=true) where l != r
    // NOT(x) = AND(x, x, neg=true) where l == r -- this is NOT an OR
    return a && a->type == AIGT::t_and && a->neg && a->l != a->r;
}

size_t AIGRewriter::count_nodes(const aig_ptr& aig) const {
    return AIG::count_aig_nodes(aig);
}

// Collect all AND-children by flattening nested AND nodes
void AIGRewriter::collect_and_children(const aig_ptr& aig, vector<aig_ptr>& children, bool neg) {
    if (!aig) return;
    if (aig->type == AIGT::t_and && !aig->neg && !neg) {
        // Unnegated AND: flatten
        collect_and_children(aig->l, children, false);
        collect_and_children(aig->r, children, false);
    } else if (neg) {
        children.push_back(AIG::new_not(aig));
    } else {
        children.push_back(aig);
    }
}

// Collect all OR-children by flattening nested OR nodes
// OR(a,b) = AND(NOT(a), NOT(b), neg=true)
void AIGRewriter::collect_or_children(const aig_ptr& aig, vector<aig_ptr>& children, bool neg) {
    if (!aig) return;
    if (is_or(aig) && !neg) {
        // This is OR(NOT(l), NOT(r)) - flatten
        // The actual OR children are NOT(l) and NOT(r)
        collect_or_children(AIG::new_not(aig->l), children, false);
        collect_or_children(AIG::new_not(aig->r), children, false);
    } else if (neg) {
        children.push_back(AIG::new_not(aig));
    } else {
        children.push_back(aig);
    }
}

aig_ptr AIGRewriter::build_and_tree(vector<aig_ptr>& children) {
    if (children.empty()) return aig_mng.new_const(true);
    if (children.size() == 1) return children[0];
    // Build balanced tree for better sharing
    while (children.size() > 1) {
        vector<aig_ptr> next;
        for (size_t i = 0; i + 1 < children.size(); i += 2) {
            next.push_back(AIG::new_and(children[i], children[i+1]));
        }
        if (children.size() % 2 == 1) {
            next.push_back(children.back());
        }
        children = std::move(next);
    }
    return children[0];
}

aig_ptr AIGRewriter::build_or_tree(vector<aig_ptr>& children) {
    if (children.empty()) return aig_mng.new_const(false);
    if (children.size() == 1) return children[0];
    while (children.size() > 1) {
        vector<aig_ptr> next;
        for (size_t i = 0; i + 1 < children.size(); i += 2) {
            next.push_back(AIG::new_or(children[i], children[i+1]));
        }
        if (children.size() % 2 == 1) {
            next.push_back(children.back());
        }
        children = std::move(next);
    }
    return children[0];
}

aig_ptr AIGRewriter::make_canonical(AIGT type, bool neg, const aig_ptr& l, const aig_ptr& r) {
    auto ll = l;
    auto rr = r;
    if (ll < rr) std::swap(ll, rr);
    StructKey key{neg, ll.get(), rr.get()};
    auto it = struct_hash.find(key);
    if (it != struct_hash.end()) {
        stats.structural_hash_hits++;
        return it->second;
    }
    auto node = std::make_shared<AIG>();
    node->type = type;
    node->neg = neg;
    node->l = ll;
    node->r = rr;
    struct_hash.emplace(key, node);
    return node;
}

// ========== Pass 1: Bottom-up simplification ==========

aig_ptr AIGRewriter::simplify_pass(const aig_ptr& aig, AigPtrMap& cache) {
    if (!aig) return nullptr;
    auto it = cache.find(aig);
    if (it != cache.end()) return it->second;

    if (aig->type == AIGT::t_const || aig->type == AIGT::t_lit) {
        cache[aig] = aig;
        return aig;
    }

    assert(aig->type == AIGT::t_and);
    auto l = simplify_pass(aig->l, cache);
    auto r = simplify_pass(aig->r, cache);
    bool neg = aig->neg;

    // --- Constant propagation ---
    if (l->type == AIGT::t_const) {
        stats.const_prop++;
        if (neg) {
            // ~(const & X)
            if (l->neg) { cache[aig] = aig_mng.new_const(true); return cache[aig]; } // ~(FALSE & X) = TRUE
            auto result = AIG::new_not(r); cache[aig] = result; return result; // ~(TRUE & X) = ~X
        } else {
            if (l->neg) { cache[aig] = l; return l; } // FALSE & X = FALSE
            cache[aig] = r; return r; // TRUE & X = X
        }
    }
    if (r->type == AIGT::t_const) {
        stats.const_prop++;
        if (neg) {
            if (r->neg) { cache[aig] = aig_mng.new_const(true); return cache[aig]; }
            auto result = AIG::new_not(l); cache[aig] = result; return result;
        } else {
            if (r->neg) { cache[aig] = r; return r; }
            cache[aig] = l; return l;
        }
    }

    // --- Identity: AND(x, x) = x ---
    if (l == r) {
        stats.idempotent_elim++;
        // Push NOT through inner AND: NOT(AND(a,b,k)) = AND(a,b,!k).
        // new_not only collapses NOT(NOT(x)); this handles NOT(NAND)=AND etc.
        if (neg && l->type == AIGT::t_and && l->l != l->r) {
            auto result = make_canonical(AIGT::t_and, !l->neg, l->l, l->r);
            cache[aig] = result;
            return result;
        }
        auto result = neg ? AIG::new_not(l) : l;
        cache[aig] = result;
        return result;
    }

    // --- Complementary pair elimination ---
    if (is_complement(l, r)) {
        stats.complement_elim++;
        auto result = neg ? aig_mng.new_const(true) : aig_mng.new_const(false);
        cache[aig] = result;
        return result;
    }

    // --- Literal-level identity (same var, same polarity) ---
    if (l->type == AIGT::t_lit && r->type == AIGT::t_lit &&
        l->var == r->var && l->neg == r->neg) {
        stats.idempotent_elim++;
        auto result = neg ? AIG::new_not(l) : l;
        cache[aig] = result;
        return result;
    }

    // --- Absorption: AND(a, AND(a, b)) = AND(a, b) ---
    if (r->type == AIGT::t_and && !r->neg) {
        if (r->l == l || r->r == l) { stats.absorption++; auto result = neg ? AIG::new_not(r) : r; cache[aig] = result; return result; }
    }
    if (l->type == AIGT::t_and && !l->neg) {
        if (l->l == r || l->r == r) { stats.absorption++; auto result = neg ? AIG::new_not(l) : l; cache[aig] = result; return result; }
    }

    // --- Absorption through OR: AND(a, OR(a, b)) = a ---
    if (is_or(r)) {
        // r = OR(NOT(r->l), NOT(r->r))
        // If l == NOT(r->l) or l == NOT(r->r), then AND(l, OR(l, ...)) = l
        if (is_complement(l, r->l) || is_complement(l, r->r)) {
            stats.absorption++;
            auto result = neg ? AIG::new_not(l) : l;
            cache[aig] = result;
            return result;
        }
    }
    if (is_or(l)) {
        if (is_complement(r, l->l) || is_complement(r, l->r)) {
            stats.absorption++;
            auto result = neg ? AIG::new_not(r) : r;
            cache[aig] = result;
            return result;
        }
    }

    // --- AND(a, OR(~a, b)) = AND(a, b) (subsumption) ---
    if (!neg && is_or(r)) {
        // r = OR(NOT(r->l), NOT(r->r))
        // Check if one OR-child is complement of l
        aig_ptr not_rl = AIG::new_not(r->l);
        aig_ptr not_rr = AIG::new_not(r->r);
        if (is_complement(l, not_rl)) {
            stats.complement_elim++;
            auto result = AIG::new_and(l, not_rr);
            cache[aig] = result;
            return result;
        }
        if (is_complement(l, not_rr)) {
            stats.complement_elim++;
            auto result = AIG::new_and(l, not_rl);
            cache[aig] = result;
            return result;
        }
    }
    if (!neg && is_or(l)) {
        aig_ptr not_ll = AIG::new_not(l->l);
        aig_ptr not_lr = AIG::new_not(l->r);
        if (is_complement(r, not_ll)) {
            stats.complement_elim++;
            auto result = AIG::new_and(r, not_lr);
            cache[aig] = result;
            return result;
        }
        if (is_complement(r, not_lr)) {
            stats.complement_elim++;
            auto result = AIG::new_and(r, not_ll);
            cache[aig] = result;
            return result;
        }
    }

    // --- Distribution: OR(AND(a,b), AND(a,c)) = AND(a, OR(b,c)) ---
    // This is when neg=true (OR gate): OR(l', r') where l'=NOT(l), r'=NOT(r)
    // If both l and r are AND gates, check for common factor
    if (neg && l->type == AIGT::t_and && !l->neg && r->type == AIGT::t_and && !r->neg) {
        // neg=true means this is OR(NOT(l), NOT(r)) = OR(NOT(AND(ll,lr)), NOT(AND(rl,rr)))
        // Actually no - neg on the outer AND means NOT(AND(l,r)) = OR(NOT(l), NOT(r))
        // But l and r are the AND children. So this node = NOT(AND(l, r)).
        // l = AND(ll, lr), r = AND(rl, rr)
        // NOT(AND(AND(ll,lr), AND(rl,rr)))
        // = OR(NOT(AND(ll,lr)), NOT(AND(rl,rr)))
        // = OR(OR(~ll,~lr), OR(~rl,~rr))
        // This is NOT the distribution pattern. Skip for now.
    }

    // --- OR subsumption: OR(a, AND(~a, b)) = OR(a, b) ---
    // Dual of AND subsumption. When neg=true this is an OR gate: OR(NOT(l), NOT(r))
    if (neg) {
        // OR children are NOT(l) and NOT(r)
        aig_ptr or_l = AIG::new_not(l);
        aig_ptr or_r = AIG::new_not(r);

        // Check if or_r is AND(~or_l, something) → remove ~or_l from the AND
        if (or_r->type == AIGT::t_and && !or_r->neg) {
            if (is_complement(or_l, or_r->l)) {
                stats.absorption++;
                auto result = AIG::new_or(or_l, or_r->r);
                cache[aig] = result;
                return result;
            }
            if (is_complement(or_l, or_r->r)) {
                stats.absorption++;
                auto result = AIG::new_or(or_l, or_r->l);
                cache[aig] = result;
                return result;
            }
        }
        // Check if or_l is AND(~or_r, something)
        if (or_l->type == AIGT::t_and && !or_l->neg) {
            if (is_complement(or_r, or_l->l)) {
                stats.absorption++;
                auto result = AIG::new_or(or_r, or_l->r);
                cache[aig] = result;
                return result;
            }
            if (is_complement(or_r, or_l->r)) {
                stats.absorption++;
                auto result = AIG::new_or(or_r, or_l->l);
                cache[aig] = result;
                return result;
            }
        }
    }

    // --- Resolution: AND(OR(a,b), OR(a,~b)) = a ---
    // When both children are OR gates sharing one term, and the other terms are complements
    if (!neg && is_or(l) && is_or(r)) {
        aig_ptr l_ch1 = AIG::new_not(l->l);
        aig_ptr l_ch2 = AIG::new_not(l->r);
        aig_ptr r_ch1 = AIG::new_not(r->l);
        aig_ptr r_ch2 = AIG::new_not(r->r);

        // Check all 4 pairings for resolution: common + complementary pair
        aig_ptr common = nullptr, lb = nullptr, rc = nullptr;
        if (l_ch1 == r_ch1)      { common = l_ch1; lb = l_ch2; rc = r_ch2; }
        else if (l_ch1 == r_ch2) { common = l_ch1; lb = l_ch2; rc = r_ch1; }
        else if (l_ch2 == r_ch1) { common = l_ch2; lb = l_ch1; rc = r_ch2; }
        else if (l_ch2 == r_ch2) { common = l_ch2; lb = l_ch1; rc = r_ch1; }

        if (common && is_complement(lb, rc)) {
            // Resolution: AND(OR(a,b), OR(a,~b)) = a
            stats.complement_elim++;
            auto result = neg ? AIG::new_not(common) : common;
            cache[aig] = result;
            return result;
        }

        // --- Distribution: AND(OR(a,b), OR(a,c)) = OR(a, AND(b,c)) ---
        if (common) {
            stats.and_or_distrib++;
            auto result = AIG::new_or(common, AIG::new_and(lb, rc));
            cache[aig] = result;
            return result;
        }
    }

    // --- Rebuild with simplified children ---
    auto result = make_canonical(AIGT::t_and, neg, l, r);
    cache[aig] = result;
    return result;
}

// ========== Pass 2: Structural hashing ==========

aig_ptr AIGRewriter::hash_cons(const aig_ptr& aig, AigPtrMap& cache) {
    if (!aig) return nullptr;
    auto it = cache.find(aig);
    if (it != cache.end()) return it->second;

    if (aig->type == AIGT::t_const || aig->type == AIGT::t_lit) {
        cache[aig] = aig;
        return aig;
    }

    auto l = hash_cons(aig->l, cache);
    auto r = hash_cons(aig->r, cache);
    auto result = make_canonical(aig->type, aig->neg, l, r);
    cache[aig] = result;
    return result;
}

// ========== Pass 3: Deep multi-level absorption ==========

aig_ptr AIGRewriter::deep_absorb(const aig_ptr& aig, AigPtrMap& cache) {
    if (!aig) return nullptr;
    auto it = cache.find(aig);
    if (it != cache.end()) return it->second;

    if (aig->type == AIGT::t_const || aig->type == AIGT::t_lit) {
        cache[aig] = aig;
        return aig;
    }

    auto l = deep_absorb(aig->l, cache);
    auto r = deep_absorb(aig->r, cache);

    // Fast path: deep_absorb's flattening and cross-level subsumption rules
    // can only fire when at least one child is a "real" gate -- a positive
    // AND (flattenable into the parent) or an OR gate (cross-level
    // absorption / subsumption). When neither child is such a gate the
    // expensive collect/sort/pairwise-subsumption pipeline is guaranteed
    // to do nothing beyond what make_canonical does, so skip it.
    //
    // On real manthan workloads this fires for the vast majority of nodes
    // (leaves of branch-ANDs are literals) and cuts deep_absorb's cost
    // from the dominant phase of aig-rewrite to a small fraction.
    auto is_proper_and = [](const aig_ptr& n) {
        return n && n->type == AIGT::t_and && !n->neg && n->l != n->r;
    };
    bool l_and = is_proper_and(l), r_and = is_proper_and(r);
    bool l_or  = is_or(l),          r_or  = is_or(r);
    if (!l_and && !r_and && !l_or && !r_or) {
        // Cheap local rules (simplify_pass would normally catch these,
        // but recursion may have produced new literal/constant children
        // that expose them for the first time).
        if (aig->type == AIGT::t_and && !aig->neg) {
            if (l == r) {
                stats.idempotent_elim++;
                cache[aig] = l;
                return l;
            }
            if (is_complement(l, r)) {
                stats.complement_elim++;
                auto result = aig_mng.new_const(false);
                cache[aig] = result;
                return result;
            }
            if (l->type == AIGT::t_const) {
                stats.const_prop++;
                auto result = l->neg ? l : r; // FALSE&x=FALSE, TRUE&x=x
                cache[aig] = result;
                return result;
            }
            if (r->type == AIGT::t_const) {
                stats.const_prop++;
                auto result = r->neg ? r : l;
                cache[aig] = result;
                return result;
            }
        }
        auto result = make_canonical(aig->type, aig->neg, l, r);
        cache[aig] = result;
        return result;
    }

    // For AND gates (not negated), flatten and deduplicate children
    if (aig->type == AIGT::t_and && !aig->neg) {
        vector<aig_ptr> children;
        collect_and_children(l, children, false);
        collect_and_children(r, children, false);

        // Sort and deduplicate
        std::sort(children.begin(), children.end());
        children.erase(std::unique(children.begin(), children.end()), children.end());

        // Quadratic-width guard. On real manthan workloads we see absorption
        // fire <0.01% of nodes, but the O(k²) complement check and cubic
        // cross-level subsumption below blow up on wide flattened groups
        // (observed 4-5s on 572k-node AIGs with almost zero rewrites). Cap
        // the expensive analyses to small groups where they matter.
        constexpr size_t kDeepAbsorbWideGroup = 16;
        const bool wide_group = children.size() > kDeepAbsorbWideGroup;

        // Check for complementary pairs (skip for wide groups)
        if (!wide_group) {
            for (size_t i = 0; i < children.size(); i++) {
                for (size_t j = i + 1; j < children.size(); j++) {
                    if (is_complement(children[i], children[j])) {
                        stats.complement_elim++;
                        auto result = aig_mng.new_const(false);
                        cache[aig] = result;
                        return result;
                    }
                }
            }
        }

        // Remove duplicates that are structurally identical
        if (children.size() < (size_t)(l->type == AIGT::t_and ? 3 : 2) + (r->type == AIGT::t_and ? 1 : 0)) {
            stats.idempotent_elim++;
        }

        // Check for constant
        children.erase(
            std::remove_if(children.begin(), children.end(),
                [this](const aig_ptr& c) {
                    if (c->type == AIGT::t_const && !c->neg) { stats.const_prop++; return true; } // TRUE removed
                    return false;
                }),
            children.end());

        for (const auto& c : children) {
            if (c->type == AIGT::t_const && c->neg) {
                stats.const_prop++;
                auto result = aig_mng.new_const(false);
                cache[aig] = result;
                return result;
            }
        }

        if (children.empty()) {
            auto result = aig_mng.new_const(true);
            cache[aig] = result;
            return result;
        }

        // Cross-level subsumption: for each OR child, check if any AND sibling
        // or its complement appears in the OR, enabling absorption or subsumption.
        // AND(a, OR(a, b)) = a  (absorption: OR child containing AND sibling)
        // AND(a, OR(~a, b)) = AND(a, b)  (subsumption: OR child containing complement)
        bool changed = !wide_group;
        while (changed) {
            changed = false;
            for (size_t i = 0; i < children.size(); i++) {
                if (!is_or(children[i])) continue;
                // Collect OR children
                vector<aig_ptr> or_kids;
                collect_or_children(children[i], or_kids, false);
                if (or_kids.size() < 2) continue;

                // Check each AND sibling against OR children
                bool absorbed = false;
                for (size_t j = 0; j < children.size() && !absorbed; j++) {
                    if (i == j) continue;
                    // Absorption: AND(a, OR(a, ...)) = a → remove the OR child entirely
                    for (const auto& ok : or_kids) {
                        if (ok == children[j]) {
                            stats.absorption++;
                            children.erase(children.begin() + i);
                            absorbed = true;
                            changed = true;
                            break;
                        }
                    }
                }
                if (absorbed) break;

                // Subsumption: AND(a, OR(~a, b, c)) = AND(a, OR(b, c))
                vector<aig_ptr> new_or_kids;
                bool or_changed = false;
                for (const auto& ok : or_kids) {
                    bool subsumed = false;
                    for (size_t j = 0; j < children.size(); j++) {
                        if (i == j) continue;
                        if (is_complement(ok, children[j])) {
                            subsumed = true;
                            stats.complement_elim++;
                            break;
                        }
                    }
                    if (!subsumed) new_or_kids.push_back(ok);
                    else or_changed = true;
                }
                if (or_changed) {
                    if (new_or_kids.empty()) {
                        // OR() with no children = FALSE, AND(..., FALSE) = FALSE
                        auto result = aig_mng.new_const(false);
                        cache[aig] = result;
                        return result;
                    }
                    children[i] = build_or_tree(new_or_kids);
                    changed = true;
                    break;
                }
            }
        }

        // Multi-child resolution: AND(OR(a,b,c), OR(a,b,~c)) = AND(OR(a,b))
        // For each pair of OR children, if they differ in exactly one term
        // and those terms are complements, replace both with the common terms.
        if (!wide_group) {
            bool res_changed = true;
            while (res_changed) {
                res_changed = false;
                for (size_t i = 0; i < children.size() && !res_changed; i++) {
                    if (!is_or(children[i])) continue;
                    vector<aig_ptr> or_i;
                    collect_or_children(children[i], or_i, false);
                    std::sort(or_i.begin(), or_i.end());

                    for (size_t j = i + 1; j < children.size() && !res_changed; j++) {
                        if (!is_or(children[j])) continue;
                        vector<aig_ptr> or_j;
                        collect_or_children(children[j], or_j, false);
                        std::sort(or_j.begin(), or_j.end());

                        if (or_i.size() != or_j.size()) continue;

                        // Find differing positions
                        vector<aig_ptr> common;
                        aig_ptr diff_i = nullptr, diff_j = nullptr;
                        int diffs = 0;
                        // Both sorted by pointer - walk them together
                        // But they may not be identical sets, so just compare element-by-element
                        for (size_t k = 0; k < or_i.size(); k++) {
                            if (or_i[k] == or_j[k]) {
                                common.push_back(or_i[k]);
                            } else {
                                diffs++;
                                diff_i = or_i[k];
                                diff_j = or_j[k];
                            }
                        }
                        if (diffs == 1 && is_complement(diff_i, diff_j)) {
                            stats.complement_elim++;
                            if (common.empty()) {
                                // OR() resolved to TRUE, AND(..., TRUE) = AND(rest)
                                children.erase(children.begin() + j);
                                children.erase(children.begin() + i);
                            } else if (common.size() == 1) {
                                children[i] = common[0];
                                children.erase(children.begin() + j);
                            } else {
                                children[i] = build_or_tree(common);
                                children.erase(children.begin() + j);
                            }
                            res_changed = true;
                        }
                    }
                }
            }
        }

        // Re-sort and re-deduplicate after subsumption/resolution changes
        std::sort(children.begin(), children.end());
        children.erase(std::unique(children.begin(), children.end()), children.end());

        if (children.empty()) {
            auto result = aig_mng.new_const(true);
            cache[aig] = result;
            return result;
        }

        auto result = build_and_tree(children);
        cache[aig] = result;
        return result;
    }

    // For OR gates (AND with neg=true, but not NOT encoding)
    if (aig->type == AIGT::t_and && aig->neg && l != r) {
        // This is OR(NOT(l), NOT(r))
        vector<aig_ptr> children;
        collect_or_children(AIG::new_not(l), children, false);
        collect_or_children(AIG::new_not(r), children, false);

        // Sort and deduplicate
        std::sort(children.begin(), children.end());
        children.erase(std::unique(children.begin(), children.end()), children.end());

        // Quadratic-width guard (same rationale as the AND path above).
        constexpr size_t kDeepAbsorbWideGroupOr = 16;
        const bool wide_or_group = children.size() > kDeepAbsorbWideGroupOr;

        // Check for complementary pairs → TRUE (skip for wide groups)
        if (!wide_or_group) {
            for (size_t i = 0; i < children.size(); i++) {
                for (size_t j = i + 1; j < children.size(); j++) {
                    if (is_complement(children[i], children[j])) {
                        stats.complement_elim++;
                        auto result = aig_mng.new_const(true);
                        cache[aig] = result;
                        return result;
                    }
                }
            }
        }

        // Remove FALSE constants
        children.erase(
            std::remove_if(children.begin(), children.end(),
                [this](const aig_ptr& c) {
                    if (c->type == AIGT::t_const && c->neg) { stats.const_prop++; return true; }
                    return false;
                }),
            children.end());

        for (const auto& c : children) {
            if (c->type == AIGT::t_const && !c->neg) {
                stats.const_prop++;
                auto result = aig_mng.new_const(true);
                cache[aig] = result;
                return result;
            }
        }

        if (children.empty()) {
            auto result = aig_mng.new_const(false);
            cache[aig] = result;
            return result;
        }

        // Cross-level subsumption for OR: for each AND-type child, check if any
        // OR sibling or its complement appears in the AND, enabling simplification.
        // OR(a, AND(a, b)) = a  (absorption: AND child containing OR sibling)
        // OR(a, AND(~a, b)) = OR(a, b)  (subsumption: AND child containing complement)
        bool changed_or = !wide_or_group;
        while (changed_or) {
            changed_or = false;
            for (size_t i = 0; i < children.size(); i++) {
                if (!(children[i]->type == AIGT::t_and && !children[i]->neg)) continue;
                // Collect AND children of this OR child
                vector<aig_ptr> and_kids;
                collect_and_children(children[i], and_kids, false);
                if (and_kids.size() < 2) continue;

                // Absorption: OR(a, AND(a, ...)) = a → remove the AND child entirely
                bool absorbed = false;
                for (size_t j = 0; j < children.size() && !absorbed; j++) {
                    if (i == j) continue;
                    for (const auto& ak : and_kids) {
                        if (ak == children[j]) {
                            stats.absorption++;
                            children.erase(children.begin() + i);
                            absorbed = true;
                            changed_or = true;
                            break;
                        }
                    }
                }
                if (absorbed) break;

                // Subsumption: OR(a, AND(~a, b, c)) = OR(a, AND(b, c))
                vector<aig_ptr> new_and_kids;
                bool and_changed = false;
                for (const auto& ak : and_kids) {
                    bool subsumed = false;
                    for (size_t j = 0; j < children.size(); j++) {
                        if (i == j) continue;
                        if (is_complement(ak, children[j])) {
                            subsumed = true;
                            stats.complement_elim++;
                            break;
                        }
                    }
                    if (!subsumed) new_and_kids.push_back(ak);
                    else and_changed = true;
                }
                if (and_changed) {
                    if (new_and_kids.empty()) {
                        // AND() with no children = TRUE, OR(..., TRUE) = TRUE
                        auto result = aig_mng.new_const(true);
                        cache[aig] = result;
                        return result;
                    }
                    children[i] = build_and_tree(new_and_kids);
                    changed_or = true;
                    break;
                }
            }
        }

        // Re-sort and re-deduplicate after subsumption changes
        std::sort(children.begin(), children.end());
        children.erase(std::unique(children.begin(), children.end()), children.end());

        if (children.empty()) {
            auto result = aig_mng.new_const(false);
            cache[aig] = result;
            return result;
        }

        auto result = build_or_tree(children);
        cache[aig] = result;
        return result;
    }

    // Default: rebuild with simplified children
    auto result = make_canonical(aig->type, aig->neg, l, r);
    cache[aig] = result;
    return result;
}

// ========== Pass 4: ITE chain depth reduction ==========

size_t AIGRewriter::compute_depth(const aig_ptr& aig, AigPtrDepthMap& cache) const {
    if (!aig || aig->type != AIGT::t_and) return 0;
    auto it = cache.find(aig);
    if (it != cache.end()) return it->second;
    size_t d = 1 + std::max(compute_depth(aig->l, cache), compute_depth(aig->r, cache));
    cache[aig] = d;
    return d;
}

aig_ptr AIGRewriter::flatten_ite_chains(const aig_ptr& aig, AigPtrMap& cache) {
    if (!aig) return nullptr;
    auto it = cache.find(aig);
    if (it != cache.end()) return it->second;

    if (aig->type == AIGT::t_const || aig->type == AIGT::t_lit) {
        cache[aig] = aig;
        return aig;
    }

    auto l = flatten_ite_chains(aig->l, cache);
    auto r = flatten_ite_chains(aig->r, cache);

    // Detect OR chains (from ITE repairs with TRUE value):
    // OR(g1, OR(g2, OR(g3, base))) → collect all guards + base, build balanced OR tree
    if (aig->neg && l != r) {
        // This is OR(NOT(l), NOT(r))
        vector<aig_ptr> or_children;
        collect_or_children(AIG::new_not(l), or_children, false);
        collect_or_children(AIG::new_not(r), or_children, false);

        if (or_children.size() >= 3) {
            // Flatten into balanced tree (reduces depth from N to log2(N))
            std::sort(or_children.begin(), or_children.end());
            or_children.erase(std::unique(or_children.begin(), or_children.end()), or_children.end());

            // Check for complementary pairs
            for (size_t i = 0; i < or_children.size(); i++) {
                for (size_t j = i + 1; j < or_children.size(); j++) {
                    if (is_complement(or_children[i], or_children[j])) {
                        stats.complement_elim++;
                        auto result = aig_mng.new_const(true);
                        cache[aig] = result;
                        return result;
                    }
                }
            }

            auto result = build_or_tree(or_children);
            cache[aig] = result;
            return result;
        }
    }

    // Detect AND chains (from ITE repairs with FALSE value):
    if (!aig->neg) {
        vector<aig_ptr> and_children;
        collect_and_children(l, and_children, false);
        collect_and_children(r, and_children, false);

        if (and_children.size() >= 3) {
            std::sort(and_children.begin(), and_children.end());
            and_children.erase(std::unique(and_children.begin(), and_children.end()), and_children.end());

            for (size_t i = 0; i < and_children.size(); i++) {
                for (size_t j = i + 1; j < and_children.size(); j++) {
                    if (is_complement(and_children[i], and_children[j])) {
                        stats.complement_elim++;
                        auto result = aig_mng.new_const(false);
                        cache[aig] = result;
                        return result;
                    }
                }
            }

            auto result = build_and_tree(and_children);
            cache[aig] = result;
            return result;
        }
    }

    auto result = make_canonical(aig->type, aig->neg, l, r);
    cache[aig] = result;
    return result;
}

// ========== Main rewrite interface ==========

aig_ptr AIGRewriter::rewrite(const aig_ptr& aig) {
    if (!aig) return nullptr;
    struct_hash.clear();

    const aig_ptr original = aig;
    const size_t original_nodes = count_nodes(original);
    aig_ptr current = aig;
    aig_ptr best = aig;
    size_t best_nodes = original_nodes;
    const int MAX_PASSES = 5;

    for (int pass = 0; pass < MAX_PASSES; pass++) {
        size_t before = count_nodes(current);

        // Pass 1: Bottom-up simplification
        {
            AigPtrMap cache;
            current = simplify_pass(current, cache);
        }

        // Pass 2: Structural hashing
        struct_hash.clear();
        {
            AigPtrMap cache;
            current = hash_cons(current, cache);
        }

        // Pass 3: Deep absorption
        {
            AigPtrMap cache;
            current = deep_absorb(current, cache);
        }

        // Pass 4: ITE chain flattening (reduces depth from N to log2(N))
        {
            AigPtrMap cache;
            current = flatten_ite_chains(current, cache);
        }

        // Pass 5: Hash again after all transforms
        struct_hash.clear();
        {
            AigPtrMap cache;
            current = hash_cons(current, cache);
        }

        stats.total_passes++;
        size_t after = count_nodes(current);

        // Track best result seen across passes
        if (after < best_nodes) {
            best = current;
            best_nodes = after;
        }

        // Stop if no progress
        if (after >= before) break;
    }

    // Never return a result larger than the original
    return best;
}

void AIGRewriter::rewrite_all(vector<aig_ptr>& defs, int verb) {
    const double start_time = cpuTime();
    stats.clear();
    struct_hash.clear();

    // Per-sub-pass wall-clock accumulators so we can see which phase
    // dominates the total cost.
    double t_simplify = 0, t_hashcons = 0, t_deep_absorb = 0;
    double t_flatten_ite = 0, t_count = 0;

    // Reused across all count queries -- unordered_set keeps its bucket
    // array allocated between clear() calls, avoiding N reallocations
    // per pass on 500k+ node AIGs.
    std::unordered_set<const AIG*> count_scratch;
    auto count_total = [&](const vector<aig_ptr>& v) -> size_t {
        double t0 = cpuTime();
        size_t n = AIG::count_aig_nodes_fast(v, count_scratch);
        t_count += cpuTime() - t0;
        return n;
    };

    stats.nodes_before = count_total(defs);

    // Save original AIGs so we can revert individual ones that grew.
    // Previously we also counted each def's nodes here (an extra O(n) per
    // def); defer that to the end so we only count grown defs when
    // necessary.
    vector<aig_ptr> originals = defs;

    // Reuse sub-pass caches across outer passes. unordered_map::clear()
    // keeps the bucket array allocated, so we avoid 4×(allocate + destroy)
    // of a 500k-entry hash map each outer pass.
    AigPtrMap simplify_cache, absorb_cache, flatten_cache, hashcons_cache;

    // Reduce MAX_PASSES from 5 to 3. Most real reduction happens in the
    // first 1-2 passes; passes 4-5 were spending full tree traversals for
    // <1% extra shrink on the 500k-node manthan workload.
    const int MAX_PASSES = 3;
    for (int pass = 0; pass < MAX_PASSES; pass++) {
        // Snapshot root pointers so we can detect a no-op pass cheaply --
        // if no root changed identity, nothing simplified and we can stop
        // without a full count_aig_nodes_fast traversal.
        vector<aig_ptr> roots_before = defs;
        // Pass A: Bottom-up simplification. simplify_pass already calls
        // make_canonical at the end so its output is structurally hashed.
        {
            double t0 = cpuTime();
            struct_hash.clear();
            simplify_cache.clear();
            for (auto& aig : defs) if (aig) aig = simplify_pass(aig, simplify_cache);
            t_simplify += cpuTime() - t0;
        }
        // Pass B: Deep absorption. Expensive (build_*_tree allocates new
        // nodes) and its incremental benefit after the first outer pass
        // is negligible on real workloads -- subsequent outer passes run
        // simplify_pass only, which still catches new opportunities that
        // pass B exposed.
        if (pass == 0) {
            double t0 = cpuTime();
            absorb_cache.clear();
            for (auto& aig : defs) if (aig) aig = deep_absorb(aig, absorb_cache);
            t_deep_absorb += cpuTime() - t0;
        }
        // Pass C: ITE chain flattening. Same argument -- only run once.
        if (pass == 0) {
            double t0 = cpuTime();
            flatten_cache.clear();
            for (auto& aig : defs) if (aig) aig = flatten_ite_chains(aig, flatten_cache);
            t_flatten_ite += cpuTime() - t0;
        }
        stats.total_passes++;

        // Cheap progress check: if no root pointer changed, no rewrite
        // fired and we're done.
        bool any_changed = false;
        for (size_t i = 0; i < defs.size(); i++) {
            if (defs[i] != roots_before[i]) { any_changed = true; break; }
        }
        bool last_pass = (pass + 1 == MAX_PASSES) || !any_changed;

        // Only run the final re-canonicalization on the LAST outer pass.
        // Between outer passes, the next simplify_pass will canonicalize
        // everything anyway via its make_canonical calls.
        if (last_pass) {
            double t0 = cpuTime();
            struct_hash.clear();
            hashcons_cache.clear();
            for (auto& aig : defs) if (aig) aig = hash_cons(aig, hashcons_cache);
            t_hashcons += cpuTime() - t0;
        }
        if (!any_changed) break;
    }

    // Revert individual AIGs that grew. We only need to check defs that
    // differ by pointer from their original -- unchanged pointers are
    // trivially the same size.
    {
        double t0 = cpuTime();
        for (size_t i = 0; i < defs.size(); i++) {
            if (defs[i] == originals[i]) continue;
            size_t orig_count = AIG::count_aig_nodes_fast(originals[i], count_scratch);
            size_t new_count = AIG::count_aig_nodes_fast(defs[i], count_scratch);
            if (new_count > orig_count) defs[i] = originals[i];
        }
        t_count += cpuTime() - t0;
    }

    stats.nodes_after = count_total(defs);

    if (verb >= 1) {
        cout << "c o [aig-rewrite] T: " << std::fixed << std::setprecision(2)
             << (cpuTime() - start_time) << " ";
        stats.print(verb);
        cout << "c o [aig-rewrite] per-pass: "
             << "simplify " << t_simplify
             << "  hashcons " << t_hashcons
             << "  deep_absorb " << t_deep_absorb
             << "  flatten_ite " << t_flatten_ite
             << "  count " << t_count
             << endl;
    }
}
