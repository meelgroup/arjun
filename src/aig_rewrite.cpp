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
    return a && a->type == AIGT::t_and && a->neg;
}

size_t AIGRewriter::count_nodes(const aig_ptr& aig) const {
    set<aig_ptr> counted;
    AIG::count_aig_nodes(aig, counted);
    return counted.size();
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
    StructKey key(type, AIG::none_var, neg, ll, rr);
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
    struct_hash[key] = node;
    return node;
}

// ========== Pass 1: Bottom-up simplification ==========

aig_ptr AIGRewriter::simplify_pass(const aig_ptr& aig, map<aig_ptr, aig_ptr>& cache) {
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

    // --- Rebuild with simplified children ---
    auto result = make_canonical(AIGT::t_and, neg, l, r);
    cache[aig] = result;
    return result;
}

// ========== Pass 2: Structural hashing ==========

aig_ptr AIGRewriter::hash_cons(const aig_ptr& aig, map<aig_ptr, aig_ptr>& cache) {
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

aig_ptr AIGRewriter::deep_absorb(const aig_ptr& aig, map<aig_ptr, aig_ptr>& cache) {
    if (!aig) return nullptr;
    auto it = cache.find(aig);
    if (it != cache.end()) return it->second;

    if (aig->type == AIGT::t_const || aig->type == AIGT::t_lit) {
        cache[aig] = aig;
        return aig;
    }

    auto l = deep_absorb(aig->l, cache);
    auto r = deep_absorb(aig->r, cache);

    // For AND gates (not negated), flatten and deduplicate children
    if (aig->type == AIGT::t_and && !aig->neg) {
        vector<aig_ptr> children;
        collect_and_children(l, children, false);
        collect_and_children(r, children, false);

        // Sort and deduplicate
        std::sort(children.begin(), children.end());
        children.erase(std::unique(children.begin(), children.end()), children.end());

        // Check for complementary pairs
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

        // Check for complementary pairs → TRUE
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

        auto result = build_or_tree(children);
        cache[aig] = result;
        return result;
    }

    // Default: rebuild with simplified children
    auto result = make_canonical(aig->type, aig->neg, l, r);
    cache[aig] = result;
    return result;
}

// ========== Main rewrite interface ==========

aig_ptr AIGRewriter::rewrite(const aig_ptr& aig) {
    if (!aig) return nullptr;
    struct_hash.clear();

    aig_ptr current = aig;
    const int MAX_PASSES = 5;

    for (int pass = 0; pass < MAX_PASSES; pass++) {
        size_t before = count_nodes(current);

        // Pass 1: Bottom-up simplification
        {
            map<aig_ptr, aig_ptr> cache;
            current = simplify_pass(current, cache);
        }

        // Pass 2: Structural hashing
        struct_hash.clear();
        {
            map<aig_ptr, aig_ptr> cache;
            current = hash_cons(current, cache);
        }

        // Pass 3: Deep absorption
        {
            map<aig_ptr, aig_ptr> cache;
            current = deep_absorb(current, cache);
        }

        // Pass 4: Hash again after absorption
        struct_hash.clear();
        {
            map<aig_ptr, aig_ptr> cache;
            current = hash_cons(current, cache);
        }

        stats.total_passes++;
        size_t after = count_nodes(current);

        // Stop if no progress
        if (after >= before) break;
    }

    return current;
}

void AIGRewriter::rewrite_all(vector<aig_ptr>& defs, int verb) {
    const double start_time = cpuTime();
    stats.clear();
    struct_hash.clear();

    // Count nodes before
    {
        set<aig_ptr> counted;
        for (const auto& aig : defs) AIG::count_aig_nodes(aig, counted);
        stats.nodes_before = counted.size();
    }

    const int MAX_PASSES = 5;
    for (int pass = 0; pass < MAX_PASSES; pass++) {
        size_t before_pass;
        {
            set<aig_ptr> counted;
            for (const auto& aig : defs) AIG::count_aig_nodes(aig, counted);
            before_pass = counted.size();
        }

        // Pass 1: Bottom-up simplification (shared cache across all AIGs)
        {
            map<aig_ptr, aig_ptr> cache;
            for (auto& aig : defs) {
                if (aig) aig = simplify_pass(aig, cache);
            }
        }

        // Pass 2: Structural hashing
        struct_hash.clear();
        {
            map<aig_ptr, aig_ptr> cache;
            for (auto& aig : defs) {
                if (aig) aig = hash_cons(aig, cache);
            }
        }

        // Pass 3: Deep absorption
        {
            map<aig_ptr, aig_ptr> cache;
            for (auto& aig : defs) {
                if (aig) aig = deep_absorb(aig, cache);
            }
        }

        // Pass 4: Hash again
        struct_hash.clear();
        {
            map<aig_ptr, aig_ptr> cache;
            for (auto& aig : defs) {
                if (aig) aig = hash_cons(aig, cache);
            }
        }

        stats.total_passes++;
        size_t after_pass;
        {
            set<aig_ptr> counted;
            for (const auto& aig : defs) AIG::count_aig_nodes(aig, counted);
            after_pass = counted.size();
        }

        if (after_pass >= before_pass) break;
    }

    // Count nodes after
    {
        set<aig_ptr> counted;
        for (const auto& aig : defs) AIG::count_aig_nodes(aig, counted);
        stats.nodes_after = counted.size();
    }

    if (verb >= 1) {
        cout << "c o [aig-rewrite] T: " << std::fixed << std::setprecision(2) << (cpuTime() - start_time) << " ";
        stats.print(verb);
    }
}
