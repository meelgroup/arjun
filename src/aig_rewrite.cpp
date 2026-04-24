/*
 Arjun - AIG Rewriting System

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#include "aig_rewrite.h"
#include "time_mem.h"
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cryptominisat5/cryptominisat.h>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <unordered_map>
#include <unordered_set>

using namespace ArjunNS;
using std::cout;
using std::endl;
using std::vector;

namespace {

// Deterministic ordering for aig_lit sorts. Default operator< on shared_ptr
// uses the raw address, which varies under ASLR; sort by stable nid paired
// with edge sign instead.
inline bool aig_lit_nid_less(const aig_lit& a, const aig_lit& b) {
    if (!a.node) return b.node != nullptr;
    if (!b.node) return false;
    if (a->nid != b->nid) return a->nid < b->nid;
    return (int)a.neg < (int)b.neg;
}

} // namespace

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

// ========== Helpers ==========

size_t AIGRewriter::count_nodes(const aig_ptr& aig) const {
    return AIG::count_aig_nodes(aig);
}

void AIGRewriter::collect_and_edges(const aig_lit& edge, vector<aig_lit>& out) {
    if (!edge) return;
    if (edge->type == AIGT::t_and && !edge.neg) {
        // Positive AND: flatten children (each already carries its edge sign).
        collect_and_edges(edge->l, out);
        collect_and_edges(edge->r, out);
    } else {
        out.push_back(edge);
    }
}

void AIGRewriter::collect_or_edges(const aig_lit& edge, vector<aig_lit>& out) {
    if (!edge) return;
    if (edge->type == AIGT::t_and && edge.neg) {
        // OR gate (negative-edge reference to AND). Its disjuncts are the
        // complements of the AND's children — De Morgan on the stored form.
        collect_or_edges(~edge->l, out);
        collect_or_edges(~edge->r, out);
    } else {
        out.push_back(edge);
    }
}

aig_lit AIGRewriter::build_and_tree(vector<aig_lit>& children) {
    if (children.empty()) return AIG::new_const(true);
    if (children.size() == 1) return children[0];
    while (children.size() > 1) {
        vector<aig_lit> next;
        next.reserve((children.size() + 1) / 2);
        for (size_t i = 0; i + 1 < children.size(); i += 2) {
            next.push_back(make_canonical(children[i], children[i+1]));
        }
        if (children.size() % 2 == 1) next.push_back(children.back());
        children = std::move(next);
    }
    return children[0];
}

aig_lit AIGRewriter::build_or_tree(vector<aig_lit>& children) {
    if (children.empty()) return AIG::new_const(false);
    if (children.size() == 1) return children[0];
    while (children.size() > 1) {
        vector<aig_lit> next;
        next.reserve((children.size() + 1) / 2);
        for (size_t i = 0; i + 1 < children.size(); i += 2) {
            // OR(a, b) = ~AND(~a, ~b). Route through make_canonical so the
            // inner AND (with ~a, ~b as its signed children) hash-conses.
            aig_lit inner = make_canonical(~children[i], ~children[i+1]);
            next.push_back(~inner);
        }
        if (children.size() % 2 == 1) next.push_back(children.back());
        children = std::move(next);
    }
    return children[0];
}

// Build an AND(l, r) with algebraic folds + structural hashing. AIG::new_and
// handles constants / idempotent / complementary / absorption first; if the
// result is still a fresh t_and we canonicalise operand order by nid and look
// it up in struct_hash for cross-call sharing.
aig_lit AIGRewriter::make_canonical(const aig_lit& l, const aig_lit& r) {
    aig_lit folded = AIG::new_and(l, r);
    if (!folded || folded->type != AIGT::t_and) return folded;

    aig_lit ll = folded->l;
    aig_lit rr = folded->r;
    // Canonical child order: larger nid first, then larger sign.
    bool swap = false;
    if (ll->nid != rr->nid) {
        swap = ll->nid < rr->nid;
    } else {
        swap = (int)ll.neg > (int)rr.neg;
    }
    if (swap) std::swap(ll, rr);

    StructKey key{ll->nid, rr->nid, ll.neg, rr.neg};
    auto it = struct_hash.find(key);
    if (it != struct_hash.end()) {
        stats.structural_hash_hits++;
        return aig_lit(it->second, folded.neg);
    }
    // Apply the canonical order to the freshly-created node (safe — new_and
    // just allocated it and no one else has a reference yet).
    folded.node->l = ll;
    folded.node->r = rr;
    struct_hash.emplace(key, folded.node);
    return folded;
}

// ========== Pass 1: Bottom-up simplification ==========
//
// Walks the AIG by node identity, rebuilding bottom-up through make_canonical
// (which chains through AIG::new_and) plus a handful of extra structural
// rules — OR absorption / subsumption / resolution / distribution — that
// AIG::new_and doesn't know about on its own. Each simplification bumps a
// stat counter that ends up in the rewrite summary line.

aig_lit AIGRewriter::simplify_pass(const aig_lit& edge, NodeRebuildMap& cache) {
    if (!edge) return aig_lit();
    auto it = cache.find(edge.get());
    if (it != cache.end()) {
        return aig_lit(it->second.node, it->second.neg ^ edge.neg);
    }

    aig_lit pos;
    if (edge->type == AIGT::t_const) {
        pos = AIG::new_const(true);
    } else if (edge->type == AIGT::t_lit) {
        pos = AIG::new_lit(edge->var, false);
    } else {
        assert(edge->type == AIGT::t_and);
        const aig_lit l = simplify_pass(edge->l, cache);
        const aig_lit r = simplify_pass(edge->r, cache);

        if (l->type == AIGT::t_const) {
            stats.const_prop++;
            pos = l.neg ? AIG::new_const(false) : r;  // FALSE∧x=FALSE, TRUE∧x=x
        } else if (r->type == AIGT::t_const) {
            stats.const_prop++;
            pos = r.neg ? AIG::new_const(false) : l;
        } else if (l == r) {
            stats.idempotent_elim++;
            pos = l;
        } else if (is_complement(l, r)) {
            stats.complement_elim++;
            pos = AIG::new_const(false);
        } else if (l->type == AIGT::t_lit && r->type == AIGT::t_lit
                   && l->var == r->var && l.neg == r.neg) {
            // Separate t_lit nodes for the same signed variable — dedup.
            stats.idempotent_elim++;
            pos = l;
        } else if (l->type == AIGT::t_lit && r->type == AIGT::t_lit
                   && l->var == r->var && l.neg != r.neg) {
            stats.complement_elim++;
            pos = AIG::new_const(false);
        }

        // Absorption: AND(a, AND(a, b)) = AND(a, b). Inner AND must be
        // positive-edge to count as a real AND.
        if (!pos && r->type == AIGT::t_and && !r.neg) {
            if (r->l == l || r->r == l) { stats.absorption++; pos = r; }
        }
        if (!pos && l->type == AIGT::t_and && !l.neg) {
            if (l->l == r || l->r == r) { stats.absorption++; pos = l; }
        }

        // Absorption / subsumption through an OR sibling. An OR's disjuncts
        // are the complements of the underlying AND's two children (De Morgan).
        if (!pos && is_or(r)) {
            const aig_lit d1 = ~r->l;
            const aig_lit d2 = ~r->r;
            if (d1 == l || d2 == l) {
                // AND(a, OR(a, ...)) = a.
                stats.absorption++;
                pos = l;
            } else if (is_complement(l, d1)) {
                // AND(a, OR(~a, b)) = AND(a, b).
                stats.complement_elim++;
                pos = make_canonical(l, d2);
            } else if (is_complement(l, d2)) {
                stats.complement_elim++;
                pos = make_canonical(l, d1);
            }
        }
        if (!pos && is_or(l)) {
            const aig_lit d1 = ~l->l;
            const aig_lit d2 = ~l->r;
            if (d1 == r || d2 == r) {
                stats.absorption++;
                pos = r;
            } else if (is_complement(r, d1)) {
                stats.complement_elim++;
                pos = make_canonical(r, d2);
            } else if (is_complement(r, d2)) {
                stats.complement_elim++;
                pos = make_canonical(r, d1);
            }
        }

        // Resolution & distribution on AND(OR, OR):
        //   AND(OR(a, b), OR(a, ~b)) = a                     (resolution)
        //   AND(OR(a, b), OR(a, c))  = OR(a, AND(b, c))      (distribution)
        if (!pos && is_or(l) && is_or(r)) {
            const aig_lit la = ~l->l, lb = ~l->r;
            const aig_lit ra = ~r->l, rb = ~r->r;

            aig_lit common, dL, dR;
            if (la == ra)      { common = la; dL = lb; dR = rb; }
            else if (la == rb) { common = la; dL = lb; dR = ra; }
            else if (lb == ra) { common = lb; dL = la; dR = rb; }
            else if (lb == rb) { common = lb; dL = la; dR = ra; }

            if (common.node) {
                if (is_complement(dL, dR)) {
                    stats.complement_elim++;
                    pos = common;
                } else {
                    stats.and_or_distrib++;
                    aig_lit inner_and = make_canonical(dL, dR);
                    aig_lit outer = make_canonical(~common, ~inner_and);
                    pos = ~outer;
                }
            }
        }

        if (!pos) pos = make_canonical(l, r);
    }

    cache[edge.get()] = pos;
    return aig_lit(pos.node, pos.neg ^ edge.neg);
}

// ========== Pass 2: Structural hashing ==========

aig_lit AIGRewriter::hash_cons(const aig_lit& edge, NodeRebuildMap& cache) {
    if (!edge) return aig_lit();
    auto it = cache.find(edge.get());
    if (it != cache.end()) return aig_lit(it->second.node, it->second.neg ^ edge.neg);

    aig_lit pos;
    if (edge->type == AIGT::t_and) {
        aig_lit l = hash_cons(edge->l, cache);
        aig_lit r = hash_cons(edge->r, cache);
        pos = make_canonical(l, r);
    } else if (edge->type == AIGT::t_const) {
        pos = AIG::new_const(true);
    } else {
        pos = AIG::new_lit(edge->var, false);
    }
    cache[edge.get()] = pos;
    return aig_lit(pos.node, pos.neg ^ edge.neg);
}

// ========== Pass 3: Multi-level absorption ==========
//
// Flattens k-ary AND / OR groups, dedups, detects complementary pairs,
// applies cross-level absorption / subsumption between AND-siblings and
// OR-child disjuncts, and resolution on OR groups that share all-but-one
// term. Operates per-edge so we handle OR gates (negative-edge ANDs) on
// their own path.

aig_lit AIGRewriter::deep_absorb(const aig_lit& edge, NodeRebuildMap& cache) {
    if (!edge) return aig_lit();
    auto it = cache.find(edge.get());
    if (it != cache.end()) return aig_lit(it->second.node, it->second.neg ^ edge.neg);

    aig_lit pos;
    if (edge->type != AIGT::t_and) {
        if (edge->type == AIGT::t_const) pos = AIG::new_const(true);
        else pos = AIG::new_lit(edge->var, false);
    } else {
        const aig_lit l = deep_absorb(edge->l, cache);
        const aig_lit r = deep_absorb(edge->r, cache);

        // Fast path: if neither child is a proper AND (positive-edge,
        // distinct children) and neither is an OR (negative-edge AND),
        // the expensive flattening can't fire. Fall through to the local
        // shortcut rules + make_canonical.
        auto is_proper_and = [](const aig_lit& e) {
            return e.node && e->type == AIGT::t_and && !e.neg && e->l != e->r;
        };
        const bool any_chain = is_proper_and(l) || is_proper_and(r)
                              || is_or(l) || is_or(r);

        if (!any_chain) {
            if (l == r) { stats.idempotent_elim++; pos = l; }
            else if (is_complement(l, r)) { stats.complement_elim++; pos = AIG::new_const(false); }
            else if (l->type == AIGT::t_const) {
                stats.const_prop++;
                pos = l.neg ? AIG::new_const(false) : r;
            } else if (r->type == AIGT::t_const) {
                stats.const_prop++;
                pos = r.neg ? AIG::new_const(false) : l;
            } else {
                pos = make_canonical(l, r);
            }
        } else {
            // ---- AND path: collect flat conjuncts, process, rebuild. ----
            vector<aig_lit> children;
            collect_and_edges(l, children);
            collect_and_edges(r, children);

            std::sort(children.begin(), children.end(), aig_lit_nid_less);
            children.erase(std::unique(children.begin(), children.end()), children.end());

            constexpr size_t kWide = 16;
            const bool wide = children.size() > kWide;

            // Complementary pair → AND folds to FALSE. Keys sort adjacent for
            // same node (differ only in sign), so a linear scan is enough.
            bool folded_false = false;
            if (!wide) {
                for (size_t i = 0; i + 1 < children.size(); i++) {
                    if (children[i].node == children[i+1].node
                        && children[i].neg != children[i+1].neg) {
                        stats.complement_elim++;
                        folded_false = true;
                        break;
                    }
                }
            }

            // Constant folds: drop TRUE, any FALSE collapses to FALSE.
            if (!folded_false) {
                vector<aig_lit> tmp;
                tmp.reserve(children.size());
                for (const auto& c : children) {
                    if (c->type == AIGT::t_const) {
                        stats.const_prop++;
                        if (c.neg) { folded_false = true; break; }  // FALSE
                        // TRUE: skip
                    } else {
                        tmp.push_back(c);
                    }
                }
                if (!folded_false) children = std::move(tmp);
            }

            if (folded_false) {
                pos = AIG::new_const(false);
            } else if (children.empty()) {
                pos = AIG::new_const(true);
            } else {
                // Cross-level subsumption: for each OR child, check if any
                // AND sibling matches one of its disjuncts (absorption) or
                // complements one (subsumption).
                bool changed = !wide;
                while (changed) {
                    changed = false;
                    for (size_t i = 0; i < children.size() && !changed; i++) {
                        if (!is_or(children[i])) continue;
                        vector<aig_lit> disj;
                        collect_or_edges(children[i], disj);
                        if (disj.size() < 2) continue;

                        // Absorption: AND(a, OR(a, ...)) = a — drop OR.
                        bool absorbed = false;
                        for (size_t j = 0; j < children.size() && !absorbed; j++) {
                            if (i == j) continue;
                            for (const auto& d : disj) {
                                if (d == children[j]) {
                                    stats.absorption++;
                                    children.erase(children.begin() + i);
                                    absorbed = true;
                                    changed = true;
                                    break;
                                }
                            }
                        }
                        if (absorbed) break;

                        // Subsumption: OR-disjunct complement of an AND-sibling drops.
                        vector<aig_lit> new_disj;
                        bool disj_changed = false;
                        for (const auto& d : disj) {
                            bool drop = false;
                            for (size_t j = 0; j < children.size(); j++) {
                                if (i == j) continue;
                                if (is_complement(d, children[j])) { drop = true; stats.complement_elim++; break; }
                            }
                            if (drop) disj_changed = true;
                            else new_disj.push_back(d);
                        }
                        if (disj_changed) {
                            if (new_disj.empty()) {
                                // Empty OR = FALSE. AND(..., FALSE) = FALSE.
                                pos = AIG::new_const(false);
                                break;
                            }
                            children[i] = build_or_tree(new_disj);
                            changed = true;
                        }
                    }
                }

                // Resolution on OR pairs: AND(OR(X, b), OR(X, ~b)) = X.
                if (!pos && !wide) {
                    bool rchanged = true;
                    while (rchanged) {
                        rchanged = false;
                        for (size_t i = 0; i < children.size() && !rchanged; i++) {
                            if (!is_or(children[i])) continue;
                            vector<aig_lit> di;
                            collect_or_edges(children[i], di);
                            std::sort(di.begin(), di.end(), aig_lit_nid_less);

                            for (size_t j = i + 1; j < children.size() && !rchanged; j++) {
                                if (!is_or(children[j])) continue;
                                vector<aig_lit> dj;
                                collect_or_edges(children[j], dj);
                                std::sort(dj.begin(), dj.end(), aig_lit_nid_less);

                                if (di.size() != dj.size()) continue;

                                vector<aig_lit> common;
                                aig_lit diff_i, diff_j;
                                int diffs = 0;
                                for (size_t k = 0; k < di.size(); k++) {
                                    if (di[k] == dj[k]) common.push_back(di[k]);
                                    else { diffs++; diff_i = di[k]; diff_j = dj[k]; }
                                }
                                if (diffs == 1 && is_complement(diff_i, diff_j)) {
                                    stats.complement_elim++;
                                    if (common.empty()) {
                                        children.erase(children.begin() + j);
                                        children.erase(children.begin() + i);
                                    } else if (common.size() == 1) {
                                        children[i] = common[0];
                                        children.erase(children.begin() + j);
                                    } else {
                                        children[i] = build_or_tree(common);
                                        children.erase(children.begin() + j);
                                    }
                                    rchanged = true;
                                }
                            }
                        }
                    }
                }

                if (!pos) {
                    std::sort(children.begin(), children.end(), aig_lit_nid_less);
                    children.erase(std::unique(children.begin(), children.end()), children.end());
                    if (children.empty()) pos = AIG::new_const(true);
                    else pos = build_and_tree(children);
                }
            }
        }
    }

    cache[edge.get()] = pos;
    return aig_lit(pos.node, pos.neg ^ edge.neg);
}

// ========== Pass 4: ITE chain depth reduction ==========
//
// Rebalance deep OR / AND chains. ITE repair loops in manthan produce long
// linear chains; flattening + rebuilding as a balanced tree drops depth
// from N to log2(N) without changing the function.

aig_lit AIGRewriter::flatten_ite_chains(const aig_lit& edge, NodeRebuildMap& cache) {
    if (!edge) return aig_lit();
    auto it = cache.find(edge.get());
    if (it != cache.end()) return aig_lit(it->second.node, it->second.neg ^ edge.neg);

    aig_lit pos;
    if (edge->type != AIGT::t_and) {
        if (edge->type == AIGT::t_const) pos = AIG::new_const(true);
        else pos = AIG::new_lit(edge->var, false);
    } else {
        const aig_lit l = flatten_ite_chains(edge->l, cache);
        const aig_lit r = flatten_ite_chains(edge->r, cache);

        // AND balanced-tree rebuild (on the positive view of the node).
        vector<aig_lit> and_children;
        collect_and_edges(l, and_children);
        collect_and_edges(r, and_children);

        if (and_children.size() >= 3) {
            std::sort(and_children.begin(), and_children.end(), aig_lit_nid_less);
            and_children.erase(std::unique(and_children.begin(), and_children.end()), and_children.end());

            // Complementary pair anywhere → AND collapses to FALSE.
            bool folded_false = false;
            for (size_t i = 0; i + 1 < and_children.size(); i++) {
                if (and_children[i].node == and_children[i+1].node
                    && and_children[i].neg != and_children[i+1].neg) {
                    stats.complement_elim++;
                    folded_false = true;
                    break;
                }
            }
            if (folded_false) pos = AIG::new_const(false);
            else pos = build_and_tree(and_children);
        }

        // Also look for deep OR chains by treating ~l and ~r as disjuncts:
        // positive(node) = AND(l, r) = ~(OR(~l, ~r)). If that inner OR has
        // ≥ 3 disjuncts, rebuild it balanced and negate.
        if (!pos) {
            vector<aig_lit> or_children;
            collect_or_edges(~l, or_children);
            collect_or_edges(~r, or_children);
            if (or_children.size() >= 3) {
                std::sort(or_children.begin(), or_children.end(), aig_lit_nid_less);
                or_children.erase(std::unique(or_children.begin(), or_children.end()),
                                  or_children.end());
                bool folded_true = false;
                for (size_t i = 0; i + 1 < or_children.size(); i++) {
                    if (or_children[i].node == or_children[i+1].node
                        && or_children[i].neg != or_children[i+1].neg) {
                        stats.complement_elim++;
                        folded_true = true;
                        break;
                    }
                }
                if (folded_true) {
                    // OR folds to TRUE ⇒ node = ~OR = FALSE.
                    pos = AIG::new_const(false);
                } else {
                    // Balanced OR rebuild, negated for the positive node view.
                    aig_lit balanced_or = build_or_tree(or_children);
                    pos = ~balanced_or;
                }
            }
        }

        if (!pos) pos = make_canonical(l, r);
    }

    cache[edge.get()] = pos;
    return aig_lit(pos.node, pos.neg ^ edge.neg);
}

// ========== Main rewrite entry points ==========

aig_ptr AIGRewriter::rewrite(const aig_ptr& aig) {
    if (!aig) return nullptr;
    struct_hash.clear();
    const size_t before = count_nodes(aig);
    aig_lit result = aig;
    { NodeRebuildMap c; result = simplify_pass(result, c); }
    struct_hash.clear();
    { NodeRebuildMap c; result = hash_cons(result, c); }
    { NodeRebuildMap c; result = deep_absorb(result, c); }
    { NodeRebuildMap c; result = flatten_ite_chains(result, c); }
    struct_hash.clear();
    { NodeRebuildMap c; result = hash_cons(result, c); }
    stats.total_passes++;
    if (count_nodes(result) > before) return aig;
    return result;
}

void AIGRewriter::rewrite_all(vector<aig_ptr>& defs, int verb) {
    const double t = cpuTime();
    stats.clear();
    struct_hash.clear();
    stats.nodes_before = AIG::count_aig_nodes_fast(defs);

    // Snapshot originals so we can revert any def that grew.
    vector<aig_ptr> originals = defs;

    {
        NodeRebuildMap cache;
        for (auto& d : defs) if (d) d = simplify_pass(d, cache);
    }
    {
        // deep_absorb handles k-ary AND/OR flattening, multi-level absorption
        // and resolution that simplify_pass's local rules miss. Expensive
        // enough to run once per rewrite_all call rather than iteratively.
        NodeRebuildMap cache;
        for (auto& d : defs) if (d) d = deep_absorb(d, cache);
    }
    {
        // flatten_ite_chains rebalances long AND / OR chains (common from
        // manthan's ITE-repair output) as balanced trees.
        NodeRebuildMap cache;
        for (auto& d : defs) if (d) d = flatten_ite_chains(d, cache);
    }
    {
        // hash_cons is cheap and makes the final AIG share structure across
        // defs; run it last so any new ANDs created by the OR / resolution
        // rewrites also hash-cons.
        struct_hash.clear();
        NodeRebuildMap cache;
        for (auto& d : defs) if (d) d = hash_cons(d, cache);
    }
    stats.total_passes++;

    // Revert grown defs.
    for (size_t i = 0; i < defs.size(); i++) {
        if (defs[i] == originals[i]) continue;
        const size_t orig_count = AIG::count_aig_nodes_fast(originals[i]);
        const size_t new_count = AIG::count_aig_nodes_fast(defs[i]);
        if (new_count > orig_count) defs[i] = originals[i];
    }
    stats.nodes_after = AIG::count_aig_nodes_fast(defs);

    if (verb >= 1) {
        cout << "c o [aig-rewrite] T: " << std::fixed << std::setprecision(2)
             << (cpuTime() - t) << " ";
        stats.print(verb);
    }
}

// ========== SAT sweeping (FRAIG-lite) ==========
//
// Identify functionally equivalent AND nodes (possibly across different
// roots in `defs`) and merge them. Standard FRAIG recipe:
//   1. Simulate each node on random 64-bit patterns. Two nodes are
//      candidate-equivalent iff their simulation signatures are equal
//      (possibly after complementing one of them).
//   2. Verify each candidate merge with a SAT solver. A merge is
//      committed only when the miter (force outputs to differ) is UNSAT.
//   3. Rebuild each def with confirmed merges applied. Every rebuilt AND
//      goes through make_canonical so the hash-cons table captures
//      downstream sharing for free.

namespace {

// Naive Tseitin: one helper per AND, 3 clauses each. Used only to drive
// the per-class SAT check; the full encoder is overkill here.
CMSat::Lit naive_encode(const aig_lit& edge, CMSat::SATSolver& solver,
                        CMSat::Lit& true_lit, bool& true_lit_set,
                        std::map<aig_lit, CMSat::Lit>& cache)
{
    auto visitor = [&](AIGT type, uint32_t var, bool neg,
                       const CMSat::Lit* left, const CMSat::Lit* right) -> CMSat::Lit {
        if (type == AIGT::t_const) {
            if (!true_lit_set) {
                solver.new_var();
                true_lit = CMSat::Lit(solver.nVars() - 1, false);
                solver.add_clause({true_lit});
                true_lit_set = true;
            }
            return neg ? ~true_lit : true_lit;
        }
        if (type == AIGT::t_lit) {
            while (solver.nVars() <= var) solver.new_var();
            return CMSat::Lit(var, neg);
        }
        assert(type == AIGT::t_and);
        const CMSat::Lit l = *left;
        const CMSat::Lit r = *right;
        solver.new_var();
        const CMSat::Lit g(solver.nVars() - 1, false);
        solver.add_clause({~g, l});
        solver.add_clause({~g, r});
        solver.add_clause({g, ~l, ~r});
        return neg ? ~g : g;
    };
    return AIG::transform<CMSat::Lit>(edge, visitor, cache);
}

} // namespace

void AIGRewriter::sat_sweep(vector<aig_ptr>& defs, int verb) {
    if (!sat_sweep_enabled) return;
    const double start_time = cpuTime();
    const size_t nodes_before = AIG::count_aig_nodes_fast(defs);

    // Collect reachable nodes in post-order (children before parents).
    // Keep the owning shared_ptr for each node so we can build signed edges
    // into it later for encoding, and so rebuild doesn't have its input
    // freed out from under it when defs[] is mutated.
    std::unordered_map<const AIG*, aig_node_ptr> raw_to_shared;
    vector<const AIG*> topo;
    std::function<void(const aig_ptr&)> dfs = [&](const aig_ptr& e) {
        if (!e) return;
        if (raw_to_shared.count(e.get())) return;
        raw_to_shared[e.get()] = e.node;
        if (e->type == AIGT::t_and) {
            dfs(e->l);
            if (e->r.get() != e->l.get()) dfs(e->r);
        }
        topo.push_back(e.get());
    };
    for (const auto& r : defs) dfs(r);

    // Random 64-bit simulation per input variable. Fixed seed → determinism.
    std::set<uint32_t> used_vars;
    for (const auto* n : topo) {
        if (n->type == AIGT::t_lit) used_vars.insert(n->var);
    }
    const uint32_t R = sweep_sim_rounds;
    std::mt19937_64 rng(0xA11CEULL);
    std::unordered_map<uint32_t, vector<uint64_t>> var_pats;
    for (uint32_t v : used_vars) {
        var_pats[v].resize(R);
        for (uint32_t i = 0; i < R; i++) var_pats[v][i] = rng();
    }

    // Simulate every node's POSITIVE value. Fanin sign flips the child's
    // pattern on the way into the AND.
    std::unordered_map<const AIG*, vector<uint64_t>> sigs;
    sigs.reserve(topo.size());
    for (const auto* n : topo) {
        vector<uint64_t> s(R);
        if (n->type == AIGT::t_const) {
            for (uint32_t i = 0; i < R; i++) s[i] = ~0ULL;
        } else if (n->type == AIGT::t_lit) {
            const auto& p = var_pats[n->var];
            for (uint32_t i = 0; i < R; i++) s[i] = p[i];
        } else {
            auto it_l = sigs.find(n->l.get());
            auto it_r = sigs.find(n->r.get());
            assert(it_l != sigs.end() && it_r != sigs.end());
            const auto& ls = it_l->second;
            const auto& rs = it_r->second;
            for (uint32_t i = 0; i < R; i++) {
                uint64_t lv = ls[i]; if (n->l.neg) lv = ~lv;
                uint64_t rv = rs[i]; if (n->r.neg) rv = ~rv;
                s[i] = lv & rv;
            }
        }
        sigs.emplace(n, std::move(s));
    }

    // Canonicalise a signature: if the MSB of round 0 is 1, XOR every word
    // with ~0. Maps `x` and `¬x` to the same canonical form so
    // complement-equivalent nodes cluster into one class.
    auto canonicalize = [&](const vector<uint64_t>& s, bool& was_flipped) {
        was_flipped = (s[0] >> 63) & 1ULL;
        if (!was_flipped) return s;
        vector<uint64_t> out(R);
        for (uint32_t i = 0; i < R; i++) out[i] = ~s[i];
        return out;
    };

    // Group t_and nodes by canonical signature.
    struct Key {
        vector<uint64_t> data;
        bool operator==(const Key& o) const { return data == o.data; }
    };
    struct KeyHash {
        size_t operator()(const Key& k) const noexcept {
            size_t h = 0xcbf29ce484222325ULL;
            for (uint64_t w : k.data) { h ^= w; h *= 0x100000001b3ULL; }
            return h;
        }
    };
    std::unordered_map<Key, vector<std::pair<const AIG*, bool>>, KeyHash> classes;
    for (const auto* n : topo) {
        if (n->type != AIGT::t_and) continue;
        bool flipped;
        Key k{canonicalize(sigs[n], flipped)};
        classes[std::move(k)].emplace_back(n, flipped);
    }

    // SAT-verify each non-singleton class against its lowest-nid
    // representative. An activation literal per-check lets us reuse one
    // solver for the whole class.
    std::unordered_map<const AIG*, std::pair<const AIG*, bool>> sub;
    for (auto& [key, members] : classes) {
        if (members.size() < 2) continue;
        if (members.size() > sweep_max_class_size) continue;
        stats.sweep_sim_groups++;
        std::sort(members.begin(), members.end(),
            [](const auto& a, const auto& b) { return a.first->nid < b.first->nid; });

        CMSat::SATSolver solver;
        solver.set_verbosity(0);
        CMSat::Lit true_lit;
        bool true_lit_set = false;
        std::map<aig_lit, CMSat::Lit> enc_cache;

        // Pre-allocate input vars so the true_lit helper doesn't alias any.
        if (!used_vars.empty()) {
            const uint32_t maxv = *std::max_element(used_vars.begin(), used_vars.end());
            solver.new_vars(maxv + 1);
        }

        auto to_edge = [&](const AIG* n) -> aig_lit {
            return aig_lit(raw_to_shared.at(n), false);
        };

        const CMSat::Lit rep_lit = naive_encode(to_edge(members[0].first),
            solver, true_lit, true_lit_set, enc_cache);
        const CMSat::Lit rep_canon = members[0].second ? ~rep_lit : rep_lit;

        for (size_t i = 1; i < members.size(); i++) {
            const auto& [node, flipped] = members[i];
            if (sub.count(node)) continue;

            const CMSat::Lit node_lit = naive_encode(to_edge(node),
                solver, true_lit, true_lit_set, enc_cache);
            const CMSat::Lit node_canon = flipped ? ~node_lit : node_lit;

            solver.new_var();
            const CMSat::Lit act(solver.nVars() - 1, false);
            solver.add_clause({~act, rep_canon, node_canon});
            solver.add_clause({~act, ~rep_canon, ~node_canon});
            vector<CMSat::Lit> assumps{act};
            stats.sweep_sat_checks++;
            const CMSat::lbool res = solver.solve(&assumps);
            // Retire the activation lit either way.
            solver.add_clause({~act});

            if (res == CMSat::l_False) {
                const bool invert = (flipped != members[0].second);
                sub[node] = {members[0].first, invert};
                stats.sweep_merges++;
            } else if (res == CMSat::l_True) {
                stats.sweep_cex_refuted++;
            }
            // l_Undef: treated as "can't prove" — no merge.
        }
    }

    // Rebuild defs applying the substitution. Every produced AND goes
    // through make_canonical → hash-consed against struct_hash, so
    // identical rebuilt ANDs share. Cache stores the rebuild for each
    // source node's POSITIVE value; callers combine with incoming edge sign.
    std::unordered_map<const AIG*, aig_lit> rebuild;
    std::function<aig_lit(const AIG*)> rebuild_node = [&](const AIG* n) -> aig_lit {
        if (!n) return aig_lit();
        auto it = rebuild.find(n);
        if (it != rebuild.end()) return it->second;

        aig_lit result;
        auto it_sub = sub.find(n);
        if (it_sub != sub.end()) {
            aig_lit rep_pos = rebuild_node(it_sub->second.first);
            result = aig_lit(rep_pos.node, rep_pos.neg ^ it_sub->second.second);
        } else if (n->type == AIGT::t_and) {
            aig_lit lp = rebuild_node(n->l.get());
            aig_lit rp = rebuild_node(n->r.get());
            aig_lit l_edge(lp.node, lp.neg ^ n->l.neg);
            aig_lit r_edge(rp.node, rp.neg ^ n->r.neg);
            result = make_canonical(l_edge, r_edge);
        } else {
            auto rsi = raw_to_shared.find(n);
            assert(rsi != raw_to_shared.end());
            result = aig_lit(rsi->second, false);
        }
        rebuild[n] = result;
        return result;
    };

    // A merge can correctly prove that an AND subtree of defs[v] ≡ x_v (since
    // defs[v] literally defines v, so any subtree functionally matching x_v
    // is valid). After rebuild, make_canonical's folding may collapse such
    // an AND into lit(v), embedding x_v as a leaf inside defs[v] — a
    // definition-level self-loop. Detect and revert those defs.
    //
    // Collect the set of variable leaves reachable from an AIG edge.
    // Memoised on node identity: rebuilt defs are DAGs with diamond sharing
    // (hash-consed by make_canonical), so a tree-style recursive walk
    // visits shared subgraphs an exponential number of times on adversarial
    // inputs (e.g. sdlx-fixpoint-5: ~90k-node post-sweep AIG made the cycle
    // check alone take >100s of CPU before memoisation).
    auto collect_leaf_vars_memo = [](const aig_ptr& e,
                                     std::unordered_set<uint32_t>& out_vars) {
        std::unordered_set<const AIG*> seen;
        std::function<void(const AIG*)> rec = [&](const AIG* n) {
            if (!n) return;
            if (!seen.insert(n).second) return;
            if (n->type == AIGT::t_lit) { out_vars.insert(n->var); return; }
            if (n->type == AIGT::t_and) {
                rec(n->l.get());
                rec(n->r.get());
            }
        };
        rec(e.get());
    };
    // Compute all proposed new defs; apply only the direct self-ref revert
    // here, then check for indirect cycles across defs below.
    std::vector<aig_ptr> orig_defs = defs;
    for (uint32_t v = 0; v < defs.size(); v++) {
        auto& d = defs[v];
        if (!d) continue;
        aig_lit pos = rebuild_node(d.get());
        aig_ptr new_d(pos.node, pos.neg ^ d.neg);
        std::unordered_set<uint32_t> leaves;
        collect_leaf_vars_memo(new_d, leaves);
        if (leaves.count(v)) {
            stats.sweep_self_ref_reverts++;
            continue;
        }
        d = new_d;
    }

    // Indirect cycle detection. The per-def has_self_lit check above only
    // catches direct self-loops (var v as a leaf of defs[v]). Cross-def
    // substitutions can also wire defs[v] to depend on some var w whose def
    // now depends (directly or indirectly) on v — forming a cycle like
    // v -> w -> ... -> v through multiple defs' AIGs. Downstream code
    // (test-synth, get_dependent_vars_recursive) infinite-loops on this.
    //
    // Fix: collect direct def-level deps (for each v, the set of defined vars
    // appearing as leaves of defs[v]). Iterate DFS cycle detection; on each
    // cycle found, pick the first cycle member that hasn't been reverted yet
    // and revert its def to the pre-sweep version. Loop until no cycles
    // remain. Reverts are bounded by defs.size() since in the worst case we
    // revert every def on a cycle back to orig, at which point that subset
    // mirrors the (acyclic) pre-sweep graph.
    auto def_deps = [&](uint32_t v) {
        // Reuse the memoised-DFS helper above; same DAG-sharing concern.
        std::unordered_set<uint32_t> leaves;
        collect_leaf_vars_memo(defs[v], leaves);
        std::vector<uint32_t> defined_deps;
        defined_deps.reserve(leaves.size());
        for (uint32_t u : leaves) {
            if (u < defs.size() && defs[u] != nullptr && u != v) defined_deps.push_back(u);
        }
        std::sort(defined_deps.begin(), defined_deps.end());
        return defined_deps;
    };
    std::vector<std::vector<uint32_t>> deps(defs.size());
    for (uint32_t v = 0; v < defs.size(); v++) {
        if (!defs[v]) continue;
        deps[v] = def_deps(v);
    }

    std::vector<bool> reverted(defs.size(), false);
    while (true) {
        std::vector<uint8_t> state(defs.size(), 0); // 0=white, 1=gray, 2=black
        std::vector<uint32_t> path;
        std::vector<uint32_t> cycle_members;
        std::function<bool(uint32_t)> dfs = [&](uint32_t v) -> bool {
            if (state[v] == 2) return false;
            if (state[v] == 1) {
                // Back edge to v; cycle is path[idx(v)..end]. Record members.
                auto it = std::find(path.begin(), path.end(), v);
                for (; it != path.end(); ++it) cycle_members.push_back(*it);
                return true;
            }
            state[v] = 1;
            path.push_back(v);
            for (uint32_t u : deps[v]) {
                if (dfs(u)) return true;
            }
            path.pop_back();
            state[v] = 2;
            return false;
        };
        bool any_cycle = false;
        for (uint32_t v = 0; v < defs.size(); v++) {
            if (state[v] == 0 && defs[v] != nullptr) {
                path.clear();
                cycle_members.clear();
                if (dfs(v)) { any_cycle = true; break; }
            }
        }
        if (!any_cycle) break;

        // Pick a cycle member that hasn't been reverted yet.
        uint32_t to_revert = std::numeric_limits<uint32_t>::max();
        for (uint32_t m : cycle_members) {
            if (!reverted[m]) { to_revert = m; break; }
        }
        if (to_revert == std::numeric_limits<uint32_t>::max()) {
            // All cycle members are already at orig defs, yet a cycle exists.
            // That can't happen if orig_defs was acyclic (which defs_invariant
            // verifies upstream), so treat this as a real bug and bail out by
            // fully reverting everything to orig.
            defs = orig_defs;
            for (uint32_t v = 0; v < defs.size(); v++) {
                if (defs[v]) deps[v] = def_deps(v);
                else deps[v].clear();
            }
            stats.sweep_cycle_reverts++;
            break;
        }
        defs[to_revert] = orig_defs[to_revert];
        deps[to_revert] = def_deps(to_revert);
        reverted[to_revert] = true;
        stats.sweep_cycle_reverts++;
    }

    if (verb >= 1) {
        const size_t nodes_after = AIG::count_aig_nodes_fast(defs);
        const double pct = nodes_before
            ? 100.0 * (1.0 - (double)nodes_after / (double)nodes_before) : 0.0;
        cout << "c o [aig-rewrite] sat-sweep T: "
             << std::fixed << std::setprecision(2) << (cpuTime() - start_time)
             << "  nodes: " << nodes_before << " -> " << nodes_after
             << " (" << std::setprecision(1) << pct << "% reduction)"
             << "  groups=" << stats.sweep_sim_groups
             << "  checks=" << stats.sweep_sat_checks
             << "  merges=" << stats.sweep_merges
             << "  refuted=" << stats.sweep_cex_refuted
             << "  self_ref_reverts=" << stats.sweep_self_ref_reverts
             << "  cycle_reverts=" << stats.sweep_cycle_reverts
             << endl;
    }
}
