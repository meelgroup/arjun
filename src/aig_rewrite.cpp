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
#include <iomanip>
#include <iostream>

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

void AIGRewriter::sat_sweep(vector<aig_ptr>& /*defs*/, int /*verb*/) {
    // FRAIG-lite SAT sweeping — restored in a later commit.
}
