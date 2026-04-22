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

// ========== Main rewrite entry points ==========

aig_ptr AIGRewriter::rewrite(const aig_ptr& aig) {
    if (!aig) return nullptr;
    struct_hash.clear();
    const size_t before = count_nodes(aig);
    NodeRebuildMap c;
    aig_lit result = simplify_pass(aig, c);
    stats.total_passes++;
    // Never return a result larger than the original.
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

    NodeRebuildMap cache;
    for (auto& d : defs) {
        if (d) d = simplify_pass(d, cache);
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
