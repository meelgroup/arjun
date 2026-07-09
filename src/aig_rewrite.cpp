/*
 Arjun - AIG Rewriting System

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#include "aig_rewrite.h"
#include "constants.h"
#include "time_mem.h"
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cryptominisat5/cryptominisat.h>
#include <iomanip>
#include <iostream>
#include <map>
#include <set>
#include <unordered_map>

using namespace ArjunNS;
using std::cout;
using std::endl;
using std::vector;

namespace {

#ifdef SLOW_DEBUG
// Brute-force equivalence check across all input assignments (≤ kMaxVars).
// Catches a rewrite rule that breaks the function the moment it fires.
inline void slow_assert_equiv(const aig_lit& a, const aig_lit& b) {
    if (!a.node || !b.node) { assert(a.node == b.node); return; }
    std::set<uint32_t> vars;
    AIG::get_dependent_vars(a, vars, std::numeric_limits<uint32_t>::max());
    AIG::get_dependent_vars(b, vars, std::numeric_limits<uint32_t>::max());
    constexpr size_t kMaxVars = 16;
    if (vars.empty() || vars.size() > kMaxVars) return;
    const uint32_t maxv = *vars.rbegin();
    std::vector<aig_lit> defs(maxv + 1, nullptr);
    std::vector<uint32_t> vlist(vars.begin(), vars.end());
    for (uint32_t mask = 0; mask < (1u << vlist.size()); mask++) {
        std::vector<CMSat::lbool> vals(maxv + 1, CMSat::l_False);
        for (size_t i = 0; i < vlist.size(); i++)
            if ((mask >> i) & 1u) vals[vlist[i]] = CMSat::l_True;
        std::map<aig_lit, CMSat::lbool> ca, cb;
        const CMSat::lbool va = AIG::evaluate(vals, a, defs, ca);
        const CMSat::lbool vb = AIG::evaluate(vals, b, defs, cb);
        assert(va == vb && "AIGRewriter changed the function!");
    }
}
#endif

} // namespace

void AIGRewriteStats::print(int verb) const {
    if (verb < 1) return;
    cout << "c o [aig-rw] T:" << std::fixed << std::setprecision(2) << total_time
         << " n:" << nodes_before << "->" << nodes_after
         << " (-" << std::fixed << std::setprecision(1)
         << (nodes_before > 0 ? (1.0 - (double)nodes_after / nodes_before) * 100.0 : 0.0) << "%)"
         << " p:" << total_passes
         << " cp:" << const_prop
         << " cmp:" << complement_elim
         << " idm:" << idempotent_elim
         << " abs:" << absorption
         << " dst:" << and_or_distrib
         << " xor:" << xor_simplify
         << " hh:" << structural_hash_hits
         << " chd:" << chain_defs
         << " chc:" << chain_cubes
         << " chdup:" << chain_dup_cubes
         << endl;
}

void AIGRewriteStats::clear() { *this = AIGRewriteStats(); }

// ========== Helpers ==========

aig_lit AIGRewriter::cached_lit(uint32_t var, bool neg) {
    auto it = lit_hash.find(var);
    if (it != lit_hash.end()) return aig_lit(it->second, neg);
    aig_lit fresh = AIG::new_lit(var, false);
    lit_hash.emplace(var, fresh.node);
    return aig_lit(fresh.node, neg);
}

aig_lit AIGRewriter::cached_const(bool val) {
    if (!const_true_node) {
        aig_lit t = AIG::new_const(true);
        const_true_node = t.node;
    }
    return aig_lit(const_true_node, !val);
}

// AND(l,r) with algebraic folds + structural hashing. AIG::new_and handles
// constants / idempotent / complementary / local absorption; if the result is
// a fresh t_and we canonicalise operand order by nid and hash-cons it.
aig_lit AIGRewriter::make_canonical(const aig_lit& l, const aig_lit& r) {
    // Fast path: probe the hash from the input key before new_and allocates.
    // On a hit (the hot case) we skip the make_shared. Fold cases
    // (const/identity/absorption) never stored their input key, so they miss
    // here and fall through to new_and.
    {
        uint64_t lnid = l->nid, rnid = r->nid;
        bool lneg = l.neg, rneg = r.neg;
        bool swap = (lnid != rnid) ? (lnid < rnid) : ((int)lneg > (int)rneg);
        if (swap) { std::swap(lnid, rnid); std::swap(lneg, rneg); }
        auto it = struct_hash.find(StructKey{lnid, rnid, lneg, rneg});
        if (it != struct_hash.end()) {
            stats.structural_hash_hits++;
            return aig_lit(it->second, false);
        }
    }

    aig_lit folded = AIG::new_and(l, r);
    if (!folded || folded->type != AIGT::t_and) return folded;

    aig_lit ll = folded->l;
    aig_lit rr = folded->r;
    bool swap = (ll->nid != rr->nid) ? (ll->nid < rr->nid)
                                     : ((int)ll.neg > (int)rr.neg);
    if (swap) std::swap(ll, rr);

    StructKey key{ll->nid, rr->nid, ll.neg, rr.neg};
    auto it = struct_hash.find(key);
    if (it != struct_hash.end()) {
        stats.structural_hash_hits++;
        return aig_lit(it->second, folded.neg);
    }
    // Safe to write children: new_and just allocated the node.
    folded.node->l = ll;
    folded.node->r = rr;
    struct_hash.emplace(key, folded.node);
    return folded;
}

// ========== Pass 1: Bottom-up simplification ==========
//
// Walks the AIG by node identity, rebuilding bottom-up through make_canonical
// plus extra OR-absorption / subsumption / resolution / distribution rules
// that AIG::new_and doesn't apply on its own.

// AND(or_e, other) where or_e is an OR (negative-edge AND).
aig_lit AIGRewriter::try_or_sibling(const aig_lit& or_e, const aig_lit& other) {
    assert(is_or(or_e));
    const aig_lit d1 = ~or_e->l;
    const aig_lit d2 = ~or_e->r;
    // AND(a, OR(a, ...)) = a
    if (d1 == other || d2 == other) { stats.absorption++; return other; }
    // AND(a, OR(~a, b)) = AND(a, b)
    if (is_complement(other, d1)) { stats.complement_elim++; return make_canonical(other, d2); }
    if (is_complement(other, d2)) { stats.complement_elim++; return make_canonical(other, d1); }

    // Drill into each disjunct: under outer AND with sibling `other`,
    //   d_i containing `other`  ⇒ d_i reduces to its other fanin (BCP).
    //   d_i containing `~other` ⇒ d_i = FALSE ⇒ OR collapses to other_d.
    auto drill = [&](const aig_lit& d, const aig_lit& other_d) -> aig_lit {
        if (!d.node || d->type != AIGT::t_and || d.neg) return aig_lit();
        if (is_complement(d->l, other) || is_complement(d->r, other)) {
            stats.complement_elim++;
            return make_canonical(other, other_d);
        }
        aig_lit x;
        if (d->l == other) x = d->r;
        else if (d->r == other) x = d->l;
        if (x.node) {
            stats.absorption++;
            aig_lit new_or = ~make_canonical(~x, ~other_d);
            return make_canonical(other, new_or);
        }
        return aig_lit();
    };
    if (aig_lit p = drill(d1, d2); p.node) return p;
    if (aig_lit p = drill(d2, d1); p.node) return p;

    // `other` is itself a positive AND: match OR disjuncts against its fanins.
    if (other->type == AIGT::t_and && !other.neg) {
        if (d1 == other->l || d1 == other->r || d2 == other->l || d2 == other->r) {
            stats.absorption++;
            return other;
        }
        if (is_complement(d1, other->l) || is_complement(d1, other->r)) {
            stats.complement_elim++;
            return make_canonical(other, d2);
        }
        if (is_complement(d2, other->l) || is_complement(d2, other->r)) {
            stats.complement_elim++;
            return make_canonical(other, d1);
        }
    }
    return aig_lit();
}

// AND(AND(A,B), AND(C,D)): complementary fanin pair ⇒ FALSE; shared fanin
// ⇒ factor as AND(shared, AND(other_l, other_r)).
aig_lit AIGRewriter::try_and_of_ands(const aig_lit& l, const aig_lit& r) {
    if (l->type != AIGT::t_and || l.neg) return aig_lit();
    if (r->type != AIGT::t_and || r.neg) return aig_lit();
    const aig_lit la = l->l, lb = l->r;
    const aig_lit ra = r->l, rb = r->r;
    if (is_complement(la, ra) || is_complement(la, rb)
     || is_complement(lb, ra) || is_complement(lb, rb)) {
        stats.complement_elim++;
        return cached_const(false);
    }
    aig_lit shared, ol, ortmp;
    if      (la == ra) { shared = la; ol = lb; ortmp = rb; }
    else if (la == rb) { shared = la; ol = lb; ortmp = ra; }
    else if (lb == ra) { shared = lb; ol = la; ortmp = rb; }
    else if (lb == rb) { shared = lb; ol = la; ortmp = ra; }
    if (!shared.node) return aig_lit();
    stats.absorption++;
    return make_canonical(shared, make_canonical(ol, ortmp));
}

// AND(OR(a,b), OR(a,~b)) = a  (resolution)
// AND(OR(a,b), OR(a,c))  = OR(a, AND(b,c))  (distribution)
aig_lit AIGRewriter::try_resolve_distribute(const aig_lit& l, const aig_lit& r) {
    if (!is_or(l) || !is_or(r)) return aig_lit();
    const aig_lit la = ~l->l, lb = ~l->r;
    const aig_lit ra = ~r->l, rb = ~r->r;
    aig_lit common, dL, dR;
    if      (la == ra) { common = la; dL = lb; dR = rb; }
    else if (la == rb) { common = la; dL = lb; dR = ra; }
    else if (lb == ra) { common = lb; dL = la; dR = rb; }
    else if (lb == rb) { common = lb; dL = la; dR = ra; }
    if (!common.node) return aig_lit();
    if (is_complement(dL, dR)) {
        stats.complement_elim++;
        return common;
    }
    stats.and_or_distrib++;
    aig_lit inner_and = make_canonical(dL, dR);
    return ~make_canonical(~common, ~inner_and);
}

aig_lit AIGRewriter::simplify_pass(const aig_lit& edge, NodeRebuildMap& cache) {
    if (!edge) return aig_lit();

    // Iterative post-order: deep AIGs would overflow the stack on recursion.
    struct Frame { const AIG* src; bool children_done; };
    std::vector<Frame> stack;
    stack.reserve(64);
    stack.push_back({edge.get(), false});

    while (!stack.empty()) {
        Frame& f = stack.back();
        const AIG* src = f.src;
        if (src == nullptr || cache.count(src)) { stack.pop_back(); continue; }
        if (src->type != AIGT::t_and) {
            cache[src] = (src->type == AIGT::t_const)
                ? cached_const(true)
                : cached_lit(src->var, false);
            stack.pop_back();
            continue;
        }
        if (!f.children_done) {
            f.children_done = true;
            stack.push_back({src->r.get(), false});
            stack.push_back({src->l.get(), false});
            continue;
        }

        // Compose child rebuilds with this node's incoming edge signs.
        auto it_lc = cache.find(src->l.get());
        auto it_rc = cache.find(src->r.get());
        aig_lit lcached = (it_lc != cache.end()) ? it_lc->second : aig_lit();
        aig_lit rcached = (it_rc != cache.end()) ? it_rc->second : aig_lit();
        const aig_lit l(lcached.node, lcached.neg ^ src->l.neg);
        const aig_lit r(rcached.node, rcached.neg ^ src->r.neg);

        aig_lit pos;

        // Constant prop, idempotent, direct complement.
        if (l->type == AIGT::t_const) {
            stats.const_prop++;
            pos = l.neg ? cached_const(false) : r;
        } else if (r->type == AIGT::t_const) {
            stats.const_prop++;
            pos = r.neg ? cached_const(false) : l;
        } else if (l == r) {
            stats.idempotent_elim++;
            pos = l;
        } else if (is_complement(l, r)) {
            stats.complement_elim++;
            pos = cached_const(false);
        }

        // AND(a, AND(~a, b)) = FALSE (complementary absorption).
        if (!pos.node && r->type == AIGT::t_and && !r.neg
            && (is_complement(r->l, l) || is_complement(r->r, l))) {
            stats.complement_elim++; pos = cached_const(false);
        }
        if (!pos.node && l->type == AIGT::t_and && !l.neg
            && (is_complement(l->l, r) || is_complement(l->r, r))) {
            stats.complement_elim++; pos = cached_const(false);
        }

        // AND(a, AND(a, b)) = AND(a, b).
        if (!pos.node && r->type == AIGT::t_and && !r.neg
            && (r->l == l || r->r == l)) { stats.absorption++; pos = r; }
        if (!pos.node && l->type == AIGT::t_and && !l.neg
            && (l->l == r || l->r == r)) { stats.absorption++; pos = l; }

        // OR-sibling rewrites.
        if (!pos.node && is_or(r)) pos = try_or_sibling(r, l);
        if (!pos.node && is_or(l)) pos = try_or_sibling(l, r);

        // XOR pattern: OR(AND_A, AND_B) with two complementary fanin pairs.
        // No structural rewrite — counter only; reductions are caught earlier.
        if (!pos.node && l->type == AIGT::t_and && l.neg
                      && r->type == AIGT::t_and && r.neg) {
            const aig_lit& la = l->l; const aig_lit& lb = l->r;
            const aig_lit& ra = r->l; const aig_lit& rb = r->r;
            int compl_pairs = (is_complement(la, ra) ? 1 : 0)
                            + (is_complement(la, rb) ? 1 : 0)
                            + (is_complement(lb, ra) ? 1 : 0)
                            + (is_complement(lb, rb) ? 1 : 0);
            if (compl_pairs >= 2) stats.xor_simplify++;
        }

        if (!pos.node) pos = try_and_of_ands(l, r);
        if (!pos.node) pos = try_resolve_distribute(l, r);
        if (!pos.node) pos = make_canonical(l, r);

        cache[src] = pos;
        stack.pop_back();
    }

    auto it = cache.find(edge.get());
    aig_lit cached = (it != cache.end()) ? it->second : aig_lit();
    return aig_lit(cached.node, cached.neg ^ edge.neg);
}

// ========== Pass 2: Structural hashing ==========

aig_lit AIGRewriter::hash_cons(const aig_lit& edge, NodeRebuildMap& cache) {
    if (!edge) return aig_lit();

    struct Frame { const AIG* src; bool children_done; };
    std::vector<Frame> stack;
    stack.reserve(64);
    stack.push_back({edge.get(), false});

    while (!stack.empty()) {
        Frame& f = stack.back();
        const AIG* src = f.src;
        if (src == nullptr || cache.count(src)) { stack.pop_back(); continue; }
        if (src->type != AIGT::t_and) {
            cache[src] = (src->type == AIGT::t_const)
                ? cached_const(true)
                : cached_lit(src->var, false);
            stack.pop_back();
            continue;
        }
        if (!f.children_done) {
            f.children_done = true;
            stack.push_back({src->r.get(), false});
            stack.push_back({src->l.get(), false});
            continue;
        }
        auto it_lc = cache.find(src->l.get());
        auto it_rc = cache.find(src->r.get());
        aig_lit lcached = (it_lc != cache.end()) ? it_lc->second : aig_lit();
        aig_lit rcached = (it_rc != cache.end()) ? it_rc->second : aig_lit();
        aig_lit l(lcached.node, lcached.neg ^ src->l.neg);
        aig_lit r(rcached.node, rcached.neg ^ src->r.neg);
        cache[src] = make_canonical(l, r);
        stack.pop_back();
    }

    auto it = cache.find(edge.get());
    aig_lit cached = (it != cache.end()) ? it->second : aig_lit();
    return aig_lit(cached.node, cached.neg ^ edge.neg);
}

// ========== Decision-list (repair-chain) compression ==========
// Rebuild root-anchored OR-of-cube / AND-of-clause runs with every cube in one
// global frequency-descending literal order, so hash-consing shares the
// near-duplicate cubes' tails. Reorders only within a same-op run.

namespace {

// Collect a pure cube (positive AND-tree) into var*2+neg literals; false if
// not a cube.
bool peel_cube(const aig_lit& e, vector<uint32_t>& out) {
    if (!e) return false;
    std::vector<aig_lit> todo{e};
    while (!todo.empty()) {
        aig_lit c = todo.back();
        todo.pop_back();
        if (c->type == AIGT::t_lit) {
            out.push_back(c->var * 2 + (c.neg ? 1u : 0u));
        } else if (c->type == AIGT::t_and && !c.neg) {
            todo.push_back(c->l);
            todo.push_back(c->r);
        } else {
            return false;
        }
    }
    return true;
}

inline bool is_or_edge(const aig_lit& e) {
    return e.node && e->type == AIGT::t_and && e.neg;
}

struct ChainRun {
    bool is_or; // true: OR(cube1, cube2, ..., tail); false: AND(~c1, ~c2, ..., tail)
    vector<vector<uint32_t>> cubes; // each sorted by literal value
};

} // namespace

void AIGRewriter::compress_cube_chains(vector<aig_lit>& defs) {
    // Global literal frequency over all defs (one shared order).
    std::unordered_map<uint32_t, uint64_t> freq;
    {
        const uint64_t epoch = AIG::next_visit_epoch();
        std::vector<const AIG*> stack;
        auto count_edge = [&](const aig_lit& e) {
            if (e.node && e->type == AIGT::t_lit)
                freq[e->var * 2 + (e.neg ? 1u : 0u)]++;
        };
        for (const auto& d : defs) {
            if (!d) continue;
            count_edge(d);
            if (d->type != AIGT::t_and) continue;
            if (d.get()->visit_epoch == epoch) continue;
            d.get()->visit_epoch = epoch;
            stack.push_back(d.get());
            while (!stack.empty()) {
                const AIG* n = stack.back();
                stack.pop_back();
                for (const aig_lit* ch : {&n->l, &n->r}) {
                    count_edge(*ch);
                    const AIG* cn = ch->get();
                    if (cn && cn->type == AIGT::t_and && cn->visit_epoch != epoch) {
                        cn->visit_epoch = epoch;
                        stack.push_back(cn);
                    }
                }
            }
        }
    }
    // rank: most frequent first; ties by literal value for determinism.
    std::unordered_map<uint32_t, uint32_t> rank;
    {
        vector<std::pair<uint64_t, uint32_t>> fr;
        fr.reserve(freq.size());
        for (const auto& [l, f] : freq) fr.push_back({f, l});
        std::sort(fr.begin(), fr.end(), [](const auto& a, const auto& b) {
            if (a.first != b.first) return a.first > b.first;
            return a.second < b.second;
        });
        for (uint32_t i = 0; i < fr.size(); i++) rank[fr[i].second] = i;
    }
    // Literals never seen as an edge get a fallback rank past all real ones.
    const uint32_t rank_base = rank.size();
    auto rank_of = [&](uint32_t l) -> uint64_t {
        auto it = rank.find(l);
        if (it != rank.end()) return it->second;
        return (uint64_t)rank_base + l;
    };

    auto mk_or = [&](const aig_lit& a, const aig_lit& b) {
        return ~make_canonical(~a, ~b);
    };
    // Build a cube right-deep, most frequent literal deepest (shared suffix).
    auto build_cube = [&](const vector<uint32_t>& lits_by_rank) -> aig_lit {
        aig_lit acc = cached_lit(lits_by_rank.back() / 2, lits_by_rank.back() & 1);
        for (size_t i = lits_by_rank.size() - 1; i-- > 0; ) {
            acc = make_canonical(cached_lit(lits_by_rank[i] / 2, lits_by_rank[i] & 1), acc);
        }
        return acc;
    };
    // Emit OR(cubes) by greedily factoring the locally most frequent literal
    // (f = OR(lit AND f_with, f_without)); single cubes use the global rank
    // order. An empty residual (cube == {lit}) absorbs its with-group.
    std::function<aig_lit(vector<vector<uint32_t>>&&)> emit_or_of_cubes =
        [&](vector<vector<uint32_t>>&& cs) -> aig_lit {
            vector<aig_lit> terms;
            while (!cs.empty()) {
                if (cs.size() == 1) {
                    terms.push_back(build_cube(cs[0]));
                    break;
                }
                std::map<uint32_t, size_t> f;
                for (const auto& c : cs) for (const uint32_t l : c) f[l]++;
                uint32_t best = 0;
                size_t bestf = 0;
                for (const auto& [l, cnt] : f)
                    if (cnt > bestf) { bestf = cnt; best = l; }
                if (bestf <= 1) {
                    for (const auto& c : cs) terms.push_back(build_cube(c));
                    break;
                }
                vector<vector<uint32_t>> with;
                vector<vector<uint32_t>> without;
                bool has_empty = false;
                for (auto& c : cs) {
                    auto it = std::find(c.begin(), c.end(), best);
                    if (it == c.end()) { without.push_back(std::move(c)); continue; }
                    c.erase(it);
                    if (c.empty()) has_empty = true;
                    else with.push_back(std::move(c));
                }
                if (has_empty) {
                    // cube == {best}: absorbs the with-group entirely.
                    terms.push_back(cached_lit(best / 2, best & 1));
                } else {
                    terms.push_back(make_canonical(cached_lit(best / 2, best & 1),
                                                   emit_or_of_cubes(std::move(with))));
                }
                cs = std::move(without);
            }
            assert(!terms.empty());
            aig_lit acc = terms[0];
            for (size_t i = 1; i < terms.size(); i++) acc = mk_or(acc, terms[i]);
            return acc;
        };

    // Only rebuild defs with at least this many cubes.
    constexpr size_t kMinChainCubes = 16;

    for (auto& def : defs) {
        if (!def || def->type != AIGT::t_and) continue;

        // Peel root-anchored runs into cube + non-cube units; continue into a
        // single non-cube unit, stop otherwise.
        vector<ChainRun> runs;
        size_t total_cubes = 0;
        aig_lit tail = def;
        bool tail_const = false; // tail became a constant (absorbing level)
        bool tail_const_val = false;
        while (true) {
            aig_lit e = tail;
            if (!e.node || e->type != AIGT::t_and) break;
            const bool level_or = is_or_edge(e);
            // Flatten this op level, dissolving same-op internal nodes.
            vector<uint32_t> cur_lits; // free literals at this level
            vector<vector<uint32_t>> cubes;
            vector<aig_lit> others;
            bool level_const_absorb = false;
            {
                const uint64_t epoch = AIG::next_visit_epoch();
                std::vector<aig_lit> todo{e};
                e.get()->visit_epoch = epoch;
                while (!todo.empty()) {
                    aig_lit n = todo.back();
                    todo.pop_back();
                    // n is a same-op internal node edge; its two child units:
                    const aig_lit c1 = level_or ? ~n->l : n->l;
                    const aig_lit c2 = level_or ? ~n->r : n->r;
                    for (const aig_lit& c : {c1, c2}) {
                        if (!c.node) continue;
                        if (c->type == AIGT::t_const) {
                            // OR with TRUE / AND with FALSE absorbs the level.
                            if (c.neg != level_or) level_const_absorb = true;
                            continue; // else neutral element
                        }
                        if (c->type == AIGT::t_lit) {
                            cur_lits.push_back(c->var * 2 + (c.neg ? 1u : 0u));
                            continue;
                        }
                        // AND node child
                        const bool same_op = level_or ? is_or_edge(c)
                                                      : (!c.neg);
                        if (same_op) {
                            if (c.get()->visit_epoch != epoch) {
                                c.get()->visit_epoch = epoch;
                                todo.push_back(c);
                            }
                            continue;
                        }
                        // Opposite-polarity AND child: cube is c on OR
                        // levels, ~c on AND levels.
                        vector<uint32_t> cube;
                        const aig_lit cube_root = level_or ? c : ~c;
                        if (peel_cube(cube_root, cube)) {
                            cubes.push_back(std::move(cube));
                        } else {
                            others.push_back(c);
                        }
                    }
                }
            }
            if (level_const_absorb) {
                tail_const = true;
                tail_const_val = level_or; // OR absorbed by TRUE, AND by FALSE
                break;
            }
            // Free literals: width-1 cubes on OR levels, clause cube {~l}
            // on AND levels.
            for (const uint32_t l : cur_lits)
                cubes.push_back({level_or ? l : (l ^ 1u)});
            if (cubes.empty()) break; // not a chain level; tail stays as-is

            runs.push_back({level_or, std::move(cubes)});
            total_cubes += runs.back().cubes.size();
            if (others.empty()) {
                // Level was exactly cubes: identity tail (OR: FALSE, AND: TRUE)
                tail_const = true;
                tail_const_val = !level_or;
                break;
            }
            if (others.size() == 1) {
                tail = others[0];
                continue;
            }
            // Multiple non-cube units: fold them and stop peeling.
            aig_lit acc = others[0];
            for (size_t i = 1; i < others.size(); i++)
                acc = level_or ? mk_or(acc, others[i])
                               : make_canonical(acc, others[i]);
            tail = acc;
            break;
        }

        if (total_cubes < kMinChainCubes) continue;

        // Rebuild from the innermost tail outward, preserving run order.
        aig_lit acc = tail_const ? cached_const(tail_const_val) : tail;
        size_t dup_dropped = 0;
        for (size_t ri = runs.size(); ri-- > 0; ) {
            ChainRun& run = runs[ri];
            // Canonicalise cubes; drop always-false (l and ~l) and duplicates.
            std::set<vector<uint32_t>> uniq;
            for (auto& c : run.cubes) {
                // Value-sort: dedup repeats, detect always-false (adjacent l, ~l).
                std::sort(c.begin(), c.end());
                c.erase(std::unique(c.begin(), c.end()), c.end());
                bool is_false = false;
                for (size_t i = 0; i + 1 < c.size(); i++)
                    if ((c[i] ^ 1u) == c[i+1]) { is_false = true; break; }
                if (is_false) { dup_dropped++; continue; }
                // Rarest first, most frequent last (deepest = shared suffix).
                std::sort(c.begin(), c.end(), [&](uint32_t a, uint32_t b) {
                    const uint64_t ra = rank_of(a), rb = rank_of(b);
                    if (ra != rb) return ra > rb;
                    return a > b;
                });
                if (!uniq.insert(c).second) dup_dropped++;
            }
            if (uniq.empty()) continue; // run had only false/dup cubes
            stats.chain_cubes += uniq.size();
            // std::set iterates in sorted (canonical) order already.
            vector<vector<uint32_t>> cs(uniq.begin(), uniq.end());
            const aig_lit s = emit_or_of_cubes(std::move(cs));
            acc = run.is_or ? mk_or(s, acc) : make_canonical(~s, acc);
        }
        stats.chain_dup_cubes += dup_dropped;
        stats.chain_defs++;
        def = acc;
    }
}

// ========== Main rewrite entry points ==========

aig_lit AIGRewriter::rewrite(const aig_lit& aig) {
    if (!aig) return nullptr;
    struct_hash.clear();
    lit_hash.clear();
    const_true_node.reset();
    const size_t before = AIG::count_aig_nodes_fast(aig);
    aig_lit result = aig;

    // A single simplify + hash-cons sweep reaches the fixed point.
    { NodeRebuildMap c; c.reserve(before); result = simplify_pass(result, c); }
    struct_hash.clear();
    struct_hash.reserve(before);
    { NodeRebuildMap c; c.reserve(before); result = hash_cons(result, c); }
    stats.total_passes++;
    SLOW_DEBUG_DO(slow_assert_equiv(aig, result));
    if (AIG::count_aig_nodes_fast(result) > before) return aig;
    return result;
}

void AIGRewriter::rewrite_all(vector<aig_lit>& defs, int verb) {
    const double t = cpuTime();
    stats.clear();
    struct_hash.clear();
    lit_hash.clear();
    const_true_node.reset();
    stats.nodes_before = AIG::count_aig_nodes_fast(defs);

    vector<aig_lit> originals = defs;

    // Per-pass tracing so a long rewrite isn't a black box: prints the AIG
    // node count and elapsed time after each pass at verb >= 2.
    auto trace = [&](const char* pass) {
        if (verb < 2) return;
        const size_t nodes = AIG::count_aig_nodes_fast(defs);
        cout << "c o [aig-rw] after " << std::setw(14)
             << std::left << pass << std::right << " nodes: " << std::setw(10)
             << nodes << " T: " << std::fixed << std::setprecision(2)
             << (cpuTime() - t) << endl;
    };
    if (verb >= 2)
        cout << "c o [aig-rw] start nodes: " << stats.nodes_before
             << " defs: " << defs.size() << endl;

    // Chain compression first (needs the raw decision-list structure).
    compress_cube_chains(defs);
    trace("chain_compress");

    // A single simplify sweep suffices; hash_cons last so new ANDs from
    // OR/resolution rewrites also share.
    const size_t n = stats.nodes_before;
    { NodeRebuildMap cache; cache.reserve(n);
      for (auto& d : defs) if (d) d = simplify_pass(d, cache); }
    trace("simplify_pass");
    { struct_hash.clear(); struct_hash.reserve(n);
      NodeRebuildMap cache; cache.reserve(n);
      for (auto& d : defs) if (d) d = hash_cons(d, cache); }
    trace("hash_cons");
    stats.total_passes++;

    // Revert any def that grew.
    for (size_t i = 0; i < defs.size(); i++) {
        if (defs[i] == originals[i]) continue;
        if (AIG::count_aig_nodes_fast(defs[i]) > AIG::count_aig_nodes_fast(originals[i]))
            defs[i] = originals[i];
    }
    stats.nodes_after = AIG::count_aig_nodes_fast(defs);
    SLOW_DEBUG_DO(for (size_t i = 0; i < defs.size(); i++)
                      slow_assert_equiv(originals[i], defs[i]));

    if (verb >= 1) {
        stats.total_time = cpuTime() - t;
        stats.print(verb);
    }
}
