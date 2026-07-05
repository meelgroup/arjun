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
