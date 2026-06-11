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

// Deterministic ordering for aig_lit sorts. The default operator< on
// shared_ptr uses raw addresses, which vary under ASLR.
inline bool aig_lit_nid_less(const aig_lit& a, const aig_lit& b) {
    if (!a.node) return b.node != nullptr;
    if (!b.node) return false;
    if (a->nid != b->nid) return a->nid < b->nid;
    return (int)a.neg < (int)b.neg;
}

#ifdef SLOW_DEBUG
// Brute-force equivalence check across all input assignments (≤ kMaxVars).
// Catches a rewrite rule that breaks the function the moment it fires.
inline void slow_assert_equiv(const aig_ptr& a, const aig_ptr& b) {
    if (!a.node || !b.node) { assert(a.node == b.node); return; }
    std::set<uint32_t> vars;
    AIG::get_dependent_vars(a, vars, std::numeric_limits<uint32_t>::max());
    AIG::get_dependent_vars(b, vars, std::numeric_limits<uint32_t>::max());
    constexpr size_t kMaxVars = 16;
    if (vars.empty() || vars.size() > kMaxVars) return;
    const uint32_t maxv = *vars.rbegin();
    std::vector<aig_ptr> defs(maxv + 1, nullptr);
    std::vector<uint32_t> vlist(vars.begin(), vars.end());
    for (uint32_t mask = 0; mask < (1u << vlist.size()); mask++) {
        std::vector<CMSat::lbool> vals(maxv + 1, CMSat::l_False);
        for (size_t i = 0; i < vlist.size(); i++)
            if ((mask >> i) & 1u) vals[vlist[i]] = CMSat::l_True;
        std::map<aig_ptr, CMSat::lbool> ca, cb;
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

void AIGRewriter::collect_and_edges(const aig_lit& edge, vector<aig_lit>& out) {
    if (!edge) return;
    if (edge->type == AIGT::t_and && !edge.neg) {
        collect_and_edges(edge->l, out);
        collect_and_edges(edge->r, out);
    } else {
        out.push_back(edge);
    }
}

void AIGRewriter::collect_or_edges(const aig_lit& edge, vector<aig_lit>& out) {
    if (!edge) return;
    if (edge->type == AIGT::t_and && edge.neg) {
        // OR = negative-edge ref to AND; disjuncts are De Morgan complements.
        collect_or_edges(~edge->l, out);
        collect_or_edges(~edge->r, out);
    } else {
        out.push_back(edge);
    }
}

aig_lit AIGRewriter::build_and_tree(vector<aig_lit>& children) {
    if (children.empty()) return cached_const(true);
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
    if (children.empty()) return cached_const(false);
    if (children.size() == 1) return children[0];
    while (children.size() > 1) {
        vector<aig_lit> next;
        next.reserve((children.size() + 1) / 2);
        for (size_t i = 0; i + 1 < children.size(); i += 2) {
            // OR(a,b) = ~AND(~a,~b); routes through make_canonical for sharing.
            aig_lit inner = make_canonical(~children[i], ~children[i+1]);
            next.push_back(~inner);
        }
        if (children.size() % 2 == 1) next.push_back(children.back());
        children = std::move(next);
    }
    return children[0];
}

// AND(l,r) with algebraic folds + structural hashing. AIG::new_and handles
// constants / idempotent / complementary / local absorption; if the result is
// a fresh t_and we canonicalise operand order by nid and hash-cons it.
aig_lit AIGRewriter::make_canonical(const aig_lit& l, const aig_lit& r) {
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

    // Iterative post-order — deep AIGs (e.g. interpolant-derived) overflow
    // the program stack on recursion.
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

// ========== Pass 3: Multi-level absorption ==========
//
// Flattens k-ary AND/OR groups, dedups, applies cross-level absorption /
// subsumption / resolution that simplify_pass's local rules miss.

// Local AND shortcuts for the case where neither child opens an AND/OR chain.
aig_lit AIGRewriter::absorb_local_and(const aig_lit& l, const aig_lit& r) {
    if (l == r) { stats.idempotent_elim++; return l; }
    if (is_complement(l, r)) { stats.complement_elim++; return cached_const(false); }
    if (l->type == AIGT::t_const) {
        stats.const_prop++;
        return l.neg ? cached_const(false) : r;
    }
    if (r->type == AIGT::t_const) {
        stats.const_prop++;
        return r.neg ? cached_const(false) : l;
    }
    return make_canonical(l, r);
}

// Fold constants and complementary pairs in a flat (sorted, deduped) AND child
// list. Returns true and sets `out` to a constant when the conjunction
// collapses (complementary pair or a FALSE conjunct ⇒ FALSE; empty ⇒ TRUE).
// Otherwise drops TRUE conjuncts in place and returns false.
bool AIGRewriter::fold_and_children(vector<aig_lit>& children, bool wide,
                                    aig_lit& out) {
    // Complementary pair ⇒ AND = FALSE. Sorted keys put same-node entries
    // adjacent, so a linear scan suffices.
    if (!wide) {
        for (size_t i = 0; i + 1 < children.size(); i++) {
            if (children[i].node == children[i+1].node
                && children[i].neg != children[i+1].neg) {
                stats.complement_elim++;
                out = cached_const(false);
                return true;
            }
        }
    }

    // Constants: drop TRUE, any FALSE ⇒ collapse.
    vector<aig_lit> tmp;
    tmp.reserve(children.size());
    for (const auto& c : children) {
        if (c->type == AIGT::t_const) {
            stats.const_prop++;
            if (c.neg) { out = cached_const(false); return true; }
        } else {
            tmp.push_back(c);
        }
    }
    children = std::move(tmp);

    if (children.empty()) { out = cached_const(true); return true; }
    return false;
}

// Wide nodes: O(n) hash-set OR-absorption only — skip the O(n²) loops.
// Drops any OR child that has a disjunct matching an AND sibling.
void AIGRewriter::absorb_wide_or(vector<aig_lit>& children) {
    std::set<std::pair<uint64_t, bool>> sibset;
    for (const auto& c : children)
        sibset.insert({c.node->nid, c.neg});
    vector<aig_lit> kept;
    kept.reserve(children.size());
    for (const auto& c : children) {
        bool absorbed = false;
        if (is_or(c)) {
            vector<aig_lit> dj;
            collect_or_edges(c, dj);
            for (const auto& d : dj) {
                if (d.node && d != c
                    && sibset.count({d.node->nid, d.neg})) {
                    absorbed = true;
                    break;
                }
            }
        }
        if (absorbed) stats.absorption++;
        else kept.push_back(c);
    }
    children.swap(kept);
}

// Cross-level absorption / subsumption against OR children (O(n²) fixed point):
//   AND(a, OR(a, ...))            = a          — drop the OR
//   AND(OR(narrow), OR(wide⊇narrow)) = OR(narrow) — drop the wider OR
//   OR disjuncts complementing an AND sibling are removed from the OR
// Returns true and sets `out` to FALSE if an emptied OR collapses the AND.
bool AIGRewriter::absorb_cross_level(vector<aig_lit>& children, aig_lit& out) {
    bool changed = true;
    while (changed) {
        changed = false;
        for (size_t i = 0; i < children.size() && !changed; i++) {
            if (!is_or(children[i])) continue;
            vector<aig_lit> disj;
            collect_or_edges(children[i], disj);
            if (disj.size() < 2) continue;

            // AND(a, OR(a, ...)) = a — drop the OR.
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

            // OR-vs-OR: narrower implies wider, so drop the wider.
            std::sort(disj.begin(), disj.end(), aig_lit_nid_less);
            bool dropped_wide = false;
            for (size_t j = 0; j < children.size() && !dropped_wide; j++) {
                if (i == j || !is_or(children[j])) continue;
                vector<aig_lit> dj;
                collect_or_edges(children[j], dj);
                if (dj.size() >= disj.size()) continue;
                std::sort(dj.begin(), dj.end(), aig_lit_nid_less);
                if (std::includes(disj.begin(), disj.end(),
                                  dj.begin(), dj.end(),
                                  aig_lit_nid_less)) {
                    stats.absorption++;
                    children.erase(children.begin() + i);
                    dropped_wide = true;
                    changed = true;
                }
            }
            if (dropped_wide) break;

            // Drop OR disjuncts that complement an AND sibling.
            vector<aig_lit> new_disj;
            bool disj_changed = false;
            for (const auto& d : disj) {
                bool drop = false;
                for (size_t j = 0; j < children.size(); j++) {
                    if (i == j) continue;
                    if (is_complement(d, children[j])) {
                        drop = true;
                        stats.complement_elim++;
                        break;
                    }
                }
                if (drop) disj_changed = true;
                else new_disj.push_back(d);
            }
            if (disj_changed) {
                if (new_disj.empty()) {
                    // Empty OR = FALSE ⇒ AND collapses.
                    out = cached_const(false);
                    return true;
                }
                children[i] = build_or_tree(new_disj);
                changed = true;
            }
        }
    }
    return false;
}

// Resolution on OR pairs of equal width: AND(OR(X,b), OR(X,~b)) = X.
void AIGRewriter::resolve_or_pairs(vector<aig_lit>& children) {
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

// Rewrite one AND node (positive value AND(l, r)) given its rebuilt children.
aig_lit AIGRewriter::absorb_and_node(const aig_lit& l, const aig_lit& r) {
    // Fast path: no AND/OR chain to flatten ⇒ use local shortcuts.
    auto is_proper_and = [](const aig_lit& e) {
        return e.node && e->type == AIGT::t_and && !e.neg && e->l != e->r;
    };
    const bool any_chain = is_proper_and(l) || is_proper_and(r)
                          || is_or(l) || is_or(r);
    if (!any_chain) return absorb_local_and(l, r);

    // Collect flat AND conjuncts.
    vector<aig_lit> children;
    collect_and_edges(l, children);
    collect_and_edges(r, children);

    std::sort(children.begin(), children.end(), aig_lit_nid_less);
    children.erase(std::unique(children.begin(), children.end()), children.end());

    constexpr size_t kWide = 16;
    const bool wide = children.size() > kWide;

    aig_lit pos;
    if (fold_and_children(children, wide, pos)) return pos;

    if (wide) {
        absorb_wide_or(children);
    } else if (absorb_cross_level(children, pos)) {
        return pos;  // emptied OR collapsed the conjunction to FALSE
    }

    if (!wide) resolve_or_pairs(children);

    std::sort(children.begin(), children.end(), aig_lit_nid_less);
    children.erase(std::unique(children.begin(), children.end()), children.end());
    return children.empty() ? cached_const(true) : build_and_tree(children);
}

aig_lit AIGRewriter::deep_absorb(const aig_lit& edge, NodeRebuildMap& cache) {
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
        const aig_lit l(lcached.node, lcached.neg ^ src->l.neg);
        const aig_lit r(rcached.node, rcached.neg ^ src->r.neg);
        assert(l.node && r.node);

        cache[src] = absorb_and_node(l, r);
        stack.pop_back();
    }

    auto it = cache.find(edge.get());
    aig_lit cached = (it != cache.end()) ? it->second : aig_lit();
    return aig_lit(cached.node, cached.neg ^ edge.neg);
}

// ========== Pass 4: ITE chain depth reduction ==========
//
// Long AND/OR chains (common in manthan's ITE-repair output) get rebuilt
// as balanced trees: depth N -> log2(N), same function.

aig_lit AIGRewriter::flatten_ite_chains(const aig_lit& edge, NodeRebuildMap& cache) {
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
        const aig_lit l(lcached.node, lcached.neg ^ src->l.neg);
        const aig_lit r(rcached.node, rcached.neg ^ src->r.neg);
        aig_lit pos;

        // AND balanced rebuild.
        vector<aig_lit> and_children;
        collect_and_edges(l, and_children);
        collect_and_edges(r, and_children);

        if (and_children.size() >= 3) {
            std::sort(and_children.begin(), and_children.end(), aig_lit_nid_less);
            and_children.erase(std::unique(and_children.begin(), and_children.end()),
                               and_children.end());
            bool folded_false = false;
            for (size_t i = 0; i + 1 < and_children.size(); i++) {
                if (and_children[i].node == and_children[i+1].node
                    && and_children[i].neg != and_children[i+1].neg) {
                    stats.complement_elim++;
                    folded_false = true;
                    break;
                }
            }
            pos = folded_false ? cached_const(false) : build_and_tree(and_children);
        }

        // OR rebuild on the inner OR view: positive(node) = ~OR(~l, ~r).
        if (!pos.node) {
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
                    pos = cached_const(false);  // ~OR = ~TRUE = FALSE
                } else {
                    aig_lit balanced_or = build_or_tree(or_children);
                    pos = ~balanced_or;
                }
            }
        }

        if (!pos.node) pos = make_canonical(l, r);
        cache[src] = pos;
        stack.pop_back();
    }

    auto it = cache.find(edge.get());
    aig_lit cached = (it != cache.end()) ? it->second : aig_lit();
    return aig_lit(cached.node, cached.neg ^ edge.neg);
}

// ========== Main rewrite entry points ==========

aig_ptr AIGRewriter::rewrite(const aig_ptr& aig) {
    if (!aig) return nullptr;
    struct_hash.clear();
    lit_hash.clear();
    const_true_node.reset();
    const size_t before = AIG::count_aig_nodes_fast(aig);
    aig_lit result = aig;

    // Fixed-point loop: deep_absorb's k-ary flattening can expose new local
    // patterns and vice versa. Capped to avoid pathological oscillation.
    constexpr int kMaxIters = 4;
    size_t prev_count = before;
    for (int iter = 0; iter < kMaxIters; iter++) {
        { NodeRebuildMap c; result = simplify_pass(result, c); }
        struct_hash.clear();
        { NodeRebuildMap c; result = hash_cons(result, c); }
        { NodeRebuildMap c; result = deep_absorb(result, c); }
        { NodeRebuildMap c; result = flatten_ite_chains(result, c); }
        struct_hash.clear();
        { NodeRebuildMap c; result = hash_cons(result, c); }
        const size_t cur_count = AIG::count_aig_nodes_fast(result);
        if (cur_count >= prev_count) break;
        prev_count = cur_count;
    }
    stats.total_passes++;
    SLOW_DEBUG_DO(slow_assert_equiv(aig, result));
    if (AIG::count_aig_nodes_fast(result) > before) return aig;
    return result;
}

void AIGRewriter::rewrite_all(vector<aig_ptr>& defs, int verb) {
    const double t = cpuTime();
    stats.clear();
    struct_hash.clear();
    lit_hash.clear();
    const_true_node.reset();
    stats.nodes_before = AIG::count_aig_nodes_fast(defs);

    vector<aig_ptr> originals = defs;

    constexpr int kMaxIters = 4;
    size_t prev_count = stats.nodes_before;
    for (int iter = 0; iter < kMaxIters; iter++) {
        { NodeRebuildMap cache;
          for (auto& d : defs) if (d) d = simplify_pass(d, cache); }
        { NodeRebuildMap cache;
          for (auto& d : defs) if (d) d = deep_absorb(d, cache); }
        { NodeRebuildMap cache;
          for (auto& d : defs) if (d) d = flatten_ite_chains(d, cache); }
        // hash_cons last so new ANDs from OR/resolution rewrites also share.
        { struct_hash.clear();
          NodeRebuildMap cache;
          for (auto& d : defs) if (d) d = hash_cons(d, cache); }
        const size_t cur_count = AIG::count_aig_nodes_fast(defs);
        if (cur_count >= prev_count) break;
        prev_count = cur_count;
    }
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
