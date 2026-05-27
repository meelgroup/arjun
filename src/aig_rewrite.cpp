/*
 Arjun - AIG Rewriting System

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#include "aig_rewrite.h"
#include "constants.h"
#include "metasolver.h"
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

// Collect every t_lit variable reachable from `e`. Memoised on node identity:
// rebuilt defs are diamond-shared DAGs, so a tree-style walk visits shared
// subgraphs exponentially often on adversarial inputs.
void collect_leaf_vars(const aig_ptr& e, std::unordered_set<uint32_t>& out_vars) {
    std::unordered_set<const AIG*> seen;
    std::function<void(const AIG*)> rec = [&](const AIG* n) {
        if (!n || !seen.insert(n).second) return;
        if (n->type == AIGT::t_lit) { out_vars.insert(n->var); return; }
        if (n->type == AIGT::t_and) { rec(n->l.get()); rec(n->r.get()); }
    };
    rec(e.get());
}

// Naive Tseitin: one helper per AND, 3 clauses each. Drives the per-class
// SAT check only — the full encoder is overkill here.
CMSat::Lit naive_encode(const aig_lit& edge, ArjunInt::MetaSolver& solver,
                        CMSat::Lit& true_lit, bool& true_lit_set,
                        std::map<aig_lit, CMSat::Lit>& cache)
{
    auto visitor = [&](AIGT type, uint32_t var,
                       const CMSat::Lit* left, const CMSat::Lit* right) -> CMSat::Lit {
        if (type == AIGT::t_const) {
            if (!true_lit_set) {
                solver.new_var();
                true_lit = CMSat::Lit(solver.nVars() - 1, false);
                solver.add_clause({true_lit});
                true_lit_set = true;
            }
            return true_lit;
        }
        if (type == AIGT::t_lit) {
            while (solver.nVars() <= var) solver.new_var();
            return CMSat::Lit(var, false);
        }
        assert(type == AIGT::t_and);
        const CMSat::Lit l = *left;
        const CMSat::Lit r = *right;
        solver.new_var();
        const CMSat::Lit g(solver.nVars() - 1, false);
        solver.add_clause({~g, l});
        solver.add_clause({~g, r});
        solver.add_clause({g, ~l, ~r});
        return g;
    };
    return AIG::transform<CMSat::Lit>(edge, visitor, cache);
}

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
        aig_lit pos;
        assert(l.node && r.node);

        // Fast path: no AND/OR chain to flatten ⇒ use local shortcuts.
        auto is_proper_and = [](const aig_lit& e) {
            return e.node && e->type == AIGT::t_and && !e.neg && e->l != e->r;
        };
        const bool any_chain = is_proper_and(l) || is_proper_and(r)
                              || is_or(l) || is_or(r);

        if (!any_chain) {
            if (l == r) { stats.idempotent_elim++; pos = l; }
            else if (is_complement(l, r)) { stats.complement_elim++; pos = cached_const(false); }
            else if (l->type == AIGT::t_const) {
                stats.const_prop++;
                pos = l.neg ? cached_const(false) : r;
            } else if (r->type == AIGT::t_const) {
                stats.const_prop++;
                pos = r.neg ? cached_const(false) : l;
            } else {
                pos = make_canonical(l, r);
            }
        } else {
            // Collect flat AND conjuncts.
            vector<aig_lit> children;
            collect_and_edges(l, children);
            collect_and_edges(r, children);

            std::sort(children.begin(), children.end(), aig_lit_nid_less);
            children.erase(std::unique(children.begin(), children.end()), children.end());

            constexpr size_t kWide = 16;
            const bool wide = children.size() > kWide;

            // Complementary pair ⇒ AND = FALSE. Sorted keys put same-node
            // entries adjacent, so a linear scan suffices.
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

            // Constants: drop TRUE, any FALSE ⇒ collapse.
            if (!folded_false) {
                vector<aig_lit> tmp;
                tmp.reserve(children.size());
                for (const auto& c : children) {
                    if (c->type == AIGT::t_const) {
                        stats.const_prop++;
                        if (c.neg) { folded_false = true; break; }
                    } else {
                        tmp.push_back(c);
                    }
                }
                if (!folded_false) children = std::move(tmp);
            }

            if (folded_false) {
                pos = cached_const(false);
            } else if (children.empty()) {
                pos = cached_const(true);
            } else {
                // Wide: O(n) hash-set pass of OR-absorption only —
                // skip the O(n²) loops below.
                if (wide) {
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

                // Cross-level absorption / subsumption with OR children.
                bool changed = !wide;
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
                                pos = cached_const(false);
                                break;
                            }
                            children[i] = build_or_tree(new_disj);
                            changed = true;
                        }
                    }
                }

                // Resolution on OR pairs: AND(OR(X,b), OR(X,~b)) = X.
                if (!pos.node && !wide) {
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

                if (!pos.node) {
                    std::sort(children.begin(), children.end(), aig_lit_nid_less);
                    children.erase(std::unique(children.begin(), children.end()), children.end());
                    if (children.empty()) pos = cached_const(true);
                    else pos = build_and_tree(children);
                }
            }
        }
        cache[src] = pos;
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

// ========== SAT sweeping (FRAIG-lite) ==========
//
// Identify functionally equivalent AND nodes across `defs` and merge them.
//   1. Simulate each node on random 64-bit patterns. Same signature (possibly
//      after complementing one) ⇒ candidate-equivalent.
//   2. SAT-verify each candidate merge (miter UNSAT ⇒ commit).
//   3. Rebuild defs through make_canonical so structural sharing recovers
//      after merges.

struct AIGRewriter::SweepState {
    std::unordered_map<const AIG*, aig_node_ptr> raw_to_shared;
    std::vector<const AIG*> topo;
    std::set<uint32_t> used_vars;
    std::unordered_map<const AIG*, std::vector<uint64_t>> sigs;
    uint32_t rounds = 0;

    struct Key {
        std::vector<uint64_t> data;
        bool operator==(const Key& o) const { return data == o.data; }
    };
    struct KeyHash {
        size_t operator()(const Key& k) const noexcept {
            size_t h = 0xcbf29ce484222325ULL;
            for (uint64_t w : k.data) { h ^= w; h *= 0x100000001b3ULL; }
            return h;
        }
    };
    std::unordered_map<Key, std::vector<std::pair<const AIG*, bool>>, KeyHash> classes;

    std::unordered_map<const AIG*, bool> const_sub;
    std::unordered_map<const AIG*, std::pair<const AIG*, bool>> sub;
};

void AIGRewriter::sweep_collect_topology(const vector<aig_ptr>& defs, SweepState& st) {
    // Post-order DFS, keeping owning shared_ptrs so rebuild can't have its
    // inputs freed out from under it when defs[] is mutated.
    std::function<void(const aig_ptr&)> dfs = [&](const aig_ptr& e) {
        if (!e) return;
        if (st.raw_to_shared.count(e.get())) return;
        st.raw_to_shared[e.get()] = e.node;
        if (e->type == AIGT::t_and) {
            dfs(e->l);
            if (e->r.get() != e->l.get()) dfs(e->r);
        }
        st.topo.push_back(e.get());
    };
    for (const auto& r : defs) dfs(r);
    for (const auto* n : st.topo) {
        if (n->type == AIGT::t_lit) st.used_vars.insert(n->var);
    }
}

void AIGRewriter::sweep_simulate(SweepState& st) {
    // Adaptive depth: +4 rounds per 4× past 256 nodes, capped at 48. More
    // rounds = fewer bogus candidate classes at linear sim cost.
    uint32_t R = sweep_sim_rounds;
    for (size_t t = st.topo.size(); t > 256 && R < 48; t >>= 2) R += 4;
    st.rounds = R;

    std::mt19937_64 rng(0xA11CEULL);
    std::unordered_map<uint32_t, vector<uint64_t>> var_pats;
    // Round 0 = all-zero / all-one / one-hot rows; splits near-constant and
    // single-variable-sensitive nodes that pure-random sim lumps together.
    uint32_t var_idx = 0;
    for (uint32_t v : st.used_vars) {
        var_pats[v].resize(R);
        for (uint32_t i = 0; i < R; i++) var_pats[v][i] = rng();
        uint64_t structured = 2ULL;  // bit 1 ⇒ "all variables = 1" row
        if (var_idx < 62) structured |= (1ULL << (var_idx + 2));
        var_pats[v][0] = structured;
        var_idx++;
    }

    // Simulate POSITIVE value of each node; fanin sign flips on the way in.
    st.sigs.reserve(st.topo.size());
    for (const auto* n : st.topo) {
        vector<uint64_t> s(R);
        if (n->type == AIGT::t_const) {
            for (uint32_t i = 0; i < R; i++) s[i] = ~0ULL;
        } else if (n->type == AIGT::t_lit) {
            const auto& p = var_pats[n->var];
            for (uint32_t i = 0; i < R; i++) s[i] = p[i];
        } else {
            const auto& ls = st.sigs.at(n->l.get());
            const auto& rs = st.sigs.at(n->r.get());
            for (uint32_t i = 0; i < R; i++) {
                uint64_t lv = ls[i]; if (n->l.neg) lv = ~lv;
                uint64_t rv = rs[i]; if (n->r.neg) rv = ~rv;
                s[i] = lv & rv;
            }
        }
        st.sigs.emplace(n, std::move(s));
    }
}

void AIGRewriter::sweep_build_classes(SweepState& st, int verb, double start_time) {
    // Canonical sig: flip if round-0 MSB is 1, so x and ~x cluster together.
    auto canonicalize = [&](const vector<uint64_t>& s, bool& flipped) {
        flipped = (s[0] >> 63) & 1ULL;
        if (!flipped) return s;
        vector<uint64_t> out(st.rounds);
        for (uint32_t i = 0; i < st.rounds; i++) out[i] = ~s[i];
        return out;
    };
    // Class AND + literal nodes both: a class containing a literal lets an
    // AND member collapse onto the leaf.
    for (const auto* n : st.topo) {
        if (n->type != AIGT::t_and && n->type != AIGT::t_lit) continue;
        bool flipped;
        SweepState::Key k{canonicalize(st.sigs[n], flipped)};
        st.classes[std::move(k)].emplace_back(n, flipped);
    }

    if (verb >= 2) {
        size_t nontrivial = 0, total_members = 0, max_class = 0;
        for (const auto& [k, m] : st.classes) {
            if (m.size() < 2) continue;
            nontrivial++;
            total_members += m.size();
            if (m.size() > max_class) max_class = m.size();
        }
        cout << "c o [aig-rw/sweep-setup] T:"
             << std::fixed << std::setprecision(2) << (cpuTime() - start_time)
             << " topo=" << st.topo.size()
             << " used_v=" << st.used_vars.size()
             << " cls=" << st.classes.size()
             << " cls_nt=" << nontrivial
             << " mem_nt=" << total_members
             << " max_cls=" << max_class
             << endl;
    }
}

void AIGRewriter::sweep_find_constants(SweepState& st) {
    // SAT-prove nodes whose entire sim signature is uniform 0 or 1. Catches
    // multi-level contradictions/tautologies that structural rules miss.
    ArjunInt::MetaSolver solver;
    solver.set_verbosity(0);
    CMSat::Lit true_lit;
    bool true_lit_set = false;
    std::map<aig_lit, CMSat::Lit> enc_cache;
    if (!st.used_vars.empty()) {
        const uint32_t maxv = *std::max_element(st.used_vars.begin(), st.used_vars.end());
        solver.new_vars(maxv + 1);
    }
    auto to_edge = [&](const AIG* n) -> aig_lit {
        return aig_lit(st.raw_to_shared.at(n), false);
    };
    for (const auto* n : st.topo) {
        if (n->type != AIGT::t_and) continue;
        const auto& s = st.sigs[n];
        bool all0 = true, all1 = true;
        for (uint64_t w : s) {
            if (w != 0ULL)  all0 = false;
            if (w != ~0ULL) all1 = false;
        }
        if (!all0 && !all1) continue;
        const bool cand_val = all1;
        stats.sweep_sat_checks++;
        const CMSat::Lit nl = naive_encode(to_edge(n), solver,
            true_lit, true_lit_set, enc_cache);
        solver.set_max_confl(sweep_conflict_budget);
        // node ≡ cand_val  ⟺  asserting node ≠ cand_val is UNSAT.
        std::vector<CMSat::Lit> assumps{ cand_val ? ~nl : nl };
        const CMSat::lbool res = solver.solve(&assumps);
        if (res == CMSat::l_False) {
            st.const_sub[n] = cand_val;
            stats.sweep_const_merges++;
        } else if (res == CMSat::l_True) {
            stats.sweep_cex_refuted++;
        } else {
            stats.sweep_timeouts++;
        }
    }
}

void AIGRewriter::sweep_verify_classes(SweepState& st, int verb, double start_time) {
    // For each non-singleton class: pick a representative (literal > lowest
    // nid), SAT-verify each other member's equivalence via an activation lit.
    // l_True ⇒ use the cex model to drop other class members that also
    // disagree with the rep (real distinguishing input, not sim coincidence).
    uint64_t classes_processed = 0;
    uint64_t last_progress = 0;
    for (auto& [key, members] : st.classes) {
        if (members.size() < 2) continue;
        const size_t member_cap = std::min<size_t>(members.size(), sweep_max_class_size);
        classes_processed++;
        if (verb >= 2 && classes_processed - last_progress >= 100) {
            cout << "c o [aig-rw/sweep-prog] T:"
                 << std::fixed << std::setprecision(2) << (cpuTime() - start_time)
                 << " cls_done=" << classes_processed
                 << " chk=" << stats.sweep_sat_checks
                 << " m=" << stats.sweep_merges
                 << " r=" << stats.sweep_cex_refuted
                 << " to=" << stats.sweep_timeouts
                 << " ca=" << stats.sweep_class_aborts
                 << endl;
            last_progress = classes_processed;
        }
        stats.sweep_sim_groups++;
        std::sort(members.begin(), members.end(),
            [](const auto& a, const auto& b) {
                const bool al = a.first->type == AIGT::t_lit;
                const bool bl = b.first->type == AIGT::t_lit;
                if (al != bl) return al;
                return a.first->nid < b.first->nid;
            });

        ArjunInt::MetaSolver solver;
        solver.set_verbosity(0);
        CMSat::Lit true_lit;
        bool true_lit_set = false;
        std::map<aig_lit, CMSat::Lit> enc_cache;
        if (!st.used_vars.empty()) {
            const uint32_t maxv = *std::max_element(st.used_vars.begin(), st.used_vars.end());
            solver.new_vars(maxv + 1);
        }
        auto to_edge = [&](const AIG* n) -> aig_lit {
            return aig_lit(st.raw_to_shared.at(n), false);
        };

        const CMSat::Lit rep_lit = naive_encode(to_edge(members[0].first),
            solver, true_lit, true_lit_set, enc_cache);
        const CMSat::Lit rep_canon = members[0].second ? ~rep_lit : rep_lit;

        // Single-pattern eval against one SAT model, memoised per model.
        std::unordered_map<const AIG*, char> ev_memo;
        std::function<bool(const AIG*, const std::vector<CMSat::lbool>&)> eval1 =
            [&](const AIG* n, const std::vector<CMSat::lbool>& model) -> bool {
                auto itm = ev_memo.find(n);
                if (itm != ev_memo.end()) return itm->second != 0;
                bool v;
                if (n->type == AIGT::t_const) v = true;
                else if (n->type == AIGT::t_lit)
                    v = n->var < model.size() && model[n->var] == CMSat::l_True;
                else {
                    bool lv = eval1(n->l.get(), model) ^ n->l.neg;
                    bool rv = eval1(n->r.get(), model) ^ n->r.neg;
                    v = lv && rv;
                }
                ev_memo[n] = v ? 1 : 0;
                return v;
            };
        std::unordered_set<const AIG*> dead;

        uint32_t streak = 0;
        for (size_t i = 1; i < member_cap; i++) {
            const auto& [node, flipped] = members[i];
            // Never rewrite a leaf into a (possibly cyclic) AND cone.
            if (node->type != AIGT::t_and) continue;
            if (st.sub.count(node) || st.const_sub.count(node) || dead.count(node)) continue;

            const CMSat::Lit node_lit = naive_encode(to_edge(node),
                solver, true_lit, true_lit_set, enc_cache);
            const CMSat::Lit node_canon = flipped ? ~node_lit : node_lit;

            solver.new_var();
            const CMSat::Lit act(solver.nVars() - 1, false);
            solver.add_clause({~act, rep_canon, node_canon});
            solver.add_clause({~act, ~rep_canon, ~node_canon});
            vector<CMSat::Lit> assumps{act};
            stats.sweep_sat_checks++;
            solver.set_max_confl(sweep_conflict_budget);
            const CMSat::lbool res = solver.solve(&assumps);
            solver.add_clause({~act});  // retire act either way

            if (res == CMSat::l_False) {
                const bool invert = (flipped != members[0].second);
                st.sub[node] = {members[0].first, invert};
                stats.sweep_merges++;
                streak = 0;
            } else if (res == CMSat::l_True) {
                stats.sweep_cex_refuted++;
                streak++;
                // Drop other class members that disagree with rep on this cex.
                const std::vector<CMSat::lbool>& model = solver.get_model();
                ev_memo.clear();
                const bool rep_val =
                    eval1(members[0].first, model) ^ members[0].second;
                for (size_t j = i + 1; j < member_cap; j++) {
                    const auto& [jn, jflip] = members[j];
                    if (st.sub.count(jn) || st.const_sub.count(jn) || dead.count(jn))
                        continue;
                    if ((eval1(jn, model) ^ jflip) != rep_val) {
                        dead.insert(jn);
                        stats.sweep_cex_filtered++;
                    }
                }
            } else {
                stats.sweep_timeouts++;
                streak++;
            }

            if (streak >= sweep_class_abort_streak) {
                stats.sweep_class_aborts++;
                break;
            }
        }
    }
}

void AIGRewriter::sweep_rebuild_defs(vector<aig_ptr>& defs,
                                     vector<aig_ptr>& orig_defs,
                                     SweepState& st) {
    // Per-source-node positive-value rebuild; caller composes incoming sign.
    // Iterative post-order — recursion blows the stack on deep AIGs.
    std::unordered_map<const AIG*, aig_lit> rebuild;
    auto rebuild_node = [&](const AIG* root) -> aig_lit {
        if (!root) return aig_lit();
        struct Frame { const AIG* n; bool deps_done; };
        std::vector<Frame> stk;
        stk.reserve(64);
        stk.push_back({root, false});
        while (!stk.empty()) {
            Frame& f = stk.back();
            const AIG* n = f.n;
            if (!n || rebuild.count(n)) { stk.pop_back(); continue; }
            if (!f.deps_done) {
                auto it_const = st.const_sub.find(n);
                if (it_const != st.const_sub.end()) {
                    rebuild[n] = cached_const(it_const->second);
                    stk.pop_back();
                    continue;
                }
                auto it_sub = st.sub.find(n);
                if (it_sub != st.sub.end()) {
                    f.deps_done = true;
                    stk.push_back({it_sub->second.first, false});
                    continue;
                }
                if (n->type == AIGT::t_and) {
                    f.deps_done = true;
                    stk.push_back({n->r.get(), false});
                    stk.push_back({n->l.get(), false});
                    continue;
                }
                rebuild[n] = aig_lit(st.raw_to_shared.at(n), false);
                stk.pop_back();
                continue;
            }
            auto it_sub = st.sub.find(n);
            if (it_sub != st.sub.end()) {
                auto& rep_pos = rebuild[it_sub->second.first];
                rebuild[n] = aig_lit(rep_pos.node, rep_pos.neg ^ it_sub->second.second);
            } else {
                assert(n->type == AIGT::t_and);
                auto& lp = rebuild[n->l.get()];
                auto& rp = rebuild[n->r.get()];
                aig_lit l_edge(lp.node, lp.neg ^ n->l.neg);
                aig_lit r_edge(rp.node, rp.neg ^ n->r.neg);
                rebuild[n] = make_canonical(l_edge, r_edge);
            }
            stk.pop_back();
        }
        auto it = rebuild.find(root);
        return (it != rebuild.end()) ? it->second : aig_lit();
    };

    orig_defs = defs;
    // A SAT merge can prove an AND subtree of defs[v] ≡ x_v (since defs[v]
    // literally defines v). After rebuild, make_canonical may collapse that
    // subtree into lit(v) — a definition-level self-loop. Detect & revert.
    for (uint32_t v = 0; v < defs.size(); v++) {
        auto& d = defs[v];
        if (!d) continue;
        aig_lit pos = rebuild_node(d.get());
        aig_ptr new_d(pos.node, pos.neg ^ d.neg);
        std::unordered_set<uint32_t> leaves;
        collect_leaf_vars(new_d, leaves);
        if (leaves.count(v)) { stats.sweep_self_ref_reverts++; continue; }
        d = new_d;
    }
}

void AIGRewriter::sweep_break_cycles(vector<aig_ptr>& defs,
                                     const vector<aig_ptr>& orig_defs) {
    // Cross-def substitution can create indirect cycles like v -> w -> ... -> v
    // that the per-def self-loop check misses. Downstream code infinite-loops
    // on those — DFS, revert one member of every cycle found, repeat.
    auto def_deps = [&](uint32_t v) {
        std::unordered_set<uint32_t> leaves;
        collect_leaf_vars(defs[v], leaves);
        std::vector<uint32_t> defined_deps;
        defined_deps.reserve(leaves.size());
        for (uint32_t u : leaves) {
            if (u < defs.size() && defs[u] != nullptr && u != v)
                defined_deps.push_back(u);
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
        std::function<bool(uint32_t)> dfs_local = [&](uint32_t v) -> bool {
            if (state[v] == 2) return false;
            if (state[v] == 1) {
                auto it = std::find(path.begin(), path.end(), v);
                for (; it != path.end(); ++it) cycle_members.push_back(*it);
                return true;
            }
            state[v] = 1;
            path.push_back(v);
            for (uint32_t u : deps[v]) if (dfs_local(u)) return true;
            path.pop_back();
            state[v] = 2;
            return false;
        };
        bool any_cycle = false;
        for (uint32_t v = 0; v < defs.size(); v++) {
            if (state[v] == 0 && defs[v] != nullptr) {
                path.clear();
                cycle_members.clear();
                if (dfs_local(v)) { any_cycle = true; break; }
            }
        }
        if (!any_cycle) break;

        uint32_t to_revert = std::numeric_limits<uint32_t>::max();
        for (uint32_t m : cycle_members) {
            if (!reverted[m]) { to_revert = m; break; }
        }
        if (to_revert == std::numeric_limits<uint32_t>::max()) {
            // Cycle through already-reverted defs ⇒ orig_defs invariant
            // violated. Fully revert and bail.
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
}

void AIGRewriter::sat_sweep(vector<aig_ptr>& defs, int verb) {
    const double start_time = cpuTime();
    const size_t nodes_before = AIG::count_aig_nodes_fast(defs);

    SweepState st;
    sweep_collect_topology(defs, st);
    sweep_simulate(st);
    sweep_build_classes(st, verb, start_time);
    sweep_find_constants(st);
    sweep_verify_classes(st, verb, start_time);

    std::vector<aig_ptr> orig_defs;
    sweep_rebuild_defs(defs, orig_defs, st);
    sweep_break_cycles(defs, orig_defs);

    SLOW_DEBUG_DO(for (uint32_t v = 0; v < defs.size(); v++)
                      slow_assert_equiv(orig_defs[v], defs[v]));

    if (verb >= 1) {
        const size_t nodes_after = AIG::count_aig_nodes_fast(defs);
        const double pct = nodes_before
            ? 100.0 * (1.0 - (double)nodes_after / (double)nodes_before) : 0.0;
        cout << "c o [aig-rw/sweep] T:"
             << std::fixed << std::setprecision(2) << (cpuTime() - start_time)
             << " n:" << nodes_before << "->" << nodes_after
             << " (-" << std::setprecision(1) << pct << "%)"
             << " g=" << stats.sweep_sim_groups
             << " chk=" << stats.sweep_sat_checks
             << " m=" << stats.sweep_merges
             << " cm=" << stats.sweep_const_merges
             << " r=" << stats.sweep_cex_refuted
             << " cxf=" << stats.sweep_cex_filtered
             << " to=" << stats.sweep_timeouts
             << " ca=" << stats.sweep_class_aborts
             << " be=" << stats.sweep_budget_exhausted
             << " srv=" << stats.sweep_self_ref_reverts
             << " cyc=" << stats.sweep_cycle_reverts
             << endl;
    }
}
