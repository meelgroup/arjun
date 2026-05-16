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

#ifdef SLOW_DEBUG
// Brute-force functional equivalence check. Enumerates every assignment over
// the (≤ kMaxVars) primary-input variables referenced by `a` or `b` and
// asserts the two AIGs agree everywhere. Skipped for wider AIGs — the
// rewriter's fuzzers cover those. Used to catch a rewrite rule that changes
// the function the instant it fires, instead of much later downstream.
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
    cout << "c o [aig-rewrite] nodes: " << nodes_before << " -> " << nodes_after
         << " (" << std::fixed << std::setprecision(1)
         << (nodes_before > 0 ? (1.0 - (double)nodes_after / nodes_before) * 100.0 : 0.0) << "% reduction)"
         << "  passes: " << total_passes
         << "  const_prop: " << const_prop
         << "  complement: " << complement_elim
         << "  idempotent: " << idempotent_elim
         << "  absorption: " << absorption
         << "  distrib: " << and_or_distrib
         << "  xor_simp: " << xor_simplify
         << "  hash_hits: " << structural_hash_hits
         << endl;
}

void AIGRewriteStats::clear() { *this = AIGRewriteStats(); }

// ========== Helpers ==========

// Return a hash-consed signed edge for variable `var`. The first call for
// each variable allocates the backing t_lit node; subsequent calls reuse it.
// This is what makes structural equality (`a == b` on aig_lits) reliable
// across all rewrites within a single rewrite_all() pass — without it, the
// rebuilder produces a fresh t_lit per occurrence and rules like
// AND(a, AND(~a, b)) = FALSE silently fall off the table.
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
        pos = cached_const(true);
    } else if (edge->type == AIGT::t_lit) {
        pos = cached_lit(edge->var, false);
    } else {
        assert(edge->type == AIGT::t_and);
        const aig_lit l = simplify_pass(edge->l, cache);
        const aig_lit r = simplify_pass(edge->r, cache);

        if (l->type == AIGT::t_const) {
            stats.const_prop++;
            pos = l.neg ? cached_const(false) : r;  // FALSE∧x=FALSE, TRUE∧x=x
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

        // Complementary absorption: AND(a, AND(~a, b)) = FALSE — fires when
        // simplify_pass has hash-consed literals so `is_complement` resolves
        // structurally. The bare AND(a, AND(a, b)) absorption rule below
        // covers the positive case; this one catches the contradiction.
        if (!pos && r->type == AIGT::t_and && !r.neg) {
            if (is_complement(r->l, l) || is_complement(r->r, l)) {
                stats.complement_elim++;
                pos = cached_const(false);
            }
        }
        if (!pos && l->type == AIGT::t_and && !l.neg) {
            if (is_complement(l->l, r) || is_complement(l->r, r)) {
                stats.complement_elim++;
                pos = cached_const(false);
            }
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
            // OR-disjunct context drill: under outer AND with sibling l, if
            // d_i is an AND containing l as a fanin, d_i reduces to its other
            // fanin (BCP via l). If d_i contains ~l, d_i = FALSE and the
            // OR collapses to the other disjunct.
            //
            //   AND(a, OR(AND(a, x), d2))   = AND(a, OR(x, d2))
            //   AND(a, OR(AND(~a, x), d2))  = AND(a, d2)
            auto try_disj_drill = [&](const aig_lit& d, const aig_lit& other_d) -> aig_lit {
                if (!d.node || d->type != AIGT::t_and || d.neg) return aig_lit();
                if (is_complement(d->l, l) || is_complement(d->r, l)) {
                    stats.complement_elim++;
                    return make_canonical(l, other_d);
                }
                aig_lit x;
                if (d->l == l) x = d->r;
                else if (d->r == l) x = d->l;
                if (x.node) {
                    stats.absorption++;
                    // AND(l, OR(x, other_d)) — OR encoded as ~AND(~x, ~other_d).
                    aig_lit new_or = ~make_canonical(~x, ~other_d);
                    return make_canonical(l, new_or);
                }
                return aig_lit();
            };
            if (!pos) pos = try_disj_drill(d1, d2);
            if (!pos) pos = try_disj_drill(d2, d1);

            if (!pos && l->type == AIGT::t_and && !l.neg) {
                // OR-vs-AND-fanin drill-down (ABC's
                // AND(p0, ~AND(C,D)) for p0 a positive AND case):
                //   AND(AND(la, lb), OR(d1, d2)) where some d_i matches a
                //   fanin of l: the OR is implied by l, drop OR  →  l.
                //   Symmetric to deep_absorb's k-ary absorption check, but
                //   fires before flattening so iteration converges faster.
                if (d1 == l->l || d1 == l->r || d2 == l->l || d2 == l->r) {
                    stats.absorption++;
                    pos = l;
                } else if (is_complement(d1, l->l) || is_complement(d1, l->r)) {
                    // d1 is the complement of a fanin of l: under l, d1=false
                    // so OR reduces to d2. AND becomes AND(l, d2).
                    stats.complement_elim++;
                    pos = make_canonical(l, d2);
                } else if (is_complement(d2, l->l) || is_complement(d2, l->r)) {
                    stats.complement_elim++;
                    pos = make_canonical(l, d1);
                }
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
            // OR-disjunct context drill, symmetric to the is_or(r) variant.
            auto try_disj_drill_l = [&](const aig_lit& d, const aig_lit& other_d) -> aig_lit {
                if (!d.node || d->type != AIGT::t_and || d.neg) return aig_lit();
                if (is_complement(d->l, r) || is_complement(d->r, r)) {
                    stats.complement_elim++;
                    return make_canonical(r, other_d);
                }
                aig_lit x;
                if (d->l == r) x = d->r;
                else if (d->r == r) x = d->l;
                if (x.node) {
                    stats.absorption++;
                    aig_lit new_or = ~make_canonical(~x, ~other_d);
                    return make_canonical(r, new_or);
                }
                return aig_lit();
            };
            if (!pos) pos = try_disj_drill_l(d1, d2);
            if (!pos) pos = try_disj_drill_l(d2, d1);

            if (!pos && r->type == AIGT::t_and && !r.neg) {
                if (d1 == r->l || d1 == r->r || d2 == r->l || d2 == r->r) {
                    stats.absorption++;
                    pos = r;
                } else if (is_complement(d1, r->l) || is_complement(d1, r->r)) {
                    stats.complement_elim++;
                    pos = make_canonical(r, d2);
                } else if (is_complement(d2, r->l) || is_complement(d2, r->r)) {
                    stats.complement_elim++;
                    pos = make_canonical(r, d1);
                }
            }
        }

        // XOR pattern observation on the OR-of-two-ANDs shape.
        //
        // The stored shape `pos = AND(~AND_A, ~AND_B)` decodes as
        // OR(AND_A, AND_B). XOR(p, q) = OR(AND(p, ~q), AND(~p, q)) lands
        // here with both inner ANDs non-degenerate. ITE-folds (ITE(s, s, e),
        // ITE(s, ~s, e), ITE(s, t, s), ITE(s, t, ~s)) never reach this point:
        //   - new_and folds AND(s, s) -> s at construction;
        //   - the is_or(r) / is_or(l) branches above catch the residual
        //     AND(~s, ~AND(~s, e)) = AND(~s, ~e) pattern earlier.
        // So the only useful thing to do here is count XOR observations
        // (it bumps xor_simplify so the fuzzer can verify the corpus hits
        // XOR shapes). No structural rewrite -- XOR is irreducible without
        // going to a wider rewrite step.
        if (!pos && l->type == AIGT::t_and && l.neg
                 && r->type == AIGT::t_and && r.neg) {
            const aig_lit& la = l->l, lb = l->r;
            const aig_lit& ra = r->l, rb = r->r;
            int compl_pairs = 0;
            if (is_complement(la, ra)) compl_pairs++;
            if (is_complement(la, rb)) compl_pairs++;
            if (is_complement(lb, ra)) compl_pairs++;
            if (is_complement(lb, rb)) compl_pairs++;
            if (compl_pairs >= 2) stats.xor_simplify++;
        }

        // AND-of-AND structural rewrites (Brummayer/Biere MEMICS'06 patterns
        // adapted from ABC's Aig_And, edge-signed AIG variant).
        //   AND(AND(A,B), AND(C,D)) collapses to FALSE if any pair of fanins
        //     across the two inner ANDs is complementary — the conjunction
        //     has the form x ∧ ¬x ∧ ... = FALSE. Catches XOR-AND pairs,
        //     AND(AND(p,¬q), AND(¬p,q)) and any other 4-fanin contradiction
        //     that deep_absorb would otherwise have to flatten to spot.
        //   AND(AND(A,B), AND(C,D)) with a shared fanin (A==C, A==D, B==C,
        //     or B==D) factors as AND(shared, AND(other_l, other_r)).
        //     Node count is unchanged but the new inner AND hash-conses
        //     against a possibly-existing AND(other_l, other_r); the shared
        //     fanin is lifted to the top so further outer-level rewrites
        //     can see it.
        if (!pos && l->type == AIGT::t_and && !l.neg
                 && r->type == AIGT::t_and && !r.neg) {
            const aig_lit la = l->l, lb = l->r;
            const aig_lit ra = r->l, rb = r->r;
            if (is_complement(la, ra) || is_complement(la, rb)
             || is_complement(lb, ra) || is_complement(lb, rb)) {
                stats.complement_elim++;
                pos = cached_const(false);
            } else {
                aig_lit shared, ol, ortmp;
                if      (la == ra) { shared = la; ol = lb; ortmp = rb; }
                else if (la == rb) { shared = la; ol = lb; ortmp = ra; }
                else if (lb == ra) { shared = lb; ol = la; ortmp = rb; }
                else if (lb == rb) { shared = lb; ol = la; ortmp = ra; }
                if (shared.node) {
                    stats.absorption++;
                    pos = make_canonical(shared, make_canonical(ol, ortmp));
                }
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
        pos = cached_const(true);
    } else {
        pos = cached_lit(edge->var, false);
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
        if (edge->type == AIGT::t_const) pos = cached_const(true);
        else pos = cached_lit(edge->var, false);
    } else {
        const aig_lit l = deep_absorb(edge->l, cache);
        const aig_lit r = deep_absorb(edge->r, cache);
        assert(l.node && r.node);  // t_and children are always non-null

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
                pos = cached_const(false);
            } else if (children.empty()) {
                pos = cached_const(true);
            } else {
                // Wide groups skip the O(n²) absorption/resolution loops
                // below, but a single hash-set pass of OR absorption is only
                // O(n + Σdisjuncts): drop any OR child one of whose disjuncts
                // equals an AND sibling — AND(a, OR(a, …)) = a.
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

                        // OR-vs-OR subset subsumption: a narrower OR implies a
                        // wider one whose disjuncts are a superset, so under
                        // the AND the wider OR is redundant — drop it.
                        //   AND(OR(a,b,c), OR(a,b)) = OR(a,b)
                        std::sort(disj.begin(), disj.end(), aig_lit_nid_less);
                        bool dropped_wide = false;
                        for (size_t j = 0; j < children.size() && !dropped_wide; j++) {
                            if (i == j || !is_or(children[j])) continue;
                            vector<aig_lit> dj;
                            collect_or_edges(children[j], dj);
                            if (dj.size() >= disj.size()) continue;  // j not narrower
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
                                pos = cached_const(false);
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
                    if (children.empty()) pos = cached_const(true);
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
        if (edge->type == AIGT::t_const) pos = cached_const(true);
        else pos = cached_lit(edge->var, false);
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
            if (folded_false) pos = cached_const(false);
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
                    pos = cached_const(false);
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
    lit_hash.clear();
    const_true_node.reset();
    const size_t before = AIG::count_aig_nodes_fast(aig);
    aig_lit result = aig;

    // Iterate to a fixed point: deep_absorb's k-ary flattening + complement
    // dedup can expose new patterns the local simplify_pass rules would
    // catch, which in turn enables further deep_absorb folds. Cap the loop
    // at a small constant — in practice convergence is fast (1-2 extra
    // iterations) and we don't want to pay for runaway oscillation on
    // adversarial inputs.
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

    // Snapshot originals so we can revert any def that grew.
    vector<aig_ptr> originals = defs;

    // Iterate to a fixed point — same rationale as the single-AIG rewrite
    // entry point. Bounded at kMaxIters to avoid pathological oscillation.
    constexpr int kMaxIters = 4;
    size_t prev_count = stats.nodes_before;
    for (int iter = 0; iter < kMaxIters; iter++) {
        {
            NodeRebuildMap cache;
            for (auto& d : defs) if (d) d = simplify_pass(d, cache);
        }
        {
            // deep_absorb handles k-ary AND/OR flattening, multi-level
            // absorption / resolution that simplify_pass's local rules miss.
            NodeRebuildMap cache;
            for (auto& d : defs) if (d) d = deep_absorb(d, cache);
        }
        {
            // flatten_ite_chains rebalances long AND / OR chains (common
            // from manthan's ITE-repair output) as balanced trees.
            NodeRebuildMap cache;
            for (auto& d : defs) if (d) d = flatten_ite_chains(d, cache);
        }
        {
            // hash_cons makes the AIG share structure across defs; run it
            // last so any new ANDs created by the OR / resolution rewrites
            // also hash-cons.
            struct_hash.clear();
            NodeRebuildMap cache;
            for (auto& d : defs) if (d) d = hash_cons(d, cache);
        }
        const size_t cur_count = AIG::count_aig_nodes_fast(defs);
        if (cur_count >= prev_count) break;
        prev_count = cur_count;
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
    SLOW_DEBUG_DO(for (size_t i = 0; i < defs.size(); i++)
                      slow_assert_equiv(originals[i], defs[i]));

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

void AIGRewriter::sat_sweep(vector<aig_ptr>& defs, int verb) {
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
    // Adaptive simulation depth. Two non-equivalent nodes that happen to
    // agree on every random pattern land in the same candidate class and
    // cost a wasted SAT check; the more nodes a sweep covers, the more such
    // coincidences arise, so scale the round count (each round = 64 patterns)
    // up with topology size. +4 rounds per 4× growth past 256 nodes, capped.
    uint32_t R = sweep_sim_rounds;
    for (size_t t = topo.size(); t > 256 && R < 48; t >>= 2) R += 4;
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
    // Both AND and literal nodes are classed: a class with a literal lets an
    // AND node functionally equal to that literal merge straight onto the
    // leaf (only ANDs are ever substituted — see the member loop below).
    std::unordered_map<Key, vector<std::pair<const AIG*, bool>>, KeyHash> classes;
    for (const auto* n : topo) {
        if (n->type != AIGT::t_and && n->type != AIGT::t_lit) continue;
        bool flipped;
        Key k{canonicalize(sigs[n], flipped)};
        classes[std::move(k)].emplace_back(n, flipped);
    }

    if (verb >= 2) {
        size_t nontrivial = 0, total_members = 0, max_class = 0;
        for (const auto& [k, m] : classes) {
            if (m.size() < 2) continue;
            nontrivial++;
            total_members += m.size();
            if (m.size() > max_class) max_class = m.size();
        }
        cout << "c o [aig-rewrite] sat-sweep setup T: "
             << std::fixed << std::setprecision(2) << (cpuTime() - start_time)
             << "  topo=" << topo.size()
             << "  used_vars=" << used_vars.size()
             << "  classes_total=" << classes.size()
             << "  classes_nontrivial=" << nontrivial
             << "  total_nontrivial_members=" << total_members
             << "  max_class=" << max_class
             << endl;
    }

    // --- Constant-node detection -------------------------------------------
    // A node whose entire simulation signature is uniformly 0 (resp. 1) is a
    // candidate constant. SAT-verify (the negated value must be UNSAT) and,
    // on success, substitute the AIG constant — make_canonical then folds the
    // whole cone away on rebuild. This is the cheap half of FRAIG's constant
    // sweep and catches multi-level contradictions/tautologies that the
    // structural rules cannot see.
    std::unordered_map<const AIG*, bool> const_sub;  // node -> proven value
    {
        CMSat::SATSolver csolver;
        csolver.set_verbosity(0);
        CMSat::Lit c_true_lit;
        bool c_true_set = false;
        std::map<aig_lit, CMSat::Lit> c_enc_cache;
        if (!used_vars.empty()) {
            const uint32_t maxv = *std::max_element(used_vars.begin(), used_vars.end());
            csolver.new_vars(maxv + 1);
        }
        auto to_edge = [&](const AIG* n) -> aig_lit {
            return aig_lit(raw_to_shared.at(n), false);
        };
        for (const auto* n : topo) {
            if (n->type != AIGT::t_and) continue;
            const auto& s = sigs[n];
            bool all0 = true, all1 = true;
            for (uint64_t w : s) {
                if (w != 0ULL)   all0 = false;
                if (w != ~0ULL)  all1 = false;
            }
            if (!all0 && !all1) continue;
            const bool cand_val = all1;
            stats.sweep_sat_checks++;
            const CMSat::Lit nl = naive_encode(to_edge(n), csolver,
                c_true_lit, c_true_set, c_enc_cache);
            csolver.set_max_confl(sweep_conflict_budget);
            // node ≡ cand_val ⟺ asserting node ≠ cand_val is UNSAT.
            std::vector<CMSat::Lit> assumps{ cand_val ? ~nl : nl };
            const CMSat::lbool res = csolver.solve(&assumps);
            if (res == CMSat::l_False) {
                const_sub[n] = cand_val;
                stats.sweep_const_merges++;
            } else if (res == CMSat::l_True) {
                stats.sweep_cex_refuted++;
            } else {
                stats.sweep_timeouts++;
            }
        }
    }

    // SAT-verify each non-singleton class against its lowest-nid
    // representative. An activation literal per-check lets us reuse one
    // solver for the whole class.
    std::unordered_map<const AIG*, std::pair<const AIG*, bool>> sub;
    bool time_exhausted = false;
    uint64_t classes_processed = 0;
    uint64_t last_progress_print_classes = 0;
    for (auto& [key, members] : classes) {
        if (members.size() < 2) continue;
        // Oversized classes used to be skipped wholesale. With the constant
        // detection pass draining the degenerate all-constant groups and the
        // counterexample filter culling simulation false-positives, it is
        // worth processing them — but still only the first sweep_max_class_size
        // members so worst-case SAT churn stays bounded.
        const size_t member_cap = std::min<size_t>(members.size(),
                                                    sweep_max_class_size);
        classes_processed++;
        if (verb >= 2 && classes_processed - last_progress_print_classes >= 100) {
            cout << "c o [aig-rewrite] sat-sweep progress"
                 << "  T: " << std::fixed << std::setprecision(2)
                 << (cpuTime() - start_time)
                 << "  classes_done=" << classes_processed
                 << "  checks=" << stats.sweep_sat_checks
                 << "  merges=" << stats.sweep_merges
                 << "  refuted=" << stats.sweep_cex_refuted
                 << "  timeouts=" << stats.sweep_timeouts
                 << "  class_aborts=" << stats.sweep_class_aborts
                 << endl;
            last_progress_print_classes = classes_processed;
        }
        stats.sweep_sim_groups++;
        // Representative = members[0]. Prefer a literal (so AND members can
        // collapse onto the leaf), then lowest nid for determinism.
        std::sort(members.begin(), members.end(),
            [](const auto& a, const auto& b) {
                const bool al = a.first->type == AIGT::t_lit;
                const bool bl = b.first->type == AIGT::t_lit;
                if (al != bl) return al;
                return a.first->nid < b.first->nid;
            });

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

        // Single-pattern AIG evaluation under a SAT counterexample model,
        // memoised on node identity for one model. Used for FRAIG-style
        // counterexample feedback: a refuting model is a real distinguishing
        // input, so any other class member that disagrees with the
        // representative on it cannot be equivalent and need not be checked.
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
        std::unordered_set<const AIG*> dead;  // members a cex has refuted

        uint32_t streak = 0;  // consecutive non-merge results in this class
        for (size_t i = 1; i < member_cap; i++) {
            const auto& [node, flipped] = members[i];
            // Only AND nodes are ever substituted — never rewrite a leaf
            // literal into a (larger, possibly cyclic) AND cone.
            if (node->type != AIGT::t_and) continue;
            if (sub.count(node) || const_sub.count(node) || dead.count(node)) continue;

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
            // Retire the activation lit either way.
            solver.add_clause({~act});

            if (res == CMSat::l_False) {
                const bool invert = (flipped != members[0].second);
                sub[node] = {members[0].first, invert};
                stats.sweep_merges++;
                streak = 0;
            } else if (res == CMSat::l_True) {
                stats.sweep_cex_refuted++;
                streak++;
                // Counterexample feedback: the model is a genuine input on
                // which `node` and the representative differ. Drop every
                // not-yet-processed member that also disagrees with the rep
                // on it — those are simulation false-positives and would
                // otherwise burn a SAT check each.
                const std::vector<CMSat::lbool>& model = solver.get_model();
                ev_memo.clear();
                const bool rep_val =
                    eval1(members[0].first, model) ^ members[0].second;
                for (size_t j = i + 1; j < member_cap; j++) {
                    const auto& [jn, jflip] = members[j];
                    if (sub.count(jn) || const_sub.count(jn) || dead.count(jn))
                        continue;
                    if ((eval1(jn, model) ^ jflip) != rep_val) {
                        dead.insert(jn);
                        stats.sweep_cex_filtered++;
                    }
                }
            } else {
                // l_Undef: budget exhausted. Treat as "can't prove".
                stats.sweep_timeouts++;
                streak++;
            }

            if (streak >= sweep_class_abort_streak) {
                // Several consecutive non-merges in a row: the class is
                // almost certainly a simulation false-positive. Skip the
                // rest rather than keep paying for SAT.
                stats.sweep_class_aborts++;
                break;
            }
        }
        if (time_exhausted) break;
    }
    if (time_exhausted) stats.sweep_budget_exhausted++;

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
        auto it_const = const_sub.find(n);
        if (it_const != const_sub.end()) {
            // Proven-constant node: emit the shared TRUE node with the edge
            // sign carrying the proven value (neg = !value).
            result = cached_const(it_const->second);
            rebuild[n] = result;
            return result;
        }
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
            result = aig_lit(raw_to_shared.at(n), false);
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
        std::function<bool(uint32_t)> dfs_local = [&](uint32_t v) -> bool {
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
                if (dfs_local(u)) return true;
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
                if (dfs_local(v)) { any_cycle = true; break; }
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

    // Every committed merge / constant fold is a SAT-verified functional
    // equivalence, and any def that gained a definitional cycle was reverted
    // above — so each final def must still compute its original function.
    SLOW_DEBUG_DO(for (uint32_t v = 0; v < defs.size(); v++)
                      slow_assert_equiv(orig_defs[v], defs[v]));

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
             << "  const_merges=" << stats.sweep_const_merges
             << "  refuted=" << stats.sweep_cex_refuted
             << "  cex_filtered=" << stats.sweep_cex_filtered
             << "  timeouts=" << stats.sweep_timeouts
             << "  class_aborts=" << stats.sweep_class_aborts
             << "  budget_exh=" << stats.sweep_budget_exhausted
             << "  self_ref_reverts=" << stats.sweep_self_ref_reverts
             << "  cycle_reverts=" << stats.sweep_cycle_reverts
             << endl;
    }
}
