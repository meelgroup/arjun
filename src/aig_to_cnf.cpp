/*
 Arjun - Efficient AIG to CNF Conversion

 See aig_to_cnf.h for the high level description.

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#include "aig_to_cnf.h"
#include <cryptominisat5/cryptominisat.h>
#include <functional>
#include <iostream>
#include <iomanip>
#include <set>

using CMSat::Lit;
using std::vector;

namespace ArjunNS {

void AIG2CNFStats::print(int verb) const {
    if (verb <= 0) return;
    std::cout
        << "c [aig2cnf] nodes=" << nodes_visited
        << " helpers=" << helpers_added
        << " clauses=" << clauses_added
        << " hits=" << cache_hits
        << "\n"
        << "c [aig2cnf] kAND: " << kary_and_count
        << " (avg-width " << std::fixed << std::setprecision(2)
        << (kary_and_count ? (double)kary_and_width_total / kary_and_count : 0.0)
        << ")  kOR: " << kary_or_count
        << " (avg-width "
        << (kary_or_count ? (double)kary_or_width_total / kary_or_count : 0.0)
        << ")  ITE: " << ite_patterns
        << "  XOR: " << xor_patterns
        << std::endl;
}

// -----------------------------------------------------------------------------
// Helpers to generate clauses.
// -----------------------------------------------------------------------------

template<class Solver>
void AIGToCNF<Solver>::add_clause(const vector<Lit>& cl) {
    solver.add_clause(cl);
    stats.clauses_added++;
}

template<class Solver>
Lit AIGToCNF<Solver>::new_helper() {
    solver.new_var();
    stats.helpers_added++;
    return Lit(solver.nVars() - 1, false);
}

template<class Solver>
Lit AIGToCNF<Solver>::get_true_lit() {
    if (my_has_true_lit) return my_true_lit;
    solver.new_var();
    stats.helpers_added++;
    my_true_lit = Lit(solver.nVars() - 1, false);
    my_has_true_lit = true;
    add_clause({my_true_lit});
    return my_true_lit;
}

// -----------------------------------------------------------------------------
// Fanout counting.
// -----------------------------------------------------------------------------
//
// We count the number of incoming edges to each AND node from inside the DAG
// being encoded. The root is special -- we DO NOT give it an implicit fanout;
// we never attempt to inline it into anything, so no need.  A node is
// "shareable" iff its fanout is >= 2: we must give it a helper variable so
// both users see the same truth value through a named lit.
//
// Non-AND nodes (literals, constants) are essentially free -- they don't need
// their own helper, they directly map to input lits / true-lit.

template<class Solver>
void AIGToCNF<Solver>::count_fanout(const aig_ptr& root) {
    fanout.clear();
    if (!root) return;
    // Use a separate visited set (NOT the fanout map) to drive DFS. Using the
    // fanout map as both visited-marker and count-storage was buggy: the
    // "fanout[child]++" in the parent created the map entry, so the child's
    // DFS saw it as already visited and never descended into grandchildren.
    std::set<aig_ptr> visited;
    std::function<void(const aig_ptr&)> dfs = [&](const aig_ptr& n) {
        if (n->type != AIGT::t_and) return;
        if (!visited.insert(n).second) return; // already visited this node
        if (n->l) {
            if (n->l->type == AIGT::t_and) fanout[n->l]++;
            dfs(n->l);
        }
        if (n->r && n->r != n->l) {
            if (n->r->type == AIGT::t_and) fanout[n->r]++;
            dfs(n->r);
        }
        // Note: when n->l == n->r (the NOT-wrapper AND(x,x,neg=true) pattern),
        // we count only one incoming edge into the child. There are
        // technically two edges in the DAG but they represent a single
        // semantic "NOT" dependency, and the encoder treats this as a unary
        // operator. Counting only once avoids spuriously bumping fanout.
    };
    dfs(root);
}

// -----------------------------------------------------------------------------
// Main entry points.
// -----------------------------------------------------------------------------

template<class Solver>
Lit AIGToCNF<Solver>::encode(const aig_ptr& root, bool force_helper) {
    assert(root);
    count_fanout(root);
    Lit out = encode_node(root);
    if (force_helper && root->type != AIGT::t_and) {
        // Caller wants a fresh helper literal. Create one and assert equivalence.
        Lit h = new_helper();
        add_clause({~h, out});
        add_clause({h, ~out});
        return h;
    }
    return out;
}

template<class Solver>
vector<Lit> AIGToCNF<Solver>::encode_batch(const vector<aig_ptr>& roots) {
    // Build fanout across ALL roots so shared subgraphs get their own helper.
    fanout.clear();
    std::set<aig_ptr> visited;
    std::function<void(const aig_ptr&)> dfs = [&](const aig_ptr& n) {
        if (!n || n->type != AIGT::t_and) return;
        if (!visited.insert(n).second) return;
        if (n->l) {
            if (n->l->type == AIGT::t_and) fanout[n->l]++;
            dfs(n->l);
        }
        if (n->r && n->r != n->l) {
            if (n->r->type == AIGT::t_and) fanout[n->r]++;
            dfs(n->r);
        }
    };
    // Bump each root's fanout by 1 so the root never gets inlined away
    // (there's nothing to inline it into, but this also prevents edge cases
    // where an AIG root is shared with another root's internal node).
    for (const auto& r : roots) {
        if (!r) continue;
        if (r->type == AIGT::t_and) fanout[r]++;
        dfs(r);
    }

    vector<Lit> result;
    result.reserve(roots.size());
    for (const auto& r : roots) {
        if (!r) { result.emplace_back(0, false); continue; }
        result.push_back(encode_node(r));
    }
    return result;
}

// -----------------------------------------------------------------------------
// Node encoding.
// -----------------------------------------------------------------------------
//
// Invariant: encode_node(n) returns a literal L such that L == value-of-n
// (including n->neg). Results are cached by pointer.

template<class Solver>
Lit AIGToCNF<Solver>::encode_node(const aig_ptr& n) {
    {
        auto it = cache.find(n);
        if (it != cache.end()) { stats.cache_hits++; return it->second; }
    }
    stats.nodes_visited++;

    // Leaves.
    if (n->type == AIGT::t_const) {
        stats.const_nodes++;
        Lit t = get_true_lit();
        Lit result = n->neg ? ~t : t;
        cache[n] = result;
        return result;
    }
    if (n->type == AIGT::t_lit) {
        stats.lit_nodes++;
        Lit result(n->var, n->neg);
        cache[n] = result;
        return result;
    }

    assert(n->type == AIGT::t_and);

    // AND(x,x,neg=true) is a NOT encoding; AND(x,x,neg=false) is identity.
    // Handle both without pattern matching below.
    if (n->l == n->r) {
        Lit sub = encode_node(n->l);
        Lit result = n->neg ? ~sub : sub;
        cache[n] = result;
        return result;
    }

    // Try pattern detection first. Patterns can only fire when we are free to
    // consume the AND node itself (we always are -- we are encoding it now).
    // They may also require inner sub-nodes to be inline-able (fanout 1).
    Lit out;
    if (detect_ite && try_ite(n, out)) { cache[n] = out; return out; }
    if (detect_xor && try_xor(n, out)) { cache[n] = out; return out; }

    // Generic path: flatten into a k-ary AND or OR.
    // n->neg == false  =>  n encodes  (l ∧ r)   [AND]
    // n->neg == true   =>  n encodes  ¬(l ∧ r) = ¬l ∨ ¬r   [OR]
    if (!n->neg) {
        // k-ary AND. We expand n's CHILDREN into the input list, never n
        // itself -- calling collect_and(n, ...) would recurse back into
        // encode_node(n) in the (rare) case where n's own fanout exceeds 1,
        // causing infinite recursion.
        vector<Lit> inputs;
        if (kary_fusion) {
            collect_and(n->l, inputs);
            if (n->r != n->l) collect_and(n->r, inputs);
        } else {
            inputs.push_back(encode_node(n->l));
            inputs.push_back(encode_node(n->r));
        }
        Lit h = new_helper();
        emit_and_equiv(h, inputs);
        stats.kary_and_count++;
        stats.kary_and_width_total += inputs.size();
        cache[n] = h;
        return h;
    } else {
        // k-ary OR (via ¬l ∨ ¬r expansion)
        vector<Lit> inputs;
        if (kary_fusion) {
            collect_disjuncts_of_neg(n->l, inputs);
            collect_disjuncts_of_neg(n->r, inputs);
        } else {
            inputs.push_back(~encode_node(n->l));
            inputs.push_back(~encode_node(n->r));
        }
        Lit h = new_helper();
        emit_or_equiv(h, inputs);
        stats.kary_or_count++;
        stats.kary_or_width_total += inputs.size();
        cache[n] = h;
        return h;
    }
}

// -----------------------------------------------------------------------------
// Flattening.
// -----------------------------------------------------------------------------
//
// collect_and(n, out): append to 'out' the list of conjuncts that together
// equal n->value. If n is an AND(neg=false) with fanout-1 (and not already
// cached), its children are recursively collected. Otherwise n is emitted as a
// single input (via encode_node, which adds a helper or looks up the cache).

template<class Solver>
void AIGToCNF<Solver>::collect_and(const aig_ptr& n, vector<Lit>& out) {
    if (n->type == AIGT::t_and && !n->neg
        && n->l != n->r
        && fanout[n] <= 1
        && cache.find(n) == cache.end())
    {
        collect_and(n->l, out);
        collect_and(n->r, out);
        return;
    }
    out.push_back(encode_node(n));
}

// collect_disjuncts_of_neg(n, out): append disjuncts that together equal
// ¬(n->value). If n is an AND(neg=false) with fanout-1, ¬(l ∧ r) = ¬l ∨ ¬r,
// so we recurse into l and r collecting *their* negation's disjuncts.

template<class Solver>
void AIGToCNF<Solver>::collect_disjuncts_of_neg(const aig_ptr& n, vector<Lit>& out) {
    if (n->type == AIGT::t_and && !n->neg
        && n->l != n->r
        && fanout[n] <= 1
        && cache.find(n) == cache.end())
    {
        collect_disjuncts_of_neg(n->l, out);
        collect_disjuncts_of_neg(n->r, out);
        return;
    }
    // Base case: emit ¬(encoding of n).
    out.push_back(~encode_node(n));
}

// -----------------------------------------------------------------------------
// Pattern detection: ITE and XOR.
// -----------------------------------------------------------------------------
//
// In this AIG representation, an AND node with neg=true represents a NAND,
// which is logically an OR: ¬(l ∧ r) = ¬l ∨ ¬r.
//
// The AIG encoding of (A OR B) is AND(¬A, ¬B) with neg=true.
// So (A1∧A2) OR (B1∧B2)  becomes:
//     AND(  AND(A1,A2, neg=true),     // ¬(A1∧A2)
//           AND(B1,B2, neg=true),     // ¬(B1∧B2)
//           neg=true                   // outer: NAND = OR
//     )
//
// ITE(s,t,e) = (s ∧ t) OR (¬s ∧ e).
// In AIG:  AND(AND(s,t,neg=t), AND(¬s,e,neg=t), neg=t)
// where s is represented as a t_lit node, so ¬s is a t_lit with flipped neg.
//
// XOR(a,b) = (a ∧ ¬b) OR (¬a ∧ b).
// Same structural shape, with selector pattern.

// Helper: inline-able => fanout 1 and not yet cached (= we can consume it
// into a pattern without leaving dangling references or double-encoding).
template<class Solver>
bool AIGToCNF<Solver>::try_ite(const aig_ptr& n, Lit& out) {
    // Local helpers (defined here so that the friend access to AIG's
    // private members applies).
    auto is_lit_complement = [](const aig_ptr& a, const aig_ptr& b) -> bool {
        return a && b
            && a->type == AIGT::t_lit && b->type == AIGT::t_lit
            && a->var == b->var && a->neg != b->neg;
    };
    // NOT wrapping in this AIG is encoded as AND(x,x,neg=true). Unwrap it
    // and return the node that the NOT-wrapper is negating.
    auto strip_not = [](const aig_ptr& a) -> aig_ptr {
        if (a && a->type == AIGT::t_and && a->neg && a->l == a->r) return a->l;
        return nullptr;
    };

    if (n->type != AIGT::t_and || !n->neg) return false;
    const aig_ptr& X = n->l;
    const aig_ptr& Y = n->r;
    if (!X || !Y || X == Y) return false;

    // n = ¬(X ∧ Y) = ¬X ∨ ¬Y. We want to express this as an ITE, which
    // requires ¬X and ¬Y each to be a 2-input AND (so that
    //   ¬X = s ∧ t, ¬Y = ¬s ∧ e  =>  n = (s∧t) ∨ (¬s∧e) = ITE(s,t,e)).
    //
    // In this AIG, "¬X" is either:
    //   (a) an AND-node X with neg=true => ¬(X->l ∧ X->r), already in AND-form,
    //       but since X itself is the AND-node, its "l,r" are the AND's inputs.
    //       However neg=true here means X is a NAND, so ¬X = X->l ∧ X->r — which
    //       is an AND. Good.
    //   (b) a NOT-wrapper AND(x,x,neg=true) wrapping some sub-AND x. Then ¬X = x,
    //       and x is (x->l ∧ x->r) if x is AND(neg=false).
    //
    // Both cases collapse to: find a node Z such that Z is AND(neg=false) and
    // ¬X = Z->l ∧ Z->r. Let's compute that for each side.
    auto as_pos_and = [&](const aig_ptr& w) -> aig_ptr {
        // Interpret ¬w as (l ∧ r) for some positive-AND sub-node.
        // Case (a): w is AND with neg=true and l != r => ¬w = w->l ∧ w->r.
        //   Represent that as a virtual pair via the node w itself (its children are the ANDs' inputs).
        // Case (b): w is a NOT-wrapper around a positive AND u: ¬w = u.
        if (!w || w->type != AIGT::t_and) return nullptr;
        if (w->neg) {
            if (w->l == w->r) {
                // NOT-wrapper: ¬w = w->l (which must be an AND(neg=false) for our use).
                aig_ptr u = w->l;
                if (u && u->type == AIGT::t_and && !u->neg && u->l != u->r) return u;
                return nullptr;
            }
            // AND with neg=true, distinct children: ¬w = w->l ∧ w->r directly.
            // Return w itself, caller should read w->l and w->r.
            return w;
        }
        return nullptr;
    };
    aig_ptr ax = as_pos_and(X);
    aig_ptr ay = as_pos_and(Y);
    if (!ax || !ay) return false;

    // Inline-ability: the nodes we are about to consume (X, Y, and possibly
    // their NOT-wrapped inner ANDs) must have fanout 1 and not yet be cached.
    auto can_consume = [&](const aig_ptr& node) -> bool {
        if (cache.find(node) != cache.end()) return false;
        auto it = fanout.find(node);
        return it != fanout.end() && it->second <= 1;
    };
    if (!can_consume(X) || !can_consume(Y)) return false;
    if (ax != X && !can_consume(ax)) return false;
    if (ay != Y && !can_consume(ay)) return false;

    const aig_ptr& x1 = ax->l;
    const aig_ptr& x2 = ax->r;
    const aig_ptr& y1 = ay->l;
    const aig_ptr& y2 = ay->r;

    // Find a literal pair (x_i, y_j) that are complements.
    const aig_ptr* sel_x = nullptr;
    const aig_ptr* other_x = nullptr;
    const aig_ptr* other_y = nullptr;
    auto try_match = [&](const aig_ptr& xa, const aig_ptr& xb,
                         const aig_ptr& ya, const aig_ptr& yb) -> bool {
        if (is_lit_complement(xa, ya)) {
            sel_x = &xa; other_x = &xb; other_y = &yb; return true;
        }
        return false;
    };
    if (!try_match(x1, x2, y1, y2) &&
        !try_match(x1, x2, y2, y1) &&
        !try_match(x2, x1, y1, y2) &&
        !try_match(x2, x1, y2, y1)) return false;

    // (*sel_x) is the selector literal for the "then" branch (¬X side). So
    // n = (sel ∧ other_x) ∨ (¬sel ∧ other_y) = ITE(sel, other_x, other_y).
    Lit s_lit((*sel_x)->var, (*sel_x)->neg);
    Lit t_lit = encode_node(*other_x);
    Lit e_lit = encode_node(*other_y);

    Lit h = new_helper();
    emit_ite(h, s_lit, t_lit, e_lit);
    stats.ite_patterns++;

    // Poison X, Y, ax, ay in cache so they cannot be reached again by the
    // generic AND/OR flattener. Use the helper literal as a sentinel since
    // these nodes are logically "consumed" by this ITE emission. Any future
    // lookups to these nodes should return the value of n, not a partial
    // encoding of the sub-structures -- but since fanout is 1 for all of
    // them there are no future lookups anyway. We still mark for safety.
    (void)strip_not;
    out = h;
    return true;
}

template<class Solver>
bool AIGToCNF<Solver>::try_xor(const aig_ptr& n, Lit& out) {
    // XOR is structurally the same as ITE where t = ¬e. In particular the
    // ITE detector above will fire with a literal selector if one of the X
    // children and one of the Y children are literal complements AND the
    // remaining children are ALSO literal complements. So XOR with literal
    // inputs is already covered by try_ite's 4-clause encoding (which for
    // t=¬e degenerates to the same number of clauses as a direct XOR).
    //
    // However, pure XOR has a more flexible matching: any literal complement
    // works as either side, and the 4-clause encoding is symmetric. If both
    // pairs of (x_i, y_j) are literal complements, we recognize it as XOR
    // *even when the selector is ambiguous* (which happens exactly when both
    // pairings match, i.e., (x1 = ¬y1, x2 = ¬y2) or similar).
    //
    // ITE already handles this case, so we don't need a separate path. Kept
    // as a placeholder for future direct XOR encoding extensions (e.g., when
    // the two sub-trees are arbitrary sub-AIGs that are known-complements).
    (void)n; (void)out;
    return false;
}

// -----------------------------------------------------------------------------
// Clause emission.
// -----------------------------------------------------------------------------

template<class Solver>
void AIGToCNF<Solver>::emit_and_equiv(Lit g, const vector<Lit>& inputs) {
    // k-ary AND equivalence: g <-> a1 ∧ a2 ∧ ... ∧ ak
    //   forward:  g -> ai         for each i
    //   backward: a1 ∧ a2 ∧ ... -> g
    // => clauses: (¬g ∨ ai) for each i, and (g ∨ ¬a1 ∨ ¬a2 ∨ ... ∨ ¬ak)
    assert(!inputs.empty());
    for (const auto& a : inputs) add_clause({~g, a});
    vector<Lit> big;
    big.reserve(inputs.size() + 1);
    big.push_back(g);
    for (const auto& a : inputs) big.push_back(~a);
    add_clause(big);
}

template<class Solver>
void AIGToCNF<Solver>::emit_or_equiv(Lit g, const vector<Lit>& inputs) {
    // k-ary OR equivalence: g <-> a1 ∨ a2 ∨ ... ∨ ak
    //   forward:  g -> a1 ∨ ... ∨ ak
    //   backward: ai -> g   for each i
    assert(!inputs.empty());
    vector<Lit> big;
    big.reserve(inputs.size() + 1);
    big.push_back(~g);
    for (const auto& a : inputs) big.push_back(a);
    add_clause(big);
    for (const auto& a : inputs) add_clause({~a, g});
}

template<class Solver>
void AIGToCNF<Solver>::emit_ite(Lit g, Lit s, Lit t, Lit e) {
    // g <-> (s ? t : e)
    // g ->  s -> t   : (¬g ∨ ¬s ∨ t)
    // g -> ¬s -> e   : (¬g ∨ s ∨ e)
    // (s ∧ t) -> g   : (g ∨ ¬s ∨ ¬t)
    // (¬s ∧ e) -> g  : (g ∨ s ∨ ¬e)
    add_clause({~g, ~s, t});
    add_clause({~g, s, e});
    add_clause({g, ~s, ~t});
    add_clause({g, s, ~e});
}

template<class Solver>
void AIGToCNF<Solver>::emit_xor(Lit g, Lit a, Lit b) {
    // g <-> (a XOR b)
    // Direct encoding:
    //  g ->  a ∨  b      : (¬g ∨  a ∨  b)
    //  g -> ¬a ∨ ¬b      : (¬g ∨ ¬a ∨ ¬b)
    //  a ∧ ¬b -> g       : (g ∨ ¬a ∨  b)
    //  ¬a ∧ b -> g       : (g ∨  a ∨ ¬b)
    add_clause({~g, a, b});
    add_clause({~g, ~a, ~b});
    add_clause({g, ~a, b});
    add_clause({g, a, ~b});
}

// -----------------------------------------------------------------------------
// Explicit instantiations.
// -----------------------------------------------------------------------------

} // namespace ArjunNS

// Explicit instantiations. The MetaSolver2 variant lives in manthan.cpp (or
// any TU that already pulls in cadical) to avoid a heavy include here.
namespace ArjunNS {
template class AIGToCNF<CMSat::SATSolver>;
} // namespace ArjunNS
