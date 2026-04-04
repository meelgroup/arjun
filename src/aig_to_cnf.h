/*
 Arjun - Efficient AIG to CNF Conversion

 Converts an AIG into a compact CNF encoding. Key optimizations over the
 naive Tseitin translation:
   - Fanout analysis: nodes with fanout 1 are inlined into their parent;
     only multi-fanout nodes get their own helper variable.
   - K-ary AND/OR fusion: flat multi-input AND/OR encodings use k+1 clauses
     and 1 helper instead of 3(k-1) clauses and k-1 helpers.
   - De Morgan expansion: NAND nodes are viewed as OR gates, and flattening
     propagates through both AND chains and OR chains.
   - ITE pattern detection: (s AND t) OR ((NOT s) AND e) with a literal
     selector is encoded with 4 clauses instead of ~9.
   - Structural sharing: each AIG node is encoded at most once (by pointer).

 The class is a template parameterised on a solver-like type Solver that
 exposes:
   void   new_var();
   uint32_t nVars() const;
   void   add_clause(const std::vector<CMSat::Lit>& cl);
 CMSat::SATSolver and ArjunInt::MetaSolver2 both satisfy this interface
 directly. For manthan's use-case, where encoded clauses must be captured
 into the Formula's clause list rather than pushed straight into the solver,
 a thin adapter (a sink) is used; see manthan.cpp.

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#pragma once

#include "arjun.h"
#include <cryptominisat5/solvertypesmini.h>
#include <cassert>
#include <cstdint>
#include <functional>
#include <map>
#include <set>
#include <vector>

namespace ArjunNS {

struct AIG2CNFStats {
    uint64_t nodes_visited = 0;
    uint64_t helpers_added = 0;
    uint64_t clauses_added = 0;
    uint64_t cache_hits = 0;

    uint64_t kary_and_count = 0;
    uint64_t kary_and_width_total = 0;
    uint64_t kary_or_count = 0;
    uint64_t kary_or_width_total = 0;
    uint64_t ite_patterns = 0;
    uint64_t xor_patterns = 0;
    uint64_t const_nodes = 0;
    uint64_t lit_nodes = 0;

    void clear() { *this = AIG2CNFStats(); }
    void print(int verb = 1) const;
};

template<class Solver>
class AIGToCNF {
public:
    explicit AIGToCNF(Solver& s) : solver(s) {}

    CMSat::Lit encode(const aig_ptr& root, bool force_helper = false);
    std::vector<CMSat::Lit> encode_batch(const std::vector<aig_ptr>& roots);

    void set_true_lit(CMSat::Lit t) { my_true_lit = t; my_has_true_lit = true; }
    const AIG2CNFStats& get_stats() const { return stats; }

    void set_detect_ite(bool b) { detect_ite = b; }
    void set_detect_xor(bool b) { detect_xor = b; }
    void set_kary_fusion(bool b) { kary_fusion = b; }

private:
    Solver& solver;
    AIG2CNFStats stats;

    CMSat::Lit my_true_lit = CMSat::Lit(0, false);
    bool my_has_true_lit = false;

    bool detect_ite = true;
    bool detect_xor = true;
    bool kary_fusion = true;

    std::map<aig_ptr, uint32_t> fanout;
    std::map<aig_ptr, CMSat::Lit> cache;

    void count_fanout(const aig_ptr& root);
    CMSat::Lit encode_node(const aig_ptr& n);
    CMSat::Lit get_true_lit();
    CMSat::Lit new_helper();

    bool try_ite(const aig_ptr& n, CMSat::Lit& out);
    bool try_xor(const aig_ptr& n, CMSat::Lit& out);

    void collect_and(const aig_ptr& n, std::vector<CMSat::Lit>& out);
    void collect_disjuncts_of_neg(const aig_ptr& n, std::vector<CMSat::Lit>& out);

    void emit_and_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    void emit_or_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    void emit_ite(CMSat::Lit g, CMSat::Lit s, CMSat::Lit t, CMSat::Lit e);
    void emit_xor(CMSat::Lit g, CMSat::Lit a, CMSat::Lit b);

    void add_clause(const std::vector<CMSat::Lit>& cl);
};

// =============================================================================
// Template implementation
// =============================================================================

template<class Solver>
void AIGToCNF<Solver>::add_clause(const std::vector<CMSat::Lit>& cl) {
    solver.add_clause(cl);
    stats.clauses_added++;
}

template<class Solver>
CMSat::Lit AIGToCNF<Solver>::new_helper() {
    solver.new_var();
    stats.helpers_added++;
    return CMSat::Lit(solver.nVars() - 1, false);
}

template<class Solver>
CMSat::Lit AIGToCNF<Solver>::get_true_lit() {
    if (my_has_true_lit) return my_true_lit;
    solver.new_var();
    stats.helpers_added++;
    my_true_lit = CMSat::Lit(solver.nVars() - 1, false);
    my_has_true_lit = true;
    add_clause({my_true_lit});
    return my_true_lit;
}

template<class Solver>
void AIGToCNF<Solver>::count_fanout(const aig_ptr& root) {
    // Uses a separate visited set (NOT the fanout map) to drive DFS. Using
    // the fanout map as both visited-marker and count-storage was buggy:
    // "fanout[child]++" in the parent created the map entry, so the child's
    // DFS saw it as already visited and never descended into grandchildren.
    fanout.clear();
    if (!root) return;
    std::set<aig_ptr> visited;
    std::function<void(const aig_ptr&)> dfs = [&](const aig_ptr& n) {
        if (n->type != AIGT::t_and) return;
        if (!visited.insert(n).second) return;
        if (n->l) {
            if (n->l->type == AIGT::t_and) fanout[n->l]++;
            dfs(n->l);
        }
        if (n->r && n->r != n->l) {
            if (n->r->type == AIGT::t_and) fanout[n->r]++;
            dfs(n->r);
        }
        // For the NOT-wrapper AND(x,x,neg=true) pattern we count only one
        // incoming edge into the shared child: semantically this is a single
        // unary NOT dependency.
    };
    dfs(root);
}

template<class Solver>
CMSat::Lit AIGToCNF<Solver>::encode(const aig_ptr& root, bool force_helper) {
    assert(root);
    count_fanout(root);
    CMSat::Lit out = encode_node(root);
    if (force_helper && root->type != AIGT::t_and) {
        CMSat::Lit h = new_helper();
        add_clause({~h, out});
        add_clause({h, ~out});
        return h;
    }
    return out;
}

template<class Solver>
std::vector<CMSat::Lit> AIGToCNF<Solver>::encode_batch(const std::vector<aig_ptr>& roots) {
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
    // Bump each root's fanout by 1 so roots never get inlined away, and so
    // that a sub-AIG appearing as both a root and an internal node of
    // another root still gets its own helper.
    for (const auto& r : roots) {
        if (!r) continue;
        if (r->type == AIGT::t_and) fanout[r]++;
        dfs(r);
    }
    std::vector<CMSat::Lit> result;
    result.reserve(roots.size());
    for (const auto& r : roots) {
        if (!r) { result.emplace_back(0, false); continue; }
        result.push_back(encode_node(r));
    }
    return result;
}

template<class Solver>
CMSat::Lit AIGToCNF<Solver>::encode_node(const aig_ptr& n) {
    {
        auto it = cache.find(n);
        if (it != cache.end()) { stats.cache_hits++; return it->second; }
    }
    stats.nodes_visited++;

    if (n->type == AIGT::t_const) {
        stats.const_nodes++;
        CMSat::Lit t = get_true_lit();
        CMSat::Lit result = n->neg ? ~t : t;
        cache[n] = result;
        return result;
    }
    if (n->type == AIGT::t_lit) {
        stats.lit_nodes++;
        CMSat::Lit result(n->var, n->neg);
        cache[n] = result;
        return result;
    }

    assert(n->type == AIGT::t_and);

    // NOT-wrapper or identity
    if (n->l == n->r) {
        CMSat::Lit sub = encode_node(n->l);
        CMSat::Lit result = n->neg ? ~sub : sub;
        cache[n] = result;
        return result;
    }

    CMSat::Lit out;
    if (detect_ite && try_ite(n, out)) { cache[n] = out; return out; }
    if (detect_xor && try_xor(n, out)) { cache[n] = out; return out; }

    if (!n->neg) {
        // k-ary AND. We expand n's CHILDREN into the input list, never n
        // itself -- calling collect_and(n, ...) would recurse back into
        // encode_node(n) in the rare case where n's own fanout exceeds 1,
        // causing infinite recursion.
        std::vector<CMSat::Lit> inputs;
        if (kary_fusion) {
            collect_and(n->l, inputs);
            if (n->r != n->l) collect_and(n->r, inputs);
        } else {
            inputs.push_back(encode_node(n->l));
            inputs.push_back(encode_node(n->r));
        }
        CMSat::Lit h = new_helper();
        emit_and_equiv(h, inputs);
        stats.kary_and_count++;
        stats.kary_and_width_total += inputs.size();
        cache[n] = h;
        return h;
    } else {
        // k-ary OR via ¬(l ∧ r) = ¬l ∨ ¬r
        std::vector<CMSat::Lit> inputs;
        if (kary_fusion) {
            collect_disjuncts_of_neg(n->l, inputs);
            collect_disjuncts_of_neg(n->r, inputs);
        } else {
            inputs.push_back(~encode_node(n->l));
            inputs.push_back(~encode_node(n->r));
        }
        CMSat::Lit h = new_helper();
        emit_or_equiv(h, inputs);
        stats.kary_or_count++;
        stats.kary_or_width_total += inputs.size();
        cache[n] = h;
        return h;
    }
}

template<class Solver>
void AIGToCNF<Solver>::collect_and(const aig_ptr& n, std::vector<CMSat::Lit>& out) {
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

template<class Solver>
void AIGToCNF<Solver>::collect_disjuncts_of_neg(const aig_ptr& n, std::vector<CMSat::Lit>& out) {
    if (n->type == AIGT::t_and && !n->neg
        && n->l != n->r
        && fanout[n] <= 1
        && cache.find(n) == cache.end())
    {
        collect_disjuncts_of_neg(n->l, out);
        collect_disjuncts_of_neg(n->r, out);
        return;
    }
    out.push_back(~encode_node(n));
}

// ITE pattern: (s ∧ t) ∨ (¬s ∧ e)  where s is a literal. In this AIG,
// n = AND(X, Y, neg=true); each of X, Y either is a NAND(a,b) directly
// (which equals a AND b under the outer negation) or a NOT-wrapper
// AND(u, u, neg=true) that wraps a positive AND u.
template<class Solver>
bool AIGToCNF<Solver>::try_ite(const aig_ptr& n, CMSat::Lit& out) {
    auto is_lit_complement = [](const aig_ptr& a, const aig_ptr& b) -> bool {
        return a && b
            && a->type == AIGT::t_lit && b->type == AIGT::t_lit
            && a->var == b->var && a->neg != b->neg;
    };

    if (n->type != AIGT::t_and || !n->neg) return false;
    const aig_ptr& lx = n->l;
    const aig_ptr& ly = n->r;
    if (!lx || !ly || lx == ly) return false;

    auto as_pos_and = [&](const aig_ptr& w) -> aig_ptr {
        if (!w || w->type != AIGT::t_and) return nullptr;
        if (w->neg) {
            if (w->l == w->r) {
                aig_ptr u = w->l;
                if (u && u->type == AIGT::t_and && !u->neg && u->l != u->r) return u;
                return nullptr;
            }
            return w;
        }
        return nullptr;
    };
    aig_ptr ax = as_pos_and(lx);
    aig_ptr ay = as_pos_and(ly);
    if (!ax || !ay) return false;

    auto can_consume = [&](const aig_ptr& node) -> bool {
        if (cache.find(node) != cache.end()) return false;
        auto it = fanout.find(node);
        return it != fanout.end() && it->second <= 1;
    };
    if (!can_consume(lx) || !can_consume(ly)) return false;
    if (ax != lx && !can_consume(ax)) return false;
    if (ay != ly && !can_consume(ay)) return false;

    const aig_ptr& x1 = ax->l;
    const aig_ptr& x2 = ax->r;
    const aig_ptr& y1 = ay->l;
    const aig_ptr& y2 = ay->r;

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

    CMSat::Lit s_lit((*sel_x)->var, (*sel_x)->neg);
    CMSat::Lit t_lit = encode_node(*other_x);
    CMSat::Lit e_lit = encode_node(*other_y);

    CMSat::Lit h = new_helper();
    emit_ite(h, s_lit, t_lit, e_lit);
    stats.ite_patterns++;
    out = h;
    return true;
}

template<class Solver>
bool AIGToCNF<Solver>::try_xor(const aig_ptr& /*n*/, CMSat::Lit& /*out*/) {
    // XOR with literal operands is already covered as a degenerate ITE (with
    // t = NOT e), so the ITE detector catches it with identical clause count.
    // Reserved for future direct XOR detection with arbitrary sub-AIG operands.
    return false;
}

template<class Solver>
void AIGToCNF<Solver>::emit_and_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs) {
    assert(!inputs.empty());
    for (const auto& a : inputs) add_clause({~g, a});
    std::vector<CMSat::Lit> big;
    big.reserve(inputs.size() + 1);
    big.push_back(g);
    for (const auto& a : inputs) big.push_back(~a);
    add_clause(big);
}

template<class Solver>
void AIGToCNF<Solver>::emit_or_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs) {
    assert(!inputs.empty());
    std::vector<CMSat::Lit> big;
    big.reserve(inputs.size() + 1);
    big.push_back(~g);
    for (const auto& a : inputs) big.push_back(a);
    add_clause(big);
    for (const auto& a : inputs) add_clause({~a, g});
}

template<class Solver>
void AIGToCNF<Solver>::emit_ite(CMSat::Lit g, CMSat::Lit s, CMSat::Lit t, CMSat::Lit e) {
    add_clause({~g, ~s, t});
    add_clause({~g, s, e});
    add_clause({g, ~s, ~t});
    add_clause({g, s, ~e});
}

template<class Solver>
void AIGToCNF<Solver>::emit_xor(CMSat::Lit g, CMSat::Lit a, CMSat::Lit b) {
    add_clause({~g, a, b});
    add_clause({~g, ~a, ~b});
    add_clause({g, ~a, b});
    add_clause({g, a, ~b});
}

} // namespace ArjunNS
