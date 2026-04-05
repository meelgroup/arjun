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
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <functional>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
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

    // Contribution counters: how often each feature fires.
    uint64_t cse_and_hits = 0;       // AND group content-hash CSE hits
    uint64_t cse_or_hits = 0;        // OR group CSE hits
    uint64_t cse_ite_hits = 0;       // ITE CSE hits
    uint64_t dedup_const_and = 0;    // AND folded to constant via dedup/complementary
    uint64_t dedup_const_or = 0;
    uint64_t demorgan_and_flat = 0;  // De Morgan NOT-wrapper flatten in collect_and
    uint64_t demorgan_or_flat = 0;   // ... in collect_disjuncts_of_neg
    uint64_t ite_sub_sel = 0;        // ITE with non-literal sub-AIG selector
    uint64_t ite_degenerate = 0;     // ITE degenerate-case fold

    double encode_time_s = 0.0;

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
    void set_group_cse(bool b) { group_cse = b; }
    void set_ite_sub_selector(bool b) { ite_sub_selector = b; }
    void set_demorgan_flatten(bool b) { demorgan_flatten = b; }
    void set_normalize_inputs(bool b) { normalize_inputs = b; }

private:
    Solver& solver;
    AIG2CNFStats stats;

    CMSat::Lit my_true_lit = CMSat::Lit(0, false);
    bool my_has_true_lit = false;

    // Feature toggles. All ON except group_cse: the fuzzer --measure mode
    // showed that content-hashed CSE across AND/OR/ITE groups costs more
    // encode time than it saves via the resulting smaller CNF, and the
    // helpers it merges across sub-formulas can hurt downstream SAT
    // propagation in the manthan pipeline.
    bool detect_ite = true;
    bool detect_xor = true;
    bool kary_fusion = true;
    bool group_cse = false;        // (default off) structural CSE for groups
    bool ite_sub_selector = true;  // allow non-literal sub-AIG ITE selectors
    bool demorgan_flatten = true;  // flatten k-ary through NOT-wrappers
    bool normalize_inputs = true;  // dedup / complementary / const fold

    // Hash on shared_ptr raw pointer for O(1) fanout/cache lookups. std::map
    // showed up as the hottest path on 500k-node manthan AIGs.
    struct AigPtrHash {
        size_t operator()(const aig_ptr& p) const noexcept {
            return std::hash<AIG*>{}(p.get());
        }
    };
    std::unordered_map<aig_ptr, uint32_t, AigPtrHash> fanout;
    std::unordered_map<aig_ptr, CMSat::Lit, AigPtrHash> cache;

    // Content-hashed caches for structural CSE across AIG pointers that
    // happen to encode the same gate. Keyed on the (sorted) literal inputs.
    using LitKey = std::vector<CMSat::Lit>;
    struct LitKeyCmp {
        bool operator()(const LitKey& a, const LitKey& b) const {
            if (a.size() != b.size()) return a.size() < b.size();
            for (size_t i = 0; i < a.size(); i++) {
                if (a[i] != b[i]) {
                    if (a[i].var() != b[i].var()) return a[i].var() < b[i].var();
                    return a[i].sign() < b[i].sign();
                }
            }
            return false;
        }
    };
    std::map<LitKey, CMSat::Lit, LitKeyCmp> and_group_cse;
    std::map<LitKey, CMSat::Lit, LitKeyCmp> or_group_cse;
    // ITE CSE: key is (s, t, e).
    using IteKey = std::tuple<uint32_t, uint32_t, uint32_t>; // var*2+sign
    std::map<IteKey, CMSat::Lit> ite_cse;

    void count_fanout(const aig_ptr& root);
    CMSat::Lit encode_node(const aig_ptr& n);
    CMSat::Lit get_true_lit();
    CMSat::Lit new_helper();

    bool try_ite(const aig_ptr& n, CMSat::Lit& out);
    bool try_xor(const aig_ptr& n, CMSat::Lit& out);

    void collect_and(const aig_ptr& n, std::vector<CMSat::Lit>& out);
    void collect_disjuncts_of_neg(const aig_ptr& n, std::vector<CMSat::Lit>& out);

    // Post-process a k-ary AND input list: dedup, detect trivial constants.
    // Returns true if the group is a constant (out_const set to the constant).
    // Otherwise updates inputs in place.
    bool normalize_and_inputs(std::vector<CMSat::Lit>& inputs, bool& out_const);
    bool normalize_or_inputs(std::vector<CMSat::Lit>& inputs, bool& out_const);

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
    std::unordered_set<aig_ptr, AigPtrHash> visited;
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
    std::unordered_set<aig_ptr, AigPtrHash> visited;
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
        if (normalize_inputs) {
            bool is_const = false;
            if (normalize_and_inputs(inputs, is_const)) {
                // AND short-circuited to FALSE.
                stats.dedup_const_and++;
                CMSat::Lit t = get_true_lit();
                CMSat::Lit result = ~t;
                cache[n] = result;
                return result;
            }
            if (inputs.empty()) {
                CMSat::Lit t = get_true_lit();
                cache[n] = t;
                return t;
            }
            if (inputs.size() == 1) {
                cache[n] = inputs[0];
                return inputs[0];
            }
        }
        if (group_cse) {
            auto it_cse = and_group_cse.find(inputs);
            if (it_cse != and_group_cse.end()) {
                stats.cse_and_hits++;
                cache[n] = it_cse->second;
                return it_cse->second;
            }
        }
        CMSat::Lit h = new_helper();
        emit_and_equiv(h, inputs);
        stats.kary_and_count++;
        stats.kary_and_width_total += inputs.size();
        if (group_cse) and_group_cse[inputs] = h;
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
        if (normalize_inputs) {
            bool is_const = false;
            if (normalize_or_inputs(inputs, is_const)) {
                stats.dedup_const_or++;
                CMSat::Lit t = get_true_lit();
                cache[n] = t;
                return t;
            }
            if (inputs.empty()) {
                CMSat::Lit t = get_true_lit();
                CMSat::Lit result = ~t;
                cache[n] = result;
                return result;
            }
            if (inputs.size() == 1) {
                cache[n] = inputs[0];
                return inputs[0];
            }
        }
        if (group_cse) {
            auto it_cse = or_group_cse.find(inputs);
            if (it_cse != or_group_cse.end()) {
                stats.cse_or_hits++;
                cache[n] = it_cse->second;
                return it_cse->second;
            }
        }
        CMSat::Lit h = new_helper();
        if (group_cse) or_group_cse[inputs] = h;
        emit_or_equiv(h, inputs);
        stats.kary_or_count++;
        stats.kary_or_width_total += inputs.size();
        cache[n] = h;
        return h;
    }
}

// collect_and(n, out): n is a conjunct of the enclosing k-ary AND; append its
// contribution. Flattens through:
//   (a) positive t_and nodes (direct child ANDs), and
//   (b) NOT-wrappers of inner OR gates via De Morgan:
//       n = AND(G, G, neg=true) where G = AND(x, y, neg=true) (an OR gate)
//       means n = NOT(OR(¬x, ¬y)) = AND(x, y), so x and y are both conjuncts.
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
    // De Morgan: NOT-wrapper of an OR gate flattens into a positive AND of the
    // OR's raw children (which are already the negations of the disjuncts).
    if (demorgan_flatten
        && n->type == AIGT::t_and && n->neg && n->l == n->r
        && fanout[n] <= 1
        && cache.find(n) == cache.end())
    {
        const aig_ptr& inner = n->l;
        if (inner && inner->type == AIGT::t_and && inner->neg
            && inner->l != inner->r
            && fanout[inner] <= 1
            && cache.find(inner) == cache.end())
        {
            stats.demorgan_and_flat++;
            collect_and(inner->l, out);
            collect_and(inner->r, out);
            return;
        }
    }
    out.push_back(encode_node(n));
}

// collect_disjuncts_of_neg(n, out): n is the raw AIG child of an outer OR
// gate (AND with neg=true), representing ¬disjunct. Append lits for the
// disjuncts hidden behind n, flattening through:
//   (a) positive t_and (¬(AND) = OR by De Morgan, so its two children
//       contribute ¬child as further disjuncts), and
//   (b) NOT-wrappers of inner OR gates (so ¬n is a further OR, whose
//       disjuncts should be merged into the outer OR).
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
    // NOT-wrapper of an inner OR gate: ¬n = inner OR, flatten its disjuncts.
    if (demorgan_flatten
        && n->type == AIGT::t_and && n->neg && n->l == n->r
        && fanout[n] <= 1
        && cache.find(n) == cache.end())
    {
        const aig_ptr& inner = n->l;
        if (inner && inner->type == AIGT::t_and && inner->neg
            && inner->l != inner->r
            && fanout[inner] <= 1
            && cache.find(inner) == cache.end())
        {
            stats.demorgan_or_flat++;
            collect_disjuncts_of_neg(inner->l, out);
            collect_disjuncts_of_neg(inner->r, out);
            return;
        }
    }
    out.push_back(~encode_node(n));
}

// Dedup and constant-folding on a k-ary AND input list. Removes duplicate
// literals and short-circuits to FALSE if x and ¬x both appear (returns
// true with out_const=false). Also folds TRUE-literals out and FALSE-literal
// to constant FALSE.
template<class Solver>
bool AIGToCNF<Solver>::normalize_and_inputs(std::vector<CMSat::Lit>& inputs, bool& out_const) {
    CMSat::Lit tlit;
    bool has_tlit = my_has_true_lit;
    if (has_tlit) tlit = my_true_lit;

    // Sort by var,sign for dedup and complementary detection.
    std::sort(inputs.begin(), inputs.end(),
        [](CMSat::Lit a, CMSat::Lit b) {
            if (a.var() != b.var()) return a.var() < b.var();
            return a.sign() < b.sign();
        });
    std::vector<CMSat::Lit> out;
    out.reserve(inputs.size());
    for (size_t i = 0; i < inputs.size(); i++) {
        CMSat::Lit l = inputs[i];
        // Remove TRUE-literal contributions.
        if (has_tlit && l == tlit) continue;
        // Short-circuit on FALSE-literal.
        if (has_tlit && l == ~tlit) { out_const = false; return true; }
        // Dedup consecutive identical lits.
        if (!out.empty() && out.back() == l) continue;
        // Complementary pair (same var, opposite sign) = AND of x and ¬x = FALSE.
        if (!out.empty() && out.back().var() == l.var()) {
            out_const = false; return true;
        }
        out.push_back(l);
    }
    inputs.swap(out);
    return false;
}

template<class Solver>
bool AIGToCNF<Solver>::normalize_or_inputs(std::vector<CMSat::Lit>& inputs, bool& out_const) {
    CMSat::Lit tlit;
    bool has_tlit = my_has_true_lit;
    if (has_tlit) tlit = my_true_lit;
    std::sort(inputs.begin(), inputs.end(),
        [](CMSat::Lit a, CMSat::Lit b) {
            if (a.var() != b.var()) return a.var() < b.var();
            return a.sign() < b.sign();
        });
    std::vector<CMSat::Lit> out;
    out.reserve(inputs.size());
    for (size_t i = 0; i < inputs.size(); i++) {
        CMSat::Lit l = inputs[i];
        if (has_tlit && l == ~tlit) continue; // FALSE contributes nothing.
        if (has_tlit && l == tlit) { out_const = true; return true; } // TRUE short-circuit.
        if (!out.empty() && out.back() == l) continue; // dedup.
        if (!out.empty() && out.back().var() == l.var()) { // x ∨ ¬x = TRUE.
            out_const = true; return true;
        }
        out.push_back(l);
    }
    inputs.swap(out);
    return false;
}

// ITE pattern: (s ∧ t) ∨ (¬s ∧ e). In this AIG,
// n = AND(X, Y, neg=true); each of X, Y is either a positive t_and (X, Y is
// a NAND — so equals a positive AND under the outer negation) or a
// NOT-wrapper AND(u, u, neg=true) that wraps a positive AND u.
// The selector s can be a literal OR any sub-AIG (typically an AND of
// many literals — the common manthan case). For non-literal selectors
// we detect the complement via pointer equality of the positive AND with
// its NOT-wrapper.
template<class Solver>
bool AIGToCNF<Solver>::try_ite(const aig_ptr& n, CMSat::Lit& out) {
    auto is_lit_complement = [](const aig_ptr& a, const aig_ptr& b) -> bool {
        return a && b
            && a->type == AIGT::t_lit && b->type == AIGT::t_lit
            && a->var == b->var && a->neg != b->neg;
    };
    // For non-literal nodes, detect that one is the NOT-wrapper of the
    // other: either (a) a is t_and NOT-wrapper (l==r, neg=true) of b, or
    // (b) b is t_and NOT-wrapper of a.
    auto is_sub_complement = [](const aig_ptr& a, const aig_ptr& b) -> bool {
        if (!a || !b) return false;
        if (a->type == AIGT::t_and && a->neg && a->l == a->r && a->l == b) return true;
        if (b->type == AIGT::t_and && b->neg && b->l == b->r && b->l == a) return true;
        return false;
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
    const aig_ptr* sel_y = nullptr;
    const aig_ptr* other_x = nullptr;
    const aig_ptr* other_y = nullptr;
    bool matched_lit = false;
    auto try_match = [&](const aig_ptr& xa, const aig_ptr& xb,
                         const aig_ptr& ya, const aig_ptr& yb) -> bool {
        if (is_lit_complement(xa, ya)) {
            sel_x = &xa; sel_y = &ya; other_x = &xb; other_y = &yb;
            matched_lit = true; return true;
        }
        if (ite_sub_selector && is_sub_complement(xa, ya)) {
            sel_x = &xa; sel_y = &ya; other_x = &xb; other_y = &yb;
            matched_lit = false; return true;
        }
        return false;
    };
    if (!try_match(x1, x2, y1, y2) &&
        !try_match(x1, x2, y2, y1) &&
        !try_match(x2, x1, y1, y2) &&
        !try_match(x2, x1, y2, y1)) return false;

    CMSat::Lit s_lit;
    if (matched_lit) {
        s_lit = CMSat::Lit((*sel_x)->var, (*sel_x)->neg);
    } else {
        stats.ite_sub_sel++;
        // Encode the selector sub-AIG. Use the positive form (whichever of
        // sel_x/sel_y is NOT a NOT-wrapper) so that s_lit's polarity
        // matches the "then" side.
        const aig_ptr& sx = *sel_x;
        const aig_ptr& sy = *sel_y;
        // Identify the positive side: it is the one that is NOT a
        // NOT-wrapper (AND(u,u,neg=true)) of the other.
        bool sx_is_wrapper = (sx->type == AIGT::t_and && sx->neg && sx->l == sx->r && sx->l == sy);
        const aig_ptr& pos_sel = sx_is_wrapper ? sy : sx;
        s_lit = encode_node(pos_sel);
        // If sel_x happens to be the NOT-wrapper, the "then" branch is
        // actually behind sel_y, i.e., we need to flip: the branch we
        // called "other_x" is paired with the *negation* of pos_sel.
        if (sx_is_wrapper) s_lit = ~s_lit;
    }
    CMSat::Lit t_lit = encode_node(*other_x);
    CMSat::Lit e_lit = encode_node(*other_y);

    // Degenerate cases.
    //   ITE(s, t, t) = t
    //   ITE(s, s, e) = s ∨ e           (s=1 → 1; s=0 → e)
    //   ITE(s, ¬s, e) = ¬s ∧ e         (s=1 → 0; s=0 → e)
    //   ITE(s, t, s) = s ∧ t           (s=1 → t; s=0 → 0)
    //   ITE(s, t, ¬s) = ¬s ∨ t         (s=1 → t; s=0 → 1)
    auto emit_or2 = [&](CMSat::Lit a, CMSat::Lit b) -> CMSat::Lit {
        std::vector<CMSat::Lit> inp = {a, b};
        if (normalize_inputs) {
            bool cst = false;
            if (normalize_or_inputs(inp, cst)) return get_true_lit();
            if (inp.empty()) return ~get_true_lit();
            if (inp.size() == 1) return inp[0];
        }
        if (group_cse) {
            auto it = or_group_cse.find(inp);
            if (it != or_group_cse.end()) return it->second;
        }
        CMSat::Lit h = new_helper();
        if (group_cse) or_group_cse[inp] = h;
        emit_or_equiv(h, inp);
        return h;
    };
    auto emit_and2 = [&](CMSat::Lit a, CMSat::Lit b) -> CMSat::Lit {
        std::vector<CMSat::Lit> inp = {a, b};
        if (normalize_inputs) {
            bool cst = false;
            if (normalize_and_inputs(inp, cst)) return ~get_true_lit();
            if (inp.empty()) return get_true_lit();
            if (inp.size() == 1) return inp[0];
        }
        if (group_cse) {
            auto it = and_group_cse.find(inp);
            if (it != and_group_cse.end()) return it->second;
        }
        CMSat::Lit h = new_helper();
        if (group_cse) and_group_cse[inp] = h;
        emit_and_equiv(h, inp);
        return h;
    };
    if (t_lit == e_lit) { stats.ite_degenerate++; out = t_lit; return true; }
    if (s_lit == t_lit)  { stats.ite_degenerate++; out = emit_or2(s_lit, e_lit);  return true; }
    if (s_lit == ~t_lit) { stats.ite_degenerate++; out = emit_and2(~s_lit, e_lit); return true; }
    if (s_lit == e_lit)  { stats.ite_degenerate++; out = emit_and2(s_lit, t_lit); return true; }
    if (s_lit == ~e_lit) { stats.ite_degenerate++; out = emit_or2(~s_lit, t_lit); return true; }

    if (group_cse) {
        // Canonicalize: flip (s,t,e) to (¬s,e,t) when selector is negative.
        if (s_lit.sign()) {
            s_lit = ~s_lit;
            std::swap(t_lit, e_lit);
        }
        auto pack = [](CMSat::Lit l) { return (l.var() << 1) | (l.sign() ? 1u : 0u); };
        IteKey key{pack(s_lit), pack(t_lit), pack(e_lit)};
        auto it_ite = ite_cse.find(key);
        if (it_ite != ite_cse.end()) {
            stats.cse_ite_hits++;
            out = it_ite->second;
            stats.ite_patterns++;
            return true;
        }
        CMSat::Lit h = new_helper();
        emit_ite(h, s_lit, t_lit, e_lit);
        ite_cse[key] = h;
        stats.ite_patterns++;
        out = h;
        return true;
    }

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
