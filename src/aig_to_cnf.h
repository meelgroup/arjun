/*
 Arjun - AIG to CNF Conversion

 Converts an AIG into a CNF encoding using Tseitin translation. Fanout
 analysis inlines single-use AND nodes into their parent; multi-fanout
 nodes get their own helper variable.

 In the new representation, AIG nodes have no output-negation: each AND
 node's two fanin edges can be independently complemented (aig_lit carries
 that edge sign). Leaves (t_lit, t_const) are positive-valued nodes; any
 sign lives on the referring edge.

 The encoder is parametrised on a solver-like Solver that exposes:
   void     new_var();
   uint32_t nVars() const;
   void     add_clause(const std::vector<CMSat::Lit>& cl);

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#pragma once

#include "arjun.h"
#include <cryptominisat5/solvertypesmini.h>
#include <cstdint>
#include <functional>
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
    // In the input-edge-neg model OR is just a negative-edge reference to an
    // AND — encode_and_node handles both polarities uniformly, so kary_or_*
    // are always zero. Kept for API compatibility with callers that still
    // query them.
    uint64_t kary_or_count = 0;
    uint64_t kary_or_width_total = 0;
    uint64_t const_nodes = 0;
    uint64_t lit_nodes = 0;

    // Stubs kept for API compatibility with callers that still track these.
    uint64_t ite_patterns = 0;
    uint64_t mux3_patterns = 0;
    uint64_t xor_patterns = 0;
    uint64_t cut_cnf_patterns = 0;
    uint64_t cut_cnf_clauses = 0;

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
    [[nodiscard]] const AIG2CNFStats& get_stats() const { return stats; }

    void set_detect_ite(bool b) { detect_ite = b; }
    void set_detect_xor(bool b) { detect_xor = b; }
    void set_cut_cnf(bool) {}
    void set_kary_fusion(bool b) { kary_fusion = b; }
    void set_group_cse(bool) {}
    void set_ite_sub_selector(bool b) { ite_sub_selector = b; }
    void set_demorgan_flatten(bool) {}
    void set_normalize_inputs(bool b) { normalize_inputs = b; }
    void set_max_kary_width(uint32_t w) { max_kary_width = w; }

private:
    Solver& solver;
    AIG2CNFStats stats;

    CMSat::Lit my_true_lit = CMSat::Lit(0, false);
    bool my_has_true_lit = false;

    bool detect_ite = true;
    bool detect_xor = true;
    bool ite_sub_selector = true;   // allow non-literal sub-AIG ITE selectors
    bool kary_fusion = true;
    bool normalize_inputs = true;
    uint32_t max_kary_width = 1u << 30;

    // Fanout counted by node identity. Leaf nodes are never helpers and
    // don't need fanout tracking.
    struct AigNodeHash {
        size_t operator()(const AIG* p) const noexcept {
            return p ? std::hash<uint64_t>{}(p->nid) : 0;
        }
    };
    std::unordered_map<const AIG*, uint32_t, AigNodeHash> fanout;

    // Encoding cache keyed on node identity. Stores the CNF literal that
    // represents the POSITIVE value of the AND node; the caller applies any
    // edge-sign. Leaves are not cached (encoding them is trivial).
    std::unordered_map<const AIG*, CMSat::Lit, AigNodeHash> cache;

    void count_fanout(const aig_ptr& root);
    CMSat::Lit encode_edge(const aig_ptr& n);
    // Encode the node n's POSITIVE value as an AND (k-ary). Callers handle
    // caching and outer-sign application.
    CMSat::Lit encode_and_positive(const AIG* n);
    CMSat::Lit get_true_lit();
    CMSat::Lit new_helper();

    // Collect k-ary AND conjuncts. Each conjunct is returned as a signed edge
    // (aig_lit). We only flatten through positive-reference AND nodes whose
    // fanout is 1 — otherwise sharing would be lost.
    void collect_and_edges(const aig_lit& child, std::vector<aig_lit>& out);

    // ITE pattern detection. Input `n` must be an OR-gate reference:
    // n.neg = true, n->type = t_and, n->l != n->r. The outer OR decomposes
    // as OR(AND_T, AND_E) where AND_T = (n->l's target, positive) and
    // AND_E similarly — each branch was a negative edge from outer to a
    // sub-AND. If the two sub-ANDs share one complementary input pair
    // (literal or sub-AIG), that pair is the selector and the remaining
    // children are the then / else values.
    struct IteShape {
        bool valid = false;
        bool sel_is_lit = false;
        uint32_t sel_var = 0;
        bool sel_neg = false;
        // For sub-AIG selectors: positive AIG for the selector, plus an
        // `invert` flag for when the matched edge pointed at it negatively.
        aig_lit sel_aig;
        bool sel_invert = false;
        aig_lit t_aig;
        aig_lit e_aig;
    };
    struct IteParse {
        bool valid = false;
        CMSat::Lit s_lit;
        aig_lit t_aig;
        aig_lit e_aig;
    };
    bool parse_ite_shape(const aig_lit& n, IteShape& out);
    bool parse_ite_at(const aig_lit& n, IteParse& out);
    bool try_ite(const aig_lit& n, CMSat::Lit& out);

    // XOR pattern detection. Same outer OR(AND_T, AND_E) shape as ITE, but
    // instead of one complementary pair across (AND_T, AND_E) there are
    // TWO — so both pairs cancel. The node's value is XOR(a, b) for some
    // (a, b) read off one of the inner ANDs.
    bool try_xor(const aig_lit& n, CMSat::Lit& out);

    void emit_and_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    void emit_or_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    void emit_ite(CMSat::Lit g, CMSat::Lit s, CMSat::Lit t, CMSat::Lit e);
    void emit_xor(CMSat::Lit g, CMSat::Lit a, CMSat::Lit b);

    // Two signed edges representing logically-complementary values: same
    // node, opposite edge sign (covers literals, constants, and sub-AIGs
    // uniformly in the input-edge-neg model).
    static bool aig_complement(const aig_lit& a, const aig_lit& b) {
        return a.node && b.node && a.node == b.node && a.neg != b.neg;
    }

    CMSat::Lit emit_and2(CMSat::Lit a, CMSat::Lit b);
    CMSat::Lit emit_or2(CMSat::Lit a, CMSat::Lit b);

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
    fanout.clear();
    if (!root) return;
    std::unordered_set<const AIG*, AigNodeHash> visited;
    std::function<void(const AIG*)> dfs = [&](const AIG* n) {
        if (!n || n->type != AIGT::t_and) return;
        if (!visited.insert(n).second) return;
        if (n->l && n->l->type == AIGT::t_and) {
            fanout[n->l.get()]++;
            dfs(n->l.get());
        }
        if (n->r && n->r.get() != n->l.get()) {
            if (n->r->type == AIGT::t_and) fanout[n->r.get()]++;
            dfs(n->r.get());
        }
    };
    dfs(root.get());
}

template<class Solver>
CMSat::Lit AIGToCNF<Solver>::encode(const aig_ptr& root, bool force_helper) {
    assert(root);
    count_fanout(root);
    CMSat::Lit out = encode_edge(root);
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
    std::unordered_set<const AIG*, AigNodeHash> visited;
    std::function<void(const AIG*)> dfs = [&](const AIG* n) {
        if (!n || n->type != AIGT::t_and) return;
        if (!visited.insert(n).second) return;
        if (n->l && n->l->type == AIGT::t_and) {
            fanout[n->l.get()]++;
            dfs(n->l.get());
        }
        if (n->r && n->r.get() != n->l.get()) {
            if (n->r->type == AIGT::t_and) fanout[n->r.get()]++;
            dfs(n->r.get());
        }
    };
    // Bump each root's fanout so roots are never inlined away.
    for (const auto& r : roots) {
        if (!r) continue;
        if (r->type == AIGT::t_and) fanout[r.get()]++;
        dfs(r.get());
    }
    std::vector<CMSat::Lit> result;
    result.reserve(roots.size());
    for (const auto& r : roots) {
        if (!r) { result.emplace_back(0, false); continue; }
        result.push_back(encode_edge(r));
    }
    return result;
}

template<class Solver>
CMSat::Lit AIGToCNF<Solver>::encode_edge(const aig_ptr& n) {
    stats.nodes_visited++;
    if (n->type == AIGT::t_const) {
        stats.const_nodes++;
        CMSat::Lit t = get_true_lit();
        return n.neg ? ~t : t;
    }
    if (n->type == AIGT::t_lit) {
        stats.lit_nodes++;
        return CMSat::Lit(n->var, n.neg);
    }
    assert(n->type == AIGT::t_and);

    // Cache stores the POSITIVE value of the node. Applying n.neg gives the
    // signed-edge lit.
    auto it = cache.find(n.get());
    if (it != cache.end()) {
        stats.cache_hits++;
        return n.neg ? ~it->second : it->second;
    }

    // Idempotent AND(x, x): node's value equals x's value.
    if (n->l == n->r) {
        CMSat::Lit sub = encode_edge(n->l);
        cache[n.get()] = sub;
        return n.neg ? ~sub : sub;
    }

    // Negative edge = OR-gate view — the shape where ITE / XOR / ... live.
    // XOR runs before ITE: XOR is a special shape of ITE (then = ~else)
    // that the degenerate-ITE path would otherwise match less cleanly.
    if (n.neg) {
        CMSat::Lit neg_lit;
        if (detect_xor && try_xor(n, neg_lit)) {
            cache[n.get()] = ~neg_lit;
            return neg_lit;
        }
        if (detect_ite && try_ite(n, neg_lit)) {
            cache[n.get()] = ~neg_lit;
            return neg_lit;
        }
    }

    // Fall through: encode as positive-value AND.
    CMSat::Lit pos = encode_and_positive(n.get());
    cache[n.get()] = pos;
    return n.neg ? ~pos : pos;
}

// Encode a t_and NODE's POSITIVE value as a k-ary AND. Caller caches.
template<class Solver>
CMSat::Lit AIGToCNF<Solver>::encode_and_positive(const AIG* n) {
    assert(n->type == AIGT::t_and);
    assert(n->l != n->r);

    std::vector<aig_lit> conjunct_edges;
    if (kary_fusion) {
        collect_and_edges(n->l, conjunct_edges);
        collect_and_edges(n->r, conjunct_edges);
    } else {
        conjunct_edges.push_back(n->l);
        conjunct_edges.push_back(n->r);
    }

    // Encode each conjunct. Also apply basic constant / dedup normalisation.
    std::vector<CMSat::Lit> inputs;
    inputs.reserve(conjunct_edges.size());
    for (const auto& c : conjunct_edges) inputs.push_back(encode_edge(c));

    if (normalize_inputs) {
        // Drop TRUE and detect FALSE / complementary pairs.
        CMSat::Lit TRUE_LIT = get_true_lit();
        std::vector<CMSat::Lit> cleaned;
        cleaned.reserve(inputs.size());
        bool folded_false = false;
        for (auto l : inputs) {
            if (l == TRUE_LIT) continue;              // drop TRUE
            if (l == ~TRUE_LIT) { folded_false = true; break; } // FALSE → AND is FALSE
            cleaned.push_back(l);
        }
        if (!folded_false) {
            // Dedup + complementary detection.
            std::sort(cleaned.begin(), cleaned.end(),
                [](CMSat::Lit a, CMSat::Lit b) {
                    if (a.var() != b.var()) return a.var() < b.var();
                    return (int)a.sign() < (int)b.sign();
                });
            std::vector<CMSat::Lit> dedup;
            dedup.reserve(cleaned.size());
            for (auto l : cleaned) {
                if (!dedup.empty() && dedup.back() == l) continue;
                if (!dedup.empty() && dedup.back().var() == l.var()) {
                    folded_false = true; break;
                }
                dedup.push_back(l);
            }
            cleaned = std::move(dedup);
        }
        if (folded_false) return ~TRUE_LIT;
        if (cleaned.empty()) return TRUE_LIT;
        if (cleaned.size() == 1) return cleaned[0];
        inputs = std::move(cleaned);
    }

    // Width cap: break very wide groups into chunks.
    if (inputs.size() > max_kary_width) {
        std::vector<CMSat::Lit> current = std::move(inputs);
        while (current.size() > max_kary_width) {
            std::vector<CMSat::Lit> next;
            next.reserve((current.size() + max_kary_width - 1) / max_kary_width);
            for (size_t i = 0; i < current.size(); i += max_kary_width) {
                size_t end = std::min(current.size(), i + max_kary_width);
                if (end - i == 1) { next.push_back(current[i]); continue; }
                std::vector<CMSat::Lit> chunk(current.begin() + i, current.begin() + end);
                CMSat::Lit hc = new_helper();
                emit_and_equiv(hc, chunk);
                stats.kary_and_count++;
                stats.kary_and_width_total += chunk.size();
                next.push_back(hc);
            }
            current = std::move(next);
        }
        if (current.size() == 1) return current[0];
        CMSat::Lit h = new_helper();
        emit_and_equiv(h, current);
        stats.kary_and_count++;
        stats.kary_and_width_total += current.size();
        return h;
    }

    CMSat::Lit h = new_helper();
    emit_and_equiv(h, inputs);
    stats.kary_and_count++;
    stats.kary_and_width_total += inputs.size();
    return h;
}

// Flatten k-ary AND through positive-reference fanout-1 AND nodes. Each
// conjunct returned is a signed edge ready for encoding.
template<class Solver>
void AIGToCNF<Solver>::collect_and_edges(const aig_lit& child, std::vector<aig_lit>& out) {
    if (child->type == AIGT::t_and
        && !child.neg
        && child->l != child->r
        && fanout[child.get()] <= 1
        && cache.find(child.get()) == cache.end())
    {
        collect_and_edges(child->l, out);
        collect_and_edges(child->r, out);
        return;
    }
    out.push_back(child);
}

template<class Solver>
void AIGToCNF<Solver>::emit_and_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs) {
    // g = AND(inputs):
    //   for each i: g → i  ⇔ ~g ∨ i  (forward implications)
    //   all i →  g        ⇔ g ∨ ~i1 ∨ ~i2 ...  (backward)
    for (auto l : inputs) add_clause({~g, l});
    std::vector<CMSat::Lit> backward;
    backward.reserve(inputs.size() + 1);
    backward.push_back(g);
    for (auto l : inputs) backward.push_back(~l);
    add_clause(backward);
}

template<class Solver>
void AIGToCNF<Solver>::emit_or_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs) {
    // g = OR(inputs):
    //   for each i: i → g  ⇔ ~i ∨ g
    //   ~g → (or-of-all-inputs) ⇔ g ∨ i1 ∨ i2 ... wait that's wrong.
    // Let me redo:
    //   g → OR  : g → (i1 ∨ i2 ∨ ...)  ⇔ ~g ∨ i1 ∨ i2 ...  (one big clause)
    //   OR → g  : for each i, i → g    ⇔ ~i ∨ g             (per-input)
    std::vector<CMSat::Lit> forward;
    forward.reserve(inputs.size() + 1);
    forward.push_back(~g);
    for (auto l : inputs) forward.push_back(l);
    add_clause(forward);
    for (auto l : inputs) add_clause({~l, g});
}

template<class Solver>
CMSat::Lit AIGToCNF<Solver>::emit_and2(CMSat::Lit a, CMSat::Lit b) {
    CMSat::Lit h = new_helper();
    emit_and_equiv(h, {a, b});
    return h;
}

template<class Solver>
CMSat::Lit AIGToCNF<Solver>::emit_or2(CMSat::Lit a, CMSat::Lit b) {
    CMSat::Lit h = new_helper();
    emit_or_equiv(h, {a, b});
    return h;
}

template<class Solver>
void AIGToCNF<Solver>::emit_ite(CMSat::Lit g, CMSat::Lit s, CMSat::Lit t, CMSat::Lit e) {
    // g ↔ (s ? t : e):
    //   s ∧ ~t → ~g   ⇔ ~s ∨ t ∨ ~g
    //   s ∧ t  → g    ⇔ ~s ∨ ~t ∨ g
    //   ~s ∧ ~e → ~g  ⇔ s ∨ e ∨ ~g
    //   ~s ∧ e → g    ⇔ s ∨ ~e ∨ g
    add_clause({~s, t, ~g});
    add_clause({~s, ~t, g});
    add_clause({s, e, ~g});
    add_clause({s, ~e, g});
}

template<class Solver>
void AIGToCNF<Solver>::emit_xor(CMSat::Lit g, CMSat::Lit a, CMSat::Lit b) {
    // g ↔ (a XOR b) = (a ∧ ~b) ∨ (~a ∧ b)
    //   g → a ∨ b
    //   g → ~a ∨ ~b
    //   ~a ∧ b → g     ⇔ a ∨ ~b ∨ g
    //   a ∧ ~b → g     ⇔ ~a ∨ b ∨ g
    add_clause({~g, a, b});
    add_clause({~g, ~a, ~b});
    add_clause({g, ~a, b});
    add_clause({g, a, ~b});
}

// =============================================================================
// ITE pattern detection
// =============================================================================
//
// An ITE at the AIG level has the shape OR(AND_T, AND_E) where AND_T and
// AND_E share one complementary input (the selector); the other children
// are the then / else values.
//
// In the input-edge-neg model that shape reads as:
//   n.neg = true                                 (outer edge is an OR)
//   n->l, n->r each have neg=true and point to   (the two AND branches
//   t_and nodes                                   referenced through an OR)
// Each AND branch's pair of children (n->l->l/r, n->r->l/r) is a pair of
// signed edges. One edge from AND_T matches an edge from AND_E with the
// same underlying node and opposite sign — that pair is the selector,
// and the remaining children are (then, else).

template<class Solver>
bool AIGToCNF<Solver>::parse_ite_shape(const aig_lit& n, IteShape& out) {
    if (!n.neg || n->type != AIGT::t_and) return false;
    if (n->l == n->r) return false;

    // Disjuncts of the outer OR are the complements of its stored children.
    const aig_lit disj_t = ~n->l;
    const aig_lit disj_e = ~n->r;
    if (disj_t.neg || disj_t->type != AIGT::t_and) return false;
    if (disj_e.neg || disj_e->type != AIGT::t_and) return false;

    const AIG* a = disj_t.get();
    const AIG* b = disj_e.get();
    // Both sub-ANDs must be consumable (fanout ≤ 1 and not yet encoded),
    // otherwise folding them into the ITE would elide a helper another
    // encoded path needs.
    auto can_consume = [&](const AIG* p) -> bool {
        if (cache.find(p) != cache.end()) return false;
        auto it = fanout.find(p);
        return it != fanout.end() && it->second <= 1;
    };
    if (!can_consume(a) || !can_consume(b)) return false;

    const aig_lit& x1 = a->l;
    const aig_lit& x2 = a->r;
    const aig_lit& y1 = b->l;
    const aig_lit& y2 = b->r;

    auto is_lit_complement = [](const aig_lit& x, const aig_lit& y) {
        return x.node && y.node
            && x->type == AIGT::t_lit && y->type == AIGT::t_lit
            && x->var == y->var && x.neg != y.neg;
    };
    // Complement of two sub-AIG references: same node, opposite sign.
    auto is_sub_complement = [](const aig_lit& x, const aig_lit& y) {
        return x.node && y.node
            && x.node == y.node && x.neg != y.neg
            && x->type == AIGT::t_and;
    };

    const aig_lit* sel_x = nullptr;
    const aig_lit* sel_y = nullptr;
    const aig_lit* other_x = nullptr;
    const aig_lit* other_y = nullptr;
    bool matched_lit = false;
    auto try_match = [&](const aig_lit& xa, const aig_lit& xb,
                         const aig_lit& ya, const aig_lit& yb) -> bool {
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
    (void)sel_y;

    out.valid = true;
    out.t_aig = *other_x;
    out.e_aig = *other_y;
    if (matched_lit) {
        out.sel_is_lit = true;
        out.sel_var = (*sel_x)->var;
        out.sel_neg = sel_x->neg;
    } else {
        out.sel_is_lit = false;
        // Selector positive-view + whether we should invert after encoding.
        out.sel_aig = aig_lit(sel_x->node, false);
        out.sel_invert = sel_x->neg;
    }
    return true;
}

template<class Solver>
bool AIGToCNF<Solver>::parse_ite_at(const aig_lit& n, IteParse& out) {
    IteShape sh;
    if (!parse_ite_shape(n, sh)) return false;
    CMSat::Lit s_lit;
    if (sh.sel_is_lit) {
        s_lit = CMSat::Lit(sh.sel_var, sh.sel_neg);
    } else {
        s_lit = encode_edge(sh.sel_aig);
        if (sh.sel_invert) s_lit = ~s_lit;
    }
    out.valid = true;
    out.s_lit = s_lit;
    out.t_aig = sh.t_aig;
    out.e_aig = sh.e_aig;
    return true;
}

// XOR pattern detection. Same outer OR(AND_T, AND_E) structural shape as
// ITE; the distinguishing feature is that BOTH AND_T / AND_E child pairs
// match complementary across the two inner ANDs. XOR(x1, x2) read off
// AND_T's children equals XNOR(a, b) = the node's POSITIVE value; the
// negative (OR-gate) view is therefore XOR(a, b) = ~(emitted helper).
template<class Solver>
bool AIGToCNF<Solver>::try_xor(const aig_lit& n, CMSat::Lit& out) {
    if (!n.neg || n->type != AIGT::t_and) return false;
    if (n->l == n->r) return false;

    const aig_lit disj_t = ~n->l;
    const aig_lit disj_e = ~n->r;
    if (disj_t.neg || disj_t->type != AIGT::t_and) return false;
    if (disj_e.neg || disj_e->type != AIGT::t_and) return false;

    const AIG* a_and = disj_t.get();
    const AIG* b_and = disj_e.get();
    auto can_consume = [&](const AIG* p) -> bool {
        if (cache.find(p) != cache.end()) return false;
        auto it = fanout.find(p);
        return it != fanout.end() && it->second <= 1;
    };
    if (!can_consume(a_and) || !can_consume(b_and)) return false;

    const aig_lit& x1 = a_and->l;
    const aig_lit& x2 = a_and->r;
    const aig_lit& y1 = b_and->l;
    const aig_lit& y2 = b_and->r;

    // Two complementary pairs required. Either (x1↔y1, x2↔y2) or (x1↔y2, x2↔y1).
    const bool matched = (aig_complement(x1, y1) && aig_complement(x2, y2))
                      || (aig_complement(x1, y2) && aig_complement(x2, y1));
    if (!matched) return false;

    CMSat::Lit a_lit = encode_edge(x1);
    CMSat::Lit b_lit = encode_edge(x2);

    // Guard against post-encoding collapses that a well-formed AIG won't
    // produce in practice (new_and would have folded AND(a, ~a) to FALSE
    // upstream) but that could still arise if a shared sub-formula lands
    // here through aggressive CSE.
    if (a_lit == b_lit) {
        // XOR(x, x) = FALSE ⇒ negative-view value = ~FALSE = TRUE.
        out = get_true_lit();
        stats.xor_patterns++;
        return true;
    }
    if (a_lit == ~b_lit) {
        // XOR(x, ~x) = TRUE ⇒ negative-view value = FALSE.
        out = ~get_true_lit();
        stats.xor_patterns++;
        return true;
    }

    CMSat::Lit h = new_helper();
    emit_xor(h, a_lit, b_lit);
    stats.xor_patterns++;
    // h = XOR(x1, x2) = XNOR(a, b) = node's POSITIVE value.
    // encode_edge wants the negative-view literal (OR-gate view = XOR(a, b)).
    out = ~h;
    return true;
}

template<class Solver>
bool AIGToCNF<Solver>::try_ite(const aig_lit& n, CMSat::Lit& out) {
    IteParse p;
    if (!parse_ite_at(n, p)) return false;

    CMSat::Lit t_lit = encode_edge(p.t_aig);
    CMSat::Lit e_lit = encode_edge(p.e_aig);

    // Degenerate folds.
    if (t_lit == e_lit)   { out = t_lit; return true; }                 // ITE(s, t, t) = t
    if (p.s_lit == t_lit) { out = emit_or2(p.s_lit, e_lit);  return true; } // ITE(s, s, e) = s ∨ e
    if (p.s_lit == ~t_lit){ out = emit_and2(~p.s_lit, e_lit); return true; } // ITE(s, ~s, e) = ~s ∧ e
    if (p.s_lit == e_lit) { out = emit_and2(p.s_lit, t_lit);  return true; } // ITE(s, t, s) = s ∧ t
    if (p.s_lit == ~e_lit){ out = emit_or2(~p.s_lit, t_lit);  return true; } // ITE(s, t, ~s) = ~s ∨ t

    CMSat::Lit h = new_helper();
    emit_ite(h, p.s_lit, t_lit, e_lit);
    stats.ite_patterns++;
    out = h;
    return true;
}

} // namespace ArjunNS
