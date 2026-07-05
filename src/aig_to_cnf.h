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
#include "constants.h"
#include "cut_cnf.h"
#include <cryptominisat5/solvertypesmini.h>
#include <algorithm>
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

    uint64_t ite_patterns = 0;
    uint64_t mux3_patterns = 0;
    // Sum of selector counts across fused MUX chains (≥2 each); average chain
    // length = mux_chain_levels_total / mux3_patterns.
    uint64_t mux_chain_levels_total = 0;
    uint64_t xor_patterns = 0;
    uint64_t cut_cnf_patterns = 0;
    uint64_t cut_cnf_clauses = 0;
    // Cut-CNF cones that collapsed to a constant or to a single input
    // projection — these need neither a helper nor any clause.
    uint64_t cut_cnf_const = 0;
    uint64_t cut_cnf_proj = 0;
    // Cut-CNF cones served from the functional (leaves+tt) CSE cache.
    uint64_t cut_cnf_cse_hits = 0;

    double encode_time_s = 0.0;

    void clear() { *this = AIG2CNFStats(); }
    void print(int verb = 1) const;
};

template<class Solver>
class AIGToCNF {
public:
    explicit AIGToCNF(Solver& s) : solver(s) {}

    CMSat::Lit encode(const aig_lit& root, bool force_helper = false);
    std::vector<CMSat::Lit> encode_batch(const std::vector<aig_lit>& roots);

    void set_true_lit(CMSat::Lit t) { my_true_lit = t; my_has_true_lit = true; }
    [[nodiscard]] const AIG2CNFStats& get_stats() const { return stats; }

    void set_detect_ite(bool b) { detect_ite = b; }
    void set_detect_xor(bool b) { detect_xor = b; }
    void set_cut_cnf(bool b) { use_cut_cnf = b; }
    void set_kary_fusion(bool b) { kary_fusion = b; }
    void set_group_cse(bool b) { group_cse = b; }
    void set_ite_sub_selector(bool b) { ite_sub_selector = b; }
    void set_normalize_inputs(bool b) { normalize_inputs = b; }
    void set_max_kary_width(uint32_t w) { max_kary_width = w; }

private:
    Solver& solver;
    AIG2CNFStats stats;

    CMSat::Lit my_true_lit = CMSat::Lit(0, false);
    bool my_has_true_lit = false;

    bool detect_ite = true;
    bool detect_xor = true;
    bool use_cut_cnf = true;        // min-CNF encoding for k≤4-input cones
    // Content-hashed CSE across AND / ITE groups. Off by default: on manthan
    // workloads its maintenance cost outweighs the CNF-size win, and the
    // deduped helpers can hurt SAT propagation. Opt in via set_group_cse(true).
    bool group_cse = false;
    bool ite_sub_selector = true;   // allow non-literal sub-AIG ITE selectors
    bool kary_fusion = true;
    bool normalize_inputs = true;
    uint32_t max_kary_width = 1u << 30;

    // Max MUX-chain fusion depth. Bounds the longest emitted clause (level+3
    // lits) so deep manthan ITE chains stay SAT-friendly while cutting helpers ~4×.
    static constexpr uint32_t kMaxMuxChain = 8;

    // Fanout counted by node identity. Leaf nodes are never helpers and
    // don't need fanout tracking.
    struct AigNodeHash {
        size_t operator()(const AIG* p) const noexcept {
            return p ? std::hash<uint64_t>{}(p->nid) : 0;
        }
    };
    std::unordered_map<const AIG*, uint32_t, AigNodeHash> fanout;

    // Encoding cache by node identity: the CNF literal for the AND node's
    // POSITIVE value (caller applies edge-sign). Leaves aren't cached.
    std::unordered_map<const AIG*, CMSat::Lit, AigNodeHash> cache;

    // Content-hashed CSE for k-ary AND groups and ITE (s, t, e) triples.
    // Only populated when group_cse is true.
    using LitKey = std::vector<CMSat::Lit>;
    struct LitKeyCmp {
        bool operator()(const LitKey& a, const LitKey& b) const {
            if (a.size() != b.size()) return a.size() < b.size();
            for (size_t i = 0; i < a.size(); i++) {
                if (a[i] != b[i]) {
                    if (a[i].var() != b[i].var()) return a[i].var() < b[i].var();
                    return (int)a[i].sign() < (int)b[i].sign();
                }
            }
            return false;
        }
    };
    std::map<LitKey, CMSat::Lit, LitKeyCmp> and_group_cse;
    // ITE CSE key: (s, t, e) each packed as (var << 1 | sign).
    using IteKey = std::tuple<uint32_t, uint32_t, uint32_t>;
    std::map<IteKey, CMSat::Lit> ite_cse;

    // Functional CSE for ≤4-input cut cones. Key: [num_inputs, sorted leaf
    // vars…, canonical TT]. Same-function cones over the same vars share a
    // helper. Tiny key, so unlike group_cse it's always on.
    std::map<std::vector<uint32_t>, CMSat::Lit> cut_cse;

    // Functional CSE for fused MUX chains. Key: packed (var<<1|sign) selector
    // / then-value / base lits, so literal-identical ITE chains share a helper.
    std::map<std::vector<uint32_t>, CMSat::Lit> mux_chain_cse;

    static void canon_sort_lits(std::vector<CMSat::Lit>& v) {
        std::sort(v.begin(), v.end(), [](CMSat::Lit a, CMSat::Lit b) {
            if (a.var() != b.var()) return a.var() < b.var();
            return (int)a.sign() < (int)b.sign();
        });
    }

    void count_fanout(const aig_lit& root);
    CMSat::Lit encode_edge(const aig_lit& n);
    // Encode the node n's POSITIVE value as an AND (k-ary). Callers handle
    // caching and outer-sign application.
    CMSat::Lit encode_and_positive(const AIG* n);
    CMSat::Lit get_true_lit();
    CMSat::Lit new_helper();

    // Collect k-ary AND conjuncts as signed edges. Only flatten through
    // positive-reference, fanout-1 AND nodes — else sharing would be lost.
    void collect_and_edges(const aig_lit& child, std::vector<aig_lit>& out);

    // ITE pattern detection. `n` is an OR-gate ref (n.neg, t_and, l!=r)
    // decomposing as OR(AND_T, AND_E). If the two sub-ANDs share one
    // complementary input pair (lit or sub-AIG), that pair is the selector
    // and the remaining children are the then / else values.
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

    // XOR pattern detection. Same OR(AND_T, AND_E) shape as ITE but with TWO
    // complementary pairs (both cancel); value is XOR(a,b) off an inner AND.
    bool try_xor(const aig_lit& n, CMSat::Lit& out);

    // Cut-CNF: collect the ≤4-input cone at `n`, compute its truth table, and
    // emit the minimum-clause CNF with one helper (MAJ3: 6 clauses vs 13).
    // Returns the helper for n's SIGNED-EDGE value (n.neg folded in).
    bool try_cut_cnf(const aig_lit& n, CMSat::Lit& out);

    // AIG-level simplification of a k-ary AND conjunct list, BEFORE CNF
    // encoding — catches what lit-level dedup misses (e.g. complementary
    // sub-AIGs). Rules: drop TRUE / FALSE short-circuits; dedup signed edges;
    // complementary pair → FALSE; OR-conjunct absorption. Returns true with
    // out_const set when the group folds to a constant; else edits in place.
    bool structural_simplify_and(std::vector<aig_lit>& conjuncts, bool& out_const);

    void emit_and_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    void emit_or_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    void emit_ite(CMSat::Lit g, CMSat::Lit s, CMSat::Lit t, CMSat::Lit e);
    // k-way MUX chain: g = ITE(s0,t0, …ITE(s_{k-1},t_{k-1}, base)). 2(k+1)
    // clauses, 1 helper — generalises MUX3 and collapses an ITE chain.
    void emit_mux_chain(CMSat::Lit g, const std::vector<CMSat::Lit>& sels,
                        const std::vector<CMSat::Lit>& tvals, CMSat::Lit base);
    void emit_xor(CMSat::Lit g, CMSat::Lit a, CMSat::Lit b);

    // True if two signed edges are logical complements: same node, opposite
    // sign (covers lits, consts, sub-AIGs uniformly).
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
    // Degenerate gates (e.g. AND(x,x)) can yield repeated literals; collapse
    // duplicates and drop tautologies so each var appears at most once.
    std::vector<CMSat::Lit> tmp(cl);
    std::sort(tmp.begin(), tmp.end());
    tmp.erase(std::unique(tmp.begin(), tmp.end()), tmp.end());
    for (size_t i = 1; i < tmp.size(); i++) {
        if (tmp[i].var() == tmp[i-1].var()) return; // tautology
    }
    solver.add_clause(tmp);
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
void AIGToCNF<Solver>::count_fanout(const aig_lit& root) {
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
CMSat::Lit AIGToCNF<Solver>::encode(const aig_lit& root, bool force_helper) {
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
std::vector<CMSat::Lit> AIGToCNF<Solver>::encode_batch(const std::vector<aig_lit>& roots) {
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
CMSat::Lit AIGToCNF<Solver>::encode_edge(const aig_lit& n) {
    stats.nodes_visited++;
    if (n->type == AIGT::t_const) {
        CMSat::Lit t = get_true_lit();
        return n.neg ? ~t : t;
    }
    if (n->type == AIGT::t_lit) {
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

    // ITE / XOR detection. The shape (AND of two negative-edge inner ANDs)
    // matches both polarities: n.neg=true → ITE/XOR, n.neg=false → the
    // De Morgan dual. try_* returns the ITE/XOR (negative-view) helper; cache
    // stores ~helper and the return applies n.neg. XOR runs first (it's a
    // degenerate ITE that ITE matches less cleanly).
    {
        CMSat::Lit neg_lit;
        if (detect_xor && try_xor(n, neg_lit)) {
            cache[n.get()] = ~neg_lit;
            return n.neg ? neg_lit : ~neg_lit;
        }
        if (detect_ite && try_ite(n, neg_lit)) {
            cache[n.get()] = ~neg_lit;
            return n.neg ? neg_lit : ~neg_lit;
        }
    }

    // Cut-CNF (both polarities): encodes the signed-edge value directly (n.neg
    // folded into the TT), so the helper IS the ref lit; cache stores ~ when n.neg.
    if (use_cut_cnf) {
        CMSat::Lit cut_lit;
        if (try_cut_cnf(n, cut_lit)) {
            cache[n.get()] = n.neg ? ~cut_lit : cut_lit;
            return cut_lit;
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

    // AIG-level structural simplification BEFORE encoding — catches
    // complementary / absorbed sub-AIGs that lit-level dedup would miss.
    if (normalize_inputs) {
        bool is_const = false;
        if (structural_simplify_and(conjunct_edges, is_const)) {
            return is_const ? get_true_lit() : ~get_true_lit();
        }
        if (conjunct_edges.empty()) return get_true_lit();
        if (conjunct_edges.size() == 1) return encode_edge(conjunct_edges[0]);
    }

    // Encode each conjunct. Also apply basic constant / dedup normalisation.
    std::vector<CMSat::Lit> inputs;
    inputs.reserve(conjunct_edges.size());
    for (const auto& c : conjunct_edges) inputs.push_back(encode_edge(c));

    if (normalize_inputs) {
        // Drop TRUE, detect FALSE / complementary pairs. Only use the TRUE
        // literal if already materialised — allocating it here would add a
        // spurious helper + unit clause to every constant-free AND.
        const bool has_true = my_has_true_lit;
        const CMSat::Lit true_lit = has_true ? my_true_lit : CMSat::Lit(0, false);
        std::vector<CMSat::Lit> cleaned;
        cleaned.reserve(inputs.size());
        bool folded_false = false;
        for (auto l : inputs) {
            if (has_true && l == true_lit) continue;                       // drop TRUE
            if (has_true && l == ~true_lit) { folded_false = true; break; } // FALSE short-circuit
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
        if (folded_false) return ~get_true_lit();
        if (cleaned.empty()) return get_true_lit();
        if (cleaned.size() == 1) return cleaned[0];
        inputs = std::move(cleaned);
    }

    // Content-hashed group CSE: if we've already emitted an AND with this
    // exact canonicalised input list, return its helper instead of creating
    // a duplicate.
    if (group_cse) {
        canon_sort_lits(inputs);
        auto it_cse = and_group_cse.find(inputs);
        if (it_cse != and_group_cse.end()) {
            return it_cse->second;
        }
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
    if (group_cse) and_group_cse[inputs] = h;
    return h;
}

// Flatten k-ary AND through positive-reference fanout-1 AND nodes; each
// conjunct is a signed edge ready for encoding. Stepping through a positive
// AND with complemented children is the De Morgan pattern, implicit here
// because negation lives on edges.
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
    //   g → OR : g → (i1 ∨ i2 ∨ ...) ⇔ ~g ∨ i1 ∨ i2 ...  (one big clause)
    //   OR → g : for each i, i → g   ⇔ ~i ∨ g             (per-input)
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
void AIGToCNF<Solver>::emit_mux_chain(CMSat::Lit g,
                                      const std::vector<CMSat::Lit>& sels,
                                      const std::vector<CMSat::Lit>& tvals,
                                      CMSat::Lit base) {
    // g ↔ ITE(s0,t0, ITE(s1,t1, … ITE(s_{k-1},t_{k-1}, base))).
    // Level i is chosen when s0…s_{i-1} are all false and s_i is true; the
    // base when every selector is false. Per chosen value v with path P:
    //   P ∧  v →  g   and   P ∧ ¬v → ¬g
    // `prefix` accumulates the earlier selectors s0…s_{i-1} that appear
    // positively in every level-i clause (the negation of "s_j false").
    assert(sels.size() == tvals.size() && sels.size() >= 1);
    SLOW_DEBUG_DO(assert(g.var() != base.var()));
    std::vector<CMSat::Lit> prefix;
    prefix.reserve(sels.size() + 2);
    for (size_t i = 0; i < sels.size(); i++) {
        std::vector<CMSat::Lit> c1(prefix);
        c1.push_back(~sels[i]); c1.push_back(~tvals[i]); c1.push_back(g);
        add_clause(c1);
        std::vector<CMSat::Lit> c2(prefix);
        c2.push_back(~sels[i]); c2.push_back(tvals[i]); c2.push_back(~g);
        add_clause(c2);
        prefix.push_back(sels[i]);
    }
    std::vector<CMSat::Lit> b1(prefix);
    b1.push_back(~base); b1.push_back(g);
    add_clause(b1);
    std::vector<CMSat::Lit> b2(prefix);
    b2.push_back(base); b2.push_back(~g);
    add_clause(b2);
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
// An AIG ITE has shape OR(AND_T, AND_E) where the two sub-ANDs share one
// complementary input (the selector); the remaining children are then/else.
// In the edge-neg model: n.neg=true, n->l/n->r both neg=true onto t_and
// nodes. The AND_T/AND_E child edge that matches with opposite sign is the
// selector; the rest are (then, else).

template<class Solver>
bool AIGToCNF<Solver>::parse_ite_shape(const aig_lit& n, IteShape& out) {
    if (n->type != AIGT::t_and) return false;
    if (n->l == n->r) return false;
    // Polarity-agnostic shape: matches ITE (n.neg=true) and its dual ~ITE
    // (n.neg=false). Caller applies n.neg to the returned helper.

    // Disjuncts of the outer OR are the complements of its stored children.
    const aig_lit disj_t = ~n->l;
    const aig_lit disj_e = ~n->r;
    if (disj_t.neg || disj_t->type != AIGT::t_and) return false;
    if (disj_e.neg || disj_e->type != AIGT::t_and) return false;

    const AIG* a = disj_t.get();
    const AIG* b = disj_e.get();
    // Both sub-ANDs must be consumable (fanout ≤ 1, not yet encoded), else
    // folding them into the ITE would elide a helper another path needs.
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

// XOR detection. Same OR(AND_T, AND_E) shape as ITE, but BOTH child pairs
// match complementary across the two inner ANDs. XOR(x1,x2) = XNOR(a,b) =
// the node's POSITIVE value; the OR-gate (negative) view is ~(emitted helper).
template<class Solver>
bool AIGToCNF<Solver>::try_xor(const aig_lit& n, CMSat::Lit& out) {
    if (n->type != AIGT::t_and) return false;
    if (n->l == n->r) return false;
    // Same reasoning as parse_ite_shape: the two-inner-ANDs structure
    // matches XOR at n.neg=true and XNOR at n.neg=false. The emitted
    // helper represents the XOR value; caller applies n.neg.

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

    // Guard against post-encoding collapses a well-formed AIG won't produce
    // (new_and folds AND(a,~a) upstream) but CSE-shared sub-formulas might.
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
    // Constant-operand folds: out = XNOR(a_lit, b_lit) (the OR-gate view);
    // XNOR with a constant collapses to the other operand. No helper, no clause.
    if (my_has_true_lit) {
        const CMSat::Lit TL = my_true_lit;
        if (a_lit ==  TL) { out =  b_lit; stats.xor_patterns++; return true; }
        if (a_lit == ~TL) { out = ~b_lit; stats.xor_patterns++; return true; }
        if (b_lit ==  TL) { out =  a_lit; stats.xor_patterns++; return true; }
        if (b_lit == ~TL) { out = ~a_lit; stats.xor_patterns++; return true; }
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

    // k-way MUX-chain fusion: while the else-branch is a consumable ITE-shaped
    // AND (fanout ≤ 1, uncached), fold it in. 1 helper + 2(k+1) clauses vs the
    // k-1 helpers chained MUX3 spends (4× cut on manthan's deep chains). Capped
    // at kMaxMuxChain to keep the longest clause (level+3) SAT-friendly.
    {
        std::vector<std::pair<CMSat::Lit, aig_lit>> levels;  // (selector, then)
        levels.emplace_back(p.s_lit, p.t_aig);
        aig_lit base = p.e_aig;
        while (levels.size() < kMaxMuxChain) {
            if (!base || base->type != AIGT::t_and || !base.neg) break;
            const AIG* bn = base.get();
            if (cache.find(bn) != cache.end()) break;
            auto it_fo = fanout.find(bn);
            if (it_fo == fanout.end() || it_fo->second > 1) break;
            IteParse q;
            if (!parse_ite_at(base, q)) break;
            levels.emplace_back(q.s_lit, q.t_aig);
            base = q.e_aig;
        }
        if (levels.size() >= 2) {
            std::vector<CMSat::Lit> sels, t_lits;
            sels.reserve(levels.size());
            t_lits.reserve(levels.size());
            for (auto& lv : levels) {
                sels.push_back(lv.first);
                t_lits.push_back(encode_edge(lv.second));
            }
            CMSat::Lit base_lit = encode_edge(base);

            // Functional CSE: a structurally distinct chain over the same
            // literal sequence is the same function — reuse its helper.
            auto pack = [](CMSat::Lit l) { return (l.var() << 1) | (l.sign() ? 1u : 0u); };
            std::vector<uint32_t> key;
            key.reserve(2 * levels.size() + 2);
            for (auto l : sels)   key.push_back(pack(l));
            key.push_back(0xFFFFFFFFu);  // separator: selectors | then-values
            for (auto l : t_lits) key.push_back(pack(l));
            key.push_back(pack(base_lit));
            auto it_cse = mux_chain_cse.find(key);
            if (it_cse != mux_chain_cse.end()) {
                out = it_cse->second;
                return true;
            }

            CMSat::Lit h = new_helper();
            emit_mux_chain(h, sels, t_lits, base_lit);
            stats.mux3_patterns++;
            stats.mux_chain_levels_total += levels.size();
            mux_chain_cse[key] = h;
            out = h;
            return true;
        }
    }

    CMSat::Lit t_lit = encode_edge(p.t_aig);
    CMSat::Lit e_lit = encode_edge(p.e_aig);

    // Constant-branch folds. A branch can hit TRUE even when AIG-level folds
    // didn't fire (e.g. collapsed inside try_cut_cnf); turns a 4-clause ITE
    // into a 3-clause AND/OR.
    if (my_has_true_lit) {
        const CMSat::Lit TL = my_true_lit;
        if (t_lit ==  TL) { out = emit_or2(p.s_lit, e_lit);   return true; } // ITE(s,1,e)=s∨e
        if (t_lit == ~TL) { out = emit_and2(~p.s_lit, e_lit); return true; } // ITE(s,0,e)=~s∧e
        if (e_lit ==  TL) { out = emit_or2(~p.s_lit, t_lit);  return true; } // ITE(s,t,1)=~s∨t
        if (e_lit == ~TL) { out = emit_and2(p.s_lit, t_lit);  return true; } // ITE(s,t,0)=s∧t
    }

    // Degenerate folds.
    if (t_lit == e_lit)   { out = t_lit; return true; }                 // ITE(s, t, t) = t
    if (p.s_lit == t_lit) { out = emit_or2(p.s_lit, e_lit);  return true; } // ITE(s, s, e) = s ∨ e
    if (p.s_lit == ~t_lit){ out = emit_and2(~p.s_lit, e_lit); return true; } // ITE(s, ~s, e) = ~s ∧ e
    if (p.s_lit == e_lit) { out = emit_and2(p.s_lit, t_lit);  return true; } // ITE(s, t, s) = s ∧ t
    if (p.s_lit == ~e_lit){ out = emit_or2(~p.s_lit, t_lit);  return true; } // ITE(s, t, ~s) = ~s ∨ t

    // Content-hashed ITE CSE: canonicalise selector polarity (flip (s,t,e)→
    // (~s,e,t) when s is negative), look up the triple. Always on — an
    // identical triple is the same gate, and the 3-int key is cheap.
    {
        CMSat::Lit s = p.s_lit;
        CMSat::Lit t = t_lit;
        CMSat::Lit e = e_lit;
        if (s.sign()) { s = ~s; std::swap(t, e); }
        auto pack = [](CMSat::Lit l) { return (l.var() << 1) | (l.sign() ? 1u : 0u); };
        IteKey key{pack(s), pack(t), pack(e)};
        auto it = ite_cse.find(key);
        if (it != ite_cse.end()) {
            stats.ite_patterns++;
            out = it->second;
            return true;
        }
        CMSat::Lit h = new_helper();
        emit_ite(h, s, t, e);
        ite_cse[key] = h;
        stats.ite_patterns++;
        out = h;
        return true;
    }
}

// =============================================================================
// Structural AIG-level simplification for k-ary AND conjunct lists
// =============================================================================

template<class Solver>
bool AIGToCNF<Solver>::structural_simplify_and(std::vector<aig_lit>& conjuncts,
                                               bool& out_const)
{
    // (1) Constant fold. FALSE in any slot makes the group FALSE; TRUE drops.
    {
        std::vector<aig_lit> tmp;
        tmp.reserve(conjuncts.size());
        for (const auto& c : conjuncts) {
            if (c->type == AIGT::t_const) {
                if (c.neg) { out_const = false; return true; }  // FALSE edge
                continue;                                        // TRUE edge
            }
            tmp.push_back(c);
        }
        conjuncts.swap(tmp);
    }
    // (2) Dedup by signed edge via one sort+unique (equality is direct: same
    // node + sign). Order on the monotonic `nid`, not the raw pointer, so ASLR
    // doesn't leak into conjunct order — the OR-absorption pass below is
    // order-sensitive and would otherwise differ across runs.
    {
        std::sort(conjuncts.begin(), conjuncts.end(),
            [](const aig_lit& a, const aig_lit& b) {
                if (a.node->nid != b.node->nid) return a.node->nid < b.node->nid;
                return (int)a.neg < (int)b.neg;
            });
        conjuncts.erase(std::unique(conjuncts.begin(), conjuncts.end()),
                         conjuncts.end());
    }
    // (3) Complementary pair: after sort by nid, same-node entries are
    // adjacent and differ only in sign.
    for (size_t i = 0; i + 1 < conjuncts.size(); i++) {
        if (conjuncts[i].node.get() == conjuncts[i+1].node.get()
            && conjuncts[i].neg != conjuncts[i+1].neg) {
            out_const = false;
            return true;
        }
    }
    // (4) OR-conjunct absorption: AND(a, OR(a,…)) → drop the OR. An OR conjunct
    // is a negative-edge AND whose disjuncts are the complements of its stored
    // children; if a sibling matches one, the OR absorbs.
    std::vector<aig_lit> kept;
    kept.reserve(conjuncts.size());
    for (size_t i = 0; i < conjuncts.size(); i++) {
        const aig_lit& ci = conjuncts[i];
        bool absorbed = false;
        // (5) OR-disjunct resolution: an OR conjunct's stored children are the
        // complements of its disjuncts. If a sibling equals a stored child,
        // that disjunct is FALSE, so the OR narrows to the other. AND(a,OR(~a,b))=AND(a,b).
        aig_lit resolved;
        if (ci->type == AIGT::t_and && ci.neg && ci->l != ci->r) {
            for (size_t j = 0; j < conjuncts.size(); j++) {
                if (i == j) continue;
                // sibling_j equals one of the disjuncts iff it's the complement
                // of ci's stored child.
                if (aig_complement(conjuncts[j], ci->l) ||
                    aig_complement(conjuncts[j], ci->r)) {
                    absorbed = true;
                    break;
                }
                if (conjuncts[j] == ci->l)      resolved = ~ci->r;
                else if (conjuncts[j] == ci->r) resolved = ~ci->l;
            }
        }
        if (absorbed) { continue; }
        if (resolved.node) { kept.push_back(resolved); continue; }
        kept.push_back(ci);
    }
    conjuncts.swap(kept);
    return false;
}

// =============================================================================
// Cut-CNF encoding
// =============================================================================
//
// Collect the consumable AND cone at n (internal fanout ≤ 1, uncached),
// compute the truth table of n's SIGNED-EDGE value over ≤4 inputs, and emit
// the minimum-clause CNF for it. MAJ3: 6 clauses + 1 helper vs 13 + 4 naive.

template<class Solver>
bool AIGToCNF<Solver>::try_cut_cnf(const aig_lit& n, CMSat::Lit& out) {
    constexpr uint32_t MAX_LEAVES = 5;
    if (n->type != AIGT::t_and) return false;

    auto can_consume = [&](const AIG* p) -> bool {
        if (cache.find(p) != cache.end()) return false;
        auto it = fanout.find(p);
        return it != fanout.end() && it->second <= 1;
    };

    // DFS the cone on SIGNED edges: leaves are non-AND nodes or non-consumable
    // ANDs, interior ANDs recurse into signed children. Qualification counts
    // DISTINCT input slots (leaf key = var for a literal, nid for a sub-AIG;
    // sign folds into the TT later), so a wide cone reusing ≤4 vars still cuts.
    std::unordered_map<aig_lit, uint32_t> leaf_idx;
    std::vector<aig_lit> leaves;
    std::set<std::pair<int, uint64_t>> distinct_slots;
    bool abort_flag = false;
    std::function<void(const aig_lit&)> dfs = [&](const aig_lit& m) {
        if (abort_flag) return;
        const bool is_interior_and = m->type == AIGT::t_and
            && (m.node == n.node || can_consume(m.get()));
        if (!is_interior_and) {
            if (leaf_idx.count(m)) return;
            const std::pair<int, uint64_t> slot_key =
                (m->type == AIGT::t_lit)
                    ? std::make_pair(0, (uint64_t)m->var)
                    : std::make_pair(1, m->nid);
            if (!distinct_slots.count(slot_key)
                && distinct_slots.size() >= MAX_LEAVES) {
                abort_flag = true;
                return;
            }
            distinct_slots.insert(slot_key);
            leaf_idx[m] = leaves.size();
            leaves.push_back(m);
            return;
        }
        dfs(m->l);
        if (!abort_flag && m->r != m->l) dfs(m->r);
    };
    dfs(n);
    if (abort_flag || leaves.empty()) return false;

    // Encode each leaf edge to a CNF lit, then dedup to ≤ MAX_LEAVES slots by
    // variable (leaves on the same var, even opposite signs, share a slot).
    std::vector<CMSat::Lit> leaf_lits;
    leaf_lits.reserve(leaves.size());
    for (const auto& l : leaves) leaf_lits.push_back(encode_edge(l));

    std::unordered_map<uint32_t, uint32_t> var_to_slot;
    std::vector<CMSat::Lit> slot_lits;
    std::vector<uint32_t> leaf_slot(leaves.size());
    std::vector<bool> leaf_sign(leaves.size());
    for (size_t i = 0; i < leaf_lits.size(); i++) {
        uint32_t v = leaf_lits[i].var();
        auto it = var_to_slot.find(v);
        uint32_t slot;
        if (it == var_to_slot.end()) {
            if (slot_lits.size() >= MAX_LEAVES) return false;
            slot = slot_lits.size();
            var_to_slot[v] = slot;
            slot_lits.emplace_back(v, false);
        } else {
            slot = it->second;
        }
        leaf_slot[i] = slot;
        leaf_sign[i] = leaf_lits[i].sign();
    }

    const uint32_t num_inputs = slot_lits.size();
    if (num_inputs == 0) return false;
    const uint32_t num_mt = 1u << num_inputs;  // ≤ 32 (MAX_LEAVES = 5)
    // num_mt == 32 makes (1u << num_mt) undefined behaviour; build all-ones
    // without overflowing.
    const uint32_t full_mask = (num_mt >= 32) ? 0xFFFFFFFFu
                                              : ((1u << num_mt) - 1);

    // Build per-leaf minterm masks.
    std::vector<uint32_t> leaf_mask(leaves.size());
    for (size_t i = 0; i < leaves.size(); i++) {
        uint32_t sm = 0;
        for (uint32_t m = 0; m < num_mt; m++) {
            if ((m >> leaf_slot[i]) & 1u) sm |= (1u << m);
        }
        leaf_mask[i] = leaf_sign[i] ? (sm ^ full_mask) : sm;
    }

    // Evaluate each interior node's POSITIVE value once (cached by node
    // pointer); the final TT applies the requested edge sign at the root.
    std::unordered_map<const AIG*, uint32_t> eval_cache;
    std::function<uint32_t(const aig_lit&)> eval = [&](const aig_lit& m) -> uint32_t {
        auto it_leaf = leaf_idx.find(m);
        if (it_leaf != leaf_idx.end()) return leaf_mask[it_leaf->second];
        auto it_c = eval_cache.find(m.get());
        if (it_c != eval_cache.end()) {
            const uint32_t v_pos = it_c->second;
            return m.neg ? ((~v_pos) & full_mask) : v_pos;
        }
        assert(m->type == AIGT::t_and);
        const uint32_t lv = eval(m->l);
        const uint32_t rv = (m->r == m->l) ? lv : eval(m->r);
        const uint32_t v_pos = lv & rv;
        eval_cache[m.get()] = v_pos;
        return m.neg ? ((~v_pos) & full_mask) : v_pos;
    };
    const uint32_t tt = eval(n);

    // Constant cone (whole sub-AIG FALSE or TRUE): no helper/clauses, the TRUE
    // literal (or its negation) IS the value. Catches contradictory /
    // tautological cones the AIG-level folds miss (contradiction spans ≥2 levels).
    if (tt == 0) {
        out = ~get_true_lit();
        stats.cut_cnf_const++;
        return true;
    }
    if (tt == full_mask) {
        out = get_true_lit();
        stats.cut_cnf_const++;
        return true;
    }

    // Projection cone: f == x_s (possibly negated) — functionally just one
    // leaf, so return that leaf lit, no helper/clauses. Source: a multi-level
    // cone whose other inputs cancel (e.g. AND(x, OR(x,y)) flattened).
    for (uint32_t s = 0; s < num_inputs; s++) {
        uint32_t proj = 0;
        for (uint32_t m = 0; m < num_mt; m++) {
            if ((m >> s) & 1u) proj |= (1u << m);
        }
        if (tt == proj) {
            out = slot_lits[s];
            stats.cut_cnf_proj++;
            return true;
        }
        if (tt == (proj ^ full_mask)) {
            out = ~slot_lits[s];
            stats.cut_cnf_proj++;
            return true;
        }
    }

    // Functional CSE: canonicalise by sorting leaf slots by var id and
    // permuting the TT to match, so same-function cones over the same vars
    // collide on one key and share a helper.
    {
        std::vector<uint32_t> order(num_inputs);
        for (uint32_t i = 0; i < num_inputs; i++) order[i] = i;
        std::sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) {
            return slot_lits[a].var() < slot_lits[b].var();
        });
        uint32_t canon_tt = 0;
        for (uint32_t mp = 0; mp < num_mt; mp++) {
            uint32_t m = 0;
            for (uint32_t sp = 0; sp < num_inputs; sp++) {
                if ((mp >> sp) & 1u) m |= 1u << order[sp];
            }
            if ((tt >> m) & 1u) canon_tt |= (1u << mp);
        }
        const uint32_t compl_tt = canon_tt ^ full_mask;
        const bool use_compl = canon_tt > compl_tt;
        const uint32_t final_tt = use_compl ? compl_tt : canon_tt;

        std::vector<uint32_t> key;
        key.reserve(num_inputs + 2);
        key.push_back(num_inputs);
        for (uint32_t i = 0; i < num_inputs; i++) key.push_back(slot_lits[order[i]].var());
        key.push_back(final_tt);

        auto it_cse = cut_cse.find(key);
        if (it_cse != cut_cse.end()) {
            stats.cut_cnf_cse_hits++;
            out = use_compl ? ~it_cse->second : it_cse->second;
            return true;
        }

        const auto& min_cnf = cut_cnf::min_cnf_for_tt(num_inputs, tt);

        // Verify the min-CNF really encodes `tt`: every minterm must force g to
        // the tt bit. Catches a bad cut_cnf entry or a canonicalisation slip.
        SLOW_DEBUG_DO({
            for (uint32_t m = 0; m < num_mt; m++) {
                bool forced_false = false;
                bool forced_true = false;
                for (const auto& c : min_cnf.clauses) {
                    bool inputs_sat = false;
                    for (uint32_t i = 0; i < num_inputs; i++) {
                        if (!(c.present & (1u << i))) continue;
                        const bool bit = (m >> i) & 1u;
                        const bool neg = (c.sign >> i) & 1u;
                        if (neg ? !bit : bit) { inputs_sat = true; break; }
                    }
                    if (inputs_sat) continue;          // clause already satisfied
                    // Inputs all false ⇒ the clause's g-literal must hold.
                    if (c.g_sign) forced_false = true; // clause is (… ∨ ¬g) ⇒ g = 0
                    else          forced_true = true;  // clause is (… ∨  g) ⇒ g = 1
                }
                const bool want = (tt >> m) & 1u;
                assert(!(forced_false && forced_true) && "cut min-CNF contradicts itself");
                assert((want ? !forced_false : !forced_true)
                       && "cut min-CNF does not encode the cone truth table");
            }
        });

        CMSat::Lit h = new_helper();
        for (const auto& c : min_cnf.clauses) {
            std::vector<CMSat::Lit> cl;
            cl.reserve(num_inputs + 1);
            for (uint32_t i = 0; i < num_inputs; i++) {
                if (!(c.present & (1u << i))) continue;
                const bool is_neg = (c.sign >> i) & 1u;
                cl.push_back(is_neg ? ~slot_lits[i] : slot_lits[i]);
            }
            cl.push_back(c.g_sign ? ~h : h);
            add_clause(cl);
        }
        stats.cut_cnf_patterns++;
        stats.cut_cnf_clauses += min_cnf.clauses.size();
        // h is the lit for the cone's function; the key stores the lit for
        // `final_tt` (possibly the complement), so flip when use_compl.
        cut_cse[key] = use_compl ? ~h : h;
        out = h;
        return true;
    }
}

} // namespace ArjunNS
