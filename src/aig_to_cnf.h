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
#include "cut_cnf.h"
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

    // Group-CSE contribution counters.
    uint64_t cse_and_hits = 0;
    uint64_t cse_ite_hits = 0;

    // How often collect_and_edges flattens through a positive-edge AND. In
    // the new input-edge-neg model this subsumes the old NOT-wrapper-of-OR
    // DeMorgan rewrite: a "double-negated OR" becomes a positive edge to
    // the underlying AND, whose children are the negations of the original
    // disjuncts — exactly the shape DeMorgan targeted.
    uint64_t demorgan_and_flat = 0;

    // Structural (AIG-level) simplification counters for the k-ary AND
    // conjunct list, applied BEFORE encoding conjuncts as CNF literals.
    uint64_t aig_dedup_and = 0;       // duplicate conjuncts dropped
    uint64_t aig_complement_and = 0;  // x and ~x in same group → FALSE
    uint64_t absorption_and = 0;      // AND(a, OR(a, ...)) → drop OR
    uint64_t dedup_const_and = 0;     // group folded to constant

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
    void set_cut_cnf(bool b) { use_cut_cnf = b; }
    void set_kary_fusion(bool b) { kary_fusion = b; }
    void set_group_cse(bool b) { group_cse = b; }
    void set_ite_sub_selector(bool b) { ite_sub_selector = b; }
    // The DeMorgan-flatten toggle is a no-op in the new model — flattening
    // through what used to be NOT-wrappers of OR gates is already captured
    // by collect_and_edges's positive-edge AND descent. Kept for API
    // compatibility.
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
    bool use_cut_cnf = true;        // min-CNF encoding for k≤4-input cones
    // Content-hashed CSE across AND / ITE groups. Off by default: on real
    // manthan workloads the content-hash maintenance cost outweighs the
    // CNF-size reduction, and the helpers it dedups can hurt downstream
    // SAT propagation. Enable via set_group_cse(true) to opt in.
    bool group_cse = false;
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

    static void canon_sort_lits(std::vector<CMSat::Lit>& v) {
        std::sort(v.begin(), v.end(), [](CMSat::Lit a, CMSat::Lit b) {
            if (a.var() != b.var()) return a.var() < b.var();
            return (int)a.sign() < (int)b.sign();
        });
    }

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

    // Cut-CNF: collect the ≤4-distinct-input cone rooted at `n`, compute
    // its 16-bit truth table, look up the minimum-clause CNF, and emit it
    // with one helper. Typical win: MAJ3 encodes in 6 clauses vs 13 for
    // the naive (a∧b) ∨ (a∧c) ∨ (b∧c). Returns the helper literal
    // representing the SIGNED-EDGE value of n (n.neg already folded in).
    bool try_cut_cnf(const aig_lit& n, CMSat::Lit& out);

    // AIG-level structural simplification of a k-ary AND conjunct list.
    // Applied BEFORE encoding conjuncts as CNF literals — catches patterns
    // that lit-level dedup misses (e.g., complementary sub-AIGs that
    // would otherwise become distinct helpers).
    //
    // Rules:
    //   (1) Drop TRUE; FALSE short-circuits to FALSE.
    //   (2) Dedup (same signed edge).
    //   (3) Complementary pair (same node, opposite sign) → FALSE.
    //   (4) OR-conjunct absorption: for an OR conjunct (negative-edge
    //       AND), if another conjunct matches one of the OR's disjuncts
    //       (= complement of the OR's stored child), drop the OR.
    //
    // Returns true and sets out_const when the group folds to a constant.
    // Otherwise updates conjuncts in place.
    bool structural_simplify_and(std::vector<aig_lit>& conjuncts, bool& out_const);

    void emit_and_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    void emit_or_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    void emit_ite(CMSat::Lit g, CMSat::Lit s, CMSat::Lit t, CMSat::Lit e);
    // MUX3: g = ITE(s1, a, ITE(s2, b, c)). 6 clauses, 1 helper — beats
    // two nested ITEs (8 clauses, 2 helpers).
    void emit_mux3(CMSat::Lit g, CMSat::Lit s1, CMSat::Lit a,
                   CMSat::Lit s2, CMSat::Lit b, CMSat::Lit c);
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

    // Cut-CNF: applicable to both polarities. Encodes the signed-edge value
    // directly (n.neg is folded into the TT), so the returned helper IS the
    // reference literal; the positive-value cache entry is ~cut_lit when n.neg.
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
            stats.dedup_const_and++;
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

    // Content-hashed group CSE: if we've already emitted an AND with this
    // exact canonicalised input list, return its helper instead of creating
    // a duplicate.
    if (group_cse) {
        canon_sort_lits(inputs);
        auto it_cse = and_group_cse.find(inputs);
        if (it_cse != and_group_cse.end()) {
            stats.cse_and_hits++;
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

// Flatten k-ary AND through positive-reference fanout-1 AND nodes. Each
// conjunct returned is a signed edge ready for encoding. Stepping through a
// positive-edge AND whose children carry complements is exactly the
// De Morgan pattern the old model handled via a dedicated NOT-wrapper
// detector; it's implicit here because negation lives on edges.
template<class Solver>
void AIGToCNF<Solver>::collect_and_edges(const aig_lit& child, std::vector<aig_lit>& out) {
    if (child->type == AIGT::t_and
        && !child.neg
        && child->l != child->r
        && fanout[child.get()] <= 1
        && cache.find(child.get()) == cache.end())
    {
        stats.demorgan_and_flat++;
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
void AIGToCNF<Solver>::emit_mux3(CMSat::Lit g, CMSat::Lit s1, CMSat::Lit a,
                                 CMSat::Lit s2, CMSat::Lit b, CMSat::Lit c) {
    //  g ↔ (s1 ? a : (s2 ? b : c))
    //    s1 ∧ ~a → ~g          ⇔ ~s1 ∨ a ∨ ~g
    //    s1 ∧ a  → g           ⇔ ~s1 ∨ ~a ∨ g
    //    ~s1 ∧ s2 ∧ ~b → ~g     ⇔ s1 ∨ ~s2 ∨ b ∨ ~g
    //    ~s1 ∧ s2 ∧ b  → g      ⇔ s1 ∨ ~s2 ∨ ~b ∨ g
    //    ~s1 ∧ ~s2 ∧ ~c → ~g    ⇔ s1 ∨ s2 ∨ c ∨ ~g
    //    ~s1 ∧ ~s2 ∧ c  → g     ⇔ s1 ∨ s2 ∨ ~c ∨ g
    add_clause({~s1, a, ~g});
    add_clause({~s1, ~a, g});
    add_clause({s1, ~s2, b, ~g});
    add_clause({s1, ~s2, ~b, g});
    add_clause({s1, s2, c, ~g});
    add_clause({s1, s2, ~c, g});
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

    // MUX3 fusion: outer's else branch is itself an ITE pattern whose sub-AND
    // is fanout-1 and uncached. One helper + 6 clauses replaces two nested
    // ITEs' 2 helpers + 8 clauses.
    if (p.e_aig && p.e_aig->type == AIGT::t_and
        && p.e_aig.neg
        && p.e_aig.node != p.t_aig.node)
    {
        const AIG* e_node = p.e_aig.get();
        auto it_fo = fanout.find(e_node);
        if (cache.find(e_node) == cache.end()
            && it_fo != fanout.end() && it_fo->second <= 1)
        {
            IteParse inner;
            if (parse_ite_at(p.e_aig, inner)) {
                CMSat::Lit a_lit = encode_edge(p.t_aig);
                CMSat::Lit b_lit = encode_edge(inner.t_aig);
                CMSat::Lit c_lit = encode_edge(inner.e_aig);
                CMSat::Lit h = new_helper();
                emit_mux3(h, p.s_lit, a_lit, inner.s_lit, b_lit, c_lit);
                stats.mux3_patterns++;
                out = h;
                return true;
            }
        }
    }

    CMSat::Lit t_lit = encode_edge(p.t_aig);
    CMSat::Lit e_lit = encode_edge(p.e_aig);

    // Degenerate folds.
    if (t_lit == e_lit)   { out = t_lit; return true; }                 // ITE(s, t, t) = t
    if (p.s_lit == t_lit) { out = emit_or2(p.s_lit, e_lit);  return true; } // ITE(s, s, e) = s ∨ e
    if (p.s_lit == ~t_lit){ out = emit_and2(~p.s_lit, e_lit); return true; } // ITE(s, ~s, e) = ~s ∧ e
    if (p.s_lit == e_lit) { out = emit_and2(p.s_lit, t_lit);  return true; } // ITE(s, t, s) = s ∧ t
    if (p.s_lit == ~e_lit){ out = emit_or2(~p.s_lit, t_lit);  return true; } // ITE(s, t, ~s) = ~s ∨ t

    // Content-hashed ITE CSE: canonicalise selector polarity (flip (s,t,e) to
    // (~s, e, t) when s is negative) and look up the (s, t, e) triple.
    if (group_cse) {
        CMSat::Lit s = p.s_lit;
        CMSat::Lit t = t_lit;
        CMSat::Lit e = e_lit;
        if (s.sign()) { s = ~s; std::swap(t, e); }
        auto pack = [](CMSat::Lit l) { return (l.var() << 1) | (l.sign() ? 1u : 0u); };
        IteKey key{pack(s), pack(t), pack(e)};
        auto it = ite_cse.find(key);
        if (it != ite_cse.end()) {
            stats.cse_ite_hits++;
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

    CMSat::Lit h = new_helper();
    emit_ite(h, p.s_lit, t_lit, e_lit);
    stats.ite_patterns++;
    out = h;
    return true;
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
    // (2) Dedup by signed edge. With the edge-sign representation equality
    // is direct (same node + same sign), so a single sort+unique pass does
    // it without the O(n²) pairwise compare the old model needed.
    {
        const size_t before = conjuncts.size();
        std::sort(conjuncts.begin(), conjuncts.end(),
            [](const aig_lit& a, const aig_lit& b) {
                if (a.node.get() != b.node.get()) {
                    return std::less<const AIG*>()(a.node.get(), b.node.get());
                }
                return (int)a.neg < (int)b.neg;
            });
        conjuncts.erase(std::unique(conjuncts.begin(), conjuncts.end()),
                         conjuncts.end());
        if (conjuncts.size() < before) stats.aig_dedup_and += before - conjuncts.size();
    }
    // (3) Complementary pair: after sort by node pointer, same-node entries
    // are adjacent and differ only in sign.
    for (size_t i = 0; i + 1 < conjuncts.size(); i++) {
        if (conjuncts[i].node.get() == conjuncts[i+1].node.get()
            && conjuncts[i].neg != conjuncts[i+1].neg) {
            stats.aig_complement_and++;
            out_const = false;
            return true;
        }
    }
    // (4) OR-conjunct absorption: AND(a, OR(a, ...)) → drop the OR. An OR
    // conjunct is a negative-edge AND; its disjuncts are the complements of
    // the underlying AND's stored children. If any sibling conjunct matches
    // one of those disjuncts, the OR absorbs.
    std::vector<aig_lit> kept;
    kept.reserve(conjuncts.size());
    for (size_t i = 0; i < conjuncts.size(); i++) {
        const aig_lit& ci = conjuncts[i];
        bool absorbed = false;
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
            }
        }
        if (absorbed) { stats.absorption_and++; continue; }
        kept.push_back(ci);
    }
    conjuncts.swap(kept);
    return false;
}

// =============================================================================
// Cut-CNF encoding
// =============================================================================
//
// Collect the cone of ANDs rooted at n that can be consumed (each internal
// node fanout ≤ 1 and not yet cached), computes the truth table of n's
// SIGNED-EDGE value (with n.neg baked in) as a function of up to 4 distinct
// input variables, and emits the minimum-clause CNF for that TT. MAJ3 is the
// canonical win: 6 clauses + 1 helper vs 13 + 4 for the naive (a∧b)∨(a∧c)∨(b∧c).

template<class Solver>
bool AIGToCNF<Solver>::try_cut_cnf(const aig_lit& n, CMSat::Lit& out) {
    constexpr uint32_t MAX_LEAVES = 4;
    if (n->type != AIGT::t_and) return false;

    auto can_consume = [&](const AIG* p) -> bool {
        if (cache.find(p) != cache.end()) return false;
        auto it = fanout.find(p);
        return it != fanout.end() && it->second <= 1;
    };

    // DFS the cone on SIGNED edges. Leaves are (non-AND nodes) OR
    // (consumable-budget-exceeded ANDs). Interior ANDs we "consume" by
    // recursing into their signed children. A hard cap of MAX_LEAVES * 4
    // aborts cones that are clearly too wide.
    std::unordered_map<aig_lit, uint32_t> leaf_idx;
    std::vector<aig_lit> leaves;
    bool abort_flag = false;
    std::function<void(const aig_lit&)> dfs = [&](const aig_lit& m) {
        if (abort_flag) return;
        const bool is_interior_and = m->type == AIGT::t_and
            && (m.node == n.node || can_consume(m.get()));
        if (!is_interior_and) {
            if (leaf_idx.count(m)) return;
            if (leaves.size() >= MAX_LEAVES * 4u) { abort_flag = true; return; }
            leaf_idx[m] = leaves.size();
            leaves.push_back(m);
            return;
        }
        dfs(m->l);
        if (!abort_flag && m->r != m->l) dfs(m->r);
    };
    dfs(n);
    if (abort_flag || leaves.empty()) return false;

    // Encode each leaf edge to a CNF literal, then dedup to at most
    // MAX_LEAVES input slots by variable. Two leaves resolving to the same
    // variable (possibly with opposite signs) share one slot.
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
    const uint32_t num_mt = 1u << num_inputs;
    const uint16_t full_mask = (uint16_t)((1u << num_mt) - 1);

    // Build per-leaf minterm masks.
    std::vector<uint16_t> leaf_mask(leaves.size());
    for (size_t i = 0; i < leaves.size(); i++) {
        uint16_t sm = 0;
        for (uint32_t m = 0; m < num_mt; m++) {
            if ((m >> leaf_slot[i]) & 1u) sm |= (uint16_t)(1u << m);
        }
        leaf_mask[i] = leaf_sign[i] ? (uint16_t)(sm ^ full_mask) : sm;
    }

    // Evaluate each interior node's POSITIVE value once (cached by node
    // pointer); the final TT applies the requested edge sign at the root.
    std::unordered_map<const AIG*, uint16_t> eval_cache;
    std::function<uint16_t(const aig_lit&)> eval = [&](const aig_lit& m) -> uint16_t {
        auto it_leaf = leaf_idx.find(m);
        if (it_leaf != leaf_idx.end()) return leaf_mask[it_leaf->second];
        auto it_c = eval_cache.find(m.get());
        if (it_c != eval_cache.end()) {
            const uint16_t v_pos = it_c->second;
            return m.neg ? (uint16_t)((~v_pos) & full_mask) : v_pos;
        }
        assert(m->type == AIGT::t_and);
        const uint16_t lv = eval(m->l);
        const uint16_t rv = (m->r == m->l) ? lv : eval(m->r);
        const uint16_t v_pos = (uint16_t)(lv & rv);
        eval_cache[m.get()] = v_pos;
        return m.neg ? (uint16_t)((~v_pos) & full_mask) : v_pos;
    };
    const uint16_t tt = eval(n);

    const auto& min_cnf = cut_cnf::min_cnf_for_tt(num_inputs, tt);

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
    out = h;
    return true;
}

} // namespace ArjunNS
