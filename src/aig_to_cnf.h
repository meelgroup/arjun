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

    // Feature toggles. The current encoder doesn't run advanced pattern
    // detection, so these are accepted for API compatibility but ignored.
    void set_detect_ite(bool) {}
    void set_detect_xor(bool) {}
    void set_cut_cnf(bool) {}
    void set_kary_fusion(bool b) { kary_fusion = b; }
    void set_group_cse(bool) {}
    void set_ite_sub_selector(bool) {}
    void set_demorgan_flatten(bool) {}
    void set_normalize_inputs(bool b) { normalize_inputs = b; }
    void set_max_kary_width(uint32_t w) { max_kary_width = w; }

private:
    Solver& solver;
    AIG2CNFStats stats;

    CMSat::Lit my_true_lit = CMSat::Lit(0, false);
    bool my_has_true_lit = false;

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
    CMSat::Lit encode_and_node(const AIG* n);
    CMSat::Lit get_true_lit();
    CMSat::Lit new_helper();

    // Collect k-ary AND conjuncts. Each conjunct is returned as a signed edge
    // (aig_lit). We only flatten through positive-reference AND nodes whose
    // fanout is 1 — otherwise sharing would be lost.
    void collect_and_edges(const aig_lit& child, std::vector<aig_lit>& out);

    void emit_and_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);

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
    CMSat::Lit pos = encode_and_node(n.get());
    return n.neg ? ~pos : pos;
}

// Encode a t_and NODE (not an edge). Returns the CNF literal for the node's
// positive value; callers apply edge sign themselves.
template<class Solver>
CMSat::Lit AIGToCNF<Solver>::encode_and_node(const AIG* n) {
    auto it = cache.find(n);
    if (it != cache.end()) { stats.cache_hits++; return it->second; }

    // Idempotent AND(x, x): the node's value equals x's value.
    if (n->l == n->r) {
        CMSat::Lit sub = encode_edge(n->l);
        cache[n] = sub;
        return sub;
    }

    // Collect conjuncts. If kary_fusion is off, collect just the two children.
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
        if (folded_false) {
            CMSat::Lit result = ~TRUE_LIT;
            cache[n] = result;
            return result;
        }
        if (cleaned.empty()) {
            cache[n] = TRUE_LIT;
            return TRUE_LIT;
        }
        if (cleaned.size() == 1) {
            cache[n] = cleaned[0];
            return cleaned[0];
        }
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
        if (current.size() == 1) { cache[n] = current[0]; return current[0]; }
        CMSat::Lit h = new_helper();
        emit_and_equiv(h, current);
        stats.kary_and_count++;
        stats.kary_and_width_total += current.size();
        cache[n] = h;
        return h;
    }

    CMSat::Lit h = new_helper();
    emit_and_equiv(h, inputs);
    stats.kary_and_count++;
    stats.kary_and_width_total += inputs.size();
    cache[n] = h;
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

} // namespace ArjunNS
