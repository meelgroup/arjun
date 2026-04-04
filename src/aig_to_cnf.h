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
   - XOR pattern detection: (a AND NOT b) OR (NOT a AND b) is encoded
     directly with 4 clauses.
   - Structural sharing: each AIG node is encoded at most once (by pointer).

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#pragma once

#include "arjun.h"
#include <cryptominisat5/solvertypesmini.h>
#include <cstdint>
#include <map>
#include <vector>

namespace ArjunNS {

struct AIG2CNFStats {
    uint64_t nodes_visited = 0;
    uint64_t helpers_added = 0;
    uint64_t clauses_added = 0;
    uint64_t cache_hits = 0;

    // Gate-level statistics
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

// Solver-generic AIG to CNF encoder. The Solver type must provide:
//   void new_var();
//   uint32_t nVars() const;
//   void add_clause(const std::vector<CMSat::Lit>& cl);
// (both CMSat::SATSolver and ArjunInt::MetaSolver2 satisfy this.)
template<class Solver>
class AIGToCNF {
public:
    explicit AIGToCNF(Solver& s) : solver(s) {}

    // Encode an AIG rooted at 'root' into the solver.
    // Returns a literal whose value is equal to the AIG's value.
    // If 'force_helper' is true, the returned literal is always a freshly
    // allocated helper variable (even if the root is a plain literal). Useful
    // when the caller needs a stable handle to bind against.
    CMSat::Lit encode(const aig_ptr& root, bool force_helper = false);

    // Encode a batch of AIGs that may share subgraphs. Returns one lit per
    // input. Null inputs yield Lit(0,false) placeholders (skipped). Structural
    // sharing across AIGs is exploited via the pointer cache.
    std::vector<CMSat::Lit> encode_batch(const std::vector<aig_ptr>& roots);

    // Provide a pre-existing "true" literal that the solver already guarantees
    // to be true (e.g., via a unit clause). If not set, the encoder allocates
    // one on first use (needed only when the AIG contains t_const nodes).
    void set_true_lit(CMSat::Lit t) { my_true_lit = t; my_has_true_lit = true; }

    const AIG2CNFStats& get_stats() const { return stats; }

    // Enable/disable individual optimizations (mostly for testing/fuzzing).
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

    // Pattern detection. If a pattern matches, emits clauses and sets 'out'.
    bool try_ite(const aig_ptr& n, CMSat::Lit& out);
    bool try_xor(const aig_ptr& n, CMSat::Lit& out);

    // Flattening. Collect AND conjuncts of 'n->value'. Recurses through
    // fanout-1 nodes whose effective operation matches AND.
    void collect_and(const aig_ptr& n, std::vector<CMSat::Lit>& out);
    // Collect OR disjuncts of '¬n->value'. This is used when starting from a
    // NAND node: the NAND equals ¬l ∨ ¬r, which is the disjuncts of ¬l and ¬r.
    void collect_disjuncts_of_neg(const aig_ptr& n, std::vector<CMSat::Lit>& out);

    // Emit equivalence g <-> (l1 ∧ l2 ∧ ... ∧ lk)  (k >= 1).
    void emit_and_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);
    // Emit equivalence g <-> (l1 ∨ l2 ∨ ... ∨ lk)  (k >= 1).
    void emit_or_equiv(CMSat::Lit g, const std::vector<CMSat::Lit>& inputs);

    // ITE: g <-> (s ? t : e). 4 clauses.
    void emit_ite(CMSat::Lit g, CMSat::Lit s, CMSat::Lit t, CMSat::Lit e);
    // XOR: g <-> (a XOR b). 4 clauses.
    void emit_xor(CMSat::Lit g, CMSat::Lit a, CMSat::Lit b);

    void add_clause(const std::vector<CMSat::Lit>& cl);
};

} // namespace ArjunNS
