/*
 Arjun

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in
 all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 THE SOFTWARE.
 */

// Craig-interpolant repair for Manthan.
//
// find_conflict's UNSAT core is a single corner of input space. The
// interpolant in input vars only generalises to the whole region where
// flipping y_rep is required, so compose_or/and on the interpolant AIG
// captures many would-be repairs at once.

#pragma once

#include "arjun.h"
#include "config.h"
#include "constants.h"
#include <cryptominisat5/solvertypesmini.h>
#include <cadical.hpp>
#include <tracer.hpp>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cstdint>
#include <memory>

namespace ArjunInt {

// McMillan-style interpolant tracer for the partition
//   A = original CNF + non-input assumption units (~to_repair, y-other lits)
//   B = input assumption units
//
// The tracer is told which original-clause IDs are B (input units). Every
// other original clause is treated as A. Derived clauses get a label
// computed from the antecedents via McMillan's rule:
//   - resolution on a shared (= input) literal     → AND of children
//   - resolution on an A-local (= non-input) lit   → OR  of children
struct InterpTracerMcMillan : public CaDiCaL::Tracer {
    InterpTracerMcMillan(const Config& _conf,
        const ArjunNS::AIGManager& _aig_mng,
        const std::set<uint32_t>& _input_vars)
        : conf(_conf), aig_mng(_aig_mng), input_vars(_input_vars) {}

    const Config& conf;
    const ArjunNS::AIGManager& aig_mng;
    const std::set<uint32_t>& input_vars;

    // O(1) shared-var lookup. "Shared" = a B-visible var, i.e. an input
    // var: interp_repair's B side holds input assumption units only.
    [[nodiscard]] bool is_shared(uint32_t v) const {
        return input_vars.count(v) != 0;
    }

    // Set by the caller before each solver->add(0): is the next clause
    // B-side (label TRUE) or A-side (label = OR of input lits)?
    bool next_is_b = false;

    // McMillan's labelled-interpolation rule: a shared (input) pivot is
    // 'b' → AND of children (the strongest interpolant); an A-local pivot
    // is 'a' → OR.

    // Variables with index >= b_local_from are B-local: they occur only
    // in B clauses, so a resolution pivot on them is AND'd just like a
    // shared (input) pivot. interp_repair's B is input units only, so it
    // leaves this at UINT32_MAX (no B-local vars); the doubled-CNF
    // interpolation in interpolant.cpp sets it to orig_num_vars so the
    // copy-2 and indicator variables (the bulk of its B side) are handled
    // correctly. A-local pivots (below the threshold, non-input) → OR.
    uint32_t b_local_from = UINT32_MAX;

    // Original clauses decided to be B-side (label = TRUE). Clause-id keyed,
    // only point-accessed (never iterated) so unordered is determinism-safe
    // and gives resolve_chain O(1) lookup.
    std::unordered_set<uint64_t> b_clause_ids;

    // ID -> clause literals (kept to find resolution pivots).
    std::unordered_map<uint64_t, std::vector<CMSat::Lit>> cls;
    // ID -> partial McMillan label (an AIG over input vars), filled for
    // the proof core during build_interpolant().
    std::unordered_map<uint64_t, ArjunNS::aig_lit> labels;
    // ID -> antecedent chain for derived clauses. Recorded as the proof
    // streams in, but only resolved (into a label) for the proof core.
    std::unordered_map<uint64_t, std::vector<uint64_t>> antec;

    // Cache: input lit -> AIG leaf node, so structural hashing dedups.
    std::map<CMSat::Lit, ArjunNS::aig_lit> lit_to_aig;

    // Structural-hash table over the t_and nodes built while resolving
    // partial interpolants. Keyed on the canonicalised (smaller-nid
    // first) child edges so equal cones across different proof clauses
    // collapse to one shared sub-DAG instead of a fresh tree each time.
    std::map<ArjunNS::AIG::AIGKey, ArjunNS::aig_lit> and_table;
    ArjunNS::aig_lit hash_and(const ArjunNS::aig_lit& l,
                              const ArjunNS::aig_lit& r);
    ArjunNS::aig_lit hash_or(const ArjunNS::aig_lit& l,
                             const ArjunNS::aig_lit& r);

    // ID of the derived empty clause; set when first seen.
    uint64_t empty_id = UINT64_MAX;

    // Incremental (assumption-based) solving. cadical reports the
    // refutation through conclude_unsat() after conclude() is called.
    // conclusion_type stays 0 on the non-incremental interp_repair path
    // (which never calls conclude()), so build_interpolant() falls back
    // to empty_id there. conclusion_root is the id of the derived empty
    // clause (CONFLICT) or of the failing-assumption clause (ASSUMPTIONS).
    int conclusion_type = 0;
    uint64_t conclusion_root = UINT64_MAX;

    // Set by build_interpolant(): the McMillan interpolant AIG, or null.
    ArjunNS::aig_lit out = nullptr;

    // For diagnostics.
    uint64_t derived_count = 0;
    uint64_t orig_count = 0;
    // Derived clauses actually on the proof core (reachable from the
    // empty clause), set by build_interpolant().
    uint64_t core_count = 0;

    void mark_b_clause(uint64_t id) { b_clause_ids.insert(id); }

    ArjunNS::aig_lit lit_aig(CMSat::Lit l);
    // OR of the shared (B-visible) lits in `cl` — the partial label for an
    // A-side clause. "Shared" is decided by is_shared() = the input_vars set.
    ArjunNS::aig_lit or_of_shared_lits(const std::vector<CMSat::Lit>& cl);

    void add_original_clause(uint64_t id, bool red,
            const std::vector<int>& clause, bool restored = false) override;
    void add_derived_clause(uint64_t id, bool red,
            const std::vector<int>& clause,
            const std::vector<uint64_t>& antecedents) override;

    // Incremental-solving events. Needed when the tracer is reused
    // across several assumption-based solves on one persistent solver
    // (the doubled-CNF interpolation in interpolant.cpp).
    // add_assumption_clause() records the failing-assumption clause;
    // conclude_unsat() reports the refutation root. The non-incremental
    // interp_repair path never triggers these.
    void add_assumption_clause(uint64_t id,
            const std::vector<int>& clause,
            const std::vector<uint64_t>& antecedents) override;
    void conclude_unsat(CaDiCaL::ConclusionType type,
            const std::vector<uint64_t>& ids) override;

    // Drop the per-solve scratch (labels, and-table, refutation root)
    // before the next incremental solve. cls / antec / b_clause_ids are
    // kept — the clause database outlives a single solve. The caller
    // must invoke this between solves; it is deliberately not driven by
    // the solve_query() callback, since cadical can derive the empty
    // clause already while clauses are being added, before solve().
    void reset_per_solve();

    // Trace back from the refutation root (empty clause, or the
    // failing-assumption clause) over the recorded antecedent chains,
    // build McMillan labels only for the reachable proof-core clauses,
    // and return the interpolant AIG (sets `out`). Returns null if no
    // refutation was recorded.
    ArjunNS::aig_lit build_interpolant();

private:
    // McMillan label of an original clause, computed lazily from
    // the current input_vars — deferred out of add_original_clause so a
    // persistent tracer picks up input vars added since the clause was.
    [[nodiscard]] ArjunNS::aig_lit original_label(uint64_t id);
    // Resolve one derived clause's antecedent chain into a McMillan
    // label. Tries the chain reversed, then forward.
    void build_derived_label(uint64_t id);
    // Replay `chain` as a linear resolution and set labels[id]. Returns
    // false (with labels[id] left at a partial value) if the chain is
    // not a clean linear resolution in this order.
    [[nodiscard]] bool resolve_chain(uint64_t id,
            const std::vector<uint64_t>& chain);
};

// Pick the subset of `clauses` relevant to an UNSAT proof seeded by the
// unit literals `units`. Pure unit propagation + a connectivity sweep, no
// SAT solve. Two sound reductions: (1) clauses the propagated assignment
// satisfies contribute nothing once their reason clauses are kept;
// (2) clauses in a variable component disjoint from the seed units are
// satisfiable spec sub-formulas and dropped. If UP alone refutes the
// formula, only the conflicting clause and its transitive reason chain
// are kept.
//
// `occ[lit.toInt()]` must list the indices into `clauses` of the clauses
// containing that literal. `n_vars` must cover every variable appearing
// in `clauses` and in `units`. `occ` may be shorter than 2*n_vars;
// out-of-range lookups are simply skipped.
[[nodiscard]] std::vector<uint32_t> collect_relevant_clauses(
        const std::vector<std::vector<CMSat::Lit>>& clauses,
        const std::vector<CMSat::Lit>& units,
        uint32_t n_vars,
        const std::vector<std::vector<uint32_t>>& occ);

class InterpRepair {
public:
    InterpRepair(const Config& _conf,
        const ArjunNS::SimplifiedCNF& _cnf,
        const std::set<uint32_t>& _input_vars,
        ArjunNS::AIGManager& _aig_mng);
    ~InterpRepair() = default;

    // Compute an interpolant I(input_vars): FALSE on the CEX, TRUE where
    // flipping y_rep stays feasible. The shared set is the input vars, so
    // I(input_vars) only captures the input projection of the must-flip
    // region — the caller must AND in the y_other-matches-context
    // conjuncts.
    //
    // Returns nullptr when there is nothing to interpolate (empty
    // conflict, or no shared lits in the conflict), the AIG exceeds
    // the node cap, or the conflict budget is exhausted.
    [[nodiscard]] ArjunNS::aig_lit compute_interpolant(
        uint32_t y_rep, CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        uint32_t max_aig_nodes = 0,
        uint64_t conflict_budget = 0);

    // SLOW_DEBUG / test-only sanity helper: interpolant evaluates to
    // FALSE on the CEX inputs. Not called on the default runtime path.
    [[nodiscard]] bool quick_check_interpolant_excludes_cex(
        const ArjunNS::aig_lit& interp,
        const std::vector<CMSat::Lit>& conflict) const;

    // SLOW_DEBUG / test-only sanity helper: full A → I miter, used to
    // guard the math during development and in unit tests. Returns true
    // on UNSAT and on a budget-exhausted (inconclusive) solve. A holds the
    // original CNF, the y_other conflict units, and ~to_repair.
    [[nodiscard]] bool slow_check_a_implies_i(
        CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        const ArjunNS::aig_lit& interp,
        uint64_t conflict_budget = 0) const;

    // SLOW_DEBUG / test-only sanity helper: for K random input patterns
    // where I(X)=FALSE, SAT-check that flipping y_rep is genuinely
    // impossible. Always returns true on the happy path.
    [[nodiscard]] bool sample_check_interpolant(
        CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        const ArjunNS::aig_lit& interp,
        uint32_t num_samples = 8,
        uint64_t seed = 42) const;

    // Statistics (read-only)
    uint64_t calls = 0;
    uint64_t calls_succeeded = 0;
    uint64_t calls_failed_oversize = 0;
    uint64_t calls_failed_other = 0;
    uint64_t calls_failed_empty_or_no_input = 0;
    // Cadical hit the conflict budget and returned l_Undef, not a proof.
    uint64_t calls_budget_exhausted = 0;
    uint64_t total_interp_nodes = 0;
    uint64_t total_conflict_lits = 0;
    // How often the interpolant AIG had fewer/more nodes than the
    // conflict clause had literals. Apples-to-oranges (gates vs lits),
    // but a useful coarse signal for whether interpolation is
    // compressing the explanation. See total_interp_support for the
    // average input-variable count of the interpolant AIG.
    uint64_t interp_smaller_than_conflict = 0;
    uint64_t interp_larger_than_conflict = 0;
    // Largest interpolant we accepted, in nodes.
    uint64_t max_interp_nodes_seen = 0;
    // Distinct input vars referenced in the interpolant AIG, summed
    // over successful calls.
    uint64_t total_interp_support = 0;
    uint64_t total_input_lits_in_conflict = 0;
    // Histogram of interpolant sizes (nodes) for tuning visibility.
    // Buckets: [0,8) [8,32) [32,128) [128,512) [512,2K) [2K,8K) [8K,32K) [32K,∞).
    static constexpr size_t HIST_BUCKETS = 8;
    uint64_t interp_size_hist[HIST_BUCKETS] = {};
    // Histogram of conflict sizes at compute_interpolant entry.
    uint64_t conflict_size_hist[HIST_BUCKETS] = {};
    static size_t bucket_of(size_t n) {
        if (n < 8) return 0;
        if (n < 32) return 1;
        if (n < 128) return 2;
        if (n < 512) return 3;
        if (n < 2048) return 4;
        if (n < 8192) return 5;
        if (n < 32768) return 6;
        return 7;
    }
    static const char* bucket_label(size_t i) {
        static const char* lbl[HIST_BUCKETS] = {
            "[0,8)", "[8,32)", "[32,128)", "[128,512)",
            "[512,2K)", "[2K,8K)", "[8K,32K)", "[32K,∞)"
        };
        return lbl[i];
    }
    // rewrite_aig effectiveness, node counts summed pre vs post the
    // heavier structural rewrite pass. The b1_* fields track the guard AIG
    // (--interprepairb1rewrite); they stay zero unless the flag is enabled.
    // The "b1_" field names keep the historical spelling.
    uint64_t total_b1_pre_rewrite = 0;
    uint64_t total_b1_post_rewrite = 0;
    uint64_t b1_rewrite_calls = 0;
    // Proof-core trimming: total derived clauses cadical streamed vs the
    // subset actually reachable from the empty clause, summed over all
    // tracing solves.
    uint64_t total_proof_derived = 0;
    uint64_t total_proof_core = 0;
    // Mini-CNF clause pruning: original clauses vs the relevant subset
    // actually fed to the tracing solver, summed over all interp solves.
    // Mutable: updated from the const setup_mini_cnf.
    mutable uint64_t total_minicnf_clauses = 0;
    mutable uint64_t total_minicnf_clauses_kept = 0;

    // Wire up the mini-CNF on `solver` with `tracer` attached.
    //   A: original CNF + non-input conflict units + ~to_repair_lit
    //   B: input conflict units
    // Returns the B-side unit count; 0 means a trivial interpolant.
    uint32_t setup_mini_cnf(CaDiCaL::Solver& solver,
            InterpTracerMcMillan& tracer,
            CMSat::Lit to_repair_lit,
            const std::vector<CMSat::Lit>& conflict) const;


private:
    const Config& conf;
    const ArjunNS::SimplifiedCNF& cnf;
    const std::set<uint32_t>& input_vars;
    ArjunNS::AIGManager& aig_mng;

    // Byte-map for O(1) input-membership check.
    std::vector<uint8_t> is_input;

    // Original CNF clauses pre-converted to cadical signed-ints (0
    // terminated), built lazily on the first interp call. Used by the
    // SLOW_DEBUG sanity helpers, which need the full A-side CNF.
    mutable std::vector<int> cnf_serialized;
    mutable bool cnf_serialized_built = false;
    void build_serialized_cnf() const;

    // Per-literal occurrence lists over the original CNF clauses, indexed
    // by CMSat::Lit::toInt(). occ[litidx] holds the indices (into
    // cnf.get_clauses()) of the clauses containing that literal. Built
    // lazily on the first interp call and reused afterwards.
    mutable std::vector<std::vector<uint32_t>> occ;
    mutable bool occ_built = false;
    void build_occ() const;

    // Pick the subset of original-CNF clause indices relevant to the
    // interpolant for this conflict. Unit propagation from the assumption
    // units drops clauses the units already satisfy; a connectivity sweep
    // drops clauses in variable components disjoint from the conflict.
    // Both reductions preserve the mini-CNF's UNSAT and the interpolant's
    // soundness — see interp_repair.cpp for the argument.
    [[nodiscard]] std::vector<uint32_t> collect_relevant_clauses(
            CMSat::Lit to_repair_lit,
            const std::vector<CMSat::Lit>& conflict) const;

    // Run one tracing solve and return its raw McMillan interpolant.
    // out_ret receives the cadical status (20=UNSAT, 0=budget, 10=SAT).
    [[nodiscard]] ArjunNS::aig_lit solve_one_interpolant(
        CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        uint64_t conflict_budget, int& out_ret);
};

} // namespace ArjunInt
