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

    // Set by the caller before each solver->add(0): is the next clause
    // B-side (label TRUE) or A-side (label = OR of input lits)?
    bool next_is_b = false;

    // Labeled-interpolation system for resolution on a shared (input)
    // pivot. SYS_MCMILLAN: shared='b' → AND of children (strongest
    // interpolant). SYS_PUDLAK: shared='ab' → the selector
    // (v∨I1)∧(¬v∨I2) (a smaller, symmetric interpolant). A-local
    // pivots are 'a' → OR in both systems.
    static constexpr int SYS_MCMILLAN = 0;
    static constexpr int SYS_PUDLAK = 1;
    int system = SYS_MCMILLAN;

    // Original clauses decided to be B-side (label = TRUE).
    std::set<uint64_t> b_clause_ids;

    // ID -> clause literals (kept to find resolution pivots).
    std::map<uint64_t, std::vector<CMSat::Lit>> cls;
    // ID -> partial McMillan label (an AIG over input vars). Original
    // clauses are labelled eagerly; derived-clause labels are only filled
    // for the proof core during build_interpolant().
    std::map<uint64_t, ArjunNS::aig_ptr> labels;
    // ID -> antecedent chain for derived clauses. Recorded as the proof
    // streams in, but only resolved (into a label) for the proof core.
    std::map<uint64_t, std::vector<uint64_t>> antec;

    // Cache: input lit -> AIG leaf node, so structural hashing dedups.
    std::map<CMSat::Lit, ArjunNS::aig_ptr> lit_to_aig;

    // Structural-hash table over the t_and nodes built while resolving
    // partial interpolants. Keyed on the canonicalised (smaller-nid
    // first) child edges so equal cones across different proof clauses
    // collapse to one shared sub-DAG instead of a fresh tree each time.
    std::map<ArjunNS::AIG::AIGKey, ArjunNS::aig_ptr> and_table;
    ArjunNS::aig_ptr hash_and(const ArjunNS::aig_ptr& l,
                              const ArjunNS::aig_ptr& r);
    ArjunNS::aig_ptr hash_or(const ArjunNS::aig_ptr& l,
                             const ArjunNS::aig_ptr& r);

    // ID of the derived empty clause; set when first seen.
    uint64_t empty_id = UINT64_MAX;

    // Set true if a proof-core clause's antecedent chain could not be
    // reconstructed as a clean linear resolution (missing antecedent,
    // multi-pivot, or no-pivot step). The partial McMillan label built
    // in that case is NOT a valid interpolant for the clause, so the
    // whole interpolant must be abandoned — build_interpolant() returns
    // null. Previously such a bail silently produced a wrong (possibly
    // unsound) interpolant.
    bool build_failed = false;

    // Set by build_interpolant(): the McMillan interpolant AIG, or null.
    ArjunNS::aig_ptr out = nullptr;

    // For diagnostics.
    uint64_t derived_count = 0;
    uint64_t orig_count = 0;
    // Derived clauses actually on the proof core (reachable from the
    // empty clause), set by build_interpolant().
    uint64_t core_count = 0;

    void mark_b_clause(uint64_t id) { b_clause_ids.insert(id); }

    ArjunNS::aig_ptr lit_aig(CMSat::Lit l);
    ArjunNS::aig_ptr or_of_input_lits(const std::vector<CMSat::Lit>& cl);

    void add_original_clause(uint64_t id, bool red,
            const std::vector<int>& clause, bool restored = false) override;
    void add_derived_clause(uint64_t id, bool red,
            const std::vector<int>& clause,
            const std::vector<uint64_t>& antecedents) override;

    // Trace back from the empty clause over the recorded antecedent
    // chains, build McMillan labels only for the reachable proof-core
    // clauses, and return the interpolant AIG (sets `out`). Returns null
    // if no empty clause was derived.
    ArjunNS::aig_ptr build_interpolant();

private:
    // Resolve one derived clause's antecedent chain into a McMillan
    // label. Assumes every antecedent already has a label.
    void build_derived_label(uint64_t id);
};

// Memoisation key for InterpRepair: (to_repair lit, max-nodes cap,
// conflict budget, nproofs, system, packed bool flags, sorted conflict
// literals). The conflict is sorted so call-order does not matter — the
// same partition always hits the same entry.
using InterpCacheKey = std::tuple<int, uint32_t, uint64_t, uint32_t,
        int, uint8_t, std::vector<int>>;

class InterpRepair {
public:
    InterpRepair(const Config& _conf,
        const ArjunNS::SimplifiedCNF& _cnf,
        const std::set<uint32_t>& _input_vars,
        ArjunNS::AIGManager& _aig_mng);
    ~InterpRepair() = default;

    // Compute an interpolant I(input_vars): FALSE on the CEX inputs,
    // TRUE where flipping y_rep stays feasible. Returns nullptr on
    // failure (SAT, oversized AIG, internal error). When `unconditional`
    // is set the y_other lits are not pinned, so I covers the must-flip
    // region universally over y_others.
    // Cache-checked entry point. The interpolant is a deterministic
    // function of (CNF, conflict set, to_repair, options), so a repeated
    // request returns the memoised result without re-solving.
    ArjunNS::aig_ptr compute_interpolant(
        uint32_t y_rep, CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        uint32_t max_aig_nodes = 0,
        bool full_rewrite = false,
        uint64_t conflict_budget = 0,
        bool unconditional = false,
        uint32_t nproofs = 1,
        int system = 0,
        bool verify = true);

    // Cheap check: interpolant evaluates to FALSE on the CEX inputs.
    [[nodiscard]] bool quick_check_interpolant_excludes_cex(
        const ArjunNS::aig_ptr& interp,
        const std::vector<CMSat::Lit>& conflict) const;

    // Heavy check: full miter that A -> I. Returns true if A & ~I is
    // UNSAT. `unconditional` selects the partition: when true the
    // non-input (y_other) conflict units are NOT pinned, matching the
    // unconditional interpolant; when false they are pinned.
    [[nodiscard]] bool slow_check_a_implies_i(
        CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        const ArjunNS::aig_ptr& interp,
        bool unconditional) const;

    // Probabilistic check: for K random input patterns where I(X)=FALSE,
    // SAT-check that flipping y_rep is genuinely impossible. Returns true
    // on pass/inconclusive, false on a confirmed counterexample.
    [[nodiscard]] bool sample_check_interpolant(
        CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        const ArjunNS::aig_ptr& interp,
        bool unconditional,
        uint32_t num_samples = 8,
        uint64_t seed = 42) const;

    // Statistics (read-only)
    uint64_t calls = 0;
    uint64_t calls_succeeded = 0;
    uint64_t calls_failed_oversize = 0;
    // Oversize McMillan interpolants that triggered a Pudlák retry.
    uint64_t calls_oversize_pudlak_retry = 0;
    uint64_t calls_failed_other = 0;
    uint64_t calls_failed_empty_or_no_input = 0;
    uint64_t calls_quick_check_failed = 0;
    // Interpolants rejected by the always-on A→I miter verification.
    uint64_t calls_verify_failed = 0;
    // Cadical hit the conflict budget and returned l_Undef, not a proof.
    uint64_t calls_budget_exhausted = 0;
    uint64_t total_interp_nodes = 0;
    uint64_t total_conflict_lits = 0;
    // How often the interpolant was smaller/larger than the conflict
    // (node-vs-lit count).
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
    // heavier structural rewrite pass. The interp_* pair tracks the raw
    // McMillan interpolant (--interprepairrewrite); the b1_* pair tracks
    // the combined branch b1 (--interprepairb1rewrite). Both stay zero
    // unless their flag is enabled.
    uint64_t total_interp_pre_rewrite = 0;
    uint64_t total_interp_post_rewrite = 0;
    uint64_t interp_rewrite_calls = 0;
    uint64_t total_b1_pre_rewrite = 0;
    uint64_t total_b1_post_rewrite = 0;
    uint64_t b1_rewrite_calls = 0;
    // Multi-proof intersection: calls where >1 proof was combined, and
    // the total number of proofs intersected over those calls.
    uint64_t interp_multiproof_calls = 0;
    uint64_t interp_multiproof_combined = 0;
    // Memoisation: total cache lookups and hits.
    uint64_t cache_lookups = 0;
    uint64_t cache_hits = 0;

    // Wire up the mini-CNF on `solver` with `tracer` attached.
    //   A: original CNF + non-input conflict units + ~to_repair_lit
    //   B: input conflict units
    // Returns the B-side unit count; 0 means a trivial interpolant.
    uint32_t setup_mini_cnf(CaDiCaL::Solver& solver,
            InterpTracerMcMillan& tracer,
            CMSat::Lit to_repair_lit,
            const std::vector<CMSat::Lit>& conflict,
            bool unconditional) const;

    void print_stats(const std::string& prefix = "[interp-repair]") const;

private:
    const Config& conf;
    const ArjunNS::SimplifiedCNF& cnf;
    const std::set<uint32_t>& input_vars;
    ArjunNS::AIGManager& aig_mng;

    // Byte-map for O(1) input-membership check.
    std::vector<uint8_t> is_input;

    // Original CNF clauses pre-converted to cadical signed-ints (0
    // terminated), built lazily on the first interp call.
    mutable std::vector<int> cnf_serialized;
    mutable bool cnf_serialized_built = false;
    void build_serialized_cnf() const;

    // The actual interpolant computation, behind the compute_interpolant
    // memoisation wrapper.
    [[nodiscard]] ArjunNS::aig_ptr compute_interpolant_impl(
        uint32_t y_rep, CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        uint32_t max_aig_nodes, bool full_rewrite,
        uint64_t conflict_budget, bool unconditional,
        uint32_t nproofs, int system, bool verify);

    // Memoised interpolants, keyed by InterpCacheKey.
    std::map<InterpCacheKey, ArjunNS::aig_ptr> interp_cache;

    // Run one tracing solve and return its raw McMillan interpolant.
    // `seed` 0 keeps cadical's default search; non-zero shuffles the
    // search so an independent proof (hence interpolant) is produced.
    // out_ret receives the cadical status (20=UNSAT, 0=budget, 10=SAT).
    [[nodiscard]] ArjunNS::aig_ptr solve_one_interpolant(
        CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        bool unconditional, uint64_t conflict_budget,
        uint32_t seed, int system, int& out_ret) const;
};

} // namespace ArjunInt
