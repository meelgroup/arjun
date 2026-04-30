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

#pragma once
#include <cstdint>
#include <map>
#include <set>
#include <vector>
#include <memory>
#include <cryptominisat5/solvertypesmini.h>
#include <cryptominisat5/cryptominisat.h>
#include "arjun.h"
#include "config.h"
#include "metasolver.h"

// Telemetry for the repair-based unate-def probe. Reset at the start of
// each `synthesis_unate_def_rep` call.
struct UnateDefRepStats {
    uint32_t tests_run = 0;          // vars we ran the rep loop for
    uint32_t hits = 0;               // vars where we found a def
    uint64_t total_iters = 0;        // total guess+refine iterations
    uint64_t miter_unsat = 0;        // miter UNSAT (def found this iter)
    uint64_t miter_sat = 0;          // miter SAT (CEX)
    uint64_t miter_undef = 0;        // miter timed out
    uint64_t f_unsat = 0;            // F-only solver UNSAT (productive CEX)
    uint64_t f_sat = 0;              // F-only solver SAT (cost-zero CEX)
    uint64_t f_undef = 0;            // F-only solver timed out
    uint64_t skipped_pattern_too_big = 0;
    // Miter UNSAT but uniqueness check failed (Skolem-only). We don't
    // commit because Manthan downstream needs F ⊨ y_test = H.
    uint64_t skolem_only_skipped = 0;
    uint64_t hit_iter_sum = 0;       // for averaging hit-iteration depth
    uint64_t hit_iter_max = 0;
    uint64_t hit_aig_nodes_sum = 0;  // for averaging final AIG size
    uint64_t hit_aig_nodes_max = 0;
    // Aux-leaf telemetry: how often the new "non-input H leaves" path actually
    // contributes. `aux_leaves_sum` counts distinct non-input leaves in the
    // committed H, summed across hits.
    uint64_t hits_using_aux = 0;
    uint64_t aux_leaves_sum = 0;
    uint64_t aux_leaves_max = 0;
    double time_total = 0.0;
    // Time breakdown (seconds). Only the three SAT calls — they dominate
    // total time and per-iter cpuTime() calls aren't free.
    double time_miter_solve = 0.0;  // SAT call on the miter
    double time_feas_solve = 0.0;   // F-solver feasibility SAT call
    double time_f_solve = 0.0;      // F-solver CEX SAT call
    // Op counts to put time numbers in context.
    uint64_t miter_solve_calls = 0;
    uint64_t feas_solve_calls = 0;
    uint64_t f_solve_calls = 0;
    uint64_t encode_h_nodes_visited = 0;
    uint64_t encode_h_nodes_emitted = 0;  // distinct AND helpers actually allocated
    uint64_t encode_h_in_f_emitted = 0;
};

// Telemetry for the conditional-unate-def probe. Reset at the start of
// each `synthesis_unate_def` call. All counts are over the inner
// (per-test) loop so we can spot expensive vs. productive patterns.
struct UnateDefCondStats {
    // Tests where conditional probing was attempted at all (i.e. neither
    // standard-unate flip was UNSAT and both witnesses were captured).
    uint32_t tests_eligible = 0;

    // Candidate L iterations that we *examined* (got past the v1==v2,
    // l_Undef, and per-var cap filters).
    uint64_t cands_examined = 0;
    // Candidates skipped because v1 == v2 (no chance to define).
    uint64_t cands_skipped_v_eq = 0;
    // Candidates skipped because v1 or v2 was l_Undef in the witness.
    uint64_t cands_skipped_undef = 0;
    // Candidates skipped because the per-test budget was exceeded.
    uint64_t cands_skipped_budget = 0;

    // Per-probe results. Each examined candidate runs probe 1, and only
    // runs probe 2 if probe 1 was UNSAT.
    uint64_t p1_unsat = 0;
    uint64_t p1_sat = 0;
    uint64_t p1_undef = 0; // conflict-budget timeout
    uint64_t p2_unsat = 0;
    uint64_t p2_sat = 0;
    uint64_t p2_undef = 0;

    // Definitions actually recorded.
    uint64_t hits = 0;
    // Sum of "how-many-cands-deep was the winner" across hits, for an
    // average winning depth metric.
    uint64_t winning_depth_sum = 0;
    uint64_t winning_depth_max = 0;
    // Of `hits`, how many had the winning L in the related-inputs prefix
    // (i.e. an input sharing at least one clause with `test`). The
    // remainder (hits - hits_in_related) came from the fall-through tail.
    // Tells us whether the structural pre-ordering actually pays off.
    uint64_t hits_in_related = 0;

    // Time spent inside the conditional block (post-flips), seconds.
    double time_in_cond = 0.0;
    // SAT calls issued from inside the conditional block.
    uint64_t cond_sat_calls = 0;
};

class Unate {
    public:
        Unate(const ArjunInt::Config& _conf) : conf(_conf) {}
        ~Unate() = default;

        void synthesis_unate_def(ArjunNS::SimplifiedCNF& cnf);
        void synthesis_unate_def_rep(ArjunNS::SimplifiedCNF& cnf);
    private:

        ArjunInt::Config conf;
        std::set<uint32_t> input;
        std::set<uint32_t> to_define;
        std::set<uint32_t> backward_defined;

        std::vector<uint32_t> var_to_indic; // for each var, the indicator
                                            // variable in the SAT solver that is true iff the var is equal to its copy (i.e. not flipped)
        std::unique_ptr<ArjunInt::MetaSolver> setup_f_not_f(const ArjunNS::SimplifiedCNF& cnf);

        // ===== Conditional unate-def probe state =====
        // Set up once at the start of synthesis_unate_def, then read/updated
        // per-test inside try_cond_unate_def.
        std::vector<uint32_t> cond_input_vars_list;
        std::vector<uint32_t> cond_input_pos;            // var -> index in cond_input_vars_list, or NOT_INPUT
        std::vector<std::vector<uint32_t>> cond_related_inputs; // per to-define var, inputs sharing a clause
        std::vector<uint32_t> cond_cand_seen_gen;        // generation-counter dedup for cur_cands
        uint32_t cond_cand_gen = 0;
        std::vector<uint32_t> cond_cur_cands;            // reusable per-test candidate buffer
        bool cond_enabled = false;
        uint32_t cond_attempts_since_last_hit = 0;
        uint32_t cond_new_defs = 0;
        double cond_my_time = 0.0;                       // wall-clock baseline for verb_print

        // Try to express `test` as a single input literal under a value-conditioned
        // probe, using the two SAT witnesses from the standard-unate flips
        // (projected to input vars in input_vals[0/1]). Returns true if a
        // definition was found and committed to `cnf`.
        bool try_cond_unate_def(
            ArjunNS::SimplifiedCNF& cnf,
            ArjunInt::MetaSolver& s,
            uint32_t test,
            const std::vector<CMSat::lbool> (&input_vals)[2],
            std::vector<CMSat::Lit>& assumps,
            const std::map<uint32_t, CMSat::Lit>& new_to_orig);

        UnateDefCondStats cond_stats;
        UnateDefRepStats rep_stats;

        // ===== synthesis_unate_def_rep helpers =====
        // Per-pass mutable state. Holds the two SAT solvers, lazy true-lits
        // for each, and the per-pass scratch buffers. Lives on the stack of
        // synthesis_unate_def_rep and is threaded into every helper. Kept
        // here (rather than as Unate fields) so it cannot persist across
        // calls or pollute synthesis_unate_def's view of the class.
        struct RepPass {
            std::unique_ptr<ArjunInt::MetaSolver> s;          // miter
            std::unique_ptr<ArjunInt::MetaSolver> f_solver;   // F-only

            CMSat::Lit s_true_lit         = CMSat::lit_Undef;
            CMSat::Lit f_true_lit         = CMSat::lit_Undef;
            CMSat::Lit cnf_true_lit_new   = CMSat::lit_Undef;
            CMSat::Lit cnf_true_lit_orig  = CMSat::lit_Undef;

            std::map<uint32_t, CMSat::Lit> new_to_orig;

            std::vector<uint32_t> aux_vars;
            std::vector<char>     aux_mask;
            std::map<uint32_t, std::vector<uint32_t>> deps_cache;

            std::vector<std::pair<uint32_t, ArjunNS::aig_ptr>> deferred_materialize;
            std::set<uint32_t> already_tested;
            uint32_t tested_num = 0;
            uint32_t new_defs   = 0;
            double   t0         = 0.0;
        };

        // Lazy true-literal allocators for each solver / cnf side.
        CMSat::Lit rep_get_s_true(RepPass& p);
        CMSat::Lit rep_get_f_true(RepPass& p);
        std::pair<CMSat::Lit, CMSat::Lit> rep_get_cnf_true(
            ArjunNS::SimplifiedCNF& cnf, RepPass& p);

        // Tseitin encoders / structural helpers.
        CMSat::Lit rep_encode_h_in_miter(
            RepPass& p, const ArjunNS::SimplifiedCNF& cnf,
            const ArjunNS::aig_ptr& h, bool is_y_prime);
        CMSat::Lit rep_encode_h_in_f(RepPass& p, const ArjunNS::aig_ptr& h);
        CMSat::Lit rep_materialize_h_in_cnf(
            ArjunNS::SimplifiedCNF& cnf, RepPass& p, const ArjunNS::aig_ptr& h);
        size_t rep_h_aux_leaf_count(const ArjunNS::aig_ptr& h) const;

        // Pass-section helpers, in the order synthesis_unate_def_rep uses
        // them. Each helper's body is a verbatim move of the corresponding
        // block in the original function (with `s` → `p.s` etc.).
        void rep_setup_yprime_backward_defs(
            ArjunNS::SimplifiedCNF& cnf, RepPass& p);
        void rep_build_indicators(ArjunNS::SimplifiedCNF& cnf, RepPass& p);
        void rep_build_f_solver(
            const ArjunNS::SimplifiedCNF& cnf, RepPass& p);
        void rep_build_base_assumps(
            const ArjunNS::SimplifiedCNF& cnf, const RepPass& p,
            uint32_t test, std::vector<CMSat::Lit>& base_assumps);
        void rep_build_aux_set(
            const ArjunNS::SimplifiedCNF& cnf, RepPass& p,
            uint32_t test, CMSat::Lit test_orig);
        void rep_process_test_var(
            ArjunNS::SimplifiedCNF& cnf, RepPass& p, uint32_t test);
        void rep_materialize_deferred(
            ArjunNS::SimplifiedCNF& cnf, RepPass& p);
        void rep_log_pass_summary(ArjunNS::SimplifiedCNF& cnf) const;
};
