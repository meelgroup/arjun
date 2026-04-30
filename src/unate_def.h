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
#include <cryptominisat5/solvertypesmini.h>
#include <cryptominisat5/cryptominisat.h>
#include "arjun.h"
#include "config.h"
#include "metasolver.h"

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
};
