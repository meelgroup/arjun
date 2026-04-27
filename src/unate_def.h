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
    uint64_t hit_iter_sum = 0;       // for averaging hit-iteration depth
    uint64_t hit_iter_max = 0;
    uint64_t hit_aig_nodes_sum = 0;  // for averaging final AIG size
    uint64_t hit_aig_nodes_max = 0;
    double time_total = 0.0;
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
        void synthesis_unate(ArjunNS::SimplifiedCNF& cnf);
    private:

        ArjunInt::Config conf;
        std::set<uint32_t> input;
        std::set<uint32_t> to_define;
        std::set<uint32_t> backward_defined;

        std::vector<uint32_t> var_to_indic; // for each var, the indicator
                                            // variable in the SAT solver that is true iff the var is equal to its copy (i.e. not flipped)
        std::unique_ptr<ArjunInt::MetaSolver> setup_f_not_f(const ArjunNS::SimplifiedCNF& cnf);

        UnateDefCondStats cond_stats;
        UnateDefRepStats rep_stats;
};
