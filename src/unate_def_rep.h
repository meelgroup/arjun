/*
 Arjun

 Copyright (c) 2026, Mate Soos and Kuldeep S. Meel. All rights reserved.

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
#include <memory>
#include <set>
#include <utility>
#include <vector>
#include <cryptominisat5/solvertypesmini.h>
#include "arjun.h"
#include "config.h"
#include "metasolver.h"

namespace ArjunInt {

// Telemetry for the repair-based unate-def probe. Reset at the start of
// each `UnateDefRep::run()` call.
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
    // Conflict minimization (greedy literal drop on the F-only solver).
    uint64_t minim_attempts = 0;       // CEXes where minim was invoked
    uint64_t minim_succeeded = 0;      // CEXes where minim removed >=1 lit
    uint64_t minim_solver_calls = 0;   // total extra F-solver calls
    uint64_t minim_lits_in = 0;        // total lits going into minim
    uint64_t minim_lits_out = 0;       // total lits remaining after minim
    double   time_minim = 0.0;         // SAT time spent inside minim
    // Input-only F-solver attempts (Manthan's "input-only conflict first").
    uint64_t inpfirst_attempts = 0;
    uint64_t inpfirst_unsat = 0;       // succeeded → input-only pattern
    uint64_t inpfirst_sat = 0;         // had to fall back to input+aux
    uint64_t inpfirst_undef = 0;       // budget hit
    // Single-shot "drop all aux from pattern" attempts after minim.
    uint64_t dropaux_attempts = 0;
    uint64_t dropaux_succeeded = 0;
    uint64_t dropaux_lits_dropped = 0;
};

// Repair-based extension of the conditional unate-def search. See the long
// comment at the top of unate_def_rep.cpp for the algorithm. Runs once per
// SimplifiedCNF; not reusable.
class UnateDefRep {
public:
    UnateDefRep(const ArjunInt::Config& _conf, ArjunNS::SimplifiedCNF& _cnf)
        : conf(_conf), cnf(_cnf) {}

    void run();
    const UnateDefRepStats& stats() const { return rep_stats; }

private:

    inline CMSat::lbool model_value(const std::vector<CMSat::lbool>& m, const CMSat::Lit l) {
        if (l.var() >= m.size()) return CMSat::l_Undef;
        CMSat::lbool v = m[l.var()];
        if (v == CMSat::l_Undef) return CMSat::l_Undef;
        return l.sign() ? (v == CMSat::l_True ? CMSat::l_False : CMSat::l_True) : v;
    }

    const ArjunInt::Config& conf;
    ArjunNS::SimplifiedCNF& cnf;

    // Populated from cnf at run() entry; read-only afterwards.
    std::set<uint32_t> input;
    std::set<uint32_t> to_define;
    std::set<uint32_t> backward_defined;

    // Two SAT solvers and lazy true-lits for each / for cnf.
    std::unique_ptr<ArjunInt::MetaSolver> s;        // miter
    std::unique_ptr<ArjunInt::MetaSolver> f_solver; // F-only
    CMSat::Lit s_true_lit         = CMSat::lit_Undef;
    CMSat::Lit f_true_lit         = CMSat::lit_Undef;
    CMSat::Lit cnf_true_lit_new   = CMSat::lit_Undef;
    CMSat::Lit cnf_true_lit_orig  = CMSat::lit_Undef;

    std::map<uint32_t, CMSat::Lit> new_to_orig;

    // Indicator var per to-define var (NEW-var-space → SAT var in `s`).
    // Rebuilt from scratch in build_indicators().
    std::vector<uint32_t> var_to_indic;

    // Per-test scratch. aux_mask is sized once at run() entry; aux_vars
    // / aux_mask contents are reset per test in build_aux_set().
    std::vector<uint32_t> aux_vars;
    std::vector<char>     aux_mask;
    // Recursive-deps cache for the cycle check on backward-defined aux
    // candidates. Cleared after every successful commit since the new
    // def changes deps.
    std::map<uint32_t, std::vector<uint32_t>> deps_cache;

    // Per-commit (test_var_NEW, H_AIG_NEW) pairs to materialize into cnf
    // clauses after the per-test loop completes. We can't materialize in
    // the loop because cnf.new_var() would shift cnf.nVars(), breaking the
    // Y'-side offset in `s` and in encode_h_in_miter.
    std::vector<std::pair<uint32_t, ArjunNS::aig_ptr>> deferred_materialize;
    std::set<uint32_t> already_tested;
    uint32_t tested_num = 0;
    uint32_t new_defs   = 0;
    double   t0         = 0.0;

    UnateDefRepStats rep_stats;

    // Lazy true-literal allocators for each solver / cnf side.
    CMSat::Lit get_s_true();
    CMSat::Lit get_f_true();
    std::pair<CMSat::Lit, CMSat::Lit> get_cnf_true();

    // Tseitin encoders / structural helpers.
    CMSat::Lit encode_h_in_miter(const ArjunNS::aig_ptr& h, bool is_y_prime);
    CMSat::Lit encode_h_in_f(const ArjunNS::aig_ptr& h);
    CMSat::Lit materialize_h_in_cnf(const ArjunNS::aig_ptr& h);
    size_t h_aux_leaf_count(const ArjunNS::aig_ptr& h) const;

    // Per-var diagnostics for the verb=1/2 trace. Lives only across
    // process_test_var and its helpers.
    struct PerVarStats {
        uint32_t iters = 0;
        uint32_t miter_sat = 0, miter_unsat = 0, miter_undef = 0;
        uint32_t f_sat = 0, f_unsat = 0, f_undef = 0;
        uint32_t skipped_big = 0;
        uint64_t pattern_sum = 0;
        uint32_t pattern_count = 0;
        uint32_t costzero_count = 0;
        // Per-var minimization counters (for the verb=2 trace line).
        uint32_t minim_attempts = 0;
        uint32_t minim_lits_dropped = 0;
        const char* stop_reason = "iter_limit";
    };
    enum class CexAction { Refine, Continue, Break };

    // Pass-section helpers, in the order run() uses them. Each helper's
    // body is a verbatim move of the corresponding block in the original
    // synthesis_unate_def_rep.
    void setup_yprime_backward_defs();
    void build_indicators();
    void build_f_solver();
    std::vector<CMSat::Lit> build_base_assumps(const uint32_t test);
    void build_allowed_aux_set(const uint32_t test, const CMSat::Lit test_orig);
    void process_test_var(const uint32_t test);
    void log_progress_periodic();
    bool try_commit_h(const uint32_t test, const CMSat::Lit test_orig,
                       const ArjunNS::aig_ptr& h, const CMSat::Lit h_top_lit,
                       const CMSat::Lit act, const uint32_t iter,
                       PerVarStats& vstats);
    CexAction process_cex(const uint32_t test, const CMSat::Lit h_top_lit, const CMSat::Lit act,
                           uint32_t iter, ArjunNS::aig_ptr& h,
                           PerVarStats& vstats);
    // Greedy minimization on the F-only conflict. Tries to drop each
    // pattern lit and re-solve with `force_wrong` kept; if still UNSAT
    // and `~force_wrong` remains in the conflict, replaces `pattern_lits`
    // with the smaller conflict. Bounded by
    // `unate_def_rep_minim_budget`. No-op when `unate_def_rep_minim==0`.
    void minimize_pattern(std::vector<CMSat::Lit>& pattern_lits,
                          CMSat::Lit force_wrong,
                          PerVarStats& vstats);
    // One-shot "drop all aux lits from the pattern at once" SAT call.
    // If the input-only subset still produces UNSAT-with-~force_wrong,
    // replace pattern_lits with the smaller (input-only) conflict.
    // Returns nothing; updates rep_stats counters and pattern_lits.
    void drop_aux_oneshot(std::vector<CMSat::Lit>& pattern_lits,
                          CMSat::Lit force_wrong,
                          PerVarStats& vstats);
    void log_per_var_summary(uint32_t test, const ArjunNS::aig_ptr& h,
                              const PerVarStats& vstats);
    void materialize_deferred();
    void log_pass_summary();
};

}
