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

#include "arjun.h"
#include "config.h"
#include "constants.h"
#include "metasolver.h"
#include "cachedsolver.h"
#include <cryptominisat5/solvertypesmini.h>

#include <cstdint>
#include <memory>
#include <vector>
#include <set>
#include <unordered_map>
#include "formula.h"

namespace ArjunInt {

using sample = std::vector<CMSat::lbool>;
class ManthanLearn;

struct ManthanStats {
    double repair_start_time;
    void print_stats(const std::string& txt = "", const std::string& color = "", const std::string& extra = "") const;

    uint32_t num_loops_repair = 0;
    uint64_t conflict_sizes_sum = 0;
    uint32_t input_only_rep = 0;
    uint64_t needs_repair_sum = 0;
    int32_t tot_repaired = 0;
    uint32_t repair_failed = 0;
    double sampl_time = 0;
    double train_time = 0;

    uint64_t input_only_conflict_sizes_sum = 0;
    uint64_t full_conflict_sizes_sum = 0;
    uint32_t input_only_conflict_count = 0;
    uint32_t full_conflict_count = 0;
    uint32_t cost_zero_repairs = 0;
    uint32_t cex_solver_calls = 0;
    uint32_t repair_solver_calls = 0;

    ManthanStats& operator+=(const ManthanStats& other) {
        num_loops_repair += other.num_loops_repair;
        conflict_sizes_sum += other.conflict_sizes_sum;
        input_only_rep += other.input_only_rep;
        needs_repair_sum += other.needs_repair_sum;
        tot_repaired += other.tot_repaired;
        repair_failed += other.repair_failed;
        sampl_time += other.sampl_time;
        train_time += other.train_time;

        input_only_conflict_sizes_sum += other.input_only_conflict_sizes_sum;
        full_conflict_sizes_sum += other.full_conflict_sizes_sum;
        input_only_conflict_count += other.input_only_conflict_count;
        full_conflict_count += other.full_conflict_count;
        cost_zero_repairs += other.cost_zero_repairs;
        cex_solver_calls += other.cex_solver_calls;
        repair_solver_calls += other.repair_solver_calls;
        return *this;
    }
};

class Manthan {
    public:
        Manthan(const Config& _conf, const ArjunNS::Arjun::ManthanConf& _mconf, ArjunNS::SimplifiedCNF&& _cnf) :
            conf(_conf), mconf(_mconf)
            , cex_solver(static_cast<SolverType>(_mconf.ctx_solver_type))
            , repair_solver(static_cast<SolverType>(_mconf.repair_solver_type), _mconf.repair_cache_size)
            , cnf(std::move(_cnf))
        {
        }
        ArjunNS::SimplifiedCNF do_manthan();
        friend class ManthanLearn;

        // Restart support: guess maps each to_define var to its tentative AIG.
        void set_guess(std::map<uint32_t, ArjunNS::aig_lit>&& g) { guess = std::move(g); }
        [[nodiscard]] bool restart_requested() const { return restart_needed; }
        [[nodiscard]] const ManthanStats& get_stats() const { return stats; }
        // AIG snapshot of every to_define formula; feeds the next round's guess.
        [[nodiscard]] std::map<uint32_t, ArjunNS::aig_lit> export_formula_aigs() const;

    private:
        // y is original output var, i.e. to_define
        // y_hat is learned var
        std::map<uint32_t, uint32_t> y_to_y_hat;
        std::map<uint32_t, CMSat::Lit> y_hat_to_y;

        // when indic is TRUE, y_hat and func_out are EQUAL
        std::map<uint32_t, uint32_t> y_hat_to_indic;
        std::map<uint32_t, uint32_t> indic_to_y;
        std::set<uint32_t> needs_repair;

        const Config& conf;
        const ArjunNS::Arjun::ManthanConf& mconf;
        MetaSolver cex_solver;
        CachedSolver repair_solver;

        // 3 sets of variables, together adding up to the CNF
        std::set<uint32_t> input;
        std::set<uint32_t> to_define;
        std::set<uint32_t> backward_defined;
        std::set<uint32_t> to_define_full; // to_define + backward_defined

        // O(1) membership mirrors of the sets above; sized to cnf.nVars(),
        // kept in sync via rebuild_var_bytemaps().
        std::vector<uint8_t> is_input;
        std::vector<uint8_t> is_backward_defined;
        void rebuild_var_bytemaps();

        // To help us account for every variable in the formulas' clauses
        std::set<uint32_t> helpers; // used for ITE
        std::set<uint32_t> y_hats; // the potential y_hats (due to ITE chains, some are "old" and unused)

        void const_functions();
        void bve_and_substitute();
        // Encode per-y AIGs into var_to_formula via AIGToCNF.
        void encode_aigs_to_formulas(const std::vector<ArjunNS::aig_lit>& aigs,
                const double start_time);
        // Compact the guess AIGs and seed var_to_formula from them.
        void init_from_guess();
        std::map<uint32_t, ArjunNS::aig_lit> guess;
        bool restart_needed = false;
        // Shared-batch AIGToCNF encode of `aigs`; sets each y's formula to
        // {aig, out}, helper defs into shared_helper_cls + cex_solver.
        void install_shared_encoded_formulas(const std::vector<ArjunNS::aig_lit>& aigs);

        void create_vars_for_y_hats();
        std::vector<uint32_t> incidence;

        CMSat::Lit map_y_to_y_hat(const CMSat::Lit& l) const;
        void print_needs_repair_vars() const;
        void print_cnf_debug_info(const sample& ctx) const;
        void print_cache_hit_rate() const;
        void get_incidence();
        bool get_counterexample(sample& ctx);
        void inject_formulas_into_solver();
        std::vector<const sample*> filter_samples(const uint32_t v, const std::vector<sample>& samples);
        void find_better_ctx_maxsat(sample& ctx);
        void find_better_ctx_normal(sample& ctx);
        template<typename S>
        void inject_cnf(S& s) const;
        bool repair(const uint32_t v, sample& ctx);
        bool find_conflict(const uint32_t y_rep, sample& ctx,
                std::vector<CMSat::Lit>& conflict);
        // Fill aig_dep_is_dep/aig_dep_list with y_rep's AIG input deps (via
        // dep_cache when unchanged). Returns true if any dep was found.
        bool compute_aig_dep_set(const uint32_t y_rep);
        // Try an input-only conflict: assume dependent inputs + ~to_repair,
        // leaving earlier y-vars free. On UNSAT sets conflict/assumps and
        // returns true (more general than full-assumption); else false.
        bool try_input_only_conflict(const uint32_t y_rep, const sample& ctx,
                const CMSat::Lit to_repair, const bool have_aig_deps,
                std::vector<CMSat::Lit>& conflict,
                std::vector<CMSat::Lit>& assumps);
        // Full-assumption conflict: dependent inputs + earlier y-vars +
        // ~to_repair. Returns true with `conflict` set on UNSAT; false on a
        // cost-zero repair (ctx updated). Used when try_input_only fails.
        bool solve_full_assumption_conflict(const uint32_t y_rep, sample& ctx,
                const CMSat::Lit to_repair, const bool have_aig_deps,
                std::vector<CMSat::Lit>& conflict,
                std::vector<CMSat::Lit>& assumps,
                const double repair_solver_start_time);
        // Copy the repair_solver model into ctx for y_rep and all later y-vars
        // (cost-zero repair: y_rep is satisfiable without changing the formula).
        void apply_cost_zero_model(const uint32_t y_rep, sample& ctx);
        // Minimize then generalise the conflict (drop y-vars) and strip the
        // to_repair literal, leaving the must-flip region's literals.
        void minimize_and_generalize_conflict(std::vector<CMSat::Lit>& conflict,
                std::vector<CMSat::Lit>& assumps, const CMSat::Lit to_repair);
        // Drop ALL y-vars from the conflict if the input-only remainder is
        // still UNSAT (a strictly more general repair).
        void try_drop_y_vars(std::vector<CMSat::Lit>& conflict,
                std::vector<CMSat::Lit>& assumps, const CMSat::Lit to_repair);
        // Reusable scratch for AIG::get_dependent_vars in find_conflict;
        // avoids per-call allocs (visited state via AIG::visit_epoch).
        std::vector<char> aig_dep_is_dep;
        std::vector<uint32_t> aig_dep_list;
        std::vector<const ArjunNS::AIG*> aig_dep_stack;
        // Memoized dep list per y, keyed by var_to_formula[y].aig's
        // pointer; a mismatch (formula rewritten) triggers recompute.
        struct DepCacheEntry {
            const ArjunNS::AIG* aig_lit;
            std::vector<uint32_t> dep_list;
        };
        std::unordered_map<uint32_t, DepCacheEntry> dep_cache;
        // Extend y_rep's cached dep list with the conflict vars after a
        // repair (new deps = old ∪ conflict); erases the entry on any
        // structurally unexpected compose result.
        void update_dep_cache_after_repair(const uint32_t y_rep,
                const ArjunNS::AIG* old_root,
                const std::vector<CMSat::Lit>& conflict);
        // Cached leaf-var list of y's formula AIG (all leaves: inputs +
        // y/y_hat vars, mixed space). Backing store is dep_cache.
        const std::vector<uint32_t>& formula_dep_list(const uint32_t y);
        // Scratch for recompute_all_y_hat_cnf's topological evaluation.
        std::vector<uint8_t> recompute_state;
        std::vector<uint32_t> recompute_topo;
        std::vector<uint32_t> recompute_dfs;
        std::vector<uint8_t> recompute_changed;
        // O(1) y <-> y_hat maps (mirrors of y_to_y_hat / y_hat_to_y) for the
        // recompute hot path; entries are UINT32_MAX where unmapped.
        std::vector<uint32_t> y_to_yhat_flat;
        std::vector<uint32_t> yhat_to_y_flat;
        std::vector<uint32_t> var_conflict_freq; // how often each var appears in conflicts
        void minimize_conflict(std::vector<CMSat::Lit>& conflict, std::vector<CMSat::Lit>& assumps, const CMSat::Lit repairing);
        uint32_t find_next_repair_var(const sample& ctx) const;
        // Add the repair conflict as a redundant clause to repair_solver,
        // to speed up future repair_solver reasoning.
        void add_repair_conflict_clause(const uint32_t y_rep, const sample& ctx,
                const std::vector<CMSat::Lit>& conflict);
        void perform_repair(const uint32_t y_rep, const sample& ctx,
                const std::vector<CMSat::Lit>& conflict);

        void add_not_f_x_yhat();
        void fill_dependency_mat_with_backward();
        void fill_var_to_formula_with(std::set<uint32_t>& vars);
        void print_y_order_occur() const;
        void compute_needs_repair(const sample& ctx);
        void recompute_all_y_hat_cnf(sample& ctx, const uint32_t y_rep);

        // ordering
        std::vector<uint32_t> y_order; //1st only depends on inputs
        std::vector<int> order_val; // inputs have order -1, everything else as per y_order
        std::vector<uint32_t> y_order_weight; // better-ctx weight per y (see pre_order_vars)
        void pre_order_vars();
        void learn_order();
        void bve_order();
        bool later_in_order(const uint32_t a, const uint32_t b) const {
            SLOW_DEBUG_DO({
                assert(order_val.size() > a);
                assert(order_val.size() > b);
            });
            return order_val[a] > order_val[b];
        }
        void set_depends_on(const uint32_t a, const uint32_t b);
        inline void set_depends_on(const uint32_t a, const CMSat::Lit b) {
            set_depends_on(a, b.var());
        }

        std::vector<sample> get_cmsgen_samples(uint32_t samples);
        void sort_all_samples(std::vector<sample>& samples);
        std::vector<std::vector<char>> dependency_mat; // dependency_mat[a][b] = 1 if a depends on b

        // Formulas
        // Persistent solver for find_better_ctx_normal: holds the (fixed)
        // CNF; per-call values arrive as assumptions.
        std::unique_ptr<CMSat::SATSolver> better_ctx_solver;
        std::unique_ptr<FHolder<MetaSolver>> fh = nullptr;
        std::map<uint32_t, FHolder<MetaSolver>::Formula> var_to_formula; // var -> formula
        // Helper defs from the shared AIGToCNF batch, referenced by multiple
        // formulas' .out chains. Inserted into cex_solver once, never dropped.
        // Debug miters must add these alongside formula clauses.
        std::vector<std::vector<CMSat::Lit>> shared_helper_cls;

        // helper functions
        std::string pr(const CMSat::lbool val) const;
        bool lbool_to_bool(const CMSat::lbool val) const {
            assert(val != CMSat::l_Undef);
            return val == CMSat::l_True;
        }
        std::vector<int> lits_to_ints(const std::vector<CMSat::Lit>& lits) {
            std::vector<int> ret;
            ret.reserve(lits.size());
            for(const auto& l: lits) ret.push_back(lit_to_pl(l));
            return ret;
        }

        // error formula counting via ganak subprocess
        void check_repair_monotonic();
        bool count_error_formula(mpz_class& out_count);
        CMSat::Lit tseitin_encode_aig(
            const ArjunNS::aig_lit& aig,
            const std::map<uint32_t, uint32_t>& count_y_to_y_hat,
            std::vector<std::vector<CMSat::Lit>>& clauses,
            uint32_t& next_var,
            CMSat::Lit true_lit,
            std::map<ArjunNS::aig_lit, CMSat::Lit>& cache);
        mpz_class prev_error_count = -1; // -1 means no previous count

        // debug
        [[nodiscard]] bool verify_final_cnf(const ArjunNS::SimplifiedCNF& fcnf) const;
        [[nodiscard]] bool is_unsat(const std::vector<CMSat::Lit>& conflict, uint32_t y_rep, const sample& ctx) const;
        [[nodiscard]] bool ctx_y_hat_correct(const sample& ctx) const;
        [[nodiscard]] bool ctx_is_sat(const sample& ctx) const;
        [[nodiscard]] bool check_map_dependency_cycles() const;
        [[nodiscard]] bool has_dependency_cycle_dfs(const uint32_t node, std::vector<uint8_t>& color, std::vector<uint32_t>& path) const; // used in check_dependency_loop
        [[nodiscard]] bool check_aig_dependency_cycles() const;
        [[nodiscard]] bool check_transitive_closure_correctness() const;
        [[nodiscard]] bool check_functions_for_y_vars() const;
        // SLOW_DEBUG: verify var_to_formula is a correct synthesis vs
        // cnf.get_clauses() with a fresh miter (independent of cex_solver).
        // _via_clauses checks .clauses+.out (what cex_solver sees); _via_aig
        // checks .aig (what becomes cnf.defs). Divergence => CNF/AIG mismatch.
        [[nodiscard]] bool check_synth_via_clauses(const std::string& where) const;
        [[nodiscard]] bool check_synth_via_aig(const std::string& where) const;
        // SLOW_DEBUG: prove f.aig and f.clauses+f.out denote the same function
        // for every y; the invariant linking "cex_solver UNSAT = correct" to
        // "final .aig export is correct".
        [[nodiscard]] bool check_aig_matches_clauses_per_formula(const std::string& where) const;
        std::vector<uint32_t> updated_y_funcs; // y_hats updated during last round of training

        ManthanStats stats;
        std::vector<uint32_t> repaired_vars_count; // for each y, how many times it was repaired
        void print_detailed_stats(const ManthanStats& stats) const;

        // Cumulative per-phase CPU time (s) for the repair loop.
        double t_cex_solve = 0;      // get_counterexample
        double t_better_ctx = 0;     // find_better_ctx_{normal,maxsat}
        double t_find_conflict = 0;  // repair_solver solves incl. minimize
        double t_perform_repair = 0; // formula/AIG compose
        double t_inject = 0;         // inject_formulas_into_solver
        double t_recompute_yhat = 0; // recompute_all_y_hat_cnf
        double t_recompute_topo = 0; // recompute: topo DFS + dirty scan
        double t_recompute_eval = 0; // recompute: AIG evaluations


        // Main stuff
        ArjunNS::SimplifiedCNF cnf;
        ArjunNS::AIGManager aig_mng;

        // Per-var successful-repair count and summed conflict-clause length
        // (avg = lits_sum / count). Separate from repaired_vars_count[v],
        // which counts attempts incl. cost-zero failures.
        std::vector<uint32_t> conflict_branch_repairs_per_var;
        std::vector<uint64_t> conflict_branch_lits_per_var;
};
}
