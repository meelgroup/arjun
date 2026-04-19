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
#include "metasolver2.h"
#include "cachedsolver.h"
#include <cryptominisat5/solvertypesmini.h>

#include <cstdint>
#include <memory>
#include <vector>
#include <set>
#include "formula.h"
#include "treedecomp/TreeDecomposition.hpp"

namespace ArjunInt {

using sample = std::vector<CMSat::lbool>;
class ManthanLearn;

class Manthan {
    public:
        Manthan(const Config& _conf, const ArjunNS::Arjun::ManthanConf& _mconf, ArjunNS::SimplifiedCNF&& _cnf) :
            conf(_conf), mconf(_mconf)
            , cex_solver(static_cast<SolverType>(_mconf.ctx_solver_type))
            , repair_solver(static_cast<SolverType>(_mconf.repair_solver_type), _mconf.repair_cache_size)
            , cnf(std::move(_cnf))
        {
                mtrand.seed(42);
        }
        ArjunNS::SimplifiedCNF do_manthan();
        friend class ManthanLearn;

    private:
        // y is original output var, i.e. to_define
        // y_hat is learned var
        std::map<uint32_t, uint32_t> y_to_y_hat;
        std::map<uint32_t, CMSat::Lit> y_hat_to_y;

        // when indic is TRUE, y_hat and func_out are EQUAL
        std::map<uint32_t, uint32_t> y_hat_to_indic;
        std::map<uint32_t, uint32_t> indic_to_y_hat;
        std::map<uint32_t, uint32_t> indic_to_y;
        std::set<uint32_t> needs_repair;

        const Config& conf;
        const ArjunNS::Arjun::ManthanConf& mconf;
        std::unique_ptr<CMSat::FieldGen> fg;
        MetaSolver2 cex_solver;
        CachedSolver repair_solver;

        // 3 sets of variables, together adding up to the CNF
        std::set<uint32_t> input;
        std::set<uint32_t> to_define;
        std::set<uint32_t> backward_defined;
        std::set<uint32_t> to_define_full; // to_define + backward_defined
        std::set<uint32_t> helper_functions; // these are in BW, but we definitely want them

        // To help us account for every variable in the formulas' clauses
        std::set<uint32_t> helpers; // used for ITE
        std::set<uint32_t> y_hats; // the potential y_hats (due to ITE chains, some are "old" and unused)

        std::unique_ptr<TWD::Graph> build_primal_graph();
        void const_functions();
        void bve_and_substitute();
        ArjunNS::aig_ptr one_level_substitute(const CMSat::Lit l, const uint32_t v, std::map<uint32_t, ArjunNS::aig_ptr>& transformed);

        void create_vars_for_y_hats();
        std::vector<uint32_t> incidence;
        std::vector<double> td_score;

        CMSat::Lit map_y_to_y_hat(const CMSat::Lit& l) const;
        void print_needs_repair_vars() const;
        void print_cnf_debug_info(const sample& ctx) const;
        void get_incidence();
        bool get_counterexample(sample& ctx);
        void inject_formulas_into_solver();
        std::vector<const sample*> filter_samples(const uint32_t v, const std::vector<sample>& samples);
        void find_better_ctx_maxsat(sample& ctx);
        void find_better_ctx_normal(sample& ctx);
        template<typename S>
        void inject_cnf(S& s) const;
        bool repair(const uint32_t v, sample& ctx);
        std::vector<sample> collect_extra_cex(const sample& ctx);
        bool find_conflict(const uint32_t y_rep, sample& ctx, std::vector<CMSat::Lit>& conflict);
        std::vector<uint32_t> var_conflict_freq; // how often each var appears in conflicts
        void minimize_conflict(std::vector<CMSat::Lit>& conflict, std::vector<CMSat::Lit>& assumps, const CMSat::Lit repairing);
        uint32_t find_next_repair_var(const sample& ctx) const;
        void perform_repair(const uint32_t y_rep, const sample& ctx, const std::vector<CMSat::Lit>& conflict);
        void add_not_f_x_yhat();
        void rebuild_cex_solver_if_needed(uint64_t total_formula_clauses, bool& did_rebuild);
        void rebuild_cex_solver();
        void fill_dependency_mat_with_backward();
        void fill_var_to_formula_with(std::set<uint32_t>& vars);
        void print_y_order_occur() const;
        void compute_needs_repair(const sample& ctx);
        void recompute_all_y_hat_cnf(sample& ctx);
        void recompute_all_y_hat_aig(sample& ctx, const uint32_t y_rep);

        // ordering
        std::vector<uint32_t> y_order; //1st only depends on inputs
        std::vector<int> order_val; // inputs have order -1, everything else as per y_order
        void topological_sort_order();
        void pre_order_vars();
        void post_order_vars();
        void learn_order();
        void bve_order();
        bool cluster_order();
        void compute_td_score_using_adj(const uint32_t nodes,
            const std::vector<std::vector<int>>& bags,
            const std::vector<std::vector<int>>& adj, const std::map<uint32_t, uint32_t>& new_to_old);
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

        std::vector<sample> get_cmsgen_samples(const uint32_t samples);
        std::vector<sample> get_samples_ccnr(const uint32_t samples);
        void sort_all_samples(std::vector<sample>& samples);
        double train(const std::vector<sample>& samples, const uint32_t v); // returns training error
        std::vector<std::vector<char>> dependency_mat; // dependency_mat[a][b] = 1 if a depends on b

        // Formulas
        void add_xor_var();
        std::unique_ptr<FHolder<MetaSolver2>> fh = nullptr;
        std::map<uint32_t, FHolder<MetaSolver2>::Formula> var_to_formula; // var -> formula

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
            const ArjunNS::aig_ptr& aig,
            const std::map<uint32_t, uint32_t>& count_y_to_y_hat,
            std::vector<std::vector<CMSat::Lit>>& clauses,
            uint32_t& next_var,
            CMSat::Lit true_lit,
            std::map<ArjunNS::aig_ptr, CMSat::Lit>& cache);
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
        std::mt19937 mtrand;
        std::vector<uint32_t> updated_y_funcs; // y_hats updated during last round of training
        std::set<uint32_t> needs_reencode; // formulas modified since last rebuild
        uint32_t nvars_at_last_rebuild = 0; // nVars at last rebuild for growth tracking

        // stats
        double repair_start_time;
        void print_stats(const std::string& txt = "", const std::string& color = "", const std::string& extra = "") const;
        void print_repair_stats(const std::string& txt = "", const std::string& color = "", const std::string& extra = "") const;
        void print_detailed_stats() const;
        uint32_t num_loops_repair = 0;
        uint64_t conflict_sizes_sum = 0;
        uint32_t generalized_repair_ok = 0;
        uint32_t generalized_repair_fallback = 0;
        uint64_t needs_repair_sum = 0;
        uint32_t tot_repaired = 0;
        uint32_t repair_failed = 0;
        std::vector<uint32_t> repaired_vars_count; // for each y, how many times it was repaired
        std::vector<uint32_t> input_only_ok; // per-var: consecutive input-only successes
        std::vector<uint32_t> input_only_fail; // per-var: consecutive input-only failures
        double sampl_time = 0;
        double train_time = 0;

        // detailed timing stats
        double time_cex_finding = 0;
        double time_collect_extra_cex = 0;
        double time_find_better_ctx = 0;
        double time_find_conflict = 0;
        double time_minimize_conflict = 0;
        double time_perform_repair = 0;
        double time_inject_formulas = 0;
        double time_recompute_y_hat = 0;
        uint64_t input_only_conflict_sizes_sum = 0;
        uint64_t full_conflict_sizes_sum = 0;
        uint32_t input_only_conflict_count = 0;
        uint32_t full_conflict_count = 0;
        uint32_t cost_zero_repairs = 0;
        uint32_t cex_solver_calls = 0;
        uint32_t repair_solver_calls = 0;

        // Main stuff
        ArjunNS::SimplifiedCNF cnf;
        ArjunNS::AIGManager aig_mng;
};
}
