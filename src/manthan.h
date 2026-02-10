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

#include "arjun.h"
#include "config.h"
#include "metasolver.h"
#include "cachedsolver.h"
#include <cryptominisat5/solvertypesmini.h>

#include <cstdint>
#include <memory>
#include <sys/types.h>
#include <vector>
#include <set>
#include "formula.h"


/* #define MLPACK_PRINT_INFO */
/* #define MLPACK_PRINT_WARN */
#include <mlpack.hpp>

using namespace arma;
using namespace mlpack;
using namespace mlpack::tree;
using namespace CMSat;

using std::vector;
using std::set;
using std::map;
using std::unique_ptr;
using std::string;
using sample = vector<lbool>;

using namespace ArjunInt;
using namespace ArjunNS;

class Manthan {
    public:
        Manthan(const Config& _conf, const Arjun::ManthanConf& _mconf, const SimplifiedCNF& _cnf)
             :
            cnf(_cnf), conf(_conf), mconf(_mconf)
            , cex_solver(static_cast<SolverType>(_mconf.ctx_solver_type))
            , repair_solver(static_cast<SolverType>(_mconf.repair_solver_type), _mconf.repair_cache_size)
        {
                mtrand.seed(42);
        }
        SimplifiedCNF do_manthan(const uint32_t max_repairs);
        const SimplifiedCNF& cnf;

    private:
        vec point_0;
        vec point_1;
        /* uint32_t last_formula_var; */

        // y is original output var, i.e. to_define
        // y_hat is learned var
        map<uint32_t, uint32_t> y_to_y_hat;
        map<uint32_t, uint32_t> y_hat_to_y;

        // when indic is TRUE, y_hat and func_out are EQUAL
        map<uint32_t, uint32_t> y_hat_to_indic;
        map<uint32_t, uint32_t> indic_to_y_hat;
        map<uint32_t, uint32_t> indic_to_y;
        set<uint32_t> needs_repair;

        const Config& conf;
        const Arjun::ManthanConf& mconf;
        unique_ptr<FieldGen> fg;
        MetaSolver cex_solver;
        CachedSolver repair_solver;

        // 3 sets of variables, together adding up to the CNF
        set<uint32_t> input;
        set<uint32_t> to_define;
        set<uint32_t> backward_defined;
        set<uint32_t> to_define_full;
        set<uint32_t> helpers;
        set<uint32_t> y_hats;

        void full_train();
        void bve_and_substitute();
        aig_ptr one_level_substitute(const Lit l, const uint32_t v, map<uint32_t, aig_ptr>& transformed);

        void create_vars_for_y_hats();
        FHolder::Formula recur(DecisionTree<>* node, const uint32_t learned_v, const vector<uint32_t>& var_remap, uint32_t depth, uint32_t& max_depth);
        vector<uint32_t> incidence;
        Lit map_y_to_y_hat(const Lit& l) const;
        uint32_t calc_non_bw_needs_repair() const;
        void print_needs_repair_vars() const;
        void print_cnf_debug_info(const sample& ctx) const;
        void get_incidence();
        bool get_counterexample(sample& ctx);
        void inject_formulas_into_solver();
        vector<sample*> filter_samples(const uint32_t v, const vector<sample>& samples);
        void find_better_ctx_maxsat(sample& ctx);
        void find_better_ctx_normal(sample& ctx);
        template<typename S>
        void inject_cnf(S& s) const;
        void inject_unit(SATSolver& s);
        bool repair(const uint32_t v, sample& ctx);
        bool find_conflict(const uint32_t y_rep, sample& ctx, vector<Lit>& conflict);
        void minimize_conflict(vector<Lit>& conflict, vector<Lit>& assumps, const Lit repairing);
        uint32_t find_next_repair_var(const sample& ctx) const;
        void perform_repair(const uint32_t y_rep, const sample& ctx, const vector<Lit>& conflict);
        void add_not_f_x_yhat(MetaSolver& s);
        void fill_dependency_mat_with_backward();
        void fill_var_to_formula_with_backward();
        void print_y_order_occur() const;
        void compute_needs_repair(const sample& ctx);
        void recompute_all_y_hat(sample& ctx, const uint32_t y_rep);

        // ordering
        vector<uint32_t> y_order; //1st only depends on inputs
        vector<int> order_val; // inputs have order -1, everything else as per y_order
        void order_vars();
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
        inline void set_depends_on(const uint32_t a, const Lit b) {
            set_depends_on(a, b.var());
        }


        bool verify_final_cnf(const SimplifiedCNF& fcnf) const;
        void add_sample_clauses(SimplifiedCNF& cnf);
        vector<sample> get_cmsgen_samples(const uint32_t num_samples);
        vector<sample> get_samples_ccnr(const uint32_t num_samples);
        void sort_all_samples(vector<sample>& samples);
        double train(const vector<sample>& samples, const uint32_t v); // returns training error
        vector<vector<char>> dependency_mat; // dependency_mat[a][b] = 1 if a depends on b

        unique_ptr<FHolder> fh = nullptr;
        std::map<uint32_t, FHolder::Formula> var_to_formula; // var -> formula
        string pr(const lbool val) const;
        bool lbool_to_bool(const lbool val) const {
            assert(val != l_Undef);
            return val == l_True;
        }

        AIGManager aig_mng;

        // debug
        bool ctx_y_hat_correct(const sample& ctx) const;
        bool ctx_is_sat(const sample& ctx) const;
        bool check_map_dependency_cycles() const;
        bool has_dependency_cycle_dfs(const uint32_t node, vector<uint8_t>& color, vector<uint32_t>& path) const; // used in check_dependency_loop
        bool check_train_correctness() const;
        bool check_aig_dependency_cycles() const;
        bool check_transitive_closure_correctness() const;
        bool check_functions_for_y_vars() const;
        std::mt19937 mtrand;
        vector<uint32_t> updated_y_funcs; // y_hats updated during last round of training

        // stats
        uint32_t num_loops_repair = 0;
        uint64_t conflict_sizes_sum = 0;
        uint64_t needs_repair_sum = 0;
        uint32_t tot_repaired = 0;
        uint32_t repair_failed = 0;

        double sampl_time = 0;
        double train_time = 0;
};
