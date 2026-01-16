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
        Manthan(const Config& _conf, const Arjun::ManthanConf& _mconf, const std::unique_ptr<FieldGen>& _fg):
            cnf(_fg->dup()), conf(_conf), mconf(_mconf), fg(_fg->dup()) {
                mtrand.seed(42);
            }
        SimplifiedCNF do_manthan(const SimplifiedCNF& cnf);
        SimplifiedCNF cnf;

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
        set<uint32_t> needs_repair;

        const Config& conf;
        const Arjun::ManthanConf& mconf;
        unique_ptr<FieldGen> fg;
        SATSolver solver;
        SATSolver repair_solver;

        // 3 sets of variables, together adding up to the CNF
        set<uint32_t> input;
        set<uint32_t> to_define;
        set<uint32_t> backward_defined;
        set<uint32_t> to_define_full;

        FHolder::Formula recur(DecisionTree<>* node, const uint32_t learned_v, const vector<uint32_t>& var_remap, uint32_t depth = 0);
        vector<uint32_t> incidence;
        void print_cnf_debug_info(const sample& ctx) const;
        void get_incidence();
        bool get_counterexample(sample& ctx);
        void inject_formulas_into_solver();
        bool check_satisfied_all_cls_with_flip(const sample& s, const uint32_t v) const;
        vector<sample*> filter_samples(const uint32_t v, const vector<sample>& samples);
        sample find_better_ctx_maxsat(const sample& ctx, uint32_t& old_needs_repair_size);
        sample find_better_ctx_normal(const sample& ctx, uint32_t& old_needs_repair_size);
        void inject_cnf(SATSolver& s, const bool also_vars = true) const;
        void inject_unit(SATSolver& s);
        bool repair(const uint32_t v, sample& ctx);
        bool find_minim_conflict(const uint32_t y_rep, sample& ctx, vector<Lit>& conflict);
        void minimize_conflict(vector<Lit>& conflict, vector<Lit>& assumps, const Lit repairing);
        uint32_t find_next_repair_var(sample& ctx);
        void perform_repair(const uint32_t y_rep, const sample& ctx, const vector<Lit>& conflict);
        void add_not_F_x_yhat();
        void fill_dependency_mat_with_backward();
        void fill_var_to_formula_with_backward();
        void print_y_order_occur() const;

        vector<uint32_t> y_order; //1st only depends on inputs
        void fix_order();


        bool verify_final_cnf(const SimplifiedCNF& fcnf) const;
        void add_sample_clauses(SimplifiedCNF& cnf);
        vector<sample> get_samples(const uint32_t num_samples);
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
        bool check_map_dependency_cycles() const;
        bool has_dependency_cycle_dfs(const uint32_t node, vector<uint8_t>& color, vector<uint32_t>& path) const; // used in check_dependency_loop
        bool check_train_correctness() const;
        bool check_aig_dependency_cycles() const;
        bool check_transitive_closure_correctness() const;
        std::mt19937 mtrand;
        vector<uint32_t> updated_y_funcs; // y_hats updated during last round of training

        // stats
        uint32_t num_loops_repair = 0;
        uint64_t conflict_sizes_sum = 0;
        uint64_t needs_repair_sum = 0;
};
