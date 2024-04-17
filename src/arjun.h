/******************************************
Copyright (C) 2020 Mate Soos

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
***********************************************/

#pragma once

#include <cstdint>
#include <vector>
#include <utility>
#include <string>
#include <mpfr.h>
#include <set>
#include <gmpxx.h>
#ifdef CMS_LOCAL_BUILD
#include "cryptominisat.h"
#else
#include <cryptominisat5/cryptominisat.h>
#endif

namespace ArjunNS {
    struct SimpConf {
        bool oracle_vivify = true;
        bool oracle_vivify_get_learnts = true;
        bool oracle_sparsify = true;
        int iter1 = 2;
        int iter2 = 2;
        int bve_grow_iter1 = 0;
        int bve_grow_iter2 = 0;
        bool appmc = false;
        int bve_too_large_resolvent = -1;
    };

    struct SimplifiedCNF {
        uint32_t nvars = 0;
        std::vector<uint32_t> sampl_vars;
        std::vector<uint32_t> opt_sampl_vars;
        std::vector<std::vector<CMSat::Lit>> cnf;
        std::vector<std::vector<CMSat::Lit>> red_cnf;

        bool weighted = false;
        mpz_class multiplier_weight = 1;
#ifdef WEIGHTED
        std::map<CMSat::Lit, double> weights; // ONLY makes sense when weighted is TRUE
#endif

        std::vector<CMSat::Lit>& map_cl(std::vector<CMSat::Lit>& cl, std::vector<uint32_t> v_map) {
            for(auto& l: cl) l = CMSat::Lit(v_map[l.var()], l.sign());
            return cl;
        }
        std::vector<uint32_t>& map_var(std::vector<uint32_t>& cl, std::vector<uint32_t> v_map) {
            for(auto& l: cl) l = v_map[l];
            return cl;
        }
        std::set<uint32_t> map_var(const std::set<uint32_t>& cl, std::vector<uint32_t> v_map) {
            std::set<uint32_t> new_set;
            for(auto& l: cl) new_set.insert(v_map[l]);
            return new_set;
        }

        // renumber variables such that sampling set start from 0...N
        void renumber_sampling_vars_for_ganak() {
            assert(sampl_vars.size() <= opt_sampl_vars.size());
            constexpr uint32_t m = std::numeric_limits<uint32_t>::max();
            std::vector<uint32_t> map_here_to_there(nvars, m);
            uint32_t i = 0;
            for(const auto& v: sampl_vars) {
                assert(v < nvars);
                map_here_to_there[v] = i;
                i++;
            }

            for(const auto& v: opt_sampl_vars) {
                assert(v < nvars);
                if (map_here_to_there[v] == m) {
                    map_here_to_there[v] = i;
                    i++;
                }
            }

            // Go through the rest of the variables not in sampling set.
            for(uint32_t x = 0; x < nvars; x++) {
                if (map_here_to_there[x] == m) {
                    map_here_to_there[x] = i;
                    i++;
                }
            }
            assert(i == nvars);

            // Now we renumber
            sampl_vars = map_var(sampl_vars, map_here_to_there);
            opt_sampl_vars = map_var(opt_sampl_vars, map_here_to_there);
            for(auto& cl: cnf) map_cl(cl, map_here_to_there);
            for(auto& cl: red_cnf) map_cl(cl, map_here_to_there);
#ifdef WEIGHTED
            if (weighted) {
                std::map<CMSat::Lit, double> new_weights;
                for(auto& w: weights)
                    new_weights[CMSat::Lit(map_here_to_there[w.first.var()], w.first.sign())] = w.second;
                weights = new_weights;
            }
#endif
        }
    };

    struct ArjPrivateData;
    #ifdef _WIN32
    class __declspec(dllexport) Arjun
    #else
    class Arjun
    #endif
    {
    public:
        Arjun();
        ~Arjun();
        static std::string get_version_info();
        static std::string get_sbva_version_info();
        static std::string get_compilation_env();
        static std::string get_solver_version_info();

        // Adding CNF
        uint32_t nVars();
        void new_var();
        bool add_xor_clause(const std::vector<CMSat::Lit>& lits, bool rhs);
        bool add_xor_clause(const std::vector<uint32_t>& vars, bool rhs);
        void set_lit_weight(const CMSat::Lit lit, const double weight);
        bool add_clause(const std::vector<CMSat::Lit>& lits);
        bool add_red_clause(const std::vector<CMSat::Lit>& lits);
        bool add_bnn_clause(
            const std::vector<CMSat::Lit>& lits,
            signed cutoff,
            CMSat::Lit out = CMSat::lit_Undef);
        void new_vars(uint32_t num);
        void set_multiplier_weight(const mpz_class mult);

        // Perform indep set calculation
        uint32_t set_sampl_vars(const std::vector<uint32_t>& vars);
        uint32_t set_opt_sampl_vars(const std::vector<uint32_t>& vars);
        uint32_t start_with_clean_sampling_set();
        const std::vector<uint32_t>& get_current_indep_set() const;
        std::vector<uint32_t> run_backwards();
        std::vector<uint32_t> extend_sampl_set();
        std::vector<uint32_t> unsat_define();

        uint32_t get_orig_num_vars() const;
        const std::vector<uint32_t>& get_orig_sampl_vars() const;
        const std::vector<uint32_t>& get_empty_sampl_vars() const;
        bool sampling_vars_set = false;
        bool get_sampl_vars_set() const { return sampling_vars_set; }

        //Get clauses
        void start_getting_constraints(
               bool red = false, // also redundant, otherwise only irred
               bool simplified = false,
               uint32_t max_len = std::numeric_limits<uint32_t>::max(),
               uint32_t max_glue = std::numeric_limits<uint32_t>::max());
        bool get_next_constraint(std::vector<CMSat::Lit>& ret, bool& is_xor, bool& rhs);
        void end_getting_constraints();
        SimplifiedCNF get_fully_simplified_renumbered_cnf(
                const SimpConf& simp_conf);
        void only_bce(SimplifiedCNF& cnf);
        void reverse_bce(SimplifiedCNF& cnf);
        std::vector<CMSat::Lit> get_zero_assigned_lits() const;
        std::vector<std::pair<CMSat::Lit, CMSat::Lit> > get_all_binary_xors() const;
        const SimplifiedCNF& get_orig_cnf() const;
        void run_sbva(SimplifiedCNF& orig,
            int64_t sbva_steps = 200, uint32_t sbva_cls_cutoff = 2,
            uint32_t sbva_lits_cutoff = 2, int sbva_tiebreak = 1);

        //Set config
        void set_seed(uint32_t seed);
        void set_verbosity(uint32_t verb);
        void set_fast_backw(bool fast_backw);
        void set_distill(bool distill);
        void set_intree(bool intree);
        void set_simp(bool simp);
        void set_bve_pre_simplify(bool bve_pre_simp);
        void set_unknown_sort(uint32_t unknown_sort);
        void set_incidence_count(uint32_t incidence_count);
        void set_or_gate_based(bool or_gate_based);
        void set_xor_gates_based(bool xor_gates_based);
        void set_probe_based(bool probe_based);
        void set_backward(bool backward);
        void set_backw_max_confl(uint32_t backw_max_confl);
        void set_gauss_jordan(bool gauss_jordan);
        void set_find_xors(bool find_xors);
        void set_ite_gate_based(bool ite_gate_based);
        void set_do_unate(bool do_unate);
        void set_irreg_gate_based(const bool irreg_gate_based);
        void set_gate_sort_special(bool gate_sort_special);
        //void set_polar_mode(CMSat::PolarityMode mode);
        void set_no_gates_below(double no_gates_below);
        void set_pred_forever_cutoff(int pred_forever_cutoff = -1);
        void set_every_pred_reduce(int every_pred_reduce = -1);
        void set_specified_order_fname(std::string specified_order_fname);
        void set_bce(const bool bce);
        void set_bve_during_elimtofile(const bool);
        void set_weighted(const bool);
        mpz_class get_multiplier_weight() const;

        //Get config
        bool get_do_unate() const;
        std::string get_specified_order_fname() const;
        double get_no_gates_below() const;
        bool get_simp() const;
        uint32_t get_verbosity() const;
        bool get_fast_backw() const;
        bool get_distill() const;
        bool get_intree() const;
        bool get_bve_pre_simplify() const;
        uint32_t get_incidence_count() const;
        uint32_t get_unknown_sort() const;
        bool get_or_gate_based() const;
        bool get_xor_gates_based() const;
        bool get_probe_based() const;
        bool get_backward() const;
        uint32_t get_backw_max_confl() const;
        bool get_gauss_jordan() const;
        bool get_find_xors() const;
        bool get_ite_gate_based() const;
        bool get_irreg_gate_based() const;
        bool get_gate_sort_special() const;
        bool get_bce() const;
        bool get_bve_during_elimtofile() const;
        bool definitely_satisfiable() const;
        const std::vector<uint32_t>& get_set_sampling_vars() const;
        bool get_weighted() const;

    private:
        ArjPrivateData* arjdata = nullptr;
    };
}
