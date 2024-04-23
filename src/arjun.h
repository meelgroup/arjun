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
        std::vector<std::vector<CMSat::Lit>> clauses;
        std::vector<std::vector<CMSat::Lit>> red_clauses;
        std::vector<uint32_t> sampl_vars;
        std::vector<uint32_t> opt_sampl_vars;
        uint32_t nvars = 0;
        mpz_class multiplier_weight = 1;
        bool weighted = false;

        uint32_t nVars() const { return nvars; }
        uint32_t new_vars(uint32_t vars) { nvars+=vars; return nvars; }
        uint32_t new_var() { nvars++; return nvars;}

        void start_with_clean_sampl_vars() {
            assert(sampl_vars.empty());
            assert(opt_sampl_vars.empty());
            for(uint32_t i = 0; i < nvars; i++) sampl_vars.push_back(i);
            for(uint32_t i = 0; i < nvars; i++) opt_sampl_vars.push_back(i);
        }
        void add_xor_clause(std::vector<uint32_t>&, bool) { exit(-1); }
        void add_xor_clause(std::vector<CMSat::Lit>&, bool) { exit(-1); }
        void add_clause(std::vector<CMSat::Lit>& cl) { clauses.push_back(cl); }
        void add_red_clause(std::vector<CMSat::Lit>& cl) { red_clauses.push_back(cl); }
        bool get_sampl_vars_set() const { return sampl_vars_set; }
        bool sampl_vars_set = false;
        bool opt_sampl_vars_given = false;
        void set_sampl_vars(std::vector<uint32_t>& vars)
            { sampl_vars_set = true; sampl_vars = vars; }
        const auto& get_sampl_vars() const { return sampl_vars; }
        void set_opt_sampl_vars(std::vector<uint32_t>& vars)
            { opt_sampl_vars_given = true; opt_sampl_vars = vars; }

        void set_multiplier_weight(mpz_class m) { multiplier_weight = m; }
        auto get_multiplier_weight() const { return multiplier_weight; }
        void set_lit_weight(CMSat::Lit /*lit*/, double /*weight*/) {
            assert(false && "Not yet supported"); exit(-1); }
        void set_weighted(bool _weighted) { weighted = _weighted; }
        bool get_weighted() const { return weighted; }

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
            for(auto& cl: clauses) map_cl(cl, map_here_to_there);
            for(auto& cl: red_clauses) map_cl(cl, map_here_to_there);
            assert(!weighted);
#ifdef WEIGHTED
            if (weighted) {
                std::map<CMSat::Lit, double> new_weights;
                for(auto& w: weights)
                    new_weights[CMSat::Lit(
                             map_here_to_there[w.first.var()], w.first.sign())] = w.second;
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

        // Perform indep set calculation
        void only_run_minimize_indep(SimplifiedCNF& cnf);
        void only_extend_sampl_vars(SimplifiedCNF& cnf);
        void only_unsat_define(SimplifiedCNF& cnf);
        void only_unate(SimplifiedCNF& cnf);

        void elim_to_file(SimplifiedCNF& cnf, bool indep_support_given,
            bool do_extend_indep, bool do_bce,
            bool do_unate, const SimpConf& simp_conf,
            int64_t sbva_steps, uint32_t sbva_cls_cutoff, uint32_t sbva_lits_cutoff, int sbva_tiebreak);
        SimplifiedCNF only_get_simplified_cnf(const SimplifiedCNF& cnf, const SimpConf& simp_conf);
        void only_bce(SimplifiedCNF& cnf);
        void only_reverse_bce(SimplifiedCNF& cnf);
        void only_backbone(SimplifiedCNF& cnf);
        const SimplifiedCNF& get_orig_cnf() const;
        void only_run_sbva(SimplifiedCNF& orig,
            int64_t sbva_steps = 200, uint32_t sbva_cls_cutoff = 2,
            uint32_t sbva_lits_cutoff = 2, int sbva_tiebreak = 1);

        //Set config
        void set_verb(uint32_t verb);
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
        void set_specified_order_fname(std::string specified_order_fname);
        void set_bce(const bool bce);
        void set_weighted(const bool);

        //Get config
        uint32_t get_verb() const;
        bool get_do_unate() const;
        std::string get_specified_order_fname() const;
        double get_no_gates_below() const;
        bool get_simp() const;
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

    private:
        ArjPrivateData* arjdata = nullptr;
    };
}
