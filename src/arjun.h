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
#include <tuple>
#ifdef CMS_LOCAL_BUILD
#include "cryptominisat.h"
#else
#include <cryptominisat5/cryptominisat.h>
#endif

namespace ArjunNS {
    struct SimplifiedCNF {
        std::vector<std::vector<CMSat::Lit>> cnf;
        std::vector<std::vector<CMSat::Lit>> red_cnf;
        std::vector<uint32_t> sampling_vars;
        uint32_t nvars = 0;
        uint32_t empty_occs = 0;
        std::string sol_ext_data;

        void clear() {
            cnf.clear();
            sampling_vars.clear();
            nvars = 0;
            empty_occs = 0;
            sol_ext_data.clear();
        }

        std::vector<CMSat::Lit>& map_cl(std::vector<CMSat::Lit>& cl, std::vector<uint32_t> var_map) {
            for(auto& l: cl) {
                l = CMSat::Lit(var_map[l.var()], l.sign());
            }
            return cl;
        }

        void renumber_sampling_for_ganak()
        {
            constexpr uint32_t m = std::numeric_limits<uint32_t>::max();
            std::vector<uint32_t> map_here_to_there(nvars, m);
            uint32_t i = 0;
            std::vector<uint32_t> translated_sampl_vars;
            for(const auto& v: sampling_vars) {
                assert(v < nvars);
                map_here_to_there[v] = i;
                translated_sampl_vars.push_back(i);
                i++;
            }
            sampling_vars = translated_sampl_vars;
            for(uint32_t x = 0; x < nvars; x++) {
                if (map_here_to_there[x] == m) {
                    map_here_to_there[x] = i;
                    i++;
                }
            }
            assert(i == nvars);
            for(auto& cl: cnf) map_cl(cl, map_here_to_there);
            for(auto& cl: red_cnf) map_cl(cl, map_here_to_there);
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
        static std::string get_compilation_env();
        static std::string get_solver_version_info();

        // Adding CNF
        uint32_t nVars();
        void new_var();
        bool add_xor_clause(const std::vector<uint32_t>& vars, bool rhs);
        bool add_clause(const std::vector<CMSat::Lit>& lits, bool red = false);
        bool add_bnn_clause(
            const std::vector<CMSat::Lit>& lits,
            signed cutoff,
            CMSat::Lit out = CMSat::lit_Undef);
        void new_vars(uint32_t num);

        // Perform indep set calculation
        uint32_t set_starting_sampling_set(const std::vector<uint32_t>& vars);
        uint32_t start_with_clean_sampling_set();
        std::vector<uint32_t> get_indep_set();
        std::vector<uint32_t> extend_indep_set();
        uint32_t get_orig_num_vars() const;
        std::vector<uint32_t> get_empty_occsampl_vars() const;

        //Get clauses
        void start_getting_small_clauses(uint32_t max_len, uint32_t max_glue, bool red = true);
        bool get_next_small_clause(std::vector<CMSat::Lit>& ret); //returns FALSE if no more
        void end_getting_small_clauses();
        const std::vector<CMSat::Lit> get_internal_cnf(uint32_t& num_cls) const;
        SimplifiedCNF get_fully_simplified_renumbered_cnf(
            const std::vector<uint32_t>& sampl_vars,
            const bool oracle_vivify,
            const bool oracle_sparsify,
            const int iters1,
            const int iters2,
            const bool renumber,
            const bool need_sol_extend);
        SimplifiedCNF only_synthesis_unate(const std::vector<uint32_t>& sampl_vars);
        SimplifiedCNF only_backbone(const std::vector<uint32_t>& sampl_vars);
        const std::vector<CMSat::BNN*>& get_bnns() const;
        std::vector<CMSat::Lit> get_zero_assigned_lits() const;
        std::vector<std::pair<CMSat::Lit, CMSat::Lit> > get_all_binary_xors() const;
        const std::vector<CMSat::Lit>& get_orig_cnf();

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
        void set_irreg_gate_based(const bool irreg_gate_based);
        void set_gate_sort_special(bool gate_sort_special);
        //void set_polar_mode(CMSat::PolarityMode mode);
        void set_no_gates_below(double no_gates_below);
        void set_pred_forever_cutoff(int pred_forever_cutoff = -1);
        void set_every_pred_reduce(int every_pred_reduce = -1);
        void set_empty_occs_based(const bool empty_occs_based);
        void set_specified_order_fname(std::string specified_order_fname);
        void set_bce(const bool bce);
        void set_bve_during_elimtofile(const bool);

        //Get config
        bool get_empty_occs_based() const;
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
        std::vector<uint32_t> get_empty_occ_sampl_vars() const;

    private:
        ArjPrivateData* arjdata = NULL;
    };
}
