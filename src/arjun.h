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

#ifndef ARJUN_H__
#define ARJUN_H__

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
        std::vector<uint32_t> sampling_vars;
        uint32_t nvars;
        uint32_t empty_occs;
        std::string sol_ext_data;

        void clear() {
            cnf.clear();
            sampling_vars.clear();
            nvars = 0;
            empty_occs = 0;
            sol_ext_data.clear();
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
        bool add_clause(const std::vector<CMSat::Lit>& lits);
        bool add_bnn_clause(
            const std::vector<CMSat::Lit>& lits,
            signed cutoff,
            CMSat::Lit out = CMSat::lit_Undef);
        void new_vars(uint32_t num);

        // Perform indep set calculation
        uint32_t set_starting_sampling_set(const std::vector<uint32_t>& vars);
        uint32_t start_with_clean_sampling_set();
        std::vector<uint32_t> get_indep_set();
        uint32_t get_orig_num_vars() const;
        void varreplace();
        std::vector<uint32_t> get_empty_occ_sampl_vars() const;

        //Get clauses
        void start_getting_small_clauses(uint32_t max_len, uint32_t max_glue, bool red = true);
        bool get_next_small_clause(std::vector<CMSat::Lit>& ret); //returns FALSE if no more
        void end_getting_small_clauses();
        const std::vector<CMSat::Lit> get_internal_cnf(uint32_t& num_cls) const;
        SimplifiedCNF get_fully_simplified_renumbered_cnf(
            const std::vector<uint32_t>& sampl_vars,
            const bool sparsify = true,
            const bool renumber = true,
            const bool need_sol_extend = false);
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
        void set_backbone_simpl(bool backbone_simpl);
        void set_ite_gate_based(bool ite_gate_based);
        void set_irreg_gate_based(const bool irreg_gate_based);
        void set_gate_sort_special(bool gate_sort_special);
        void set_backbone_simpl_max_confl(uint64_t backbone_simpl_max_confl);
        //void set_polar_mode(CMSat::PolarityMode mode);
        void set_no_gates_below(double no_gates_below);
        void set_pred_forever_cutoff(int pred_forever_cutoff = -1);
        void set_every_pred_reduce(int every_pred_reduce = -1);
        void set_empty_occs_based(const bool empty_occs_based);
        void set_specified_order_fname(std::string specified_order_fname);
        void set_bce(const bool bce);
        void set_bve_during_elimtofile(const bool);
        void set_backbone_simpl_cmsgen(const bool);

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
        bool get_backbone_simpl() const;
        bool get_ite_gate_based() const;
        bool get_irreg_gate_based() const;
        bool get_gate_sort_special() const;
        uint64_t get_backbone_simpl_max_confl() const;
        bool get_bce() const;
        bool get_bve_during_elimtofile() const;
        bool get_backbone_simpl_cmsgen() const;

    private:
        ArjPrivateData* arjdata = NULL;
    };
}

#endif
