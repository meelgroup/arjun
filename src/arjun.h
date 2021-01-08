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
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>

namespace ArjunNS {
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
        std::string get_version_info();
        std::string get_solver_version_info();
        //void set_projection_set(const std::vector<uint32_t>& vars);
        uint32_t nVars();
        void new_var();
        void add_xor_clause(const std::vector<uint32_t>& vars, bool rhs);
        void add_clause(const std::vector<CMSat::Lit>& lits);
        void set_seed(uint32_t seed);
        uint32_t set_starting_sampling_set(const std::vector<uint32_t>& vars);
        uint32_t start_with_clean_sampling_set();
        std::vector<uint32_t> get_indep_set();
        uint32_t get_orig_num_vars() const;
        void new_vars(uint32_t num);

        //Get clauses
        void start_getting_small_clauses(uint32_t max_len, uint32_t max_glue, bool red = true);
        bool get_next_small_clause(std::vector<CMSat::Lit>& ret); //returns FALSE if no more
        void end_getting_small_clauses();

        //Set config
        std::vector<std::vector<CMSat::Lit>> get_cnf();
        void set_verbosity(uint32_t verb);
        void set_fast_backw(bool fast_backw);
        void set_distill(bool distill);
        void set_intree(bool intree);
        void set_guess(bool guess);
        void set_pre_simplify(bool simp);
        void set_incidence_sort(uint32_t incidence_sort);
        void set_or_gate_based(bool or_gate_based);
        void set_xor_gates_based(bool xor_gates_based);
        void set_probe_based(bool probe_based);
        void set_polarmode(bool polarmode);
        void set_forward(bool forward);
        void set_backward(bool backward);
        void set_assign_fwd_val(bool assign_fwd_val);
        void set_backw_max_confl(uint32_t backw_max_confl);
        void set_solve_to_sat(bool solve_to_sat);
        void set_gauss_jordan(bool gauss_jordan);
        void set_regularly_simplify(bool reg_simp);
        void set_fwd_group(uint32_t forward_group);
        void set_find_xors(bool find_xors);
        void set_backbone_simpl(bool backbone_simpl);

        //Get config
        uint32_t get_verbosity() const;
        bool get_fast_backw() const;
        bool get_distill() const;
        bool get_intree() const;
        bool get_guess() const;
        bool get_pre_simplify() const;
        uint32_t get_incidence_sort() const;
        bool get_or_gate_based() const;
        bool get_xor_gates_based() const;
        bool get_probe_based() const;
        bool get_polarmode() const;
        bool get_forward() const;
        bool get_backward() const;
        bool get_assign_fwd_val() const;
        uint32_t get_backw_max_confl() const;
        bool get_solve_to_sat() const;
        bool get_gauss_jordan() const;
        bool get_regularly_simplify() const;
        uint32_t get_fwd_group() const;
        bool get_find_xors() const;
        bool get_backbone_simpl() const;
        std::vector<CMSat::Lit> get_zero_assigned_lits() const;
        std::vector<std::pair<CMSat::Lit, CMSat::Lit> > get_all_binary_xors() const;

    private:
        ArjPrivateData* arjdata = NULL;
    };
}

#endif
