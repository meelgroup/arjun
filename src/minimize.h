/*
 Arjun

 Copyright (c) 2019, Mate Soos and Kuldeep S. Meel. All rights reserved.

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
#include <vector>
#include <iostream>
#include <iomanip>
#include <random>
#include <algorithm>
#include <map>
#include <set>
#include <vector>
#include <sstream>
#include <string>
#ifdef CMS_LOCAL_BUILD
#include "cryptominisat.h"
#else
#include <cryptominisat5/cryptominisat.h>
#endif

#include "config.h"

using namespace CMSat;
using std::cout;
using std::endl;
using std::map;
using std::set;
using std::string;
using std::vector;

namespace ArjunInt {

struct Minimize
{
    Minimize(const Config& _conf) : conf(_conf) {
        set_up_solver();
    }
    ~Minimize() { delete solver; }

    void run_minimize_indep(ArjunNS::SimplifiedCNF& cnf);

    const Config conf;
    CMSat::SATSolver* solver = nullptr;
    bool already_duplicated = false;
    vector<uint32_t> sampling_vars;
    vector<uint32_t> empty_sampling_vars;

    vector<char> seen;
    uint32_t orig_num_vars = std::numeric_limits<uint32_t>::max();

    //assert indic[var] to TRUE to force var==var+orig_num_vars
    vector<uint32_t> var_to_indic; //maps an ORIG VAR to an INDICATOR VAR
    vector<uint32_t> indic_to_var; //maps an INDICATOR VAR to ORIG VAR

    //Incidence as counted by clauses it's appeared together with other variables
    vector<uint32_t> incidence;

    vector<Lit> dont_elim;

    void init();
    void update_sampling_set(
        const vector<uint32_t>& unknown,
        const vector<char>& unknown_set,
        const vector<uint32_t>& indep
    );
    bool preproc_and_duplicate(const ArjunNS::SimplifiedCNF& orig_cnf);
    void add_fixed_clauses();
    void print_orig_sampling_set();
    void start_with_clean_sampl_vars();
    void duplicate_problem(const ArjunNS::SimplifiedCNF& orig_cnf);
    void get_incidence();
    void set_up_solver();
    ArjunNS::SimplifiedCNF get_init_cnf();

    //simp
    vector<uint32_t> toClear;
    bool simplify();
    bool remove_definable_by_gates();
    void remove_definable_by_irreg_gates();
    void remove_zero_assigned_literals(bool print = true);
    void remove_eq_literals(bool print = true);
    void get_empty_occs();
    bool probe_all();
    void empty_out_indep_set_if_unsat();
    bool simplify_bve_only();
    bool run_gauss_jordan();
    void check_no_duplicate_in_sampling_set();
    void order_sampl_set_for_simp();

    //backward
    void fill_assumptions_backward(
        vector<Lit>& assumptions,
        vector<uint32_t>& unknown,
        const vector<char>& unknown_set,
        const vector<uint32_t>& indep);
    void backward_round();
    void order_by_file(const string& fname, vector<uint32_t>& unknown);
    void print_sorted_unknown(const vector<uint32_t>& unknown) const;
};

}
