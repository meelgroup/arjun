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

#ifndef ARJUN_COMMON_H
#define ARJUN_COMMON_H

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
#include <cryptominisat5/cryptominisat.h>
#include "cryptominisat5/dimacsparser.h"

#include "time_mem.h"
#include "arjun_config.h"

using namespace CMSat;
using std::cout;
using std::cerr;
using std::endl;
using std::map;
using std::set;
using std::string;
using std::vector;

struct Common
{
    Common() {
        sampling_set = &sampling_set_tmp1;
        other_sampling_set = &sampling_set_tmp2;
    }

    ~Common()
    {
        delete solver;
    }

    Config conf;
    CMSat::SATSolver* solver = NULL;
    vector<uint32_t> sampling_set_tmp1;
    vector<uint32_t> sampling_set_tmp2;
    vector<uint32_t>* sampling_set = NULL;


    vector<Lit> tmp;
    vector<char> seen;
    uint32_t orig_num_vars;
    uint32_t orig_samples_set_size;
    uint32_t total_eq_removed = 0;
    uint32_t total_set_removed = 0;
    uint32_t mult_or_invers_var;
    enum ModeType {one_mode, many_mode};

    //assert indic[var] to FASLE to force var==var+orig_num_vars
    vector<uint32_t> var_to_indic; //maps an ORIG VAR to an INDICATOR VAR
    vector<uint32_t> indic_to_var; //maps an INDICATOR VAR to ORIG VAR


    vector<uint32_t>* other_sampling_set = NULL;
    map<uint32_t, vector<uint32_t>> global_assump_to_testvars;
    vector<uint32_t> incidence;
    vector<double> vsids_scores;
    vector<Lit> dont_elim;
    vector<Lit> tmp_implied_by;
    string saved_fname; //This is a HACK and needs removal

    //setup, common functions
    void readInAFile(const string& filename, uint32_t var_offset, bool get_sampling_set);
    void update_sampling_set(
        const vector<uint32_t>& unknown,
        const vector<char>& unknown_set,
        const vector<uint32_t>& indep
    );
    void init_solver_setup(bool init_sampling, string fname);
    void print_indep_set();
    void add_fixed_clauses();
    void init_samping_set(bool recompute);


    //guess
    void run_guess();
    void fill_assumptions_inv(
        vector<Lit>& assumptions,
        const vector<uint32_t>& indep,
        const vector<uint32_t>& unknown,
        const vector<char>& unknown_set,
        uint32_t group,
        uint32_t offs,
        uint32_t index,
        vector<char>& dontremove_vars);
    void guess_round(
        uint32_t group,
        bool reverse = false,
        bool shuffle = false,
        int offset = 0);
    uint32_t guess_remove_and_update_ass(
        vector<Lit>& assumptions,
        vector<char>& unknown_set,
        vector<char>& dontremove_vars);

    //simp
    void simp();
    void remove_definable_by_gates();
    void remove_zero_assigned_literals();
    void remove_eq_literals();

    //forward
    void set_guess_forward_round(
        const vector<uint32_t>& indep,
        vector<uint32_t>& unknown,
        vector<char>& unknown_set,
        uint32_t group,
        uint32_t offs,
        vector<char>& guess_set);
    void fill_assumptions_forward(
        vector<Lit>& assumptions,
        const vector<uint32_t>& indep,
        vector<uint32_t>& unknown,
        uint32_t group,
        uint32_t offs,
        vector<char>& guess_set);
    bool forward_round(
        uint32_t max_iters = std::numeric_limits<uint32_t>::max(),
        uint32_t group = 1,
        bool reverse = false,
        bool shuffle = false,
        int offset = 0);

    //backward
    void fill_assumptions_backward(
        vector<Lit>& assumptions,
        vector<uint32_t>& unknown,
        const vector<char>& unknown_set,
        const vector<uint32_t>& indep);
    bool backward_round(
        uint32_t max_iters = std::numeric_limits<uint32_t>::max());

};

struct IncidenceSorter
{
    IncidenceSorter(const vector<uint32_t>& _inc) :
        inc(_inc)
    {}

    bool operator()(const uint32_t a, const uint32_t b) {
        return inc[a] > inc[b];
    }

    const vector<uint32_t>& inc;
};

struct VSIDSSorter
{
    VSIDSSorter(const vector<uint32_t>& _inc, const vector<double>& _vsids) :
        vsids(_vsids),
        inc(_inc)
    {}

    bool operator()(const uint32_t a, const uint32_t b) {
        if (inc[a] != inc[b]) {
            return inc[a] > inc[b];
        }
        return vsids[a] > vsids[b];
    }

    const vector<double>& vsids;
    const vector<uint32_t>& inc;
};

//ARJUN_COMMON_H
#endif
