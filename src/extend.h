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

#include <cstdint>
#include <sys/types.h>
#include <vector>
#include <map>
#include <set>
#include <memory>
#include <cryptominisat5/cryptominisat.h>
#include "config.h"
#include "arjun.h"
#include "interpolant.h"

using std::vector;
using std::map;
using std::set;
using namespace CMSat;
using namespace ArjunInt;
using namespace ArjunNS;

struct Extend {
    Extend(const Config& _conf) : interp(_conf), conf(_conf) {}
    ~Extend() = default;

    void add_all_indics_except(const set<uint32_t>& except);
    std::unique_ptr<SATSolver> solver;
    Interpolant interp;
    uint32_t orig_num_vars = std::numeric_limits<uint32_t>::max();

    //assert indic[var] to TRUE to force var==var+orig_num_vars
    vector<uint32_t> var_to_indic; //maps an ORIG VAR to an INDICATOR VAR
    vector<uint32_t> indic_to_var; //maps an INDICATOR VAR to ORIG VAR
    vector<Lit> dont_elim;
    vector<char> seen;

    template<class T>
    void fill_assumptions_extend(
        vector<Lit>& assumptions,
        const T& indep);
    void extend_round(SimplifiedCNF& cnf);

    void unsat_define(SimplifiedCNF& cnf);
    Config conf;

    void fill_solver(const SimplifiedCNF& cnf);
    void get_incidence();
    vector<uint32_t> incidence;
};
