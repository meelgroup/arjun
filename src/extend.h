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
#include <vector>
#include <set>
#include <memory>
#include <cryptominisat5/cryptominisat.h>
#include "config.h"
#include "arjun.h"

class Extend {
public:
    Extend(const ArjunInt::Config& _conf) : conf(_conf) {}
    void extend_round(ArjunNS::SimplifiedCNF& cnf);
    void extend_synth(ArjunNS::SimplifiedCNF& cnf);
    bool check_extend(const ArjunNS::SimplifiedCNF& cnf);

private:
    void fill_solver(const ArjunNS::SimplifiedCNF& cnf);
    void get_incidence();
    std::vector<uint32_t> incidence;

    template<class T>
    void fill_assumptions_extend(
        std::vector<CMSat::Lit>& assumptions,
        const T& indep);

    ArjunInt::Config conf;

    //assert indic[var] to TRUE to force var==var+orig_num_vars
    std::vector<uint32_t> var_to_indic; //maps an ORIG VAR to an INDICATOR VAR
    std::vector<uint32_t> indic_to_var; //maps an INDICATOR VAR to ORIG VAR
    std::vector<CMSat::Lit> dont_elim;
    std::vector<char> seen;

    void add_all_indics_except(const std::set<uint32_t>& except);
    std::unique_ptr<CMSat::SATSolver> solver;
    uint32_t orig_num_vars = std::numeric_limits<uint32_t>::max();
};
