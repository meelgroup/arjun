
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

#include "src/config.h"
#include <cstdint>
#include <vector>
#include <set>
#include "config.h"
#include "arjun.h"

using namespace CMSat;
using namespace ArjunInt;
using namespace ArjunNS;
using std::vector;
using std::set;

class Sampo {
public:
    Sampo(const Config& _conf, Arjun* _arjun);
    ~Sampo();
    SimplifiedCNF get_fully_simplified_renumbered_cnf(
        const vector<uint32_t>& sampl_vars, //contains empty_vars!
        const bool sparsify,
        const bool renumber,
        const bool need_sol_extend);

private:
    SATSolver* solver = nullptr;
    SATSolver* setup_f_not_f_indic();
    void conditional_flippable();
    void synthesis_unit();

    bool backbone_simpl();
    void fill_solver();
    void get_simplified_cnf(
        vector<uint32_t>& sampl_vars, const bool renumber,
        vector<vector<Lit>>& cnf, uint32_t& nvars);

    Arjun* arjun;
    const Config& conf;

    // For the unit/flippable
    //
    vector<uint32_t> var_to_indic;
    vector<uint32_t> indic_to_var;
    uint32_t orig_num_vars;
    vector<uint8_t> in_formula;
    set<uint32_t> sampl_set;
};
