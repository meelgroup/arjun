/*
 This file is part of Arjun

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

#include "arjun.h"

#include <vector>
#include <iostream>
#include <limits>
#include <set>

using std::vector;
using std::cout;
using std::endl;
using std::numeric_limits;
using namespace CMSat;
using namespace ArjunNS;

int main()
{
    const uint32_t num_vars = 100;

    SimplifiedCNF cnf;
    cnf.new_vars(num_vars);

    vector<Lit> clause;

    //TODO add clauses here
    //1 2 0
    clause.clear();
    clause.push_back(CMSat::Lit(0, false));
    clause.push_back(CMSat::Lit(1, false));
    cnf.add_clause(clause);

    //1 2 10 0
    clause.clear();
    clause.push_back(CMSat::Lit(0, false));
    clause.push_back(CMSat::Lit(1, false));
    clause.push_back(CMSat::Lit(9, false));
    cnf.add_clause(clause);

    //3 -4 0
    clause.clear();
    clause.push_back(CMSat::Lit(2, false));
    clause.push_back(CMSat::Lit(3, true));
    cnf.add_clause(clause);

    //3 -4  5 0
    clause.clear();
    clause.push_back(CMSat::Lit(2, false));
    clause.push_back(CMSat::Lit(3, true));
    clause.push_back(CMSat::Lit(4, true));
    cnf.add_clause(clause);

    vector<uint32_t> proj;
    for(uint32_t i = 0; i < 100; i++) proj.push_back(i);
    cnf.set_sampl_vars(proj);

    Arjun arjun;
    arjun.set_verb(0);
    arjun.only_run_backwards(cnf);
    std::set<uint32_t> dont_elim (proj.begin(), proj.end());

    SimpConf simp_conf;
    auto cnf2 = arjun.only_get_simplified_cnf(cnf, simp_conf);

    cout << "p cnf " << cnf2.nvars << " " << cnf2.clauses.size() << endl;
    for(const auto& cl: cnf2.clauses) {
        for(const auto& l: cl) {
            int lit = l.var()+1;
            if (l.sign()) lit *= -1;
            cout << lit << " ";
        }
        cout << "0" << endl;
    }
    for(const auto& cl: cnf2.clauses) {
        cout << "c red ";
        for(const auto& l: cl) {
            int lit = l.var()+1;
            if (l.sign()) lit *= -1;
            cout << lit << " ";
        }
        cout << "0" << endl;
    }
    return 0;
}
