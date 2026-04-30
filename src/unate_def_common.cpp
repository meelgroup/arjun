/*
 Arjun

 Copyright (c) 2026, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#include "unate_def_common.h"
#include "constants.h"
#include "time_mem.h"
#include <iomanip>
#include <vector>

using namespace ArjunNS;
using namespace CMSat;
using std::vector;
using std::setprecision;
using std::fixed;

namespace ArjunInt {

std::unique_ptr<ArjunInt::MetaSolver> setup_f_not_f(
        const SimplifiedCNF& cnf,
        const std::set<uint32_t>& input,
        const ArjunInt::Config& conf) {
    double my_time = cpuTime();

    vector<Lit> tmp;
    auto s = std::make_unique<ArjunInt::MetaSolver>();
    s->new_vars(cnf.nVars()*2); // one for orig, one for copy
    s->set_verbosity(0);

    vector<Lit> not_f_cls;
    for(const auto& cl: cnf.get_clauses()) {
        // F(x)
        s->add_clause(cl);

        // !F(y)
        s->new_var(); // new var for each clause
                      // z is true iff clause is TRUE
        const Lit z = Lit(s->nVars()-1, false);

        // (C shifted) V -z
        tmp.clear();
        for(const auto& l: cl) {
            if (input.count(l.var())) tmp.push_back(l);
            else tmp.push_back(Lit(l.var()+cnf.nVars(), l.sign()));
        }
        tmp.push_back(~z);
        s->add_clause(tmp);

        // (each -lit in C, shifted) V z
        for(const auto& l: cl) {
            tmp.clear();
            if (input.count(l.var())) tmp = {~l,  z};
            else tmp = {Lit(l.var()+cnf.nVars(), !l.sign()),  z};
            s->add_clause(tmp);
        }
        not_f_cls.push_back(~z);
    }

    // At least ONE clause must be FALSE
    s->add_clause(not_f_cls);

    verb_print(1, "[unate/def] Built up the F and ~F_x_y solver. T: "
            << fixed << setprecision(2) << (cpuTime() - my_time));
    return s;
}

}
