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

#include "autarky.h"
#include <cryptominisat5/cryptominisat.h>
#include "time_mem.h"
#include "arjun.h"
#include "constants.h"

using namespace ArjunNS;
using namespace CMSat;
using std::vector;
using std::fixed;
using std::setprecision;


Autarky::Autarky(const Config& _conf) : conf(_conf) {}

// Following paper https://sun.iwu.edu/~mliffito/publications/sat08_liffiton_autarkies.pdf
// "Searching for Autarkies to Trim Unsatisfiable Clause Sets"
void Autarky::do_autarky(SimplifiedCNF& cnf) {
    const double start_time = cpuTime();
    s.set_verbosity(0);
    s.new_vars(cnf.nVars()); // orig set of vars

    vector<LitSub> lit_sub(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        LitSub ls;
        s.new_var();
        ls.pos = Lit(s.nVars()-1, false);
        s.new_var();
        ls.neg = Lit(s.nVars()-1, false);
        lit_sub[i] = ls;
    }

    vector<Lit> cl_sel(cnf.get_clauses().size());
    for(uint32_t i = 0; i < cnf.get_clauses().size(); i++) {
        s.new_var();
        cl_sel[i] = Lit(s.nVars()-1, false);
    }

    vector<Lit> var_sel(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        s.new_var();
        var_sel[i] = Lit(s.nVars()-1, false);
    }

    // Sampling variables should not be part of the autarky
    for(const auto& v: cnf.get_sampl_vars()) s.add_clause({~var_sel[v]});

    vector<Lit> cl;
    for(uint32_t i = 0; i < cnf.get_clauses().size(); i++) {
        const auto& ocl = cnf.get_clauses()[i];
        s.add_clause(ocl);

        //1. We replace every literal in the formula with a literal-substitute; x_j in the formula becomes x1_j , while ¬xj is replaced with x0_j .
        //2. Each clause Ci is augmented with a clause-selector yi to form a new clause C′ i = (yi → Ci) = (¬yi ∨ Ci)
        cl.clear();
        for(const auto& l: ocl) {
            if (l.sign()) cl.push_back(lit_sub[l.var()].neg);
            else cl.push_back(lit_sub[l.var()].pos);
        }
        cl.push_back(~cl_sel[i]);
        s.add_clause(cl);


        // We add clauses to require that a clause be enabled (y_i = TRUE) if
        // any one of its variables is enabled. Thus, for any x_j present in clause C_i,
        // we add a clause (x+_j → y_i) = (¬x+_j ∨ y_i).
        for(const auto& l: ocl) {
            s.add_clause({~var_sel[l.var()], cl_sel[i]});
        }
    }

    /*
    We create a variable-selector x+_j for every variable x_j .
    When x+_j is TRUE, x_j will be enabled, and it is disabled otherwise.
    For every variable xj , we add clauses to relate its variable-selector x+_j ,
    its two literal-substitutes x0_j and x1_j , and the value of the variable itself, x_j .
    In short, we want each literal- substitute to be TRUE when the variable is enabled (x+_j is TRUE)
    and x_j has the corresponding value. This leads to new clauses encoding the following:
    (x1 j = x+ j AND xj ) and (x0 j = x+ j AND ¬xj ).
    */

    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        // (x1 j = x+_j AND x_j)
        cl.clear();
        cl.push_back(lit_sub[i].pos);
        cl.push_back(~var_sel[i]);
        cl.push_back(~Lit(i, false));
        s.add_clause(cl);
        cl.clear();
        cl.push_back(~lit_sub[i].pos);
        cl.push_back(var_sel[i]);
        s.add_clause(cl);
        cl.clear();
        cl.push_back(~lit_sub[i].pos);
        cl.push_back(Lit(i, false));
        s.add_clause(cl);

        // (x0_j = x+_j AND ¬x_j)
        cl.clear();
        cl.push_back(lit_sub[i].neg);
        cl.push_back(~var_sel[i]);
        cl.push_back(~Lit(i, true));
        s.add_clause(cl);
        cl.clear();
        cl.push_back(~lit_sub[i].neg);
        cl.push_back(var_sel[i]);
        s.add_clause(cl);
        cl.clear();
        cl.push_back(~lit_sub[i].neg);
        cl.push_back(Lit(i, true));
        s.add_clause(cl);
    }

    // At least one variable must be enabled
    cl.clear();
    for(uint32_t i = 0; i < cnf.nVars(); i++) cl.push_back(var_sel[i]);
    s.add_clause(cl);

    uint32_t autaries = 0;
    uint32_t tot_autarkies = 0;
    bool found_autarky = true;
    while(found_autarky) {
        auto ret = s.solve();
        assert(ret != l_Undef);
        if (ret == l_False) break;

        assert(ret == l_True);
        autaries++;
        auto model = s.get_model();

        vector<uint32_t> autarky_vars;
        for(uint32_t i = 0; i < cnf.nVars(); i++) {
            const Lit l = var_sel[i];
            if (model[l.var()] == l_True)
                autarky_vars.push_back(i);
        }
        for(const auto& v: autarky_vars) {
            tot_autarkies++;
            verb_print(2, "Found autarky var: " << v+1 << " val: " << model[v]);
            const Lit l = Lit(v, model[v] == l_False);
            s.add_clause({l});
            cnf.add_clause({l});
        }
    }
    verb_print(1, "[arjun] Found " << autaries << " autarkies. Total autarky vars: " << tot_autarkies
        << " T: " << fixed << setprecision(2) << (cpuTime() - start_time));
}
