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

#include "minimize.h"
#include <cstdint>
#include <algorithm>
#include <vector>

#include "arjun.h"
#include "time_mem.h"
#include "constants.h"

using namespace ArjunInt;
using namespace CMSat;
using namespace ArjunNS;
using std::vector;
using std::string;
using std::cout;
using std::endl;

bool Minimize::simplify_bve_only() {
    //BVE ***ONLY***, don't eliminate the original variables
    solver->set_intree_probe(false);
    solver->set_distill(false);
    for(uint32_t var: sampling_vars) {
        dont_elim.push_back(Lit(var, false));
        dont_elim.push_back(Lit(var+orig_num_vars, false));
    }
    double simp_bve_time = cpuTime();
    verb_print(1, "[arjun] CMS::simplify() with *only* BVE...");

    if (conf.simp) {
        solver->set_bve(1);
        solver->set_verbosity(conf.verb);
        string str("occ-bve");
        if (solver->simplify(&dont_elim, &str) == l_False) return false;
        verb_print(1, "[arjun] CMS::simplify() with *only* BVE finished. T: "
            << cpuTime() - simp_bve_time);
    }
    solver->set_intree_probe(true);
    solver->set_distill(true);
    return true;
}

bool Minimize::run_gauss_jordan() {
    if (conf.gauss_jordan && conf.simp) {
        string str = "occ-xor";
        solver->set_bve(0);
        solver->set_allow_otf_gauss();
        if (solver->simplify(&dont_elim, &str) == l_False) {
            return false;
        }
    }
    return true;
}

bool Minimize::set_zero_weight_lits(const ArjunNS::SimplifiedCNF& cnf) const {
    if (!cnf.get_weighted()) return true;
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (cnf.get_lit_weight(Lit(i, false))->is_zero()) {
            solver->add_clause({Lit(i, true)});
        }
        if (cnf.get_lit_weight(Lit(i, true))->is_zero()) {
            solver->add_clause({Lit(i, false)});
        }
    }
    return solver->okay();
}

bool Minimize::preproc_and_duplicate(const ArjunNS::SimplifiedCNF& orig_cnf) {
    assert(!already_duplicated);
    if (conf.simp && !set_zero_weight_lits(orig_cnf)) return false;
    if (conf.simp && !simplify()) return false;
    get_incidence();
    duplicate_problem(orig_cnf);
    if (conf.simp && !simplify_bve_only()) return false;
    add_fixed_clauses();
    if (!run_gauss_jordan()) return false;

    //Seen needs re-init, because we got new variables
    seen.clear(); seen.resize(solver->nVars(), 0);

    solver->set_simplify(conf.simp);
    solver->set_intree_probe(conf.intree && conf.simp);
    solver->set_distill(conf.distill && conf.simp);
    solver->set_find_xors(conf.gauss_jordan && conf.simp);
    return true;
}

void Minimize::run_minimize(ArjunNS::SimplifiedCNF& cnf, bool all_indep) {
    double start_time = cpuTime();
    fill_solver(cnf);
    init();
    if (!preproc_and_duplicate(cnf)) goto end;
    backward_round();

    end:
    if (all_indep) {
        verb_print(2, "[arjun] All variables are independent, filling opt_sampl_vars to all vars.");
        cnf.set_all_opt_indep();
    }
    cnf.fix_weights(solver, sampling_vars, empty_sampling_vars);

    // Get back clauses
    const auto eq_lits = solver->get_all_binary_xors();
    for(auto p: eq_lits) {
        if (p.first.var() >= cnf.nVars() || p.second.var() >= cnf.nVars()) continue;
        vector<Lit> cl(2);
        cl[0] = p.first;
        cl[1] = ~p.second;
        cnf.add_clause(cl);
        verb_print(5, "[w-debug] adding cl: " << cl);
        cl[0] = ~cl[0];
        cl[1] = ~cl[1];
        cnf.add_clause(cl);
        verb_print(5, "[w-debug] adding cl: " << cl);
    }

    // Clean sampling sets from set vars
    auto zero_assigned = solver->get_zero_assigned_lits();
    std::erase_if(zero_assigned, [&](const Lit& l) { return l.var() >= cnf.nVars(); });
    for(const auto& l: zero_assigned) { cnf.add_clause({l}); }
    cnf.remove_sampling_vars(zero_assigned);

    for(const auto& v: cnf.get_sampl_vars())
        verb_print(5, "[w-debug] minim final sampl var: " << v+1);
    for(const auto& v: cnf.get_opt_sampl_vars())
        verb_print(5, "[w-debug] minim final opt sampl var: " << v+1);
    cnf.remove_equiv_weights();

    verb_print(5, "[w-debug] ----- minimize done.");

    verb_print(1, "[arjun] run_minimize finished "
        << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_time));
}


ArjunNS::Arjun::IndepInfo Minimize::run_minimize_info(ArjunNS::SimplifiedCNF& cnf, bool all_indep)
{
    run_minimize(cnf, all_indep);

    ArjunNS::Arjun::IndepInfo info;
    std::vector<std::pair<Lit, Lit>> raw_eq = solver->get_all_binary_xors();
    for (auto& p : raw_eq) {
        if (p.first.var()  >= cnf.nVars()) continue;
        if (p.second.var() >= cnf.nVars()) continue;
        info.eq_lits.push_back(p);
    }

    info.backbone = solver->get_zero_assigned_lits();
    auto pred = [&](const CMSat::Lit& l) { return l.var() >= cnf.nVars(); };
    std::erase_if(info.backbone, pred);

    info.free_vars = empty_sampling_vars;
    return info;
}
