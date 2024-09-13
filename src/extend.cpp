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

#include <algorithm>
#include <cstdint>
#include <iomanip>
#include <map>

#include "src/arjun.h"
#include "src/time_mem.h"
#include "extend.h"
#include "constants.h"
#include "cryptominisat5/solvertypesmini.h"
#include "formula.h"

/* extern "C" { */
/* #include "mpicosat/mpicosat.h" */
/* } */
#include "cadical.hpp"

using namespace ArjunInt;
using namespace ArjunNS;
using namespace CaDiCaL;
using std::setw;

void Extend::add_all_indics_except(const set<uint32_t>& except) {
    assert(dont_elim.empty());
    assert(var_to_indic.empty());
    assert(indic_to_var.empty());

    var_to_indic.resize(orig_num_vars*2, var_Undef);

    vector<Lit> tmp;
    for(uint32_t var = 0; var < orig_num_vars; var++) {
        if (except.count(var)) continue;

        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        //torem_orig.push_back(Lit(this_indic, false));
        var_to_indic[var] = this_indic;
        var_to_indic[var+orig_num_vars] = this_indic;
        dont_elim.push_back(Lit(this_indic, false));
        indic_to_var.resize(this_indic+1, var_Undef);
        indic_to_var[this_indic] = var;

        // Below two mean var == (var+orig) in case indic is TRUE
        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,        true));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,        true));
        solver->add_clause(tmp);
    }
    seen.clear();
    seen.resize(indic_to_var.size()*2, 0);
}

void Extend::unsat_define(SimplifiedCNF& cnf) {
    double start_round_time = cpuTime();
    assert(cnf.sampl_vars.size() == cnf.opt_sampl_vars.size());
    assert(cnf.opt_sampl_vars_set);
    uint32_t start_size = cnf.opt_sampl_vars.size();
    fill_solver(cnf);

    solver->set_verbosity(0);
    solver->set_scc(1);

    // Fill no need
    set<uint32_t> no_need;
    // [ replaced, replaced_with ]
    /* auto ret1 = solver->get_all_binary_xors(); */
    /* for(const auto& p: ret1) no_need.insert(p.first.var()); */
    auto ret2 = solver->get_zero_assigned_lits();
    for(const auto& p: ret2) no_need.insert(p.var());
    for(const auto& v: cnf.opt_sampl_vars) no_need.insert(v);
    add_all_indics_except(no_need);

    // set up interpolant
    interp.fill_picolsat(solver, orig_num_vars);
    interp.fill_var_to_indic(var_to_indic);

    // Generate my_true_lit
    solver->new_var();
    assert(cnf.fh->my_true_lit == lit_Undef);
    cnf.fh->my_true_lit = Lit(solver->nVars()-1, false);

    //Initially, all of samping_set is unknown
    for(const auto& x: seen) assert(x == 0);
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (no_need.count(i)) continue;
        unknown.push_back(i);
    }

    sort_unknown(unknown, incidence);
    verb_print(1,"[arjun] Start unknown size: " << unknown.size());
    uint32_t sat = 0;
    set<uint32_t> unknown_set(unknown.begin(), unknown.end());

    vector<Lit> assumptions;
    uint32_t num_done = 0;
    uint32_t num_unsat = 0;
    while(!unknown.empty()) {
        if (num_done % 100 == 99) {
            verb_print(1, "[padoa] done: " << setw(4) << num_done
                    << " unsat: " << setw(4) << num_unsat
                    << " left: " << setw(4) << unknown.size()
                    << " T: " << std::setprecision(2) << std::fixed << setw(6)
                    << (cpuTime() - start_round_time)
                    << " var/s: " << setw(6) << (double)num_done/(cpuTime() - start_round_time));

        }
        uint32_t test_var = unknown.back();
        unknown.pop_back();
        if (unknown_set.count(test_var) == 0) continue;

        assert(test_var < orig_num_vars);
        verb_print(5, "Testing: " << test_var);

        //Assumption filling -- assume everything in indep is the same
        assert(test_var != var_Undef);

        assumptions.clear();
        uint32_t indic = var_to_indic[test_var];
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        //TODO: Actually, we should get conflict, that will make things easier
        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        ret = solver->solve(&assumptions);
        num_done++;

        if (ret == l_False) verb_print(5, "[arjun] extend solve(): False");
        else if (ret == l_True) {verb_print(5, "[arjun] extend solve(): True");sat++;}
        else if (ret == l_Undef) verb_print(5, "[arjun] extend solve(): Undef");

        if (ret == l_False) {
            num_unsat++;
            // Dependent fully on `indep`
            // TODO: run get_conflict and then we know which were
            // actually needed, so we can do an easier generation/check
            interp.generate_picosat(assumptions, test_var, cnf);
            vector<Lit> cl;
            Lit l(indic, false);
            cl.push_back(l);
            solver->add_clause(cl);
            interp.add_clause(cl);
            cnf.opt_sampl_vars.push_back(test_var);

        } else if (ret == l_True) {
            // Optimisation: if we see both true and false, then it cannot be independent
            for(uint32_t v = 0; v < orig_num_vars; v++) {
                if (!unknown_set.count(v)) continue;
                uint32_t other_v = v + orig_num_vars;
                if (solver->get_model()[other_v] != solver->get_model()[v]) {
                    verb_print(5,"TRUE erasing v: " << v + 1 << " because it's been seen both true&false");
                    unknown_set.erase(v);
                }
            }
            // Not fully dependent
        } else {
            // Unknown
        }
    }

    verb_print(1, "defined via Padoa: " << cnf.opt_sampl_vars.size()-start_size
            << " SAT: " << sat
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();
    cnf.last_formula_var = solver->nVars();
}

void Extend::extend_round(SimplifiedCNF& cnf) {
    assert(cnf.opt_sampl_vars_set = true);
    double start_round_time = cpuTime();
    const uint32_t orig_size = cnf.opt_sampl_vars.size();
    fill_solver(cnf);
    solver->set_verbosity(0);
    set<uint32_t> opt_sampl(cnf.opt_sampl_vars.begin(), cnf.opt_sampl_vars.end());

    /* auto xors = solver->get_recovered_xors(false); */
    /* for(const auto& g: xors) { */
    /*     int bad = 0; */
    /*     for(const auto& v: g.first) { */
    /*         if (!opt_sampl.count(v)) bad++; */
    /*         if (v >= orig_num_vars) bad = 100; */
    /*         if (bad > 1) break; */
    /*     } */
    /*     if (bad != 1) continue; */
    /*     for(const auto& v: g.first) { opt_sampl.insert(v); } */
    /* } */
    auto ites = solver->get_recovered_ite_gates();
    for(const auto& g: ites) {
        if (g.rhs.var() >= orig_num_vars) continue;
        bool ok = true;
        for(const auto& l: g.lhs) if (!opt_sampl.count(l.var())) {
            ok = false;
            break;
        }
        if (!ok) continue;
        opt_sampl.insert(g.rhs.var());
    }
    auto ors = solver->get_recovered_or_gates();
    for(const auto& g: ors) {
        if (g.rhs.var() >= orig_num_vars) continue;
        bool ok = true;
        for(const auto& l: g.get_lhs()) if (!opt_sampl.count(l.var())) {
            ok = false;
            break;
        }
        if (!ok) continue;
        opt_sampl.insert(g.rhs.var());
    }
    verb_print(1, "[extend-gates] Gates added to opt indep: " << opt_sampl.size()-orig_size << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));

    // Fill no need
    set<uint32_t> no_need;
    auto ret2 = solver->get_zero_assigned_lits();
    for(const auto& p: ret2) no_need.insert(p.var());
    add_all_indics_except(no_need);

    vector<Lit> cl;
    for(const auto& v: opt_sampl) {
        if (var_to_indic[v] == var_Undef) continue;
        cl.clear();
        cl.push_back(Lit(var_to_indic[v], false));
        solver->add_clause(cl);
    }

    //Initially, all of vars are unknown, except sampling set & replaced & set
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (no_need.count(i)) continue;
        if (opt_sampl.count(i)) continue;
        if (solver->removed_var(i)) continue;
        unknown.push_back(i);
    }

    sort_unknown(unknown, incidence);
    /* std::reverse(unknown.begin(), unknown.end()); */
    verb_print(1,"[arjun-extend] Start unknown size: " << unknown.size());

    vector<Lit> assumptions;
    uint32_t ret_undef = 0;
    /* conf.verb = 5; */
    set<uint32_t> unknown_set(unknown.begin(), unknown.end());
    uint32_t num_done = 0;
    while(!unknown.empty()) {
        uint32_t test_var = unknown.back();
        unknown.pop_back();
        if (unknown_set.count(test_var) == 0) continue;
        unknown_set.erase(test_var);
        num_done++;
        if (num_done == 300 && unknown_set.size() > 1000) {
            verb_print(1, "[arjun] extend: too many to do, after 100 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 2;
        }
        if (num_done == 500 && unknown_set.size() > 1000) {
            verb_print(1, "[arjun] extend: too many to do, after 1000 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 2;
        }
        if (num_done == 1000 && unknown_set.size() > 2000) {
            verb_print(1, "[arjun] extend: too many to do, after 2000 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 4;
        }
        if (num_done == 3000 && unknown_set.size() > 3000) {
            verb_print(1, "[arjun] extend: too many to do, after 3000 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 4;
        }
        if (num_done == 6000 && unknown_set.size() > 3000) {
            verb_print(1, "[arjun] extend: too many to do, after 6000 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 4;
        }
        if (num_done == 15000 && unknown_set.size() > 3000) {
            verb_print(1, "[arjun] extend: too many to do, after 9000 still lots left. BREAKING");
            break;
        }
        /* cout << "num_done: " << num_done << " unknown_set.size(): " << unknown_set.size() << " confl: " << (double)solver->get_sum_conflicts()/((double)num_done*conf.extend_max_confl) << endl; */

        assert(test_var < orig_num_vars);
        verb_print(5, "Testing: " << test_var);

        //Assumption filling
        assert(test_var != var_Undef);
        assumptions.clear();
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        solver->set_max_confl(conf.extend_max_confl);
        ret = solver->solve(&assumptions);
        if (ret == l_False) {
            verb_print(5, "[arjun] extend solve(): False");
        } else if (ret == l_True) {
            verb_print(5, "[arjun] extend solve(): True");
        } else if (ret == l_Undef) {
            verb_print(5, "[arjun] extend solve(): Undef");
            ret_undef++;
        }

        if (ret == l_Undef) {
            // Timed out, we'll treat is as unknown
            assert(test_var < orig_num_vars);
        } else if (ret == l_True) {
            for(uint32_t v = 0; v < orig_num_vars; v++) {
                if (!unknown_set.count(v)) continue;
                uint32_t other_v = v + orig_num_vars;
                if (solver->get_model()[other_v] != solver->get_model()[v]) {
                    verb_print(5,"TRUE erasing v: " << v + 1);
                    unknown_set.erase(v);
                }
            }
            // Not fully dependent
        } else if (ret == l_False) {
            // Dependent fully on `indep`
            opt_sampl.insert(test_var);
            cl.clear();
            cl.push_back(Lit(var_to_indic[test_var], false));
            solver->add_clause(cl);
        }
    }
    cnf.set_opt_sampl_vars(opt_sampl);

    verb_print(1, "[arjun-extend] Extend finished "
            << " orig size: " << orig_size
            << " final size: " << cnf.opt_sampl_vars.size()
            << " Undef: " << ret_undef
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 4) solver->print_stats();
}

void Extend::get_incidence() {
    assert(orig_num_vars == solver->nVars());

    incidence.clear();
    incidence.resize(orig_num_vars, 0);
    assert(solver->nVars() == orig_num_vars);
    vector<uint32_t> inc = solver->get_lit_incidence();
    assert(inc.size() == orig_num_vars*2);
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        Lit l = Lit(i, true);
        incidence[l.var()] = std::min(inc[l.toInt()],inc[(~l).toInt()]);
    }
}

void Extend::fill_solver(const SimplifiedCNF& cnf) {
    assert(solver == nullptr);
    solver = new SATSolver;
    solver->set_verbosity(conf.verb);
    solver->set_prefix("c o ");
    solver->set_find_xors(false);
    assert(solver->nVars() == 0); // Solver here is empty

    // Inject original CNF
    orig_num_vars = cnf.nvars;
    solver->new_vars(orig_num_vars);
    for(const auto& cl: cnf.clauses) solver->add_clause(cl);
    for(const auto& cl: cnf.red_clauses) solver->add_red_clause(cl);
    get_incidence();

    // Double vars
    solver->new_vars(orig_num_vars);
    seen.clear();
    seen.resize(solver->nVars()*2, 0);

    // We only need to double the non-opt-sampling vars
    for(const auto& v: cnf.opt_sampl_vars) seen[v] = 1;
    vector<Lit> cl2;
    for(const auto& cl: cnf.clauses) {
        cl2.clear();
        for (const auto& l: cl) {
            if (seen[l.var()]) cl2.push_back(l);
            else cl2.push_back(Lit(l.var()+orig_num_vars, l.sign()));
        }
        solver->add_clause(cl2);
    }
    for(const auto& v: cnf.opt_sampl_vars) seen[v] = 0;
}
