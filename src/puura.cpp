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

#include "cryptominisat5/cryptominisat.h"
#include <cstdint>
#include <vector>
#include <limits>
#include <iostream>
#include <iomanip>
#include <random>
#include "time_mem.h"
#include "puura.h"
#include "arjun.h"
#include "common.h"

using namespace ArjunNS;
using namespace CMSat;
using std::cout;
using std::endl;
using std::vector;


Puura::Puura(const Config& _conf) : conf(_conf) {}
Puura::~Puura() { delete solver; }

SATSolver* Puura::setup_f_not_f_indic()
{
    double my_time = cpuTime();
    orig_num_vars = solver->nVars();
    var_to_indic.clear();
    var_to_indic.resize(orig_num_vars, var_Undef);
    indic_to_var.clear();
    indic_to_var.resize(solver->nVars(), var_Undef);
    in_formula.clear();
    in_formula.resize(orig_num_vars, 0);

    vector<Lit> tmp;
    SATSolver* s = new SATSolver;
    s->set_verbosity(0);
    s->new_vars(orig_num_vars*2); // one for orig, one for copy
    s->set_bve(false);
    s->set_bva(false);
    s->set_no_simplify_at_startup();
    s->set_simplify(false);
    s->set_sls(false);
    s->set_find_xors(false);
    //Indicator variable is FALSE when they are NOT equal
    for(uint32_t var = 0; var < solver->nVars(); var++) {
        if (solver->removed_var(var)) continue;
        s->new_var();
        uint32_t this_indic = s->nVars()-1;
        var_to_indic[var] = this_indic;
        indic_to_var.resize(this_indic+1, var_Undef);
        indic_to_var[this_indic] = var;

        // Below two mean var == (var+orig) in case indic is TRUE
        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,      true));
        s->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,      true));
        s->add_clause(tmp);

        // Below two mean var == !(var+orig) in case indic is FALSE
        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,      false));
        s->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,      false));
        s->add_clause(tmp);
        /* cout << "indic: " << this_indic+1 << " vars: " << var+1 << " " << var+orig_num_vars+1 << endl; */
    }

    solver->start_getting_constraints(false);
    vector<Lit> zs;
    bool ret = true;
    vector<Lit> clause;
    bool is_xor, rhs;
    while(ret) {
        ret = solver->get_next_constraint(clause, is_xor, rhs);
        if (!ret) break;
        assert(!is_xor);
        assert(rhs);

        // set in_formula (but not in a unit)
        if (clause.size() > 1) for(const auto l: clause) in_formula[l.var()] = 1;

        // F(x)
        s->add_clause(clause);

        // !F(y)
        s->new_var(); // new var for each clause
        uint32_t zv = s->nVars()-1;
        Lit z = Lit(zv, false);

        // (C shifted) V -z
        tmp.clear();
        for(auto l: clause) tmp.push_back(Lit(l.var()+orig_num_vars, l.sign()));
        tmp.push_back(~z);
        s->add_clause(tmp);

        // (each -lit in C, shifted) V z
        for(auto l: clause) {
            tmp.clear();
            tmp = {Lit(l.var()+orig_num_vars, !l.sign()),  z};
            s->add_clause(tmp);
        }
        zs.push_back(~z);
    }
    solver->end_getting_constraints();

    // At least ONE clause must be FALSE
    s->add_clause(zs);
    s->simplify();
    cout << "c [puura] Built up the solver. T: " << (cpuTime() - my_time) << endl;
    return s;
}

void Puura::synthesis_unate(bool do_given) {
    double my_time = cpuTime();
    SATSolver* s = setup_f_not_f_indic();
    vector<Lit> assumps;
    vector<Lit> cl;
    uint32_t undefs = 0;
    uint32_t falses = 0;
    bool timeout = false;
    auto orig_units = solver->get_zero_assigned_lits().size();

    set<uint32_t> given_set;
    if (do_given) given_set = sampl_set;
    given_set.insert(var_Undef);
    for(uint32_t given: given_set) {
        if (given != var_Undef && !sampl_set.count(given)) continue;
        if (given != var_Undef && solver->removed_var(given)) continue;
        verb_print(1, "Will unate test " << orig_num_vars-sampl_set.size() << " vars given " << ((given == var_Undef) ? -1 : (int)given));
        for(uint32_t test = 0; test < orig_num_vars; test++) {
            if (test == given) continue;
            if (solver->removed_var(test)) continue;
            // we can only do this for non-sampling vars
            // for sampling vars, we need to have BOTH ways mapping
            if (sampl_set.count(test)) continue;
            if (s->get_sum_conflicts() > 50000) {timeout = true; break;}
            verb_print(3, "given: " << std::setw(3)
                << ((given == var_Undef) ? -1 : (given+1))
                << " test: " << (test+1)
                << " confl: " << s->get_sum_conflicts());

            assumps.clear();
            for(uint32_t i2 = 0; i2 < solver->nVars(); i2++) {
                if (i2 == given || i2 == test) continue;
                if (solver->removed_var(i2)) continue;
                assumps.push_back(Lit(var_to_indic[i2], false)); // they ARE equal
            }
            if (given != var_Undef) {
                assumps.push_back(Lit(given, false));
                assumps.push_back(Lit(given+orig_num_vars, false));
            }

            for(int flip = 0; flip < 2; flip++) {
                assumps.push_back(Lit(test, true ^ flip));
                assumps.push_back(Lit(test+orig_num_vars, false ^ flip));
                s->set_max_confl(1500);
                auto ret = s->solve(&assumps);
                verb_print(4, "Ret: " << ret << " flip: " << flip);
                if (ret == l_False) {
                    verb_print(2, "given: " << std::setw(3)
                        << ((given == var_Undef) ? -1 : (given+1))
                        << " test: " << std::setw(3)  << (test+1)
                        << " FALSE"
                        << " T: " << (cpuTime() - my_time));
                    falses++;

                    cl = {Lit(test, false ^ flip)};
                    if (given != var_Undef) cl.push_back(Lit(given, true));
                    s->add_clause(cl);
                    solver->add_clause(cl);
                    /* cout << "cl : " << cl << " 0" << endl; */
                    cl = {Lit(test+orig_num_vars, false ^ flip)};
                    if (given != var_Undef) cl.push_back(Lit(given+orig_num_vars, true));
                    s->add_clause(cl);
                    break;
                }
                if (ret == l_Undef) undefs++;
                assumps.pop_back();
                assumps.pop_back();
            }
        }
    }

    cout << "c [synthesis-unate]"
        << " set: " << (solver->get_zero_assigned_lits().size()-orig_units)
        << " orig units: " << orig_units
        << " falses: " << falses << " undefs: " << undefs
        << " T-out: " << (int)timeout
        << " T: " << (cpuTime()-my_time)
        << endl;

    delete s;
}

void Puura::conditional_dontcare()
{
    double my_time = cpuTime();
    SATSolver* s = setup_f_not_f_indic();
    vector<Lit> assumps;
    auto v = solver->get_verbosity();
    solver->set_verbosity(0);
    for(int given = -1; given < (int)orig_num_vars*2; given++) {
        Lit g;
        if (given == -1) g = lit_Undef;
        else g = Lit(given/2, given%2);
        if (given != -1 &&
                (!in_formula[g.var()] || !sampl_set.count(g.var()) ||
                 solver->removed_var(g.var()))) continue;

        // Let's check if there is a solution with this condition at all
        assumps.clear();
        if (given != -1) assumps = {g};
        const auto ret = solver->solve(&assumps);
        if (ret == l_False) continue;

        for(const auto& i: sampl_set) {
            if (!in_formula[i]) continue;
            if (solver->removed_var(i)) continue;
            if (i == g.var()) continue;

            // Checking now if var i is dontcare
            my_time = cpuTime();
            assumps.clear();
            if (given != -1) assumps.push_back(g);
            for(const auto& i2: sampl_set) {
                // They are all equal except for this
                if (i != i2) assumps.push_back(Lit(var_to_indic[i2], false));
            }
            // but this is NOT equal
            assumps.push_back(Lit(i, true));
            assumps.push_back(Lit(i+orig_num_vars, false));
            s->set_max_confl(1000);
            auto sret = s->solve(&assumps);
            if (sret == l_False) {
                verb_print(2, "Assuming " << g
                    << " then var " << (i+1) << " is dontcare?"
                    << "Ret: " << sret << " T: " << std::fixed << std::setprecision(2) << (cpuTime() - my_time)
                    << " -- inside F: " << (int)in_formula[i]);
                vector<Lit> cl;
                cl.push_back(~g);
                cl.push_back(Lit(i+1, false));
                solver->add_clause(cl);
            }
            s->set_verbosity(0);
        }
    }
    solver->set_verbosity(v);

    delete s;
}

void Puura::get_simplified_cnf(SimplifiedCNF& scnf, const bool renumber)
{
    assert(scnf.cnf.empty());
    vector<Lit> clause;
    bool is_xor, rhs;
    solver->start_getting_constraints(false, renumber);
    if (renumber) scnf.sampling_vars = solver->translate_sampl_set(scnf.sampling_vars);
    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        scnf.cnf.push_back(clause);
    }
    solver->end_getting_constraints();

    solver->start_getting_constraints(true, renumber);
    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        scnf.red_cnf.push_back(clause);
    }
    solver->end_getting_constraints();

    scnf.nvars = renumber ? solver->simplified_nvars() :  solver->nVars();
    std::sort(scnf.sampling_vars.begin(), scnf.sampling_vars.end());
}

void Puura::fill_solver(Arjun* arjun)
{
    assert(solver == nullptr);
    solver = new CMSat::SATSolver;
    solver->set_verbosity(conf.verb);
    solver->set_find_xors(false);

    assert(solver->nVars() == 0); // Solver here is empty
    solver->new_vars(arjun->get_orig_num_vars());

    // Inject original CNF
    const auto cnf = arjun->get_orig_cnf();
    vector<Lit> cl;
    for(const auto& l: cnf) {
        if (l != lit_Undef) {
            assert(l.var() < arjun->get_orig_num_vars());
            cl.push_back(l);
            continue;
        }
        solver->add_clause(cl);
        cl.clear();
    }

    // inject set vars
    const auto lits =  arjun->get_zero_assigned_lits();
    for(const auto& l: lits) {
        assert(l.var() < arjun->get_orig_num_vars());
        cl.clear();
        cl.push_back(l);
        solver->add_clause(cl);
    }

    // inject bin-xor clauses
    auto bin_xors = arjun->get_all_binary_xors();
    vector<uint32_t> dummy_v;
    for(const auto& bx: bin_xors) {
        dummy_v.clear();
        dummy_v.push_back(bx.first.var());
        dummy_v.push_back(bx.second.var());
        solver->add_xor_clause(dummy_v, bx.first.sign()^bx.second.sign());
    }
}

bool replace(std::string& str, const std::string& from, const std::string& to) {
    size_t start_pos = str.find(from);
    if(start_pos == std::string::npos)
        return false;
    str.replace(start_pos, from.length(), to);
    return true;
}

SimplifiedCNF Puura::get_fully_simplified_renumbered_cnf(
    Arjun* arjun,
    const vector<uint32_t>& sampl_vars,
    const SimpConf simp_conf,
    const bool renumber,
    const bool need_sol_extend)
{
    fill_solver(arjun);
    solver->set_renumber(renumber);
    solver->set_scc(renumber);
    setup_sampl_vars_dontelim(sampl_vars);

    //Below works VERY WELL for: ProcessBean, pollard, track1_116.mcc2020_cnf
    //   and blasted_TR_b14_even3_linear.cnf.gz.no_w.cnf
    //with CMS ef6ea7e87e00bde50c0cce0c1e13a012191c4e1c and Arjun 5f2dfe814e07ee6ee0dde65b1350b5c343209ed0
    solver->set_varelim_check_resolvent_subs(false);
    solver->set_max_red_linkin_size(0);
    solver->set_timeout_all_calls(100);
    solver->set_weaken_time_limitM(2000);
    solver->set_oracle_get_learnts(simp_conf.oracle_vivify_get_learnts);
    solver->set_oracle_removed_is_learnt(1);
    if (!simp_conf.appmc) {
        solver->set_min_bva_gain(simp_conf.bve_grow_iter1);
        solver->set_occ_based_lit_rem_time_limitM(500);
        solver->set_bve_too_large_resolvent(-1);
    } else {
        solver->set_occ_based_lit_rem_time_limitM(0);
    }
    solver->set_bve(conf.bve_during_elimtofile);

    if (conf.do_unate) synthesis_unate(false);
    // occ-cl-rem-with-orgates not used -- should test and add, probably to 2nd iter
    // eqlit-find from oracle not used (too slow?)
    string str("must-scc-vrepl, full-probe, backbone, sub-cls-with-bin, sub-impl, distill-cls-onlyrem, occ-resolv-subs, occ-backw-sub, occ-rem-with-orgates, occ-bve, occ-ternary-res, intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, clean-cls, distill-cls, distill-bins, ");
    if (simp_conf.appmc) str = string("must-scc-vrepl, full-probe, backbone, sub-cls-with-bin, sub-impl, distill-cls-onlyrem, occ-resolv-subs, occ-backw-sub, occ-bve, intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, clean-cls, distill-cls, distill-bins, ");
    for (int i = 0; i < simp_conf.iter1; i++) solver->simplify(&dont_elim, &str);

    // Now doing Oracle
    /* conditional_dontcare(); */
    string str2;
    if (conf.bce) {str2 = "occ-bce"; solver->simplify(&dont_elim, &str2);}
    if (simp_conf.oracle_vivify && simp_conf.oracle_sparsify) str2 = "oracle-vivif-sparsify";
    else if (simp_conf.oracle_vivify) str2 = "oracle-vivif";
    else if (simp_conf.oracle_sparsify) str2 = "oracle-sparsify";
    else str2 = "";
    solver->simplify(&dont_elim, &str2);

    // Now more expensive BVE, also RED linked in to occur
    if (!simp_conf.appmc) {
        solver->set_min_bva_gain(simp_conf.bve_grow_iter2);
        solver->set_varelim_check_resolvent_subs(true);
    }
    solver->set_max_red_linkin_size(20);
    for (int i = 0; i < simp_conf.iter2; i++) solver->simplify(&dont_elim, &str);

    // Final cleanup -- renumbering, disconnected component removing, etc.
    str.clear();
    if (arjun->definitely_satisfiable()) { str += string("occ-rem-unconn-assumps, "); }
    str += string(", must-scc-vrepl, must-renumber,");
    if (conf.bce) str += "occ-bce,";
    solver->simplify(&dont_elim, &str);

    vector<uint32_t> empty_occs;
    SimplifiedCNF cnf;
    cnf.sampling_vars = sampl_vars;

    if (conf.empty_occs_based) {
        solver->clean_sampl_and_get_empties(cnf.sampling_vars, empty_occs);
        dont_elim.clear();
        for(uint32_t v: cnf.sampling_vars) dont_elim.push_back(Lit(v, false));
        str = "occ-bve-empty, must-renumber";
        solver->simplify(&dont_elim, &str);
    }
    get_simplified_cnf(cnf, renumber);

    cnf.empty_occs = empty_occs.size();

    if (need_sol_extend) {
#ifdef ARJUN_SERIALIZE
        cnf.sol_ext_data = solver.serialize_solution_reconstruction_data();
#else
        cout << "ERROR: Both Arjun and CMS needs to be compiled with 'ARJUN_SERIALIZE' to extend solutions" << endl;
        exit(-1);
#endif
    }

    return cnf;
}

void Puura::setup_sampl_vars_dontelim(const vector<uint32_t>& sampl_vars)
{
    assert(dont_elim.empty());
    for(uint32_t v: sampl_vars) dont_elim.push_back(Lit(v, false));
    sampl_set.clear();
    for(uint32_t v: sampl_vars) sampl_set.insert(v);
}

SimplifiedCNF Puura::only_synthesis_unate(Arjun* arjun, const vector<uint32_t>& sampl_vars)
{
    fill_solver(arjun);
    setup_sampl_vars_dontelim(sampl_vars);
    synthesis_unate();

    SimplifiedCNF cnf;
    cnf.sampling_vars = sampl_vars;
    get_simplified_cnf(cnf, false);
    return cnf;
}


SimplifiedCNF Puura::only_conditional_dontcare(Arjun* arjun, const vector<uint32_t>& sampl_vars)
{
    fill_solver(arjun);
    setup_sampl_vars_dontelim(sampl_vars);

    conditional_dontcare();
    std::string s = "clean-cls";
    solver->simplify(&dont_elim, &s);

    SimplifiedCNF cnf;
    cnf.sampling_vars = sampl_vars;
    get_simplified_cnf(cnf, false);
    return cnf;
}

SimplifiedCNF Puura::only_backbone(Arjun* arjun, const vector<uint32_t>& sampl_vars)
{
    fill_solver(arjun);
    setup_sampl_vars_dontelim(sampl_vars);

    std::string s = "backbone";
    solver->simplify(&dont_elim, &s);

    SimplifiedCNF cnf;
    cnf.sampling_vars = sampl_vars;
    get_simplified_cnf(cnf, false);
    return cnf;
}
