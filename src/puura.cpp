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

#include <cstdint>
#include <vector>
#include <limits>
#include <iostream>
#include <iomanip>
#include <random>

#ifdef CMS_LOCAL_BUILD
#include "sbva.h"
#include "cryptominisat.h"
#else
#include <sbva/sbva.h>
#include "cryptominisat5/cryptominisat.h"
#endif
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

void Puura::get_simplified_cnf(SimplifiedCNF& scnf,
        const vector<uint32_t>& sampl_vars,
        const vector<uint32_t>& set_sampl_vars,
        const vector<uint32_t>& empty_sampl_vars,
        const vector<uint32_t>& orig_sampl_vars) {
    assert(scnf.cnf.empty());

    vector<Lit> clause;
    bool is_xor, rhs;


    scnf.sampl_vars = sampl_vars;
    scnf.weighted = solver->get_weighted();

    solver->start_getting_constraints(false, true);

    // Weights/empties/etc
    const auto tmp = solver->translate_sampl_set(empty_sampl_vars);
    mpz_class dummy(2);
    mpz_pow_ui(dummy.get_mpz_t(), dummy.get_mpz_t(), tmp.size());
    scnf.multiplier_weight = solver->get_multiplier_weight()*dummy;
#ifdef WEIGHTED
    if (scnf.weighted) {
        solver->get_weights(scnf.weights, sampl_vars, orig_sampl_vars);
        // todo
    }
#endif

    scnf.sampl_vars = solver->translate_sampl_set(scnf.sampl_vars);
    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        scnf.cnf.push_back(clause);
    }
    solver->end_getting_constraints();

    solver->start_getting_constraints(true, true);
    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        scnf.red_cnf.push_back(clause);
    }
    solver->end_getting_constraints();

    scnf.nvars = solver->simplified_nvars();
    std::sort(scnf.sampl_vars.begin(), scnf.sampl_vars.end());
}

void Puura::fill_solver(Arjun* arjun) {
    assert(solver == nullptr);
    solver = new CMSat::SATSolver;
    solver->set_verbosity(conf.verb);
    solver->set_find_xors(false);

    assert(solver->nVars() == 0); // Solver here is empty

    // Inject original CNF
    const auto& cnf = arjun->get_orig_cnf();
    solver->new_vars(cnf.nvars);
    for(const auto& cl: cnf.cnf) solver->add_clause(cl);
    for(const auto& cl: cnf.red_cnf) solver->add_red_clause(cl);
#ifdef WEIGHTED
    if (cnf.weighted) {
        for(const auto& it: cnf.weights) solver->set_lit_weight(it.first, it.second);
    }
#endif
    solver->set_multiplier_weight(cnf.multiplier_weight);

    // inject set vars
    const auto lits = arjun->get_zero_assigned_lits();
    vector<Lit> cl;
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
    const SimpConf simp_conf,
    vector<uint32_t>& sampl_vars,
    vector<uint32_t>& set_sampl_vars,
    vector<uint32_t>& empty_sampl_vars,
    vector<uint32_t>& orig_sampl_vars)
{
    verb_print(3, "Running "<< __PRETTY_FUNCTION__);
    fill_solver(arjun);
    solver->set_renumber(true);
    solver->set_scc(true);
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
        solver->set_bve_too_large_resolvent(simp_conf.bve_too_large_resolvent);
    } else {
        solver->set_occ_based_lit_rem_time_limitM(0);
    }
    solver->set_bve(conf.bve_during_elimtofile);

    // occ-cl-rem-with-orgates not used -- should test and add, probably to 2nd iter
    // eqlit-find from oracle not used (too slow?)
    string str("must-scc-vrepl, full-probe, sub-cls-with-bin, sub-impl, distill-cls-onlyrem, occ-resolv-subs, occ-backw-sub, occ-rem-with-orgates, occ-bve, occ-ternary-res, intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, clean-cls, distill-cls, distill-bins, ");
    if (simp_conf.appmc) str = string("must-scc-vrepl, full-probe, sub-cls-with-bin, sub-impl, distill-cls-onlyrem, occ-resolv-subs, occ-backw-sub, occ-bve, intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, clean-cls, distill-cls, distill-bins, ");
    for (int i = 0; i < simp_conf.iter1; i++) solver->simplify(&dont_elim, &str);

    // Now doing Oracle
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

    SimplifiedCNF cnf;
    solver->get_empties(sampl_vars, empty_sampl_vars);
    dont_elim.clear();
    for(uint32_t v: sampl_vars) dont_elim.push_back(Lit(v, false));
    str = "occ-bve-empty, must-renumber";
    solver->simplify(&dont_elim, &str);
    get_simplified_cnf(cnf, sampl_vars, set_sampl_vars, empty_sampl_vars, orig_sampl_vars);
    return cnf;
}

void Puura::setup_sampl_vars_dontelim(const vector<uint32_t>& sampl_vars)
{
    assert(dont_elim.empty());
    for(uint32_t v: sampl_vars) dont_elim.push_back(Lit(v, false));
    sampl_set.clear();
    for(uint32_t v: sampl_set) sampl_set.insert(v);
}

void Puura::run_sbva(SimplifiedCNF& orig,
        int64_t sbva_steps, uint32_t sbva_cls_cutoff, uint32_t sbva_lits_cutoff, int sbva_tiebreak) {

    if (sbva_steps == 0) return;

    auto my_time = cpuTime();
    verb_print(1, "[arjun-sbva] entering SBVA with"
            " vars: " << orig.nvars << " cls: " << orig.cnf.size());

    SBVA::Config sbva_conf;
    sbva_conf.steps = sbva_steps*1e6;
    sbva_conf.matched_cls_cutoff = sbva_cls_cutoff;
    sbva_conf.matched_lits_cutoff = sbva_lits_cutoff;
    sbva_conf.preserve_model_cnt = 1;
    SBVA::CNF cnf;
    cnf.init_cnf(orig.nvars, sbva_conf);
    vector<int> tmp;
    for(const auto& cl: orig.cnf) {
        tmp.clear();
        for(const auto& l: cl) tmp.push_back((l.var()+1) * (l.sign() ? -1 : 1));
        cnf.add_cl(tmp);
    }
    cnf.finish_cnf();
    assert(sbva_tiebreak == 0 || sbva_tiebreak == 1);
    cnf.run(sbva_tiebreak == 1 ? SBVA::Tiebreak::ThreeHop : SBVA::Tiebreak::None);
    uint32_t ncls;
    auto ret = cnf.get_cnf(orig.nvars, ncls);

    orig.cnf.clear();
    vector<Lit> cl;
    uint32_t at = 0;
    while(ret.size() > at) {
        int l = ret[at++];
        if (l == 0) {
            orig.cnf.push_back(cl);
            cl.clear();
            continue;
        }
        cl.push_back(Lit(std::abs(l)-1, l < 0));
    }
    assert(cl.empty() && "SBVA should have ended with a 0");

    if (conf.verb) {
        cout << "c [arjun-sbva] steps remainK: " << std::setprecision(2) << std::fixed
           << (double)sbva_conf.steps/1000.0
           << " Timeout: " << (sbva_conf.steps <= 0 ? "Yes" : "No")
           << " T: " << std::setprecision(2) << std::fixed
           << (cpuTime() - my_time)
           << endl;
        cout << "c [arjun-sbva] exited SBVA with"
            " vars: " << orig.nvars << " cls: " << orig.cnf.size() << endl;
    }
}
