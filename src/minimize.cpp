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
#include <limits>

#include "src/arjun.h"
#include "time_mem.h"
#include "constants.h"

using namespace ArjunInt;
using std::numeric_limits;

void Minimize::update_sampling_set(
    const vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const vector<uint32_t>& indep
) {
    sampling_vars.clear();
    for(const auto& var: unknown) {
        if (unknown_set[var]) sampling_vars.push_back(var);
    }
    for(const auto& var: indep) sampling_vars.push_back(var);

}

void Minimize::start_with_clean_sampl_vars() {
    sampling_vars.clear();
    for (size_t i = 0; i < solver->nVars(); i++) {
        sampling_vars.push_back(i);
    }
}

void Minimize::print_orig_sampling_set()
{
    if (sampling_vars.size() > 100) {
        cout
        << "c [arjun] Sampling var set contains over 100 variables, not displaying"
        << endl;
    } else {
        cout << "c [arjun] Sampling set: ";
        for (auto v: sampling_vars) cout << v+1 << ", ";
        cout << endl;
    }
    cout << "c [arjun] Orig size         : " << sampling_vars.size() << endl;
}

void Minimize::add_fixed_clauses()
{
    double fix_cl_time = cpuTime();
    dont_elim.clear();
    var_to_indic.clear();
    var_to_indic.resize(orig_num_vars, var_Undef);
    indic_to_var.clear();
    indic_to_var.resize(solver->nVars(), var_Undef);

    //If indicator variable is TRUE, they are FORCED EQUAL
    vector<Lit> tmp;
    for(uint32_t var: sampling_vars) {
        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        //torem_orig.push_back(Lit(this_indic, false));
        var_to_indic[var] = this_indic;
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

    //Don't eliminate the sampling variables
    for(uint32_t var: sampling_vars) {
        dont_elim.push_back(Lit(var, false));
        dont_elim.push_back(Lit(var+orig_num_vars, false));
    }
    if (conf.verb) {
        cout << "c [arjun] Adding fixed clauses time: " << (cpuTime()-fix_cl_time) << endl;
    }
}

void Minimize::duplicate_problem(const ArjunNS::SimplifiedCNF& orig_cnf) {
    assert(!already_duplicated);
    solver->set_verbosity(std::max<int>(conf.verb-2, 0));

    //Duplicate the already simplified problem
    if (conf.verb) cout << "c [arjun] Duplicating CNF..." << endl;
    double dupl_time = cpuTime();

    solver->new_vars(orig_num_vars);
    for(const auto& cl: orig_cnf.clauses) {
        auto cl2 = cl;
        for(auto& l: cl2) l = Lit(l.var()+orig_num_vars, l.sign());
        solver->add_clause(cl2);
    }
    if (conf.verb) cout << "c [arjun] Duplicated CNF. T: " << (cpuTime() - dupl_time) << endl;
    already_duplicated = true;
}

void Minimize::get_incidence() {
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

void Minimize::set_up_solver()
{
    assert(solver == nullptr);
    solver = new SATSolver;
    solver->set_up_for_arjun();
    solver->set_renumber(0);
    solver->set_bve(0);
    solver->set_verbosity(std::max(conf.verb-2, 0));
    solver->set_intree_probe(conf.intree && conf.simp);
    solver->set_distill(conf.distill && conf.simp);
    solver->set_sls(false);
    solver->set_find_xors(false);
}

bool Minimize:: simplify_bve_only() {
    //BVE ***ONLY***, don't eliminate the original variables
    solver->set_intree_probe(false);
    solver->set_distill(false);
    for(uint32_t var: sampling_vars) {
        dont_elim.push_back(Lit(var, false));
        dont_elim.push_back(Lit(var+orig_num_vars, false));
    }
    double simp_bve_time = cpuTime();
    if (conf.verb) {
        cout << "c [arjun] CMS::simplify() with *only* BVE..." << endl;
    }

    if (conf.simp) {
        solver->set_bve(1);
        solver->set_verbosity(std::max(conf.verb-2, 0));
        string str("occ-bve");
        if (solver->simplify(&dont_elim, &str) == l_False) return false;
        verb_print(1, "[arjun] CMS::simplify() with *only* BVE finished. T: "
            << cpuTime() - simp_bve_time);
    }
    solver->set_intree_probe(true);
    solver->set_distill(true);
    return true;
}

bool Minimize::run_gauss_jordan()
{
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

template <class T>
void check_sanity_sampling_vars(T vars, const uint32_t nvars)
{
    for(const auto& v: vars) if (v >= nvars) {
        cout << "ERROR: sampling set provided is incorrect, it has a variable in it: " << v+1 << " that is larger than the total number of variables: " << nvars << endl;
        exit(-1);
    }
}

void Minimize::init() {
    assert(orig_num_vars == std::numeric_limits<uint32_t>::max() && "double init");
    orig_num_vars = solver->nVars();
    check_sanity_sampling_vars(sampling_vars, orig_num_vars);
    seen.clear();
    seen.resize(solver->nVars(), 0);
}

bool Minimize::preproc_and_duplicate(const ArjunNS::SimplifiedCNF& orig_cnf) {
    assert(!already_duplicated);
    get_incidence();
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

void Minimize::run_minimize_indep(ArjunNS::SimplifiedCNF& cnf) {
    double start_time = cpuTime();
    solver->set_verbosity(conf.verb);
    solver->new_vars(cnf.nvars);
    for(const auto& cl: cnf.clauses) solver->add_clause(cl);
    for(const auto& cl: cnf.red_clauses) solver->add_red_clause(cl);
    sampling_vars = cnf.sampl_vars;
    if (cnf.opt_sampl_vars_given) {
        if (cnf.sampl_vars != cnf.opt_sampl_vars) {
            cout <<"ERROR: backwards does not support opt sampling set" << endl;
            exit(-1);
        }
    }
    assert(!cnf.weighted);

    init();
    if (!preproc_and_duplicate(cnf)) goto end;
    assert(!cnf.weighted);
    backward_round();

    end:
    // Get what we came here for
    cnf.sampl_vars = sampling_vars;

    // Take units and binary xors back
    for(const auto& l: solver->get_zero_assigned_lits())
        if (l.var() < cnf.nvars) cnf.clauses.push_back({l});
    for(const auto& p: solver->get_all_binary_xors()) {
        if (p.first.var() >= cnf.nvars || p.second.var() >= cnf.nvars) continue;
        vector<Lit> cl(2);
        cl[0] = p.first;
        cl[1] = ~p.second;
        cnf.clauses.push_back(cl);
        cl[0] = ~cl[0];
        cl[1] = ~cl[1];
        cnf.clauses.push_back(cl);
    }

    mpz_class dummy(2);
    mpz_pow_ui(dummy.get_mpz_t(), dummy.get_mpz_t(), empty_sampling_vars.size());
    cnf.multiplier_weight *= dummy;

    verb_print(1, "[arjun] run_minimize_indep finished "
        << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_time));
}
