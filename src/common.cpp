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

#include "common.h"
#include <cstdint>
#include <limits>

using namespace ArjunInt;
using std::numeric_limits;

void Common::update_sampling_set(
    const vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const vector<uint32_t>& indep
) {
    sampling_set.clear();
    for(const auto& var: unknown) {
        if (unknown_set[var]) sampling_set.push_back(var);
    }
    for(const auto& var: indep) sampling_set.push_back(var);

}

void Common::start_with_clean_sampling_set() {
    sampling_set.clear();
    for (size_t i = 0; i < solver->nVars(); i++) {
        sampling_set.push_back(i);
        orig_sampling_vars.push_back(i);
    }
}

void Common::print_orig_sampling_set()
{
    if (sampling_set.size() > 100) {
        cout
        << "c [arjun] Sampling var set contains over 100 variables, not displaying"
        << endl;
    } else {
        cout << "c [arjun] Sampling set: ";
        for (auto v: sampling_set) cout << v+1 << ", ";
        cout << endl;
    }
    cout << "c [arjun] Orig size         : " << sampling_set.size() << endl;
}

void Common::add_fixed_clauses()
{
    double fix_cl_time = cpuTime();
    dont_elim.clear();
    var_to_indic.clear();
    var_to_indic.resize(orig_num_vars, var_Undef);
    indic_to_var.clear();
    indic_to_var.resize(solver->nVars(), var_Undef);

    //If indicator variable is TRUE, they are FORCED EQUAL
    vector<Lit> tmp;
    for(uint32_t var: sampling_set) {
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
    for(uint32_t var: sampling_set) {
        dont_elim.push_back(Lit(var, false));
        dont_elim.push_back(Lit(var+orig_num_vars, false));
    }
    if (conf.verb) {
        cout << "c [arjun] Adding fixed clauses time: " << (cpuTime()-fix_cl_time) << endl;
    }
}

void Common::duplicate_problem() {
    solver->set_verbosity(std::max<int>(conf.verb-2, 0));

    //Duplicate the already simplified problem
    if (conf.verb) cout << "c [arjun] Duplicating CNF..." << endl;
    double dupl_time = cpuTime();
    auto cnf = get_init_cnf();

    solver->new_vars(orig_num_vars);
    for(auto& cl: cnf.cnf) {
        for(auto& l: cl) l = Lit(l.var()+orig_num_vars, l.sign());
        solver->add_clause(cl);
    }
    if (conf.verb) cout << "c [arjun] Duplicated CNF. T: " << (cpuTime() - dupl_time) << endl;
}

ArjunNS::SimplifiedCNF Common::get_init_cnf() {
    ArjunNS::SimplifiedCNF cnf;

    vector<Lit> clause;
    bool is_xor, rhs;
    solver->start_getting_constraints(false);
    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        cnf.cnf.push_back(clause);
    }
    solver->end_getting_constraints();

    cnf.nvars = solver->nVars();
    cnf.sampl_vars = sampling_set;
    cnf.opt_sampl_vars = sampling_set;
    cnf.multiplier_weight = solver->get_multiplier_weight();
#ifdef WEIGHTED
    if (cnf.weighted) {
        solver->get_weights(cnf.weights, sampling_set, orig_sampling_vars);
        //todo
    }
#endif

    return cnf;
}

void Common::get_incidence()
{
    incidence.clear();
    incidence.resize(orig_num_vars, 0);
    incidence.clear();
    incidence_probing.resize(orig_num_vars, 0);
    assert(solver->nVars() == orig_num_vars);
    vector<uint32_t> inc = solver->get_lit_incidence();
    assert(inc.size() == orig_num_vars*2);
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        Lit l = Lit(i, true);
        if (conf.incidence_count == 1) {
            incidence[l.var()] = inc[l.toInt()] + inc[(~l).toInt()];
        } else if (conf.incidence_count == 2) {
            incidence[l.var()] = std::max(inc[l.toInt()], inc[(~l).toInt()]);
        } else if (conf.incidence_count == 3) {
            incidence[l.var()] = std::min(inc[l.toInt()],inc[(~l).toInt()]);
        } else {
            assert(false && "This is NOT accepted incidence count");
        }
    }
}

void Common::set_up_solver()
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

bool Common:: simplify_bve_only() {
    //BVE ***ONLY***, don't eliminate the original variables
    solver->set_intree_probe(false);
    solver->set_distill(false);
    for(uint32_t var: sampling_set) {
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

bool Common::run_gauss_jordan()
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

void Common::init() {
    orig_cnf = get_init_cnf();
    assert(orig_num_vars  == std::numeric_limits<uint32_t>::max() && "double init");
    orig_num_vars = solver->nVars();
    check_sanity_sampling_vars(sampling_set, orig_num_vars);
    seen.clear();
    seen.resize(solver->nVars(), 0);
}

bool Common::preproc_and_duplicate() {
    assert(!already_duplicated);
    already_duplicated = true;
    get_incidence();
    if (conf.simp && !simplify()) return false;
    get_incidence();
    duplicate_problem();
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
