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

#include <utility>
#include <tuple>
#include <limits>

#include "arjun.h"
#include "config.h"
#include "common.h"
#include "GitSHA1.h"
#include "puura.h"

using std::pair;
using std::numeric_limits;
using namespace ArjunInt;

#if defined _WIN32
    #define DLL_PUBLIC __declspec(dllexport)
#else
    #define DLL_PUBLIC __attribute__ ((visibility ("default")))
    #define DLL_LOCAL  __attribute__ ((visibility ("hidden")))
#endif

#define set_get_macro(TYPE, NAME) \
DLL_PUBLIC void Arjun::set_##NAME (TYPE NAME) \
{ \
    arjdata->common.conf.NAME = NAME; \
} \
DLL_PUBLIC TYPE Arjun::get_##NAME () const \
{ \
    return arjdata->common.conf.NAME; \
} \

namespace ArjunNS {
    struct ArjPrivateData {
        Common common;
    };
}

using namespace ArjunNS;

void check_duplicated(bool duplicated) {
    if (!duplicated) return;
    cout << "ERROR: manipulating the solver AFTER call to indep support manipulation" << endl;
    assert(false);
    exit(-1);
}

DLL_PUBLIC Arjun::Arjun()
{
    arjdata = new ArjPrivateData;
}

DLL_PUBLIC Arjun::~Arjun()
{
    delete arjdata;
}

DLL_PUBLIC uint32_t Arjun::nVars() {
    return arjdata->common.solver->nVars();
}

DLL_PUBLIC void Arjun::new_vars(uint32_t num)
{
    check_duplicated(arjdata->common.already_duplicated);
    arjdata->common.solver->new_vars(num);
}

DLL_PUBLIC void Arjun::new_var()
{
    check_duplicated(arjdata->common.already_duplicated);
    arjdata->common.solver->new_var();
}

DLL_PUBLIC bool Arjun::add_clause(const vector<CMSat::Lit>& lits)
{
    check_duplicated(arjdata->common.already_duplicated);
    return arjdata->common.solver->add_clause(lits);
}

DLL_PUBLIC bool Arjun::add_red_clause(const vector<CMSat::Lit>& lits)
{
    check_duplicated(arjdata->common.already_duplicated);
    return arjdata->common.solver->add_red_clause(lits);
}

DLL_PUBLIC bool Arjun::add_xor_clause(const vector<uint32_t>& vars, bool rhs)
{
    check_duplicated(arjdata->common.already_duplicated);
    assert(false && "Funnily enough this does NOT work. The XORs would generate a BVA variable, and that would then not be returned as part of the simplified CNF. We could calculate a smaller independent set, but that's all.");
    return arjdata->common.solver->add_xor_clause(vars, rhs);
}

DLL_PUBLIC bool Arjun::add_xor_clause(const vector<CMSat::Lit>& lits, bool rhs)
{
    check_duplicated(arjdata->common.already_duplicated);
    assert(false && "Funnily enough this does NOT work. The XORs would generate a BVA variable, and that would then not be returned as part of the simplified CNF. We could calculate a smaller independent set, but that's all.");
    return arjdata->common.solver->add_xor_clause(lits, rhs);
}

DLL_PUBLIC bool Arjun::add_bnn_clause(
            const std::vector<CMSat::Lit>& lits,
            signed cutoff,
            Lit out
        )
{
    check_duplicated(arjdata->common.already_duplicated);
    return arjdata->common.solver->add_bnn_clause(lits, cutoff, out);
}

DLL_PUBLIC uint32_t Arjun::set_starting_sampling_set(const vector<uint32_t>& vars)
{
    check_duplicated(arjdata->common.already_duplicated);
    *arjdata->common.sampling_set = vars;
    return arjdata->common.sampling_set->size();
}

DLL_PUBLIC uint32_t Arjun::start_with_clean_sampling_set()
{
    check_duplicated(arjdata->common.already_duplicated);
    arjdata->common.start_with_clean_sampling_set();
    return arjdata->common.sampling_set->size();
}

DLL_PUBLIC string Arjun::get_version_info()
{
    return ArjunIntNS::get_version_sha1();
}

DLL_PUBLIC std::string Arjun::get_solver_version_info()
{
    return CMSat::SATSolver::get_text_version_info();
}

DLL_PUBLIC std::string Arjun::get_compilation_env()
{
    return ArjunIntNS::get_compilation_env();
}

DLL_PUBLIC const std::vector<Lit>& Arjun::get_orig_cnf()
{
    return arjdata->common.orig_cnf;
}

DLL_PUBLIC const vector<uint32_t>& Arjun::get_current_indep_set() const {
    return *arjdata->common.sampling_set;
}

DLL_PUBLIC vector<uint32_t> Arjun::get_indep_set()
{
    double starTime = cpuTime();
    arjdata->common.init();
    if (!arjdata->common.preproc_and_duplicate()) goto end;

    //Backward
    if (arjdata->common.conf.backward) arjdata->common.backward_round();

    end:
    arjdata->common.empty_out_indep_set_if_unsat();
    if (arjdata->common.conf.verb) {
        cout << "c [arjun] get_indep_set finished "
        << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - starTime)
        << endl;
    }

    // Deal with empty_occs
    arjdata->common.sampling_set->insert(
        arjdata->common.sampling_set->begin(),
        arjdata->common.empty_occs.begin(),
        arjdata->common.empty_occs.end());

    return *arjdata->common.sampling_set;
}


DLL_PUBLIC vector<uint32_t> Arjun::synthesis_define()
{
    assert(!arjdata->common.already_duplicated);
    arjdata->common.conf.simp = false;
    std::set<uint32_t> input;
    for(const auto& v: *arjdata->common.sampling_set) input.insert(v);
    arjdata->common.init();
    if (!arjdata->common.preproc_and_duplicate()) goto end;
    arjdata->common.synthesis_define(input);

    end:
    return *arjdata->common.sampling_set;
}

DLL_PUBLIC vector<uint32_t> Arjun::extend_indep_set()
{
    assert(!arjdata->common.already_duplicated);
    double starTime = cpuTime();
    arjdata->common.conf.simp = false;
    uint32_t orig_size = arjdata->common.sampling_set->size();
    arjdata->common.init();
    if (!arjdata->common.preproc_and_duplicate()) goto end;

    arjdata->common.extend_round();
    if (arjdata->common.conf.verb) {
        cout << "c [arjun] extend fully finished"
        << " Extended by: " << (arjdata->common.sampling_set->size() - orig_size)
        << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - starTime)
        << endl;
    }

    end:
    return *arjdata->common.sampling_set;
}

DLL_PUBLIC const vector<CMSat::BNN*>& Arjun::get_bnns() const
{
    return arjdata->common.solver->get_bnns();
}

DLL_PUBLIC void Arjun::start_getting_small_clauses(uint32_t max_len, uint32_t max_glue, bool red)
{
    arjdata->common.solver->start_getting_small_clauses(max_len, max_glue, red);
}

DLL_PUBLIC bool Arjun::get_next_small_clause(std::vector<CMSat::Lit>& ret)
{
    return arjdata->common.solver->get_next_small_clause(ret);
}

DLL_PUBLIC void Arjun::end_getting_small_clauses()
{
    arjdata->common.solver->end_getting_small_clauses();
}

DLL_PUBLIC uint32_t Arjun::get_orig_num_vars() const
{
    if (arjdata->common.orig_num_vars == std::numeric_limits<uint32_t>::max()) {
        return arjdata->common.solver->nVars();
    }

    return arjdata->common.orig_num_vars;
}


DLL_PUBLIC void Arjun::set_verbosity(uint32_t verb)
{
    arjdata->common.conf.verb = verb;
    arjdata->common.solver->set_verbosity(verb);
}

DLL_PUBLIC void Arjun::set_seed(uint32_t seed)
{
    arjdata->common.random_source.seed(seed);
}

DLL_PUBLIC uint32_t Arjun::get_verbosity() const
{
    return arjdata->common.conf.verb;
}

set_get_macro(bool, fast_backw)
set_get_macro(bool, distill)
set_get_macro(bool, intree)
set_get_macro(bool, bve_pre_simplify)
set_get_macro(bool, simp)
set_get_macro(uint32_t, unknown_sort)
set_get_macro(uint32_t, incidence_count)
set_get_macro(bool, or_gate_based)
set_get_macro(bool, xor_gates_based)
set_get_macro(bool, probe_based)
set_get_macro(bool, backward)
set_get_macro(uint32_t, backw_max_confl)
set_get_macro(bool, gauss_jordan)
set_get_macro(bool, ite_gate_based)
set_get_macro(bool, irreg_gate_based)
set_get_macro(double, no_gates_below)
set_get_macro(std::string, specified_order_fname)
set_get_macro(bool, empty_occs_based)
set_get_macro(bool, bce)
set_get_macro(bool, bve_during_elimtofile)
set_get_macro(bool, do_unate)

DLL_PUBLIC vector<uint32_t> Arjun::get_empty_occ_sampl_vars() const
{
    return arjdata->common.empty_occs;
}

DLL_PUBLIC void Arjun::set_pred_forever_cutoff(int pred_forever_cutoff)
{
    arjdata->common.solver->set_pred_forever_cutoff(pred_forever_cutoff);
}

DLL_PUBLIC void Arjun::set_every_pred_reduce(int every_pred_reduce)
{
    arjdata->common.solver->set_every_pred_reduce(every_pred_reduce);
}

DLL_PUBLIC vector<Lit> Arjun::get_zero_assigned_lits() const
{
    vector<Lit> ret;
    vector<Lit> lits = arjdata->common.solver->get_zero_assigned_lits();
    for(const auto& lit: lits) {
        if (lit.var() < arjdata->common.orig_num_vars) {
            ret.push_back(lit);
        }
    }

    return ret;
}

DLL_PUBLIC std::vector<std::pair<CMSat::Lit, CMSat::Lit> > Arjun::get_all_binary_xors() const
{
    vector<pair<Lit, Lit>> ret;
    const auto bin_xors = arjdata->common.solver->get_all_binary_xors();
    for(const auto& bx: bin_xors) {
        if (bx.first.var() < arjdata->common.orig_num_vars &&
            bx.second.var() < arjdata->common.orig_num_vars)
        {
            ret.push_back(bx);
        }
    }

    return ret;
}

DLL_PUBLIC const vector<Lit> Arjun::get_internal_cnf(uint32_t& num_cls) const
{
    vector<Lit> cnf;
    bool ret = true;
    num_cls = 0;

    arjdata->common.solver->start_getting_small_clauses(
        std::numeric_limits<uint32_t>::max(),
        std::numeric_limits<uint32_t>::max(),
        false);
    vector<Lit> clause;
    while (ret) {
        ret = arjdata->common.solver->get_next_small_clause(clause);
        if (!ret) break;

        bool ok = true;
        for(auto l: clause) {
            if (l.var() >= arjdata->common.orig_num_vars) {
                ok = false;
                break;
            }
        }

        if (ok) {
            for(auto const& l: clause) cnf.push_back(l);
            cnf.push_back(lit_Undef);
            num_cls++;
        }
    }
    arjdata->common.solver->end_getting_small_clauses();
    return cnf;
}

bool Arjun::definitely_satisfiable() const {
    return arjdata->common.definitely_satisfiable;
}

DLL_PUBLIC SimplifiedCNF Arjun::get_fully_simplified_renumbered_cnf(
    const vector<uint32_t>& sampl_vars,
    const SimpConf& simpConf,
    const bool renumber,
    const bool need_sol_extend)
{
    Puura pura(arjdata->common.conf);
    return pura.get_fully_simplified_renumbered_cnf(
            this, sampl_vars, simpConf, renumber, need_sol_extend);
}

DLL_PUBLIC SimplifiedCNF Arjun::only_synthesis_unate(const vector<uint32_t>& sampl_vars)
{
    arjdata->common.init();
    Puura pura(arjdata->common.conf);
    return pura.only_synthesis_unate(this, sampl_vars);
}

DLL_PUBLIC SimplifiedCNF Arjun::only_conditional_dontcare(const vector<uint32_t>& sampl_vars)
{
    arjdata->common.init();
    Puura pura(arjdata->common.conf);
    return pura.only_conditional_dontcare(this, sampl_vars);
}

DLL_PUBLIC SimplifiedCNF Arjun::only_backbone(const vector<uint32_t>& sampl_vars)
{
    arjdata->common.init();
    Puura pura(arjdata->common.conf);
    return pura.only_backbone(this, sampl_vars);
}
