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
#include <limits>
#include <sbva/sbva.h>

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

DLL_PUBLIC uint32_t Arjun::set_sampl_vars(const vector<uint32_t>& vars)
{
    sampling_vars_set = true;
    check_duplicated(arjdata->common.already_duplicated);
    arjdata->common.sampling_set = vars;
    arjdata->common.orig_sampling_vars = vars;
    return arjdata->common.sampling_set.size();
}


DLL_PUBLIC uint32_t Arjun::set_opt_sampl_vars(const std::vector<uint32_t>& vars) {
    if (!sampling_vars_set) {
        std::cerr << "ERROR: For arjun, you must set optional sampling vars after setting the sampling vars" << std::endl;
        assert(false);
        exit(-1);
    }
    if (vars != arjdata->common.sampling_set) {
        std::cerr << "ERROR: For arjun, you must set optional sampling vars EXACTLY the same as the sampling set" << std::endl;
        assert(false);
        exit(-1);
    }
    return vars.size();
}

DLL_PUBLIC uint32_t Arjun::start_with_clean_sampling_set()
{
    sampling_vars_set = true;
    check_duplicated(arjdata->common.already_duplicated);
    arjdata->common.start_with_clean_sampling_set();
    return arjdata->common.sampling_set.size();
}

DLL_PUBLIC string Arjun::get_sbva_version_info()
{
    return SBVA::get_version_sha1();
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

DLL_PUBLIC const SimplifiedCNF& Arjun::get_orig_cnf() const
{
    return arjdata->common.orig_cnf;
}

DLL_PUBLIC const vector<uint32_t>& Arjun::get_current_indep_set() const {
    return arjdata->common.sampling_set;
}

DLL_PUBLIC vector<uint32_t> Arjun::run_backwards() {
    double start_time = cpuTime();
    arjdata->common.init();
    if (!arjdata->common.preproc_and_duplicate()) goto end;
    if (!arjdata->common.orig_cnf.weighted && arjdata->common.conf.backward)
        arjdata->common.backward_round();

    end:
    if (arjdata->common.conf.verb) {
        cout << "c [arjun] run_backwards finished "
        << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_time)
        << endl;
    }
    return arjdata->common.sampling_set;
}

DLL_PUBLIC vector<uint32_t> Arjun::unsat_define() {
    assert(!arjdata->common.already_duplicated);
    arjdata->common.conf.simp = false;
    arjdata->common.init();
    {
        auto cnf = get_orig_cnf();
        Arjun a2;
        a2.new_vars(cnf.nvars);
        for(const auto& cl: cnf.cnf) a2.add_clause(cl);
        a2.set_sampl_vars(cnf.sampl_vars);
        a2.arjdata->common.conf.or_gate_based = false;
        a2.arjdata->common.conf.xor_gates_based = false;
        a2.arjdata->common.conf.ite_gate_based = false;
        a2.arjdata->common.conf.irreg_gate_based = false;
        a2.arjdata->common.init();
        if (!a2.arjdata->common.preproc_and_duplicate()) goto end;
        a2.arjdata->common.unsat_define(arjdata->common.orig_sampling_vars);
        arjdata->common.sampling_set = a2.arjdata->common.sampling_set;
    }
    arjdata->common.orig_sampling_vars = arjdata->common.sampling_set;

    end:
    return arjdata->common.sampling_set;
}

DLL_PUBLIC vector<uint32_t> Arjun::extend_sampl_set()
{
    assert(!arjdata->common.already_duplicated);
    double start_time = cpuTime();
    arjdata->common.conf.simp = false;
    uint32_t orig_size = arjdata->common.sampling_set.size();
    arjdata->common.init();
    if (!arjdata->common.preproc_and_duplicate()) goto end;

    arjdata->common.extend_round();
    if (arjdata->common.conf.verb) {
        cout << "c [arjun] extend fully finished"
        << " Extended by: " << (arjdata->common.sampling_set.size() - orig_size)
        << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_time)
        << endl;
    }

    end:
    return arjdata->common.sampling_set;
}

DLL_PUBLIC void Arjun::start_getting_constraints(
       bool red, // also redundant, otherwise only irred
       bool simplified,
       uint32_t max_len,
       uint32_t max_glue) {
    arjdata->common.solver->start_getting_constraints(red, simplified, max_len, max_glue);
}

DLL_PUBLIC bool Arjun::get_next_constraint(std::vector<CMSat::Lit>& ret, bool& is_xor, bool& rhs) {
    return arjdata->common.solver->get_next_constraint(ret, is_xor, rhs);
}

DLL_PUBLIC void Arjun::end_getting_constraints() {
    arjdata->common.solver->end_getting_constraints();
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

DLL_PUBLIC void Arjun::set_seed(uint32_t seed) { arjdata->common.random_source.seed(seed); }
DLL_PUBLIC uint32_t Arjun::get_verbosity() const { return arjdata->common.conf.verb; }

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
set_get_macro(bool, bve_during_elimtofile)
set_get_macro(bool, do_unate)
set_get_macro(bool, weighted)

DLL_PUBLIC void Arjun::set_pred_forever_cutoff(int pred_forever_cutoff) {
    arjdata->common.solver->set_pred_forever_cutoff(pred_forever_cutoff);
}

DLL_PUBLIC void Arjun::set_every_pred_reduce(int every_pred_reduce) {
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

DLL_PUBLIC bool Arjun::definitely_satisfiable() const {
    return arjdata->common.definitely_satisfiable;
}


struct Clause {
    uint32_t at = numeric_limits<uint32_t>::max();
    vector<Lit> lits;
    bool red = false;
};
DLL_PUBLIC void Arjun::only_bce(SimplifiedCNF& cnf) {
    // If all variables are in opt sampling set, return
    set<uint32_t> dont_block(cnf.opt_sampl_vars.begin(),
            cnf.opt_sampl_vars.end());
    if (dont_block.size() == cnf.nvars) return;

    const double start_time = cpuTime();
    vector<Clause> cls;
    vector<vector<uint32_t>> occs(cnf.nvars*2);
    uint32_t at = 0;
    for(const auto& cl: cnf.cnf) {
        // UNSAT CNF, just return the CNF
        if (cl.empty()) return;

        Clause c;
        c.lits = cl;
        c.at = at;
        c.red = false;
        cls.push_back(c);
        for(const auto& l: cl) occs[l.toInt()].push_back(at);
        assert(cl.size() > 1 && "CNF must be simplified for BCE");
        at++;
    }

    vector<uint8_t> seen;
    seen.resize(cnf.nvars*2, 0);

    uint32_t tot_removed = 0;
    bool removed_one;
    do {
        removed_one = false;
        for(auto& cl: cls) {
            if (cl.red) continue;
            bool can_remove = false;
            for(const auto& l: cl.lits) seen[l.toInt()] = true;
            for(const auto& l: cl.lits) {
                if (dont_block.count(l.var())) continue;
                bool all_blocking = true;
                for(const auto& cl2_at: occs[(~l).toInt()]) {
                    const Clause& cl2 = cls[cl2_at];
                    if (cl2.red) continue;
                    bool found_blocking_lit = false;
                    for(const auto& l2: cl2.lits) {
                        if (l2 == ~l) continue;
                        if (seen[(~l2).toInt()]) {found_blocking_lit = true; break;}
                    }
                    if (!found_blocking_lit) {all_blocking = false; break;}
                }
                if (all_blocking) {can_remove = true; break; }
            }
            for(const auto& l: cl.lits) seen[l.toInt()] = 0;
            if (can_remove) {
                cl.red = true;
                removed_one = true;
                tot_removed++;
            }
        }
    } while(removed_one);

    cnf.cnf.clear();
    for(const auto& cl: cls) {
        if (!cl.red) cnf.cnf.push_back(cl.lits);
        else cnf.red_cnf.push_back(cl.lits);
    }
    if (arjdata->common.conf.verb)
        cout << "v o [arjun] BCE removed " << tot_removed << " clauses"
            " T: " << (cpuTime() - start_time) << endl;
}

DLL_PUBLIC SimplifiedCNF Arjun::get_fully_simplified_renumbered_cnf(const SimpConf& simp_conf)
{
    Puura puura(arjdata->common.conf);
    return puura.get_fully_simplified_renumbered_cnf(this, simp_conf,
            arjdata->common.sampling_set,
            arjdata->common.empty_sampling_vars,
            arjdata->common.orig_sampling_vars);
}


DLL_PUBLIC void Arjun::reverse_bce(SimplifiedCNF& cnf)
{
    Puura puura(arjdata->common.conf);
    return puura.reverse_bce(cnf);
}

DLL_PUBLIC void Arjun::set_lit_weight(
        [[maybe_unused]] const CMSat::Lit lit, [[maybe_unused]] const double weight) {
#ifdef WEIGHTED
    arjdata->common.solver->set_lit_weight(lit, weight);
#else
    assert(false && "This is not a weighted build");
#endif
 }

DLL_PUBLIC void Arjun::run_sbva(SimplifiedCNF& orig,
            int64_t sbva_steps, uint32_t sbva_cls_cutoff, uint32_t sbva_lits_cutoff, int sbva_tiebreak)
{
    if (sbva_steps == 0) return;

    Puura puura(arjdata->common.conf);
    puura.run_sbva(orig, sbva_steps, sbva_cls_cutoff, sbva_lits_cutoff, sbva_tiebreak);
}

DLL_PUBLIC const std::vector<uint32_t>& Arjun::get_empty_sampl_vars() const {
    return arjdata->common.empty_sampling_vars;
}

DLL_PUBLIC const std::vector<uint32_t>& Arjun::get_orig_sampl_vars() const {
    return arjdata->common.orig_sampling_vars;
}

DLL_PUBLIC const std::vector<uint32_t>& Arjun::get_set_sampling_vars() const {
    return arjdata->common.set_sampling_vars;
}

DLL_PUBLIC void Arjun::set_multiplier_weight(const mpz_class mult) {
    arjdata->common.solver->set_multiplier_weight(mult);
}

DLL_PUBLIC mpz_class Arjun::get_multiplier_weight() const {
    return arjdata->common.solver->get_multiplier_weight();
}
