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

#include <limits>
#include <sbva/sbva.h>

#include "arjun.h"
#include "config.h"
#include "minimize.h"
#include "GitSHA1.h"
#include "puura.h"
#include "extend.h"
#include "time_mem.h"
#include "constants.h"
#include "manthan.h"

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
    arjdata->conf.NAME = NAME; \
} \
DLL_PUBLIC TYPE Arjun::get_##NAME () const \
{ \
    return arjdata->conf.NAME; \
} \

namespace ArjunNS {
    struct ArjPrivateData {
        Config conf;
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
    return CMSat::SATSolver::get_text_version_info("c o ");
}

DLL_PUBLIC std::string Arjun::get_compilation_env()
{
    return ArjunIntNS::get_compilation_env();
}

DLL_PUBLIC void Arjun::standalone_minimize_indep(SimplifiedCNF& cnf, bool all_indep) {
    Minimize common(arjdata->conf);
    common.run_minimize_indep(cnf, all_indep);
}

DLL_PUBLIC void Arjun::standalone_minimize_indep_synt(SimplifiedCNF& cnf) {
    Minimize common(arjdata->conf);
    common.run_minimize_for_synth(cnf);
}

DLL_PUBLIC void Arjun::standalone_unsat_define(SimplifiedCNF& cnf) {
    Extend extend(arjdata->conf);
    extend.unsat_define(cnf);
}

DLL_PUBLIC void Arjun::standalone_extend_sampl_set(SimplifiedCNF& cnf)
{
    Extend extend(arjdata->conf);
    extend.extend_round(cnf);
}

DLL_PUBLIC SimplifiedCNF Arjun::standalone_get_simplified_cnf(
                const SimplifiedCNF& cnf, const SimpConf& simp_conf)
{
    Puura puura(arjdata->conf);
    return puura.get_fully_simplified_renumbered_cnf(cnf, simp_conf);
}

DLL_PUBLIC SimplifiedCNF Arjun::standalone_manthan(const SimplifiedCNF& cnf)
{
    Manthan manthan(arjdata->conf, cnf.fg);
    return manthan.do_manthan(cnf);
}

DLL_PUBLIC void Arjun::standalone_rev_bce(SimplifiedCNF& cnf)
{
    Puura puura(arjdata->conf);
    return puura.reverse_bce(cnf);
}

DLL_PUBLIC void Arjun::standalone_unate(SimplifiedCNF& cnf)
{
    Puura puura(arjdata->conf);
    puura.synthesis_unate(cnf);
}

DLL_PUBLIC void Arjun::standalone_sbva(SimplifiedCNF& orig,
            int64_t sbva_steps, uint32_t sbva_cls_cutoff, uint32_t sbva_lits_cutoff, int sbva_tiebreak)
{
    Puura puura(arjdata->conf);
    puura.run_sbva(orig, sbva_steps, sbva_cls_cutoff, sbva_lits_cutoff, sbva_tiebreak);
}

struct Clause {
    uint32_t at = numeric_limits<uint32_t>::max();
    vector<Lit> lits;
    bool red = false;
};

DLL_PUBLIC void Arjun::standalone_bce(SimplifiedCNF& cnf) {
    // Unfortunately, with opt_sampling_set, we rely on a variables
    // being fully deterministic. So we can't block on them
    // otherwise we'd need to remove those variables from the opt_sampling set
    set<uint32_t> dont_block;
    for(const auto& v: cnf.sampl_vars) dont_block.insert(v);
    for(const auto& v: cnf.opt_sampl_vars) dont_block.insert(v);
    if (dont_block.size() == cnf.nvars) return;

    const double start_time = cpuTime();
    vector<Clause> cls;
    vector<vector<uint32_t>> occs(cnf.nvars*2);
    uint32_t at = 0;
    for(const auto& cl: cnf.clauses) {
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

    cnf.clauses.clear();
    for(const auto& cl: cls) {
        if (!cl.red) cnf.clauses.push_back(cl.lits);
        else cnf.red_clauses.push_back(cl.lits);
    }
    verb_print2(1, "[arjun] BCE removed " << tot_removed << " clauses"
        " T: " << (cpuTime() - start_time));
}

DLL_PUBLIC void Arjun::standalone_backbone(SimplifiedCNF& cnf) {
    Puura puura(arjdata->conf);
    puura.backbone(cnf);
}

DLL_PUBLIC void Arjun::standalone_elim_to_file(SimplifiedCNF& cnf,
        const ElimToFileConf& etof_conf, const SimpConf& simp_conf) {
    cnf.remove_equiv_weights();
    cnf = standalone_get_simplified_cnf(cnf, simp_conf);
    cnf.remove_equiv_weights();
    auto simp_conf2 = simp_conf;
    simp_conf2.bve_grow_iter1 = 0;
    simp_conf2.bve_grow_iter2 = 0;
    simp_conf2.iter1 = 1;
    simp_conf2.iter2 = 1;
    simp_conf2.bve_too_large_resolvent = 4;
    cnf = standalone_get_simplified_cnf(cnf, simp_conf2);
    if (etof_conf.num_sbva_steps > 0)
        standalone_sbva(cnf, etof_conf.num_sbva_steps,
                etof_conf.sbva_cls_cutoff, etof_conf.sbva_lits_cutoff, etof_conf.sbva_tiebreak);
    if (etof_conf.all_indep) {
        vector<uint32_t> all_vars;
        for(uint32_t i = 0; i < cnf.nvars; i++) all_vars.push_back(i);
        cnf.set_opt_sampl_vars(all_vars);
    }
    if (etof_conf.do_extend_indep && cnf.opt_sampl_vars.size() != cnf.nvars)
        standalone_extend_sampl_set(cnf);
    if (etof_conf.do_bce) standalone_bce(cnf);
    if (etof_conf.do_unate)
        standalone_unate(cnf);
    cnf.remove_equiv_weights();
    if (etof_conf.do_renumber) cnf.renumber_sampling_vars_for_ganak();
}

set_get_macro(bool, distill)
set_get_macro(bool, intree)
set_get_macro(bool, bve_pre_simplify)
set_get_macro(int, simp)
set_get_macro(uint32_t, incidence_count)
set_get_macro(bool, or_gate_based)
set_get_macro(bool, xor_gates_based)
set_get_macro(bool, probe_based)
set_get_macro(uint32_t, backw_max_confl)
set_get_macro(bool, gauss_jordan)
set_get_macro(bool, ite_gate_based)
set_get_macro(bool, irreg_gate_based)
set_get_macro(double, no_gates_below)
set_get_macro(std::string, specified_order_fname)
set_get_macro(uint32_t, verb)
set_get_macro(uint32_t, extend_max_confl)
set_get_macro(int, oracle_find_bins)
set_get_macro(int, num_samples)
set_get_macro(double, cms_glob_mult)
set_get_macro(int, extend_ccnr)
set_get_macro(int, autarkies)
