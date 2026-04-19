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

#include <cryptominisat5/cryptominisat.h>
#include <cstdint>
#include <memory>
#include <vector>
#include <iostream>
#include <iomanip>
#include <string>

#include <sbva/sbva.h>
#include "time_mem.h"
#include "puura.h"
#include "arjun.h"
#include "constants.h"

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::vector;
using std::set;
using std::unique_ptr;
using namespace CMSat;
using std::vector;
using std::setw;
using std::setprecision;
using std::string;
using std::unique_ptr;

Puura::Puura(const Config& _conf) : conf(_conf) {}
Puura::~Puura() = default;

void Puura::backbone(SimplifiedCNF& cnf) {
    double my_time = cpuTime();
    if (cnf.get_weighted()) {
        for(const auto& v: cnf.get_opt_sampl_vars()) {
            Lit l(v, false);
            if (cnf.get_lit_weight(l)->is_zero()) cnf.add_clause({~l});
            if (cnf.get_lit_weight(~l)->is_zero()) cnf.add_clause({l});
        }
    }
    auto solver = fill_solver(cnf);
    string str = "clean-cls, must-scc-vrepl, full-probe, must-scc-vrepl, must-renumber";
    solver->simplify(nullptr, &str);
    solver->set_verbosity(conf.verb);
    bool backbone_done = cnf.get_backbone_done();
    solver->backbone_simpl(20*1000ULL, backbone_done);
    cnf.set_backbone_done(backbone_done);

    auto lits = solver->get_zero_assigned_lits();
    for(const auto& l: lits) {
        cnf.add_clause({l});
        verb_print(3,"backbone inserting : " << l);
    }
    verb_print(2, "backbone inserted: " << lits.size() << " T: " << (cpuTime() - my_time));
    verb_print(1, "[arjun-backbone] done, T: " << (cpuTime() - my_time));
}

std::unique_ptr<SATSolver> Puura::fill_solver(const SimplifiedCNF& cnf) {
    auto solver = std::make_unique<SATSolver>();
    solver->set_verbosity(conf.verb);
    solver->set_prefix("c o ");
    solver->set_find_xors(false);
    assert(solver->nVars() == 0); // Solver here is empty

    // Inject original CNF
    solver->new_vars(cnf.nVars());
    for(const auto& cl: cnf.get_clauses()) solver->add_clause(cl);
    for(const auto& cl: cnf.get_red_clauses()) solver->add_red_clause(cl);
    return solver;
}

void Puura::reverse_bce(SimplifiedCNF& cnf) {
    auto solver = fill_solver(cnf);
    solver->set_renumber(false);
    solver->set_scc(false);
    set_up_sampl_vars_dont_elim(cnf);
    solver->set_sampl_vars(cnf.get_sampl_vars());
    solver->reverse_bce();
}

bool Puura::set_zero_weight_lits(const ArjunNS::SimplifiedCNF& cnf, std::unique_ptr<SATSolver>& solver) {
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

SimplifiedCNF Puura::get_fully_simplified_renumbered_cnf(
    const SimplifiedCNF& cnf,
    const SimpConf simp_conf)
{
    SLOW_DEBUG_DO(cnf.check_red_cls_deriveable());
    const double my_time = cpuTime();
    if (cnf.get_need_aig()) {
        SLOW_DEBUG_DO(assert(cnf.defs_invariant()));
        cnf.get_var_types(conf.verb | verbose_debug_enabled, "start get_fully_simplified_renumbered_cnf").unpack_to(input, to_define, backward_defined);
    }
    for(const auto& v: cnf.get_sampl_vars())
        verb_print(5, "[w-debug] orig sampl var: " << v+1);
    for(const auto& v: cnf.get_opt_sampl_vars())
        verb_print(5, "[w-debug] orig opt sampl var: " << v+1);

    auto solver = fill_solver(cnf);
    set_zero_weight_lits(cnf, solver);
    verb_print(3, "Running "<< __PRETTY_FUNCTION__);
    solver->set_renumber(true);
    solver->set_scc(true);
    if (conf.cms_glob_mult > 0) solver->set_orig_global_timeout_multiplier(conf.cms_glob_mult);
    set_up_sampl_vars_dont_elim(cnf);

    //Below works VERY WELL for: ProcessBean, pollard, track1_116.mcc2020_cnf
    //   and blasted_TR_b14_even3_linear.cnf.gz.no_w.cnf
    //with CMS ef6ea7e87e00bde50c0cce0c1e13a012191c4e1c and Arjun 5f2dfe814e07ee6ee0dde65b1350b5c343209ed0
    solver->set_varelim_check_resolvent_subs(false);
    solver->set_max_red_linkin_size(0);
    solver->set_do_subs_with_resolvent_clauses(simp_conf.do_subs_with_resolvent_clauses);
    /* solver->set_timeout_all_calls(100); */
    solver->set_weaken_time_limitM(simp_conf.weaken_limit);
    solver->set_oracle_get_learnts(simp_conf.oracle_vivify_get_learnts);
    solver->set_oracle_removed_is_learnt(1);
    solver->set_oracle_find_bins(conf.oracle_find_bins);
    solver->set_oracle_mult(simp_conf.oracle_mult);
    solver->set_bve(simp_conf.do_bve);
    if (!simp_conf.appmc) {
        solver->set_min_bva_gain(simp_conf.bve_grow_iter1);
        solver->set_bve_nonstop(simp_conf.bve_grow_nonstop);
        solver->set_occ_based_lit_rem_time_limitM(500);
        solver->set_bve_too_large_resolvent(simp_conf.bve_too_large_resolvent);
    } else {
        solver->set_occ_based_lit_rem_time_limitM(0);
    }

    // occ-cl-rem-with-orgates not used -- should test and add, probably to 2nd iter
    // eqlit-find from oracle not used (too slow?)
    // D: occ-ternary-res moved before occ-bve (ternary->binary enables more SCC equivalences for BVE)
    // B: distill-cls-onlyrem added after occ-bve (removes clauses subsumed after variable elimination)
    // K: must-scc-vrepl between occ-ternary-res and occ-bve so BVE sees the
    //    var-substitutions implied by the new binaries ternary-res produced.
    //    Without it, BVE is still reasoning against the old var IDs.
    // L: sub-impl right after occ-bve. BVE produces new binary resolvents, and
    //    sub-impl cleans out the transitively-redundant ones cheaply (it's
    //    just walking implications) before distill sees them.
    string str("must-scc-vrepl, full-probe, sub-impl, sub-cls-with-bin, distill-cls-onlyrem, occ-backw-sub, occ-resolv-subs, occ-rem-with-orgates, occ-ternary-res, must-scc-vrepl, occ-bve, sub-impl, distill-cls-onlyrem, intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, clean-cls, distill-cls, distill-bins, ");
    if (simp_conf.appmc) str = string("must-scc-vrepl, full-probe, sub-cls-with-bin, sub-impl, distill-cls-onlyrem, occ-resolv-subs, occ-backw-sub, occ-bve, intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, clean-cls, distill-cls, distill-bins, ");
    // C: iter2 uses a separate string with extra occ-backw-sub at the end (catches clauses subsumed by BVE resolvents)
    string str_iter2 = str + string("occ-backw-sub, ");
    for (int i = 0; i < simp_conf.iter1; i++) solver->simplify(&dont_elim, &str);

    // Now doing Oracle
    string str2;
    bool backbone_done = cnf.get_backbone_done();
    if (!backbone_done && simp_conf.do_backbone_puura) {
        solver->backbone_simpl(simp_conf.backbone_max_confl, backbone_done);
        // N: after backbone_simpl sets units and adds bins, run the trio
        //    sub-impl + sub-cls-with-bin + distill-cls-onlyrem so the new
        //    binaries collapse against the existing ones, the new units
        //    strengthen/drop clauses via sub-cls-with-bin, and distill
        //    removes anything that's now a tautology. Previously only
        //    must-scc-vrepl ran, and oracle-vivif then paid full price to
        //    vivify clauses a unit would have satisfied for free.
        string str_post_backbone = "must-scc-vrepl, sub-impl, sub-cls-with-bin, distill-cls-onlyrem, must-renumber";
        solver->simplify(&dont_elim, &str_post_backbone);
    }
    if (backbone_done) {
        if (simp_conf.oracle_vivify && simp_conf.oracle_sparsify) str2 = "oracle-vivif-sparsify";
        else if (simp_conf.oracle_vivify) str2 = "oracle-vivif";
        else if (simp_conf.oracle_sparsify) str2 = "oracle-sparsify";
    } else {
        if (simp_conf.oracle_vivify && simp_conf.oracle_sparsify) str2 = "oracle-vivif-sparsify-mustfinish";
        else if (simp_conf.oracle_vivify) str2 = "oracle-vivif";
    }
    solver->simplify(&dont_elim, &str2);

    // Now more expensive BVE, also RED linked in to occur
    if (!simp_conf.appmc) {
        solver->set_min_bva_gain(simp_conf.bve_grow_iter2);
        solver->set_bve_nonstop(simp_conf.bve_grow_nonstop);
        solver->set_varelim_check_resolvent_subs(true);
    }
    solver->set_max_red_linkin_size(20);
    for (int i = 0; i < simp_conf.iter2; i++) {
        if (i >= 1) {
            solver->set_picosat_gate_limitK(400);
            solver->set_picosat_confl_limit(1000);
        }
        solver->simplify(&dont_elim, &str_iter2);
    }

    // Final cleanup -- renumbering, disconnected component removing, etc.
    str.clear();

    // one more sparisfy
    if (simp_conf.oracle_extra && simp_conf.oracle_sparsify && simp_conf.oracle_vivify) {
        string s;
        if (backbone_done) s = "oracle-vivif-fast, oracle-sparsify-fast";
        else s = "oracle-vivif-sparsify-mustfinish";
        solver->simplify(&dont_elim, &s);
    }
    if (simp_conf.oracle_extra && !simp_conf.appmc) {
        solver->set_min_bva_gain(0);
        string s_bve = "occ-bve";
        solver->simplify(&dont_elim, &s_bve);
    }

    str += string(", must-scc-vrepl, sub-impl, sub-cls-with-bin, distill-cls-onlyrem, intree-probe, must-scc-vrepl, must-renumber,");
    solver->simplify(&dont_elim, &str);

    auto new_sampl_vars = cnf.get_sampl_vars();
    vector<uint32_t> new_empty_sampl_vars;
    solver->clean_sampl_get_empties(new_sampl_vars, new_empty_sampl_vars);
    if (!cnf.get_weighted()) {
      dont_elim.clear();
      for(uint32_t v: new_sampl_vars) dont_elim.emplace_back(v, false);
    } else {
      // don't eliminate anything but the empties from opt_sampl_vars
      set<Lit> tmp(dont_elim.begin(), dont_elim.end());
      for(uint32_t v: new_empty_sampl_vars) {
          tmp.erase(Lit(v, false));
          tmp.erase(Lit(v, true));
      }
      dont_elim.clear();
      for(const auto& l: tmp) dont_elim.push_back(l);
    }
    str = "occ-bve-empty, must-renumber";
    solver->simplify(&dont_elim, &str);
    verb_print(1, "[puura] new_empty_sampl_vars size: " << new_empty_sampl_vars.size());

    // Return final one
    auto ret_cnf = cnf.get_cnf(solver, new_sampl_vars, new_empty_sampl_vars, conf.verb);
    ret_cnf.set_backbone_done(backbone_done);
    if (cnf.get_need_aig()) {
        auto [input_vars2, to_define2, backward_defined2] = ret_cnf.get_var_types(0 | verbose_debug_enabled, "end get_fully_simplified_renumbered_cnf");
        verb_print(1, COLRED "[puura] Done. final vars: " << ret_cnf.nVars()
            << " final cls: " << ret_cnf.get_clauses().size()
            << " defined: " << to_define.size() - to_define2.size()
            << " still to define: " << to_define2.size()
            << " T: " << setprecision(2) << setw(2) << (cpuTime() - my_time));
    } else {
        verb_print(1, COLRED "[puura] Done. final vars: " << ret_cnf.nVars()
            << " final cls: " << ret_cnf.get_clauses().size()
            << " T: " << setprecision(2) << setw(2) << (cpuTime() - my_time));
    }
    SLOW_DEBUG_DO(ret_cnf.check_red_cls_deriveable());
    return ret_cnf;
}

void Puura::set_up_sampl_vars_dont_elim(const SimplifiedCNF& cnf) {
    assert(dont_elim.empty());
    if (cnf.get_weighted()) {
        for(uint32_t v: cnf.get_opt_sampl_vars()) {
            if (cnf.weight_set(v)) {
                verb_print(5, "[w-debug] dont_elim due to weight: " << v+1);
                dont_elim.emplace_back(v, false);
            }
        }
    }
    for(uint32_t v: cnf.get_sampl_vars()) dont_elim.emplace_back(v, false);
    sampl_set.clear();
    for(uint32_t v: cnf.get_sampl_vars()) sampl_set.insert(v);
}

void Puura::run_sbva(SimplifiedCNF& cnf,
        int64_t sbva_steps, uint32_t sbva_cls_cutoff, uint32_t sbva_lits_cutoff,
        int sbva_tiebreak)
{
    if (sbva_steps == 0) return;
    assert(cnf.get_opt_sampl_vars_set());

    auto my_time = cpuTime();
    verb_print(1,
           std::left << setw(35) << "[arjun-sbva] entering SBVA with"
           << " vars: " << setw(7) << cnf.nVars() << setw(8) << " cls: " << cnf.get_clauses().size()
           << " opt sampl: " << cnf.get_opt_sampl_vars() .size());

    SBVA::Config sbva_conf;
    sbva_conf.steps = sbva_steps*1e6;
    sbva_conf.matched_cls_cutoff = sbva_cls_cutoff;
    sbva_conf.matched_lits_cutoff = sbva_lits_cutoff;
    sbva_conf.preserve_model_cnt = 1;
    if (conf.verb >= 3) sbva_conf.verbosity = 1;
    SBVA::CNF sbva;
    sbva.init_cnf(cnf.nVars(), sbva_conf);
    vector<int> tmp;
    for(const auto& cl: cnf.get_clauses()) {
        tmp.clear();
        for(const auto& l: cl) tmp.push_back((l.var()+1) * (l.sign() ? -1 : 1));
        sbva.add_cl(tmp);
    }
    sbva.finish_cnf();
    assert(sbva_tiebreak == 0 || sbva_tiebreak == 1);
    sbva.run(sbva_tiebreak == 1 ? SBVA::Tiebreak::ThreeHop : SBVA::Tiebreak::None);
    uint32_t ncls;
    uint32_t nvars;
    auto ret = sbva.get_cnf(nvars, ncls);
    cnf.replace_clauses_with(ret, nvars, ncls);

    verb_print(1,
           std::left << setw(35) << "[arjun-sbva] exited SBVA with"
           << " vars: " << setw(7) << cnf.nVars() << setw(8) << " cls: " << cnf.get_clauses().size());
    verb_print(1, "[arjun-sbva] steps remainK: " << std::setprecision(2) << std::fixed
           << (double)sbva_conf.steps/1000.0
           << " T-out: " << (sbva_conf.steps <= 0 ? "Yes" : "No")
           << " T: " << std::setprecision(2) << std::fixed
           << (cpuTime() - my_time));
}
