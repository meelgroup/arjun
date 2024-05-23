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
#include <cwchar>
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
using namespace CMSat;
using std::cout;
using std::endl;
using std::vector;
using std::setw;
using std::setprecision;
using std::string;
using std::map;

Puura::Puura(const Config& _conf) : conf(_conf) {}
Puura::~Puura() = default;

SATSolver* Puura::setup_f_not_f_indic(const SimplifiedCNF& cnf) {
    double my_time = cpuTime();

    vector<Lit> tmp;
    SATSolver* s = new SATSolver;
    orig_num_vars = cnf.nvars;
    s->set_verbosity(0);
    s->set_prefix("c o ");
    s->new_vars(cnf.nvars*2); // one for orig, one for copy
    s->set_bve(false);
    s->set_bva(false);
    s->set_no_simplify_at_startup();
    s->set_simplify(false);
    s->set_sls(false);
    s->set_find_xors(false);

    vector<Lit> zs;
    for(const auto& cl: cnf.clauses) {
        // F(x)
        s->add_clause(cl);

        // !F(y)
        s->new_var(); // new var for each clause
        uint32_t zv = s->nVars()-1;
        Lit z = Lit(zv, false);

        // (C shifted) V -z
        tmp.clear();
        for(auto l: cl) {
            if (sampl_set.count(l.var())) {
                tmp.push_back(l);
            } else {
                tmp.push_back(Lit(l.var()+orig_num_vars, l.sign()));
            }
        }
        tmp.push_back(~z);
        s->add_clause(tmp);

        // (each -lit in C, shifted) V z
        for(auto l: cl) {
            tmp.clear();
            if (sampl_set.count(l.var())) {
                tmp = {~l,  z};
            } else {
                tmp = {Lit(l.var()+orig_num_vars, !l.sign()),  z};
            }
            s->add_clause(tmp);
        }
        zs.push_back(~z);
    }

    // At least ONE clause must be FALSE
    s->add_clause(zs);
    s->simplify();
    verb_print(1, "[puura] Built up the solver. T: " << (cpuTime() - my_time));
    return s;
}

void Puura::backbone(SimplifiedCNF& cnf) {
    auto solver = fill_solver(cnf);
    solver->backbone_simpl(20*1000ULL, cnf.backbone_done);
    auto lits = solver->get_zero_assigned_lits();
    for(const auto& l: lits) cnf.clauses.push_back({l});
    delete solver;
}

// TODO: Beware, empty var elim (i.e. all resolvents are tautology) should be done BEFORE this
void Puura::synthesis_unate(SimplifiedCNF& cnf) {
    double my_time = cpuTime();
    uint32_t new_units = 0;
    sampl_set.clear();
    for(const auto& v: cnf.sampl_vars) sampl_set.insert(v);
    verb_print(1, "sampling set size: " << sampl_set.size());

    SATSolver* s = setup_f_not_f_indic(cnf);
    vector<Lit> assumps;
    vector<Lit> cl;
    uint32_t undefs = 0;
    bool timeout = false;
    s->set_find_xors(true);
    s->set_scc(true);
    s->set_bve(false);

    uint32_t to_test = 0;
    dont_elim.clear();
    for(uint32_t test = 0; test < orig_num_vars; test++) {
        if (s->removed_var(test)) continue;
        if (sampl_set.count(test)) continue;
        dont_elim.push_back(Lit(test, false));
        dont_elim.push_back(Lit(test+orig_num_vars, false));
        to_test ++;
    }
    s->simplify(&dont_elim);
    s->set_bve(false);

    verb_print(1, "[unate] Going to test: " << to_test);
    uint32_t tested_num = 0;
    uint32_t old_units;
    do {
        old_units = new_units;
        for(uint32_t test = 0; test < orig_num_vars; test++) {
            if (s->removed_var(test)) continue;
            if (sampl_set.count(test)) continue;
            if (s->get_sum_conflicts() > 50000) {timeout = true; break;}
            tested_num++;
            if (tested_num % 100 == 99) {
                verb_print(1, "[unate] test no: " << setw(5) << tested_num
                    << " confl K: " << setw(4) << s->get_sum_conflicts()/1000
                    << " new units: " << setw(4) << new_units
                    << " T: " << setprecision(2) << std::fixed << (cpuTime() - my_time));
            }

            assumps.clear();
            for(int flip = 0; flip < 2; flip++) {
                assumps.push_back(Lit(test, true ^ flip));
                assumps.push_back(Lit(test+orig_num_vars, false ^ flip));
                s->set_max_confl(1500);
                s->set_no_confl_needed();
                auto ret = s->solve(&assumps, true);
                verb_print(4, "[unate] Ret: " << ret << " flip: " << flip);
                if (ret == l_False) {
                    verb_print(2, "[unate] test: " << std::setw(3)  << (test+1)
                        << " FALSE"
                        << " T: " << (cpuTime() - my_time));

                    cl = {Lit(test, false ^ flip)};
                    cnf.clauses.push_back(cl);
                    s->add_clause(cl);

                    cl = {Lit(test+orig_num_vars, false ^ flip)};
                    s->add_clause(cl);
                    new_units++;
                    break;
                }
                if (ret == l_Undef) undefs++;
                assumps.pop_back();
                assumps.pop_back();
            }
        }
    } while (new_units > old_units);

    verb_print(1, "[unate]" << " new units: " << new_units << " undefs: " << undefs
        << " T-out: " << (int)timeout << " T: " << (cpuTime()-my_time));

    delete s;
}

SimplifiedCNF Puura::get_cnf(
        SATSolver* solver,
        const vector<uint32_t>& sampl_vars,
        const vector<uint32_t>& opt_sampl_vars,
        const vector<uint32_t>& empty_sampl_vars
        ) {
    SimplifiedCNF scnf;
    vector<Lit> clause;
    bool is_xor, rhs;
    scnf.weighted = solver->get_weighted();

    // IRRED clauses
    solver->start_getting_constraints(false, true);

    const auto empties = solver->translate_sampl_set(empty_sampl_vars, true);
    if (scnf.weighted) {
        map<Lit, mpq_class> w;
        solver->get_weights(w, sampl_vars, opt_sampl_vars);
        mpq_class mul(1);
        for(const auto& v: empties) {
            mul *= w[Lit(v, false)] + w[Lit(v, true)];
        }
        const auto units = solver->get_zero_assigned_lits();
        for(const auto& u: units) mul *= w[u];
        scnf.multiplier_weight = solver->get_multiplier_weight()*mul;
    } else {
        mpz_class dummy(2);
        mpz_pow_ui(dummy.get_mpz_t(), dummy.get_mpz_t(), empties.size());
        scnf.multiplier_weight = solver->get_multiplier_weight()*dummy;
    }

    scnf.set_sampl_vars(solver->translate_sampl_set(sampl_vars, false));

    // Opt sampl vars
    auto tmp = solver->translate_sampl_set(opt_sampl_vars, false);
    std::set<uint32_t> tmp2(tmp.begin(), tmp.end());
    for(const auto& t: empties) tmp2.erase(t);
    scnf.set_opt_sampl_vars(tmp2);

    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        scnf.clauses.push_back(clause);
    }
    solver->end_getting_constraints();

    // RED clauses
    solver->start_getting_constraints(true, true);
    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        scnf.red_clauses.push_back(clause);
    }
    solver->end_getting_constraints();

    scnf.nvars = solver->simplified_nvars();
    std::sort(scnf.sampl_vars.begin(), scnf.sampl_vars.end());
    return scnf;
}

SATSolver* Puura::fill_solver(const SimplifiedCNF& cnf) {
    SATSolver* solver;
    solver = new SATSolver;
    solver->set_verbosity(conf.verb);
    solver->set_prefix("c o ");
    solver->set_find_xors(false);
    assert(solver->nVars() == 0); // Solver here is empty

    // Inject original CNF
    solver->new_vars(cnf.nvars);
    for(const auto& cl: cnf.clauses) solver->add_clause(cl);
    for(const auto& cl: cnf.red_clauses) solver->add_red_clause(cl);
    if (cnf.weighted) {
        for(const auto& it: cnf.weights) {
            solver->set_lit_weight(Lit(it.first, false), it.second.pos);
            solver->set_lit_weight(Lit(it.first, true), it.second.neg);
        }
    }
    solver->set_multiplier_weight(cnf.multiplier_weight);
    return solver;
}

bool replace(std::string& str, const std::string& from, const std::string& to) {
    size_t start_pos = str.find(from);
    if(start_pos == std::string::npos)
        return false;
    str.replace(start_pos, from.length(), to);
    return true;
}

void Puura::reverse_bce(SimplifiedCNF& cnf) {
    auto solver = fill_solver(cnf);
    solver->set_renumber(false);
    solver->set_scc(false);
    setup_sampl_vars_dontelim(cnf.sampl_vars);
    solver->set_sampl_vars(cnf.sampl_vars);
    solver->reverse_bce();
    delete solver;
}

SimplifiedCNF Puura::get_fully_simplified_renumbered_cnf(
    const SimplifiedCNF& cnf,
    const SimpConf simp_conf,
    const vector<uint32_t>& empty_sampl_vars)
{
    auto solver = fill_solver(cnf);
    verb_print(3, "Running "<< __PRETTY_FUNCTION__);
    solver->set_renumber(true);
    solver->set_scc(true);
    setup_sampl_vars_dontelim(cnf.sampl_vars);

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

    // occ-cl-rem-with-orgates not used -- should test and add, probably to 2nd iter
    // eqlit-find from oracle not used (too slow?)
    string str("must-scc-vrepl, full-probe, sub-cls-with-bin, sub-impl, distill-cls-onlyrem, occ-resolv-subs, occ-backw-sub, occ-rem-with-orgates, occ-bve, intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, occ-ternary-res, clean-cls, distill-cls, distill-bins, ");
    if (simp_conf.appmc) str = string("must-scc-vrepl, full-probe, sub-cls-with-bin, sub-impl, distill-cls-onlyrem, occ-resolv-subs, occ-backw-sub, occ-bve, intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, clean-cls, distill-cls, distill-bins, ");
    for (int i = 0; i < simp_conf.iter1; i++) solver->simplify(&dont_elim, &str);

    // Now doing Oracle
    string str2;
    bool backbone_done = cnf.backbone_done;
    if (!backbone_done)
        solver->backbone_simpl(30*1000, backbone_done);
    if (backbone_done) {
        if (simp_conf.oracle_vivify && simp_conf.oracle_sparsify) str2 = "oracle-vivif-sparsify";
        else if (simp_conf.oracle_vivify) str2 = "oracle-vivif";
        else if (simp_conf.oracle_sparsify) str2 = "oracle-sparsify";
    }
    else str2 = "";
    solver->simplify(&dont_elim, &str2);

    // Now more expensive BVE, also RED linked in to occur
    if (!simp_conf.appmc) {
        solver->set_min_bva_gain(simp_conf.bve_grow_iter2);
        solver->set_varelim_check_resolvent_subs(true);
    }
    solver->set_max_red_linkin_size(20);
    for (int i = 0; i < simp_conf.iter2; i++) {
        if (i >= 1) {
            solver->set_picosat_gate_limitK(400);
            solver->set_picosat_confl_limit(1000);
        }
        solver->simplify(&dont_elim, &str);
    }

    // Final cleanup -- renumbering, disconnected component removing, etc.
    str.clear();

    // TODO this is useful...
    /* if (arjun->definitely_satisfiable()) { str += string("occ-rem-unconn-assumps, "); } */

    str += string(", must-scc-vrepl, must-renumber,");
    solver->simplify(&dont_elim, &str);

    // Deal with empties
    auto new_sampl_vars = cnf.sampl_vars;
    auto new_empty_sampl_vars = empty_sampl_vars;
    solver->clean_sampl_get_empties(new_sampl_vars, new_empty_sampl_vars);
    dont_elim.clear();
    for(uint32_t v: new_sampl_vars) dont_elim.push_back(Lit(v, false));
    str = "occ-bve-empty, must-renumber";
    solver->simplify(&dont_elim, &str);

    // Return final one
    auto ret = get_cnf(
            solver, new_sampl_vars, cnf.opt_sampl_vars, new_empty_sampl_vars);
    ret.backbone_done = backbone_done;
    delete solver;
    return ret;
}

void Puura::setup_sampl_vars_dontelim(const vector<uint32_t>& sampl_vars)
{
    assert(dont_elim.empty());
    for(uint32_t v: sampl_vars) dont_elim.push_back(Lit(v, false));
    sampl_set.clear();
    for(uint32_t v: sampl_vars) sampl_set.insert(v);
}

void Puura::run_sbva(SimplifiedCNF& cnf,
        int64_t sbva_steps, uint32_t sbva_cls_cutoff, uint32_t sbva_lits_cutoff,
        int sbva_tiebreak)
{
    if (sbva_steps == 0) return;
    assert(cnf.opt_sampl_vars_given);

    auto my_time = cpuTime();
    verb_print(1,
           std::left << setw(35) << "[arjun-sbva] entering SBVA with"
           << " vars: " << setw(7) << cnf.nvars << setw(8) << " cls: " << cnf.clauses.size()
           << " opt sampl: " << cnf.opt_sampl_vars .size());

    SBVA::Config sbva_conf;
    sbva_conf.steps = sbva_steps*1e6;
    sbva_conf.matched_cls_cutoff = sbva_cls_cutoff;
    sbva_conf.matched_lits_cutoff = sbva_lits_cutoff;
    sbva_conf.preserve_model_cnt = 1;
    if (conf.verb >= 3) sbva_conf.verbosity = 1;
    SBVA::CNF sbva;
    sbva.init_cnf(cnf.nvars, sbva_conf);
    vector<int> tmp;
    for(const auto& cl: cnf.clauses) {
        tmp.clear();
        for(const auto& l: cl) tmp.push_back((l.var()+1) * (l.sign() ? -1 : 1));
        sbva.add_cl(tmp);
    }
    sbva.finish_cnf();
    assert(sbva_tiebreak == 0 || sbva_tiebreak == 1);
    sbva.run(sbva_tiebreak == 1 ? SBVA::Tiebreak::ThreeHop : SBVA::Tiebreak::None);
    uint32_t ncls;
    auto ret = sbva.get_cnf(cnf.nvars, ncls);

    cnf.clauses.clear();
    vector<Lit> cl;
    uint32_t at = 0;
    while(ret.size() > at) {
        int l = ret[at++];
        if (l == 0) {
            cnf.clauses.push_back(cl);
            cl.clear();
            continue;
        }
        cl.push_back(Lit(std::abs(l)-1, l < 0));
    }
    assert(cl.empty() && "SBVA should have ended with a 0");

    verb_print(1,
           std::left << setw(35) << "[arjun-sbva] exited SBVA with"
           << " vars: " << setw(7) << cnf.nvars << setw(8) << " cls: " << cnf.clauses.size());
    verb_print(1, "[arjun-sbva] steps remainK: " << std::setprecision(2) << std::fixed
           << (double)sbva_conf.steps/1000.0
           << " T-out: " << (sbva_conf.steps <= 0 ? "Yes" : "No")
           << " T: " << std::setprecision(2) << std::fixed
           << (cpuTime() - my_time));
}
