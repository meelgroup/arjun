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

#include <cmath>
#include <algorithm>
#include "minimize.h"
#include "constants.h"
#include "time_mem.h"
#include "ccnr_cms.h"

using std::pair;
using namespace ArjunInt;

void Minimize::check_no_duplicate_in_sampling_set()
{
    for(auto const& v: sampling_vars) {
        if (seen[v]) {
            cout << "ERROR: Variable " << v+1 << " in sampling set twice!" << endl;
            assert(false);
        }
        seen[v] = 1;
    }
    for(auto const& v: sampling_vars) seen[v] = 0;
}

bool Minimize::simplify() {
    assert(conf.simp);
    check_no_duplicate_in_sampling_set();
    auto old_size = sampling_vars.size();
    double my_time = cpuTime();

    if (conf.probe_based && !probe_all()) return false;
    remove_eq_literals();
    remove_zero_assigned_literals();
    get_empty_occs();
    if (conf.bve_pre_simplify) {
        verb_print(1, "[arjun-simp] CMS::simplify() with no BVE, intree probe...");
        double simp_time = cpuTime();
        solver->set_bve(0);
        solver->set_intree_probe(1);
        solver->set_oracle_find_bins(conf.oracle_find_bins);
        std::string s;
        if (conf.simp == 1) s = "intree-probe";
        else s = "str-impl, intree-probe,occ-ternary-res, occ-backw-sub, distill-litrem, must-distill-cls, distill-bins, oracle-vivif-veryfast";
        if (solver->simplify(nullptr, &s) == l_False) return false;
        if (conf.simp >= 3) {
            if (solver->simplify(nullptr, &s) == l_False) return false;
        }
        if (solver->simplify() == l_False) return false;
        solver->set_intree_probe(conf.intree);
        remove_zero_assigned_literals();
        verb_print(1,"[arjun-simp] CMS::simplify() with no BVE finished."
            << " T: " << (cpuTime() - simp_time));
    }
    bool use_gates = true;
    if (sampling_vars.size() < 90*1000) {
        verb_print(1, "WARNING: Turning off gates, because the sampling size is small, so we can just do it. Size: " << sampling_vars.size());
        use_gates = false;
    } else {
        verb_print(1, "[arjun-simp] num vars: " << sampling_vars.size() << " not turning off gates.");
    }

    if ((conf.xor_gates_based || conf.or_gate_based || conf.ite_gate_based) &&
            use_gates) remove_definable_by_gates();
    if (conf.irreg_gate_based && use_gates) remove_definable_by_irreg_gates();

    remove_eq_literals();
    remove_zero_assigned_literals();
    get_empty_occs();
    if (conf.probe_based && !probe_all()) return false;
    remove_eq_literals();
    remove_zero_assigned_literals();
    get_empty_occs();
    if (conf.irreg_gate_based && use_gates) remove_definable_by_irreg_gates();
    if (sampling_vars.size() > 10 && conf.autarkies > 0) run_autarkies();

    solver->set_verbosity(std::max<int>(conf.verb-2, 0));

    verb_print(1, "[arjun] simplification finished "
        << " removed: " << (old_size-sampling_vars.size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_vars.size(), old_size)
        << " T: " << (cpuTime() - my_time));

    check_no_duplicate_in_sampling_set();
    return true;
}

void Minimize::empty_out_indep_set_if_unsat() {
    if (solver->okay()) return;

    //It's UNSAT so the sampling set is empty
    sampling_vars.clear();
    verb_print(1, "[arjun] CNF is UNSAT, setting sampling set to empty");
}

bool Minimize::probe_all()
{
    double my_time = cpuTime();
    order_sampl_set_for_simp();
    auto old_size = sampling_vars.size();
    string s("clean-cls, must-scc-vrepl");
    if (solver->simplify(nullptr, &s) == l_False) return false;

    verb_print(1, "[arjun-simp] probing all sampling variables");
    for(auto v: sampling_vars) {
        uint32_t min_props = 0;
        Lit l(v, false);
        if(solver->probe(l, min_props) == l_False) return false;
    }
    s = "must-scc-vrepl";
    if (solver->simplify(nullptr, &s) == l_False) return false;
    solver->set_verbosity(std::max<int>(conf.verb-2, 0));
    remove_zero_assigned_literals(true);
    remove_eq_literals();

    verb_print(1, "[arjun-simp] probe"
        << " removed: " << (old_size-sampling_vars.size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_vars.size(), old_size)
        << " T: " << (cpuTime() - my_time));

    return true;
}

enum class GateT {or_gate, xor_gate, ite_gate};

struct GateOccurs
{
    GateOccurs(GateT _t, uint32_t _at) :
        t(_t),
        at(_at)
    {}

    GateT t;
    uint32_t at;
};

bool Minimize::remove_definable_by_gates() {
    double my_time = cpuTime();
    order_sampl_set_for_simp();
    uint32_t old_size = sampling_vars.size();
    vector<vector<GateOccurs>> vars_gate_occurs(orig_num_vars);
    vector<pair<vector<uint32_t>, bool>> xors;
    vector<OrGate> ors;
    vector<ITEGate> ites;

    assert(toClear.empty());

    if (conf.xor_gates_based) xors = solver->get_recovered_xors(false);
    if (conf.or_gate_based) ors = solver->get_recovered_or_gates();
    if (conf.ite_gate_based) ites = solver->get_recovered_ite_gates();

    for(auto v: sampling_vars) {
        toClear.push_back(v);
        seen[v] = 1;
    }

    vector<uint32_t> rhs_incidence(solver->nVars(), 0);

    //Build occur for XOR
    uint32_t potential = 0;
    for(uint32_t i = 0; i < xors.size(); i ++) {
        const auto& x = xors[i];
        uint32_t num = 0;
        bool all_orig = true;
        for(auto v: x.first) {
            if (v < orig_num_vars) {
                num += seen[v];
            } else {
                all_orig = false;
                break;
            }
        }
        //This one can be used to remove a variable
        if (all_orig && num == x.first.size()) {
            for(const uint32_t v: x.first) {
                rhs_incidence[v]++;
                vars_gate_occurs[v].push_back(GateOccurs(GateT::xor_gate, i));
                potential++;
            }
        }
    }

    //Build occur for OR
    for(uint32_t i = 0; i < ors.size(); i ++) {
        const auto& orgate = ors[i];
        uint32_t num = 0;
        bool all_orig = true;
        for(const Lit& l: orgate.lits) {
            if (l.var() < orig_num_vars) num += seen[l.var()];
            else {
                all_orig = false;
                break;
            }
        }
        if (orgate.rhs.var() < orig_num_vars) num += seen[orgate.rhs.var()];
        else {
            all_orig = false;
            break;
        }
        //This one can be used to remove a variable
        if (all_orig && num == orgate.lits.size()+1) {
            rhs_incidence[orgate.rhs.var()]++;
            vars_gate_occurs[orgate.rhs.var()].push_back(GateOccurs(GateT::or_gate, i));
            potential++;
        }
    }

    //Build occur for ITE
    for(uint32_t i = 0; i < ites.size(); i ++) {
        const auto& itegate = ites[i];
        uint32_t num = 0;
        bool all_orig = true;
        for(const Lit& l: itegate.get_all()) {
            if (l.var() < orig_num_vars) {
                num += seen[l.var()];
            } else {
                all_orig = false;
                break;
            }
        }
        //This one can be used to remove a variable
        if (all_orig && num == itegate.get_all().size()) {
            rhs_incidence[itegate.rhs.var()]++;
            vars_gate_occurs[itegate.rhs.var()].push_back(GateOccurs(GateT::ite_gate, i));
            potential++;
        }
    }

    verb_print(4, "[arjun-simp] XOR Potential: " << potential);

    order_sampl_set_for_simp();
    uint32_t non_zero_occs = 0;

    // If this is large, it means it'd get removed anyway:
    //       bottom of the pie, we go through the pile in reverse order to try to remove
    vector<double> var_to_rel_position(orig_num_vars, 1.0);
    for(uint32_t i = 0; i < sampling_vars.size(); i++) {
        assert(sampling_vars.at(i) < orig_num_vars);
        var_to_rel_position[sampling_vars.at(i)] = (double)(sampling_vars.size()-i)/(double)sampling_vars.size();
    }

    for(uint32_t v: sampling_vars) {
        assert(seen[v]);
        if (vars_gate_occurs[v].empty()) continue;

        // Only try removing if it's at the bottom X percent of unknown_sort
        // If 0.01 is SMALLER, then we have to remove with backward LESS
        if (var_to_rel_position[v] < conf.no_gates_below) continue;

        non_zero_occs++;
        //cout << "Trying to define var " << v << " size of lookup: " << vars_xor_occurs[v].size() << endl;

        //Define v as a function of the other variables in the XOR
        for(const auto& gate: vars_gate_occurs[v]) {
            if (gate.t == GateT::xor_gate) {
                const auto& x = xors[gate.at];
                bool ok = true;
                bool found_v = false;
                for(auto xor_v: x.first) {
                    //Have they been removed from sampling set in the meanwhile?
                    if (!seen[xor_v]) {
                        ok = false;
                        break;
                    }
                    if (xor_v == v) {
                        found_v = true;
                    }
                }
                if (!ok) {
                    //In the meanwhile, the variable that could define this
                    //have been set to be defined themselves. Cycle could happen.
                    continue;
                }

                //All good, we can define v in terms of the other variables
                assert(found_v);
                seen[v] = 0;
                break;
            } else if (gate.t == GateT::or_gate) {
                const auto& o = ors[gate.at];
                bool ok = true;
                for(auto& or_l: o.get_lhs()) {
                    if (!seen[or_l.var()]) {
                        ok = false;
                        break;
                    }
                }
                if (!ok) {
                    //In the meanwhile, the variable that could define this
                    //have been set to be defined themselves. Cycle could happen.
                    continue;
                }
                seen[v] = 0;
                break;
            } else if (gate.t == GateT::ite_gate) {
                const auto& ite = ites[gate.at];
                bool ok = true;
                for(auto& ite_l: ite.lhs) {
                    if (!seen[ite_l.var()]) {
                        ok = false;
                        break;
                    }
                }
                if (!ok) {
                    //In the meanwhile, the variable that could define this
                    //have been set to be defined themselves. Cycle could happen.
                    continue;
                }
                seen[v] = 0;
                break;
            } else {
                assert(false);
            }
        }
    }

    vector<uint32_t> new_sampl_set;
    for(auto v: toClear) {
        if (seen[v]) new_sampl_set.push_back(v);
        seen[v] = 0;
    }
    toClear.clear();

    bool changed = sampling_vars.size() > new_sampl_set.size();
    std::swap(sampling_vars, new_sampl_set);

    verb_print(1, "[arjun-simp] GATE-based"
        << " Potential was: " << potential
        << " Non-zero OCCs were: " << non_zero_occs
        << " removed: " << (old_size-sampling_vars.size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_vars.size(), old_size)
        << " T: " << (cpuTime() - my_time));

    return changed;
}

void Minimize::order_sampl_set_for_simp()
{
    get_incidence();
    sort_unknown(sampling_vars, incidence);
    std::reverse(sampling_vars.begin(), sampling_vars.end()); //we want most likely independent as last
}

void Minimize::get_empty_occs() {
    const double my_time = cpuTime();
    uint32_t old_size = sampling_vars.size();

    solver->set_verbosity(std::max<int>(conf.verb-2, 0));
    solver->clean_sampl_get_empties(sampling_vars, empty_sampling_vars);

    verb_print(1, "[arjun-simp] get-empties"
        << " removed: " << (old_size-sampling_vars.size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_vars.size(), old_size)
        << " total empties now: " << empty_sampling_vars.size()
        << " T: " << std::setprecision(2) << cpuTime() - my_time);
    solver->set_verbosity(std::max<int>(conf.verb-2, 0));
}

void Minimize::remove_definable_by_irreg_gates() {
    assert(conf.irreg_gate_based);
    double my_time = cpuTime();
    uint32_t old_size = sampling_vars.size();
    order_sampl_set_for_simp();

    sampling_vars = solver->remove_definable_by_irreg_gate(sampling_vars);

    verb_print(1, "[arjun-simp] IRREG-GATE-based"
        << " removed: " << (old_size-sampling_vars.size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_vars.size(), old_size)
        << " T: " << (cpuTime() - my_time));
}

void Minimize::remove_zero_assigned_literals(bool print) {
    seen.clear();
    seen.resize(solver->nVars(), 0);

    const auto orig_sampling_set_size = sampling_vars.size();
    for(auto x: sampling_vars) seen[x] = 1;

    const auto zero_ass = solver->get_zero_assigned_lits();
    for(Lit l: zero_ass) seen[l.var()] = 0;

    sampling_vars.clear();
    for(uint32_t i = 0; i < seen.size() && i < orig_num_vars; i++) {
        if (seen[i]) sampling_vars.push_back(i);
        seen[i] = 0;
    }

    if (print) verb_print(1,"[arjun-simp] Removed set       : "
        << (orig_sampling_set_size - sampling_vars.size())
        << " new size: " << sampling_vars.size());
}

void Minimize::remove_eq_literals() {
    seen.clear();
    seen.resize(solver->nVars(), 0);

    bool go_again;
    uint32_t orig_sampling_set_size = sampling_vars.size();
    for(auto x: sampling_vars) seen[x] = 1;
    do {
        go_again = false;
        std::string s("must-scc-vrepl, clean-cls, sub-impl");
        solver->simplify(nullptr, &s);

        // [ replaced, replaced_with ]
        const auto eq_lits = solver->get_all_binary_xors();
        for(auto mypair: eq_lits) {
            if (seen[mypair.second.var()] && seen[mypair.first.var()]) {
                seen[mypair.first.var()] = 0;
                go_again = true;
            }
        }
    } while(go_again);

    sampling_vars.clear();
    for(uint32_t i = 0; i < seen.size() && i < orig_num_vars; i++) {
        if (seen[i]) sampling_vars.push_back(i);
        seen[i] = 0;
    }

    verb_print(1, "[arjun-simp] Removed eq lits: "
        << (orig_sampling_set_size - sampling_vars.size())
        << " new size: " << sampling_vars.size());
}

void Minimize::run_autarkies() {
    double my_time = cpuTime();
    int ret = 1;
    int at = 0;
    uint32_t set = 0;
    while (ret) {
        const vector<vector<Lit>> cnf;
        string s = string("clean-cls, must-scc-vrepl");
        if (solver->simplify(nullptr, &s) == l_False) return;

        vector<uint32_t> units;
        solver->start_getting_constraints(false);
        vector<vector<Lit>> cls;
        bool is_xor, rhs;
        uint32_t nvars = solver->nVars();
        vector<Lit> cl;
        while(solver->get_next_constraint(cl, is_xor, rhs)) {
            assert(!is_xor); assert(rhs);
            if (cl.size() == 1) units.push_back(cl[0].var());
            else cls.push_back(cl);
        }
        solver->end_getting_constraints();
        std::ofstream f("autarky-" + std::to_string(at) + ".cnf");
        f << "p cnf " << nvars << " " << cls.size() << endl;
        for(const auto& c: cls) {
            for(const auto& l: c) f << l << " ";
            f << "0" << endl;
        }
        f.close();

        ArjunCCNR::Ganak_ccnr ccnr(conf.verb);
        vector<uint32_t> notouch_vars(sampling_vars);
        for(auto v: units) notouch_vars.push_back(v);

        ret = ccnr.main(cls, nvars, notouch_vars, conf.autarkies);
        if (ret == 1) {
            auto model = ccnr.get_model();
            for(uint32_t i = 0; i < model.size(); i++) {
                if (model[i] != l_Undef) {
                    auto lit = Lit(i, model[i] == l_False);
                    solver->add_clause({lit});
                    set++;
                    /* cout << "c [AUTARKY] at " << at << " set " << lit << endl; */
                }
            }
        }
        at++;
    }

    verb_print(1, "[arjun-simp] AUTARY set:" << set << " T: " << (cpuTime() - my_time));
}

