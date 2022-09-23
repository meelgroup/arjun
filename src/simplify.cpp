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

#include <algorithm>
#include <random>
#include "common.h"

using std::pair;
using namespace ArjunInt;

void Common::check_no_duplicate_in_sampling_set()
{
    for(auto const& v: *sampling_set) {
        if (seen[v]) {
            cout << "Variable " << v+1 << " in sampling set twice!" << endl;
            assert(false);
        }
        seen[v] = 1;
    }
    for(auto const& v: *sampling_set) seen[v] = 0;
}

bool Common::simplify()
{
    assert(conf.simp);
    check_no_duplicate_in_sampling_set();
    auto old_size = sampling_set->size();
    double myTime = cpuTime();

    if (conf.xor_gates_based || conf.or_gate_based || conf.ite_gate_based) {
        remove_definable_by_gates();
    }
    if (conf.irreg_gate_based) remove_definable_by_irreg_gates();
    if (conf.empty_occs_based) find_equiv_subformula();

    if (conf.pre_simplify) {
        verb_print(1, "[arjun-simp] CMS::simplify() with no BVE, intree probe...");
        double simpTime = cpuTime();
        solver->set_bve(0);
        solver->set_intree_probe(1);
        if (solver->simplify() == l_False) return false;
        solver->set_intree_probe(conf.intree);
        verb_print(1,"[arjun-simp] CMS::simplify() with no BVE finished."
            << " T: " << (cpuTime() - simpTime));
    }

    if (conf.backbone_simpl) {
        if (!backbone_simpl()) return false;
    } else {
        // Find at least one solution (so it's not UNSAT) within some timeout
        solver->set_verbosity(0);
        solver->set_max_confl(1000);
        lbool ret = solver->solve();
        if (ret == l_True) definitely_satisfiable = true;
        solver->set_verbosity(std::max<int>(conf.verb-2, 0));
    }

    remove_eq_literals();
    remove_zero_assigned_literals();
    if (conf.probe_based && !probe_all()) return false;

    if (conf.empty_occs_based) find_equiv_subformula();
    if (conf.irreg_gate_based) remove_definable_by_irreg_gates();

    solver->set_verbosity(std::max<int>(conf.verb-2, 0));

    verb_print(1, "[arjun] simplification finished "
        << " removed: " << (old_size-sampling_set->size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_set->size(), old_size)
        << " T: " << (cpuTime() - myTime));

    check_no_duplicate_in_sampling_set();
    return true;
}

struct IncSorterAsc
{
    IncSorterAsc(const vector<uint32_t>& _inc) :
        inc(_inc)
    {}

    bool operator()(const uint32_t a, const uint32_t b) const {
        //Return that the order is OK when "a" has less incidence than "b"
        return inc[a] < inc[b];
    }

    const vector<uint32_t>& inc;
};

bool Common::backbone_simpl()
{
    if (conf.verb) {
        cout << "c [backbone-simpl] starting backbone simplification..." << endl;
    }
    uint64_t last_sum_conflicts = 0;
    int64_t max_confl = conf.backbone_simpl_max_confl;

    solver->set_verbosity(0);
    double myTime = cpuTime();
    uint32_t orig_vars_set = solver->get_zero_assigned_lits().size();
    bool finished = false;
    Lit l;

    vector<Lit> tmp_clause;
    vector<Lit> assumps;
    vector<lbool> model;
    vector<char> model_enabled;
    const auto old_polar_mode = solver->get_polarity_mode();
    solver->set_polarity_mode(PolarityMode::polarmode_neg);

    vector<Lit> zero_set = solver->get_zero_assigned_lits();
    for(auto const& l2: zero_set) seen[l2.var()] = 1;
    for(auto const& v: empty_occs) seen[v] = 1;
    vector<uint32_t> var_order;
    for(uint32_t i = 0, max = solver->nVars(); i < max; i++) {
        if (seen[i]) continue;
        var_order.push_back(i);
    }
    for(auto const& l2: zero_set) seen[l2.var()] = 0;
    for(auto const& v: empty_occs) seen[v] = 0;
    if (var_order.empty()) return true;

    std::mt19937 g;
    g.seed(1337);
    std::shuffle(var_order.begin(), var_order.end(), g);

    solver->set_max_confl(max_confl);
//     cout << "c [backbone] sum conf: " << solver->get_sum_conflicts() << endl;
    max_confl -= solver->get_sum_conflicts();
    last_sum_conflicts = solver->get_sum_conflicts();
    lbool ret = solver->solve();
    if (ret == l_False) {
        return false;
    }
    if (ret == l_Undef || max_confl < 0) {
        goto end;
    }

    model = solver->get_model();
    model_enabled.resize(solver->nVars(), 1);

    for(const uint32_t var: var_order) {
        if (!model_enabled[var]) {
            continue;
        }

        l = Lit(var, model[var] == l_False);

        //There is definitely a solution with "l". Let's see if ~l fails.
        assumps.clear();
        assumps.push_back(~l);
//         cout << "c [backbone]  assumps: " << endl;
//         for (auto const& l2: assumps) cout << l2 << " , ";
//         cout << " -- sum conf: " << solver->get_sum_conflicts() << endl;
        solver->set_max_confl(max_confl);
        ret = solver->solve(&assumps);

        //Update max confl
        assert(last_sum_conflicts <= solver->get_sum_conflicts());
        max_confl -= ((int64_t)solver->get_sum_conflicts() - last_sum_conflicts);
        max_confl -= 100;
        last_sum_conflicts = solver->get_sum_conflicts();
//         cout << "max_confl: " << max_confl << endl;

        //Check return value
        if (ret == l_True) {
            const auto& this_model = solver->get_model();
            for(uint32_t i2 = 0, max = solver->nVars(); i2 < max; i2++) {
                if (this_model[i2] != model[i2]) {
                    model_enabled[i2] = 0;
                }
            }
        } else if (ret == l_False) {
            tmp_clause.clear();
            tmp_clause.push_back(l);
            if (!solver->add_clause(tmp_clause)) {
                return false;
            }
        }
        if (ret == l_Undef || max_confl < 0) {
            goto end;
        }
    }
    finished = true;
    assert(solver->okay());

    end:
    uint32_t num_set = solver->get_zero_assigned_lits().size() - orig_vars_set;
    double time_used = cpuTime() - myTime;
    solver->set_polarity_mode(old_polar_mode);

    if (conf.verb) {
        if (!finished) {
            cout << "c [backbone-simpl] "
            << "skipping, taking more than max conflicts:"
            << print_value_kilo_mega(conf.backbone_simpl_max_confl)
            << endl;
        }
        cout << "c [backbone-simpl]"
        << " set: " << num_set
        << " conflicts used: " << print_value_kilo_mega(solver->get_sum_conflicts())
        << " conflicts max: " << print_value_kilo_mega(conf.backbone_simpl_max_confl)
        << " T: " << std::setprecision(2) << time_used
        << endl;
    }
    solver->set_verbosity(std::max<int>(conf.verb-2, 0));

    return true;
}

void Common::empty_out_indep_set_if_unsat()
{
    if (solver->okay()) return;

    //It's UNSAT so the sampling set is empty
    other_sampling_set->clear();
    std::swap(sampling_set, other_sampling_set);
    empty_occs.clear();
    if (conf.verb) {
        cout << "c [arjun] CNF is UNSAT, setting sampling set to empty"
        << endl;
    }
}

bool Common::probe_all()
{
    double myTime = cpuTime();
    order_sampl_set_for_simp();
    auto old_size = sampling_set->size();

    incidence_probing.resize(orig_num_vars, 0);
    for(auto v: *sampling_set) {
        uint32_t min_props = 0;
        Lit l(v, false);
        if(solver->probe(l, min_props) == l_False) {
            return false;
        }
        incidence_probing[v] = min_props;
    }
    string s("must-scc-vrepl");
    if (solver->simplify(NULL, &s) == l_False) {
        return false;
    }
    solver->set_verbosity(std::max<int>(conf.verb-2, 0));
    remove_zero_assigned_literals(true);
    remove_eq_literals(true);

    if (conf.verb) {
        cout << "c [arjun-simp] probe"
        << " removed: " << (old_size-sampling_set->size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_set->size(), old_size)
        << " T: " << (cpuTime() - myTime) << endl;
    }

    return true;
}

struct OccurSorter {
    OccurSorter(const vector<vector<uint32_t>>& _occ) :
        occ(_occ)
    {}

    bool operator()(uint32_t v1, uint32_t v2) const {
        return occ[v1].size() < occ[v2].size();
    }

    const vector<vector<uint32_t>>& occ;

};

enum class gate_t {or_gate, xor_gate, ite_gate};

struct GateOccurs
{
    GateOccurs(gate_t _t, uint32_t _at) :
        t(_t),
        at(_at)
    {}

    gate_t t;
    uint32_t at;
};

bool Common::remove_definable_by_gates()
{
    double myTime = cpuTime();
    order_sampl_set_for_simp();
    uint32_t old_size = sampling_set->size();
    vector<vector<GateOccurs>> vars_gate_occurs(orig_num_vars);
    vector<pair<vector<uint32_t>, bool>> xors;
    vector<OrGate> ors;
    vector<ITEGate> ites;

    assert(toClear.empty());

    if (conf.xor_gates_based) xors = solver->get_recovered_xors(false);
    if (conf.or_gate_based) ors = solver->get_recovered_or_gates();
    if (conf.ite_gate_based) ites = solver->get_recovered_ite_gates();

    for(auto v: *sampling_set) {
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
                vars_gate_occurs[v].push_back(GateOccurs(gate_t::xor_gate, i));
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
            vars_gate_occurs[orgate.rhs.var()].push_back(GateOccurs(gate_t::or_gate, i));
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
            vars_gate_occurs[itegate.rhs.var()].push_back(GateOccurs(gate_t::ite_gate, i));
            potential++;
        }
    }


    if (conf.verb > 4) cout << "c [arjun-simp] XOR Potential: " << potential << endl;

    order_sampl_set_for_simp();
    uint32_t non_zero_occs = 0;
    uint32_t seen_set_0 = 0;
    for(uint32_t v: *sampling_set) {
        assert(seen[v]);
        if (vars_gate_occurs[v].size() == 0) {
            continue;
        }
        non_zero_occs++;
        //cout << "Trying to define var " << v << " size of lookup: " << vars_xor_occurs[v].size() << endl;

        //Define v as a function of the other variables in the XOR
        for(const auto& gate: vars_gate_occurs[v]) {
            if (gate.t == gate_t::xor_gate) {
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
                seen_set_0++;
                break;
            } else if (gate.t == gate_t::or_gate) {
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
                seen_set_0++;
                break;
            } else if (gate.t == gate_t::ite_gate) {
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
                seen_set_0++;
                break;
            } else {
                assert(false);
            }
        }
    }

    other_sampling_set->clear();
    for(auto v: toClear) {
        if (seen[v]) {
            other_sampling_set->push_back(v);
        }
        seen[v] = 0;
    }
    toClear.clear();

    bool changed = sampling_set->size() > other_sampling_set->size();
    //TODO atomic swap
    std::swap(sampling_set, other_sampling_set);

    if (conf.verb) {
        cout << "c [arjun-simp] GATE-based"
        << " Potential was: " << potential
        << " Non-zero OCCs were: " << non_zero_occs
        << " removed: " << (old_size-sampling_set->size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_set->size(), old_size)
        << " T: " << (cpuTime() - myTime) << endl;
    }

    return changed;
}

void Common::order_sampl_set_for_simp()
{
    get_incidence();
    std::sort(sampling_set->begin(), sampling_set->end(), IncidenceSorter<uint32_t>(incidence));
    std::reverse(sampling_set->begin(), sampling_set->end()); //we want most likely independent as last
}

void Common::find_equiv_subformula()
{
    assert(conf.empty_occs_based);
    const double myTime = cpuTime();
    uint32_t old_size = sampling_set->size();

    solver->set_verbosity(std::max<int>(conf.verb-2, 0));
    solver->find_equiv_subformula(*sampling_set, empty_occs, conf.mirror_empty);

    if (conf.verb) {
        cout << "c [arjun-simp] equiv-subform"
        << " removed: " << (old_size-sampling_set->size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_set->size(), old_size)
        << " total equiv_subform now: " << empty_occs.size()
        << " T: " << std::setprecision(2) << cpuTime() - myTime
        << endl;
    }
    solver->set_verbosity(std::max<int>(conf.verb-2, 0));
}

void Common::remove_definable_by_irreg_gates()
{
    assert(conf.irreg_gate_based);
    double myTime = cpuTime();
    uint32_t old_size = sampling_set->size();
    order_sampl_set_for_simp();

    *other_sampling_set = solver->remove_definable_by_irreg_gate(*sampling_set);
    std::swap(sampling_set, other_sampling_set);

    if (conf.verb) {
        cout << "c [arjun-simp] IRREG-GATE-based"
        << " removed: " << (old_size-sampling_set->size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_set->size(), old_size)
        << " T: " << (cpuTime() - myTime) << endl;
    }
}

void Common::remove_zero_assigned_literals(bool print)
{
    //Remove zero-assigned literals
    seen.clear();
    seen.resize(solver->nVars(), 0);

    *other_sampling_set = *sampling_set;
    uint32_t orig_sampling_set_size = other_sampling_set->size();
    for(auto x: *other_sampling_set) {
        seen[x] = 1;
    }
    const auto zero_ass = solver->get_zero_assigned_lits();
    for(Lit l: zero_ass) {
        seen[l.var()] = 0;
    }

    other_sampling_set->clear();
    for(uint32_t i = 0; i < seen.size() && i < orig_num_vars; i++) {
        if (seen[i]) {
            other_sampling_set->push_back(i);
        }
        seen[i] = 0;
    }
    //TODO atomic swap
    std::swap(sampling_set, other_sampling_set);

    if (print && conf.verb) {
        total_set_removed += orig_sampling_set_size - sampling_set->size();
        cout << "c [arjun-simp] Removed set       : "
        << (orig_sampling_set_size - sampling_set->size())
        << " new size: " << sampling_set->size()
        << endl;
    }
}

void Common::remove_eq_literals(bool print)
{
    uint32_t orig_sampling_set_size = sampling_set->size();
    for(auto x: *sampling_set) seen[x] = 1;
    const auto eq_lits = solver->get_all_binary_xors();
    for(auto mypair: eq_lits) {
        //Only remove if both are sampling vars
        if (seen[mypair.second.var()] == 1 && seen[mypair.first.var()] == 1) {
            seen[mypair.first.var()] = 0;
        }
    }

    other_sampling_set->clear();
    for(uint32_t i = 0; i < seen.size() && i < orig_num_vars; i++) {
        if (seen[i]) {
            other_sampling_set->push_back(i);
        }
        seen[i] = 0;
    }
    //TODO atomic swap
    std::swap(sampling_set, other_sampling_set);

    total_eq_removed += orig_sampling_set_size - sampling_set->size();

    if (print && conf.verb) {
        cout << "c [arjun-simp] Removed eq lits: "
        << (orig_sampling_set_size - sampling_set->size())
        << " new size: " << sampling_set->size()
        << endl;
    }
}
