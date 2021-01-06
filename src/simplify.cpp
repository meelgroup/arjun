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

bool Common::simplify_intree_probe_xorgates_normgates_probe()
{
    assert(solver->okay());
    auto old_size = sampling_set->size();
    double myTime = cpuTime();

    solver->set_verbosity(0);
    if (conf.or_gate_based) {
        remove_definable_by_gates();
    }

    if (conf.pre_simplify) {
        if (conf.verb) {
            cout << "c [arjun-simp] CMS::simplify() with no BVE, intree probe..." << endl;
        }
        double simpTime = cpuTime();
        solver->set_verbosity(std::max((int)conf.verb-2, 0));
        solver->set_no_bve();
        solver->set_intree_probe(1);
        if (solver->simplify() == l_False) {
            return false;
        }
        solver->set_intree_probe(conf.intree);
        solver->set_verbosity(std::max((int)conf.verb-2, 0));
        if (conf.verb) {
            cout << "c [arjun-simp] CMS::simplify() with no BVE finished. T: "
            << (cpuTime() - simpTime)
            << endl;
        }
    }

    if (conf.xor_gates_based) {
        bool changed = true;
        while(changed) {
            changed = remove_definabile_by_xor();
        }
    }
    remove_eq_literals();
    remove_zero_assigned_literals();
    if (conf.or_gate_based) {
        remove_definable_by_gates();
    }

    if (conf.probe_based) {
        if (!probe_all()) {
            return false;
        }
    }
    solver->set_verbosity(std::max<int>((int)conf.verb-2, 0));

    if (conf.verb) {
        cout << "c [arjun] Arjun simplification finished "
        << " removed: " << (old_size-sampling_set->size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_set->size(), old_size)
        << " T: " << (cpuTime() - myTime)
        << endl;
    }

    return true;
}

bool Common::probe_all()
{
    double myTime = cpuTime();
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

bool Common::remove_definabile_by_xor()
{
    double myTime = cpuTime();
    uint32_t old_size = sampling_set->size();
    vector<vector<uint32_t>> vars_xor_occurs(orig_num_vars);

    assert(toClear.empty());
    auto xors = solver->get_recovered_xors(true);
    for(auto v: *sampling_set) {
        toClear.push_back(v);
        seen[v] = 1;
    }

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
            for(auto v: x.first) {
                vars_xor_occurs[v].push_back(i);
                potential++;
            }
        }
    }
    if (conf.verb > 4) {
        cout << "c [arjun-simp] XOR Potential: " << potential << endl;
    }

    /*NOTE: there are a few ways to sort. But we want to sort NOT
            to optimize what we remove NOW. Instead, we should optimize what
            removes most once EVERYTHING runs. The best NOW would be
            //std::sort(sampling_set->begin(), sampling_set->end(), OccurSorter(vars_xor_occurs));
            --> This sorts with lowest occur numbers first
            --> So we have the highest chance that we can set defined later variables

            Instead, we should sort by reverse incidence, as that's the one
            that will be the right order in the long run.
    */
    std::sort(sampling_set->begin(), sampling_set->end(), IncidenceSorter<uint32_t>(incidence));
    std::reverse(sampling_set->begin(), sampling_set->end());
    uint32_t non_zero_occs = 0;
    uint32_t seen_set_0 = 0;
    for(uint32_t v: *sampling_set) {
        assert(seen[v]);
        if (vars_xor_occurs[v].size() == 0) {
            continue;
        }
        non_zero_occs++;
//         cout << "Do something with v " << v << " size: " << vars_xor_occurs[v].size() << endl;

        //Define v as a function of the other variables in the XOR
        for(uint32_t o: vars_xor_occurs[v]) {
            const auto& x = xors[o];
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
        }
    }
    if (conf.verb) {
        cout << "c [arjun-simp] XOR-based"
        << " Potential was: " << potential
        << " Non-zero OCCs were: " << non_zero_occs
        << " seen_set_0: " << seen_set_0 << endl;
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
        cout << "c [arjun-simp] XOR-based"
        << " removed: " << (old_size-sampling_set->size())
        << " perc: " << std::fixed << std::setprecision(2)
        << stats_line_percent(old_size-sampling_set->size(), old_size)
        << " T: " << (cpuTime() - myTime) << endl;
    }

    return changed;
}

void Common::remove_definable_by_gates()
{
    double myTime = cpuTime();

    if (conf.verb) {
        cout << "c [arjun-simp] attempting gate-based..." << endl;
    }


    bool changed = true;
    uint32_t iter = 0;
    while (changed) {
        auto old_size = sampling_set->size();
        vector<uint32_t> definable = solver->get_definabe(*sampling_set);

        for(auto v: definable) {
            assert(v < orig_num_vars);
            seen[v] = 1;
        }

        other_sampling_set->clear();
        for(auto v: *sampling_set) {
            if (seen[v] == 0) {
                other_sampling_set->push_back(v);
            }
        }

        //cleanup
        for(auto v: definable) {
            seen[v] = 0;
        }


        changed = sampling_set->size() > other_sampling_set->size();
        //TODO atomic swap
        std::swap(sampling_set, other_sampling_set);

        if (conf.verb) {
            cout << "c [arjun-simp] gate-based"
            << " iter: " << iter
            << " removed: " << (old_size-sampling_set->size())
            << " perc: " << std::fixed << std::setprecision(2)
            << stats_line_percent(old_size-sampling_set->size(), old_size)
            << " T: " << (cpuTime() - myTime) << endl;
        }
        iter++;
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
    *other_sampling_set = *sampling_set;

    uint32_t orig_sampling_set_size = other_sampling_set->size();
    for(auto x: *other_sampling_set) {
        seen[x] = 1;
    }
    const auto zero_ass = solver->get_all_binary_xors();
    for(auto mypair: zero_ass) {
        //Only remove if both are sampling vars
        if (seen[mypair.second.var()] == 1 && seen[mypair.first.var()] == 1) {
            //Doesn't matter which one to remove
            seen[mypair.second.var()] = 0;
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
        cout << "c [arjun-simp] Removed equivalent: "
        << (orig_sampling_set_size - sampling_set->size())
        << " new size: " << sampling_set->size()
        << endl;
    }
}
