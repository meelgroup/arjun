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

void Common::fill_assumptions_backward(
    vector<Lit>& assumptions,
    vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const vector<uint32_t>& indep)
{
    cout << "Filling assumps BEGIN" << endl;
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);
        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);
        // cout << "assump indic for var: " << var << endl;
        assumptions.push_back(Lit(indic, true));
    }
    
    // We need to group the "unknown" variables by their groups, if
    // applicable. This helper array is meant to do that.
    vector<bool> added (orig_num_vars, false);
    cout << "unknown.size() = " << unknown.size() << endl;
    cout << "assumptions.size() = " << assumptions.size() << endl;

    uint32_t j = 0;
    for(uint32_t i = 0; i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        if (unknown_set[var] == 0) continue;

        assert(var < orig_num_vars);
        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);

        if (conf.group_indep && in_variable_group(var)) {
            if (!added[var]) {
                // cout << "var " << var << " was not yet added, adding now" << endl;
                for (auto& grp_var: var_groups[var2var_group[var]]) {
                    unknown[j++] = grp_var;
                    indic = var_to_indic[grp_var];
                    assert(indic != var_Undef);
                    assumptions.push_back(Lit(indic, true));
                    assert(!added[grp_var]);
                    added[grp_var] = true;
                    i++;
                }
                i--;
            } else {
                cout << "var " << var << " was already added" << endl;
            }
        } else {
            unknown[j++] = var;
            assert(indic != var_Undef);
            assumptions.push_back(Lit(indic, true));
        }

        if (conf.verb > 5) {
            cout << "Filled assump with unknown: " << var << endl;
        }
    }
    unknown.resize(j);
    cout << "Filling assumps END, total unknown size: " << unknown.size() << endl;
}

void Common::backward_round()
{
    for(const auto& x: seen) assert(x == 0);

    double start_round_time = cpuTimeTotal();
    //start with empty independent set
    vector<uint32_t> indep;
    vector<uint32_t> unknown;
    vector<char> unknown_set;
    unknown_set.resize(orig_num_vars, 0);
    for(const auto& x: *sampling_set) {
        assert(x < orig_num_vars);
        if (conf.group_indep && in_variable_group(x)) {
            for (auto& grp_var: var_groups[get_group_idx(x)]) {
                if (unknown_set[grp_var] == 0) {
                    unknown.push_back(grp_var);
                    unknown_set[grp_var] = 1;
                }
            }
        } else {
            assert(unknown_set[x] == 0 && "No var should be in 'sampling_set' twice!");
            unknown.push_back(x);
            unknown_set[x] = 1;
        }
    }

    // TODO: bring back sorting! But respecting the groups!
    if (conf.group_indep) {
        cout << "c [arjun] WARNING: no sorting in grouped independent support setting!" << endl;
    } else {
        sort_unknown(unknown);
    }
    if (conf.verb >= 4) {
        cout << "Sorted output: "<< endl;
        for (const auto& v:unknown) {
            cout
            << "Var: " << std::setw(6) << v
            << " inc: " << std::setw(6) << incidence[v]
            << " prop-inc: " << std::setw(6) << incidence_probing[v];
            if (var_to_num_communities.size() > v) {
                cout << " fan-out to comms: " << std::setw(6) << var_to_num_communities[v].size();
            }
            cout << endl;
        }
    }

    if (conf.verb) {
        cout << "c [arjun] Start unknown size: " << unknown.size() << endl;
    }

    vector<Lit> assumptions;
    uint32_t iter = 0;
    uint32_t not_indep = 0;

    double myTime = cpuTime();

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_set->size()) > 20 ) {
        uint32_t will_do_iters = sampling_set->size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    uint32_t fast_backw_calls = 0;
    uint32_t fast_backw_max = 0;
    uint32_t fast_backw_tot = 0;
    vector<uint32_t> non_indep_vars;

    while(true) {
        uint32_t test_var = var_Undef;
        cout << "new iteration!" << endl;
        cout << "assumptions.size() = " << assumptions.size() << endl;

        while(!unknown.empty()) {
            uint32_t var = unknown[unknown.size()-1];
            unknown.pop_back();

            if (unknown_set[var]) {
                test_var = var;
                //Remove all in group
                if (get_group_idx(var) != 0) {
                    for(uint32_t i = 1; i < var_groups[get_group_idx(test_var)].size(); i++) {
                        assert(!unknown.empty());
                        uint32_t v2 = unknown[unknown.size()-1];
                        assert(get_group_idx(v2) == get_group_idx(var));
                        assert(unknown_set[v2]);
                        unknown_set[v2] = 0;
                        unknown.pop_back();
                    }
                }
                break;
            }
        }

        if (test_var == var_Undef) {
            cout << "c [arjun] we are done, backward is finished" << endl;
            break;
        }

        assert(test_var < orig_num_vars);
        assert(unknown_set[test_var] == 1);
        unknown_set[test_var] = 0;
        
        cout << "Testing: " << test_var << endl;
        cout << "unknown.size() = " << unknown.size() << endl;

        //Assumption filling
        assert(test_var != var_Undef);
        fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
        
        lbool ret = l_Undef;
        assert(test_var != var_Undef);
        if (get_group_idx(test_var) != 0) {
            const uint32_t orig_ass_size = assumptions.size();
            for (auto& v: var_groups[get_group_idx(test_var)]) {
                assumptions.push_back(Lit(v, false));
                assumptions.push_back(Lit(v + orig_num_vars, true));
                solver->set_max_confl(conf.backw_max_confl);
                ret = solver->solve(&assumptions);
                if (ret == l_Undef || ret == l_True) break;
                assumptions.resize(orig_ass_size);
            }
            cout << "Final ret: " << ret << endl;
        } else {
            assumptions.push_back(Lit(test_var, false));
            assumptions.push_back(Lit(test_var + orig_num_vars, true));
            solver->set_max_confl(conf.backw_max_confl);
            ret = solver->solve(&assumptions);
        }
        solver->set_no_confl_needed();
        
        // TODO: make grouped variables compatible with fast_backw
        if (ret == l_False) {
            ret_false++;
            if (conf.verb >= 5) cout << "c [arjun] backw solve(): False" << endl;
        } else if (ret == l_True) {
            ret_true++;
            if (conf.verb >= 5) cout << "c [arjun] backw solve(): True" << endl;
        } else if (ret == l_Undef) {
            if (conf.verb >= 5) cout << "c [arjun] backw solve(): Undef" << endl;
            ret_undef++;
        }

        cout << "ret = " << ret << endl;

        // cout << "unknown_set:" << endl;
        // for (uint32_t i = 0; i < unknown_set.size(); i++) {
        //     cout << "unknown_set[" << std::setw(3) << i << "] = " << (int)unknown_set[i] << endl;
        // }

        // TODO: come up with an equivalent assertion for group mode.
        if (!conf.group_indep) {
            assert(unknown_set[test_var] == 0);
        }
        
        if (ret == l_Undef || //Timed out, we'll treat is as unknown
            ret == l_True)    //Independent
        {   
            assert(test_var < orig_num_vars);
            if (in_variable_group(test_var)) {
                cout << "Group " <<  var2var_group[test_var] << " is independent" << endl;
                for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
                    cout << "Pushing " << grp_var << " to indep." << endl;
                    indep.push_back(grp_var);
                }
            } else {
                cout << "Pushing " <<  test_var << " to indep." << endl;
                indep.push_back(test_var);
            }
        } else if (ret == l_False) {
            //not independent
            //i.e. given that all in indep+unkown is equivalent, it's not possible that a1 != b1
            cout << "Variable " << test_var << " is NOT independent" << endl;
            not_indep++;
        }

        if (iter % mod == (mod-1) && conf.verb) {
            //solver->remove_and_clean_all();
            cout
            << "c [arjun] iter: " << std::setw(5) << iter;
            if (mod == 1) {
                cout
                << " ret: " << std::setw(8) << ret;
            } else {
                cout
                << " T/F/U: ";
                std::stringstream ss;
                ss << ret_true << "/" << ret_false << "/" << ret_undef;
                cout << std::setw(10) << std::left << ss.str() << std::right;
                ret_true = 0;
                ret_false = 0;
                ret_undef = 0;
            }
            cout
            << " by: " << std::setw(3) << 1
            << " U: " << std::setw(7) << unknown.size()
            << " I: " << std::setw(7) << indep.size()
            << " N: " << std::setw(7) << not_indep
            ;
            if (conf.fast_backw) {
                cout << " backb avg:" << std::setprecision(1) << std::setw(7)
                << (double)fast_backw_tot/(double)fast_backw_calls
                << " backb max:" << std::setw(7) << fast_backw_max;
            }
            cout << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
            << endl;
            myTime = cpuTime();
            fast_backw_tot = 0;
            fast_backw_calls = 0;
            fast_backw_max = 0;
        }
        iter++;
        cout << "printed stats" << endl;
        if (iter % 500 == 499) {
            update_sampling_set(unknown, unknown_set, indep);
        }
    }
    update_sampling_set(unknown, unknown_set, indep);

    if (conf.verb) {
        cout << "c [arjun] backward round finished T: "
        << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
        << endl;
    }
    if (conf.verb >= 2) {
        solver->print_stats();
    }
}
