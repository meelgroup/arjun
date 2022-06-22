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
    if (conf.verb > 5) {
        cout << "Filling assumps BEGIN" << endl;
    }
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);

        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);

        // The known independents should already contain all the grouped
        // variables. Variables belonging to the same group, should be grouped
        // in the list of known indepdents also. Therefore, there is no need 
        // for special treatment here.
        assumptions.push_back(Lit(indic, true));
        cout << "pushed indic var " << indic << " on assumptions stack" << endl;

        if (conf.verb > 5) {
            cout << "Filled assump with indep: " << var << endl;
        }
    }

    //Add unknown as assumptions, clean "unknown"
    
    // We need to group the "unknown" variables by their groups, if
    // applicable. This helper array is meant to do that.
    vector<bool> added (orig_num_vars, false);
    cout << "unknown.size() = " << unknown.size() << endl;
    cout << "assumptions.size() = " << assumptions.size() << endl;

    // We are going to fill the unknown vector with the indicator variables of
    // variables that we have not yet branched on (?).
    uint32_t j = 0;
    for(uint32_t i = 0; i < unknown.size(); i++) {
        cout << "i = " << i << endl;
        uint32_t var = unknown[i];
        // cout << "added[" << var << "] (var " << var << ") = " << added[var] << endl;
        if (unknown_set[var] == 0) {
            cout << "continue" << endl;
            continue;
        } 

        // anna: I commented this part of the function out and replaced by the
        // function below.
        // else {
        //     cout << "change unknown[ " << j << "] = " << unknown[j] << " to var " << var << endl;
        //     unknown[j++] = var;
        // }


        assert(var < orig_num_vars);
        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);

        if (conf.group_indep && in_variable_group(var)) {
            if (!added[var]) {
                cout << "var " << var << " was not yet added, adding now" << endl;
                for (auto& grp_var: var_groups[var2var_group[var]]) {
                    unknown[j++] = grp_var;
                    indic = var_to_indic[grp_var];
                    assert(indic != var_Undef);
                    assumptions.push_back(Lit(indic, true));
                    added[grp_var] = true;
                    // Continue to iterate through the array, knowin that 
                    // variables corresponding to the same group are also
                    // grouped together in the unknown stack:
                    i++;
                    cout << "pushed group var " << grp_var << " on assumptions stack" << endl;
                }
                // Since the outer loop automatically increases i, but we already
                // increased it in the inner loop, we must decrease it now
                // to make sure that we don't miss some variables.
                i--;
            } else {
                cout << "var " << var << " was already added" << endl;
            }
        } else {
            cout << "change unknown[ " << j << "] = " << unknown[j] << " to var " << var << endl;
            unknown[j++] = var;
            assert(indic != var_Undef);
            assumptions.push_back(Lit(indic, true));
            cout << "pushed non group variable " << var << " on assumptions stack"  << endl;
        }

        if (conf.verb > 5) {
            cout << "Filled assump with unknown: " << var << endl;
        }    

        // if (conf.group_indep && in_variable_group(var)) {
        //     uint32_t grp_idx = var2var_group[var];
        //     for (auto& grp_var: var_groups[grp_idx]) {
        //         indic = var_to_indic[grp_var];
        //         assert(grp_var != var_Undef);
        //         assert(indic != var_Undef);
        //         assumptions.push_back(Lit(indic, true));
        //         cout << "pushed back unknown ass " << Lit(indic, true) 
        //              << " (indic! var " << indic 
        //              << ", indic_var " << Lit(indic, true).var() << ")" << endl;
        //     }
        // } else{
        //     assumptions.push_back(Lit(indic, true));
        // }
    }
    unknown.resize(j);
    cout << "Filling assumps END, total unknown size: " << unknown.size() << endl;
    if (conf.verb > 5) {
        cout << "Filling assumps END, total assumps size: " << assumptions.size() << endl;
    }
}

void Common::backward_round()
{
    for(const auto& x: seen) {
        assert(x == 0);
    }

    double start_round_time = cpuTimeTotal();
    //start with empty independent set
    vector<uint32_t> indep;

    //Initially, all of samping_set is unknown

    // stack of variables for which we don't know if they are independent or not
    vector<uint32_t> unknown;       
    // helper array to keep track of which variables are on the unknown stack(?)
    vector<char> unknown_set;
    unknown_set.resize(orig_num_vars, 0);
    for(const auto& x: *sampling_set) {
        assert(x < orig_num_vars);
        // TODO: See if we can come up with an alternative for this assertion:
        // assert(unknown_set[x] == 0 && "No var should be in 'sampling_set' twice!");
        // I disabled it to make it possible to group variables together in
        // their variable groups.
        if (conf.group_indep && in_variable_group(x)) {
            for (auto& grp_var: var_groups[get_group_idx(x)]) {
                if (unknown_set[grp_var] == 0) {
                    unknown.push_back(grp_var);
                    cout << "Pushing var " << grp_var << " on unknown stack during init." << endl;
                    unknown_set[grp_var] = 1;
                }
            }
        } else {
            cout << "Pushing non-group var " << x << " on unknown stack during init." << endl;
            assert(unknown_set[x] == 0 && "No var should be in 'sampling_set' twice!");
            unknown.push_back(x);
            unknown_set[x] = 1;
        }
    }

    cout << "Before sorting, unknown.size() = " << unknown.size() << endl;

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
    bool quick_pop_ok = false;
    uint32_t fast_backw_calls = 0;
    uint32_t fast_backw_max = 0;
    uint32_t fast_backw_tot = 0;
    uint32_t indic_var = var_Undef;
    vector<uint32_t> non_indep_vars;
    vector<uint32_t> this_group;
    bool new_group = true;

    cout << "Start while loop, assumptions.size() = " << assumptions.size() << endl;
    while(true) {
        uint32_t test_var = var_Undef;
        cout << "new iteration!" << endl;
        cout << "assumptions.size() = " << assumptions.size() << endl;
        for (auto& a: assumptions) {
          cout << "assumption: " << a << endl;
        }
        if (quick_pop_ok) {
            cout << "quick_pop_ok" << endl;
            //Remove 2 last 
            assumptions.pop_back();
            assumptions.pop_back();

            cout << "assumptions.size() = " << assumptions.size() << endl;
            

            //No more left, try again with full
            if (assumptions.empty()) {
                if (conf.verb >= 5) cout << "c [arjun] No more left, try again with full" << endl;
                cout << "c [arjun] No more left, try again with full" << endl;
                break;
            }
          
            cout << "assumptions: " << endl;
            for (auto& ass: assumptions) {
                cout << "ass: " << ass << ", (indic_)var: " << ass.var() << endl;       
            }

            // Here we are popping assumptions that are indicator variables, and
            // branching on them.

            // If we are in group mode and are still processing a group, we
            // simply select the next group variable to branch on:
            if (conf.group_indep && !this_group.empty()) {
                cout << "Next group variable: " << this_group[this_group.size()-1] << endl;
                cout << "Corresponding indic_var: " << var_to_indic[this_group[this_group.size()-1]] << endl;;
                indic_var = var_to_indic[this_group[this_group.size()-1]];
                this_group.pop_back();
                new_group = false;
            } 
            // If we are not in group mode, or have processed the full group,
            // we simply take the next indicator variable on the assumptions
            // stack to branch on:
            else {
                indic_var = assumptions[assumptions.size()-1].var();
            }
            cout << "indic_var: " << indic_var << endl;
            cout << "corresponding var: " << indic_to_var[indic_var] << endl;
            // We have processed all elements of the previous group, so
            // now we must initialise a new this_group vector and remove
            // all group indicator variables from the assumptions stack.
            cout << "conf.group_indep = " << conf.group_indep << endl;
            // cout << "this_group.empty() = " << this_group.empty() << endl;
            // cout << "in_variable_group(" << indic_to_var[indic_var] << ") = " 
                //  << in_variable_group(indic_to_var[indic_var]) << endl;
            if (conf.group_indep && this_group.empty() && 
                in_variable_group(indic_to_var[indic_var])) {
                for (auto& grp_var: var_groups[get_group_idx(indic_to_var[indic_var])]) {
                    this_group.push_back(grp_var);
                    assumptions.pop_back();
                } 
                new_group = true;
            } else {
                assumptions.pop_back();
            }

            cout << "indic_to_var.size() = " << indic_to_var.size() << endl;
            assert(indic_var < indic_to_var.size());
            test_var = indic_to_var[indic_var];
            assert(test_var != var_Undef);
            assert(test_var < orig_num_vars);

            //something is messed up
            if (!unknown_set[test_var]) {
                cout << "!!! Something is messed up !!! (test_var = " << test_var << ")" << endl;
                cout << "unkown_set[" << test_var << "] = " << unknown_set[test_var] << endl;
                quick_pop_ok = false;
                continue;
            }

            uint32_t last_unkn = unknown[unknown.size()-1];
            
            // If we're in group mode and just started processing a new 
            // variable group, we must remove all variables in that group from
            // the unknown set. NOTE: we assume here that the variables
            // in the same group are also grouped together in the unknown set.
            if (conf.group_indep && new_group) {
                assert(last_unkn == test_var);
                for (uint32_t i = 0; i < this_group.size(); i++) {
                    unknown.pop_back();
                    // TODO: Decide what to do about unknown_set
                }
            } else {
                assert(last_unkn == test_var);
                unknown.pop_back();
            } // by anna
        } 
        // !quick_pop_ok:
        else {
            cout << "No quick pop!" << endl;

            // Remove variables from the unknown stack until you find a
            // variable for which unknown_set is true (such that that variable
            // actually is unknown). That variable will be the first one to 
            // branch on(?)
            while(!unknown.empty()) {

                uint32_t var = unknown[unknown.size()-1];

                if (conf.group_indep) {
                    if (!this_group.empty()) {
                        var = this_group[this_group.size()-1];
                        this_group.pop_back();
                    } else {
                        // TODO: decide what to do here.
                    }
                } else {
                    unknown.pop_back();
                }
                
                cout << "unknown_set[" << var << "] = " << unknown_set[var] << endl;
                if (unknown_set[var]) {
                    test_var = var; 
                    break;
                }
                cout << "selected unknown var " << var << endl;
            }

            // This happens if the unknown stack doesn't contain any variables
            // anymore that are actually unknown.
            if (test_var == var_Undef) {
                //we are done, backward is finished
                if (conf.verb >= 5) cout << "c [arjun] we are done, backward is finished" << endl;
                cout << "c [arjun] we are done, backward is finished" << endl;
                break;
            }
            // If there was still an unknown variable on the stack, we get its
            // corresponding indicator variable and branch on it.
            indic_var = var_to_indic[test_var];
        }

        cout << "we're here!" << endl;

        assert(test_var < orig_num_vars);

        if (conf.group_indep) {
            if (new_group) {
                cout << "new_group!" << endl;
                for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
                    assert(unknown_set[grp_var] == 1);
                    unknown_set[grp_var] = 0;
                }
            }
        } else {
            assert(unknown_set[test_var] == 1);
            unknown_set[test_var] = 0;
        } // by anna
        
        cout << "Testing: " << test_var << endl;
        cout << "unknown.size() = " << unknown.size() << endl;

        for (uint i = 0; i < unknown.size(); i++) {
            cout << "unknown[" << i << "] = " << unknown[i] << endl; 
        }

        //Assumption filling
        assert(test_var != var_Undef);
        if (!quick_pop_ok) {
            fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
        }
        cout << "After fill_assumptions_backward, assumptions.size() = " << assumptions.size() << endl;
        
        assert(test_var != var_Undef);
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_no_confl_needed();
        
        // TODO: make grouped variables compatible with fast_backw
        lbool ret = l_Undef;
        if (!conf.fast_backw) {
            solver->set_max_confl(conf.backw_max_confl);
            std::vector<CMSat::Lit> old_assumptions = assumptions;
            ret = solver->solve(&assumptions);
            for (uint i = 0; i < old_assumptions.size(); i++) {
                cout << "oa: " << old_assumptions[i] << ", na: " << assumptions[i] << endl;
                if (old_assumptions[i] != assumptions[i]) {
                  cout << "DIFF!" << endl;
                }
            }
        } else {
            FastBackwData b;
            b._assumptions = &assumptions;
            b.indic_to_var  = &indic_to_var;
            b.orig_num_vars = orig_num_vars;
            b.non_indep_vars = &non_indep_vars;
            b.indep_vars = &indep;
            b.fast_backw_on = true;
            b.test_indic = &indic_var;
            b.test_var = &test_var;
            b.max_confl = conf.backw_max_confl;

            fast_backw_calls++;
            if (conf.verb > 5) {
                cout << "test var is: " << test_var << endl;
                cout << "find_fast_backw BEGIN " << endl;
            }
            non_indep_vars.clear();
            uint32_t indep_vars_last_pos = indep.size();

            // TODO: the next call fails with grouped variables
            ret = solver->find_fast_backw(b);

            if (conf.verb >= 3) {
                cout
                << "c [arjun] non_indep_vars.size(): " << non_indep_vars.size()
                << " indep.size(): " << indep.size()
                << " ret: " << ret
                << " test_var: " << test_var
                << endl;
            }
            if (ret == l_False) {
                if (conf.verb) {
                    cout << "c [arjun] Problem is UNSAT" << endl;
                }
                for(auto& x: unknown_set) {
                    x = 0;
                }
                unknown.clear();
                indep.clear();
                assumptions.clear();
                break;
            }

            fast_backw_tot += non_indep_vars.size();
            fast_backw_max = std::max<uint32_t>(non_indep_vars.size(), fast_backw_max);
            for(uint32_t i = indep_vars_last_pos; i < indep.size(); i ++) {
                uint32_t var = indep[i];
                unknown_set[var] = 0;
            }

            for(uint32_t i = 0; i < non_indep_vars.size(); i ++) {
                uint32_t var = non_indep_vars[i];
                assert(var < orig_num_vars);
                unknown_set[var] = 0;
                not_indep++;
            }
            quick_pop_ok = false;

            //We have finished it all off
            if (test_var == var_Undef) {
                assert(indic_var == var_Undef);
                continue;
            }
            unknown_set[test_var] = 0;
        }
        
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

        // cout << "test_var = " << test_var << ", in group " << get_group_idx(test_var) << endl;
        cout << "unknown_set:" << endl;
        for (uint32_t i = 0; i < unknown_set.size(); i++) {
            cout << "unknown_set[" << i << "] = " << unknown_set[i] << endl;
        }

        // TODO: come up with an equivalent assertion for group mode.
        if (!conf.group_indep) {
            assert(unknown_set[test_var] == 0);
        }
        
        if (ret == l_Undef || //Timed out, we'll treat is as unknown
            ret == l_True)    //Independent
        {   
            quick_pop_ok = false;
            assert(test_var < orig_num_vars);
            if (conf.group_indep && in_variable_group(test_var)) {
                cout << "Group " <<  var2var_group[test_var] << " is independent" << endl;
                for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
                    cout << "Pushing " << grp_var << " to indep." << endl;
                    indep.push_back(grp_var);
                }
                this_group.clear();
            } else {
                cout << "Pushing " <<  test_var << " to indep." << endl;
                indep.push_back(test_var);
            } // anna
        } else if (ret == l_False) {
            //not independent
            //i.e. given that all in indep+unkown is equivalent, it's not possible that a1 != b1
            cout << "Variable " << test_var << " is NOT independent" << endl;
            not_indep++;
            quick_pop_ok = true;
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
