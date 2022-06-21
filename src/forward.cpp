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

//Only called once.
void Common::set_guess_forward_round(
    const vector<uint32_t>& indep,
    vector<uint32_t>& unknown,
    vector<char>& unknown_set,
    uint32_t group,
    uint32_t offs,
    vector<char>& guess_set)
{
    for(auto& x: seen) {
        x = 0;
    }

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);
        uint32_t ass = var_to_indic[var];
        assert(ass != var_Undef);
        if (!seen[ass]) {
            seen[ass] = 1;
        }
    }

    for(uint32_t i = group*offs; i < group*(offs+1) && i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        assert(var < orig_num_vars);
        if (unknown_set[var]) {
            unknown_set[var] = 0;
            uint32_t ass = var_to_indic[var];
            if (!seen[ass]) {
                if (conf.group_indep && in_variable_group(var)) {
                    uint32_t grp_idx = var2var_group[var] ;
                    for (auto& grp_var: var_groups[grp_idx]) {
                        ass = var_to_indic[grp_var];
                        seen[ass] = 1;
                        guess_set[grp_var] = 1;
                    }
                } else {
                    seen[ass] = 1;
                    guess_set[var] = 1;
                } // by anna
            }
        }
    }

    //clear seen
    for(auto& x: seen) {
        x = 0;
    }
}

// Only called once
void Common::fill_assumptions_forward(
    vector<Lit>& assumptions,
    const vector<uint32_t>& indep,
    vector<uint32_t>& unknown,
    uint32_t group,
    uint32_t offs,
    vector<char>& guess_set)
{
    assumptions.clear();
    for(auto& x: seen) {
        assert(x == 0);
    }

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);
        uint32_t ass = var_to_indic[var];
        assert(ass != var_Undef);
        if (!seen[ass]) {
            if (conf.group_indep && in_variable_group(var)) {
              uint32_t grp_idx = var2var_group[var];
              for (auto& grp_var: var_groups[grp_idx]) {
                  ass = var_to_indic[grp_var];
                  assert(ass != var_Undef);
                  seen[ass] = 1;
                  assumptions.push_back(Lit(ass, true));
              }
            } else {
                seen[ass] = 1;
                assumptions.push_back(Lit(ass, true));
            } // by anna
        } 
    }

    for(uint32_t i = group*offs; i < group*(offs+1) && i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        assert(var < orig_num_vars);
        if (guess_set[var]) {
            uint32_t ass = var_to_indic[var];
            if (!seen[ass]) {
                if (conf.group_indep && in_variable_group(var)) {
                  uint32_t grp_idx = var2var_group[var];
                  for (auto& grp_var: var_groups[grp_idx]) {
                      ass = var_to_indic[grp_var];
                      assert(ass != var_Undef);
                      seen[ass] = 1;
                      assumptions.push_back(Lit(ass, true));
                  }
                } else {
                    seen[ass] = 1;
                    assumptions.push_back(Lit(ass, true));
                } // by anna
            } 
        }
    }

    //clear seen
    for(const auto& var: unknown) {
        uint32_t ass = var_to_indic[var];
        seen[ass] = 0;
    }

    for(const auto& var: indep) {
        uint32_t ass = var_to_indic[var];
        seen[ass] = 0;
    }
}

bool Common::forward_round(
    uint32_t max_iters,
    uint32_t group,
    int offset)
{
    if (conf.verb) {
        cout << "c [arjun] Running FORWARD with group " << group
        << " offset: " << offset
        << " max_iters: " << max_iters
        << endl;
    }

    ///Will be used in case assign_fwd_val is set and we mess up the solver
    SATSolver* solver2 = NULL;

    for(const auto& x: seen) {
        assert(x == 0);
    }

    double start_round_time = cpuTimeTotal();

    //start with empty independent set
    vector<uint32_t> indep;

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    vector<char> unknown_set;
    unknown_set.resize(orig_num_vars, 0);
    for(const auto& x: *sampling_set) {
        cout << "x = " << x << " (forward_round)" << endl;
        unknown.push_back(x);
        unknown_set[x] = 1;
        cout << "unknown_set[" << x << "] = " << unknown_set[x] << endl;
    }
    cout << "unknown.size() after init = " << unknown.size() << endl;

    uint32_t iter = 0;
    uint32_t not_indep = 0;

    double myTime = cpuTime();
    vector<char> tried_var_already;
    tried_var_already.resize(orig_num_vars, 0);

    //Calc printing data
    uint32_t mod = 1;
    if ((sampling_set->size()) > 20 ) {
        uint32_t will_do_iters = sampling_set->size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }


    //Sort how we'll try to decide the unknowns
    // TODO: bring back sorting, but with groups!
    // sort_unknown(unknown);
    std::reverse(unknown.begin(), unknown.end());
    vector<char> guess_set(orig_num_vars, 0);
    for(uint32_t var = 0; var < orig_num_vars; var++) {
        guess_set[var] = 0;
    }
    vector<uint32_t> pick_possibilities;
    for(const auto& unk_v: unknown) {
        if (unknown_set[unk_v]){
            pick_possibilities.push_back(unk_v);
        }
    }
    std::sort(pick_possibilities.begin(), pick_possibilities.end(), IncidenceSorter<uint32_t>(incidence));
    if (conf.verb) {
        cout << "c [arjun] Start unknown size: " << pick_possibilities.size() << endl;
    }
    std::reverse(pick_possibilities.begin(), pick_possibilities.end());

    set_guess_forward_round(
        indep,
        unknown,
        unknown_set,
        group,
        offset,
        guess_set
    );

    vector<Lit> assumptions;
    fill_assumptions_forward(
        assumptions,
        indep,
        unknown,
        group,
        offset,
        guess_set
    );

    //we will mess up the solver, so this saves the state
    if (conf.assign_fwd_val) {
        assert(conf.simp == 1 && "Cannot do this without simp");
        solver2 = new SATSolver();
        bool ret = true;
        solver2->set_up_for_arjun();
        solver->start_getting_small_clauses(
            std::numeric_limits<uint32_t>::max(),
            std::numeric_limits<uint32_t>::max(),
            false
        );
        solver2->new_vars(solver->nVars());
        vector<Lit> lits;
        while(ret) {
            ret = solver->get_next_small_clause(lits);
            if (ret) {
                solver2->add_clause(lits);
            }
        }
    }


    //Make assumptions set
    if (conf.assign_fwd_val) {
        for(const auto& a: assumptions) {
            tmp.clear();
            tmp.push_back(a);
            solver->add_clause(tmp);
        }
        assumptions.clear();
    }

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    bool last_indep = true;
    vector<uint32_t> test_group;
    if (conf.verb >= 2) {
        cout << "c [arjun] Forward start assumptions set: " << assumptions.size() << endl;
    }
    while(iter < max_iters) {
        //Select var
        uint32_t test_var = var_Undef;

        // If there are still variables left in the group to process, pick the
        // next variable in the group.
        cout << "test_group.size() = " << test_group.size() << endl;

        if (conf.group_indep && !test_group.empty()) {
          test_var = test_group[test_group.size()-1];
          cout << "Processing the rest of group " << get_group_idx(test_var) << endl;
          test_group.pop_back();
        }
        // Otherwise, select a new (group) variable to process.
        else {
            cout << "pick new variable for branching" << endl;
            cout << "pick_possibilities.size() = " << pick_possibilities.size() << endl;
            for(int i = pick_possibilities.size()-1; i>= 0; i--) {
                uint32_t var = pick_possibilities[i];
                cout << "tried_var_already[" << var << "] = " << tried_var_already[var] << endl;
                cout << "unknown_set[" << var << "] = " << unknown_set[var] << endl;
                cout << "guess_set[" << var << "] = " << guess_set[var] << endl;
                if (!tried_var_already[var] && unknown_set[var] && !guess_set[var]) {
                    test_var = pick_possibilities[i];
                    cout << "Found new testvar! " << test_var << endl;
                    break;
                } else {
                    cout << "Popping back " << pick_possibilities[pick_possibilities.size()-1] << endl;
                    pick_possibilities.pop_back();
                }

            }
            // If we have just picked a new group variable, initialise the 
            // test_group helper vector:
            if (test_var == var_Undef) {
                break;
            }
            if (conf.group_indep) {
                for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
                    if (grp_var != test_var) {
                        test_group.push_back(grp_var);
                    }
                }
            }
        }
        if (test_var == var_Undef) {
            break;
        }
        
        cout << "Branching on var " << test_var << endl;

        // Mark relevant variables as no longer unknown
        cout << "full unknown_set:" << endl;
        for (uint32_t i = 0; i < unknown_set.size(); i++) {
            cout << "unknown_set[" << i << "]: " << unknown_set[i] << endl;
        }

        if (conf.group_indep && in_variable_group(test_var)) {
            for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
                assert(grp_var < orig_num_vars);
                // The following assertion is no longer helpful, since we are
                // removing groups of variables from the unknown set.
                // assert(unknown_set[grp_var] == 1);
                unknown_set[grp_var] = 0;
                assert(guess_set[grp_var] == 0);
                tried_var_already[grp_var] = 1;
            }
        } else {
            assert(test_var < orig_num_vars);
            assert(unknown_set[test_var] == 1);
            unknown_set[test_var] = 0;
            assert(guess_set[test_var] == 0);
            tried_var_already[test_var] = 1;
        } // by anna
        

        //Assumption filling: with guess_set that is in range + indep
        assert(test_var != var_Undef);

        //Add new one
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));
        // if (conf.group_indep && in_variable_group(test_var)) {
        //     uint32_t grp_idx = var2var_group[test_var];
        //     for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
        //         assumptions.push_back(Lit(grp_var, false));
        //         assumptions.push_back(Lit(grp_var + orig_num_vars, true));
        //     }
        // } else {
        //     assumptions.push_back(Lit(test_var, false));
        //     assumptions.push_back(Lit(test_var + orig_num_vars, true));
        // }        

        solver->set_max_confl(conf.backw_max_confl);
        solver->set_no_confl_needed();

        lbool ret = solver->solve(&assumptions);
        if (ret == l_False) {
            ret_false++;
        } else if (ret == l_True) {
            ret_true++;
        } else if (ret == l_Undef) {
            ret_undef++;
        }

        cout << "ret = " << ret << endl;

        // Formula is SAT, so test_var is Independent.
        if (ret == l_Undef || ret == l_True) {
            assert(test_var < orig_num_vars);
            assert(unknown_set[test_var] == 0);
            // In group mode: since we have found that one variable in
            // test_group is independent, we add all group variables to the
            // Independent set, and clean the test_group helper vector.
            if (conf.group_indep && in_variable_group(test_var)) {
                for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
                    cout << "Pushing group var " << grp_var << " to indep." << endl;
                    indep.push_back(grp_var);
                }
                test_group.clear();
            } 
            // When not in group mode, we simply add test_var to the set of 
            // independent variables.
            else {
                cout << "Pushing var " << test_var << " to indep." << endl;
                indep.push_back(test_var);
            }
            last_indep = true;
        } else if (ret == l_False) {
            //not independent
            not_indep++;
            last_indep = false;
        }

        //Remove test var's assumptions
        cout << "assumptions.size() before: " << assumptions.size() << endl;
        assumptions.pop_back();
        assumptions.pop_back();
        cout << "assumptions.size() after: " << assumptions.size() << endl;


        //NOTE: in case last var was DEP, we can STILL add it.
        //        But should we? It'll make the assumption set larger which
        //        would be OK if we hacked this into CMS but passing
        //        a large assumption set is not a good idea
        if (last_indep) {
            cout << "last_indep" << endl;
            //in case last var was INDEP: This is needed
            uint32_t ass = var_to_indic[test_var];
            assert(ass != var_Undef);
            assert(!seen[ass]);
            if (conf.assign_fwd_val) {
                
                if (conf.group_indep && in_variable_group(test_var)) {
                    for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
                        ass = var_to_indic[grp_var];
                        tmp.clear();
                        tmp.push_back(Lit(ass, true));
                        solver->add_clause(tmp);
                    }
                } else {
                    tmp.clear();
                    tmp.push_back(Lit(ass, true));
                    solver->add_clause(tmp);
                }
            } else {
                if (conf.group_indep && in_variable_group(test_var)) {
                    for (auto& grp_var: var_groups[get_group_idx(test_var)]) {
                        ass = var_to_indic[grp_var];
                        assumptions.push_back(Lit(ass, true));
                    }
                } else {
                    assumptions.push_back(Lit(ass, true));
                }
            }
        }

        if (iter % mod == (mod-1) && conf.verb) {
            cout
            << "c [arjun] iter: " << std::setw(5) << iter;
            if (mod == 1) {
                cout << " mode: "
                << " guess one "
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
            << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
            << endl;
            myTime = cpuTime();

        }
        iter++;
    }

    unknown.clear();
    for (uint32_t var = 0; var < orig_num_vars; var++){
        if (guess_set[var]) {
            if (conf.group_indep && in_variable_group(var)) {
                for (auto& grp_var: var_groups[get_group_idx(var)]) {
                    if (unknown_set[grp_var] == 0) {    // avoid adding variables multiple times
                        unknown_set[grp_var] = 1;
                        unknown.push_back(grp_var);
                    }
                }
            } else {
                unknown_set[var] = 1;
                unknown.push_back(var);
            }
            
        }
    }
    for (auto var: indep) {
        if (unknown_set[var] == 0) {
            if (conf.group_indep && in_variable_group(var)) {
                for (auto& grp_var: var_groups[get_group_idx(var)]) {
                    cout << "unknown_set[" << grp_var << "] = " << unknown_set[grp_var] 
                         << " (in group " << get_group_idx(var) << ")" << endl;
                    if (unknown_set[grp_var] == 0) {
                        unknown.push_back(grp_var);
                        unknown_set[grp_var] = 1;
                        cout << "Setting unknown_set[" << grp_var 
                             << "] to 1: " << unknown_set[grp_var] << endl;
                    }
                }
            } else {
                unknown.push_back(var);
                unknown_set[var] = 1;
            }
        }
    }

    if (conf.assign_fwd_val) {
        delete solver;
        solver = solver2;
    }

    indep.clear();
    update_sampling_set(unknown, unknown_set, indep);
    if (conf.verb) {
        cout << "c [arjun] forward round finished T: "
        << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
        << endl;
    }
    return iter < max_iters;
}
