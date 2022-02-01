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
                seen[ass] = 1;
                guess_set[var] = 1;
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
            seen[ass] = 1;
            assumptions.push_back(Lit(ass, true));
        }
    }

    for(uint32_t i = group*offs; i < group*(offs+1) && i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        assert(var < orig_num_vars);
        if (guess_set[var]) {
            uint32_t ass = var_to_indic[var];
            if (!seen[ass]) {
                seen[ass] = 1;
                assumptions.push_back(Lit(ass, true));
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
        unknown.push_back(x);
        unknown_set[x] = 1;
    }

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
    sort_unknown(unknown);
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
    if (conf.verb >= 2) {
        cout << "c [arjun] Forward start assumptions set: " << assumptions.size() << endl;
    }
    while(iter < max_iters) {
        //Select var
        uint32_t test_var = var_Undef;
        for(int i = pick_possibilities.size()-1; i>= 0; i--) {
            uint32_t var = pick_possibilities[i];
            if (!tried_var_already[var] && unknown_set[var] && !guess_set[var]) {
                test_var = pick_possibilities[i];
                break;
            } else {
                pick_possibilities.pop_back();
            }
        }
        if (test_var == var_Undef) {
            break;
        }
        assert(test_var < orig_num_vars);
        assert(unknown_set[test_var] == 1);
        unknown_set[test_var] = 0;
        assert(guess_set[test_var] == 0);
        tried_var_already[test_var] = 1;

        //Assumption filling: with guess_set that is in range + indep
        assert(test_var != var_Undef);

        //Add new one
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

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

        if (ret == l_Undef || ret == l_True) {
            assert(test_var < orig_num_vars);
            assert(unknown_set[test_var] == 0);
            indep.push_back(test_var);
            last_indep = true;
        } else if (ret == l_False) {
            //not independent
            not_indep++;
            last_indep = false;
        }

        //Remove test var's assumptions
        assumptions.pop_back();
        assumptions.pop_back();

        //NOTE: in case last var was DEP, we can STILL add it.
        //        But should we? It'll make the assumption set larger which
        //        would be OK if we hacked this into CMS but passing
        //        a large assumption set is not a good idea
        if (last_indep) {
            //in case last var was INDEP: This is needed
            uint32_t ass = var_to_indic[test_var];
            assert(ass != var_Undef);
            assert(!seen[ass]);
            if (conf.assign_fwd_val) {
                tmp.clear();
                tmp.push_back(Lit(ass, true));
                solver->add_clause(tmp);
            } else {
                assumptions.push_back(Lit(ass, true));
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
            unknown_set[var] = 1;
            unknown.push_back(var);
        }
    }

    for (auto var: indep) {
        if (!unknown_set[var]) {
            unknown.push_back(var);
            unknown_set[var] = 1;
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
