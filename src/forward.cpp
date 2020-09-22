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
    uint32_t group ,
    bool reverse,
    bool shuffle,
    int offset)
{

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

    vector<Lit> assumptions;
    uint32_t iter = 0;
    uint32_t not_indep = 0;

    double myTime = cpuTime();
    vector<char> tried_var_already;
    tried_var_already.resize(orig_num_vars, 0);

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_set->size()) > 20 ) {
        uint32_t will_do_iters = sampling_set->size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }
    std::sort(unknown.begin(), unknown.end(), IncidenceSorter(incidence));
    if (reverse) {
        std::reverse(unknown.begin(), unknown.end());
    }
    if (shuffle) {
        std::random_shuffle(unknown.begin(), unknown.end());
    }
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
    std::sort(pick_possibilities.begin(), pick_possibilities.end(), IncidenceSorter(incidence));
    cout << "c [mis] Start unknown size: " << pick_possibilities.size() << endl;

    set_guess_forward_round(
        indep,
        unknown,
        unknown_set,
        group,
        offset,
        guess_set
    );

    fill_assumptions_forward(
        assumptions,
        indep,
        unknown,
        group,
        offset,
        guess_set
    );
    if (conf.set_val_forward) {
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
    uint32_t prev_test_var = var_Undef;
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

        //Remove old
        if (iter != 0) {
            assumptions.pop_back();
            assumptions.pop_back();

            //in case of DEP: This is just an optimization, to add the dependent var
            //in case of INDEP: This is needed.
            uint32_t ass = var_to_indic[prev_test_var];
            assert(ass != var_Undef);
            assert(!seen[ass]);
            if (conf.set_val_forward) {
                tmp.clear();
                tmp.push_back(Lit(ass, true));
                solver->add_clause(tmp);
            } else {
                assumptions.push_back(Lit(ass, true));
            }
        }

        //Add new one
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_max_confl(10);
        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        ret = solver->solve(&assumptions);
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
        } else if (ret == l_False) {
            //not independent
            not_indep++;
            //TODO: In the forward pass, even when the variable is not independent, we can still add it to the assumptions
        }

        if (iter % mod == (mod-1)) {
            cout
            << "c [mis] iter: " << std::setw(5) << iter;
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
        prev_test_var = test_var;
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

    indep.clear();
    update_sampling_set(unknown, unknown_set, indep);
    cout << "c [mis] forward round finished T: "
    << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
    << endl;

    if (conf.set_val_forward) {
        //we messed up the solver, re-init please
        cout << "We messed up the solver, re-init needed here -- TODO this is not a good idea AT ALL" << endl;
        init_solver_setup(false, saved_fname);
    }
    return iter < max_iters;
}