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
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);

        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);
        assumptions.push_back(Lit(indic, true));
    }

    //Add unknown as assumptions, clean "unknown"
    uint32_t j = 0;
    std::sort(unknown.begin(), unknown.end(), IncidenceSorter(incidence));
    for(uint32_t i = 0; i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        if (unknown_set[var] == 0) {
            continue;
        } else {
            unknown[j++] = var;
        }

        assert(var < orig_num_vars);
        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);
        assumptions.push_back(Lit(indic, true));
    }
    unknown.resize(j);
}

bool Common::backward_round(
    uint32_t max_iters)
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
    cout << "c [mis] Start unknown size: " << unknown.size() << endl;

    vector<Lit> assumptions;
    uint32_t iter = 0;
    ModeType mode_type = conf.always_one_by_one ? one_mode : many_mode;
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

    vector<uint32_t> pick_possibilities;
    pick_possibilities.reserve(unknown.size());
    for(const auto& unk_v: unknown) {
        pick_possibilities.push_back(unk_v);
    }
    std::sort(pick_possibilities.begin(), pick_possibilities.end(), IncidenceSorter(incidence));

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    bool quick_pop_ok = false;
    uint32_t backbone_calls = 0;
    uint32_t backbone_max = 0;
    uint32_t backbone_tot = 0;
    while(iter < max_iters) {
        if (iter % 500 == 0) {
            mode_type = many_mode;
        } else {
            mode_type = one_mode;
        }
        //quick_pop_ok = false;

        if (conf.always_one_by_one) {
            mode_type = one_mode;
        }

        auto old_mode_type = mode_type;

        uint32_t test_var = var_Undef;
        if (mode_type == one_mode) {
            if (quick_pop_ok) {
                //Remove 2 last
                assumptions.pop_back();
                assumptions.pop_back();

                //No more left, try again with full
                if (assumptions.empty()) {
                    quick_pop_ok = false;
                    continue;
                }

                uint32_t ass_var = assumptions[assumptions.size()-1].var();
                assumptions.pop_back();
                assert(ass_var < indic_to_var.size());
                test_var = indic_to_var[ass_var];
                assert(test_var != var_Undef);
                assert(test_var < orig_num_vars);

                //Something is odd, try again with full
                if (!unknown_set[test_var]) {
                    test_var = var_Undef;
                    quick_pop_ok = false;
                    continue;
                }
                uint32_t last_unkn = unknown[unknown.size()-1];
                assert(last_unkn == test_var);
                unknown.pop_back();
            } else {
                for(int i = pick_possibilities.size()-1; i>= 0; i--) {
                    uint32_t var = pick_possibilities[i];
                    if (!tried_var_already[var] && unknown_set[var]) {
                        test_var = pick_possibilities[i];
                        break;
                    } else {
                        pick_possibilities.pop_back();
                    }
                }

                if (test_var == var_Undef) {
                    //we are done, backward is finished
                    break;
                }
            }
            assert(test_var < orig_num_vars);
            assert(unknown_set[test_var] == 1);
            unknown_set[test_var] = 0;
            tried_var_already[test_var] = 1;
        }

        //Assumption filling
        if (mode_type == many_mode) {
            fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
            assumptions.push_back(Lit(mult_or_invers_var, true));
        }
        else if (mode_type == one_mode) {
            assert(test_var != var_Undef);
            if (!quick_pop_ok) {
                fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
                assumptions.push_back(Lit(test_var, false));
                assumptions.push_back(Lit(test_var + orig_num_vars, true));
            } else {
                assumptions.push_back(Lit(test_var, false));
                assumptions.push_back(Lit(test_var + orig_num_vars, true));
            }
        }

        solver->set_max_confl(conf.backw_max_confl);
        if (mode_type == one_mode) {
            solver->set_no_confl_needed();
        }

        lbool ret = l_Undef;
        if (!conf.backbone) {
            ret = solver->solve(&assumptions);
        } else {
            backbone_calls++;
            vector<uint32_t> non_indep_vars;
            ret = solver->find_backbone(
                &assumptions,
                indic_to_var,
                orig_num_vars,
                non_indep_vars,
                test_var,
                indep.size());
            assert(ret != l_False);

//             cout << "non_indep_vars.size(): " << non_indep_vars.size() << endl;
            backbone_tot += non_indep_vars.size();
            backbone_max = std::max<uint32_t>(non_indep_vars.size(), backbone_max);
            for(uint32_t i = 0; i < non_indep_vars.size(); i ++) {
                uint32_t var = non_indep_vars[i];
                assert(var < orig_num_vars);
                if (i == 0) {
                    assert(unknown_set[var] == 0);
                } else {
                    assert(unknown_set[var] == 1);
                    unknown_set[var] = 0;
                }
                not_indep++;
            }
            quick_pop_ok = false;

            //We have finished it all off
            if (test_var == var_Undef) {
                continue;
            }
            unknown_set[test_var] = 0;
        }
        if (ret == l_False) {
            ret_false++;
        } else if (ret == l_True) {
            ret_true++;
        } else if (ret == l_Undef) {
            ret_undef++;
        }

        if (ret == l_Undef) {
            //Timed out, we'll treat is as unknown
            quick_pop_ok = false;
            if (mode_type == one_mode) {
                assert(test_var < orig_num_vars);
                assert(unknown_set[test_var] == 0);
                unknown_set[test_var] = 1;
                unknown.push_back(test_var);
            }
            assert(mode_type != many_mode && "TODO waaaait... we don't deal with many_mode here???");
        } else if (ret == l_True) {
            //Independent
            quick_pop_ok = false;
            assert(mode_type == one_mode);
            if (mode_type == one_mode) {
                indep.push_back(test_var);
            }
        } else if (ret == l_False) {
            if (mode_type == one_mode) {
                //not independent
                //i.e. given that all in indep+unkown is equivalent, it's not possible that a1 != b1
                not_indep++;
                quick_pop_ok = true;
            } else if (mode_type == many_mode) {
                quick_pop_ok = false;
                vector<Lit> reason = solver->get_conflict();
                for(Lit l: reason) {
                    seen[l.var()] = 1;
                }
                vector<uint32_t> not_in_reason;
                for(Lit l: assumptions) {
                    if (!seen[l.var()]) {
                        not_in_reason.push_back(l.var());
                    }
                }
                for(Lit l: reason) {
                    seen[l.var()] = 0;
                }

                //not independent.
                for(uint32_t ass: not_in_reason) {
                    if (ass >= indic_to_var.size()
                        || indic_to_var[ass] == var_Undef
                    ) {
                        continue;
                    }
                    uint32_t var = indic_to_var[ass];
                    not_indep++;
                    unknown_set[var] = 0;

                    //Remove from solver
                    tmp.clear();
                    tmp.push_back(Lit(ass, false));
                    solver->add_clause(tmp);
                }
            } else {
                assert(false && "only one_mode or many_mode exists");
            }
        }

        if (iter % mod == (mod-1)) {
            //remove_definable_by_gates();
            //solver->remove_and_clean_all();
            cout
            << "c [mis] iter: " << std::setw(5) << iter;
            if (mod == 1) {
                cout << " mode: "
                << (old_mode_type==one_mode ? "one " :
                ((old_mode_type==many_mode) ? "many" : "inv " ))
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
            if (conf.backbone) {
                cout << " backb avg:" << std::setprecision(1) << std::setw(7)
                << (double)backbone_tot/(double)backbone_calls
                << " backb max:" << std::setw(7) << backbone_max;
            }
            cout << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
            << endl;
            myTime = cpuTime();
            backbone_tot = 0;
            backbone_calls = 0;
            backbone_max = 0;
        }
        iter++;

        if (iter % 500 == 499) {
            update_sampling_set(unknown, unknown_set, indep);
        }
    }
    update_sampling_set(unknown, unknown_set, indep);
    cout << "c [mis] backward round finished T: "
    << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
    << endl;

    return iter < max_iters;
}
