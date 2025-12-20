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

#include "constants.h"
#include "minimize.h"
#include "constants.h"
#include "interpolant.h"
#include "src/interpolant.h"
#include "src/time_mem.h"
#include <algorithm>
#include <set>

using namespace ArjunInt;

void Minimize::fill_assumptions_backward(
    vector<Lit>& assumptions,
    vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const vector<uint32_t>& indep)
{
    verb_print(5, "Filling assumps BEGIN");
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);

        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);
        assumptions.push_back(Lit(indic, false));
        verb_print(5, "Filled assump with indep: " << var+1);
    }

    //Add unknown as assumptions, clean "unknown"
    uint32_t j = 0;
    for(uint32_t i = 0; i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        if (unknown_set[var] == 0) continue;
        else unknown[j++] = var;
        verb_print(5, "Filled assump with unknown: " << var+1);

        assert(var < orig_num_vars);
        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);
        assumptions.push_back(Lit(indic, false));
    }
    unknown.resize(j);
    verb_print(5, "Filling assumps END, total assumps size: " << assumptions.size());
}

void Minimize::order_by_file(const string& fname, vector<uint32_t>& unknown) {
    std::set<uint32_t> old_unknown(unknown.begin(), unknown.end());
    unknown.clear();

    std::ifstream infile(fname);
    std::string line;
    uint32_t line_num = 1;
    while (std::getline(infile, line))
    {
        std::istringstream iss(line);
        int a;
        if (!(iss >> a)) {
            cout << "ERROR: the file '" << fname << "' contains a line we cannot parse to be a variable number" << endl;
            cout << "ERROR line number: " << line_num << std::endl;
            cout << "ERROR: lines should ONLY contain a single variable" << endl;
            exit(EXIT_FAILURE);
        }
        if (old_unknown.find(a) == old_unknown.end()) {
            cout << "WARNING: the variable " << a << " is in the order file but not in the original order." << endl;
        }
        unknown.push_back(a);
        line_num++;
    }
}

void Minimize::print_sorted_unknown(const vector<uint32_t>& unknown) const
{
    if (conf.verb >= 4) {
        cout << "c o Sorted output: "<< endl;
        for (const auto& v: unknown) {
            cout << "c o var: " << v+1 << " occ: " << incidence[v]
            //<< " prop-inc: " << std::setw(6) << incidence_probing[v]
            << endl;
        }
    }
}

void Minimize::backward_round() {
#ifndef NDEBUG
    for(const auto& x: seen) assert(x == 0);
#endif
    double start_round_time = cpuTime();
    //start with empty independent set
    vector<uint32_t> indep;

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    vector<char> unknown_set(orig_num_vars, 0);
    for(const auto& x: sampling_vars) {
        assert(x < orig_num_vars);
        assert(unknown_set[x] == 0 && "No var should be in 'sampling_vars' twice!");
        unknown.push_back(x);
        unknown_set[x] = 1;
    }
    sort_unknown(unknown, incidence);
    /* std::reverse(unknown.begin(), unknown.end()); */
    /* std::mt19937_64 rand(33); */
    /* std::shuffle(unknown.begin(), unknown.end(), rand); */
    if (!conf.specified_order_fname.empty()) order_by_file(conf.specified_order_fname, unknown);
    print_sorted_unknown(unknown);
    verb_print(1, "[arjun] Start unknown size: " << unknown.size());
    solver->set_verbosity(0);

    vector<Lit> assumptions;
    uint32_t iter = 0;
    uint32_t not_indep = 0;
    double my_time = cpuTime();

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_vars.size()) > 20 ) {
        uint32_t will_do_iters = sampling_vars.size();
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
    while(true) {
        uint32_t test_var = var_Undef;
        if (quick_pop_ok) {
            //Remove 2 last
            assumptions.pop_back();
            assumptions.pop_back();

            //No more left, try again with full
            if (assumptions.empty()) {
                verb_print(5, "[arjun] No more left, try again with full");
                break;
            }

            indic_var = assumptions[assumptions.size()-1].var();
            assumptions.pop_back();
            assert(indic_var < indic_to_var.size());
            test_var = indic_to_var[indic_var];
            assert(test_var != var_Undef);
            assert(test_var < orig_num_vars);

            //something is messed up
            if (!unknown_set[test_var]) {
                quick_pop_ok = false;
                continue;
            }
            uint32_t last_unkn = unknown[unknown.size()-1];
            assert(last_unkn == test_var);
            unknown.pop_back();
        } else {
            while(!unknown.empty()) {
                uint32_t var = unknown[unknown.size()-1];
                if (unknown_set[var]) {
                    test_var = var;
                    unknown.pop_back();
                    break;
                } else {
                    unknown.pop_back();
                }
            }

            if (test_var == var_Undef) {
                //we are done, backward is finished
                verb_print(5, "[arjun] we are done, backward is finished");
                break;
            }
            indic_var = var_to_indic[test_var];
        }
        assert(test_var < orig_num_vars);
        assert(unknown_set[test_var] == 1);
        unknown_set[test_var] = 0;
        verb_print(5, "[arjun] Testing: " << test_var+1);

        //Assumption filling
        assert(test_var != var_Undef);
        if (!quick_pop_ok) {
            fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
        }
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        if (!conf.fast_backw) {
            solver->set_max_confl(conf.backw_max_confl);
            ret = solver->solve(&assumptions);
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
            ret = solver->find_fast_backw(b);

            verb_print(3, "[arjun] non_indep_vars.size(): " << non_indep_vars.size()
                << " indep.size(): " << indep.size() << " ret: " << ret << " test_var: " << test_var);
            if (ret == l_False) {
                verb_print(5, "[arjun] Problem is UNSAT");
                for(auto& x: unknown_set) x = 0;
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

            for(const auto& var: non_indep_vars) {
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
            verb_print(5, "[arjun] backw solve(): False");
        } else if (ret == l_True) {
            ret_true++;
            verb_print(5, "[arjun] backw solve(): True");
        } else if (ret == l_Undef) {
            verb_print(5, "[arjun] backw solve(): Undef");
            ret_undef++;
        }

        assert(unknown_set[test_var] == 0);
        if (ret == l_Undef) {
            //Timed out, we'll treat is as unknown
            quick_pop_ok = false;
            assert(test_var < orig_num_vars);
            indep.push_back(test_var);
        } else if (ret == l_True) {
            //Independent
            quick_pop_ok = false;
            indep.push_back(test_var);
        } else if (ret == l_False) {
            //not independent
            //i.e. given that all in indep+unkown is equivalent, it's not possible that a1 != b1
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
            << std::setprecision(2) << std::fixed << (cpuTime() - my_time)
            << endl;
            my_time = cpuTime();
            fast_backw_tot = 0;
            fast_backw_calls = 0;
            fast_backw_max = 0;
        }
        iter++;

        if (iter % 500 == 499) {
            update_sampling_set(unknown, unknown_set, indep);
        }
    }
    update_sampling_set(unknown, unknown_set, indep);

    verb_print(1, COLRED "[arjun] backward round finished. U: " <<
            " I: " << sampling_vars.size() << " T: "
        << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 4) solver->print_stats();
}

void Minimize::backward_round_synth(ArjunNS::SimplifiedCNF& cnf) {
    SLOW_DEBUG_DO(for(const auto& x: seen) assert(x == 0));
    double start_round_time = cpuTime();
    vector<uint32_t> indep;
    Interpolant interp(conf);
    interp.solver = solver.get();
    interp.fill_picolsat(orig_num_vars);
    interp.fill_var_to_indic(var_to_indic);

    //Initially, all of samping_set is unknown
    vector<char> unknown_set(orig_num_vars, 0);
    vector<uint32_t> unknown;
    set<uint32_t> dep;
    for(const auto& x: cnf.opt_sampl_vars) dep.insert(x);
    for(uint32_t x = 0; x < orig_num_vars; x++) {
        if (dep.count(x)) {
            solver->add_clause({Lit(var_to_indic[x], false)});
            continue;
        }
        unknown.push_back(x);
        unknown_set[x] = 1;
    }
    sort_unknown(unknown, incidence);
    print_sorted_unknown(unknown);
    verb_print(1, "[arjun] Start unknown size: " << unknown.size());
    solver->set_verbosity(0);

    vector<Lit> assumptions;
    uint32_t ret_true = 0;
    uint32_t ret_false = 0;
    uint32_t ret_undef = 0;
    while(true) {
        // Find a variable to test
        uint32_t test_var = var_Undef;
        while(!unknown.empty()) {
            uint32_t var = unknown.back();
            if (unknown_set[var]) {
                test_var = var;
                unknown.pop_back();
                break;
            } else {
                unknown.pop_back();
            }
        }

        if (test_var == var_Undef) {
            //we are done, backward is finished
            verb_print(5, "[arjun] we are done, " << __PRETTY_FUNCTION__ << " is finished");
            break;
        }
        assert(test_var < orig_num_vars);
        assert(unknown_set[test_var]);
        unknown_set[test_var] = 0;
        verb_print(3, "Testing: " << test_var+1);

        //Assumption filling
        assert(test_var != var_Undef);
        fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));
        solver->set_no_confl_needed();

        // See if it can be defined by anything
        lbool ret = l_Undef;
        solver->set_max_confl(conf.backw_max_confl);
        ret = solver->solve(&assumptions);

        if (ret == l_False) {
            ret_false++;
            verb_print(3, "[arjun] " << __PRETTY_FUNCTION__ << " solve(): False");
        } else if (ret == l_True) {
            ret_true++;
            verb_print(3, "[arjun] " << __PRETTY_FUNCTION__ << " solve(): True");
        } else if (ret == l_Undef) {
            verb_print(3, "[arjun] " << __PRETTY_FUNCTION__ << " solve(): Undef");
            ret_undef++;
        }

        assert(unknown_set[test_var] == 0);
        if (ret == l_Undef) {
            //Timed out, we'll treat is as unknown
            assert(test_var < orig_num_vars);
            indep.push_back(test_var);
        } else if (ret == l_True) {
            //Independent
            indep.push_back(test_var);
        } else if (ret == l_False) {
            //not independent
            //i.e. given that all in indep+unkown is equivalent, it's not possible that a1 != b1
            dep.insert(test_var);
            interp.generate_interpolant(assumptions, test_var, cnf);
        }
    }

    verb_print(3, __PRETTY_FUNCTION__ << " dep size: " << dep.size());
    verb_print(1, COLRED "[arjun] backward round finished. T: " << ret_true << " U: " << ret_undef
            << " F: " << ret_false << " I: " << sampling_vars.size() << " T: "
        << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();

    cnf.add_aigs_from(interp.get_aig_mng(), interp.get_defs());
}
