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
#include <algorithm>
#include <set>

using namespace ArjunInt;

template<class T>
void Common::fill_assumptions_extend(
    vector<Lit>& assumptions,
    const T& indep)
{
    verb_print(5, "Filling assumps BEGIN");
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);
        uint32_t indic = var_to_indic[var];
        assumptions.push_back(Lit(indic, false));
        verb_print(5, "Filled assump with indep: " << var);
    }
    verb_print(5, "Filling assumps END, total assumps size: " << assumptions.size());
}

void Common::add_all_indics()
{
    vector<Lit> tmp;
    for(uint32_t var = 0; var < orig_num_vars; var++) {
        // Already has an indicator variable
        if (var_to_indic[var] != var_Undef) continue;
        if (solver->removed_var(var)) continue;

        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        //torem_orig.push_back(Lit(this_indic, false));
        var_to_indic[var] = this_indic;
        dont_elim.push_back(Lit(this_indic, false));
        indic_to_var.resize(this_indic+1, var_Undef);
        indic_to_var[this_indic] = var;

        // Below two mean var == (var+orig) in case indic is TRUE
        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,        true));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,        true));
        solver->add_clause(tmp);
    }
}

void Common::synthesis_define(const set<uint32_t>& input) {
    assert(already_duplicated);
    solver->set_verbosity(0);
    add_all_indics();

    for(const auto& x: seen) assert(x == 0);
    double start_round_time = cpuTimeTotal();
    double myTime = cpuTime();
    set<uint32_t> indep;

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (solver->removed_var(i)) continue;
        indep.insert(i);
        if (input.count(i)) continue;
        unknown.push_back(i);
    }

    sort_unknown(unknown);
    /* std::reverse(unknown.begin(), unknown.end()); */
    verb_print(1,"[arjun] Start unknown size: " << unknown.size());

    vector<Lit> assumptions;
    uint32_t iter = 0;

    //Calc mod:
    uint32_t mod = 1;
    if (unknown.size() > 20 ) {
        uint32_t will_do_iters = unknown.size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;

    uint32_t tot_ret_false = 0;
    while(!unknown.empty()) {
        uint32_t test_var = unknown.back();
        unknown.pop_back();

        assert(test_var < orig_num_vars);
        verb_print(5, "Testing: " << test_var);

        //Assumption filling
        assert(test_var != var_Undef);
        indep.erase(test_var);
        fill_assumptions_extend(assumptions, indep);
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        solver->set_max_confl(conf.backw_max_confl);
        ret = solver->solve(&assumptions);
        if (ret == l_False) {
            ret_false++;
            tot_ret_false++;
            if (conf.verb >= 5) cout << "c [arjun] extend solve(): False" << endl;
        } else if (ret == l_True) {
            ret_true++;
            if (conf.verb >= 5) cout << "c [arjun] extend solve(): True" << endl;
        } else if (ret == l_Undef) {
            if (conf.verb >= 5) cout << "c [arjun] extend solve(): Undef" << endl;
            ret_undef++;
        }

        if (ret == l_Undef) {
            // Timed out, we'll treat is as unknown
            assert(test_var < orig_num_vars);
            indep.insert(test_var);
        } else if (ret == l_True) {
            // Not fully dependent
            indep.insert(test_var);
        } else if (ret == l_False) {
            // Dependent fully on `indep`
        }

        if (iter % mod == (mod-1) && conf.verb) {
            cout
            << "c [arjun] iter: " << std::setw(5) << iter;
            if (mod == 1) cout << " ret: " << std::setw(8) << ret;
            else {
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
            << " U: " << std::setw(7) << ret_undef
            << " I: " << std::setw(7) << ret_false
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - myTime) << endl;
            myTime = cpuTime();
        }
        iter++;
    }
    sampling_set->clear();
    for(const auto& i: indep) sampling_set->push_back(i);

    verb_print(1, "[arjun] extend round finished "
            << " final extension: " << tot_ret_false
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();
}

void Common::extend_round()
{
    assert(already_duplicated);
    solver->set_verbosity(0);
    add_all_indics();

    for(const auto& x: seen) assert(x == 0);
    double start_round_time = cpuTimeTotal();
    double myTime = cpuTime();
    vector<uint32_t> indep = *sampling_set;
    for(const auto& v: indep) seen[v] = 1;

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (seen[i]) continue;
        if (solver->removed_var(i)) continue;
        unknown.push_back(i);
    }
    for(const auto& v: indep) seen[v] = 0;

    sort_unknown(unknown);
    verb_print(1,"[arjun] Start unknown size: " << unknown.size());

    vector<Lit> assumptions;
    uint32_t iter = 0;

    //Calc mod:
    uint32_t mod = 1;
    if (unknown.size() > 20 ) {
        uint32_t will_do_iters = unknown.size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    while(!unknown.empty()) {
        uint32_t test_var = unknown.back();
        unknown.pop_back();

        assert(test_var < orig_num_vars);
        verb_print(5, "Testing: " << test_var);

        //Assumption filling
        assert(test_var != var_Undef);
        fill_assumptions_extend(assumptions, indep);
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        solver->set_max_confl(conf.backw_max_confl);
        ret = solver->solve(&assumptions);
        if (ret == l_False) {
            ret_false++;
            if (conf.verb >= 5) cout << "c [arjun] extend solve(): False" << endl;
        } else if (ret == l_True) {
            ret_true++;
            if (conf.verb >= 5) cout << "c [arjun] extend solve(): True" << endl;
        } else if (ret == l_Undef) {
            if (conf.verb >= 5) cout << "c [arjun] extend solve(): Undef" << endl;
            ret_undef++;
        }

        if (ret == l_Undef) {
            // Timed out, we'll treat is as unknown
            assert(test_var < orig_num_vars);
        } else if (ret == l_True) {
            // Not fully dependent
        } else if (ret == l_False) {
            // Dependent fully on `indep`
            indep.push_back(test_var);
        }

        if (iter % mod == (mod-1) && conf.verb) {
            cout
            << "c [arjun] iter: " << std::setw(5) << iter;
            if (mod == 1) cout << " ret: " << std::setw(8) << ret;
            else {
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
            << " X: " << std::setw(7) << ret_false
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - myTime) << endl;
            myTime = cpuTime();
        }
        iter++;

    }
    *sampling_set = indep;

    verb_print(1, "[arjun] extend round finished "
            << " final size: " << indep.size()
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();
}
