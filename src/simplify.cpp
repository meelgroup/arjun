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

void Common::simp(vector<char>* unknown_set)
{
    if (conf.simp) {
        double simp_time = cpuTime();
        cout << "c [mis] Simplifying..." << endl;
        solver->simplify(&dont_elim);
        remove_eq_literals(unknown_set);
        remove_zero_assigned_literals(unknown_set);
        cout << "c [mis] Simplify finished. T: " << (cpuTime() - simp_time) << endl;
        //incidence = solver->get_var_incidence();
    }
}

void Common::remove_zero_assigned_literals(vector<char>* unknown_set)
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
        if (unknown_set && l.var() < orig_num_vars) {
            (*unknown_set)[l.var()] = 0;
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

    total_set_removed += orig_sampling_set_size - sampling_set->size();
    cout << "c [mis] Removed set       : "
    << (orig_sampling_set_size - sampling_set->size())
    << " new size: " << sampling_set->size()
    << endl;
}

void Common::remove_eq_literals(vector<char>* unknown_set)
{
    seen.clear();
    seen.resize(solver->nVars(), 0);
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
            if (unknown_set && mypair.second.var() < orig_num_vars) {
                (*unknown_set)[mypair.second.var()] = 0;
            }
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

    cout << "c [mis] Removed equivalent: "
    << (orig_sampling_set_size - sampling_set->size())
    << " new size: " << sampling_set->size()
    << endl;

}
