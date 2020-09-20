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

void Common::simp()
{
    auto old_size = sampling_set->size();
    double myTime = cpuTime();

    if (conf.gate_based) {
        remove_definable_by_gates();
    }

    cout << "c [mis] Simplifying..." << endl;
    if (conf.simp) {
        solver->simplify(&dont_elim);
    }
    remove_eq_literals();
    remove_zero_assigned_literals();
    if (conf.gate_based) {
        remove_definable_by_gates();
    }
    cout << "c [mis] Simplify finished "
    << " removed: " << (old_size-sampling_set->size())
    << " perc: " << std::fixed << std::setprecision(2)
    << ((double)(old_size-sampling_set->size())/(double)old_size)*100.0
    << " T: " << (cpuTime() - myTime)
    << endl;

    //incidence = solver->get_var_incidence();
}

void Common::remove_definable_by_gates()
{
    double myTime = cpuTime();
    auto old_size = sampling_set->size();
    vector<uint32_t> vars = *sampling_set;
    vector<uint32_t> definable = solver->get_definabe(vars);

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

    //TODO atomic swap
    std::swap(sampling_set, other_sampling_set);

    cout << "c [mis] gate-based"
    << " removed: " << (old_size-sampling_set->size())
    << " perc: " << std::fixed << std::setprecision(2)
    << ((double)(old_size-sampling_set->size())/(double)old_size)*100.0
    << " T: " << (cpuTime() - myTime) << endl;
}

void Common::remove_zero_assigned_literals()
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

    total_set_removed += orig_sampling_set_size - sampling_set->size();
    cout << "c [mis] Removed set       : "
    << (orig_sampling_set_size - sampling_set->size())
    << " new size: " << sampling_set->size()
    << endl;
}

void Common::remove_eq_literals()
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
