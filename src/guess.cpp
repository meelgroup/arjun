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

void Common::fill_assumptions_inv(
    vector<Lit>& assumptions,
    const vector<uint32_t>& indep,
    const vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    uint32_t group,
    uint32_t offs,
    uint32_t index,
    vector<char>& dontremove_vars)
{
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        //assumptions.push_back(Lit(this_indic2[var], true)); //Shouldn't this be false?
        uint32_t ass = var_to_indic[var];
        if (!seen[ass]) {
            seen[ass] = 1;
            assumptions.push_back(Lit(ass, true));
            dontremove_vars[var] = 1;
        }
    }

    for(uint32_t i = group*offs; i < group*(offs+index+1) && i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        assert(var < orig_num_vars);
        if (unknown_set[var]) {
            uint32_t ass = var_to_indic[var];
            if (!seen[ass]) {
                seen[ass] = 1;
                assumptions.push_back(Lit(ass, true));
                dontremove_vars[var] = 1;
            }
        }
    }

    //clear seen
    for(const auto& x: assumptions) {
        seen[x.var()] = 0;
    }
}

void Common::run_guess()
{
    double myTime = cpuTime();
    uint32_t start_sampl = sampling_set->size();

    uint32_t div = 5;
    uint32_t guess_indep = std::max<uint32_t>(sampling_set->size()/div, 20);

    //NORM
    uint32_t cur_sampl_size = sampling_set->size();
    if (true) {
        cout << " ============ INV ==============" << endl;
        for (uint32_t i = 0; i < div/2; i++){
            guess_round(guess_indep, true, false, i);
        }
    }
    uint32_t inv_removed = cur_sampl_size - sampling_set->size();

    cur_sampl_size = sampling_set->size();
    if (true) {
        cout << " ============ NORM ==============" << endl;
        for (uint32_t i = 0; i < div/2; i++) {
            guess_round(guess_indep, false, false, i);
        }
    }
    uint32_t norm_removed = cur_sampl_size - sampling_set->size();

    cur_sampl_size = sampling_set->size();
    if (true) {
        cout << " ============ RND ==============" << endl;
        for (uint32_t i = 0; i < div/2; i++) {
            guess_round(guess_indep, false, true, 0);
        }
    }
    uint32_t rnd_removed = cur_sampl_size - sampling_set->size();

    cout
    << "[mis] GUESS"
    << " rem: " << std::setw(7) << (start_sampl - sampling_set->size())
    << " rem-inv: " << inv_removed
    << " rem-norm: " << norm_removed
    << " rem-rnd: " << rnd_removed
    << " T: " << (cpuTime() - myTime) << endl;
}


void Common::guess_round(
    uint32_t group,
    bool reverse,
    bool shuffle,
    int offset)
{
    for(const auto& x: seen) {
        assert(x == 0);
    }

    if (offset >= sampling_set->size()/group) {
        return;
    }

    double start_round_time = cpuTimeTotal();
    //start with empty independent set
    vector<uint32_t> indep;

    seen.resize(solver->nVars(), 0);

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
    uint32_t removed = 0;
    double myTime = cpuTime();
    vector<char> tried_var_already;
    tried_var_already.resize(orig_num_vars, 0);

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_set->size()/group) > 20 ) {
        uint32_t will_do_iters = (sampling_set->size()/group);
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }
    vector<char> dontremove_vars(orig_num_vars, 0);

    std::sort(unknown.begin(), unknown.end(), IncidenceSorter(incidence));
    if (reverse) {
        std::reverse(unknown.begin(), unknown.end());
    }
    if (shuffle) {
        std::random_shuffle(unknown.begin(), unknown.end());
    }

    bool should_continue_guess = true;
    uint32_t tot_removed = 0;
    while(iter < 5) {
        should_continue_guess = false;

        //Assumption filling
        if (iter < 5) {
            fill_assumptions_inv(
                assumptions,
                indep,
                unknown,
                unknown_set,
                group,
                offset,
                iter,
                dontremove_vars
            );
            assumptions.push_back(Lit(mult_or_invers_var, true));
        }

        solver->set_max_confl(100);
        removed = guess_remove_and_update_ass(
            assumptions, unknown_set, dontremove_vars);

        tot_removed += removed;

        if (iter % mod == (mod-1)) {
            cout
            << "c [mis] iter: " << std::setw(5) << iter;
            cout << " mode: guess ";
            cout
            << " Test: " << std::setw(7) << assumptions.size()
            << " Rem: " << std::setw(7) << tot_removed
            << " U: " << std::setw(7) << unknown.size()
            << " I: " << std::setw(7) << indep.size()
            << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
            << endl;
            myTime = cpuTime();
            tot_removed = 0;
        }
        iter++;
    }
    update_sampling_set(unknown, unknown_set, indep);
    cout << "c [mis] guess round finished T: "
    << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
    << endl;
}


uint32_t Common::guess_remove_and_update_ass(
    vector<Lit>& assumptions,
    vector<char>& unknown_set,
    vector<char>& dontremove_vars)
{
    uint32_t removed = 0;
    seen.resize(solver->nVars(), 0);

    bool ok = solver->implied_by(assumptions, tmp_implied_by);
    if (!ok) {
        return 0;
    }

    //Anything that's remaining, remove
    for(const Lit p: tmp_implied_by) {
        uint32_t ind = p.var();
        if (p.sign() == false ||
            ind >= indic_to_var.size() ||
            indic_to_var[ind] == var_Undef)
        {
            continue;
        }
        uint32_t var = indic_to_var[ind];

        //Setting them to be dependent
        if (!dontremove_vars[var] && unknown_set[var]) {
            unknown_set[var] = 0;
            assumptions.push_back(Lit(ind, true));
            dontremove_vars[var] = 1;
            removed++;
        }
    }

    return removed;
}
