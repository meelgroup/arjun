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

#pragma once

#include <cstdint>
#include <string>

namespace ArjunInt {

struct Config {
    int verb = 1;
    int simp = 2;
    int distill = 1;
    int intree = 1;
    int bve_pre_simplify = 1;
    int incidence_count = 3; // this determines what incidence MEANS
    int or_gate_based = 1;
    int xor_gates_based = 1;
    int ite_gate_based = 1;
    int irreg_gate_based = 1;
    int probe_based = 1;
    int gauss_jordan = 0;
    double no_gates_below = 0.01;
    std::string specified_order_fname;
    uint32_t backw_max_confl = 20000;
    uint32_t unate_max_confl = 100;
    uint32_t extend_max_confl = 30000;
    int unate_def_cond = 1;
    uint32_t unate_def_cond_max_per_var = 64;
    uint32_t unate_def_cond_max_confl = 4000;
    // 1 = try inputs sharing a clause with `test` first; 0 = use the
    // sorted input list. Used for A/B-testing the structural ordering.
    int unate_def_cond_relfirst = 1;
    // Disable conditional probe after this many consecutive misses with
    // zero hits so far. Low = bail aggressively; very high = effectively
    // never disable.
    uint32_t unate_def_cond_dry_streak = 128;
    // Repair-based unate definition search (manthan-style guess+refine).
    // Runs after standard unate_def for variables still undefined.
    int unate_def_rep = 1;
    uint32_t unate_def_rep_iters = 30;       // max guess+refine iters per var
    uint32_t unate_def_rep_max_pattern = 12; // skip CEX if conflict (= pattern lits) bigger than this
    uint32_t unate_def_rep_max_costzero = 2; // give up on a var after this many cost-zero CEXes
    uint32_t unate_def_rep_max_confl = 4000; // SAT conflict budget per probe
    bool weighted = false;
    int oracle_find_bins = 6;
    double cms_glob_mult = -1.0;
    int extend_ccnr = 0;
    std::string debug_synth;
    uint32_t seed = 42;
};

}
