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
    int fast_backw = 1;
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
    uint32_t extend_max_confl = 1000;
    bool weighted = false;
    uint32_t num_samples = 10000;
    int oracle_find_bins = 6;
    double cms_glob_mult = -1.0;
    int extend_ccnr = 0;
    int autarkies = 0;
};

}
