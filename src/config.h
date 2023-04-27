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

#ifndef CONFIG_H
#define CONFIG_H

#include <cstdint>
#include <string>

namespace ArjunInt {

struct Config {
    int verb = 3;
    int seed = 0;
    int simp = 1;
    int fast_backw = 1;
    int distill = 1;
    int intree = 1;
    int bve_pre_simplify = 1;
    int incidence_count = 3; // this determines what incidence MEANS
    int unknown_sort = 1; // this determines HOW we sort
    int or_gate_based = 1;
    int xor_gates_based = 1;
    int ite_gate_based = 1;
    int irreg_gate_based = 1;
    int empty_occs_based = 1;
    int probe_based = 1;
    int backward = 1;
    int gauss_jordan = 0;
    int backbone_simpl = 1;
    int backbone_simpl_cmsgen = 1;
    uint64_t backbone_simpl_max_confl = 20ULL*1000ULL;
    int bce = 0;
    double no_gates_below = 0.01;
    std::string specified_order_fname;
    uint32_t backw_max_confl = 5000;
    int bve_during_elimtofile = true;
};

}

//ARJUN_CONFIG_H
#endif
