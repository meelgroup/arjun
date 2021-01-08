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

// moving to expected best:
// --regsimp 1 --intree 1 --gaussj 0 --sort 3 --distill 1 --xorgate 1 --orgate 1 --guess 1 --fastbackw 1 --findxor 0

struct Config {
    int verb = 3;
    int seed = 0;
    int fast_backw = 1;
    int distill = 1;
    int regularly_simplify = 1;
    int intree = 1;
    int guess = 1;
    int pre_simplify = 1;
    int incidence_sort = 3;
    int or_gate_based = 1;
    int xor_gates_based = 1;
    int probe_based = 1;
    int polarmode = 0;
    int forward = 0;
    int forward_group = 10;
    int backward = 1;
    int assign_fwd_val = 0;
    int gauss_jordan = 0;
    int find_xors = 0;
    int backbone_simpl = 1;
    uint32_t backw_max_confl = 500;
    uint32_t guess_max_confl = 1000;
};

//ARJUN_CONFIG_H
#endif
