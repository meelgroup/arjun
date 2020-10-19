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

struct Config {
    int verb = 0;
    int seed = 0;
    int fast_backw = 1;
    int distill = 0;
    int intree = 1;
    int guess = 1;
    int simp = 1;
    int incidence_sort = 3;
    int gate_based = 1;
    int xor_based = 0;
    int probe_based = 1;
    int polarmode = 0;
    int forward = 0;
    int backward = 1;
    int assign_fwd_val = 0;
    int solve_to_sat = 0;
    int do_xors = 1;
    uint32_t backw_max_confl = 500;
};

//ARJUN_CONFIG_H
#endif
