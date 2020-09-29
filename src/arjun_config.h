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

#ifndef ARJUN_CONFIG_H
#define ARJUN_CONFIG_H

struct Config {
    int verb = 0;
    int seed = 0;
    int backbone = 1;
    int distill = 0;
    int intree = 1;
    int guess = 1;
    int force_by_one = 1;
    int simp = 1;
    int gate_based = 1;
    int xor_based = 1;
    int probe_based = 1;
    int polarmode = 0;
    int always_one_by_one = 1;
    int recompute_sampling_set = 1;
    int smart_duplicate = 1;
    int forward = 0;
    int backward = 1;
    int backward_full = 1;
    int set_val_forward = 0;
    uint32_t backw_max_confl = 500;
};

//ARJUN_CONFIG_H
#endif
