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
    int or_gate_based = 1;
    int xor_gates_based = 1;
    int ite_gate_based = 1;
    int irreg_gate_based = 1;
    int probe_based = 1;
    int gauss_jordan = 0;
    double no_gates_below = 0.01;
    std::string specified_order_fname;
    uint32_t backw_max_confl = 20000;
    uint32_t extend_max_confl = 30000;
    int unate_def_eq = 1;
    uint32_t unate_def_eq_max_per_var = 128;
    uint32_t unate_def_max_confl = 15000;
    uint32_t unate_def_eq_max_confl = 10000;
    // Disable equiv probe after this many consecutive misses with
    // zero hits so far. Low = bail aggressively; very high = effectively
    // never disable.
    uint32_t unate_def_eq_dry_streak = 128;
    // Allow non-input vars (to-define + already-tested non-backward-defined)
    // as the candidate L in the equiv t = L probe. Inputs are still
    // tried first; non-inputs only after the input list is exhausted.
    // 0 = inputs only (old behavior). 1 = inputs first, then non-inputs.
    int unate_def_eq_noninput = 1;
    int oracle_find_bins = 6;
    double cms_glob_mult = -1.0;
    int extend_ccnr = 0;
    // Rebuild the persistent interpolation solver + tracer after this
    // many interpolants. Besides bounding the tracer's accumulating clause
    // maps, the rebuild re-loads the doubled CNF with all accumulated
    // indicator equalities substituted in (v' merged into v), which
    // collapses copy-2 into copy-1 and keeps the proofs — and hence the
    // interpolant AIGs — small. Lowering it rebuilds (and re-simplifies)
    // more often.
    uint32_t interp_rebuild_every = 50;
    // Per-interpolant conflict budget; over this, skip the var. 0 = off.
    uint32_t interp_max_confl = 100000;
    std::string debug_synth;
    // Enable the expensive AIG rewrite passes (k-ary absorption + ITE
    // flattening). Off by default: they are O(n^2) and dominate rewrite time.
    int deep_rewrite = 0;
    uint32_t seed = 42;
};

}
