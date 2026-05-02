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
    uint32_t unate_def_cond_max_per_var = 128;
    uint32_t unate_def_cond_max_confl = 4000;
    // Disable conditional probe after this many consecutive misses with
    // zero hits so far. Low = bail aggressively; very high = effectively
    // never disable.
    uint32_t unate_def_cond_dry_streak = 128;
    // Allow non-input vars (to-define + already-tested non-backward-defined)
    // as the candidate L in the conditional t = L probe. Inputs are still
    // tried first; non-inputs only after the input list is exhausted.
    // 0 = inputs only (old behavior). 1 = inputs first, then non-inputs.
    int unate_def_cond_noninput = 1;
    // Repair-based unate definition search (manthan-style guess+refine).
    // Runs after standard unate_def for variables still undefined.
    uint32_t unate_def_rep_iters = 10;       // max guess+refine iters per var
    uint32_t unate_def_rep_max_pattern = 20;  // skip CEX if conflict (= pattern lits) bigger than this
    uint32_t unate_def_rep_max_costzero = 5; // give up on a var after this many cost-zero CEXes
    uint32_t unate_def_rep_max_confl = 5000; // SAT conflict budget per probe
    // Allow H to use non-input leaves to attack the cost-zero gap (F-bifunctional X).
    // 0 = input-only (old behavior).
    // 1 = input + backward-defined vars whose recursive deps don't include `test`.
    // 2 = input + backward-defined + still-undefined to-define vars (richest; relies
    //     on Manthan-side dependency tracking to keep the synthesis cycle-free).
    uint32_t unate_def_rep_aux = 2;
    // Greedy conflict minimization on the F-only solver: after extracting
    // the initial pattern, iteratively try dropping each lit and re-solving.
    // 0 = off (old behavior). 1 = greedy single pass. 2 = greedy + extra
    // shuffled passes for hot vars (similar to manthan's hot-var minim).
    uint32_t unate_def_rep_minim = 1;
    // Per-iteration budget on minimization solver calls. The minim loop
    // exits when removed_any goes false OR when budget hits zero. Keep
    // bounded since minim is O(pattern_size) extra solves per CEX.
    uint32_t unate_def_rep_minim_budget = 32;
    // Try an input-only F-solver call before the input+aux call. Manthan's
    // "input-only conflict first" — if the conflict survives without aux
    // pinning, the resulting pattern is over inputs only (smaller H, no
    // Y-side aux encode at commit). Disabled when aux mode is 0 since
    // the aux set is empty there. 0 = off; 1 = always try first; 2 = try
    // first but only when aux_vars non-empty.
    uint32_t unate_def_rep_input_only_first = 2;
    // After greedy minim of an input+aux conflict, attempt to drop *all*
    // aux lits at once (single solver call). Manthan's "drop y-vars from
    // conflict" — one shot SAT call to test whether the conflict still
    // holds with aux lits gone. On UNSAT, the resulting pattern is over
    // inputs only.
    uint32_t unate_def_rep_drop_aux = 1;
    // Multi-CEX collection à la manthan. After miter SAT, collect up to
    // K-1 additional CEX models by blocking each model's (input, aux)
    // projection. Then score models by an input-only F-only probe and
    // refine H using the model with the smallest input-only conflict
    // (or first if none input-only-UNSAT). 1 = off (single CEX); 2..N
    // = collect this many models per iter.
    uint32_t unate_def_rep_multi_cex_k = 1;
    // Verbosity for the per-iteration trace (manthan-style). At verb >=
    // unate_def_rep_iter_verb, every guess+refine iter prints a line
    // showing miter/f outcomes, pattern size, conflict size, h node
    // count. 0 = always print (chatty). Default 4 = only when --verb 4
    // or higher, since most users only want the per-var line.
    uint32_t unate_def_rep_iter_verb = 4;
    // When sorting pattern lits for greedy minim, prefer dropping lower-
    // pattern-frequency vars first (manthan's `var_conflict_freq`). 0 =
    // off (alphabetical); 1 = sort within aux/input buckets by ascending
    // freq. Default 0 — on this benchmark set the freq sort doesn't
    // produce H AIGs Manthan deals with cleanly downstream (bob loses
    // ~5s per repair round even though unate_def_rep finds more hits).
    uint32_t unate_def_rep_freq_sort = 0;
    // After greedy minim's main loop, do up to N extra passes with a
    // reverse-order shuffle. Manthan-style "extra passes for hot
    // variables" — the greedy result depends on iteration order, and
    // a different order can find additional removable lits. Each pass
    // counts against the same budget. 0 = off; N = up to N extra.
    uint32_t unate_def_rep_minim_extra_passes = 0;
    bool weighted = false;
    int oracle_find_bins = 6;
    double cms_glob_mult = -1.0;
    int extend_ccnr = 0;
    std::string debug_synth;
    uint32_t seed = 42;
};

}
