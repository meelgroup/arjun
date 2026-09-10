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
    uint32_t unate_def_max_confl_total = 50000.; // whole pass, not per call. 0 = off
    // Disable equiv probe after this many consecutive misses with zero hits.
    uint32_t unate_def_eq_dry_streak = 128;
    // Allow non-input vars as candidate L in the equiv t=L probe (tried after
    // inputs). 0 = inputs only; 1 = inputs first, then non-inputs.
    int unate_def_eq_noninput = 1;
    int oracle_find_bins = 6;
    double cms_glob_mult = -1.0;
    int extend_ccnr = 0;
    std::string debug_synth;
    // If set, dump guess AIGs at each restart to <prefix>-restart<N>.aig/.v.
    std::string dump_restart_aig;
    uint32_t seed = 42;
    // CNF rewriting through AIG lifting (cnf_rewrite.cpp).
    // bitmask: 1 = after the first puura pass, 2 = before puura, 4 = portfolio of plain vs pre-rewrite
    int cnf_rewrite = 2;
    double cnfrw_portfolio_min_gain = 3.0;
    int cnfrw_max_gate_inputs = 1000000;
    int cnfrw_max_xor_size = 8;
    int cnfrw_irreg = 1;
    int cnfrw_pg = 1;
    int cnfrw_constr = 0;
    int cnfrw_half = 1;
    int cnfrw_dup_var_weight = 6;
    int cnfrw_chain = 0;
    int cnfrw_pareto = 1;
    int cnfrw_inline_fanout = 0;
    int cnfrw_distrib = 1;
    int cnfrw_cofactor = 48;
    int cnfrw_cofactor_shared = 0;
    int cnfrw_or_distrib = 1;
    std::string cnfrw_dump;
    int cnfrw_irreg_max_prod = 64;
    int cnfrw_irreg_max_vars = 14;
    int cnfrw_rewrite = 1;
    int cnfrw_balance = 0;
    int cnfrw_group_cse = 1;
    int cnfrw_cut_cnf = 1;
    int cnfrw_detect_ite = 1;
    int cnfrw_detect_xor = 1;
    int cnfrw_guard = 1;
    int cnfrw_var_weight = 6;
    int cnfrw_cls_weight = 1;
    int cnfrw_kary_fusion = 1;
    int cnfrw_max_kary = 1000000;
    int cnfrw_max_mux_chain = 8;
    int cnfrw_min_gain = 0;
    int cnfrw_max_cls_len = 0;
    int cnfrw_encoder = 0;
    int cnfrw_map_leaves = 5;
    int cnfrw_map_cuts = 8;
    double cnfrw_map_helper_w = 1.0;
};

}
