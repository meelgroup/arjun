/*
 Arjun

 Copyright (c) 2026, Mate Soos. All rights reserved.

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

// Unit tests for InterpRepair (Craig-interpolant repair for Manthan).
//
// These exercise compute_interpolant() directly on hand-built CNFs and
// check the interpolant property — A→I and exclusion of the CEX — via
// the public verification methods, plus the McMillan/Pudlák systems,
// multi-proof intersection, and the memoisation cache.

#include "interp_repair.h"
#include "arjun.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <set>
#include <vector>

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::cout;
using std::endl;
using std::set;
using std::vector;

static int failures = 0;

static void check(bool cond, const char* msg) {
    if (cond) {
        cout << "c o [test-interp-repair] ok:   " << msg << endl;
    } else {
        cout << "c o [test-interp-repair] FAIL: " << msg << endl;
        failures++;
    }
}

// Build a SimplifiedCNF over `nvars` variables with the given clauses.
static SimplifiedCNF make_cnf(const std::unique_ptr<FieldGen>& fg,
        uint32_t nvars, const vector<vector<Lit>>& clauses) {
    SimplifiedCNF cnf(fg);
    cnf.new_vars(nvars);
    for (const auto& cl : clauses) cnf.add_clause(cl);
    return cnf;
}

int main() {
    std::unique_ptr<FieldGen> fg = std::make_unique<FGenMpz>();
    Config conf;

    // CNF (x0 ∨ y1): x0 is an input, y1 a to-define variable. With
    // conflict {y1+, x0+} and to_repair = y1+, the mini-CNF is
    // (x0∨y1) ∧ ¬x0 ∧ ¬y1 — UNSAT — so an interpolant over x0 exists.
    const vector<vector<Lit>> cls_xy = {{ Lit(0, false), Lit(1, false) }};
    const Lit to_repair(1, false);
    const vector<Lit> conflict = { Lit(1, false), Lit(0, false) };

    // --- Test 1: McMillan interpolant is produced and verified. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(1, to_repair, conflict);
        check(interp != nullptr, "McMillan interpolant produced for (x0 v y1)");
        if (interp != nullptr) {
            check(ir.quick_check_interpolant_excludes_cex(interp, conflict),
                  "interpolant evaluates FALSE on the CEX inputs");
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp, false),
                  "A -> I holds (full miter)");
        }
    }

    // --- Test 2: memoisation cache. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr first = ir.compute_interpolant(1, to_repair, conflict);
        const uint64_t hits0 = ir.cache_hits;
        aig_ptr second = ir.compute_interpolant(1, to_repair, conflict);
        check(second == first, "repeated identical call returns the cached AIG");
        check(ir.cache_hits == hits0 + 1, "cache hit is recorded");

        // The conflict literal set keys the cache, so call-order must not
        // matter — a reordered conflict hits the same entry.
        const vector<Lit> conflict_rev = { Lit(0, false), Lit(1, false) };
        const uint64_t hits1 = ir.cache_hits;
        ir.compute_interpolant(1, to_repair, conflict_rev);
        check(ir.cache_hits == hits1 + 1,
              "reordered conflict hits the same cache entry");
    }

    // --- Test 3: Pudlák system also yields a verified interpolant. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(
            1, to_repair, conflict, /*max_aig_nodes=*/0, /*full_rewrite=*/false,
            /*conflict_budget=*/0, /*unconditional=*/false, /*nproofs=*/1,
            /*system=*/1 /*Pudlák*/, /*verify=*/true);
        check(interp != nullptr, "Pudlák interpolant produced");
        if (interp != nullptr) {
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp, false),
                  "Pudlák interpolant satisfies A -> I");
        }
    }

    // --- Test 4: multi-proof intersection stays sound. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(
            1, to_repair, conflict, 0, false, 0, false,
            /*nproofs=*/4, /*system=*/0, /*verify=*/true);
        check(interp != nullptr, "multi-proof (4) interpolant produced");
        if (interp != nullptr) {
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp, false),
                  "intersected interpolant satisfies A -> I");
        }
    }

    // --- Test 5: a conflict with no input literal has no B side, so
    // compute_interpolant must decline (return null). ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        const vector<Lit> conflict_no_input = { Lit(1, false) };
        aig_ptr interp = ir.compute_interpolant(1, to_repair, conflict_no_input);
        check(interp == nullptr, "no-input conflict yields no interpolant");
    }

    // --- Test 6: an empty conflict yields no interpolant. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(1, to_repair, {});
        check(interp == nullptr, "empty conflict yields no interpolant");
    }

    // --- Test 7: a two-clause CNF with two input vars in the conflict.
    // CNF (x0∨y2) ∧ (x1∨y2): with ¬y2 the formula forces x0 ∧ x1, so
    // the conflict {y2+, x0+, x1+} gives the UNSAT mini-CNF
    // (x0∨y2)∧(x1∨y2) ∧ ¬y2 ∧ ¬x0 ∧ ¬x1 and a real interpolant over
    // {x0, x1}. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 3, {
            { Lit(0, false), Lit(2, false) },
            { Lit(1, false), Lit(2, false) }});
        set<uint32_t> inputs = {0, 1};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        const Lit tr2(2, false);
        const vector<Lit> conf2 = { Lit(2, false), Lit(0, false), Lit(1, false) };
        aig_ptr interp = ir.compute_interpolant(2, tr2, conf2);
        check(interp != nullptr, "two-clause / two-input interpolant produced");
        if (interp != nullptr) {
            check(ir.quick_check_interpolant_excludes_cex(interp, conf2),
                  "two-input interpolant excludes the CEX");
            check(ir.slow_check_a_implies_i(tr2, conf2, interp, false),
                  "two-input interpolant satisfies A -> I");
        }
    }

    // --- Test 8: with verification disabled the interpolant is still
    // returned, and (for this easy instance) is in fact sound. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(
            1, to_repair, conflict, 0, false, 0, false, 1, 0,
            /*verify=*/false);
        check(interp != nullptr, "interpolant produced with verify disabled");
        if (interp != nullptr) {
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp, false),
                  "unverified interpolant still checks out on this instance");
        }
    }

    if (failures == 0) {
        cout << "c o [test-interp-repair] ALL TESTS PASSED" << endl;
        return 0;
    }
    cout << "c o [test-interp-repair] " << failures << " TEST(S) FAILED" << endl;
    return 1;
}
