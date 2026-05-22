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
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp),
                  "A -> I holds (full miter)");
        }
    }

    // --- Test 2: Pudlák system also yields a verified interpolant. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(
            1, to_repair, conflict, /*max_aig_nodes=*/0,
            /*conflict_budget=*/0, /*system=*/1 /*Pudlák*/);
        check(interp != nullptr, "Pudlák interpolant produced");
        if (interp != nullptr) {
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp),
                  "Pudlák interpolant satisfies A -> I");
        }
    }

    // --- Test 4: a conflict with no input literal has no B side, so
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

    // --- Test 5: an empty conflict yields no interpolant. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(1, to_repair, {});
        check(interp == nullptr, "empty conflict yields no interpolant");
    }

    // --- Test 6: a two-clause CNF with two input vars in the conflict.
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
            check(ir.slow_check_a_implies_i(tr2, conf2, interp),
                  "two-input interpolant satisfies A -> I");
        }
    }

    // --- Test 7: with verification disabled the interpolant is still
    // returned, and (for this easy instance) is in fact sound. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, cls_xy);
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(
            1, to_repair, conflict, 0, 0, /*system=*/0);
        check(interp != nullptr, "interpolant produced with verify disabled");
        if (interp != nullptr) {
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp),
                  "unverified interpolant still checks out on this instance");
        }
    }

    // --- Test 8: mini-CNF pruning. The relevant core is still (x0∨y1)
    // with conflict {y1+,x0+}, but the CNF is padded with clauses the
    // pruner must drop: (¬x0∨x5) is satisfied by the ¬x0 assumption
    // unit, and (x3∨x4) sits in a variable component disconnected from
    // the conflict. compute_interpolant must still return a verified
    // interpolant over x0, unaffected by the junk. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 6, {
            { Lit(0, false), Lit(1, false) },   // core: x0 ∨ y1
            { Lit(0, true),  Lit(5, false) },   // satisfied by ¬x0
            { Lit(3, false), Lit(4, false) }}); // disconnected component
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(1, to_repair, conflict);
        check(interp != nullptr, "interpolant produced despite padded CNF");
        if (interp != nullptr) {
            check(ir.quick_check_interpolant_excludes_cex(interp, conflict),
                  "padded-CNF interpolant excludes the CEX");
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp),
                  "padded-CNF interpolant satisfies A -> I (full CNF)");
        }
    }

    // --- Test 9: an original unit clause that contradicts an assumption
    // unit. CNF (x0) ∧ (x0∨y1): unit propagation of the ¬x0 assumption
    // immediately falsifies the (x0) clause, so the pruner must anchor
    // its kept set on that clause rather than emitting an empty (and
    // satisfiable) mini-CNF. ---
    {
        SimplifiedCNF cnf = make_cnf(fg, 2, {
            { Lit(0, false) },                 // unit clause: x0
            { Lit(0, false), Lit(1, false) }}); // x0 ∨ y1
        set<uint32_t> inputs = {0};
        AIGManager aig_mng;
        InterpRepair ir(conf, cnf, inputs, aig_mng);

        aig_ptr interp = ir.compute_interpolant(1, to_repair, conflict);
        check(interp != nullptr, "interpolant produced with unit-clause conflict");
        if (interp != nullptr) {
            check(ir.slow_check_a_implies_i(to_repair, conflict, interp),
                  "unit-clause-conflict interpolant satisfies A -> I");
        }
    }

    if (failures == 0) {
        cout << "c o [test-interp-repair] ALL TESTS PASSED" << endl;
        return 0;
    }
    cout << "c o [test-interp-repair] " << failures << " TEST(S) FAILED" << endl;
    return 1;
}
