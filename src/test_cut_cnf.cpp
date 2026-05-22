/*
 Standalone smoke test for cut_cnf.h. Exercises truth tables by:
 (1) computing the min-CNF, (2) re-evaluating the CNF on every input
 assignment and verifying it uniquely determines g to match f.

 Coverage: every 1-4-input truth table exhaustively, plus a 5-input sample
 (the 5-input path uses 32-bit truth tables and the greedy-cover fallback).

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#include "cut_cnf.h"
#include <cstdio>
#include <cstdlib>
#include <vector>

using namespace ArjunNS::cut_cnf;

// Returns the set of g values (as a 2-bit mask: bit 0 = g=0 satisfies, bit
// 1 = g=1 satisfies) allowed by the CNF under a given input minterm `m`.
static uint32_t cnf_evaluate(const MinCnf& cnf, uint32_t m, bool g) {
    for (const auto& c : cnf.clauses) {
        bool sat = false;
        for (uint32_t i = 0; i < cnf.num_inputs; i++) {
            if (!(c.present & (1u << i))) continue;
            bool bit = (m >> i) & 1;
            bool neg = (c.sign >> i) & 1;
            bool lit_val = neg ? !bit : bit;
            if (lit_val) { sat = true; break; }
        }
        if (!sat) {
            bool g_sat = c.g_sign ? !g : g;
            if (!g_sat) return 0;
        }
    }
    return 1;
}

static int check_tt(uint32_t num_inputs, uint32_t tt) {
    const MinCnf& cnf = min_cnf_for_tt(num_inputs, tt);
    uint32_t max_m = 1u << num_inputs;
    for (uint32_t m = 0; m < max_m; m++) {
        bool f_val = (tt >> m) & 1;
        bool g_allowed_false = cnf_evaluate(cnf, m, false);
        bool g_allowed_true  = cnf_evaluate(cnf, m, true);
        // g must be forced to f_val: only g_val == f_val is allowed.
        bool expect_false = !f_val;
        bool expect_true  = f_val;
        if (g_allowed_false != expect_false || g_allowed_true != expect_true) {
            fprintf(stderr, "FAIL tt=0x%x  m=%u  f=%d  allowed(g=0)=%d (want %d) allowed(g=1)=%d (want %d)\n",
                tt, m, f_val, g_allowed_false, expect_false, g_allowed_true, expect_true);
            return 1;
        }
    }
    return 0;
}

int main() {
    int fails = 0;
    // k = 1..4: exhaustive over every truth table.
    for (uint32_t k = 1; k <= 4; k++) {
        uint32_t max_tt = 1u << (1u << k);
        for (uint32_t tt = 0; tt < max_tt; tt++) {
            if (check_tt(k, tt)) fails++;
        }
    }
    // k = 5: 32-bit truth tables — 4 billion is too many to enumerate, so
    // sample randomly plus a few structured functions (parity, majority,
    // a projection, a constant) that stress the prime-cover code paths.
    for (uint32_t i = 0; i < 4000; i++) {
        uint32_t tt = ((uint32_t)rand() << 17) ^ ((uint32_t)rand() << 2) ^ (uint32_t)rand();
        if (check_tt(5, tt)) fails++;
    }
    {
        uint32_t parity5 = 0, maj5 = 0;
        for (uint32_t m = 0; m < 32; m++) {
            if (__builtin_popcount(m) & 1) parity5 |= (1u << m);
            if (__builtin_popcount(m) >= 3) maj5 |= (1u << m);
        }
        if (check_tt(5, parity5))           fails++;  // hardest: no merges
        if (check_tt(5, maj5))              fails++;
        if (check_tt(5, 0xAAAAAAAAu))       fails++;  // projection of x0
        if (check_tt(5, 0x00000000u))       fails++;  // constant 0
        if (check_tt(5, 0xFFFFFFFFu))       fails++;  // constant 1
    }

    // Report sizes for a few notable functions.
    auto report = [](const char* name, uint32_t k, uint32_t tt) {
        const MinCnf& cnf = min_cnf_for_tt(k, tt);
        printf("%-20s k=%u tt=0x%x  clauses=%zu\n", name, k, tt, cnf.clauses.size());
    };
    report("ALWAYS_FALSE(1)", 1, 0b00);
    report("IDENTITY(1)",     1, 0b10);
    report("NOT(1)",          1, 0b01);
    report("ALWAYS_TRUE(1)",  1, 0b11);
    report("AND(2)",          2, 0b1000);
    report("OR(2)",           2, 0b1110);
    report("XOR(2)",          2, 0b0110);
    report("XNOR(2)",         2, 0b1001);
    report("ITE(3)",          3, 0b11001100); // ite(a,b,c) — adjust if needed
    report("MAJ3(3)",         3, 0b11101000);

    if (fails) {
        fprintf(stderr, "\n%d failure(s)\n", fails);
        return 1;
    }
    printf("All min-CNF self-tests passed.\n");
    return 0;
}
