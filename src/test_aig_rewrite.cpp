/*
 Arjun - AIG Rewriting System Tests
 */

#include "aig_rewrite.h"
#include <iostream>
#include <cassert>
#include <vector>

using namespace ArjunNS;
using std::cout;
using std::endl;
using std::vector;

static AIGManager aig_mng;

static size_t count_nodes(const aig_ptr& aig) {
    return AIG::count_aig_nodes(aig);
}

// Evaluate an AIG with a given assignment using the public evaluate() method
static bool eval(const aig_ptr& aig, uint32_t num_vars, uint32_t mask) {
    std::vector<CMSat::lbool> vals(num_vars);
    for (uint32_t v = 0; v < num_vars; v++) {
        vals[v] = ((mask >> v) & 1) ? CMSat::l_True : CMSat::l_False;
    }
    std::vector<aig_ptr> defs(num_vars, nullptr);
    std::map<aig_ptr, CMSat::lbool> cache;
    auto result = AIG::evaluate(vals, aig, defs, cache);
    assert(result != CMSat::l_Undef);
    return result == CMSat::l_True;
}

// Check that two AIGs are functionally equivalent over all assignments
// of variables 0..num_vars-1
static bool functionally_equal(const aig_ptr& a, const aig_ptr& b, uint32_t num_vars) {
    assert(num_vars <= 20);
    for (uint32_t mask = 0; mask < (1u << num_vars); mask++) {
        if (eval(a, num_vars, mask) != eval(b, num_vars, mask)) return false;
    }
    return true;
}

static int tests_passed = 0;
static int tests_failed = 0;

static void check(bool cond, const char* msg) {
    if (cond) {
        tests_passed++;
    } else {
        tests_failed++;
        cout << "FAIL: " << msg << endl;
    }
}

// ===== Test cases =====

void test_const_prop() {
    auto x = AIG::new_lit(0);
    auto t = aig_mng.new_const(true);
    auto f = aig_mng.new_const(false);

    AIGRewriter rw;

    // AND(TRUE, x) = x
    auto a1 = AIG::new_and(t, x);
    auto r1 = rw.rewrite(a1);
    check(functionally_equal(a1, r1, 1), "AND(TRUE, x) = x");
    check(count_nodes(r1) == 1, "AND(TRUE, x) is single node");

    // AND(FALSE, x) = FALSE
    auto a2 = AIG::new_and(f, x);
    auto r2 = rw.rewrite(a2);
    check(functionally_equal(a2, r2, 1), "AND(FALSE, x) = FALSE functional");
    check(count_nodes(r2) == 1, "AND(FALSE, x) is const");

    // OR(TRUE, x) = TRUE
    auto a3 = AIG::new_or(t, x);
    auto r3 = rw.rewrite(a3);
    check(functionally_equal(a3, r3, 1), "OR(TRUE, x) = TRUE functional");

    // OR(FALSE, x) = x
    auto a4 = AIG::new_or(f, x);
    auto r4 = rw.rewrite(a4);
    check(functionally_equal(a4, r4, 1), "OR(FALSE, x) = x functional");
}

void test_complement_elim() {
    auto x = AIG::new_lit(0);
    auto nx = AIG::new_lit(0, true);

    AIGRewriter rw;

    // AND(x, ~x) = FALSE
    auto a1 = AIG::new_and(x, nx);
    auto r1 = rw.rewrite(a1);
    check(functionally_equal(a1, r1, 1), "AND(x, ~x) = FALSE functional");
    check(count_nodes(r1) == 1 && !eval(r1, 1, 0) && !eval(r1, 1, 1), "AND(x, ~x) is FALSE");

    // OR(x, ~x) = TRUE
    auto a2 = AIG::new_or(x, nx);
    auto r2 = rw.rewrite(a2);
    check(functionally_equal(a2, r2, 1), "OR(x, ~x) = TRUE functional");
}

void test_idempotent() {
    auto x = AIG::new_lit(0);

    AIGRewriter rw;

    // AND(x, x) = x
    auto a1 = AIG::new_and(x, x);
    auto r1 = rw.rewrite(a1);
    check(functionally_equal(a1, r1, 1), "AND(x, x) = x functional");

    // OR(x, x) = x
    auto a2 = AIG::new_or(x, x);
    auto r2 = rw.rewrite(a2);
    check(functionally_equal(a2, r2, 1), "OR(x, x) = x functional");
}

void test_absorption() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);

    AIGRewriter rw;

    // AND(a, AND(a, b)) = AND(a, b)
    auto ab = AIG::new_and(a, b);
    auto a_ab = AIG::new_and(a, ab);
    auto r1 = rw.rewrite(a_ab);
    check(functionally_equal(a_ab, r1, 2), "AND(a, AND(a,b)) functional");
    check(count_nodes(r1) <= count_nodes(a_ab), "AND(a, AND(a,b)) reduces nodes");

    // AND(a, OR(a, b)) = a
    auto a_or_b = AIG::new_or(a, b);
    auto a_and_or = AIG::new_and(a, a_or_b);
    auto r2 = rw.rewrite(a_and_or);
    check(functionally_equal(a_and_or, r2, 2), "AND(a, OR(a,b)) = a functional");
}

void test_subsumption() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto na = AIG::new_lit(0, true);

    AIGRewriter rw;

    // AND(a, OR(~a, b)) = AND(a, b)
    auto na_or_b = AIG::new_or(na, b);
    auto a_and_or = AIG::new_and(a, na_or_b);
    auto r1 = rw.rewrite(a_and_or);
    check(functionally_equal(a_and_or, r1, 2), "AND(a, OR(~a, b)) = AND(a, b) functional");
    check(count_nodes(r1) <= count_nodes(a_and_or), "subsumption reduces nodes");
}

void test_nested_and_flatten() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;

    // AND(a, AND(a, AND(b, c))) should flatten and remove duplicate a
    auto bc = AIG::new_and(b, c);
    auto a_bc = AIG::new_and(a, bc);
    auto a_a_bc = AIG::new_and(a, a_bc);
    auto r1 = rw.rewrite(a_a_bc);
    check(functionally_equal(a_a_bc, r1, 3), "nested AND flatten functional");
    check(count_nodes(r1) <= count_nodes(a_a_bc), "nested AND flatten reduces nodes");
}

void test_ite_pattern() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;

    // ITE(a, b, c) = OR(AND(a, b), AND(~a, c))
    auto ite = AIG::new_ite(b, c, a);
    auto r1 = rw.rewrite(ite);
    check(functionally_equal(ite, r1, 3), "ITE rewrite functional");

    // ITE(a, b, b) = b (should already be simplified at construction)
    auto ite2 = AIG::new_ite(b, b, a);
    auto r2 = rw.rewrite(ite2);
    check(functionally_equal(ite2, r2, 3), "ITE(a, b, b) = b functional");
}

void test_deep_complement_in_chain() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto na = AIG::new_lit(0, true);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;

    // AND(a, AND(~a, b)) = FALSE
    auto na_b = AIG::new_and(na, b);
    auto a_and_na_b = AIG::new_and(a, na_b);
    auto r1 = rw.rewrite(a_and_na_b);
    check(functionally_equal(a_and_na_b, r1, 3), "AND(a, AND(~a, b)) = FALSE functional");
    check(count_nodes(r1) == 1 && !eval(r1, 3, 0), "AND(a, AND(~a, b)) is FALSE");

    // OR(a, OR(~a, b)) = TRUE
    auto na_or_b = AIG::new_or(na, b);
    auto a_or_na_or_b = AIG::new_or(a, na_or_b);
    auto r2 = rw.rewrite(a_or_na_or_b);
    check(functionally_equal(a_or_na_or_b, r2, 3), "OR(a, OR(~a, b)) = TRUE functional");
}

void test_multi_aig_sharing() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;

    // Two AIGs sharing substructure
    auto ab = AIG::new_and(a, b);
    auto aig1 = AIG::new_and(ab, c);
    auto aig2 = AIG::new_or(ab, c);

    vector<aig_ptr> defs = {aig1, aig2};
    rw.rewrite_all(defs, 0);

    check(functionally_equal(aig1, defs[0], 3), "multi-AIG rewrite preserves AIG 1");
    check(functionally_equal(aig2, defs[1], 3), "multi-AIG rewrite preserves AIG 2");
}

void test_large_and_chain() {
    // AND(x0, AND(x1, AND(x2, ... AND(x0, x1)...)))
    // The repeated x0 should be eliminated
    const uint32_t n = 8;
    vector<aig_ptr> lits;
    for (uint32_t i = 0; i < n; i++) lits.push_back(AIG::new_lit(i));

    // Build a chain with duplicates
    auto chain = lits[0];
    for (uint32_t i = 1; i < n; i++) chain = AIG::new_and(chain, lits[i]);
    // Add duplicates
    chain = AIG::new_and(chain, lits[0]);
    chain = AIG::new_and(chain, lits[1]);
    chain = AIG::new_and(chain, lits[2]);

    AIGRewriter rw;
    auto r = rw.rewrite(chain);
    check(functionally_equal(chain, r, n), "large AND chain with duplicates functional");
    check(count_nodes(r) <= count_nodes(chain), "large AND chain reduces nodes");
}

void test_double_negation() {
    auto a = AIG::new_lit(0);

    AIGRewriter rw;

    // NOT(NOT(a)) = a
    auto nna = AIG::new_not(AIG::new_not(a));
    auto r = rw.rewrite(nna);
    check(functionally_equal(nna, r, 1), "NOT(NOT(a)) = a functional");
    check(count_nodes(r) == 1, "NOT(NOT(a)) is single node");
}

void test_not_through_and() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;

    // NOT(AND(a,b)) should simplify to NAND(a,b) = AND(a,b,neg=true).
    // Original shape: outer-NOT node + inner-AND node + 2 lits = 4 nodes.
    // Expected shape: single AND(neg=true) + 2 lits = 3 nodes.
    {
        auto and_ab = AIG::new_and(a, b);
        auto not_and = AIG::new_not(and_ab);
        auto r = rw.rewrite(not_and);
        check(functionally_equal(not_and, r, 2), "NOT(AND(a,b)) functional");
        check(count_nodes(r) == 3, "NOT(AND(a,b)) collapses outer NOT into inner");
    }

    // NOT(NAND(a,b)) should simplify to AND(a,b) (neg flipped).
    {
        auto nand_ab = AIG::new_and(a, b, /*neg=*/true);
        auto not_nand = AIG::new_not(nand_ab);
        auto r = rw.rewrite(not_nand);
        check(functionally_equal(not_nand, r, 2), "NOT(NAND(a,b)) functional");
        check(count_nodes(r) == 3, "NOT(NAND(a,b)) = AND(a,b) is 3 nodes");
    }

    // NOT(AND(a, AND(b,c))): outer NOT should fold into outer AND's neg,
    // giving NAND(a, AND(b,c)) with no extra inverter layer.
    {
        auto and_bc = AIG::new_and(b, c);
        auto and_abc = AIG::new_and(a, and_bc);
        auto before = count_nodes(AIG::new_not(and_abc));
        auto not_abc = AIG::new_not(and_abc);
        auto r = rw.rewrite(not_abc);
        check(functionally_equal(not_abc, r, 3), "NOT(AND(a,AND(b,c))) functional");
        check(count_nodes(r) < before, "NOT(AND(a,AND(b,c))) strictly smaller");
    }

    // Double NOT through AND: NOT(NOT(AND(a,b))) must collapse back to AND(a,b).
    // This tests interplay of new_not's NOT-NOT rule and the new NOT-through-AND rule.
    {
        auto and_ab = AIG::new_and(a, b);
        auto double_not = AIG::new_not(AIG::new_not(and_ab));
        auto r = rw.rewrite(double_not);
        check(functionally_equal(and_ab, r, 2), "NOT(NOT(AND(a,b))) = AND(a,b)");
        check(count_nodes(r) == 3, "NOT(NOT(AND(a,b))) is 3 nodes");
    }

    // NOT applied to NOT-shaped AND (l==r) must NOT trigger the new rule
    // (the new rule guards l->l != l->r). new_not's double-NOT rule handles it.
    {
        auto not_a = AIG::new_not(a);
        auto r = rw.rewrite(AIG::new_not(not_a));
        check(functionally_equal(a, r, 1), "NOT(NOT(lit)) = lit functional");
        check(count_nodes(r) == 1, "NOT(NOT(lit)) is 1 node");
    }
}

void test_rewrite_preserves_null() {
    AIGRewriter rw;
    auto r = rw.rewrite(nullptr);
    check(r == nullptr, "rewrite(nullptr) = nullptr");
}

void test_distribution() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;

    // AND(OR(a,b), OR(a,c)) = OR(a, AND(b,c))
    auto a_or_b = AIG::new_or(a, b);
    auto a_or_c = AIG::new_or(a, c);
    auto both = AIG::new_and(a_or_b, a_or_c);
    auto r = rw.rewrite(both);
    check(functionally_equal(both, r, 3), "distribution AND(OR(a,b),OR(a,c)) functional");
    check(count_nodes(r) <= count_nodes(both), "distribution reduces or preserves nodes");
}

void test_complex_ite_chain() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);
    auto d = AIG::new_lit(3);

    AIGRewriter rw;

    // Build a chain of ITEs that should simplify
    auto ite1 = AIG::new_ite(b, c, a);         // ITE(a, b, c)
    auto ite2 = AIG::new_ite(ite1, d, a);      // ITE(a, ite1, d)
    auto r = rw.rewrite(ite2);
    check(functionally_equal(ite2, r, 4), "complex ITE chain functional");

    // ITE(a, b, b) should already be b
    auto trivial = AIG::new_ite(b, b, a);
    auto r2 = rw.rewrite(trivial);
    check(functionally_equal(trivial, r2, 3), "ITE(a,b,b)=b functional");
    check(count_nodes(r2) == 1, "ITE(a,b,b) is single node");
}

void test_deep_or_chain_flattening() {
    // Build a deeply nested OR chain: OR(g0, OR(g1, OR(g2, ... OR(g_{n-1}, base))))
    // This mimics what happens after many ITE repairs with TRUE value
    const uint32_t n = 10;
    auto base = AIG::new_lit(n); // base variable
    aig_ptr chain = base;
    for (uint32_t i = 0; i < n; i++) {
        chain = AIG::new_or(AIG::new_lit(i), chain);
    }

    size_t nodes_before = count_nodes(chain);

    AIGRewriter rw;
    auto r = rw.rewrite(chain);
    check(functionally_equal(chain, r, n + 1), "deep OR chain flattening functional");

    size_t nodes_after = count_nodes(r);
    // A balanced OR tree of 11 inputs needs ~10 AND nodes (for the OR encoding)
    // The linear chain has ~20 nodes (each OR = 2 nodes due to NOT encoding)
    check(nodes_after <= nodes_before, "deep OR chain nodes reduced or equal");
    cout << "  OR chain nodes: " << nodes_before << " -> " << nodes_after << endl;
}

void test_deep_and_chain_flattening() {
    const uint32_t n = 10;
    auto base = AIG::new_lit(n);
    aig_ptr chain = base;
    for (uint32_t i = 0; i < n; i++) {
        chain = AIG::new_and(AIG::new_not(AIG::new_lit(i)), chain);
    }

    AIGRewriter rw;
    auto r = rw.rewrite(chain);
    check(functionally_equal(chain, r, n + 1), "deep AND chain flattening functional");
    check(count_nodes(r) <= count_nodes(chain), "deep AND chain node count reduced or equal");
}

int main() {
    cout << "=== AIG Rewriter Tests ===" << endl;

    test_const_prop();
    test_complement_elim();
    test_idempotent();
    test_absorption();
    test_subsumption();
    test_nested_and_flatten();
    test_ite_pattern();
    test_deep_complement_in_chain();
    test_multi_aig_sharing();
    test_large_and_chain();
    test_double_negation();
    test_not_through_and();
    test_rewrite_preserves_null();
    test_distribution();
    test_complex_ite_chain();
    test_deep_or_chain_flattening();
    test_deep_and_chain_flattening();

    cout << endl << "Results: " << tests_passed << " passed, " << tests_failed << " failed" << endl;
    return tests_failed > 0 ? 1 : 0;
}
