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

static size_t count_nodes(const aig_lit& aig) {
    return AIG::count_aig_nodes_fast(aig);
}

// Evaluate an AIG with a given assignment using the public evaluate() method
static bool eval(const aig_lit& aig, uint32_t num_vars, uint32_t mask) {
    std::vector<CMSat::lbool> vals(num_vars);
    for (uint32_t v = 0; v < num_vars; v++) {
        vals[v] = ((mask >> v) & 1) ? CMSat::l_True : CMSat::l_False;
    }
    std::vector<aig_lit> defs(num_vars, nullptr);
    std::map<aig_lit, CMSat::lbool> cache;
    auto result = AIG::evaluate(vals, aig, defs, cache);
    assert(result != CMSat::l_Undef);
    return result == CMSat::l_True;
}

// Check that two AIGs are functionally equivalent over all assignments
// of variables 0..num_vars-1
static bool functionally_equal(const aig_lit& a, const aig_lit& b, uint32_t num_vars) {
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

    AIGRewriter rw;

    // AND(a, AND(~a, b)) = FALSE
    auto na_b = AIG::new_and(na, b);
    auto a_and_na_b = AIG::new_and(a, na_b);
    auto r1 = rw.rewrite(a_and_na_b);
    check(functionally_equal(a_and_na_b, r1, 2), "AND(a, AND(~a, b)) = FALSE functional");
    check(count_nodes(r1) == 1 && !eval(r1, 2, 0), "AND(a, AND(~a, b)) is FALSE");

    // OR(a, OR(~a, b)) = TRUE
    auto na_or_b = AIG::new_or(na, b);
    auto a_or_na_or_b = AIG::new_or(a, na_or_b);
    auto r2 = rw.rewrite(a_or_na_or_b);
    check(functionally_equal(a_or_na_or_b, r2, 2), "OR(a, OR(~a, b)) = TRUE functional");
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

    vector<aig_lit> defs = {aig1, aig2};
    rw.rewrite_all(defs, 0);

    check(functionally_equal(aig1, defs[0], 3), "multi-AIG rewrite preserves AIG 1");
    check(functionally_equal(aig2, defs[1], 3), "multi-AIG rewrite preserves AIG 2");
}

void test_large_and_chain() {
    // AND(x0, AND(x1, AND(x2, ... AND(x0, x1)...)))
    // The repeated x0 should be eliminated
    const uint32_t n = 8;
    vector<aig_lit> lits;
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

    // NOT(AND(a,b)) -> NAND(a,b) = AND(a,b,neg=true): 4 nodes collapse to 3.
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

    // NOT(AND(a, AND(b,c))): NOT is just an edge-flip (no inverter node), so
    // node count is unchanged; only semantics must match.
    {
        auto and_bc = AIG::new_and(b, c);
        auto and_abc = AIG::new_and(a, and_bc);
        auto before = count_nodes(AIG::new_not(and_abc));
        auto not_abc = AIG::new_not(and_abc);
        auto r = rw.rewrite(not_abc);
        check(functionally_equal(not_abc, r, 3), "NOT(AND(a,AND(b,c))) functional");
        check(count_nodes(r) <= before, "NOT(AND(a,AND(b,c))) no growth");
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
    aig_lit chain = base;
    for (uint32_t i = 0; i < n; i++) {
        chain = AIG::new_or(AIG::new_lit(i), chain);
    }

    size_t nodes_before = count_nodes(chain);

    AIGRewriter rw;
    auto r = rw.rewrite(chain);
    check(functionally_equal(chain, r, n + 1), "deep OR chain flattening functional");

    size_t nodes_after = count_nodes(r);
    // Rewrite must never grow the AIG (it reverts if it would).
    check(nodes_after <= nodes_before, "deep OR chain nodes reduced or equal");
    cout << "  OR chain nodes: " << nodes_before << " -> " << nodes_after << endl;
}

void test_deep_and_chain_flattening() {
    const uint32_t n = 10;
    auto base = AIG::new_lit(n);
    aig_lit chain = base;
    for (uint32_t i = 0; i < n; i++) {
        chain = AIG::new_and(AIG::new_not(AIG::new_lit(i)), chain);
    }

    AIGRewriter rw;
    auto r = rw.rewrite(chain);
    check(functionally_equal(chain, r, n + 1), "deep AND chain flattening functional");
    check(count_nodes(r) <= count_nodes(chain), "deep AND chain node count reduced or equal");
}

// AND-of-AND contradiction: AND(AND(a,b), AND(~a,c)) collapses to FALSE in one
// simplify_pass. Tests the 4-fanin complement check (Brummayer algebraic rules).
void test_and_of_and_contradiction() {
    auto a = AIG::new_lit(0);
    auto na = AIG::new_lit(0, true);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;
    auto ab = AIG::new_and(a, b);
    auto nac = AIG::new_and(na, c);
    auto both = AIG::new_and(ab, nac);
    auto r = rw.rewrite(both);
    check(functionally_equal(both, r, 3), "AND(AND(a,b), AND(~a,c)) functional");
    check(count_nodes(r) == 1 && !eval(r, 3, 0) && !eval(r, 3, 7),
          "AND(AND(a,b), AND(~a,c)) = FALSE");
    check(rw.get_stats().complement_elim >= 1,
          "AND-of-AND contradiction bumps complement_elim");
}

// ITE(s, s, e) = OR(s, e): with the then-arm equal to the selector, the OR view
// collapses to s∨e. Verifies the rewriter sees that.
void test_ite_t_eq_sel() {
    auto s = AIG::new_lit(0);
    auto e = AIG::new_lit(1);

    AIGRewriter rw;
    // ITE(s, s, e) via new_ite: returns OR(AND(s, s), AND(~s, e)) = OR(s, AND(~s, e)).
    auto ite = AIG::new_ite(s, e, CMSat::Lit(0, false));
    auto r = rw.rewrite(ite);
    check(functionally_equal(ite, r, 2), "ITE(s,s,e) functional");
    // Functionally s∨e: must be TRUE in 3 of 4 input combos.
    int true_count = 0;
    for (uint32_t m = 0; m < 4; m++) if (eval(r, 2, m)) true_count++;
    check(true_count == 3, "ITE(s,s,e) = s∨e truth count");
}

// ITE(s, t, s) = AND(s, t). Similar shape with the e-arm matching the
// selector. Verifies the symmetric fold path.
void test_ite_e_eq_sel() {
    auto s = AIG::new_lit(0);
    auto t = AIG::new_lit(1);

    AIGRewriter rw;
    auto ite = AIG::new_ite(t, s, CMSat::Lit(0, false));  // ITE(s, t, s)
    auto r = rw.rewrite(ite);
    check(functionally_equal(ite, r, 2), "ITE(s,t,s) functional");
    int true_count = 0;
    for (uint32_t m = 0; m < 4; m++) if (eval(r, 2, m)) true_count++;
    check(true_count == 1, "ITE(s,t,s) = s∧t truth count");
}

// and_or_distrib: AND(OR(a, b), OR(a, c)) = OR(a, AND(b, c)).
// Pins both functional correctness and that the counter is bumped.
void test_and_or_distrib() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;
    auto a_or_b = AIG::new_or(a, b);
    auto a_or_c = AIG::new_or(a, c);
    auto both = AIG::new_and(a_or_b, a_or_c);
    auto r = rw.rewrite(both);
    check(functionally_equal(both, r, 3), "AND(OR(a,b), OR(a,c)) functional");
    check(rw.get_stats().and_or_distrib >= 1,
          "and_or_distrib counter bumped");
}

// structural_hash_hits: the same AND subtree built twice from fresh edges
// should collapse to one node after rewrite_all across two AIGs.
void test_structural_hash_hits() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;
    auto ab1 = AIG::new_and(a, b);
    auto ab2 = AIG::new_and(a, b); // fresh independent AND with the same fanins
    auto root1 = AIG::new_and(ab1, c);
    auto root2 = AIG::new_and(ab2, c);

    vector<aig_lit> defs = {root1, root2};
    rw.rewrite_all(defs, 0);
    check(rw.get_stats().structural_hash_hits >= 1,
          "duplicate AND subtrees produce a structural-hash hit");
    check(functionally_equal(root1, defs[0], 3),
          "structural-hash defs[0] functional");
    check(functionally_equal(root2, defs[1], 3),
          "structural-hash defs[1] functional");
}

// BCP-lite disjunct drill: AND(a, OR(AND(a, x), d2)) -> AND(a, OR(x, d2)).
// Verifies the disj-drill branch fires and stays equivalent.
void test_bcp_disjunct_drill_share() {
    auto a = AIG::new_lit(0);
    auto x = AIG::new_lit(1);
    auto d = AIG::new_lit(2);

    AIGRewriter rw;
    auto and_ax = AIG::new_and(a, x);
    auto or_ax_d = AIG::new_or(and_ax, d);
    auto root = AIG::new_and(a, or_ax_d);
    const auto abs_before = rw.get_stats().absorption;
    auto r = rw.rewrite(root);
    check(functionally_equal(root, r, 3), "BCP drill AND(a,OR(AND(a,x),d)) functional");
    check(rw.get_stats().absorption > abs_before,
          "BCP drill shared bumps absorption");
}

// Multi-level BCP: nested AND(a, OR(AND(b, OR(AND(a,x), c)), d)). Needs multiple
// iterations to compose folds — tests the fixed-point loop across passes.
void test_bcp_multi_level() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);
    auto d = AIG::new_lit(3);
    auto x = AIG::new_lit(4);

    auto and_ax = AIG::new_and(a, x);
    auto or_ax_c = AIG::new_or(and_ax, c);
    auto and_b_or = AIG::new_and(b, or_ax_c);
    auto or_outer = AIG::new_or(and_b_or, d);
    auto root = AIG::new_and(a, or_outer);

    size_t before = count_nodes(root);

    AIGRewriter rw;
    auto r = rw.rewrite(root);
    check(functionally_equal(root, r, 5),
          "multi-level BCP functional");
    cout << "  multi-level BCP nodes: " << before << " -> " << count_nodes(r) << endl;
    // Semantic equivalence over all 32 assignments is the real property;
    // the node-count check below is a soft expectation.
    check(count_nodes(r) <= before, "multi-level BCP doesn't grow AIG");
}

// BCP-lite drill with complement: AND(a, OR(AND(~a, x), d2)) = AND(a, d2) —
// the ~a disjunct is FALSE under a. Strongest of the two BCP-lite cases.
void test_bcp_disjunct_drill_complement() {
    auto a = AIG::new_lit(0);
    auto na = AIG::new_lit(0, true);
    auto x = AIG::new_lit(1);
    auto d = AIG::new_lit(2);

    AIGRewriter rw;
    auto and_nax = AIG::new_and(na, x);
    auto or_nax_d = AIG::new_or(and_nax, d);
    auto root = AIG::new_and(a, or_nax_d);
    const auto compl_before = rw.get_stats().complement_elim;
    auto r = rw.rewrite(root);
    check(functionally_equal(root, r, 3),
          "BCP drill AND(a,OR(AND(~a,x),d)) functional");
    check(rw.get_stats().complement_elim > compl_before,
          "BCP drill complement bumps complement_elim");
    // Result is AND(a, d) — 2 lits + 1 AND = 3 nodes.
    check(count_nodes(r) <= 3, "BCP complement drill reduces to AND(a, d)");
}

// is_or drill-down into AND fanin: AND(AND(a,b), OR(a,c)) absorbs the OR since
// a∧b implies a. Verifies the sub-fanin absorption branch.
void test_is_or_drill_into_and() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;
    auto ab = AIG::new_and(a, b);
    auto a_or_c = AIG::new_or(a, c);
    auto both = AIG::new_and(ab, a_or_c);
    const auto abs_before = rw.get_stats().absorption;
    auto r = rw.rewrite(both);
    check(functionally_equal(both, r, 3),
          "AND(AND(a,b), OR(a,c)) functional");
    check(rw.get_stats().absorption > abs_before,
          "drill-down absorption fires");
    // Result is AND(a, b) — 3 nodes (2 lits + 1 AND).
    check(count_nodes(r) <= 3,
          "AND(AND(a,b), OR(a,c)) reduces to AND(a,b)");
}

// is_or drill-down with complement: AND(AND(a,b), OR(~a,c)) — under a∧b the ~a
// disjunct is false, so OR reduces to c, giving AND(a,b,c). Tests the complement path.
void test_is_or_drill_into_and_complement() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);
    auto na = AIG::new_lit(0, true);

    AIGRewriter rw;
    auto ab = AIG::new_and(a, b);
    auto na_or_c = AIG::new_or(na, c);
    auto both = AIG::new_and(ab, na_or_c);
    const auto compl_before = rw.get_stats().complement_elim;
    auto r = rw.rewrite(both);
    check(functionally_equal(both, r, 3),
          "AND(AND(a,b), OR(~a,c)) functional");
    check(rw.get_stats().complement_elim > compl_before,
          "drill-down complement reduction fires");
}

// Complement absorption with literal-vs-OR-disjunct: AND(a, OR(~a, b)) = AND(a, b)
// — exercises the complement_elim path on the is_or(r) branch.
void test_complement_absorption_or() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto na = AIG::new_lit(0, true);

    AIGRewriter rw;
    auto na_or_b = AIG::new_or(na, b);
    auto root = AIG::new_and(a, na_or_b);
    const auto compl_before = rw.get_stats().complement_elim;
    auto r = rw.rewrite(root);
    check(functionally_equal(root, r, 2), "AND(a, OR(~a, b)) functional");
    check(rw.get_stats().complement_elim > compl_before,
          "AND(a, OR(~a, b)) bumps complement_elim");
}

// XOR pattern bump: XOR(p, q) leaves nodes alone but bumps xor_simplify so
// the fuzzer / consumer can confirm the pattern was observed.
void test_xor_pattern_recognized() {
    auto p = AIG::new_lit(0);
    auto q = AIG::new_lit(1);
    auto xor_pq = AIG::new_or(
        AIG::new_and(p, AIG::new_not(q)),
        AIG::new_and(AIG::new_not(p), q));

    AIGRewriter rw;
    auto r = rw.rewrite(xor_pq);
    check(functionally_equal(xor_pq, r, 2), "XOR(p,q) functional");
    check(rw.get_stats().xor_simplify >= 1,
          "XOR pattern bumps xor_simplify counter");
}

// Shared-conjunct factoring: (a∧b) ∨ (a∧c) ∨ (a∧d) collapses to a ∧ (b∨c∨d)
// via simplify_pass's resolve/distribute rule.
void test_fixed_point_iteration() {
    // (a∧b) ∨ (a∧c) ∨ (a∧d) collapses to a ∧ (b∨c∨d); the single-pass result
    // is bigger than the fixed-point result.
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);
    auto d = AIG::new_lit(3);

    auto ab = AIG::new_and(a, b);
    auto ac = AIG::new_and(a, c);
    auto ad = AIG::new_and(a, d);
    auto or1 = AIG::new_or(ab, ac);
    auto or2 = AIG::new_or(or1, ad);

    size_t before = count_nodes(or2);

    AIGRewriter rw;
    auto r = rw.rewrite(or2);
    check(functionally_equal(or2, r, 4), "fixed-point iteration functional");
    // Fixed-point result factors shared `a` to the top; best case is
    // 4 lits + 2 ANDs = 6 nodes, which iteration achieves.
    check(count_nodes(r) < before, "fixed-point shrinks AIG");
}

// OR-of-OR with shared disjunct: OR(OR(a,b), OR(a,c)) collapses via the
// AND-of-AND rule on the De Morgan dual (shared ~a in the negated-lit ANDs).
void test_or_of_or_sharing() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;
    auto ab = AIG::new_or(a, b);
    auto ac = AIG::new_or(a, c);
    auto both = AIG::new_or(ab, ac);
    auto r = rw.rewrite(both);
    check(functionally_equal(both, r, 3), "OR(OR(a,b), OR(a,c)) functional");
    check(rw.get_stats().absorption >= 1,
          "OR-of-OR sharing bumps absorption (via AND-of-AND on De Morgan)");
}

// OR-of-OR tautology: OR(OR(a,b), OR(~a,c)) is always TRUE (a or ~a holds).
// De Morgan dual is AND-of-AND with complementary fanins, folding to FALSE.
void test_or_of_or_tautology() {
    auto a = AIG::new_lit(0);
    auto na = AIG::new_lit(0, true);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;
    auto ab = AIG::new_or(a, b);
    auto nac = AIG::new_or(na, c);
    auto both = AIG::new_or(ab, nac);
    auto r = rw.rewrite(both);
    check(functionally_equal(both, r, 3),
          "OR(OR(a,b), OR(~a,c)) functional");
    // TRUE in all 8 assignments of 3 vars.
    int true_count = 0;
    for (uint32_t m = 0; m < 8; m++) if (eval(r, 3, m)) true_count++;
    check(true_count == 8, "OR(OR(a,b), OR(~a,c)) = TRUE");
    check(count_nodes(r) == 1, "OR(OR(a,b), OR(~a,c)) folds to const");
}

// AND-of-AND with shared fanin: AND(AND(a,b), AND(a,c)) factors to
// AND(a, AND(b,c)), exposing AND(b,c) for hash-consing and the shared 'a'.
void test_and_of_and_sharing() {
    auto a = AIG::new_lit(0);
    auto b = AIG::new_lit(1);
    auto c = AIG::new_lit(2);

    AIGRewriter rw;
    auto ab = AIG::new_and(a, b);
    auto ac = AIG::new_and(a, c);
    auto both = AIG::new_and(ab, ac);
    auto r = rw.rewrite(both);
    check(functionally_equal(both, r, 3), "AND(AND(a,b), AND(a,c)) functional");
    // Original: 3 lit + 3 AND = 6 nodes. After rewrite: 3 lit + AND(b,c) +
    // AND(a, AND(b,c)) = 5 nodes.
    check(count_nodes(r) <= 5, "AND-of-AND sharing reduces nodes");
    check(rw.get_stats().absorption >= 1,
          "AND-of-AND sharing bumps absorption");
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
    test_and_of_and_contradiction();
    test_fixed_point_iteration();
    test_or_of_or_sharing();
    test_or_of_or_tautology();
    test_and_of_and_sharing();
    test_ite_t_eq_sel();
    test_ite_e_eq_sel();
    test_and_or_distrib();
    test_structural_hash_hits();
    test_complement_absorption_or();
    test_is_or_drill_into_and();
    test_is_or_drill_into_and_complement();
    test_bcp_disjunct_drill_share();
    test_bcp_disjunct_drill_complement();
    test_bcp_multi_level();
    test_xor_pattern_recognized();

    cout << endl << "Results: " << tests_passed << " passed, " << tests_failed << " failed" << endl;
    return tests_failed > 0 ? 1 : 0;
}
