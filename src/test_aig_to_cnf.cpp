/*
 Arjun - AIG-to-CNF pure-chain regression test

 Verifies that the AIG -> CNF encoder collapses structural chains into
 single k-ary gates (one helper, one "big" clause plus k binary clauses).
 These are canonical best-cases: if a wide positive AND chain doesn't fuse
 into a single k-ary AND, the encoder has lost its most important
 optimisation.

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#include "aig_to_cnf.h"
#include "arjun.h"
#include <cryptominisat5/cryptominisat.h>

#include <cassert>
#include <cstdlib>
#include <iostream>
#include <vector>

using namespace ArjunNS;
using namespace CMSat;

static int failures = 0;

static void fail(const std::string& msg) {
    std::cerr << "FAIL: " << msg << std::endl;
    failures++;
}

// Build AND(l_0, l_1, ..., l_{N-1}) as a left-leaning chain of AIG AND
// nodes using distinct positive literals.
static aig_ptr build_and_chain(uint32_t n) {
    aig_ptr cur = AIG::new_lit(0, false);
    for (uint32_t i = 1; i < n; i++) {
        cur = AIG::new_and(cur, AIG::new_lit(i, false));
    }
    return cur;
}

static aig_ptr build_or_chain(uint32_t n) {
    aig_ptr cur = AIG::new_lit(0, false);
    for (uint32_t i = 1; i < n; i++) {
        cur = AIG::new_or(cur, AIG::new_lit(i, false));
    }
    return cur;
}

// Balanced AND tree: pairwise bottom-up. Same semantics as the linear
// chain, but every internal AND has fanout exactly 1 -- still must flatten.
static aig_ptr build_balanced_and_tree(uint32_t n) {
    std::vector<aig_ptr> level;
    level.reserve(n);
    for (uint32_t i = 0; i < n; i++) level.push_back(AIG::new_lit(i, false));
    while (level.size() > 1) {
        std::vector<aig_ptr> next;
        next.reserve((level.size() + 1) / 2);
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            next.push_back(AIG::new_and(level[i], level[i+1]));
        }
        if (level.size() % 2 == 1) next.push_back(level.back());
        level = std::move(next);
    }
    return level[0];
}

static aig_ptr build_balanced_or_tree(uint32_t n) {
    std::vector<aig_ptr> level;
    level.reserve(n);
    for (uint32_t i = 0; i < n; i++) level.push_back(AIG::new_lit(i, false));
    while (level.size() > 1) {
        std::vector<aig_ptr> next;
        next.reserve((level.size() + 1) / 2);
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            next.push_back(AIG::new_or(level[i], level[i+1]));
        }
        if (level.size() % 2 == 1) next.push_back(level.back());
        level = std::move(next);
    }
    return level[0];
}

struct EncResult {
    uint64_t clauses;
    uint64_t helpers;
    uint64_t kary_and;
    uint64_t kary_and_width_total;
    uint64_t kary_or;
    uint64_t kary_or_width_total;
    Lit out;
};

static EncResult encode(const aig_ptr& root, uint32_t nvars) {
    SATSolver s;
    s.set_verbosity(0);
    s.new_vars(nvars);
    AIGToCNF<SATSolver> enc(s);
    // Disable cut-based CNF so n=4 chains surface as k-ary gates here.
    // The cut encoder would otherwise absorb small (≤4-leaf) cones into
    // CUT patterns, which is what these tests are explicitly NOT
    // checking.
    enc.set_cut_cnf(false);
    Lit out = enc.encode(root);
    const auto& st = enc.get_stats();
    return {
        st.clauses_added,
        st.helpers_added,
        st.kary_and_count,
        st.kary_and_width_total,
        st.kary_or_count,
        st.kary_or_width_total,
        out
    };
}

static void check_single_kand(const char* name, aig_ptr root, uint32_t n) {
    EncResult r = encode(root, n);
    std::cout << name << " (n=" << n << "):"
              << "  clauses=" << r.clauses
              << "  helpers=" << r.helpers
              << "  kAND=" << r.kary_and
              << "  kAND_width_total=" << r.kary_and_width_total
              << std::endl;
    if (r.kary_and != 1u) {
        fail(std::string(name) + ": expected exactly 1 k-ary AND, got "
             + std::to_string(r.kary_and));
    }
    if (r.kary_and_width_total != n) {
        fail(std::string(name) + ": expected k-ary AND width " + std::to_string(n)
             + ", got " + std::to_string(r.kary_and_width_total));
    }
    if (r.helpers != 1u) {
        fail(std::string(name) + ": expected 1 helper, got "
             + std::to_string(r.helpers));
    }
    // k binary + 1 big clause
    if (r.clauses != n + 1) {
        fail(std::string(name) + ": expected " + std::to_string(n + 1)
             + " clauses, got " + std::to_string(r.clauses));
    }
}

static void check_single_kor(const char* name, aig_ptr root, uint32_t n) {
    EncResult r = encode(root, n);
    std::cout << name << " (n=" << n << "):"
              << "  clauses=" << r.clauses
              << "  helpers=" << r.helpers
              << "  kOR=" << r.kary_or
              << "  kOR_width_total=" << r.kary_or_width_total
              << std::endl;
    if (r.kary_or != 1u) {
        fail(std::string(name) + ": expected exactly 1 k-ary OR, got "
             + std::to_string(r.kary_or));
    }
    if (r.kary_or_width_total != n) {
        fail(std::string(name) + ": expected k-ary OR width " + std::to_string(n)
             + ", got " + std::to_string(r.kary_or_width_total));
    }
    if (r.helpers != 1u) {
        fail(std::string(name) + ": expected 1 helper, got "
             + std::to_string(r.helpers));
    }
    if (r.clauses != n + 1) {
        fail(std::string(name) + ": expected " + std::to_string(n + 1)
             + " clauses, got " + std::to_string(r.clauses));
    }
}

int main() {
    // Linear chain, all positive distinct literals: must produce exactly
    // one k-ary AND of width n.
    for (uint32_t n : {4u, 16u, 64u, 256u}) {
        check_single_kand("linear_and_chain", build_and_chain(n), n);
    }
    // Same for OR.
    for (uint32_t n : {4u, 16u, 64u, 256u}) {
        check_single_kor("linear_or_chain", build_or_chain(n), n);
    }
    // Balanced binary tree (log-depth): still must flatten to one k-ary gate.
    for (uint32_t n : {4u, 16u, 64u, 256u}) {
        check_single_kand("balanced_and_tree", build_balanced_and_tree(n), n);
    }
    for (uint32_t n : {4u, 16u, 64u, 256u}) {
        check_single_kor("balanced_or_tree", build_balanced_or_tree(n), n);
    }

    if (failures != 0) {
        std::cerr << failures << " failure(s)" << std::endl;
        return 1;
    }
    std::cout << "All pure-chain AIG->CNF tests passed." << std::endl;
    return 0;
}
