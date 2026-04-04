/*
 Arjun - AIG Rewriting System

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#pragma once

#include "arjun.h"
#include <vector>
#include <map>
#include <set>
#include <cstdint>

namespace ArjunNS {

// Statistics for AIG rewriting
struct AIGRewriteStats {
    uint64_t const_prop = 0;
    uint64_t complement_elim = 0;
    uint64_t idempotent_elim = 0;
    uint64_t absorption = 0;
    uint64_t demorgan_push = 0;
    uint64_t and_or_distrib = 0;
    uint64_t ite_simplify = 0;
    uint64_t structural_hash_hits = 0;
    uint64_t total_passes = 0;
    uint64_t nodes_before = 0;
    uint64_t nodes_after = 0;

    void print(int verb) const;
    void clear();
};

class AIGRewriter {
public:
    AIGRewriter() = default;

    // Rewrite a single AIG to a simpler equivalent
    aig_ptr rewrite(const aig_ptr& aig);

    // Rewrite a vector of AIGs (sharing structure across all)
    void rewrite_all(std::vector<aig_ptr>& defs, int verb = 1);

    // Get rewriting statistics
    const AIGRewriteStats& get_stats() const { return stats; }

private:
    AIGRewriteStats stats;

    // Structural hash table for canonical forms
    using StructKey = std::tuple<AIGT, uint32_t, bool, aig_ptr, aig_ptr>;
    std::map<StructKey, aig_ptr> struct_hash;

    // --- Core rewrite passes ---

    // Pass 1: Bottom-up simplification with structural rules
    aig_ptr simplify_pass(const aig_ptr& aig, std::map<aig_ptr, aig_ptr>& cache);

    // Pass 2: Structural hashing / CSE
    aig_ptr hash_cons(const aig_ptr& aig, std::map<aig_ptr, aig_ptr>& cache);

    // Pass 3: Multi-level absorption and complementary elimination
    aig_ptr deep_absorb(const aig_ptr& aig, std::map<aig_ptr, aig_ptr>& cache);

    // Pass 4: ITE chain detection and depth reduction
    aig_ptr flatten_ite_chains(const aig_ptr& aig, std::map<aig_ptr, aig_ptr>& cache);

    // Compute depth of an AIG
    size_t compute_depth(const aig_ptr& aig, std::map<aig_ptr, size_t>& cache) const;

    // --- Helper functions ---

    // Collect all children of a chained AND (flattening)
    void collect_and_children(const aig_ptr& aig, std::vector<aig_ptr>& children, bool neg);

    // Collect all children of a chained OR (flattening)
    void collect_or_children(const aig_ptr& aig, std::vector<aig_ptr>& children, bool neg);

    // Build a balanced AND tree from a list of children
    aig_ptr build_and_tree(std::vector<aig_ptr>& children);

    // Build a balanced OR tree from a list of children
    aig_ptr build_or_tree(std::vector<aig_ptr>& children);

    // Check if two AIG nodes are complements of each other
    bool is_complement(const aig_ptr& a, const aig_ptr& b) const;

    // Get the "unnegated" form of an AIG (strip top-level negation)
    aig_ptr strip_not(const aig_ptr& a) const;

    // Check if an AIG represents an OR gate (AND with neg=true)
    bool is_or(const aig_ptr& a) const;

    // Make canonical form (normalize operand order)
    aig_ptr make_canonical(AIGT type, bool neg, const aig_ptr& l, const aig_ptr& r);

    // Count nodes in an AIG
    size_t count_nodes(const aig_ptr& aig) const;

    AIGManager aig_mng;
};

} // namespace ArjunNS
