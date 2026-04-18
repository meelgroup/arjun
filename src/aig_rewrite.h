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
#include <unordered_map>
#include <cstdint>
#include <functional>

// Visibility export macros for proper symbol visibility with -fvisibility=hidden
#if defined(_WIN32) || defined(__CYGWIN__)
  #ifdef arjun_EXPORTS
    #define ARJUN_PUBLIC __declspec(dllexport)
  #else
    #define ARJUN_PUBLIC __declspec(dllimport)
  #endif
#else
  #if defined(arjun_EXPORTS)
    #define ARJUN_PUBLIC __attribute__((visibility("default")))
  #else
    #define ARJUN_PUBLIC
  #endif
#endif

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

class ARJUN_PUBLIC AIGRewriter {
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

    // Structural hash table for canonical AND nodes. In practice the
    // rewriter only hash-conses t_and nodes with var == none_var, so we
    // key on just (neg, l, r) instead of the full 5-tuple -- a much
    // cheaper hash than the old std::tuple<AIGT,uint32_t,bool,...> key.
    struct StructKey {
        bool neg;
        AIG* l;
        AIG* r;
        bool operator==(const StructKey& o) const noexcept {
            return neg == o.neg && l == o.l && r == o.r;
        }
    };
    struct StructKeyHash {
        size_t operator()(const StructKey& k) const noexcept {
            // Combine the two pointers via a cheap multiplicative mix.
            size_t a = reinterpret_cast<uintptr_t>(k.l);
            size_t b = reinterpret_cast<uintptr_t>(k.r);
            size_t h = a * 0x9e3779b97f4a7c15ULL;
            h ^= b + (h >> 32);
            h *= 0xff51afd7ed558ccdULL;
            h ^= (size_t)k.neg;
            return h;
        }
    };
    std::unordered_map<StructKey, aig_ptr, StructKeyHash> struct_hash;

    // Hash on the shared_ptr's raw pointer. Reused for every per-pass cache.
    struct AigPtrHash {
        size_t operator()(const aig_ptr& p) const noexcept {
            return std::hash<AIG*>{}(p.get());
        }
    };
    using AigPtrMap = std::unordered_map<aig_ptr, aig_ptr, AigPtrHash>;
    using AigPtrDepthMap = std::unordered_map<aig_ptr, size_t, AigPtrHash>;

    // --- Core rewrite passes ---

    // Pass 1: Bottom-up simplification with structural rules
    aig_ptr simplify_pass(const aig_ptr& aig, AigPtrMap& cache);

    // Pass 2: Structural hashing / CSE
    aig_ptr hash_cons(const aig_ptr& aig, AigPtrMap& cache);

    // Pass 3: Multi-level absorption and complementary elimination
    aig_ptr deep_absorb(const aig_ptr& aig, AigPtrMap& cache);

    // Pass 4: ITE chain detection and depth reduction
    aig_ptr flatten_ite_chains(const aig_ptr& aig, AigPtrMap& cache);

    // Compute depth of an AIG
    size_t compute_depth(const aig_ptr& aig, AigPtrDepthMap& cache) const;

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
