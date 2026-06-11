/*
 Arjun - AIG Rewriting System

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#pragma once

#include "arjun.h"
#include <cstdint>
#include <unordered_map>
#include <vector>

#if defined(_WIN32) || defined(__CYGWIN__)
  #define ARJUN_PUBLIC __declspec(dllexport)
#else
  #define ARJUN_PUBLIC __attribute__((visibility("default")))
#endif

namespace ArjunNS {

struct AIGRewriteStats {
    uint64_t const_prop = 0;
    uint64_t complement_elim = 0;
    uint64_t idempotent_elim = 0;
    uint64_t absorption = 0;
    uint64_t and_or_distrib = 0;
    uint64_t xor_simplify = 0;
    uint64_t structural_hash_hits = 0;
    uint64_t total_passes = 0;
    uint64_t nodes_before = 0;
    uint64_t nodes_after = 0;
    double total_time = 0.0;

    void print(int verb) const;
    void clear();
};

class ARJUN_PUBLIC AIGRewriter {
public:
    AIGRewriter() = default;

    // Rewrite a single AIG to a simpler equivalent.
    aig_ptr rewrite(const aig_ptr& aig);

    // Rewrite a vector of AIGs sharing structure across all.
    void rewrite_all(std::vector<aig_ptr>& defs, int verb = 1);

    const AIGRewriteStats& get_stats() const { return stats; }

private:
    AIGRewriteStats stats;

    // Hash-cons for AND nodes keyed on the two signed child edges (nid+sign).
    // In this AIG flavour an AND has no output sign — outer sign lives on the
    // referring edge — so it never appears in the key.
    struct StructKey {
        uint64_t l_nid;
        uint64_t r_nid;
        bool l_neg;
        bool r_neg;
        bool operator==(const StructKey& o) const noexcept {
            return l_nid == o.l_nid && r_nid == o.r_nid
                && l_neg == o.l_neg && r_neg == o.r_neg;
        }
    };
    struct StructKeyHash {
        size_t operator()(const StructKey& k) const noexcept {
            size_t a = static_cast<size_t>(k.l_nid);
            size_t b = static_cast<size_t>(k.r_nid);
            size_t h = a * 0x9e3779b97f4a7c15ULL;
            h ^= b + (h >> 32);
            h *= 0xff51afd7ed558ccdULL;
            h ^= ((size_t)k.l_neg << 1) | (size_t)k.r_neg;
            return h;
        }
    };
    std::unordered_map<StructKey, aig_node_ptr, StructKeyHash> struct_hash;

    // Hash-cons for t_lit nodes by variable id. Without this, structurally
    // identical literals would compare unequal and rules like
    // AND(a, AND(~a, b)) = FALSE would silently miss.
    std::unordered_map<uint32_t, aig_node_ptr> lit_hash;
    // Shared TRUE node so const-folded edges across the rebuild share.
    aig_node_ptr const_true_node;

    aig_lit cached_lit(uint32_t var, bool neg);
    aig_lit cached_const(bool val);

    // Maps SOURCE NODE -> rebuilt signed edge for its POSITIVE value.
    using NodeRebuildMap = std::unordered_map<const AIG*, aig_lit>;

    aig_lit simplify_pass(const aig_lit& edge, NodeRebuildMap& cache);
    aig_lit hash_cons(const aig_lit& edge, NodeRebuildMap& cache);
    aig_lit deep_absorb(const aig_lit& edge, NodeRebuildMap& cache);
    aig_lit flatten_ite_chains(const aig_lit& edge, NodeRebuildMap& cache);

    // simplify_pass rule helpers. Each returns a non-null aig_lit if the rule
    // fires, else default-constructed (no match). `pos` in the caller is set
    // from the first match in priority order.
    aig_lit try_or_sibling(const aig_lit& or_e, const aig_lit& other);
    aig_lit try_and_of_ands(const aig_lit& l, const aig_lit& r);
    aig_lit try_resolve_distribute(const aig_lit& l, const aig_lit& r);

    void collect_and_edges(const aig_lit& edge, std::vector<aig_lit>& out);
    void collect_or_edges(const aig_lit& edge, std::vector<aig_lit>& out);
    aig_lit build_and_tree(std::vector<aig_lit>& children);
    aig_lit build_or_tree(std::vector<aig_lit>& children);

    static bool is_complement(const aig_lit& a, const aig_lit& b) {
        return a.node && b.node && a.node == b.node && a.neg != b.neg;
    }
    static bool is_or(const aig_lit& a) {
        return a.node && a->type == AIGT::t_and && a.neg;
    }

    aig_lit make_canonical(const aig_lit& l, const aig_lit& r);
};

} // namespace ArjunNS
