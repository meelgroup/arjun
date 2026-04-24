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

// Statistics for AIG rewriting.
struct AIGRewriteStats {
    uint64_t const_prop = 0;
    uint64_t complement_elim = 0;
    uint64_t idempotent_elim = 0;
    uint64_t absorption = 0;
    uint64_t and_or_distrib = 0;
    uint64_t ite_simplify = 0;
    uint64_t structural_hash_hits = 0;
    uint64_t total_passes = 0;
    uint64_t nodes_before = 0;
    uint64_t nodes_after = 0;

    // SAT sweeping (FRAIG-lite) counters.
    uint64_t sweep_sim_groups = 0;
    uint64_t sweep_sat_checks = 0;
    uint64_t sweep_merges = 0;
    uint64_t sweep_cex_refuted = 0;
    uint64_t sweep_timeouts = 0;         // SAT checks hitting the conflict budget (l_Undef)
    uint64_t sweep_class_aborts = 0;     // Classes abandoned after too many consecutive refutations
    uint64_t sweep_budget_exhausted = 0; // Wall-clock budget hit; remaining classes skipped
    uint64_t sweep_self_ref_reverts = 0;
    uint64_t sweep_cycle_reverts = 0;

    void print(int verb) const;
    void clear();
};

class ARJUN_PUBLIC AIGRewriter {
public:
    AIGRewriter() = default;

    // Rewrite a single AIG to a simpler equivalent.
    aig_ptr rewrite(const aig_ptr& aig);

    // Rewrite a vector of AIGs, sharing structure across all.
    void rewrite_all(std::vector<aig_ptr>& defs, int verb = 1);

    // FRAIG-lite SAT sweeping: detect and merge functionally equivalent
    // AND nodes across `defs`. Every merge is verified via CryptoMiniSat.
    // Opt-in; no-op unless set_sat_sweep(true) was called.
    void sat_sweep(std::vector<aig_ptr>& defs, int verb = 1);

    void set_sat_sweep(bool b) { sat_sweep_enabled = b; }
    void set_sat_sweep_sim_patterns(uint32_t n) { sweep_sim_rounds = n; }
    void set_sat_sweep_max_class(uint32_t n) { sweep_max_class_size = n; }
    void set_sat_sweep_conflict_budget(uint64_t n) { sweep_conflict_budget = n; }
    void set_sat_sweep_time_budget(double s) { sweep_time_budget_s = s; }

    const AIGRewriteStats& get_stats() const { return stats; }

private:
    AIGRewriteStats stats;
    bool sat_sweep_enabled = false;
    // Number of 64-bit simulation rounds (each round = 64 patterns). More
    // rounds = fewer bogus candidate classes at linear simulation cost.
    uint32_t sweep_sim_rounds = 4;
    // Skip classes larger than this to avoid quadratic SAT churn on
    // degenerate "all constants" groups simulation can't split.
    uint32_t sweep_max_class_size = 64;
    // Per-check CMS conflict budget. Bounds worst-case solve time on big
    // cones. l_Undef from hitting the budget is treated as "cannot prove".
    uint64_t sweep_conflict_budget = 500;
    // Give up on a class after this many consecutive refutations/timeouts
    // with no merge. A class that keeps refuting is almost always a
    // simulation coincidence — further SAT checks on it are wasted time.
    uint32_t sweep_class_abort_streak = 2;
    // Wall-clock budget for the entire sat_sweep() call. A safety net for
    // pathological blow-ups on huge AIGs; not a primary throttle — the
    // per-class abort streak + conflict budget should already keep useful
    // work inside a tight envelope.
    double sweep_time_budget_s = 60.0;

    // Structural hash table for canonical AND nodes. Keyed on the two signed
    // child edges (nid + sign). In the new model an AND node has no output
    // sign of its own — the outer sign lives on the referring edge, so it's
    // never part of the key.
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

    // Per-pass caches map SOURCE NODE → rebuilt signed edge for the node's
    // POSITIVE value. Callers XOR in the incoming edge sign on return.
    using NodeRebuildMap = std::unordered_map<const AIG*, aig_lit>;

    // Bottom-up simplification: constant propagation, idempotent elimination,
    // complementary-pair detection, local absorption, OR-subsumption,
    // resolution / distribution on AND-of-ORs. Counters for each rule land
    // in the matching AIGRewriteStats field.
    aig_lit simplify_pass(const aig_lit& edge, NodeRebuildMap& cache);

    // Structural-hashing pass: rebuild bottom-up, routing every AND through
    // make_canonical so structurally identical subgraphs across the AIGs
    // share a single node. Doesn't change semantics — just dedup.
    aig_lit hash_cons(const aig_lit& edge, NodeRebuildMap& cache);

    // Deep / multi-level absorption: flatten k-ary AND and OR groups,
    // dedup, detect complementary pairs, apply cross-level absorption and
    // subsumption between AND-siblings and OR-child disjuncts, plus
    // resolution on OR pairs that share all-but-one term.
    aig_lit deep_absorb(const aig_lit& edge, NodeRebuildMap& cache);

    // ITE chain depth reduction: flatten long AND / OR chains (common in
    // manthan's ITE-repair output) and rebuild them as balanced trees so
    // downstream encoders see O(log n) depth instead of O(n).
    aig_lit flatten_ite_chains(const aig_lit& edge, NodeRebuildMap& cache);

    // --- Helpers ---

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
    size_t count_nodes(const aig_ptr& aig) const;
};

} // namespace ArjunNS
