/*
 Arjun - AIG Rewriting System

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#pragma once

#include "arjun.h"
#include <cstdint>
#include <vector>

#if defined(_WIN32) || defined(__CYGWIN__)
  #define ARJUN_PUBLIC __declspec(dllexport)
#else
  #define ARJUN_PUBLIC __attribute__((visibility("default")))
#endif

namespace ArjunNS {

// Statistics for AIG rewriting
struct AIGRewriteStats {
    uint64_t structural_hash_hits = 0;
    uint64_t total_passes = 0;
    uint64_t nodes_before = 0;
    uint64_t nodes_after = 0;

    // SAT sweeping (FRAIG-lite) counters.
    uint64_t sweep_sim_groups = 0;
    uint64_t sweep_sat_checks = 0;
    uint64_t sweep_merges = 0;
    uint64_t sweep_cex_refuted = 0;

    void print(int verb) const;
    void clear();
};

class ARJUN_PUBLIC AIGRewriter {
public:
    AIGRewriter() = default;

    // Rewrite a single AIG to a simpler equivalent. Structure-preserving —
    // the result is guaranteed to be no larger than the input.
    aig_ptr rewrite(const aig_ptr& aig);

    // Rewrite a vector of AIGs (sharing structure across all)
    void rewrite_all(std::vector<aig_ptr>& defs, int verb = 1);

    // FRAIG-lite SAT sweeping. Currently a no-op; retained for API
    // compatibility with callers that opt-in.
    void sat_sweep(std::vector<aig_ptr>& defs, int verb = 1);

    void set_sat_sweep(bool b) { sat_sweep_enabled = b; }
    void set_sat_sweep_sim_patterns(uint32_t) {}
    void set_sat_sweep_max_class(uint32_t) {}

    const AIGRewriteStats& get_stats() const { return stats; }

private:
    AIGRewriteStats stats;
    bool sat_sweep_enabled = false;
};

} // namespace ArjunNS
