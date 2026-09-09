/*
 Arjun - AIG SAT sweeping (FRAIG)

 Merges functionally equivalent AND nodes (and constant nodes) across a set
 of AIG roots. Candidates come from random simulation; each candidate pair
 is proved or refuted with a SAT solver over a Tseitin encoding of the
 AIGs alone, so merges are valid in any context. Refuting models refine the
 simulation signatures.

 Copyright (c) 2026, Mate Soos. MIT License.
 */

#pragma once

#include "arjun.h"
#include <cstdint>
#include <vector>

#if defined(_WIN32) || defined(__CYGWIN__)
  #define ARJUN_FRAIG_PUBLIC __declspec(dllexport)
#else
  #define ARJUN_FRAIG_PUBLIC __attribute__((visibility("default")))
#endif

namespace ArjunNS {

struct ARJUN_FRAIG_PUBLIC AIGFraigStats {
    uint64_t and_nodes = 0;
    uint64_t leaves = 0;
    uint64_t sim_classes = 0;
    uint64_t sim_class_nodes = 0;
    uint64_t const_cands = 0;
    uint64_t checks = 0;
    uint64_t proved_eq = 0;
    uint64_t proved_const = 0;
    uint64_t disproved = 0;
    uint64_t timeouts = 0;
    uint64_t cex_patterns = 0;
    uint64_t conflicts = 0;
    uint64_t nodes_before = 0;
    uint64_t nodes_after = 0;
    double time = 0.0;
    void print(int verb) const;
};

struct AIGFraigConf {
    uint32_t sim_words = 16;
    int64_t max_confl_per_check = 300;
    int64_t max_confl_total = 300000;
    uint32_t max_checks = 1u << 22;
    uint32_t max_cex = 2048;
    double max_time = 20.0;
    int verb = 0;
};

class ARJUN_FRAIG_PUBLIC AIGFraig {
public:
    explicit AIGFraig(const AIGFraigConf& c) : conf(c) {}
    bool fraig(std::vector<aig_lit>& roots);
    const AIGFraigStats& get_stats() const { return stats; }

private:
    AIGFraigConf conf;
    AIGFraigStats stats;
};

}
