/*
 Arjun - AIG simulation helper (factored from aig_rewrite.cpp)

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#pragma once

#include "arjun.h"
#include <cstdint>
#include <set>
#include <unordered_map>
#include <vector>

namespace ArjunNS {

// 64-bit random-pattern simulation over a topologically ordered AIG. Used by
// sat_sweep (FRAIG-lite equivalence merging) and reusable by any AIG pass
// that needs (a) a stable topo order of every reachable node, (b) per-node
// 64*R-bit signatures from a deterministic PRNG, and (c) the "used input
// vars" set.
//
// SimState only owns the topology + signatures + var set. Callers add their
// own per-pass scratch (substitution maps, candidate classes, etc.) by
// composition or inheritance.
//
// Determinism: PRNG seed is fixed and per-var pattern construction is keyed
// on iteration over an ordered std::set<uint32_t>, so two SimState runs on
// the same defs[] produce bit-identical signatures.
class SimState {
public:
    // Min rounds. The collect_topology / simulate split lets a caller
    // mutate used_vars between the two passes (e.g. add extra interface
    // vars) before simulating.
    uint32_t sim_rounds = 16;

    // raw pointer -> owning shared_ptr. Keeps every reachable node alive
    // across mutations of the original defs[] roots (e.g. while sat_sweep
    // is rebuilding defs[] in place).
    std::unordered_map<const AIG*, aig_node_ptr> raw_to_shared;

    // Post-order: children precede parents. Iteration order is fully
    // determined by the input defs[] order + child traversal order.
    std::vector<const AIG*> topo;

    // Every t_lit::var seen in topo.
    std::set<uint32_t> used_vars;

    // Per-node positive-value 64-bit signatures across R rounds.
    std::unordered_map<const AIG*, std::vector<uint64_t>> sigs;

    // Actual rounds used (>= sim_rounds; adaptive on large topos).
    uint32_t rounds = 0;

    // Collect post-order DFS topology starting from each non-null root in
    // `defs`. Populates raw_to_shared, topo, used_vars. Re-callable: state
    // accumulates rather than resetting, so a caller can stage multiple
    // root sets if needed.
    void collect_topology(const std::vector<aig_ptr>& defs);

    // Simulate every node in `topo`. Reads `used_vars` to allocate input
    // patterns; writes `sigs`; sets `rounds`. PRNG is seeded with a fixed
    // constant. Round 0 carries structured all-1 / one-hot patterns that
    // split near-constant / single-variable-sensitive nodes which pure
    // random sim would falsely cluster.
    void simulate();

    // Re-simulate using the same PRNG seed but more rounds. Useful when a
    // caller wants to grow the sim depth past sim_rounds without rebuilding
    // the topology. `rounds` is clamped to >= current value.
    void simulate_with_rounds(uint32_t R);
};

} // namespace ArjunNS
