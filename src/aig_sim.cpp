/*
 Arjun - AIG simulation helper (factored from aig_rewrite.cpp)

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#include "aig_sim.h"
#include <functional>
#include <random>

using namespace ArjunNS;
using std::vector;

void SimState::collect_topology(const vector<aig_ptr>& defs) {
    // Post-order DFS, keeping owning shared_ptrs so callers can mutate the
    // root vector without freeing nodes still in topo[].
    std::function<void(const aig_ptr&)> dfs = [&](const aig_ptr& e) {
        if (!e) return;
        if (raw_to_shared.count(e.get())) return;
        raw_to_shared[e.get()] = e.node;
        if (e->type == AIGT::t_and) {
            dfs(e->l);
            if (e->r.get() != e->l.get()) dfs(e->r);
        }
        topo.push_back(e.get());
    };
    for (const auto& r : defs) dfs(r);
    for (const auto* n : topo) {
        if (n->type == AIGT::t_lit) used_vars.insert(n->var);
    }
}

void SimState::simulate() {
    // Adaptive depth: +4 rounds per 4× past 256 nodes, capped at 48. More
    // rounds = fewer bogus candidate classes at linear sim cost.
    uint32_t R = sim_rounds;
    for (size_t t = topo.size(); t > 256 && R < 48; t >>= 2) R += 4;
    simulate_with_rounds(R);
}

void SimState::simulate_with_rounds(uint32_t R) {
    if (R < rounds) R = rounds;
    rounds = R;

    std::mt19937_64 rng(0xA11CEULL);
    std::unordered_map<uint32_t, vector<uint64_t>> var_pats;
    // Round 0 = all-zero / all-one / one-hot rows; splits near-constant and
    // single-variable-sensitive nodes that pure-random sim lumps together.
    uint32_t var_idx = 0;
    for (uint32_t v : used_vars) {
        var_pats[v].resize(R);
        for (uint32_t i = 0; i < R; i++) var_pats[v][i] = rng();
        uint64_t structured = 2ULL;  // bit 1 ⇒ "all variables = 1" row
        if (var_idx < 62) structured |= (1ULL << (var_idx + 2));
        var_pats[v][0] = structured;
        var_idx++;
    }

    // Simulate POSITIVE value of each node; fanin sign flips on the way in.
    sigs.clear();
    sigs.reserve(topo.size());
    for (const auto* n : topo) {
        vector<uint64_t> s(R);
        if (n->type == AIGT::t_const) {
            for (uint32_t i = 0; i < R; i++) s[i] = ~0ULL;
        } else if (n->type == AIGT::t_lit) {
            const auto& p = var_pats[n->var];
            for (uint32_t i = 0; i < R; i++) s[i] = p[i];
        } else {
            const auto& ls = sigs.at(n->l.get());
            const auto& rs = sigs.at(n->r.get());
            for (uint32_t i = 0; i < R; i++) {
                uint64_t lv = ls[i]; if (n->l.neg) lv = ~lv;
                uint64_t rv = rs[i]; if (n->r.neg) rv = ~rv;
                s[i] = lv & rv;
            }
        }
        sigs.emplace(n, std::move(s));
    }
}
