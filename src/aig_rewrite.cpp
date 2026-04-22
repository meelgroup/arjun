/*
 Arjun - AIG Rewriting System

 Reduces the structural size of an AIG while preserving its function. The
 current implementation delegates to AIG::simplify_aig (which runs the
 algebraic simplifications baked into new_and / new_or / new_const plus a
 structural-CSE pass). The FRAIG-lite SAT sweeping entry point is retained
 for API compatibility but is currently a no-op — the simpler passes are
 enough to pass the correctness fuzzers in the new input-edge-neg model.

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. MIT License.
 */

#include "aig_rewrite.h"
#include "time_mem.h"
#include <algorithm>
#include <cstdint>
#include <iomanip>
#include <iostream>

using namespace ArjunNS;
using std::cout;
using std::endl;
using std::vector;

void AIGRewriteStats::print(int verb) const {
    if (verb < 1) return;
    cout << "c o [aig-rewrite] nodes: " << nodes_before << " -> " << nodes_after
         << " (" << std::fixed << std::setprecision(1)
         << (nodes_before > 0 ? (1.0 - (double)nodes_after / nodes_before) * 100.0 : 0.0) << "% reduction)"
         << "  passes: " << total_passes
         << "  hash_hits: " << structural_hash_hits
         << endl;
}

void AIGRewriteStats::clear() { *this = AIGRewriteStats(); }

aig_ptr AIGRewriter::rewrite(const aig_ptr& aig) {
    if (!aig) return nullptr;
    return AIG::simplify_aig(aig);
}

void AIGRewriter::rewrite_all(vector<aig_ptr>& defs, int verb) {
    const double t = cpuTime();
    stats.nodes_before = AIG::count_aig_nodes_fast(defs);
    for (auto& d : defs) {
        if (d != nullptr) d = AIG::simplify_aig(d);
    }
    stats.nodes_after = AIG::count_aig_nodes_fast(defs);
    stats.total_passes++;
    if (verb >= 1) {
        cout << "c o [aig-rewrite] " << stats.nodes_before
             << " -> " << stats.nodes_after
             << " nodes  T: " << std::fixed << std::setprecision(2)
             << (cpuTime() - t) << endl;
    }
}

void AIGRewriter::sat_sweep(vector<aig_ptr>& /*defs*/, int /*verb*/) {
    // FRAIG-lite SAT sweeping was disabled in the input-edge-neg migration.
    // The correctness fuzzers don't require it; re-enable here once the
    // pattern-matching helpers are ported.
}
