/*
 Arjun — brute_force_synth.cpp

 Brute-force synthesis. See brute_force_synth.h.

 Copyright (c) 2026, Mate Soos. All rights reserved.
*/

#include "brute_force_synth.h"

#include "arjun.h"
#include "backward.h"
#include "constants.h"
#include "metasolver.h"
#include "time_mem.h"

#include <cryptominisat5/solvertypesmini.h>

#include <algorithm>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <unordered_map>
#include <vector>

using std::vector;
using std::setprecision;
using std::fixed;

using ArjunNS::AIG;
using ArjunNS::aig_ptr;
using ArjunNS::SimplifiedCNF;
using CMSat::Lit;

namespace ArjunInt {

BruteForceSynth::BruteForceSynth(const ArjunInt::Config& _conf,
                           const ArjunNS::Arjun::ManthanConf& _mconf,
                           ArjunNS::SimplifiedCNF&& _cnf)
    : conf(_conf), mconf(_mconf), cnf(std::move(_cnf))
{}

template<typename S>
void BruteForceSynth::inject_cnf(S& s) const {
    s.new_vars(cnf.nVars());
    for (const auto& c : cnf.get_clauses()) s.add_clause(c);
    for (const auto& c : cnf.get_red_clauses()) s.add_red_clause(c);
}

aig_ptr BruteForceSynth::build_decision_tree(const vector<bool>& table,
                                         const vector<uint32_t>& sorted_inputs) {
    // Bottom-up pair-merge; ITE folds constant subtrees.
    const uint32_t n = sorted_inputs.size();
    if (n == 0) {
        assert(table.size() == 1);
        return AIG::new_const(table[0]);
    }
    vector<aig_ptr> level;
    level.reserve(table.size());
    for (bool b : table) level.push_back(AIG::new_const(b));

    for (uint32_t lvl = 0; lvl < n; lvl++) {
        const uint32_t split_var = sorted_inputs[lvl];
        const CMSat::Lit branch_lit(split_var, /*sign=*/false);
        vector<aig_ptr> next;
        next.reserve(level.size() / 2);
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            next.push_back(AIG::new_ite(level[i + 1], level[i], branch_lit));
        }
        level = std::move(next);
    }
    assert(level.size() == 1);
    return level[0];
}

void BruteForceSynth::maybe_minimize_enum_set() {
    if (!mconf.brute_force_synth_minim) return;
    if (orig_sampl_cnf.empty()) return;
    if (orig_sampl_cnf.size() > mconf.brute_force_synth_minim_max) {
        verb_print(1, "[brute_force_synth] enum set " << orig_sampl_cnf.size()
            << " > minim cap " << mconf.brute_force_synth_minim_max << "; skipping minim");
        return;
    }

    const double t0 = cpuTime();
    const size_t before = orig_sampl_cnf.size();
    vector<uint32_t> candidate(orig_sampl_cnf.begin(), orig_sampl_cnf.end());

    Backward bw(conf);
    vector<uint32_t> minimized = bw.minimize_subset(cnf, candidate);

    orig_sampl_cnf.clear();
    orig_sampl_cnf.insert(minimized.begin(), minimized.end());

    verb_print(1, "[brute_force_synth] minim shrank enum set: " << before
        << " -> " << orig_sampl_cnf.size()
        << " (2^N rows: " << (1ull << before) << " -> "
        << (1ull << orig_sampl_cnf.size()) << "). T: "
        << fixed << setprecision(2) << (cpuTime() - t0));
}

void BruteForceSynth::synth_complete_with_models() {
    assert(orig_sampl_cnf.size() <= mconf.brute_force_synth_threshold);

    vector<uint32_t> undet(to_define.begin(), to_define.end());
    if (undet.empty()) return;

    verb_print(1, "[brute_force_synth] SAT-model completion on " << undet.size()
        << " undet vars over " << orig_sampl_cnf.size() << " orig sampling vars");
    const double t0 = cpuTime();

    MetaSolver sat(SolverType::cadical);
    inject_cnf(sat);

    vector<uint32_t> sorted_inputs(orig_sampl_cnf.begin(), orig_sampl_cnf.end());
    std::sort(sorted_inputs.begin(), sorted_inputs.end());
    const uint32_t n_in = sorted_inputs.size();
    const uint64_t n_assign = 1ull << n_in;

    // UNSAT-input rows stay false (vacuously free; AIG simplifier folds).
    std::unordered_map<uint32_t, vector<bool>> tables;
    tables.reserve(undet.size());
    for (uint32_t y : undet) tables[y].assign(n_assign, false);

    vector<Lit> forbid;
    forbid.reserve(n_in);
    uint64_t covered_count = 0;
    while (true) {
        const auto ret = sat.solve();
        if (ret == CMSat::l_False) break;
        release_assert(ret == CMSat::l_True &&
                       "brute_force_synth: SAT solver returned UNDEF on a "
                       "supposedly-finite enumeration");
        const auto& model = sat.get_model();
        uint64_t mask = 0;
        forbid.clear();
        for (uint32_t i = 0; i < n_in; i++) {
            const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
            if (mv) mask |= (1ull << i);
            forbid.emplace_back(sorted_inputs[i], mv);
        }
        if (mask < n_assign) {
            covered_count++;
            for (uint32_t y : undet) {
                tables[y][mask] = (model[y] == CMSat::l_True);
            }
        }
        sat.add_clause(forbid);
    }

    skol.assign(cnf.nVars(), nullptr);
    for (uint32_t y : undet) {
        skol[y] = build_decision_tree(tables.at(y), sorted_inputs);
    }

    verb_print(1, "[brute_force_synth] done. covered " << covered_count
        << "/" << n_assign << " consistent input patterns. T: "
        << fixed << setprecision(2) << (cpuTime() - t0));
}

void BruteForceSynth::commit_definitions() {
    vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    for (uint32_t y : to_define) {
        release_assert(skol[y] != nullptr &&
                       "brute_force_synth must produce a Skolem for every to_define var");
        aigs[y] = skol[y];
    }
    cnf.map_aigs_to_orig(aigs, cnf.nVars());
    cnf.simplify_aigs(conf.verb);
}

SimplifiedCNF BruteForceSynth::do_synth() {
    const double my_time = cpuTime();
    verb_print(1, "[brute_force_synth] starting; nVars=" << cnf.nVars()
        << " clauses=" << cnf.get_clauses().size());

    cnf.get_var_types(conf.verb, "start do_synth").unpack_to(
        input, to_define, backward_defined);

    // VarTypes.input lumps extend-defined vars in; we enumerate over the
    // narrower orig sampling set only.
    orig_sampl_cnf.clear();
    const auto& o2n = cnf.get_orig_to_new_var();
    for (uint32_t v : cnf.get_orig_sampl_vars()) {
        auto it = o2n.find(v);
        if (it == o2n.end()) continue;
        orig_sampl_cnf.insert(it->second.var());
    }

    if (to_define.empty()) {
        verb_print(1, "[brute_force_synth] nothing to define — returning unchanged CNF");
        return std::move(cnf);
    }

    verb_print(1, "[brute_force_synth] partition: |orig_sampl|=" << orig_sampl_cnf.size()
        << " |input|=" << input.size()
        << " |to_define|=" << to_define.size()
        << " |backward_defined|=" << backward_defined.size());

    maybe_minimize_enum_set();

    // Decline (don't abort) above the threshold: caller falls back to Manthan.
    if (orig_sampl_cnf.size() > mconf.brute_force_synth_threshold) {
        verb_print(1, "[brute_force_synth] enum set " << orig_sampl_cnf.size()
            << " > threshold " << mconf.brute_force_synth_threshold
            << "; declining — Manthan will synthesize");
        return std::move(cnf);
    }

    synth_complete_with_models();
    commit_definitions();

    verb_print(1, "[brute_force_synth] done — all " << to_define.size()
        << " to_define vars committed. T: "
        << fixed << setprecision(2) << (cpuTime() - my_time));
    return std::move(cnf);
}

} // namespace ArjunInt
