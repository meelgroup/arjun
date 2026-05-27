/*
 Arjun — cadet.cpp

 Phase-E-only synthesis: enumerate consistent X assignments via a
 forbid-clause SAT loop, tabulate every undet y per model, then build a
 Shannon tree per y over the sorted orig sampling vars. Always finishes
 alone (no Manthan fallback) when |orig_sampl_cnf| is within the gate.

 Copyright (c) 2026, Mate Soos. All rights reserved.
*/

#include "cadet.h"

#include "arjun.h"
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

using std::cout;
using std::endl;
using std::vector;
using std::setprecision;
using std::fixed;

using ArjunNS::AIG;
using ArjunNS::aig_ptr;
using ArjunNS::SimplifiedCNF;
using CMSat::Lit;

namespace ArjunInt {

Cadet::Cadet(const ArjunInt::Config& _conf,
             const ArjunNS::Arjun::ManthanConf& _mconf,
             ArjunNS::SimplifiedCNF&& _cnf)
    : conf(_conf), mconf(_mconf), cnf(std::move(_cnf))
{}

template<typename S>
void Cadet::inject_cnf(S& s) const {
    s.new_vars(cnf.nVars());
    for (const auto& c : cnf.get_clauses()) s.add_clause(c);
    for (const auto& c : cnf.get_red_clauses()) s.add_red_clause(c);
}

aig_ptr Cadet::build_shannon_tree(const vector<bool>& table,
                                  const vector<uint32_t>& sorted_inputs) {
    // Bottom-up pair-merge: level[i] = ITE(sorted_inputs[L],
    //   high=prev[2i+1], low=prev[2i]). ITE folds constant subtrees.
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

void Cadet::synth_complete_with_models() {
    // 2^|orig_sampl_cnf| tables; guard or we OOM. No fallback exists.
    release_assert(orig_sampl_cnf.size() <= mconf.cadet_phase_e_threshold &&
                   "cadet Phase E: |orig_sampl_cnf| > cadet_phase_e_threshold "
                   "(would OOM on the 2^N truth tables); raise --cadetphaseeth "
                   "if you understand the memory cost, or don't use --cadet");

    vector<uint32_t> undet(to_define.begin(), to_define.end());
    if (undet.empty()) return;

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase E — SAT-model completion on "
             << undet.size() << " undet vars over "
             << orig_sampl_cnf.size() << " orig sampling vars" << endl;
    }
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
                       "cadet Phase E: SAT solver returned UNDEF on a "
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
        skol[y] = build_shannon_tree(tables.at(y), sorted_inputs);
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase E done. covered " << covered_count
             << "/" << n_assign << " consistent input patterns. T: "
             << fixed << setprecision(2) << (cpuTime() - t0) << endl;
    }
}

void Cadet::commit_definitions() {
    vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    for (uint32_t y : to_define) {
        release_assert(skol[y] != nullptr &&
                       "cadet must produce a Skolem for every to_define var");
        aigs[y] = skol[y];
    }
    cnf.map_aigs_to_orig(aigs, cnf.nVars());
    cnf.simplify_aigs(conf.verb);
}

SimplifiedCNF Cadet::do_cadet() {
    const double my_time = cpuTime();
    if (conf.verb >= 1) {
        cout << "c o [cadet] starting; nVars=" << cnf.nVars()
             << " clauses=" << cnf.get_clauses().size() << endl;
    }

    cnf.get_var_types(conf.verb, "start do_cadet").unpack_to(
        input, to_define, backward_defined);

    // VarTypes.input lumps extend-defined vars in; orig_sampl_cnf is
    // the narrower set we actually enumerate over.
    orig_sampl_cnf.clear();
    const auto& o2n = cnf.get_orig_to_new_var();
    for (uint32_t v : cnf.get_orig_sampl_vars()) {
        auto it = o2n.find(v);
        if (it == o2n.end()) continue;
        orig_sampl_cnf.insert(it->second.var());
    }

    if (to_define.empty()) {
        if (conf.verb >= 1) {
            cout << "c o [cadet] nothing to define — returning unchanged CNF" << endl;
        }
        return std::move(cnf);
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] partition: |orig_sampl|=" << orig_sampl_cnf.size()
             << " |input|=" << input.size()
             << " |to_define|=" << to_define.size()
             << " |backward_defined|=" << backward_defined.size() << endl;
    }

    synth_complete_with_models();
    commit_definitions();

    if (conf.verb >= 1) {
        cout << "c o [cadet] done — all " << to_define.size()
             << " to_define vars committed. T: "
             << fixed << setprecision(2) << (cpuTime() - my_time) << endl;
    }
    return std::move(cnf);
}

} // namespace ArjunInt
