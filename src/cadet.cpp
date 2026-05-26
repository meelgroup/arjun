/*
 Arjun

 cadet.cpp — In-tree port of CADET's incremental-determinization core
 (Markus N. Rabe, SAT 2016). Used in place of Manthan when --cadet 1 is set.

 Algorithm overview
 ==================
 CADET solves 2QBF formulas ∀X. ∃Y. φ(X, Y) by constructing a Skolem
 function for every existential variable in Y. The Skolem function for
 y ∈ Y is a Boolean function f_y(X) such that ∀X. φ(X, f_y(X), …) holds
 — i.e. plugging the Skolem functions into φ yields a tautology over X.

 CADET builds the Skolem functions incrementally rather than guessing
 them up-front (as Manthan does). It uses a SAT solver to detect when an
 existential variable's value is *forced* by the formula given the
 partial Skolem functions built so far ("unique consequence" / pure-
 literal propagation), and falls back to decisions + conflict analysis
 when no propagation is possible.

 Phasing
 =======
 This file implements the algorithm in phases, gated on input size and
 partition structure:

   Phase A — exhaustive enumeration. When |inputs| is small, build the
   Skolem function for every y by enumerating every input assignment,
   calling SAT under the assumption, and constructing a multi-input
   table (DNF-of-minterms) AIG. Slow but correct, and sufficient for
   the small fuzzer CNFs where every other phase might miss corner
   cases. This is the v1.

   Phase B (TODO) — per-clause unique-consequence propagation. For each
   clause C ∋ y where every other literal is already a function of
   inputs, the disjunction-of-negated-other-literals is a sub-region
   where y must hold; OR these into the running Skolem.

   Phase C (TODO) — decisions + conflict analysis. When propagation
   stops, pick an undetermined y, set f_y = false (or true), use the
   SAT solver to detect conflicts, learn clauses, and backtrack.

 Copyright (c) 2026, Mate Soos. All rights reserved.
*/

#include "cadet.h"

#include "arjun.h"
#include "constants.h"
#include "metasolver.h"
#include "time_mem.h"

#include <cryptominisat5/solvertypesmini.h>

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <set>
#include <vector>

using std::cout;
using std::endl;
using std::set;
using std::vector;
using std::setprecision;
using std::fixed;

using ArjunNS::AIG;
using ArjunNS::aig_ptr;
using ArjunNS::aig_lit;
using ArjunNS::SimplifiedCNF;
using ArjunNS::VarTypes;
using CMSat::Lit;
using CMSat::lbool;

namespace ArjunInt {

// Threshold for Phase A's exhaustive enumeration. 2^16 = 65536 SAT calls
// is the upper bound we're willing to spend per benchmark in v1. Anything
// larger needs Phase B/C, which are not implemented yet.
static constexpr uint32_t kSmallInputThreshold = 16;

Cadet::Cadet(const ArjunInt::Config& _conf,
             const ArjunNS::Arjun::ManthanConf& _mconf,
             ArjunNS::SimplifiedCNF&& _cnf)
    : conf(_conf), mconf(_mconf), cnf(std::move(_cnf))
{
    (void)mconf; // currently unused; will be once we implement Phase B/C
}

template<typename S>
void Cadet::inject_cnf(S& s) const {
    s.new_vars(cnf.nVars());
    for (const auto& c : cnf.get_clauses()) s.add_clause(c);
    for (const auto& c : cnf.get_red_clauses()) s.add_red_clause(c);
}

bool Cadet::inputs_are_small() const {
    // Enumeration size is 2^|orig_sampl_cnf|, NOT 2^|input|. The latter
    // counts extend-defined vars too, which are not free (they have AIG
    // defs over the orig sampling vars), so enumerating them would
    // generate lots of inconsistent assumption sets the SAT solver
    // immediately reject.
    return orig_sampl_cnf.size() <= kSmallInputThreshold;
}

aig_ptr Cadet::build_shannon_tree(const vector<bool>& table,
                                  const vector<uint32_t>& sorted_inputs) {
    // table is indexed by integer mask of length sorted_inputs.size().
    // Bit i of the mask corresponds to sorted_inputs[i]. We Shannon-
    // decompose bottom-up, level by level: at level L the surviving
    // nodes cover 2^L leaves, addressed by the high (n-L) bits of the
    // original mask. Pair-merge: level[i] = ITE(sorted_inputs[L],
    //                                          high=level_prev[2i+1],
    //                                          low=level_prev[2i]).
    // ITE collapses to the common subtree when both children match, so
    // constant regions vanish naturally.
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
            // level[i]   has bit `lvl` = 0  → low branch
            // level[i+1] has bit `lvl` = 1  → high branch
            // ITE(b, l, r) returns l when b is true.
            next.push_back(AIG::new_ite(level[i + 1], level[i], branch_lit));
        }
        level = std::move(next);
    }
    assert(level.size() == 1);
    return level[0];
}

bool Cadet::synth_by_enumeration() {
    // Enumerate only over the *orig* sampling vars (in CNF numbering).
    // The wider `input` set returned by get_var_types also lumps in
    // extend-defined vars (vars whose AIG def depends only on orig
    // sampling vars). Those are not free — the CNF constrains them — so
    // enumerating them is wasteful and would mostly produce inconsistent
    // assumption sets.
    //
    // Order deterministically by var id so the AIG construction order
    // matches across runs (CLAUDE.md determinism rule — never order on
    // pointer addresses).
    vector<uint32_t> sorted_inputs(orig_sampl_cnf.begin(), orig_sampl_cnf.end());
    std::sort(sorted_inputs.begin(), sorted_inputs.end());
    const uint32_t n_in = sorted_inputs.size();

    if (n_in > kSmallInputThreshold) {
        if (conf.verb >= 1) {
            cout << "c o [cadet] enumeration aborts: " << n_in
                 << " inputs exceeds threshold " << kSmallInputThreshold << endl;
        }
        return false;
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase A — exhaustive enumeration over "
             << n_in << " inputs (2^" << n_in << " = " << (1ull << n_in)
             << " SAT calls)" << endl;
    }
    const double t0 = cpuTime();

    // Collect a per-y value table over all 2^n_in input assignments. We
    // build the AIG only AFTER the table is filled, via Shannon
    // decomposition — much smaller than a flat OR-of-minterms.
    const uint64_t n_assignments = 1ull << n_in;
    std::map<uint32_t, vector<bool>> table;
    for (uint32_t y : to_define) table[y].assign(n_assignments, false);

    MetaSolver solver(SolverType::cadical);
    inject_cnf(solver);

    vector<Lit> assumps;
    assumps.reserve(n_in);
    uint64_t sat_calls = 0;
    uint64_t unsat_calls = 0;
    for (uint64_t mask = 0; mask < n_assignments; mask++) {
        assumps.clear();
        for (uint32_t i = 0; i < n_in; i++) {
            const bool v = (mask >> i) & 1ull;
            assumps.push_back(Lit(sorted_inputs[i], /*sign=*/!v));
        }
        const auto ret = solver.solve(&assumps);
        if (ret == CMSat::l_True) {
            sat_calls++;
            const auto& model = solver.get_model();
            for (uint32_t y : to_define) {
                assert(y < model.size());
                if (model[y] == CMSat::l_True) table[y][mask] = true;
            }
        } else if (ret == CMSat::l_False) {
            // Input combination has no satisfying assignment — y can be
            // anything here. Leaving the table entry as `false` (default)
            // is fine: Shannon decomposition will pull constant regions
            // together, and "false" merges naturally with neighbours.
            unsat_calls++;
        } else {
            cout << "ERROR: [cadet] SAT solver returned UNKNOWN during enumeration"
                 << endl;
            return false;
        }
    }

    skol.assign(cnf.nVars(), nullptr);
    for (uint32_t v : input) skol[v] = AIG::new_lit(v, /*neg=*/false);
    for (uint32_t v : backward_defined) skol[v] = cnf.get_def(v);
    for (uint32_t y : to_define) {
        skol[y] = build_shannon_tree(table.at(y), sorted_inputs);
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase A done. SAT calls: " << sat_calls
             << " UNSAT: " << unsat_calls
             << " T: " << fixed << setprecision(2) << (cpuTime() - t0) << endl;
    }
    return true;
}

void Cadet::collect_component(uint32_t seed_var,
                              const set<uint32_t>& stop_set,
                              const vector<vector<uint32_t>>& var_to_clauses,
                              vector<uint32_t>& support_out,
                              vector<uint32_t>& to_def_out,
                              vector<uint32_t>& clauses_out) const {
    // BFS over the clause graph: a clause is "expanded" (its other vars
    // pushed onto the frontier) the first time we reach it. stop_set
    // vars terminate expansion — we record them as boundary but don't
    // continue through their clauses.
    const uint32_t n_vars = cnf.nVars();
    vector<char> visited_var(n_vars, 0);
    vector<char> visited_clause(cnf.get_clauses().size(), 0);
    vector<uint32_t> frontier;
    frontier.push_back(seed_var);
    visited_var[seed_var] = 1;

    set<uint32_t> support, to_def;
    set<uint32_t> clauses_set;
    while (!frontier.empty()) {
        uint32_t v = frontier.back();
        frontier.pop_back();
        if (stop_set.count(v)) {
            // Sink — orig sampling var. Record as a boundary input and
            // do NOT expand its clauses (those clauses are owned by
            // some "other" component that the input separates).
            support.insert(v);
            continue;
        }
        // Otherwise v is one of: to_define, extend-defined, or
        // backward-defined. All three: we expand their clauses. Only
        // to_define vars get recorded for Skolem-building.
        if (to_define.count(v)) to_def.insert(v);
        for (uint32_t cls_idx : var_to_clauses[v]) {
            if (visited_clause[cls_idx]) continue;
            visited_clause[cls_idx] = 1;
            clauses_set.insert(cls_idx);
            for (const auto& l : cnf.get_clauses()[cls_idx]) {
                if (!visited_var[l.var()]) {
                    visited_var[l.var()] = 1;
                    frontier.push_back(l.var());
                }
            }
        }
    }
    support_out.assign(support.begin(), support.end());
    std::sort(support_out.begin(), support_out.end());
    to_def_out.assign(to_def.begin(), to_def.end());
    std::sort(to_def_out.begin(), to_def_out.end());
    clauses_out.assign(clauses_set.begin(), clauses_set.end());
    std::sort(clauses_out.begin(), clauses_out.end());
}

bool Cadet::synth_by_components() {
    // Build var → clause-index map once.
    const auto& clauses = cnf.get_clauses();
    vector<vector<uint32_t>> var_to_clauses(cnf.nVars());
    for (uint32_t ci = 0; ci < clauses.size(); ci++) {
        for (const auto& l : clauses[ci]) var_to_clauses[l.var()].push_back(ci);
    }

    // Sinks for BFS: ONLY the orig sampling vars. We deliberately do
    // NOT stop at extend-defined or backward-defined vars: those have
    // AIG defs that ultimately bottom out at orig sampling vars, and
    // F's clauses constraining them connect them to the same orig
    // sampling vars that other components might also touch. If we
    // stopped at them, two "components" could implicitly share the
    // same orig sampling var via defined-intermediate boundary nodes;
    // their independently-built Skolems would then disagree on that
    // shared input, producing wrong AIGs (verified via test-synth on
    // the fuzzer seed 9340754230162260130).
    //
    // Trade-off: this makes components larger (they grow through every
    // defined intermediate var), so Phase B helps less on CNFs where
    // backward/extend has already linked everything. Phase C will be
    // the answer for those cases.
    set<uint32_t> stop_set = orig_sampl_cnf;

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase B — clause-graph component enumeration"
             << endl;
    }
    const double t0 = cpuTime();

    // Pre-load a single SAT solver with the full CNF. We'll reuse it
    // across all components, calling it under different assumption sets.
    // (The full CNF on the solver is fine: extra constraints outside
    // the current component can only be more restrictive, never less,
    // and within a component the answer is the same as if we'd loaded
    // only the component's clauses.)
    MetaSolver solver(SolverType::cadical);
    inject_cnf(solver);

    skol.assign(cnf.nVars(), nullptr);
    for (uint32_t v : input) skol[v] = AIG::new_lit(v, /*neg=*/false);
    for (uint32_t v : backward_defined) skol[v] = cnf.get_def(v);

    set<uint32_t> not_yet_done(to_define.begin(), to_define.end());
    uint64_t total_sat = 0, total_unsat = 0;
    uint64_t max_comp_inputs = 0, max_comp_to_def = 0;
    uint32_t n_components = 0;

    while (!not_yet_done.empty()) {
        const uint32_t seed = *not_yet_done.begin();
        vector<uint32_t> comp_inputs, comp_to_def, comp_cls;
        collect_component(seed, stop_set, var_to_clauses,
                          comp_inputs, comp_to_def, comp_cls);
        n_components++;
        max_comp_inputs = std::max<uint64_t>(max_comp_inputs, comp_inputs.size());
        max_comp_to_def = std::max<uint64_t>(max_comp_to_def, comp_to_def.size());

        if (comp_inputs.size() > kSmallInputThreshold) {
            if (conf.verb >= 1) {
                cout << "c o [cadet] Phase B aborts: component seeded at y="
                     << (seed + 1) << " has " << comp_inputs.size()
                     << " inputs > threshold " << kSmallInputThreshold << endl;
            }
            return false;
        }
        if (conf.verb >= 2) {
            cout << "c o [cadet]   component #" << n_components
                 << ": " << comp_inputs.size() << " inputs, "
                 << comp_to_def.size() << " to_define, "
                 << comp_cls.size() << " clauses" << endl;
        }

        // Enumerate over THIS component's inputs only. All to_define
        // vars in the component get their value from the same SAT call,
        // so their Skolems are mutually consistent. Inputs outside the
        // component are propagated freely by the SAT solver; their
        // choice doesn't affect this component because F decomposes
        // along the boundary.
        const uint64_t n_assign = 1ull << comp_inputs.size();
        std::map<uint32_t, vector<bool>> tables;
        for (uint32_t y : comp_to_def) tables[y].assign(n_assign, false);

        vector<Lit> assumps;
        assumps.reserve(comp_inputs.size());
        for (uint64_t mask = 0; mask < n_assign; mask++) {
            assumps.clear();
            for (size_t i = 0; i < comp_inputs.size(); i++) {
                const bool v = (mask >> i) & 1ull;
                assumps.push_back(Lit(comp_inputs[i], /*sign=*/!v));
            }
            const auto ret = solver.solve(&assumps);
            if (ret == CMSat::l_True) {
                total_sat++;
                const auto& model = solver.get_model();
                for (uint32_t y : comp_to_def) {
                    if (model[y] == CMSat::l_True) tables[y][mask] = true;
                }
            } else if (ret == CMSat::l_False) {
                total_unsat++; // don't-care for this input
            } else {
                cout << "ERROR: [cadet] SAT solver returned UNKNOWN in Phase B"
                     << endl;
                return false;
            }
        }

        for (uint32_t y : comp_to_def) {
            skol[y] = build_shannon_tree(tables.at(y), comp_inputs);
            not_yet_done.erase(y);
        }
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase B done. components: " << n_components
             << " max inputs/comp: " << max_comp_inputs
             << " max to_def/comp: " << max_comp_to_def
             << " SAT/UNSAT: " << total_sat << "/" << total_unsat
             << " T: " << fixed << setprecision(2) << (cpuTime() - t0) << endl;
    }
    return true;
}

void Cadet::commit_definitions() {
    // Build a vector indexed by var, holding the Skolem AIG for each
    // to_define var (and nullptr elsewhere) — exactly the form
    // map_aigs_to_orig expects from Manthan.
    vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    for (uint32_t y : to_define) {
        assert(skol[y] != nullptr);
        aigs[y] = skol[y];
    }
    const uint32_t cnf_nvars = cnf.nVars();
    cnf.map_aigs_to_orig(aigs, cnf_nvars);
}

SimplifiedCNF Cadet::do_cadet() {
    const double my_time = cpuTime();
    if (conf.verb >= 1) {
        cout << "c o [cadet] starting; nVars=" << cnf.nVars()
             << " clauses=" << cnf.get_clauses().size() << endl;
    }

    // Partition vars into input/to_define/backward_defined, the same split
    // Manthan uses.
    cnf.get_var_types(conf.verb, "start do_cadet").unpack_to(
        input, to_define, backward_defined);

    // Independently compute the orig sampling vars in CNF numbering.
    // VarTypes.input would include extend-defined vars (vars defined by an
    // AIG over orig sampling vars), which are not actually free in F;
    // enumerating over them in Phase A would generate inconsistent
    // assumption sets. We only enumerate over the orig sampling vars.
    orig_sampl_cnf.clear();
    const auto& o2n = cnf.get_orig_to_new_var();
    for (uint32_t v : cnf.get_orig_sampl_vars()) {
        auto it = o2n.find(v);
        if (it == o2n.end()) continue; // eliminated from CNF
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

    // ---- Phase B: connected-component enumeration. Decompose the
    // clause graph (treating inputs and backward_defined as sinks) into
    // components; each component carries its own bounded input set and
    // its to_define vars are jointly enumerated. Scales past Phase A's
    // global-threshold gate when F decomposes naturally.
    bool done = synth_by_components();

    // ---- Phase A fallback: global enumeration. Only viable for
    // pathologically small problems where every y touches every input.
    // For now we only try this when |orig_sampl_cnf| is itself small;
    // larger problems fall through to Phase C (not yet implemented).
    if (!done && inputs_are_small()) {
        done = synth_by_enumeration();
    }

    if (!done) {
        // TODO: Phase C — decisions + conflict analysis for the hard cases.
        cout << "ERROR: [cadet] Phase B and Phase A both failed. " << endl
             << "       |orig_sampl| = " << orig_sampl_cnf.size()
             << " is too large for Phase A's global enumeration, and at "
             << "least one to_define var has a local support that's also "
             << "too large for Phase B. Phase C (decisions + conflict "
             << "analysis) — the proper incremental-determinization loop "
             << "— is not yet implemented. Use --cadet 0 for now."
             << endl;
        std::exit(EXIT_FAILURE);
    }

    commit_definitions();

    if (conf.verb >= 1) {
        cout << "c o [cadet] done. T: " << fixed << setprecision(2)
             << (cpuTime() - my_time) << endl;
    }
    return std::move(cnf);
}

} // namespace ArjunInt
