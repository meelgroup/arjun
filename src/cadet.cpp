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

aig_ptr Cadet::build_input_minterm(const vector<bool>& vals,
                                   const vector<uint32_t>& sorted_inputs) {
    assert(vals.size() == sorted_inputs.size());
    // AND across all input vars: AIG(x_i) if vals[i], else ~AIG(x_i).
    aig_ptr acc = AIG::new_const(true);
    for (size_t i = 0; i < sorted_inputs.size(); i++) {
        aig_ptr lit = AIG::new_lit(sorted_inputs[i], /*neg=*/!vals[i]);
        acc = AIG::new_and(acc, lit);
    }
    return acc;
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

    // For each y in to_define, accumulate an OR of input-minterms where y
    // must be 1.
    std::map<uint32_t, aig_ptr> skolem_pos;
    for (uint32_t y : to_define) skolem_pos[y] = AIG::new_const(false);

    MetaSolver solver(SolverType::cadical);
    inject_cnf(solver);

    const uint64_t n_assignments = 1ull << n_in;
    vector<Lit> assumps;
    assumps.reserve(n_in);
    vector<bool> vals(n_in);
    uint64_t sat_calls = 0;
    uint64_t unsat_calls = 0;
    for (uint64_t mask = 0; mask < n_assignments; mask++) {
        assumps.clear();
        for (uint32_t i = 0; i < n_in; i++) {
            const bool v = (mask >> i) & 1ull;
            vals[i] = v;
            assumps.push_back(Lit(sorted_inputs[i], /*sign=*/!v));
        }
        const auto ret = solver.solve(&assumps);
        if (ret == CMSat::l_True) {
            sat_calls++;
            const auto& model = solver.get_model();
            // For each to_define y, if model[y] == True, add this input
            // minterm to skolem_pos[y].
            for (uint32_t y : to_define) {
                assert(y < model.size());
                if (model[y] == CMSat::l_True) {
                    aig_ptr minterm = build_input_minterm(vals, sorted_inputs);
                    skolem_pos[y] = AIG::new_or(skolem_pos[y], minterm);
                }
            }
        } else if (ret == CMSat::l_False) {
            // Input combination has no satisfying assignment — the values
            // of the to_define vars under this input are vacuously free.
            // Default each y to FALSE here (no minterm added).
            unsat_calls++;
        } else {
            cout << "ERROR: [cadet] SAT solver returned UNKNOWN during enumeration"
                 << endl;
            return false;
        }
    }

    // Commit into skol[].
    skol.assign(cnf.nVars(), nullptr);
    for (uint32_t v : input) {
        // For inputs, the "Skolem" is just the var itself; not stored back
        // into cnf.defs but used internally.
        skol[v] = AIG::new_lit(v, /*neg=*/false);
    }
    for (uint32_t v : backward_defined) {
        skol[v] = cnf.get_def(v);
    }
    for (uint32_t y : to_define) skol[y] = skolem_pos.at(y);

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase A done. SAT calls: " << sat_calls
             << " UNSAT: " << unsat_calls
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

    // ---- Phase A: small-input enumeration ----
    if (inputs_are_small()) {
        if (!synth_by_enumeration()) {
            cout << "ERROR: [cadet] Phase A failed; Phase B/C not yet implemented"
                 << endl;
            std::exit(EXIT_FAILURE);
        }
    } else {
        // TODO: Phase B/C — incremental determinization for large inputs.
        cout << "ERROR: [cadet] " << orig_sampl_cnf.size() << " orig sampling "
             << "vars exceed enumeration threshold " << kSmallInputThreshold
             << ". Phase B (unique-consequence propagation) and Phase C "
             << "(decisions + conflict analysis) are not yet implemented. "
             << "Use --cadet 0 (the default Manthan path) for this benchmark."
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
