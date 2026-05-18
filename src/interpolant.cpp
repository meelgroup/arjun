/*
 Arjun

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in
 all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 THE SOFTWARE.
 */

#include "interpolant.h"
#include "interp_repair.h"
#include "constants.h"

#include <cadical.hpp>
#include <fstream>
#include <memory>
#include <sstream>

using namespace CMSat;
using namespace CaDiCaL;
using namespace ArjunInt;
using namespace ArjunNS;
using std::vector;
using std::set;
using std::endl;

// Selector variable for clause i of all_cls / indicator unit k. They sit
// above the doubled-CNF variables, so they never collide with real lits.
static inline int sel_lit(uint32_t sel_var) { return (int)sel_var + 1; }

void Interpolant::fill_from_solver(SATSolver* solver, uint32_t _orig_num_vars,
        const AIGManager& _aig_mng) {
    orig_num_vars = _orig_num_vars;
    tot_num_vars = solver->nVars();
    aig_mng = &_aig_mng;

    // Extract the (already CMS-simplified) doubled CNF once. This mirrors
    // what fill_picolsat used to feed into PicoSAT; the indicator units
    // permanently added to the solver later are tracked via add_unit_cl.
    all_cls.clear();
    solver->start_getting_constraints(false);
    vector<Lit> cl;
    bool is_xor, rhs;
    while (solver->get_next_constraint(cl, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        all_cls.push_back(cl);
    }
    solver->end_getting_constraints();

    // Build the persistent core-extraction solver. Each clause c_i is
    // stored as (c_i ∨ ¬s_i) with a fresh selector s_i = tot_num_vars+i.
    // Inprocessing/preprocessing are disabled so the single-occurrence
    // selector variables are never eliminated between incremental solves.
    core_solver = std::make_unique<Solver>();
    core_solver->set("inprocessing", 0);
    core_solver->set("preprocessing", 0);
    for (uint32_t i = 0; i < all_cls.size(); i++) {
        for (const auto& l : all_cls[i]) core_solver->add(lit_to_pl(l));
        core_solver->add(-sel_lit(tot_num_vars + i));   // ¬s_i
        core_solver->add(0);
    }
    verb_print(2, "[interp] doubled CNF extracted: " << all_cls.size()
            << " clauses, " << tot_num_vars << " vars");
}

void Interpolant::add_unit_cl(const vector<Lit>& cl) {
    assert(cl.size() == 1);
    // Selectored just like the doubled-CNF clauses, so failed() can tell
    // whether this indicator unit is part of a given conflict's core.
    const uint32_t sel = tot_num_vars + all_cls.size() + indicator_units.size();
    core_solver->add(lit_to_pl(cl[0]));
    core_solver->add(-sel_lit(sel));
    core_solver->add(0);
    indicator_units.push_back(cl[0]);
}

void Interpolant::generate_interpolant(const vector<Lit>& assumptions,
        uint32_t test_var, const set<uint32_t>& input_vars) {
    verb_print(2, "[interp] generating interpolant for var: " << test_var+1);
    verb_print(3, "[interp] assumptions: " << assumptions);

    const uint32_t n_cls = all_cls.size();
    const uint32_t n_ind = indicator_units.size();

    // --- 1. Extract a clause-level UNSAT core. Assume every clause /
    // indicator-unit selector (activating the whole doubled CNF) plus
    // this test_var's assumptions, solve, then read the core via failed().
    for (uint32_t i = 0; i < n_cls + n_ind; i++)
        core_solver->assume(sel_lit(tot_num_vars + i));
    for (const auto& l : assumptions) core_solver->assume(lit_to_pl(l));

    const int cret = core_solver->solve();
    // CMS already proved this UNSAT under the same assumptions.
    release_assert(cret == 20 && "interpolant core solve must be UNSAT");

    // The mini-CNF: only the clauses / units / assumptions cadical's
    // refutation actually used. Its (A,B) partition gives an interpolant
    // valid for the full doubled problem (a subset that stays UNSAT and
    // keeps the same partition yields the same kind of interpolant).
    vector<vector<Lit>> mini_cls;
    vector<char> mini_is_b;
    auto take = [&](const vector<Lit>& cl, bool is_b) {
        mini_cls.push_back(cl);
        mini_is_b.push_back(is_b ? 1 : 0);
    };
    for (uint32_t i = 0; i < n_cls; i++)
        if (core_solver->failed(sel_lit(tot_num_vars + i)))
            take(all_cls[i], is_b_clause(all_cls[i]));
    const uint32_t core_cls = mini_cls.size();
    for (uint32_t k = 0; k < n_ind; k++)
        if (core_solver->failed(sel_lit(tot_num_vars + n_cls + k)))
            take({indicator_units[k]}, true);   // indicator units are B-side
    for (const auto& l : assumptions)
        if (core_solver->failed(lit_to_pl(l)))
            take({l}, l.var() >= orig_num_vars);
    verb_print(3, "[interp] core: " << core_cls << " / " << n_cls
            << " doubled clauses, " << mini_cls.size() << " mini-CNF clauses");

    // --- 2. Solve the mini-CNF on a fresh CaDiCaL with the McMillan
    // tracer, which reconstructs the interpolant from the UNSAT proof.
    // Partition: A = clauses entirely in copy 1, B = everything else.
    auto cdcl = std::make_unique<Solver>();
    InterpTracerMcMillan tracer(conf, *aig_mng, input_vars);
    // copy-2 and indicator variables (index >= orig_num_vars) are B-local.
    tracer.b_local_from = orig_num_vars;
    cdcl->connect_proof_tracer(&tracer, true);

    for (size_t i = 0; i < mini_cls.size(); i++) {
        tracer.next_is_b = mini_is_b[i];
        for (const auto& l : mini_cls[i]) cdcl->add(lit_to_pl(l));
        cdcl->add(0);
        tracer.next_is_b = false;
    }

    if (!conf.debug_synth.empty()) {
        std::stringstream name;
        name << conf.debug_synth << "-core-" << test_var+1 << ".cnf";
        verb_print(1, "[interp] writing mini-CNF to: " << name.str());
        auto f = std::ofstream(name.str());
        f << "p cnf " << tot_num_vars << " " << mini_cls.size() << endl;
        f << "c orig_num_vars: " << orig_num_vars << endl;
        f << "c output: " << test_var+1 << endl;
        for (const auto& c : mini_cls) f << c << " 0" << endl;
        f.close();
    }

    const int ret = cdcl->solve();
    cdcl->disconnect_proof_tracer(&tracer);
    // CMS already proved this UNSAT and the prefilter preserves UNSAT, so
    // the mini-CNF must come back UNSAT (20).
    release_assert(ret == 20 && "interpolant mini-CNF must be UNSAT");

    aig_ptr interp = tracer.build_interpolant();
    // The proof exists and was traced, so reconstruction must succeed.
    release_assert(interp != nullptr
        && "interpolant tracer failed to reconstruct from proof");
    interp = AIG::simplify_aig(interp);
    release_assert(interp != nullptr
        && "interpolant: simplify_aig returned null");

    defs[test_var] = interp;
    verb_print(5, "[interp] definition of var " << test_var+1
            << " is: " << interp);
}
