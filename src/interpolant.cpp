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

Interpolant::~Interpolant() {
    // Detach the tracer before either it or the solver is destroyed:
    // an attached tracer is otherwise deleted by the solver's destructor.
    if (solver && tracer) solver->disconnect_proof_tracer(tracer.get());
}

void Interpolant::load_solver() {
    // Build a fresh incremental CaDiCaL + McMillan tracer and (re)load the
    // doubled CNF and the indicator units accumulated so far. Partition:
    // A = clauses entirely in copy 1, B = everything else (copy 2,
    // indicators, and their units).
    solver = std::make_unique<Solver>();
    tracer = std::make_unique<InterpTracerMcMillan>(conf, *aig_mng, *input_vars);
    // copy-2 and indicator variables (index >= orig_num_vars) are B-local.
    tracer->b_local_from = orig_num_vars;
    solver->connect_proof_tracer(tracer.get(), true);

    for (const auto& c : all_cls) {
        tracer->next_is_b = is_b_clause(c);
        for (const auto& l : c) solver->add(lit_to_pl(l));
        solver->add(0);
        tracer->next_is_b = false;
    }
    for (const auto& l : indicator_units) {
        tracer->next_is_b = true;
        solver->add(lit_to_pl(l));
        solver->add(0);
        tracer->next_is_b = false;
    }
    solves_since_rebuild = 0;
}

void Interpolant::fill_from_solver(SATSolver* cms_solver,
        uint32_t _orig_num_vars, const AIGManager& _aig_mng,
        const set<uint32_t>& _input_vars) {
    orig_num_vars = _orig_num_vars;
    tot_num_vars = cms_solver->nVars();
    aig_mng = &_aig_mng;
    input_vars = &_input_vars;

    // Extract the doubled CNF once. The indicator
    // units permanently added to the solver later come via add_unit_cl.
    all_cls.clear();
    cms_solver->start_getting_constraints(false);
    vector<Lit> cl;
    bool is_xor, rhs;
    while (cms_solver->get_next_constraint(cl, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        all_cls.push_back(cl);
    }
    cms_solver->end_getting_constraints();

    load_solver();
    verb_print(2, "[interp] doubled CNF loaded into incremental solver: "
            << all_cls.size() << " clauses, " << tot_num_vars << " vars");
}

void Interpolant::add_unit_cl(const vector<Lit>& cl) {
    assert(cl.size() == 1);
    // A variable proven defined/independent: add its indicator unit,
    // B-side, to the persistent interpolation solver.
    tracer->next_is_b = true;
    solver->add(lit_to_pl(cl[0]));
    solver->add(0);
    tracer->next_is_b = false;
    indicator_units.push_back(cl[0]);
}

void Interpolant::generate_interpolant(const vector<Lit>& assumptions,
        uint32_t test_var) {
    verb_print(2, "[interp] generating interpolant for var: " << test_var+1);
    verb_print(3, "[interp] assumptions: " << assumptions);

    if (!conf.debug_synth.empty()) {
        std::stringstream name;
        name << conf.debug_synth << "-core-" << test_var+1 << ".cnf";
        verb_print(1, "[interp] writing doubled CNF to: " << name.str());
        const size_t n = all_cls.size() + indicator_units.size()
                + assumptions.size();
        auto f = std::ofstream(name.str());
        f << "p cnf " << tot_num_vars << " " << n << endl;
        f << "c orig_num_vars: " << orig_num_vars << endl;
        f << "c output: " << test_var+1 << endl;
        for (const auto& c : all_cls) f << c << " 0" << endl;
        for (const auto& l : indicator_units) f << l << " 0" << endl;
        for (const auto& l : assumptions) f << l << " 0" << endl;
        f.close();
    }

    // One incremental, assumption-based solve on the persistent solver.
    // The test_var assumptions are assumed (not added as clauses), so the
    // doubled CNF and indicator units stay reusable for the next call.
    tracer->reset_per_solve();
    for (const auto& l : assumptions) solver->assume(lit_to_pl(l));
    const int ret = solver->solve();
    // CMS already proved this UNSAT under the same assumptions.
    release_assert(ret == 20 && "interpolant solve must be UNSAT");
    // conclude() makes cadical emit the incremental-proof conclusion, so
    // the tracer sees the failing-assumption clause and conclude_unsat.
    solver->conclude();

    aig_ptr interp = tracer->build_interpolant();
    // Invariant: after a UNSAT solve the tracer has seen a refutation root,
    // so build_interpolant returns a non-null AIG.
    release_assert(interp != nullptr
        && "interpolant: build_interpolant returned null after UNSAT proof");
    interp = AIG::simplify_aig(interp);
    release_assert(interp != nullptr
        && "interpolant: simplify_aig returned null");

    defs[test_var] = interp;
    verb_print(5, "[interp] definition of var " << test_var+1
            << " is: " << interp);

    // Periodically rebuild solver + tracer so the tracer's clause maps
    // (which accumulate every clause of every solve) do not grow without
    // bound. The doubled CNF and indicator units are simply reloaded.
    if (++solves_since_rebuild >= conf.interp_rebuild_every) {
        verb_print(2, "[interp] rebuilding incremental solver after "
                << solves_since_rebuild << " interpolants");
        solver->disconnect_proof_tracer(tracer.get());
        load_solver();
    }
}
