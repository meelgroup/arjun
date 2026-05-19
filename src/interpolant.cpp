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

void Interpolant::fill_from_solver(SATSolver* solver, uint32_t _orig_num_vars,
        const AIGManager& _aig_mng) {
    orig_num_vars = _orig_num_vars;
    tot_num_vars = solver->nVars();
    aig_mng = &_aig_mng;

    // Extract the (already CMS-simplified) doubled CNF once. The indicator
    // units permanently added to the solver later are tracked via
    // add_unit_cl.
    all_cls.clear();
    solver->start_getting_constraints(false);
    vector<Lit> cl;
    bool is_xor, rhs;
    while (solver->get_next_constraint(cl, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        all_cls.push_back(cl);
    }
    solver->end_getting_constraints();

    verb_print(2, "[interp] doubled CNF extracted: " << all_cls.size()
            << " clauses, " << tot_num_vars << " vars");
}

void Interpolant::add_unit_cl(const vector<Lit>& cl) {
    assert(cl.size() == 1);
    // Folded into every later interpolant solve as a B-side unit.
    indicator_units.push_back(cl[0]);
}

void Interpolant::generate_interpolant(const vector<Lit>& assumptions,
        uint32_t test_var, const set<uint32_t>& input_vars) {
    verb_print(2, "[interp] generating interpolant for var: " << test_var+1);
    verb_print(3, "[interp] assumptions: " << assumptions);

    // Solve the whole doubled CNF (plus the accumulated indicator units
    // and this test_var's assumptions, all added as clauses) on a fresh
    // CaDiCaL with the McMillan tracer, which reconstructs the interpolant
    // from the UNSAT proof. Clauses the refutation never touches never
    // enter the proof, hence never enter the interpolant, so no separate
    // core-extraction pre-solve is needed.
    // Partition: A = clauses entirely in copy 1, B = everything else.
    auto cdcl = std::make_unique<Solver>();
    InterpTracerMcMillan tracer(conf, *aig_mng, input_vars);
    // copy-2 and indicator variables (index >= orig_num_vars) are B-local.
    tracer.b_local_from = orig_num_vars;
    cdcl->connect_proof_tracer(&tracer, true);

    auto add_cl = [&](const vector<Lit>& cl, bool is_b) {
        tracer.next_is_b = is_b;
        for (const auto& l : cl) cdcl->add(lit_to_pl(l));
        cdcl->add(0);
        tracer.next_is_b = false;
    };
    for (const auto& cl : all_cls) add_cl(cl, is_b_clause(cl));
    for (const auto& l : indicator_units)         // indicator units are B-side
        add_cl(vector<Lit>{l}, true);
    for (const auto& l : assumptions)
        add_cl(vector<Lit>{l}, l.var() >= orig_num_vars);

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

    const int ret = cdcl->solve();
    cdcl->disconnect_proof_tracer(&tracer);
    // CMS already proved this UNSAT under the same assumptions, so the
    // doubled CNF must come back UNSAT (20).
    release_assert(ret == 20 && "interpolant doubled-CNF must be UNSAT");

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
