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

#pragma once

#include <cryptominisat5/solvertypesmini.h>
#include "constants.h"
#include "arjun.h"
#include "config.h"
#include "interp_repair.h"
#include <cadical.hpp>
#include <vector>
#include <set>
#include <memory>
#include <cstdint>

namespace ArjunInt {

// Definition extraction by Craig interpolation over a doubled CNF.
//
// extend/backward build a doubled formula: copy 1 = vars [0, orig_num_vars),
// copy 2 = vars [orig_num_vars, 2*orig_num_vars), tied together by
// indicator variables. When the doubled solver proves a `test_var` is
// functionally determined by the input variables (UNSAT under the
// test_var-differs-across-copies assumptions), the McMillan interpolant of
//   A = clauses lying entirely inside copy 1
//   B = everything else (copy 2, indicators, and their units)
// over the shared input variables IS the definition of test_var.
//
// The doubled CNF is loaded once in fill_from_solver into one
// persistent incremental CaDiCaL with InterpTracerMcMillan attached; indicator
// units are added via add_unit_cl. Each generate_interpolant is one
// assumption-based solve (assume the differs-across-copies lits, solve,
// conclude()), so per-test_var cost is just the solve plus proof-core rebuild.
//
// The tracer's clause maps (cls / antec) can't be pruned safely — a derived
// clause may antecede a later proof — so they grow unboundedly. The
// solver + tracer are therefore rebuilt every conf.interp_rebuild_every
// interpolants to cap memory and lookup cost.
class Interpolant {
public:
    Interpolant(const Config& _conf, const uint32_t num_vars) :
        conf(_conf) {
        defs.resize(num_vars, nullptr);
    }
    ~Interpolant();

    // Extract the doubled CNF from `solver` once and load
    // it into the persistent incremental interpolation solver, before the
    // per-variable solve loop starts. `input_vars` is the caller's live
    // input-variable set: the tracer keeps a reference to it and picks up
    // variables added to it as the loop proceeds.
    void fill_from_solver(CMSat::SATSolver* solver, uint32_t orig_num_vars,
        const ArjunNS::AIGManager& aig_mng,
        const std::set<uint32_t>& input_vars);

    // `test_var` was just proven UNSAT under `assumptions`; reconstruct
    // and store its definition AIG over the current input vars.
    void generate_interpolant(const std::vector<CMSat::Lit>& assumptions,
        uint32_t test_var);

    // Record an indicator unit clause permanently added to the doubled
    // problem (a var proven independent/defined): add it, B-side, to the
    // persistent interpolation solver too.
    void add_unit_cl(const std::vector<CMSat::Lit>& cl);

    auto& get_defs() { return defs; }

private:
    const Config conf;
    uint32_t orig_num_vars = 0;
    uint32_t tot_num_vars = 0;
    const ArjunNS::AIGManager* aig_mng = nullptr;

    // The doubled CNF, extracted once in fill_from_solver
    // (kept only for the optional --debugsynth CNF dump).
    std::vector<std::vector<CMSat::Lit>> all_cls;
    // Indicator units accumulated as variables get defined / proven
    // independent over the course of the solve loop.
    std::vector<CMSat::Lit> indicator_units;

    // Persistent incremental CaDiCaL holding the doubled CNF + indicator
    // units, with the McMillan tracer attached. Rebuilt periodically.
    std::unique_ptr<CaDiCaL::Solver> solver;
    std::unique_ptr<InterpTracerMcMillan> tracer;
    // The caller's live input-variable set, bound into each fresh tracer.
    const std::set<uint32_t>* input_vars = nullptr;
    // Interpolants produced since the last (re)build of solver + tracer.
    uint32_t solves_since_rebuild = 0;

    // defs[v] = AIG definition of v over the input vars (original var
    // space), or nullptr if v was not defined this way.
    std::vector<ArjunNS::aig_ptr> defs;

    // Create a fresh solver + tracer and (re)load the doubled CNF and the
    // indicator units accumulated so far into it.
    void load_solver();

    // A clause is A-side iff it lies entirely inside copy 1.
    bool is_b_clause(const std::vector<CMSat::Lit>& cl) const {
        for (const auto& l : cl)
            if (l.var() >= orig_num_vars) return true;
        return false;
    }
};

}
