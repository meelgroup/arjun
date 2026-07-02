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
// copy 2 = vars [orig_num_vars, 2*orig_num_vars), tied by indicators. When the
// solver proves `test_var` is determined by the input vars (UNSAT under the
// differs-across-copies assumptions), the McMillan interpolant of
//   A = clauses entirely inside copy 1,   B = everything else
// over the shared input vars IS the definition of test_var.
//
// The doubled CNF is loaded once into one persistent incremental CaDiCaL with
// InterpTracerMcMillan attached; each generate_interpolant is one
// assumption-based solve. The tracer's clause maps can't be pruned safely, so
// solver + tracer are rebuilt every conf.interp_rebuild_every interpolants.
class Interpolant {
public:
    Interpolant(const Config& _conf, const uint32_t num_vars) :
        conf(_conf) {
        defs.resize(num_vars, nullptr);
    }
    ~Interpolant();

    // Load the doubled CNF from `solver` into the interpolation solver. The
    // tracer keeps a reference to `input_vars` and picks up vars added later.
    void fill_from_solver(CMSat::SATSolver* solver, uint32_t orig_num_vars,
        const ArjunNS::AIGManager& aig_mng,
        const std::set<uint32_t>& input_vars);

    // `test_var` was just proven UNSAT under `assumptions`; reconstruct
    // and store its definition AIG over the current input vars.
    void generate_interpolant(const std::vector<CMSat::Lit>& assumptions,
        uint32_t test_var);

    // Add an indicator unit (a var proven independent/defined), B-side.
    void add_unit_cl(const std::vector<CMSat::Lit>& cl);

    auto& get_defs() { return defs; }

private:
    const Config conf;
    uint32_t orig_num_vars = 0;
    uint32_t tot_num_vars = 0;
    const ArjunNS::AIGManager* aig_mng = nullptr;

    // The doubled CNF, extracted once (kept for the --debugsynth CNF dump).
    std::vector<std::vector<CMSat::Lit>> all_cls;
    std::vector<CMSat::Lit> indicator_units;

    // Persistent incremental CaDiCaL + McMillan tracer, rebuilt periodically.
    std::unique_ptr<CaDiCaL::Solver> solver;
    std::unique_ptr<InterpTracerMcMillan> tracer;
    const std::set<uint32_t>* input_vars = nullptr;
    uint32_t solves_since_rebuild = 0;

    // defs[v] = AIG definition of v over the input vars, or nullptr.
    std::vector<ArjunNS::aig_lit> defs;

    void load_solver();

    // A clause is B-side iff it touches any var outside copy 1.
    bool is_b_clause(const std::vector<CMSat::Lit>& cl) const {
        for (const auto& l : cl)
            if (l.var() >= orig_num_vars) return true;
        return false;
    }
};

}
