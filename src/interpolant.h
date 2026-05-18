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
// No PicoSAT is involved. The (CMS-simplified) doubled CNF is extracted
// once into a persistent incremental CaDiCaL where every clause is
// guarded by a fresh selector literal. Per test_var: assume all
// selectors + the test_var assumptions, solve, and read the UNSAT core
// back via failed() — a true clause-level core, as small as PicoSAT's
// was. That core (and only it) feeds a fresh CaDiCaL solve with
// InterpTracerMcMillan, which reconstructs the interpolant from the
// proof.
class Interpolant {
public:
    Interpolant(const Config& _conf, const uint32_t num_vars) :
        conf(_conf) {
        defs.resize(num_vars, nullptr);
    }
    ~Interpolant() = default;

    // Extract the (CMS-simplified) doubled CNF from `solver` once, before
    // the per-variable solve loop starts.
    void fill_from_solver(CMSat::SATSolver* solver, uint32_t orig_num_vars,
        const ArjunNS::AIGManager& aig_mng);

    // `test_var` was just proven UNSAT under `assumptions`; reconstruct
    // and store its definition AIG over `input_vars`.
    void generate_interpolant(const std::vector<CMSat::Lit>& assumptions,
        uint32_t test_var, const std::set<uint32_t>& input_vars);

    // Record an indicator unit clause permanently added to the doubled
    // problem (a var proven independent/defined). Folded into every later
    // mini-CNF as a B-side unit.
    void add_unit_cl(const std::vector<CMSat::Lit>& cl);

    auto& get_defs() { return defs; }

private:
    const Config conf;
    uint32_t orig_num_vars = 0;
    uint32_t tot_num_vars = 0;
    const ArjunNS::AIGManager* aig_mng = nullptr;

    // The doubled CMS-simplified CNF, extracted once in fill_from_solver.
    std::vector<std::vector<CMSat::Lit>> all_cls;
    // Indicator units accumulated as variables get defined / proven
    // independent over the course of the solve loop.
    std::vector<CMSat::Lit> indicator_units;

    // Persistent incremental CaDiCaL for clause-level core extraction.
    // Holds every clause of all_cls and every indicator unit, each
    // guarded by a selector literal. Selector variables start at
    // tot_num_vars: clause i of all_cls uses selector tot_num_vars+i,
    // indicator unit k uses tot_num_vars+all_cls.size()+k.
    std::unique_ptr<CaDiCaL::Solver> core_solver;

    // defs[v] = AIG definition of v over the input vars (original var
    // space), or nullptr if v was not defined this way.
    std::vector<ArjunNS::aig_ptr> defs;

    // A clause is A-side iff it lies entirely inside copy 1.
    bool is_b_clause(const std::vector<CMSat::Lit>& cl) const {
        for (const auto& l : cl)
            if (l.var() >= orig_num_vars) return true;
        return false;
    }
};

}
