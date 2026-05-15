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

// Craig-interpolant repair for Manthan (Option 2 in IDEAS-3-categories.md).
//
// On a Manthan repair, find_conflict returns an UNSAT core
// (input lits + y-other lits + ~to_repair). The conflict clause is a
// single corner of input space. The interpolant in input vars only
// generalises to the entire region of inputs for which flipping y_rep
// is required. compose_or/and on the interpolant AIG (instead of an
// AND-of-conflict-literals AIG) captures many would-be repairs at once.

#pragma once

#include "arjun.h"
#include "config.h"
#include "constants.h"
#include <cryptominisat5/solvertypesmini.h>
#include <cadical.hpp>
#include <tracer.hpp>
#include <map>
#include <set>
#include <vector>
#include <cstdint>
#include <memory>

namespace ArjunInt {

// McMillan-style interpolant tracer for the partition
//   A = original CNF + non-input assumption units (~to_repair, y-other lits)
//   B = input assumption units
//
// The tracer is told which original-clause IDs are B (input units). Every
// other original clause is treated as A. Derived clauses get a label
// computed from the antecedents via McMillan's rule:
//   - resolution on a shared (= input) literal     → AND of children
//   - resolution on an A-local (= non-input) lit   → OR  of children
struct InterpTracerMcMillan : public CaDiCaL::Tracer {
    InterpTracerMcMillan(const Config& _conf,
        const ArjunNS::AIGManager& _aig_mng,
        const std::set<uint32_t>& _input_vars)
        : conf(_conf), aig_mng(_aig_mng), input_vars(_input_vars) {}

    const Config& conf;
    const ArjunNS::AIGManager& aig_mng;
    const std::set<uint32_t>& input_vars;

    // Set by the caller before each solver->add(0) so the synchronous
    // add_original_clause callback knows whether the about-to-arrive
    // clause is B-side (label = TRUE) or A-side (label = OR of input lits).
    // Default = false (A-side).
    bool next_is_b = false;

    // Original clauses we've decided are B-side (label = TRUE). Anything
    // else is A-side (label = OR of input literals in the clause).
    std::set<uint64_t> b_clause_ids;

    // ID -> clause literals (we keep these to know what pivots to look for
    // on resolution).
    std::map<uint64_t, std::vector<CMSat::Lit>> cls;
    // ID -> partial McMillan label (an AIG over input vars).
    std::map<uint64_t, ArjunNS::aig_ptr> labels;

    // Cache: input lit -> AIG leaf node, so structural hashing dedups.
    std::map<CMSat::Lit, ArjunNS::aig_ptr> lit_to_aig;

    // Set when the empty clause is derived. The repair caller reads this
    // and uses it as the interpolant.
    ArjunNS::aig_ptr out = nullptr;

    // For diagnostics.
    uint64_t derived_count = 0;
    uint64_t orig_count = 0;

    void mark_b_clause(uint64_t id) { b_clause_ids.insert(id); }

    ArjunNS::aig_ptr lit_aig(CMSat::Lit l);
    ArjunNS::aig_ptr or_of_input_lits(const std::vector<CMSat::Lit>& cl);

    void add_original_clause(uint64_t id, bool red,
            const std::vector<int>& clause, bool restored = false) override;
    void add_derived_clause(uint64_t id, bool red,
            const std::vector<int>& clause,
            const std::vector<uint64_t>& antecedents) override;
};

class InterpRepair {
public:
    InterpRepair(const Config& _conf,
        const ArjunNS::SimplifiedCNF& _cnf,
        const std::set<uint32_t>& _input_vars,
        ArjunNS::AIGManager& _aig_mng);
    ~InterpRepair() = default;

    // Compute an interpolant I(input_vars) such that:
    //   - For inputs in I, flipping y_rep is feasible (so y_rep_func can stay)
    //   - For the original CEX inputs, I is FALSE (we need to learn the flip)
    //
    // Args:
    //   y_rep         : the variable being repaired
    //   to_repair_lit : the literal whose negation is being assumed
    //                   (i.e. y_rep with the WRONG value the candidate gave)
    //   conflict      : conflict literals from repair_solver (excludes
    //                   to_repair). Each is a unit assumption.
    //
    // Returns nullptr on failure (interpolation problem reported SAT,
    // returned an oversized AIG, or hit any internal error).
    ArjunNS::aig_ptr compute_interpolant(
        uint32_t y_rep, CMSat::Lit to_repair_lit,
        const std::vector<CMSat::Lit>& conflict,
        uint32_t max_aig_nodes = 0);

    // Light-weight check: that the interpolant evaluates to FALSE on the
    // CEX input pattern (i.e. on this CEX's inputs, the interpolant
    // correctly says "must flip"). Returns true on pass.
    [[nodiscard]] bool quick_check_interpolant_excludes_cex(
        const ArjunNS::aig_ptr& interp,
        const std::vector<CMSat::Lit>& conflict) const;

    // Statistics (read-only)
    uint64_t calls = 0;
    uint64_t calls_succeeded = 0;
    uint64_t calls_failed_oversize = 0;
    uint64_t calls_failed_other = 0;
    uint64_t calls_quick_check_failed = 0;
    uint64_t total_interp_nodes = 0;
    uint64_t total_conflict_lits = 0;
    double   total_solve_time = 0.0;
    double   total_setup_time = 0.0;

    void print_stats(const std::string& prefix = "[interp-repair]") const;

private:
    const Config& conf;
    const ArjunNS::SimplifiedCNF& cnf;
    const std::set<uint32_t>& input_vars;
    ArjunNS::AIGManager& aig_mng;

    // Byte-map for O(1) input-membership check.
    std::vector<uint8_t> is_input;
};

} // namespace ArjunInt
