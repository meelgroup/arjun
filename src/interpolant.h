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
#include <cadical.hpp>
#include <tracer.hpp>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <memory>
#include <cstdint>

namespace ArjunInt {

// McMillan labelled interpolation for the partition
//   A = clauses entirely inside copy 1,   B = everything else.
// Original A clauses get label = OR of their shared lits, B clauses get TRUE.
// A resolution pivot on a shared/B-local var → AND of children, on an
// A-local var → OR.
struct InterpTracerMcMillan : public CaDiCaL::Tracer {
    InterpTracerMcMillan(const Config& _conf,
        const ArjunNS::AIGManager& _aig_mng,
        const std::set<uint32_t>& _input_vars)
        : conf(_conf), aig_mng(_aig_mng), input_vars(_input_vars) {}

    const Config& conf;
    const ArjunNS::AIGManager& aig_mng;
    const std::set<uint32_t>& input_vars;

    // "Shared" = a B-visible var, i.e. an input var.
    [[nodiscard]] bool is_shared(uint32_t v) const {
        return input_vars.count(v) != 0;
    }

    // Set before each solver->add(0): is the next original clause B-side?
    bool next_is_b = false;

    // Vars with index >= b_local_from occur only in B, so a pivot on them
    // is AND'd like a shared pivot. Set to orig_num_vars by the doubled-CNF
    // interpolation to cover the copy-2 and indicator variables.
    uint32_t b_local_from = UINT32_MAX;

    std::unordered_set<uint64_t> b_clause_ids;
    std::unordered_map<uint64_t, std::vector<CMSat::Lit>> cls;
    std::unordered_map<uint64_t, ArjunNS::aig_lit> labels;
    std::unordered_map<uint64_t, std::vector<uint64_t>> antec;
    std::map<CMSat::Lit, ArjunNS::aig_lit> lit_to_aig;

    // Structural-hash table over t_and nodes, keyed on canonicalised child
    // edges so equal cones across proof clauses share one sub-DAG.
    std::map<ArjunNS::AIG::AIGKey, ArjunNS::aig_lit> and_table;
    ArjunNS::aig_lit hash_and(const ArjunNS::aig_lit& l,
                              const ArjunNS::aig_lit& r);
    ArjunNS::aig_lit hash_or(const ArjunNS::aig_lit& l,
                             const ArjunNS::aig_lit& r);

    uint64_t empty_id = UINT64_MAX;

    // cadical reports the refutation via conclude_unsat(). conclusion_root
    // is the empty clause (CONFLICT) or failing-assumption clause (ASSUMPTIONS).
    int conclusion_type = 0;
    uint64_t conclusion_root = UINT64_MAX;

    ArjunNS::aig_lit out = nullptr;

    uint64_t derived_count = 0;
    uint64_t orig_count = 0;
    uint64_t core_count = 0;

    void mark_b_clause(uint64_t id) { b_clause_ids.insert(id); }

    ArjunNS::aig_lit lit_aig(CMSat::Lit l);
    ArjunNS::aig_lit or_of_shared_lits(const std::vector<CMSat::Lit>& cl);

    void add_original_clause(uint64_t id, bool red,
            const std::vector<int>& clause, bool restored = false) override;
    void add_derived_clause(uint64_t id, bool red,
            const std::vector<int>& clause,
            const std::vector<uint64_t>& antecedents) override;
    void add_assumption_clause(uint64_t id,
            const std::vector<int>& clause,
            const std::vector<uint64_t>& antecedents) override;
    void conclude_unsat(CaDiCaL::ConclusionType type,
            const std::vector<uint64_t>& ids) override;

    // Drop per-solve scratch (labels, and-table, refutation root) between
    // solves; cls / antec / b_clause_ids outlive a single solve. Must be
    // called by the caller, not solve_query(): cadical can derive the empty
    // clause while clauses are still being added, before solve().
    void reset_per_solve();

    // Trace back from the refutation root over the antecedent chains,
    // build McMillan labels for the reachable proof core, and return the
    // interpolant AIG (also sets `out`). Null if no refutation was recorded.
    ArjunNS::aig_lit build_interpolant();

private:
    // Computed lazily from the current input_vars so a persistent tracer
    // picks up input vars added after the clause.
    [[nodiscard]] ArjunNS::aig_lit original_label(uint64_t id);
    void build_derived_label(uint64_t id);
    // Replay `chain` as a linear resolution into labels[id]. Returns false
    // (labels[id] left partial) if the chain is not a clean linear resolution.
    [[nodiscard]] bool resolve_chain(uint64_t id,
            const std::vector<uint64_t>& chain);
};

// Definition extraction by Craig interpolation over a doubled CNF.
//
// extend/backward build a doubled formula: copy 1 = vars [0, orig_num_vars),
// copy 2 = vars [orig_num_vars, 2*orig_num_vars), tied by indicators. When
// `test_var` is proven determined by the input vars (UNSAT under the
// differs-across-copies assumptions), the McMillan interpolant of A = copy 1,
// B = everything else, over the shared input vars, IS its definition.
//
// The doubled CNF is loaded once into a persistent incremental CaDiCaL with
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

    void fill_from_solver(CMSat::SATSolver* solver, uint32_t orig_num_vars,
        const ArjunNS::AIGManager& aig_mng,
        const std::set<uint32_t>& input_vars);

    // Reconstruct and store test_var's definition AIG. Returns false (var
    // left undefined) if the solve exceeded conf.interp_max_confl.
    bool generate_interpolant(const std::vector<CMSat::Lit>& assumptions,
        uint32_t test_var);

    // Add an indicator unit (a var proven independent/defined), B-side.
    void add_unit_cl(const std::vector<CMSat::Lit>& cl);

    auto& get_defs() { return defs; }

private:
    const Config conf;
    uint32_t orig_num_vars = 0;
    uint32_t tot_num_vars = 0;
    const ArjunNS::AIGManager* aig_mng = nullptr;

    // The doubled CNF, kept for the --debugsynth CNF dump.
    std::vector<std::vector<CMSat::Lit>> all_cls;
    std::vector<CMSat::Lit> indicator_units;

    std::unique_ptr<CaDiCaL::Solver> solver;
    std::unique_ptr<InterpTracerMcMillan> tracer;
    const std::set<uint32_t>* input_vars = nullptr;
    uint32_t solves_since_rebuild = 0;

    // defs[v] = AIG definition of v over the input vars, or nullptr.
    std::vector<ArjunNS::aig_lit> defs;

    void load_solver();

    // B-side iff it touches any var outside copy 1.
    bool is_b_clause(const std::vector<CMSat::Lit>& cl) const {
        for (const auto& l : cl)
            if (l.var() >= orig_num_vars) return true;
        return false;
    }
};

}
