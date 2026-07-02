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

// McMillan-style interpolant tracer for the partition
//   A = clauses entirely inside copy 1,   B = everything else
//
// The tracer is told which original-clause IDs are B (via next_is_b before
// each solver->add(0)). Derived clauses get a label computed from the
// antecedents via McMillan's rule:
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

    // O(1) shared-var lookup. "Shared" = a B-visible var, i.e. an input var.
    [[nodiscard]] bool is_shared(uint32_t v) const {
        return input_vars.count(v) != 0;
    }

    // Set by the caller before each solver->add(0): is the next clause
    // B-side (label TRUE) or A-side (label = OR of input lits)?
    bool next_is_b = false;

    // McMillan's labelled-interpolation rule: a shared (input) pivot is
    // 'b' → AND of children (the strongest interpolant); an A-local pivot
    // is 'a' → OR.

    // Variables with index >= b_local_from are B-local: they occur only
    // in B clauses, so a resolution pivot on them is AND'd just like a
    // shared (input) pivot. The doubled-CNF interpolation sets it to
    // orig_num_vars so the copy-2 and indicator variables (the bulk of its
    // B side) are handled correctly. A-local pivots (below the threshold,
    // non-input) → OR.
    uint32_t b_local_from = UINT32_MAX;

    // Original clauses decided to be B-side (label = TRUE). Clause-id keyed,
    // only point-accessed (never iterated) so unordered is determinism-safe
    // and gives resolve_chain O(1) lookup.
    std::unordered_set<uint64_t> b_clause_ids;

    // ID -> clause literals (kept to find resolution pivots).
    std::unordered_map<uint64_t, std::vector<CMSat::Lit>> cls;
    // ID -> partial McMillan label (an AIG over input vars), filled for
    // the proof core during build_interpolant().
    std::unordered_map<uint64_t, ArjunNS::aig_lit> labels;
    // ID -> antecedent chain for derived clauses. Recorded as the proof
    // streams in, but only resolved (into a label) for the proof core.
    std::unordered_map<uint64_t, std::vector<uint64_t>> antec;

    // Cache: input lit -> AIG leaf node, so structural hashing dedups.
    std::map<CMSat::Lit, ArjunNS::aig_lit> lit_to_aig;

    // Structural-hash table over the t_and nodes built while resolving
    // partial interpolants. Keyed on the canonicalised (smaller-nid
    // first) child edges so equal cones across different proof clauses
    // collapse to one shared sub-DAG instead of a fresh tree each time.
    std::map<ArjunNS::AIG::AIGKey, ArjunNS::aig_lit> and_table;
    ArjunNS::aig_lit hash_and(const ArjunNS::aig_lit& l,
                              const ArjunNS::aig_lit& r);
    ArjunNS::aig_lit hash_or(const ArjunNS::aig_lit& l,
                             const ArjunNS::aig_lit& r);

    // ID of the derived empty clause; set when first seen.
    uint64_t empty_id = UINT64_MAX;

    // Incremental (assumption-based) solving. cadical reports the
    // refutation through conclude_unsat() after conclude() is called.
    // conclusion_root is the id of the derived empty clause (CONFLICT) or
    // of the failing-assumption clause (ASSUMPTIONS).
    int conclusion_type = 0;
    uint64_t conclusion_root = UINT64_MAX;

    // Set by build_interpolant(): the McMillan interpolant AIG, or null.
    ArjunNS::aig_lit out = nullptr;

    // For diagnostics.
    uint64_t derived_count = 0;
    uint64_t orig_count = 0;
    // Derived clauses actually on the proof core (reachable from the
    // empty clause), set by build_interpolant().
    uint64_t core_count = 0;

    void mark_b_clause(uint64_t id) { b_clause_ids.insert(id); }

    ArjunNS::aig_lit lit_aig(CMSat::Lit l);
    // OR of the shared (B-visible) lits in `cl` — the partial label for an
    // A-side clause. "Shared" is decided by is_shared() = the input_vars set.
    ArjunNS::aig_lit or_of_shared_lits(const std::vector<CMSat::Lit>& cl);

    void add_original_clause(uint64_t id, bool red,
            const std::vector<int>& clause, bool restored = false) override;
    void add_derived_clause(uint64_t id, bool red,
            const std::vector<int>& clause,
            const std::vector<uint64_t>& antecedents) override;

    // Incremental-solving events. Needed when the tracer is reused
    // across several assumption-based solves on one persistent solver.
    // add_assumption_clause() records the failing-assumption clause;
    // conclude_unsat() reports the refutation root.
    void add_assumption_clause(uint64_t id,
            const std::vector<int>& clause,
            const std::vector<uint64_t>& antecedents) override;
    void conclude_unsat(CaDiCaL::ConclusionType type,
            const std::vector<uint64_t>& ids) override;

    // Drop the per-solve scratch (labels, and-table, refutation root)
    // before the next incremental solve. cls / antec / b_clause_ids are
    // kept — the clause database outlives a single solve. The caller
    // must invoke this between solves; it is deliberately not driven by
    // the solve_query() callback, since cadical can derive the empty
    // clause already while clauses are being added, before solve().
    void reset_per_solve();

    // Trace back from the refutation root (empty clause, or the
    // failing-assumption clause) over the recorded antecedent chains,
    // build McMillan labels only for the reachable proof-core clauses,
    // and return the interpolant AIG (sets `out`). Returns null if no
    // refutation was recorded.
    ArjunNS::aig_lit build_interpolant();

private:
    // McMillan label of an original clause, computed lazily from
    // the current input_vars — deferred out of add_original_clause so a
    // persistent tracer picks up input vars added since the clause was.
    [[nodiscard]] ArjunNS::aig_lit original_label(uint64_t id);
    // Resolve one derived clause's antecedent chain into a McMillan
    // label. Tries the chain reversed, then forward.
    void build_derived_label(uint64_t id);
    // Replay `chain` as a linear resolution and set labels[id]. Returns
    // false (with labels[id] left at a partial value) if the chain is
    // not a clean linear resolution in this order.
    [[nodiscard]] bool resolve_chain(uint64_t id,
            const std::vector<uint64_t>& chain);
};

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
