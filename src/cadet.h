/*
 Arjun

 cadet.h — In-tree port of CADET's incremental-determinization core (Markus
 N. Rabe, SAT 2016). Used in place of Manthan when --cadet 1 is set.

 Copyright (c) 2026, Mate Soos. All rights reserved.

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

#include "arjun.h"
#include "config.h"
#include "metasolver.h"
#include <cryptominisat5/solvertypesmini.h>

#include <cstdint>
#include <map>
#include <memory>
#include <set>
#include <vector>

namespace ArjunInt {

// Cadet — synthesis driver that mirrors Manthan's API surface but uses a
// CADET-style incremental-determinization algorithm to construct Skolem
// functions for the unsynthesized variables of a SimplifiedCNF.
//
// Like Manthan, it consumes a SimplifiedCNF where some variables are already
// synthesized (have an AIG in cnf.defs[v]) and others are not; it produces a
// SimplifiedCNF where every previously-unsynthesized variable has been
// assigned an AIG definition over the inputs and previously-synthesized
// variables. The result satisfies cnf.synth_done().
class Cadet {
public:
    Cadet(const ArjunInt::Config& _conf,
          const ArjunNS::Arjun::ManthanConf& _mconf,
          ArjunNS::SimplifiedCNF&& _cnf);

    ArjunNS::SimplifiedCNF do_cadet();

private:
    const ArjunInt::Config& conf;
    const ArjunNS::Arjun::ManthanConf& mconf;
    ArjunNS::SimplifiedCNF cnf;

    // Var partitions, mirroring Manthan's split. NB: `input` here matches
    // VarTypes.input — it lumps `extend-defined` vars (those with an AIG
    // def depending only on orig sampling vars) together with the orig
    // sampling vars themselves, since the SAT solver treats both as free
    // for synthesis purposes. The narrower "true" set of orig sampling
    // vars (cnf-numbering) is held in `orig_sampl_cnf` and is the one we
    // actually enumerate over.
    std::set<uint32_t> input;            // free + extend-defined
    std::set<uint32_t> to_define;        // vars without an AIG def — Cadet must produce one
    std::set<uint32_t> backward_defined; // vars already defined upstream
    std::set<uint32_t> orig_sampl_cnf;   // orig sampling vars in CNF numbering

    // skol[v] = Skolem function for v in CNF-numbering. Phase C+D
    // initializes input and backward_defined entries to the literal
    // AIG (AIG::new_lit(v, false)) — opaque leaves that
    // map_aigs_to_orig later rewrites to orig-space. For to_define
    // vars, skol starts nullptr and gets filled by the algorithm.
    // Phase F treats input/backward leaves through the SAT solver
    // (their values come from the model), so skol[] for those vars
    // is only used by Phase C+D's AIG-pos_force construction.
    std::vector<ArjunNS::aig_ptr> skol;

    // Persistent Skolem SAT solver — one cadical instance shared
    // across Phase C+D, kept incrementally updated as commits happen.
    // Built once in do_cadet() with F injected; Phase D adds unit
    // clauses as it commits constants, and (later phases) tseitin-
    // encode skol[] AIGs into it on commit. Reusing the same solver
    // lets cadical retain learnt clauses across decisions.
    std::unique_ptr<MetaSolver> skolem_sat;

    // Per-var clause occurrence index: var → [(clause_idx, sign_of_lit)].
    // sign=true means the literal in that clause is the NEGATION of
    // the var. Built once in do_cadet() and reused by Phase C/D so
    // each propagation pass doesn't rebuild it.
    std::vector<std::vector<std::pair<uint32_t, bool>>> var_clauses;

    // clause_dead[ci]=1 once some literal in clause ci has been
    // committed to TRUE (i.e. skol[v]=const matching the lit's sign).
    // Pure-literal detection in Phase C considers a clause "removed"
    // when dead, so an undet var y is pure if every clause containing
    // ¬y (resp. y) has already become dead via other commits.
    std::vector<uint8_t> clause_dead;

    // VSIDS variable activities. var_activity[v] starts at a
    // clause-density seed (Jeroslow-Wang-like) and gets bumped each
    // time v appears in a learnt clause / failed-assumption core.
    // activity_inc grows after each conflict (it's the inverse of
    // multiplicative decay — we scale UP the bump rather than scaling
    // every activity DOWN, then occasionally rescale when overflow
    // threatens). Used by Phase D's variable-pick and Phase F's
    // per-y ordering.
    std::vector<double> var_activity;
    double activity_inc = 1.0;
    static constexpr double kActivityDecay = 0.95;
    static constexpr double kActivityRescaleThreshold = 1e100;

    void bump_var(uint32_t v);
    void decay_activities();

    // Trail of skol[] commits, in commit order. Each entry records the
    // var, whether it was a decision (vs propagation), and the SAT
    // assumption literal that gates this decision (only meaningful for
    // decisions). Used by backjump_to_level to undo speculative
    // commits.
    struct TrailEntry {
        uint32_t var;            // cnf-space var id committed
        uint32_t dec_lvl;        // decision level at the time of commit
        bool is_decision;        // true: a guessed Phase-D decision;
                                 // false: a propagation/forced commit
        CMSat::Lit decision_lit; // only meaningful for decisions —
                                 // the lit assumed in skolem_sat at the
                                 // time of decision. On backjump we
                                 // drop it from active_assumptions.
    };
    std::vector<TrailEntry> trail;

    // Stack of decision lits, indexed by decision level (entry d is
    // the assumption literal for level d+1). solve()'d via
    // active_decision_assumps() to get the current assumption set.
    std::vector<CMSat::Lit> decision_lits;

    // Current decision level. 0 = root level, where all commits are
    // permanent. >0 = inside a speculative decision context.
    uint32_t decision_lvl = 0;

    // --- algorithm pieces ---

    // Phase E: small-input SAT-model enumeration. Loads F + Tseitin
    // of any existing skol[y] commits into a fresh SAT solver, then
    // repeatedly solves and forbids the seen input pattern until
    // UNSAT. Per-undet-y value tables collect every model's y values;
    // a Shannon-decomposition tree builds each Skolem from its table
    // at the end. Runs whenever |orig_sampl_cnf| ≤ kSmallInputThreshold
    // (16), i.e. ≤ 65k SAT calls — faster per iter than Phase F at
    // that size because there's no uniqueness/minimization overhead.
    bool synth_complete_with_models();

    // Phase F: terminal SAT-model + UNSAT-core-generalize loop.
    // For each model M, ask minim under (sel + kept_input_lits)
    // whether joint undet Y must differ from M's value. On UNSAT,
    // the conflict core identifies the input bits required for
    // forcing — every other bit can be dropped from the case. On
    // joint-SAT (alternatives exist for Y at X*), fall back to
    // per-y uniqueness for small undet sets (cap kPerYUndetCap) and
    // commit individually-forced y's via single clauses.
    //
    // Soundness: the uniqueness check verifies that joint Y = M is
    // the ONLY joint Skolem over the (potentially exponential) kept
    // region, so committing that joint value over the region is
    // correct.
    //
    // Terminal completion guarantee: no input-size threshold, no
    // iter cap. Each iteration forbids a non-empty kept-input
    // region, so total iterations ≤ 2^|orig_sampl_cnf| — finite.
    // Phase F is what backs cadet's "always finishes" contract.
    //
    // Currently the wrapper forwards the full undet set / full
    // orig sampling space to synth_phase_f_subset() in one call.
    // An earlier per-component decomposition was reverted because
    // extend-defined vars' existing AIG defs transitively cross
    // component boundaries, breaking per-component soundness; the
    // worker remains parametrized so a future, correctly-merged
    // decomposition can wire it up per component.
    bool synth_complete_with_interp_generalization();

    // Phase F worker: run the SAT-model + UNSAT-core-generalize loop
    // on the supplied (sub_inputs, sub_undet) subset. Builds its own
    // sat and minim solvers, encoding the current skol[] state, then
    // enumerates over sub_inputs to fill in Skolems for sub_undet.
    // Returns true on convergence, false on UNDEF from the SAT solver
    // (never happens in practice — no hard SAT timeout is set).
    bool synth_phase_f_subset(const std::vector<uint32_t>& sub_inputs,
                              const std::vector<uint32_t>& sub_undet);

    // Phase C+D: incremental determinization (CADET's signature).
    //
    // Phase C — unique-consequence propagation. For each undetermined
    // to_define var y, iterate over the clauses mentioning y. When
    // every other literal in a clause is already a function of inputs /
    // earlier-determined vars, the clause forces y to a specific value
    // over the "forced region" (where all other literals are false).
    // Accumulating the positive-force region over all positive-y
    // clauses gives a candidate Skolem.
    //
    // Phase D — decisions. When Phase C reaches a fixpoint with vars
    // still undetermined, pick the undetermined var with the fewest
    // clauses (least-constrained = least likely to need a non-constant
    // function) and commit a constant Skolem chosen by SAT: try
    // y=false first, fall back to y=true if F+y=false is unsat under
    // the running solver state. This is CADET's "decision" step.
    //
    // What's MISSING vs full CADET: conflict analysis. Real CADET, on
    // an inconsistent decision, derives a learnt clause that prunes
    // the relevant input region and backtracks. Here we accept the
    // decision at face value and rely on:
    //   (a) the synthesis precondition (F satisfiable for every input)
    //       making most decisions sound,
    //   (b) the SAT-based test in Phase D rejecting decisions that
    //       are constant-unsat under the running state,
    //   (c) the per-commit cycle check from Phase C catching
    //       structural cycles,
    //   (d) Phase F (terminal) catching any remainder.
    //
    // Returns true iff every to_define var was determinized.
    bool synth_by_propagation();

    // Phase C unit step: try to commit skol[y] from its clauses.
    // Returns true if a commit happened (and tseitin'd it into
    // skolem_sat). dep_cache is shared across calls for amortization.
    bool try_propagate(uint32_t y,
                       std::map<uint32_t, std::vector<uint32_t>>& dep_cache,
                       const std::map<uint32_t, CMSat::Lit>& new_to_orig);

    // Build the set of "neighbour" vars for var v: every undet var
    // sharing at least one clause with v. Used to enqueue work after
    // a commit.
    void enqueue_neighbours(uint32_t v,
                            std::vector<uint8_t>& in_queue,
                            std::vector<uint32_t>& queue) const;

    // When skol[v] becomes a constant matching `val`, every clause
    // where v appears with that polarity is satisfied. Mark those
    // clauses dead so pure-literal detection can ignore them.
    void mark_clauses_dead_by_constant(uint32_t v, bool val);

    // Try a pure-literal commit on y: if every undead clause where y
    // appears has y positively (resp. negatively), committing y=true
    // (resp. false) satisfies all of them and so is sound. Returns
    // true if committed.
    bool try_pure_literal(uint32_t y);

    // Build a Skolem AIG from a value table by Shannon decomposition over
    // `sorted_inputs`. `table[mask]` is the y-value for the input
    // assignment whose bit i corresponds to sorted_inputs[i]. Identical
    // sibling subtrees collapse, so constants and pure-literal cases come
    // out at minimal cost.
    ArjunNS::aig_ptr build_shannon_tree(const std::vector<bool>& table,
                                        const std::vector<uint32_t>& sorted_inputs);

    // Inject the entire CNF into the given solver.
    template<typename S>
    void inject_cnf(S& s) const;

    // One-shot helper: inject F into `s`, allocate a known-true literal
    // (needed by AIGToCNF for constant nodes), and tseitin-encode every
    // already-committed skol[y] as `y ↔ root` clauses. Constant skols
    // become unit clauses. Returns the true-literal in `out_true_lit`.
    // Used by Phase E and Phase F when they need their own private
    // solver instance.
    void build_solver_with_skols(MetaSolver& s, CMSat::Lit& out_true_lit) const;

    // True-literal used by the persistent skolem_sat solver — allocated
    // once when skolem_sat is built. Needed for AIGToCNF encoding when
    // we add Phase C/D commits incrementally.
    CMSat::Lit skolem_sat_true_lit;

    // Add the tseitin encoding of skol[y] into skolem_sat. Called from
    // Phase C's commit site so the persistent solver immediately knows
    // about each new commit — subsequent Phase D probes then run under
    // F + (all prior skol[] commits), strictly stronger than F alone.
    void tseitin_skol_into_skolem_sat(uint32_t y);

    // Set defs[v] for every v in to_define from skol[v], via map_aigs_to_orig.
    void commit_definitions();
};

} // namespace ArjunInt
