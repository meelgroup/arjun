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

    // n_undet_per_clause[ci] = count of lits in clause ci whose var
    // still has skol[v] == nullptr. Initialised to clause length, then
    // decremented on every commit and incremented on every backjump.
    // try_propagate uses it as a fast pre-check: if ANY clause
    // containing y has n_undet > 1, y is not yet a unique consequence
    // and we can skip the per-clause AIG-build pass. Avoids the
    // O(|y_clauses| · avg_clause_len) inner walk on the common case
    // where some neighbour is still undet. Cadet's analogue is the
    // unique_consequence[]/clauses_to_check pair in skolem.c.
    std::vector<uint16_t> n_undet_per_clause;

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
    // VSIDS multiplicative-decay factor (per decay step). Default 0.95;
    // overridable via mconf.cadet_activity_decay. NOT constexpr so that
    // mconf can override it at construction time.
    double activity_decay = 0.95;
    static constexpr double kActivityRescaleThreshold = 1e100;

    void bump_var(uint32_t v);
    void decay_activities();

    // Adjust n_undet_per_clause for every clause containing v by
    // `delta` (typically -1 on commit, +1 on backjump). Cheap O(|v's
    // clauses|).
    void clause_undet_delta(uint32_t v, int delta);

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
        // Clauses that this commit killed via
        // mark_clauses_dead_by_constant. On backjump we un-kill them
        // so pure-literal stays sound across speculative regions.
        std::vector<uint32_t> killed_clauses;
    };
    std::vector<TrailEntry> trail;

    // Stack of decision lits, indexed by decision level (entry d is
    // the assumption literal for level d+1). solve()'d via
    // active_decision_assumps() to get the current assumption set.
    std::vector<CMSat::Lit> decision_lits;

    // Per-decision-level selector var (level d → sel_lits[d-1]). When
    // we commit a tentative constant at level d, we add it as
    // (¬sel_d ∨ lit_val) so deactivating sel_d makes the clause
    // trivially satisfied. On backjump from d to t, we permanently
    // add {¬sel_d} for each killed level d > t so cadical can simplify
    // those clauses away.
    std::vector<CMSat::Lit> sel_lits;

    // === Partial Assignment domain (internal BCP propagator) =========
    //
    // For every CNF var v with skol[v] committed to a CONSTANT,
    // pa_value[v] holds that constant. For everything else (X
    // universals, Y vars with non-const skol, Y vars not yet
    // committed), pa_value[v] = l_Undef. Mirrors upstream's
    // PartialAssignment (cadet/src/partial_assignment.c).
    //
    // pa_reason[v] is the clause idx (into cnf.get_clauses()) that
    // forced v's value during BCP; PA_REASON_SOURCE marks an
    // assignment that came from outside BCP (decision, Phase C
    // pos_force commit, CEGAR commit, pure literal). pa_level[v] is
    // the dec_lvl at assignment time.
    //
    // BCP propagates Y vars only — universals are never assigned
    // (would falsely constrain ∀X). When a clause becomes unit and the
    // sole unassigned lit's var is in to_define, the var is auto-
    // committed as a constant at the current dec_lvl.
    //
    // Used by 1-UIP conflict analysis and recursive learnt-clause
    // minimization (upcoming passes).
    static constexpr uint32_t PA_REASON_SOURCE = UINT32_MAX;
    static constexpr uint32_t PA_NO_CONFLICT   = UINT32_MAX;

    std::vector<CMSat::lbool> pa_value;
    std::vector<uint32_t> pa_reason;
    std::vector<uint32_t> pa_level;
    std::vector<CMSat::Lit> pa_trail;
    std::vector<uint32_t> pa_bcp_queue;
    std::vector<uint8_t>  pa_bcp_in_queue;
    uint32_t pa_conflict_clause = PA_NO_CONFLICT;

    uint64_t pa_propagations    = 0;  // # auto-commits via BCP
    uint64_t pa_conflicts_caught = 0; // # BCP-detected conflicts

    // Init PA arrays. Sized to cnf.nVars(); all entries l_Undef.
    void pa_init();
    // Record an assignment at the current decision_lvl. reason =
    // clause idx, or PA_REASON_SOURCE. Idempotent on equal-value
    // re-assignment; sets pa_conflict_clause on contradictory
    // re-assignment.
    void pa_assign(uint32_t v, bool val, uint32_t reason);
    // Pop PA assignments made at levels > target. Companion to
    // backjump_to_level; clears the conflict flag.
    void pa_pop_to_level(uint32_t target);
    // Look up lit's value under PA: l_True if PA satisfies lit,
    // l_False if PA falsifies it, l_Undef if v unassigned.
    CMSat::lbool pa_lit_value(CMSat::Lit lit) const;
    // Enqueue every clause containing var v for BCP recheck. Called
    // after v gets pa-assigned.
    void pa_enqueue_clauses_for_var(uint32_t v);
    // Drain the BCP worklist. Auto-commits Y units (skol[] becomes a
    // constant, all bookkeeping updated). Stops on PA conflict; sets
    // pa_conflict_clause and returns false. Outer queues are bumped
    // for every auto-commit so Phase C/D's neighbour-driven
    // propagation picks up the new state.
    bool pa_drain_bcp(std::vector<uint8_t>& outer_in_queue,
                      std::vector<uint32_t>& outer_neighbour_queue);

    // 1-UIP-style conflict analysis over the PA implication graph.
    // Called when pa_conflict_clause != PA_NO_CONFLICT. Walks back
    // through pa_reason, resolves clause reasons until only sources
    // (PA_REASON_SOURCE) remain at the conflict's decision level, and
    // builds a learnt clause. The learnt clause is added to skolem_sat
    // and learnt_clauses; backjump_to_level(second_highest_lvl) pops
    // the speculative stack. Returns false on level-0 conflict (caller
    // should bail to Phase E/F).
    //
    // Note: non-strict 1-UIP — when multiple sources appear at the
    // conflict level (e.g. a Phase D decision plus one or more Phase D
    // forced commits / Phase C propagations at the same level, all
    // PA_REASON_SOURCE), every source becomes a learnt-clause lit at
    // that level. Sound, slightly weaker than upstream's strict 1-UIP
    // (which would need synthetic resolution chains for non-decision
    // sources). A future tightening can plug those in.
    bool handle_pa_conflict_1uip(std::vector<uint8_t>& outer_in_queue,
                                 std::vector<uint32_t>& outer_neighbour_queue);
    uint64_t uip_conflicts_handled = 0;
    uint64_t uip_learnt_lits_total = 0;

    // CDCL-learnt clauses over original variables (no selectors).
    // Each conflict produces one entry — the negation of the failed
    // decision lits, i.e. a clause that refutes that combination of
    // decisions across all inputs. Sound to inject into any solver
    // that has F over the same vars; Phase E and Phase F do that on
    // setup so they benefit from work done in Phase C+D.
    std::vector<std::vector<CMSat::Lit>> learnt_clauses;

    // Counters for the Phase D conflict-clause minimization pass.
    // Reported in the Phase C+D summary; useful for tuning the
    // --cadetclausemin* knobs.
    uint64_t clause_min_total_in_lits = 0;
    uint64_t clause_min_total_out_lits = 0;
    uint64_t clause_min_resolves = 0;
    uint64_t clause_min_drops = 0;

    // Try to drop each selector from `kept` via a re-solve. On success
    // refresh `kept` from the new failed-assumption core (cadical may
    // tighten it further on its own). Single-pass, descending dlvl
    // order. `kept` on entry holds the var-ids of the failed selectors;
    // on return it holds the strengthened subset. Caller maps back to
    // decision_lits. No-op when |kept| ≤ cadet_clause_min_size_floor.
    void minimize_failed_selectors(std::set<uint32_t>& kept);

    // Current decision level. 0 = root level, where all commits are
    // permanent. >0 = inside a speculative decision context.
    uint32_t decision_lvl = 0;

    // Build the list of currently-active selector lits to be assumed in
    // Phase D probes / Phase C downstream checks. Returns sel_lits[0..d-1].
    std::vector<CMSat::Lit> active_assumps() const;

    // Undo trail entries with dec_lvl > target and revert their skol[]
    // slots. Drops decision lits and selectors above target.
    // Permanently kills (¬sel_d) for each removed level so cadical
    // can purge selector-gated clauses on its next simplification.
    void backjump_to_level(uint32_t target);

    // Make a fresh guess decision: pick var v with polarity val,
    // increment decision_lvl, allocate a selector, add the gated
    // decision clause {¬sel_d, (v=val)} to skolem_sat, and record
    // the commit on the trail. Tentative: backjumpable.
    void make_decision(uint32_t v, bool val);

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

    // Phase C+D: incremental determinization with CDCL (CADET's
    // signature).
    //
    // Phase C — unique-consequence propagation. For each undetermined
    // to_define var y, walk its clauses; when every non-y literal is
    // already a function of earlier-determined vars, the clause forces
    // y over its "negated-other-literals" region. Accumulating those
    // regions over the positive-y clauses gives a candidate Skolem. A
    // worklist re-checks only neighbours after each commit. Pure-
    // literal applies whenever every undead clause containing y has
    // y in one polarity (committing it then satisfies the alive
    // clauses).
    //
    // Phase D — sound forced-constant decisions + CDCL guesses.
    // Forced step: VSIDS-ordered scan of undet vars; assume y=true,
    // and if UNSAT under current state, commit y=false (vice versa).
    // When forced-only runs out, optionally make a speculative guess
    // at a fresh decision level, gated by a selector. Subsequent
    // commits at that level are also gated. A global conflict check
    // (solve under active selectors) detects when F + decisions is
    // UNSAT; the failed-assumption core maps back to decision lits,
    // and the learnt clause = OR(~decision_lits in core) gets added
    // permanently to skolem_sat (and to learnt_clauses for Phase E/F
    // to replay). Backjump to the second-highest level in the core.
    //
    // VSIDS-bumps come from failed-assumption cores in Phase D's
    // forced probes, Phase F's joint and per-y UNSAT cores, plus
    // small bumps on every Phase C commit. JW-style seed initialises
    // activity from clause density.
    //
    // Geometric restart: after K conflicts the speculative tree is
    // discarded (learnt clauses survive). K starts at 16, grows by
    // 1.5× per restart. Hard guess-depth cap (8) bounds search depth.
    //
    // Returns true iff every to_define var was determinized at level 0.
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

    // Periodic skolem_sat replenish. Discards the accumulated Tseitin
    // bloat by rebuilding skolem_sat from F + current level-0 skol[]
    // commits + learnt_clauses. Called only at decision_lvl == 0, so
    // sel_lits / decision_lits do not need to be re-created. Returns
    // immediately if `cadet_skolem_sat_replenish_every` is 0 or the
    // commit count is below the threshold.
    void maybe_replenish_skolem_sat();

    // Try to ratify speculative decisions at the END of Phase D before
    // unconditionally rolling back to level 0. For each level d from 1
    // upward, probe skolem_sat under (sel[0..d-2] + ¬decision_lit_d).
    // UNSAT ⇒ the decision is F-implied under prior selectors —
    // typically because new learnt clauses arrived after the guess.
    // Promote sel_d to a unit clause (effectively moving the level to
    // 0) and keep its trail entries. On the first SAT, stop trying
    // higher levels and backjump them. Returns the number of levels
    // ratified.
    uint32_t ratify_speculative_decisions();
    uint32_t total_ratified = 0;
    // Number of level-0 commits added to skolem_sat since the last
    // build/replenish. Bumped in tseitin_skol_into_skolem_sat for the
    // level-0 path; reset by maybe_replenish_skolem_sat on rebuild.
    uint32_t skolem_sat_commits_since_build = 0;
    // Total replenishes done in this Phase D entry — printed in the
    // summary.
    uint32_t skolem_sat_replenishes = 0;

    // Set defs[v] for every v in to_define from skol[v], via map_aigs_to_orig.
    void commit_definitions();

    // === CEGAR refinement layer (Phase D companion) ====================
    //
    // CEGAR adds an UNSAT-core-driven cube-shrinking step that runs
    // between Phase D's forced-only pass and its speculative guess.
    // For each round:
    //   1. Solve skolem_sat under active selectors to get a SAT model.
    //   2. Read off the universal cube = (interface_var_values from the
    //      model). The "interface" is the precomputed set of orig
    //      sampling vars that actually co-occur with any to_define var
    //      in a clause; vars outside it are independent and can't
    //      affect uniqueness of undet y. Mirrors cadet's
    //      casesplits_update_interface() (casesplits.c:81).
    //   3. Probe a SECOND solver (exists_solver) with (sel +
    //      "∃ still-undet y differs from M[y]") + the cube assumed.
    //   4. UNSAT means the cube forces joint Y = M; the failed-
    //      assumption core tells us which cube bits were load-bearing
    //      (the rest can be dropped — same one-shot generalization
    //      Phase F uses). Commit Y = M as a permanent blocking clause
    //      over the kept cube.
    //   5. (Optional) Per-y CEGAR: for each undet y, ask "is y alone
    //      forced under the kept cube?" via the same trick.
    //
    // Effect: shrinks the universal search space Phase F must later
    // cover, often eliminating it on Phase-D-bottlenecked runs.

    // Interface vars: orig_sampl_cnf vars that share a clause with at
    // least one to_define var. Computed once in do_cadet() after
    // var_clauses is built; used by CEGAR rounds. Sorted ascending.
    std::vector<uint32_t> cegar_interface;

    // Second SAT solver instance for CEGAR: F + Tseitin of all
    // level-0 committed skols. Built lazily on the first CEGAR call.
    // exists_solver_true_lit is its always-true literal (allocated at
    // build time, used by AIGToCNF for constant nodes).
    std::unique_ptr<MetaSolver> exists_solver;
    CMSat::Lit exists_solver_true_lit;
    // Number of level-0 skol[] commits already Tseitin-encoded into
    // exists_solver. When the running count of level-0 commits exceeds
    // this, the new ones are encoded incrementally before the next
    // CEGAR round. Used so we don't re-encode the whole skol[] table
    // every round.
    uint32_t exists_solver_committed_count = 0;
    // Per-var flag: is skol[v] already Tseitin-encoded into the current
    // exists_solver? Reset on rebuild. Used by cegar_sync_exists_solver
    // to find newly-committed (since last sync) level-0 entries.
    std::vector<uint8_t> exists_solver_encoded;
    // Per-Phase-D-entry running count of total CEGAR rounds executed,
    // for the --cadetcegarmaxtot cap. Reset at the start of
    // synth_by_propagation().
    uint32_t cegar_total_rounds = 0;
    // Per-y CEGAR adaptive disable state. Counts only ratify across
    // rounds. Once disabled, stays disabled for the rest of the
    // Phase D entry.
    uint64_t cegar_per_y_checks = 0;
    uint64_t cegar_per_y_commits = 0;
    bool cegar_per_y_disabled = false;
    // Outer CEGAR disable. Set when the drain has run for at least
    // mconf.cadet_cegar_overall_disable_after rounds across all stalls
    // without producing any *constant* commits (the per-y commits are
    // only constraint clauses; useful but they don't shrink the undet
    // set). Once disabled, cegar_drain_at_level_0 returns false
    // immediately for the rest of the Phase D entry.
    bool cegar_disabled = false;
    // Stats across the Phase D entry (reset at the top of
    // synth_by_propagation). Printed in the Phase C+D summary.
    uint64_t cegar_stat_rounds = 0;       // CEGAR rounds attempted
    uint64_t cegar_stat_joint_unsat = 0;  // UNSAT (cube forces joint Y=M)
    uint64_t cegar_stat_joint_sat = 0;    // SAT  (joint Y has alternatives)
    uint64_t cegar_stat_joint_undef = 0;  // UNDEF
    uint64_t cegar_stat_cube_total = 0;   // sum of kept cube sizes
    uint64_t cegar_stat_joint_commits = 0;// joint-Y commits (one per UNSAT round)
    uint64_t cegar_stat_per_y_commits = 0;// per-y commits within rounds
    // Selector lits for forbid-on-SAT clauses added to skolem_sat. Each
    // entry is the positive selector for a forbid clause `(¬sel ∨ ¬cube)`
    // that excludes one previously-explored X-cube from CEGAR's M
    // generation. CEGAR's level-0 solve of skolem_sat passes these as
    // assumptions (so the forbids are active there). Phase D's polarity
    // probes and the CDCL global-conflict check do NOT pass them, so the
    // forbids stay inactive there — this is load-bearing for soundness:
    // a probe under an artificially-restricted X space could falsely
    // conclude that y is universally forced.
    std::vector<CMSat::Lit> cegar_forbid_selectors;

    // Compute cegar_interface — single pass over var_clauses. Cheap.
    void cegar_build_interface();
    // (Re)build exists_solver. Called lazily on first CEGAR round, or
    // when --cadetcegarrebuildevery commits have accumulated since the
    // last build.
    void cegar_build_exists_solver();
    // Bring exists_solver up-to-date with any level-0 skol[] commits
    // made since the last sync. No-op if nothing new committed.
    void cegar_sync_exists_solver();
    // Result of one CEGAR round. `constant_commit` is the headline
    // signal — it's true iff at least one undet y had skol[y] flipped
    // from nullptr to a permanent AIG constant this round (whether via
    // an empty joint cube or an empty per-y cube). The driver uses
    // this to decide whether real undet-set-shrinking progress is
    // happening, vs only clause-additions that constrain skolem_sat
    // without committing.
    //
    // `any_clause_added` is true iff we either committed a constant OR
    // added one of the non-empty-cube implication clauses to
    // skolem_sat. It's looser than `constant_commit`; the driver uses
    // it to detect the "joint SAT + no per-y commit" stall (both
    // false) for the consec_no_progress bail.
    //
    // `kept_cube_size` is the surviving joint kept-cube size when
    // joint-UNSAT, or UINT32_MAX otherwise; driver uses it for the
    // average-cube effectiveness break.
    struct CegarRoundResult {
        bool constant_commit = false;
        bool any_clause_added = false;
        uint32_t kept_cube_size = UINT32_MAX;
    };
    // Try one CEGAR round. See CegarRoundResult.
    CegarRoundResult cegar_one_round(std::vector<uint8_t>& in_queue,
                                     std::vector<uint32_t>& queue);
    // Per-stall driver: call cegar_one_round repeatedly until either
    // (a) a round commits something (caller re-runs propagation), or
    // (b) the per-stall round cap is hit, or
    // (c) the trailing avg kept-cube-size exceeds the effectiveness
    //     threshold (cube minimization isn't biting), or
    // (d) a round returns false (joint SAT + no per-y commit) twice in
    //     a row (no progress in sight). Returns true iff any commits
    //     were made across the drain.
    bool cegar_drain_at_level_0(std::vector<uint8_t>& in_queue,
                                std::vector<uint32_t>& queue);
};

} // namespace ArjunInt
