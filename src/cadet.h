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

// CADET-style synthesis driver (Manthan API surface).
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

    // `input` includes extend-defined vars; `orig_sampl_cnf` is the
    // narrower set actually enumerated over.
    std::set<uint32_t> input;
    std::set<uint32_t> to_define;
    std::set<uint32_t> backward_defined;
    std::set<uint32_t> orig_sampl_cnf;

    // input + backward_defined get opaque leaves (AIG::new_lit). to_define
    // starts nullptr and gets filled by the algorithm.
    std::vector<ArjunNS::aig_ptr> skol;

    // Persistent skolem SAT solver — F injected once, incrementally fed
    // commits across Phase C+D.
    std::unique_ptr<MetaSolver> skolem_sat;

    // var → [(clause_idx, sign_of_lit)]. sign=true means the lit is ¬var.
    std::vector<std::vector<std::pair<uint32_t, bool>>> var_clauses;

    // Set when a clause is satisfied by some committed-constant skol[v].
    // Used by pure-literal detection.
    std::vector<uint8_t> clause_dead;

    // Fast pre-check for try_propagate: any clause with n_undet > 1
    // can't yet make y a unique consequence.
    std::vector<uint16_t> n_undet_per_clause;

    // VSIDS. JW-style clause-density seed; bump-up scheme (scale inc up
    // rather than scale activities down).
    std::vector<double> var_activity;
    double activity_inc = 1.0;
    double activity_decay = 0.95; // mconf-overridable, hence not constexpr
    static constexpr double kActivityRescaleThreshold = 1e100;

    void bump_var(uint32_t v);
    void decay_activities();
    void clause_undet_delta(uint32_t v, int delta);

    struct TrailEntry {
        uint32_t var;
        uint32_t dec_lvl;
        bool is_decision;
        CMSat::Lit decision_lit; // only meaningful when is_decision
        // Clauses killed via mark_clauses_dead_by_constant; un-killed on
        // backjump so pure-literal stays sound across speculative regions.
        std::vector<uint32_t> killed_clauses;
    };
    std::vector<TrailEntry> trail;

    std::vector<CMSat::Lit> decision_lits;

    // Per-level selector: commits at level d are gated by (¬sel_d ∨ lit).
    // Backjump permanently adds ¬sel_d so cadical can simplify them away.
    std::vector<CMSat::Lit> sel_lits;

    // PartialAssignment: pa_value[v] holds skol[v]'s constant (or
    // l_Undef). pa_reason[v] is the unit-propagating clause idx, or
    // PA_REASON_SOURCE for non-BCP commits. BCP only propagates Y vars;
    // propagating universals would falsely constrain ∀X.
    static constexpr uint32_t PA_REASON_SOURCE = UINT32_MAX;
    static constexpr uint32_t PA_NO_CONFLICT   = UINT32_MAX;

    std::vector<CMSat::lbool> pa_value;
    std::vector<uint32_t> pa_reason;
    std::vector<uint32_t> pa_level;
    std::vector<CMSat::Lit> pa_trail;
    std::vector<uint32_t> pa_bcp_queue;
    std::vector<uint8_t>  pa_bcp_in_queue;
    uint32_t pa_conflict_clause = PA_NO_CONFLICT;

    uint64_t pa_propagations    = 0;
    uint64_t pa_conflicts_caught = 0;

    void pa_init();
    // Idempotent on equal-value re-assignment; sets pa_conflict_clause
    // on contradictory re-assignment.
    void pa_assign(uint32_t v, bool val, uint32_t reason);
    // Pop assignments at levels > target; clears the conflict flag.
    void pa_pop_to_level(uint32_t target);
    CMSat::lbool pa_lit_value(CMSat::Lit lit) const;
    void pa_enqueue_clauses_for_var(uint32_t v);
    // Auto-commits unit Y vars at current dec_lvl. Returns false on
    // conflict (pa_conflict_clause set).
    bool pa_drain_bcp(std::vector<uint8_t>& outer_in_queue,
                      std::vector<uint32_t>& outer_neighbour_queue);

    // 1-UIP over the PA implication graph. Synthetic-resolves non-
    // decision PA_REASON_SOURCE lits at conflict_dlvl via "implied by
    // all decisions ≤ d" so the learnt clause has exactly one lit at
    // conflict_dlvl. Returns false on level-0 conflict.
    bool handle_pa_conflict_1uip(std::vector<uint8_t>& outer_in_queue,
                                 std::vector<uint32_t>& outer_neighbour_queue);
    uint64_t uip_conflicts_handled = 0;
    uint64_t uip_learnt_lits_total = 0;
    uint64_t uip_strict_decision_terminations = 0;
    uint64_t uip_strict_synthetic_resolves = 0;

    // Sörensson-Biere recursive minimization; runs before backjump.
    void minimize_learnt_recursive(std::vector<CMSat::Lit>& learnt);
    uint64_t uip_min_in_lits = 0;
    uint64_t uip_min_out_lits = 0;

    // Two-sided Skolem (upstream skolem_var pos_lit/neg_lit). Per Y,
    // add sufficient-direction clause (¬pos_var[y] → some non-y lit
    // of each pos-y clause is true). Then ¬pos_var[y] UNSAT under
    // sel_lits ⇔ y forced TRUE universally; symmetric for neg.
    std::vector<CMSat::Lit> pos_var;
    std::vector<CMSat::Lit> neg_var;
    static constexpr uint32_t TWO_SIDED_INVALID_VAR = UINT32_MAX;

    // Rebuild on every fresh skolem_sat (including replenish).
    void two_sided_build(MetaSolver& solver);
    uint64_t two_sided_pos_unsat = 0;
    uint64_t two_sided_neg_unsat = 0;

    // Learnt clauses over original vars (no selectors); replayed into
    // Phase E/F's solvers on setup.
    std::vector<std::vector<CMSat::Lit>> learnt_clauses;

    uint64_t clause_min_total_in_lits = 0;
    uint64_t clause_min_total_out_lits = 0;
    uint64_t clause_min_resolves = 0;
    uint64_t clause_min_drops = 0;

    // Drop selectors from `kept` via re-solves; single pass, descending
    // dlvl. No-op when |kept| ≤ cadet_clause_min_size_floor.
    void minimize_failed_selectors(std::set<uint32_t>& kept);

    uint32_t decision_lvl = 0;

    std::vector<CMSat::Lit> active_assumps() const;

    // Undo trail entries with dec_lvl > target; add ¬sel_d for each
    // removed level so cadical can purge selector-gated clauses.
    void backjump_to_level(uint32_t target);

    void make_decision(uint32_t v, bool val);

    // Phase E: enumerate SAT models over orig_sampl_cnf, build per-y
    // Shannon trees. Only runs when |orig_sampl_cnf| ≤ threshold.
    bool synth_complete_with_models();

    // Phase F: terminal SAT-model + UNSAT-core-generalize loop. No
    // input-size threshold, no iter cap; ≤ 2^|orig_sampl_cnf| iters.
    // Joint-UNSAT iters drop bits via the core; joint-SAT iters fall
    // back to per-y uniqueness (capped). Per-component decomposition
    // was unsound (extend-defined vars cross components); the worker
    // is kept parametrized for a future correct version.
    bool synth_complete_with_interp_generalization();

    bool synth_phase_f_subset(const std::vector<uint32_t>& sub_inputs,
                              const std::vector<uint32_t>& sub_undet);

    // Phase C+D: unique-consequence + pure-literal propagation, then
    // forced-constant probes (two-sided) and speculative CDCL guesses
    // gated by selectors. Geometric restarts; ratify-or-rollback at
    // end. Returns true iff every to_define var was determinized at
    // level 0.
    bool synth_by_propagation();

    bool try_propagate(uint32_t y,
                       std::map<uint32_t, std::vector<uint32_t>>& dep_cache,
                       const std::map<uint32_t, CMSat::Lit>& new_to_orig);

    void enqueue_neighbours(uint32_t v,
                            std::vector<uint8_t>& in_queue,
                            std::vector<uint32_t>& queue) const;

    void mark_clauses_dead_by_constant(uint32_t v, bool val);

    bool try_pure_literal(uint32_t y);

    // Shannon decomposition over sorted_inputs; collapses identical
    // sibling subtrees.
    ArjunNS::aig_ptr build_shannon_tree(const std::vector<bool>& table,
                                        const std::vector<uint32_t>& sorted_inputs);

    template<typename S>
    void inject_cnf(S& s) const;

    // Inject F + allocate true-lit + tseitin-encode every committed
    // skol[y]. Used by Phase E/F for their private solvers.
    void build_solver_with_skols(MetaSolver& s, CMSat::Lit& out_true_lit) const;

    CMSat::Lit skolem_sat_true_lit;

    void tseitin_skol_into_skolem_sat(uint32_t y);

    // Rebuild skolem_sat from F + level-0 skol[] commits + learnt_
    // clauses to shed Tseitin bloat. Level-0 only.
    void maybe_replenish_skolem_sat();

    // For each level d, probe ¬decision_lit_d under sel[0..d-2];
    // UNSAT ⇒ promote sel_d to unit (move level to 0). Stops at first
    // SAT. Returns number ratified.
    uint32_t ratify_speculative_decisions();
    uint32_t total_ratified = 0;
    uint32_t skolem_sat_commits_since_build = 0;
    uint32_t skolem_sat_replenishes = 0;

    void commit_definitions();

    // CEGAR companion at level-0 stalls: solve skolem_sat for a model M,
    // assume the universal cube in a 2nd solver under "∃ undet y ≠ M[y]";
    // UNSAT → drop non-core cube bits, commit Y=M (or per-y commit).

    // orig_sampl_cnf vars co-occurring with a to_define var. Sorted.
    std::vector<uint32_t> cegar_interface;

    // F + Tseitin of all level-0 skols. Lazily built.
    std::unique_ptr<MetaSolver> exists_solver;
    CMSat::Lit exists_solver_true_lit;
    uint32_t exists_solver_committed_count = 0;
    std::vector<uint8_t> exists_solver_encoded;
    uint32_t cegar_total_rounds = 0;
    uint64_t cegar_per_y_checks = 0;
    uint64_t cegar_per_y_commits = 0;
    bool cegar_per_y_disabled = false;
    // Set after N rounds with no constant commit; sticky until end of
    // Phase D.
    bool cegar_disabled = false;
    uint64_t cegar_stat_rounds = 0;
    uint64_t cegar_stat_joint_unsat = 0;
    uint64_t cegar_stat_joint_sat = 0;
    uint64_t cegar_stat_joint_undef = 0;
    uint64_t cegar_stat_cube_total = 0;
    uint64_t cegar_stat_joint_commits = 0;
    uint64_t cegar_stat_per_y_commits = 0;
    // Selectors for forbid-on-SAT clauses. Assumed only during CEGAR's
    // own skolem_sat solve — NEVER during Phase D probes or the global
    // conflict check (load-bearing: would falsely commit y under an
    // artificially-restricted X space).
    std::vector<CMSat::Lit> cegar_forbid_selectors;

    void cegar_build_interface();
    void cegar_build_exists_solver();
    void cegar_sync_exists_solver();
    // constant_commit: true iff some skol[y] flipped to a level-0 const.
    // any_clause_added: looser — clauses-only progress also counts.
    // kept_cube_size: joint-UNSAT kept cube size (UINT32_MAX otherwise).
    struct CegarRoundResult {
        bool constant_commit = false;
        bool any_clause_added = false;
        uint32_t kept_cube_size = UINT32_MAX;
    };
    CegarRoundResult cegar_one_round(std::vector<uint8_t>& in_queue,
                                     std::vector<uint32_t>& queue);
    // Round-cap, avg-cube, and consec-no-progress bails.
    bool cegar_drain_at_level_0(std::vector<uint8_t>& in_queue,
                                std::vector<uint32_t>& queue);
};

} // namespace ArjunInt
