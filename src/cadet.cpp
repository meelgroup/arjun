/*
 Arjun

 cadet.cpp — In-tree port of CADET's incremental-determinization core
 (Markus N. Rabe, SAT 2016). Used in place of Manthan when --cadet 1 is
 set. Always finishes synthesis alone — no Manthan fallback.

 Algorithm overview
 ==================
 CADET solves 2QBF formulas ∀X. ∃Y. φ(X, Y) by constructing a Skolem
 function for every existential variable in Y. The Skolem function for
 y ∈ Y is a Boolean function f_y(X) such that ∀X. φ(X, f_y(X), …) holds
 — i.e. plugging the Skolem functions into φ yields a tautology over X.

 CADET builds Skolem functions incrementally rather than guessing them
 up-front (as Manthan does). It uses a SAT solver to detect when an
 existential variable's value is *forced* by F given the partial
 Skolem functions built so far ("unique consequence" propagation),
 and falls back to SAT-model-driven case construction when propagation
 stops.

 Phases (current implementation)
 ===============================
   Phase C — worklist-driven unique-consequence + pure-literal
   propagation. When a clause's non-y literals are all functions of
   earlier-determined vars, y is forced over its "negated-other-
   literals" region. Pure-literal commits y to whichever polarity
   satisfies all of y's surviving (undead) clauses. Every commit
   re-enqueues only its undet neighbours — no full-table scans.
   skol[] is updated AND the commit is tseitin-encoded into the
   persistent skolem_sat (gated by the current decision level's
   selector when at decision_lvl > 0).

   Phase D — sound forced commits via SAT probes, plus speculative
   CDCL guesses. The forced step picks undet vars in VSIDS order and
   probes both polarities under active selector assumptions; a UNSAT
   polarity becomes a permanent (or selector-gated) commit. When
   forced-only stalls, a guess opens a fresh decision level with a
   selector and a gated decision clause. A global conflict check at
   the start of each pass spots when F+decisions is UNSAT; the
   failed-assumption core gets mapped back to decision lits, the
   learnt clause is added permanently (plus stashed for Phase E/F),
   and backjumping pops the trail to the second-highest level.
   Geometric restart (initial K=16, ×1.5 per restart) keeps the
   speculative tree from compounding.

   Phase E — small-input SAT-model enumeration. When |orig_sampl| ≤
   16, repeatedly solve F+Tseitin(prior commits)+CDCL learnt clauses
   under "forbid seen inputs"; collect each model's undet y values
   into a per-y table; build Shannon trees at the end.

   Phase F — terminal: SAT-model + UNSAT-core generalization with
   per-y uniqueness fallback. VSIDS-ordered per-y scan, bumps from
   joint and per-y cores. No input-size threshold, no iter cap. Each
   iter either drops bits via the joint UNSAT core or, on joint-SAT,
   falls back to per-y uniqueness (capped at 30 undet vars). Total
   iter count ≤ 2^|orig_sampl_cnf| — finite. Phase F is what backs
   cadet's "always finishes" contract.

 SAT infrastructure
 ==================
   A single persistent MetaSolver(cadical) — skolem_sat — is built
   once with F and incrementally fed every Phase C/D commit
   (constants directly, AIGs via AIGToCNF). Phase D's polarity
   probes and the CDCL global-conflict check use it. Phase E and
   Phase F each build a private solver via build_solver_with_skols(),
   which also replays the CDCL learnt_clauses.

 Copyright (c) 2026, Mate Soos. All rights reserved.
*/

#include "cadet.h"

#include "arjun.h"
#include "constants.h"
#include "metasolver.h"
#include "aig_to_cnf.h"
#include "time_mem.h"

#include <cryptominisat5/solvertypesmini.h>

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <set>
#include <unordered_map>
#include <vector>

using std::cout;
using std::endl;
using std::set;
using std::vector;
using std::setprecision;
using std::fixed;

using ArjunNS::AIG;
using ArjunNS::AIGT;
using ArjunNS::aig_ptr;
using ArjunNS::aig_lit;
using ArjunNS::SimplifiedCNF;
using ArjunNS::VarTypes;
using CMSat::Lit;
using CMSat::lbool;

namespace ArjunInt {

// Threshold for Phase E's exhaustive enumeration. 2^16 = 65536 SAT calls
// is the wall-time upper bound we're willing to spend per benchmark on
// Phase E's naive enumeration. For anything larger Phase F (terminal,
// no input-size threshold) takes over.
static constexpr uint32_t kSmallInputThreshold = 16;

Cadet::Cadet(const ArjunInt::Config& _conf,
             const ArjunNS::Arjun::ManthanConf& _mconf,
             ArjunNS::SimplifiedCNF&& _cnf)
    : conf(_conf), mconf(_mconf), cnf(std::move(_cnf))
{
    (void)mconf; // kept for API parity with Manthan's constructor;
                 // none of the Manthan-specific knobs apply to cadet.
}

template<typename S>
void Cadet::inject_cnf(S& s) const {
    s.new_vars(cnf.nVars());
    for (const auto& c : cnf.get_clauses()) s.add_clause(c);
    for (const auto& c : cnf.get_red_clauses()) s.add_red_clause(c);
}

void Cadet::make_decision(uint32_t v, bool val) {
    assert(skol[v] == nullptr);
    // Allocate fresh selector. sel_d active ⇒ decision in force.
    skolem_sat->new_var();
    const Lit sel(skolem_sat->nVars() - 1, /*sign=*/false);
    sel_lits.push_back(sel);

    // Decision lit: y=val. For val=true: Lit(v, sign=false). For
    // val=false: Lit(v, sign=true).
    const Lit dlit(v, /*sign=*/!val);
    decision_lits.push_back(dlit);
    decision_lvl++;

    // Gated decision clause: (¬sel_d ∨ dlit). When sel_d assumed,
    // dlit must hold.
    skolem_sat->add_clause({~sel, dlit});

    // Commit skol[v] to the constant and trail it as a decision.
    skol[v] = AIG::new_const(val);
    trail.push_back({v, decision_lvl, /*is_decision=*/true, dlit, {}});
    mark_clauses_dead_by_constant(v, val);
}

std::vector<Lit> Cadet::active_assumps() const {
    // Return [sel_lits[0], ..., sel_lits[decision_lvl-1]] —
    // assumption list that activates all currently-live decision levels.
    return std::vector<Lit>(sel_lits.begin(),
                            sel_lits.begin() + decision_lvl);
}

void Cadet::backjump_to_level(uint32_t target) {
    assert(target <= decision_lvl);
    if (target == decision_lvl) return;
    // Pop trail entries committed at levels > target. Reset their
    // skol[] slots and un-kill their clauses.
    while (!trail.empty() && trail.back().dec_lvl > target) {
        auto& te = trail.back();
        for (uint32_t ci : te.killed_clauses) clause_dead[ci] = 0;
        skol[te.var] = nullptr;
        trail.pop_back();
    }
    // Permanently kill selector vars for levels (target, decision_lvl].
    // After ¬sel_d is added, cadical can simplify away every level-d
    // clause on its next garbage collection.
    for (uint32_t d = target + 1; d <= decision_lvl; d++) {
        const Lit sl = sel_lits[d - 1];
        skolem_sat->add_clause({~sl});
    }
    decision_lits.resize(target);
    sel_lits.resize(target);
    decision_lvl = target;
}

void Cadet::bump_var(uint32_t v) {
    assert(v < var_activity.size());
    var_activity[v] += activity_inc;
    if (var_activity[v] > kActivityRescaleThreshold) {
        // Rescale all activities to avoid double overflow.
        const double inv = 1.0 / kActivityRescaleThreshold;
        for (auto& a : var_activity) a *= inv;
        activity_inc *= inv;
    }
}

void Cadet::decay_activities() {
    // Multiplicative decay: scale the bump-increment UP by 1/decay
    // each time, equivalent to scaling all activities DOWN by decay.
    // O(1) per decay step.
    activity_inc *= (1.0 / kActivityDecay);
    if (activity_inc > kActivityRescaleThreshold) {
        const double inv = 1.0 / kActivityRescaleThreshold;
        for (auto& a : var_activity) a *= inv;
        activity_inc *= inv;
    }
}

void Cadet::tseitin_skol_into_skolem_sat(uint32_t y) {
    // Communicate skol[y] to the persistent SAT solver. At level 0
    // commits are permanent. At decision_lvl > 0 we ONLY gate
    // constants under sel_d (so backjump can kill them); non-constant
    // pos_force AIGs are left in skol[] only, since selector-gating
    // every clause produced by AIGToCNF would require a wrapper —
    // future work.
    assert(skolem_sat != nullptr);
    assert(skol[y] != nullptr);
    const bool gated = (decision_lvl > 0);
    if (skol[y]->type == AIGT::t_const) {
        const bool val = !skol[y].neg;
        if (gated) {
            const Lit sel = sel_lits[decision_lvl - 1];
            skolem_sat->add_clause({~sel, Lit(y, /*sign=*/!val)});
        } else {
            skolem_sat->add_clause({Lit(y, /*sign=*/!val)});
        }
        return;
    }
    if (gated) return; // non-constant level>0 commits: skol[] only
    using AIGEnc = ArjunNS::AIGToCNF<MetaSolver>;
    AIGEnc enc(*skolem_sat);
    enc.set_true_lit(skolem_sat_true_lit);
    const Lit root = enc.encode(skol[y]);
    skolem_sat->add_clause({~Lit(y, /*sign=*/false), root});
    skolem_sat->add_clause({Lit(y, /*sign=*/false), ~root});
}

void Cadet::build_solver_with_skols(MetaSolver& s, Lit& out_true_lit) const {
    inject_cnf(s);
    s.new_var();
    const uint32_t tv = s.nVars() - 1;
    out_true_lit = Lit(tv, /*sign=*/false);
    s.add_clause({out_true_lit});
    using AIGEnc = ArjunNS::AIGToCNF<MetaSolver>;
    AIGEnc enc(s);
    enc.set_true_lit(out_true_lit);
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) continue;
        if (skol[y]->type == AIGT::t_const) {
            const bool val = !skol[y].neg;
            s.add_clause({Lit(y, /*sign=*/!val)});
        } else {
            const Lit root = enc.encode(skol[y]);
            s.add_clause({~Lit(y, /*sign=*/false), root});
            s.add_clause({Lit(y, /*sign=*/false), ~root});
        }
    }
    // Inject CDCL-learnt clauses from Phase D so the new solver gets
    // the same combinatorial pruning. They're over original vars, so
    // safe to add as red clauses.
    for (const auto& lc : learnt_clauses) s.add_red_clause(lc);
}


aig_ptr Cadet::build_shannon_tree(const vector<bool>& table,
                                  const vector<uint32_t>& sorted_inputs) {
    // table is indexed by integer mask of length sorted_inputs.size().
    // Bit i of the mask corresponds to sorted_inputs[i]. We Shannon-
    // decompose bottom-up, level by level: at level L the surviving
    // nodes cover 2^L leaves, addressed by the high (n-L) bits of the
    // original mask. Pair-merge: level[i] = ITE(sorted_inputs[L],
    //                                          high=level_prev[2i+1],
    //                                          low=level_prev[2i]).
    // ITE collapses to the common subtree when both children match, so
    // constant regions vanish naturally.
    const uint32_t n = sorted_inputs.size();
    if (n == 0) {
        assert(table.size() == 1);
        return AIG::new_const(table[0]);
    }
    vector<aig_ptr> level;
    level.reserve(table.size());
    for (bool b : table) level.push_back(AIG::new_const(b));

    for (uint32_t lvl = 0; lvl < n; lvl++) {
        const uint32_t split_var = sorted_inputs[lvl];
        const CMSat::Lit branch_lit(split_var, /*sign=*/false);
        vector<aig_ptr> next;
        next.reserve(level.size() / 2);
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            // level[i]   has bit `lvl` = 0  → low branch
            // level[i+1] has bit `lvl` = 1  → high branch
            // ITE(b, l, r) returns l when b is true.
            next.push_back(AIG::new_ite(level[i + 1], level[i], branch_lit));
        }
        level = std::move(next);
    }
    assert(level.size() == 1);
    return level[0];
}

bool Cadet::try_propagate(uint32_t y,
                          std::map<uint32_t, vector<uint32_t>>& dep_cache,
                          const std::map<uint32_t, Lit>& new_to_orig) {
    if (skol[y] != nullptr) return false;

    const auto& clauses = cnf.get_clauses();
    bool all_determined = true;
    aig_ptr pos_force = AIG::new_const(false);
    // We accumulate ONLY the positive-force region. The negative-force
    // region need not be computed: by the synthesis precondition
    // (F satisfiable for every input), positive and negative force
    // regions never overlap, so committing y = pos_force — TRUE on the
    // positive region, FALSE elsewhere — never violates a negative-y
    // clause.
    for (const auto& [ci, sign_y] : var_clauses[y]) {
        if (sign_y) continue;
        aig_ptr forced = AIG::new_const(true);
        for (const auto& l : clauses[ci]) {
            if (l.var() == y) continue;
            if (skol[l.var()] == nullptr) {
                all_determined = false;
                break;
            }
            aig_ptr lit_aig = skol[l.var()];
            if (l.sign()) lit_aig = ~lit_aig;
            forced = AIG::new_and(forced, ~lit_aig);
        }
        if (!all_determined) break;
        pos_force = AIG::new_or(pos_force, forced);
    }
    // Negative-y clauses must still be CHECKED for "all_determined".
    if (all_determined) {
        for (const auto& [ci, sign_y] : var_clauses[y]) {
            if (!sign_y) continue;
            for (const auto& l : clauses[ci]) {
                if (l.var() == y) continue;
                if (skol[l.var()] == nullptr) {
                    all_determined = false;
                    break;
                }
            }
            if (!all_determined) break;
        }
    }
    if (!all_determined) return false;

    // Cycle check via transitive orig-space deps.
    const uint32_t y_orig = new_to_orig.at(y).var();
    std::set<uint32_t> cnf_leaves;
    AIG::get_dependent_vars(pos_force, cnf_leaves, /*self=*/UINT32_MAX);
    for (uint32_t leaf : cnf_leaves) {
        uint32_t leaf_orig = new_to_orig.at(leaf).var();
        if (leaf_orig == y_orig) return false;
        if (cnf.defined(leaf_orig)) {
            const auto& deps = cnf.get_dependent_vars_recursive(leaf_orig, dep_cache);
            if (std::find(deps.begin(), deps.end(), y_orig) != deps.end()) {
                if (conf.verb >= 3) {
                    cout << "c o [cadet]   skipping y=" << (y + 1)
                         << " (orig " << y_orig + 1
                         << "): commit would create a defs[] cycle" << endl;
                }
                return false;
            }
        }
    }
    // Commit.
    skol[y] = pos_force;
    trail.push_back({y, decision_lvl, /*is_decision=*/false,
                     CMSat::Lit(0, false), {}});
    if (pos_force->type == AIGT::t_const) {
        mark_clauses_dead_by_constant(y, !pos_force.neg);
    }
    tseitin_skol_into_skolem_sat(y);
    // Small activity bump for vars whose Phase-C propagation actually
    // pulled them in — they're more likely to participate in future
    // tight forcing. Bumping all dependent vars too (the leaves of
    // pos_force) would spread activity too thin; just bump y.
    if (y < var_activity.size()) bump_var(y);
    return true;
}

void Cadet::mark_clauses_dead_by_constant(uint32_t v, bool val) {
    // Lit appears as +v when sign=false; that literal is TRUE iff val
    // is true. ¬v has sign=true and is TRUE iff val is false. The
    // satisfying-sign matches `!val` (since sign=true means ¬v).
    // We also record the freshly-killed clauses in trail.back() so
    // backjump_to_level can un-kill them.
    const bool sat_sign = !val;
    assert(!trail.empty() && "mark_clauses_dead_by_constant must run "
                             "AFTER pushing the commit's TrailEntry");
    auto& killed = trail.back().killed_clauses;
    for (const auto& [ci, sign_v] : var_clauses[v]) {
        if (sign_v == sat_sign && !clause_dead[ci]) {
            clause_dead[ci] = 1;
            killed.push_back(ci);
        }
    }
}

bool Cadet::try_pure_literal(uint32_t y) {
    if (skol[y] != nullptr) return false;
    // Count surviving (undead) clauses by polarity-of-y.
    bool has_pos = false, has_neg = false;
    for (const auto& [ci, sign_y] : var_clauses[y]) {
        if (clause_dead[ci]) continue;
        if (sign_y) has_neg = true;
        else has_pos = true;
        if (has_pos && has_neg) return false;
    }
    if (!has_pos && !has_neg) {
        // Every clause already dead — y is unconstrained. Commit false
        // (arbitrary; later AIG simplification folds it away).
        skol[y] = AIG::new_const(false);
        trail.push_back({y, decision_lvl, /*is_decision=*/false, Lit(0, false), {}});
        mark_clauses_dead_by_constant(y, false);
        tseitin_skol_into_skolem_sat(y);
        return true;
    }
    // Pure: if has_pos and !has_neg, y only appears positively in
    // surviving clauses; setting y=true satisfies all of them.
    // Symmetric for has_neg.
    const bool val = has_pos;
    skol[y] = AIG::new_const(val);
    trail.push_back({y, decision_lvl, /*is_decision=*/false, Lit(0, false), {}});
    mark_clauses_dead_by_constant(y, val);
    tseitin_skol_into_skolem_sat(y);
    return true;
}

void Cadet::enqueue_neighbours(uint32_t v,
                               std::vector<uint8_t>& in_queue,
                               std::vector<uint32_t>& queue) const {
    const auto& clauses = cnf.get_clauses();
    for (const auto& [ci, sign_v] : var_clauses[v]) {
        (void)sign_v;
        for (const auto& l : clauses[ci]) {
            const uint32_t u = l.var();
            if (u == v) continue;
            if (skol[u] != nullptr) continue;
            if (!in_queue[u]) {
                in_queue[u] = 1;
                queue.push_back(u);
            }
        }
    }
}

bool Cadet::synth_by_propagation() {
    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase C — unique-consequence propagation" << endl;
    }
    const double t0 = cpuTime();

    const auto new_to_orig = cnf.get_new_to_orig_var();
    std::map<uint32_t, vector<uint32_t>> dep_cache;

    skol.assign(cnf.nVars(), nullptr);
    for (uint32_t v : input) skol[v] = AIG::new_lit(v, /*neg=*/false);
    for (uint32_t v : backward_defined) skol[v] = AIG::new_lit(v, /*neg=*/false);

    trail.clear();
    decision_lits.clear();
    sel_lits.clear();
    decision_lvl = 0;

    MetaSolver& decision_sat = *skolem_sat;

    // Worklist-driven Phase C: every undet y starts on the queue.
    // When we commit y, every undet neighbour (sharing a clause) gets
    // re-enqueued — they're the only vars whose try_propagate result
    // could change. Avoids the O(passes × |to_define| × clauses) cost
    // of the old fixpoint loop.
    std::vector<uint8_t> in_queue(cnf.nVars(), 0);
    std::vector<uint32_t> queue;
    queue.reserve(to_define.size());
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) { in_queue[y] = 1; queue.push_back(y); }
    }

    // Seed clause_dead from any already-committed const skol[]. Today
    // this loop is a no-op because skol[] was just reset above, but it
    // would matter if synth_by_propagation got re-entered with a
    // partially-built skol state.
    for (uint32_t y : to_define) {
        if (skol[y] != nullptr && skol[y]->type == AIGT::t_const) {
            trail.push_back({y, decision_lvl,
                             /*is_decision=*/false, Lit(0, false), {}});
            mark_clauses_dead_by_constant(y, !skol[y].neg);
        }
    }

    uint32_t total_committed = 0;
    uint32_t total_decisions = 0;
    uint32_t total_pure = 0;
    uint32_t total_conflicts = 0;
    uint32_t total_restarts = 0;
    // Geometric restart schedule: backjump to level 0 after every
    // `restart_threshold` conflicts, then grow the threshold by
    // kRestartFactor. Keeps learnt clauses; just discards the
    // speculative tree so a fresh exploration can start.
    uint32_t restart_threshold = 16;
    uint32_t conflicts_since_restart = 0;
    static constexpr double kRestartFactor = 1.5;
    // Latch set when we hit the guess-depth cap and want one more
    // forced-only pass at level 0 (to pick up vars now forced by
    // learnt clauses) before exiting.
    bool no_more_guesses = false;
    uint32_t pass = 0;
    while (true) {
        pass++;
        // Geometric restart: when we've taken enough conflicts inside
        // the current speculative tree, throw away the tree (keeping
        // learnt clauses) and start fresh.
        if (decision_lvl > 0 &&
                conflicts_since_restart >= restart_threshold) {
            backjump_to_level(0);
            conflicts_since_restart = 0;
            restart_threshold = (uint32_t)(restart_threshold * kRestartFactor);
            total_restarts++;
            if (conf.verb >= 1) {
                cout << "c o [cadet] restart #" << total_restarts
                     << ", next threshold " << restart_threshold
                     << ", learnt=" << learnt_clauses.size() << endl;
            }
            // Re-enqueue every undet var.
            for (uint32_t y : to_define) {
                if (skol[y] == nullptr && !in_queue[y]) {
                    in_queue[y] = 1;
                    queue.push_back(y);
                }
            }
        }
        uint32_t committed_this_pass = 0;
        // Drain the propagation worklist.
        while (!queue.empty()) {
            const uint32_t y = queue.back();
            queue.pop_back();
            in_queue[y] = 0;
            // Try unique-consequence propagation first, then pure-literal.
            // Pure-literal can apply when not-all-determined: it doesn't
            // require knowing every clause's other lits, just that the
            // surviving clauses for y are one-sided.
            bool committed = try_propagate(y, dep_cache, new_to_orig);
            if (!committed) {
                if (try_pure_literal(y)) {
                    committed = true;
                    total_pure++;
                }
            }
            if (committed) {
                committed_this_pass++;
                total_committed++;
                enqueue_neighbours(y, in_queue, queue);
            }
        }
        if (conf.verb >= 2) {
            cout << "c o [cadet]   prop pass #" << pass
                 << ": committed " << committed_this_pass << endl;
        }

        // Phase D — propagation has stalled. We want to find SOME undet
        // var that F forces to a constant under current decisions
        // (commit it, resume propagation, possibly unblock more vars).
        //
        // Try every undet candidate, not just one. The earlier version
        // bailed after the first failed candidate, which on real
        // benchmarks (sdlx-fixpoint-5) was the difference between
        // "0 commits / give up" and "stop trying just because the
        // least-constrained var happened to be input-dependent".
        //
        // Order: by ascending clause-count (least-constrained first;
        // those are the most likely to be forced). Two SAT calls per
        // candidate at worst (both polarities); we accept that.
        //
        // We commit a CONSTANT Skolem only when F (plus earlier
        // decisions) FORCES pick to that constant — opposite-polarity
        // assumption is UNSAT. A looser check ("F+(y=c) sat") would be
        // unsound: it only means SOME input X works, not every X, so a
        // constant decision would violate F on some other input.

        // Conflict check at the current decision context. If under
        // active selector assumptions F is already UNSAT, our decision
        // stack is bad — find the responsible decisions in the failed
        // core, learn the negation as a permanent clause, and backjump
        // to the second-highest level among the responsible decisions.
        if (decision_lvl > 0) {
            vector<Lit> base = active_assumps();
            if (decision_sat.solve(&base) == CMSat::l_False) {
                const auto failed = decision_sat.get_conflict();
                vector<Lit> learnt;
                uint32_t max_lvl = 0, second_lvl = 0;
                for (const Lit& f : failed) {
                    // f is ~assumed_lit. The assumed lit is a selector
                    // sel_d (positive), so f is ~sel_d. Find d.
                    for (uint32_t d = 1; d <= decision_lvl; d++) {
                        if (sel_lits[d - 1].var() == f.var()) {
                            learnt.push_back(~decision_lits[d - 1]);
                            if (d > max_lvl) {
                                second_lvl = max_lvl;
                                max_lvl = d;
                            } else if (d > second_lvl) {
                                second_lvl = d;
                            }
                            break;
                        }
                    }
                }
                if (max_lvl == 0 || learnt.empty()) {
                    // F+empty UNSAT — means F itself is UNSAT.
                    // Shouldn't reach this in synthesis (precondition is
                    // F sat for every input). Bail to Phase E/F.
                    backjump_to_level(0);
                    break;
                }
                for (const Lit& l : learnt) {
                    const uint32_t v = l.var();
                    if (v < var_activity.size()) bump_var(v);
                }
                decay_activities();
                // Permanent learnt clause. Refutes the current
                // decision conjunction across all inputs. Also store
                // for Phase E/F to inject into their fresh solvers.
                decision_sat.add_clause(learnt);
                learnt_clauses.push_back(learnt);
                total_conflicts++;
                conflicts_since_restart++;
                backjump_to_level(second_lvl);
                if (conf.verb >= 1) {
                    cout << "c o [cadet] CDCL conflict at lvl "
                         << max_lvl << ": learnt " << learnt.size()
                         << " lits, backjump to " << second_lvl << endl;
                }
                // Re-enqueue every still-undet var — they might be
                // forced under the new learnt clause.
                for (uint32_t y : to_define) {
                    if (skol[y] == nullptr && !in_queue[y]) {
                        in_queue[y] = 1;
                        queue.push_back(y);
                    }
                }
                continue; // restart outer loop with shallower state
            }
        }

        // Order undet by VSIDS activity (highest first). Activities are
        // JW-seeded from clause density and get bumped each time a var
        // shows up in a failed-assumption core, so vars participating
        // in many UNSAT proofs rise to the front.
        vector<uint32_t> undet;
        undet.reserve(to_define.size());
        for (uint32_t y : to_define) {
            if (skol[y] == nullptr) undet.push_back(y);
        }
        if (undet.empty()) break; // nothing left undetermined
        std::sort(undet.begin(), undet.end(),
                  [&](uint32_t a, uint32_t b) {
                      return var_activity[a] > var_activity[b];
                  });

        bool any_decided = false;
        vector<Lit> base_assumps = active_assumps();
        vector<Lit> assumps;
        assumps.reserve(base_assumps.size() + 1);
        for (uint32_t pick : undet) {
            if (skol[pick] != nullptr) continue; // earlier decision propagated

            auto bump_core = [&]() {
                // Every var in the failed-assumption core participated
                // in the UNSAT proof — bump its activity so it floats
                // up next pass.
                const auto failed = decision_sat.get_conflict();
                for (const auto& f : failed) {
                    const uint32_t v = f.var();
                    if (v < var_activity.size()) bump_var(v);
                }
                decay_activities();
            };

            // SAT call 1: assume pick=true under current decisions;
            // UNSAT ⇒ pick must be false.
            assumps = base_assumps;
            assumps.push_back(Lit(pick, /*sign=*/false));
            auto commit_const = [&](bool val) {
                bump_core();
                skol[pick] = AIG::new_const(val);
                trail.push_back({pick, decision_lvl,
                                 /*is_decision=*/false, Lit(0, false), {}});
                mark_clauses_dead_by_constant(pick, val);
                // Unified tseitin path: at level 0 permanent, at
                // level>0 gated by sel_d. Backjump kills the gating.
                tseitin_skol_into_skolem_sat(pick);
                total_decisions++;
                any_decided = true;
                enqueue_neighbours(pick, in_queue, queue);
                if (conf.verb >= 2) {
                    cout << "c o [cadet]   forced: skol[" << (pick + 1)
                         << "] := " << (val ? "true" : "false")
                         << " at lvl " << decision_lvl << endl;
                }
            };
            if (decision_sat.solve(&assumps) == CMSat::l_False) {
                commit_const(false);
                continue;
            }
            // SAT call 2: assume pick=false under current decisions;
            // UNSAT ⇒ pick must be true.
            assumps = base_assumps;
            assumps.push_back(Lit(pick, /*sign=*/true));
            if (decision_sat.solve(&assumps) == CMSat::l_False) {
                commit_const(true);
                continue;
            }
            // Neither polarity forced — pick is genuinely
            // input-dependent. Skip and try the next candidate.
        }

        if (!any_decided) {
            // No undet var is forced by F under current decisions.
            // CDCL step: guess the highest-VSIDS undet at a new
            // decision level. Subsequent propagation runs under the
            // assumed sel_d. On a future probe UNSAT-with-sel_d-in-
            // core we'll backjump and learn (later commit).
            //
            // If there are no remaining undet, we're done.
            uint32_t guess = UINT32_MAX;
            double best = -1.0;
            for (uint32_t y : to_define) {
                if (skol[y] != nullptr) continue;
                if (var_activity[y] > best) {
                    best = var_activity[y];
                    guess = y;
                }
            }
            if (guess == UINT32_MAX) break; // nothing left
            // Soft cap on speculative depth — Phase F is terminal and
            // will mop up anything not committed. The cap also
            // bounds the work of "explore-and-backtrack" before we
            // give up and let downstream phases finish.
            static constexpr uint32_t kMaxGuessDepth = 8;
            if (no_more_guesses) break;
            if (decision_lvl >= kMaxGuessDepth) {
                if (conf.verb >= 1) {
                    cout << "c o [cadet] Phase D: hit guess-depth cap "
                         << kMaxGuessDepth << ", draining level-0 forced"
                         << endl;
                }
                backjump_to_level(0);
                no_more_guesses = true;
                // Re-enqueue every undet — learnt clauses may unit-
                // propagate them. Then re-enter the outer loop; the
                // next "no_more_guesses" branch will exit cleanly.
                for (uint32_t y : to_define) {
                    if (skol[y] == nullptr && !in_queue[y]) {
                        in_queue[y] = 1;
                        queue.push_back(y);
                    }
                }
                continue;
            }
            // Guess polarity: pick the value that satisfies more
            // surviving (undead) clauses — JW-style on the residual
            // formula. If y appears positively in more undead clauses
            // (sign=false), commit y=true; otherwise y=false. Pure-
            // literal handled the one-sided extremes, so this only
            // kicks in when both polarities are non-trivial.
            uint32_t n_pos = 0, n_neg = 0;
            for (const auto& [ci, sign_y] : var_clauses[guess]) {
                if (clause_dead[ci]) continue;
                if (sign_y) n_neg++; else n_pos++;
            }
            const bool guess_val = (n_pos >= n_neg);
            make_decision(guess, guess_val);
            enqueue_neighbours(guess, in_queue, queue);
            if (conf.verb >= 1) {
                cout << "c o [cadet] Phase D: guess skol[" << (guess + 1)
                     << "] := " << (guess_val ? "true" : "false")
                     << " (lvl " << decision_lvl
                     << ", undet=" << undet.size() << ")" << endl;
            }
            continue;
        }
        // Loop continues: propagation may make progress now that some
        // picks are committed.
    }

    // Before handing off to Phase E/F, undo every speculative (level>0)
    // commit. Phase E/F can only see level-0-permanent skol[] entries;
    // a wrong guess left behind here would corrupt their result.
    // Without conflict-driven CDCL the guess infrastructure can't
    // ratify a speculative commit, so they all get rolled back —
    // future commits will add the conflict-analysis step that turns
    // ratified guesses into permanent commits.
    if (decision_lvl > 0) backjump_to_level(0);

    uint32_t remaining = 0;
    for (uint32_t y : to_define) if (skol[y] == nullptr) remaining++;

    if (conf.verb >= 1) {
        const uint32_t prop_only = total_committed > total_pure
                                       ? total_committed - total_pure : 0;
        cout << "c o [cadet] Phase C+D done. passes: " << pass
             << " uc-props: " << prop_only
             << " pure: " << total_pure
             << " forced: " << total_decisions
             << " conflicts: " << total_conflicts
             << " restarts: " << total_restarts
             << " learnt: " << learnt_clauses.size()
             << " remaining: " << remaining
             << " T: " << fixed << setprecision(2) << (cpuTime() - t0) << endl;
    }
    return remaining == 0;
}

bool Cadet::synth_complete_with_models() {
    // Phase E. Builds the rest of cadet's Skolems on top of whatever
    // Phase C+D already committed, by:
    //   (1) Loading F into a fresh SAT solver.
    //   (2) Tseitin-encoding every prior skol[] commit (Phase C's
    //       pos_force AIGs and Phase D's constant decisions) and
    //       y ↔ skol[y] equivalence clauses. Any SAT model then
    //       respects the prior commits automatically.
    //   (3) Enumerating orig-sampling-var assignments via repeated
    //       SAT solving — each iteration finds a model, records y
    //       values for the still-undet vars into a per-y table,
    //       and forbids that exact input pattern so the next solve
    //       returns a different one. Stops when the solver returns
    //       UNSAT (every consistent input has been visited).
    //   (4) Building each undet y's Skolem from its table via
    //       Shannon decomposition (build_shannon_tree).
    //
    // Soundness: every recorded (input, y) pair comes from a SAT model
    // of F + prior commits, so the joint values for all undet y's at
    // each input are mutually consistent and consistent with what was
    // already committed.
    //
    // Limit: |orig_sampl_cnf| <= kSmallInputThreshold (16). For larger
    // inputs Phase E gives up; Phase F (terminal, no threshold) takes
    // over.
    if (orig_sampl_cnf.size() > kSmallInputThreshold) return false;

    // Identify still-undetermined to_define vars. If Phase C+D already
    // determinized everything, Phase E has nothing to do.
    vector<uint32_t> undet;
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) undet.push_back(y);
    }
    if (undet.empty()) return true;

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase E — SAT-model completion on "
             << undet.size() << " undet vars over "
             << orig_sampl_cnf.size() << " orig sampling vars (Phase C+D "
             << "committed " << (to_define.size() - undet.size())
             << "/" << to_define.size() << " already)" << endl;
    }
    const double t0 = cpuTime();

    // Build a fresh SAT solver loaded with F + tseitin of prior skol[]
    // commits via the shared helper. Phase E adds forbid clauses later
    // and so cannot share the persistent skolem_sat (those forbid
    // clauses must not leak into Phase F or Phase D).
    MetaSolver sat(SolverType::cadical);
    Lit true_lit;
    build_solver_with_skols(sat, true_lit);
    (void)true_lit; // currently unused after setup, kept for future ext.

    // Now iterate: every solve returns a SAT model whose values for
    // committed y's already match their skol[]s (via the Tseitin
    // encoding); we just record values for the UNDET y's and forbid
    // the input pattern.
    vector<uint32_t> sorted_inputs(orig_sampl_cnf.begin(), orig_sampl_cnf.end());
    std::sort(sorted_inputs.begin(), sorted_inputs.end());
    const uint32_t n_in = sorted_inputs.size();
    const uint64_t n_assign = 1ull << n_in;

    // Per-y value table; missing inputs default to false (those
    // assignments are UNSAT under F + prior commits, so y's value
    // there is vacuously free and "false" is a fine default — it
    // gets folded away by AIG simplification anyway).
    // unordered_map — see the matching note on `partial` in Phase F.
    // We only index `tables[y]` with y from `undet`; never iterate the
    // map itself, so ordered traversal is unneeded.
    std::unordered_map<uint32_t, vector<bool>> tables;
    tables.reserve(undet.size());
    for (uint32_t y : undet) tables[y].assign(n_assign, false);

    vector<Lit> forbid;
    forbid.reserve(n_in);
    uint64_t covered_count = 0;
    while (true) {
        const auto ret = sat.solve();
        if (ret == CMSat::l_False) break;
        if (ret != CMSat::l_True) {
            // UNDEF / unknown — bail; the caller (do_cadet) will
            // run Phase F to finish the still-undet vars.
            return false;
        }
        const auto& model = sat.get_model();
        uint64_t mask = 0;
        forbid.clear();
        for (uint32_t i = 0; i < n_in; i++) {
            const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
            if (mv) mask |= (1ull << i);
            forbid.push_back(Lit(sorted_inputs[i], mv));
        }
        if (mask < n_assign) {
            covered_count++;
            for (uint32_t y : undet) {
                tables[y][mask] = (model[y] == CMSat::l_True);
            }
        }
        sat.add_clause(forbid);
    }

    // Build Shannon trees for each undet y and commit.
    for (uint32_t y : undet) {
        skol[y] = build_shannon_tree(tables.at(y), sorted_inputs);
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase E done. covered " << covered_count
             << "/" << n_assign << " consistent input patterns. T: "
             << fixed << setprecision(2) << (cpuTime() - t0) << endl;
    }
    return true;
}

bool Cadet::synth_complete_with_interp_generalization() {
    // Monolithic Phase F: build Skolems for all still-undet vars over
    // the full orig sampling space in one SAT-model-enumeration loop.
    //
    // An earlier attempt at per-component decomposition was unsound:
    // when a clause involves a to_define var and an extend-defined
    // var, the extend var's existing AIG def transitively touches
    // OTHER to_define vars in different components. The per-component
    // Skolems then implicitly relied on consistent values for the
    // out-of-component orig-sampling vars feeding those extend defs,
    // producing skol[y1], skol[y2] that were each individually
    // consistent with F but JOINTLY incorrect at some inputs. Caught
    // by fuzz_cadet seed 11995170551103480696 (test-synth: "Sample
    // does not satisfy the CNF"). The worker is kept as a callable
    // helper (synth_phase_f_subset) so a future, correctly-merged
    // decomposition can call it; the current wrapper just forwards
    // the full undet set / full orig sampling set in one call.
    vector<uint32_t> all_undet;
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) all_undet.push_back(y);
    }
    if (all_undet.empty()) return true;
    vector<uint32_t> all_inputs(orig_sampl_cnf.begin(), orig_sampl_cnf.end());
    std::sort(all_inputs.begin(), all_inputs.end());
    return synth_phase_f_subset(all_inputs, all_undet);
}


bool Cadet::synth_phase_f_subset(const std::vector<uint32_t>& sub_inputs_in,
                                 const std::vector<uint32_t>& sub_undet) {
    // Phase F worker — operates on the supplied subset. Same algorithm
    // as the original monolithic Phase F, but `sorted_inputs` and
    // `undet` come from the parameters instead of class state.
    //
    // Like Phase E, but each iteration's case covers many
    // inputs (not just one). The generalization comes from greedy
    // bit-dropping with a uniqueness check:
    //
    //   For each SAT model M, build a tentative "case condition" = the
    //   input pattern from M. Then for each input bit i in turn, ask
    //   the SAT solver:
    //
    //     "F + (kept input lits without i) + (joint undet y ≠ M's
    //      values, gated by a selector) is UNSAT?"
    //
    //   If UNSAT: over the region "kept lits ∧ bit i unconstrained",
    //   the joint values for undet y's are FORCED to equal M's. Bit i
    //   doesn't affect what the y's must be — drop it from the case
    //   condition. Greedy across bits keeps shrinking the condition.
    //
    // Soundness: the uniqueness check is over the FULL kept region
    // (all combinations of dropped bits + whatever the SAT solver
    // picks for non-input vars), so committing the joint M-values
    // over the kept region is correct: there's no consistent y other
    // than M's values in that region.
    //
    // The "joint undet y ≠ M" assumption is encoded via a fresh
    // selector variable per iteration so it can be deactivated when
    // we move on (cadical doesn't support clause removal; selector
    // toggles are the standard incremental-SAT idiom).
    //
    // Termination: like Phase E, we forbid each minimized case
    // pattern after committing it. The outer SAT solve hits UNSAT
    // when every consistent input pattern has been covered by some
    // case. We also bound the iteration count to keep poorly-
    // converging inputs from running forever.
    //
    // Phase F has no input-size threshold and no iteration cap. It is
    // the terminal completion phase: it MUST succeed because the user
    // contract is that cadet always finishes (no Manthan fallback).
    //
    // Termination: each iteration forbids a non-empty kept-input
    // region, so total iterations ≤ 2^|orig_sampl_cnf| — finite.
    // Practical iterations are much smaller because each case's
    // UNSAT-core extraction generalizes over many inputs.
    //
    // The kPhaseFMaxIters constant is kept as a soft "warn but keep
    // going" threshold — the loop logs progress diagnostics every
    // kPhaseFMaxIters iters but never terminates early.
    static constexpr uint32_t kPhaseFMaxIters = 5000;
    // Periodic AIG simplification cadence. Long Phase F runs build
    // deep ITE chains; without periodic compression the AIG grows
    // unboundedly and each new_ite call walks an ever-larger DAG.
    static constexpr uint32_t kPhaseFSimplifyEvery = 1000;

    const std::vector<uint32_t>& undet = sub_undet;
    if (undet.empty()) return true;

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase F worker — " << undet.size()
             << " undet vars over " << sub_inputs_in.size()
             << " inputs (no iter cap; "
             << "diagnostic-flush every " << kPhaseFMaxIters << ")" << endl;
    }
    const double t0 = cpuTime();

    // We need TWO SAT solvers:
    //   * sat — for outer enumeration: F + Tseitin(prior commits) +
    //     accumulated forbid clauses (one per committed case so the
    //     next outer solve picks an uncovered input region).
    //   * minim — for the per-iteration uniqueness check: F +
    //     Tseitin(prior commits) ONLY. No forbid clauses.
    //
    // Why separate: the uniqueness check assumes (kept lits ∖ i) and
    // asks "is joint y = M_undet forced over this region?". If a
    // previous case's forbid clause becomes UNSAT under our
    // assumption (because dropping bit i lets our region overlap that
    // previous region on its kept bits), sat would return UNSAT for
    // the WRONG reason — making us spuriously drop bits and commit
    // wrong cases. Caught by fuzz_cadet seed 12315156945706132842.
    MetaSolver sat(SolverType::cadical);
    MetaSolver minim(SolverType::cadical);
    Lit sat_true_lit, minim_true_lit;
    build_solver_with_skols(sat, sat_true_lit);
    build_solver_with_skols(minim, minim_true_lit);
    (void)sat_true_lit; (void)minim_true_lit;

    vector<uint32_t> sorted_inputs = sub_inputs_in;
    std::sort(sorted_inputs.begin(), sorted_inputs.end());
    const uint32_t n_in = sorted_inputs.size();

    // Per-y partial Skolem (ITE chain of cases). Starts FALSE; each
    // iteration prepends a case via new_ite(value, prev, condition).
    // unordered_map (vs std::map) — we never iterate `partial`, only
    // index it via `partial[y]` with y drawn from `undet`, so the
    // ordered-traversal property of std::map is unused and we trade
    // a log(|undet|) factor for the O(1) lookup. Helps on the
    // hundreds-undet runs where Phase F iter count is large.
    std::unordered_map<uint32_t, aig_ptr> partial;
    partial.reserve(undet.size());
    for (uint32_t y : undet) partial[y] = AIG::new_const(false);

    uint32_t iters = 0;
    uint64_t total_drops = 0;
    bool converged = false;
    // Diagnostic counters: distinguish why Phase F's minimization
    // succeeded or failed at each iter.
    uint32_t n_uniq_unsat = 0;     // uniqueness check returned UNSAT (good — drops possible)
    uint32_t n_uniq_sat = 0;       // uniqueness check returned SAT (joint Y has alternatives — no drops)
    uint32_t n_uniq_unknown = 0;   // UNDEF (rare — solver gave up)
    uint64_t total_core_size = 0;  // size of UNSAT core when the check returned UNSAT
    // Per-y uniqueness fallback (runs only when joint uniqueness check
    // returns SAT — i.e., joint Y has alternatives at X*). For each
    // undet y, check whether y is *individually* forced at X*. Forced
    // y's get committed via a single permanent clause (no Tseitin —
    // the case condition is just a conjunction of input lits).
    uint64_t n_per_y_checks = 0;       // total per-y uniqueness SAT calls
    uint64_t n_per_y_commits = 0;      // per-y individually-forced commits
    // Adaptive disable flag: after the first productivity window of
    // per-y attempts, if commits/checks ratio is too low, per-y is
    // disabled for the remainder of this worker run.
    bool per_y_disabled = false;
    while (true) {
        // Outer solve: find an uncovered input pattern.
        const auto ret = sat.solve();
        if (ret == CMSat::l_False) { converged = true; break; }
        if (ret != CMSat::l_True) return false;
        iters++;

        const auto& model = sat.get_model();

        // Add a "selectable" uniqueness clause to the MINIM solver
        // (NOT the main `sat` solver, whose accumulated forbid clauses
        // would interfere with the uniqueness check — see
        // build_solver comment).
        //
        //   ¬sel ∨ (some undet y ≠ M's value for y)
        // When sel is asserted, the clause says "some y differs from M".
        // We solve minim under (sel + kept input lits) to ask "is
        // there a way for the kept inputs to extend to F-sat with some
        // undet y ≠ M?".  UNSAT ⇒ joint y = M is forced over the kept
        // region.
        minim.new_var();
        const uint32_t sel_var = minim.nVars() - 1;
        const Lit sel_lit(sel_var, /*sign=*/false);
        std::vector<Lit> uniq_clause;
        uniq_clause.reserve(undet.size() + 1);
        uniq_clause.push_back(~sel_lit);
        for (uint32_t y : undet) {
            const bool v = (model[y] == CMSat::l_True);
            // "y differs from v": if v=true, literal is ¬y; if v=false, y.
            uniq_clause.push_back(Lit(y, /*sign=*/v));
        }
        minim.add_clause(uniq_clause);

        // UNSAT-core-based minimization. Replaces the per-bit greedy
        // loop (which did n SAT calls per case, one per bit) with ONE
        // SAT call followed by an UNSAT-core extraction.
        //
        // Setup: assume sel + EVERY input-match lit. The clause set
        // says (gated by sel) "joint undet y must differ from M". If
        // that's UNSAT under the full-pattern assumption, joint y=M is
        // uniquely forced at the model's input — but more usefully,
        // cadical's UNSAT core tells us WHICH input lits were actually
        // used in the proof. Any input lit NOT in the core was
        // irrelevant: removing its assumption leaves the formula
        // UNSAT (uniqueness still holds with that bit free). So we
        // can safely drop every bit whose var is absent from the
        // core — same soundness guarantee as the per-bit greedy, but
        // O(1) SAT calls instead of O(n).
        //
        // get_conflict() returns ~l for each failed assumption l, so
        // failed_input_vars is just the var-id set of the conflict.
        std::vector<bool> kept(n_in, true);
        uint32_t bits_dropped = 0;
        // Captured per-iter so the per-y fallback after the joint
        // commit can tell whether THIS iter took the joint-SAT branch.
        lbool joint_unique_result = CMSat::l_Undef;
        {
            std::vector<Lit> assumps;
            assumps.reserve(n_in + 1);
            assumps.push_back(sel_lit);
            for (uint32_t i = 0; i < n_in; i++) {
                const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
                assumps.push_back(Lit(sorted_inputs[i], /*sign=*/!mv));
            }
            const auto r = minim.solve(&assumps);
            joint_unique_result = r;
            if (r == CMSat::l_False) {
                n_uniq_unsat++;
                const auto failed = minim.get_conflict();
                total_core_size += failed.size();
                std::set<uint32_t> failed_vars;
                for (const Lit& f : failed) failed_vars.insert(f.var());
                // Bump every var in the joint UNSAT core — those input
                // bits and undet vars that participated in the proof
                // are the discriminative ones.
                for (uint32_t v : failed_vars) {
                    if (v < var_activity.size()) bump_var(v);
                }
                decay_activities();
                for (uint32_t i = 0; i < n_in; i++) {
                    if (failed_vars.count(sorted_inputs[i]) == 0) {
                        kept[i] = false;
                        bits_dropped++;
                    }
                }
            } else if (r == CMSat::l_True) {
                n_uniq_sat++;
                // joint y=M is not unique at this input pattern
                // (multiple joint y satisfy F here). No bit can be
                // dropped JOINTLY; the joint case covers only this
                // exact input. But individual y's might still be
                // forced — fall through to per-y uniqueness check
                // below the joint commit block.
            } else {
                n_uniq_unknown++;
                // UNDEF — solver gave up. Same fallback: no drops.
            }
        }
        total_drops += bits_dropped;

        // Deactivate the uniqueness clause permanently (we don't need
        // it anymore; future iterations get their own selectors).
        minim.add_clause({~sel_lit});

        // Build min_pattern AIG from the kept bits. If everything was
        // dropped, the case covers the WHOLE input space — joint y =
        // M is the unique Skolem and we can commit constants.
        aig_ptr min_pattern = AIG::new_const(true);
        std::vector<Lit> forbid_clause;
        bool any_kept = false;
        for (uint32_t i = 0; i < n_in; i++) {
            if (!kept[i]) continue;
            any_kept = true;
            const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
            min_pattern = AIG::new_and(min_pattern, AIG::new_lit(sorted_inputs[i], !mv));
            forbid_clause.push_back(Lit(sorted_inputs[i], mv));
        }

        if (!any_kept) {
            // Whole input space → joint y = M is the unique Skolem
            // globally. Commit constants and we're done.
            for (uint32_t y : undet) {
                const bool v = (model[y] == CMSat::l_True);
                partial[y] = AIG::new_const(v);
            }
            if (conf.verb >= 2) {
                cout << "c o [cadet]   iter " << iters
                     << ": commit covers entire input space" << endl;
            }
            converged = true;
            break;
        }

        // Prepend the case to each undet y's partial Skolem:
        //   new_skol = ITE(min_pattern, M[y], old_skol)
        for (uint32_t y : undet) {
            const bool v = (model[y] == CMSat::l_True);
            partial[y] = AIG::new_ite(AIG::new_const(v), partial[y], min_pattern);
        }
        // Forbid this minimized pattern so the next outer solve picks
        // an uncovered input region.
        sat.add_clause(forbid_clause);

        if (conf.verb >= 2) {
            cout << "c o [cadet]   iter " << iters
                 << ": kept " << (n_in - bits_dropped)
                 << " / " << n_in << " bits" << endl;
        }

        // Per-y uniqueness fallback. Runs only on joint-SAT iters —
        // joint-UNSAT iters already commit a wide case via the
        // joint-UNSAT-core, so additional per-y work is wasted there.
        //
        // For each undet y, ask minim: "F ∧ y ≠ M[y] ∧ X=X* UNSAT?".
        // If so, y is individually forced at X*; the UNSAT core gives
        // the per-y kept bits. We commit y over that case via ONE
        // permanent clause to both sat and minim:
        //
        //   (X ≠ kept_bits) ∨ (y = M[y])
        //
        // No Tseitin needed — the case condition is a conjunction of
        // input lits, so its negation is exactly the disjunction in
        // the clause.
        //
        // Soundness: same UNSAT-core argument as joint uniqueness —
        // any X with kept_bits at their X*-values forces y=M[y] in F.
        //
        // Without per-y, joint-SAT iters cover exactly one input
        // minterm each, so the total Phase F iter count is ~|number of
        // consistent input patterns|. Per-y often shrinks that 10×+
        // because individual y's are forced under far more inputs
        // than joint Y.
        //
        // Cost guard: per-y adds |undet| SAT calls + |undet| clauses
        // to the running solvers per joint-SAT iter. Tight static cap
        // (kPerYUndetCap) avoids the worst case; an additional ADAPTIVE
        // disable kicks in mid-run when the first window of per-y
        // attempts has poor productivity (very few commits relative to
        // checks), since that means subsequent per-y calls will
        // probably be the same costly miss. Either guard alone is
        // unsound for performance: the static cap misses fast runs at
        // medium undet sizes (~30-60) where per-y would pay off, and
        // the adaptive disable alone would let huge-undet runs do a
        // ruinous first window before bailing.
        static constexpr uint32_t kPerYUndetCap = 30;
        static constexpr uint64_t kPerYProductivityWindow = 5000;
        // Below this commits/checks ratio, per-y is disabled for the
        // rest of the Phase F worker run. Calibrated against the
        // fuzzer: productive per-y typically hits >0.4 commits/check;
        // unproductive runs sit at <0.05 and dominate the slowdown.
        static constexpr double kPerYMinProductivity = 0.1;
        const bool was_joint_sat_this_iter = (joint_unique_result == CMSat::l_True);
        // Adaptive disable: after the productivity window, check the
        // commits/checks ratio. If poor, disable per-y for this run.
        // per_y_disabled is a function-scope variable (declared
        // outside the iter loop) so this check persists across iters.
        if (!per_y_disabled &&
            n_per_y_checks >= kPerYProductivityWindow) {
            const double ratio = double(n_per_y_commits) / double(n_per_y_checks);
            if (ratio < kPerYMinProductivity) {
                per_y_disabled = true;
                if (conf.verb >= 1) {
                    cout << "c o [cadet]   Phase F per-y disabled at iter "
                         << iters << ": productivity "
                         << fixed << setprecision(3) << ratio
                         << " < " << kPerYMinProductivity
                         << " ("  << n_per_y_commits << "/" << n_per_y_checks
                         << ")" << endl;
                }
            }
        }
        if (was_joint_sat_this_iter && undet.size() <= kPerYUndetCap
            && !per_y_disabled) {
            // VSIDS-ordered per-y scan: vars with higher activity get
            // checked first. A successful per-y commit reduces future
            // iter counts more for high-activity vars (those that were
            // failing-core members during earlier joint checks), so
            // ordering them first tends to converge faster.
            std::vector<uint32_t> py_order(undet.begin(), undet.end());
            std::sort(py_order.begin(), py_order.end(),
                      [&](uint32_t a, uint32_t b) {
                          return var_activity[a] > var_activity[b];
                      });
            for (uint32_t y : py_order) {
                n_per_y_checks++;
                minim.new_var();
                const uint32_t sel_y_var = minim.nVars() - 1;
                const Lit sel_y(sel_y_var, /*sign=*/false);
                const bool y_v = (model[y] == CMSat::l_True);
                // (¬sel_y ∨ y ≠ y_v): asserts y differs from M[y] when sel_y.
                minim.add_clause({~sel_y, Lit(y, /*sign=*/y_v)});

                std::vector<Lit> assumps;
                assumps.reserve(n_in + 1);
                assumps.push_back(sel_y);
                for (uint32_t i = 0; i < n_in; i++) {
                    const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
                    assumps.push_back(Lit(sorted_inputs[i], /*sign=*/!mv));
                }
                const auto rr = minim.solve(&assumps);
                // Deactivate the per-y uniqueness clause forever.
                minim.add_clause({~sel_y});

                if (rr != CMSat::l_False) continue; // y not forced at X*

                // y is individually forced at X*. Extract UNSAT core
                // for the per-y kept bits.
                const auto failed = minim.get_conflict();
                std::set<uint32_t> failed_vars;
                for (const Lit& f : failed) failed_vars.insert(f.var());

                // Bump y plus every var in the per-y proof core — those
                // vars made y forced at X*, so they're discriminative.
                bump_var(y);
                for (const auto& f : failed) {
                    const uint32_t v = f.var();
                    if (v < var_activity.size()) bump_var(v);
                }
                decay_activities();

                // Build the commit clause: (X ≠ kept_bits) ∨ (y = M[y]).
                std::vector<Lit> commit_clause;
                commit_clause.reserve(n_in + 1);
                aig_ptr case_aig = AIG::new_const(true);
                for (uint32_t i = 0; i < n_in; i++) {
                    if (failed_vars.count(sorted_inputs[i]) == 0) continue;
                    const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
                    // X_i ≠ mv: if mv=true, lit is ¬X_i (sign=true); else X_i (sign=false).
                    commit_clause.push_back(Lit(sorted_inputs[i], /*sign=*/mv));
                    // case AIG: AND of input matching lits
                    case_aig = AIG::new_and(case_aig,
                        AIG::new_lit(sorted_inputs[i], /*neg=*/!mv));
                }
                // y matches M[y]: if y_v=true, lit is y; else ¬y.
                commit_clause.push_back(Lit(y, /*sign=*/!y_v));
                sat.add_clause(commit_clause);
                minim.add_clause(commit_clause);

                // Update partial Skolem for y. The ITE prepend: at X
                // in case, return M[y]; else fall through to prev.
                partial[y] = AIG::new_ite(AIG::new_const(y_v),
                                          partial[y], case_aig);
                n_per_y_commits++;
            }
        }

        // Periodic AIG simplification: as the iteration count grows,
        // each `partial[y]` is a deepening ITE chain. AIG::new_ite
        // walks the existing DAG looking for structural matches, so
        // unsimplified deep chains slow every iteration down. Walk
        // the partial map and compress every kPhaseFSimplifyEvery
        // iters — this keeps per-iter wall time stable across runs
        // that take many thousands of iterations to converge.
        if (iters % kPhaseFSimplifyEvery == 0) {
            for (uint32_t y : undet) {
                partial[y] = AIG::simplify_aig(partial[y]);
            }
            if (conf.verb >= 1) {
                cout << "c o [cadet]   Phase F progress: iter=" << iters
                     << " uniq-UNSAT=" << n_uniq_unsat
                     << " uniq-SAT=" << n_uniq_sat
                     << " per-y-checks=" << n_per_y_checks
                     << " per-y-commits=" << n_per_y_commits
                     << " T=" << fixed << setprecision(2)
                     << (cpuTime() - t0) << endl;
            }
        }
    }

    auto print_phase_f_stats = [&](const std::string& outcome) {
        cout << "c o [cadet] Phase F " << outcome
             << ". iters=" << iters
             << " uniq-UNSAT=" << n_uniq_unsat
             << " uniq-SAT=" << n_uniq_sat
             << " uniq-UNDEF=" << n_uniq_unknown
             << " per-y-commits=" << n_per_y_commits
             << " / checks=" << n_per_y_checks
             << " avg-drops/iter=" << std::fixed << setprecision(1)
             << (iters > 0 ? double(total_drops) / iters : 0.0)
             << " avg-core-size=" << std::fixed << setprecision(1)
             << (n_uniq_unsat > 0 ? double(total_core_size) / n_uniq_unsat : 0.0)
             << " T=" << fixed << setprecision(2) << (cpuTime() - t0) << endl;
    };

    if (!converged) {
        // Phase F did not finish covering the input space — should
        // never happen since the loop has no iter cap. The only path
        // is SAT-solver UNDEF on outer solve. Print stats and bail.
        if (conf.verb >= 1) {
            print_phase_f_stats("did NOT converge (SAT UNDEF — bailing)");
        }
        return false;
    }

    for (uint32_t y : undet) skol[y] = partial[y];

    if (conf.verb >= 1) {
        print_phase_f_stats("converged + committed");
    }
    return true;
}

void Cadet::commit_definitions() {
    // Build a vector indexed by var, holding the Skolem AIG for each
    // to_define var. With Phase F's terminal completion guarantee,
    // every to_define var MUST have a non-null skol[y] by the time we
    // commit — assert that so any future regression that lets a var
    // slip through trips loudly here, not silently downstream.
    vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    for (uint32_t y : to_define) {
        release_assert(skol[y] != nullptr &&
                       "cadet must produce a Skolem for every to_define var");
        aigs[y] = skol[y];
    }
    const uint32_t cnf_nvars = cnf.nVars();
    cnf.map_aigs_to_orig(aigs, cnf_nvars);

    // Compress what we just committed. Phase F builds Skolems as deep
    // ITE chains; without this, every committed iteration adds an ITE
    // branch per undet var, and a 1000-iter Phase F run on 900 vars
    // produces a 900k-node AIG that downstream verification (test-synth)
    // can't handle in a reasonable time. AIG::simplify_aigs walks each
    // def, runs the cheap structural simplifier, and replaces in-place.
    cnf.simplify_aigs(conf.verb);
}

SimplifiedCNF Cadet::do_cadet() {
    const double my_time = cpuTime();
    if (conf.verb >= 1) {
        cout << "c o [cadet] starting; nVars=" << cnf.nVars()
             << " clauses=" << cnf.get_clauses().size() << endl;
    }

    // Partition vars into input/to_define/backward_defined, the same split
    // Manthan uses.
    cnf.get_var_types(conf.verb, "start do_cadet").unpack_to(
        input, to_define, backward_defined);

    // Independently compute the orig sampling vars in CNF numbering.
    // VarTypes.input would include extend-defined vars (vars defined by an
    // AIG over orig sampling vars), which are not actually free in F;
    // enumerating over them in Phase A would generate inconsistent
    // assumption sets. We only enumerate over the orig sampling vars.
    orig_sampl_cnf.clear();
    const auto& o2n = cnf.get_orig_to_new_var();
    for (uint32_t v : cnf.get_orig_sampl_vars()) {
        auto it = o2n.find(v);
        if (it == o2n.end()) continue; // eliminated from CNF
        orig_sampl_cnf.insert(it->second.var());
    }

    if (to_define.empty()) {
        if (conf.verb >= 1) {
            cout << "c o [cadet] nothing to define — returning unchanged CNF" << endl;
        }
        return std::move(cnf);
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] partition: |orig_sampl|=" << orig_sampl_cnf.size()
             << " |input|=" << input.size()
             << " |to_define|=" << to_define.size()
             << " |backward_defined|=" << backward_defined.size() << endl;
    }

    // Build the per-var clause occurrence index once. Used by Phase C
    // and Phase D, and (transitively) by Phase F's per-y fallback.
    {
        const auto& clauses = cnf.get_clauses();
        var_clauses.assign(cnf.nVars(), {});
        for (uint32_t ci = 0; ci < clauses.size(); ci++) {
            for (const auto& l : clauses[ci]) {
                var_clauses[l.var()].emplace_back(ci, l.sign());
            }
        }
        clause_dead.assign(clauses.size(), 0);
    }

    // VSIDS seed: Jeroslow-Wang-style — heavier vars in shorter clauses
    // are more likely to be forced; activity starts at 2^-len summed
    // over clauses, capped at len<=10 to avoid pow underflow. This gives
    // Phase D a useful priority before any conflict has happened.
    var_activity.assign(cnf.nVars(), 0.0);
    activity_inc = 1.0;
    {
        const auto& clauses = cnf.get_clauses();
        for (const auto& c : clauses) {
            if (c.size() > 10) continue;
            const double w = std::ldexp(1.0, -(int)c.size()); // 2^-size
            for (const auto& l : c) var_activity[l.var()] += w;
        }
    }

    // Build the persistent Skolem SAT solver once with F injected.
    // Phase C adds tseitin-encoded skol[y] AIGs as it commits them
    // (so Phase D's probes run under F + all prior commits), and
    // Phase D adds unit clauses for constants. cadical retains learnt
    // clauses across solve() calls, so each new decision builds on
    // prior work.
    skolem_sat = std::make_unique<MetaSolver>(SolverType::cadical);
    inject_cnf(*skolem_sat);
    skolem_sat->new_var();
    skolem_sat_true_lit = Lit(skolem_sat->nVars() - 1, /*sign=*/false);
    skolem_sat->add_clause({skolem_sat_true_lit});

    // ---- Phase C+D: unique-consequence propagation with sound
    // constant decisions. CADET-flavored core; scales independently of
    // input count, limited only by structural propagation reach and by
    // how many vars F forces to constants.
    bool done = synth_by_propagation();

    // ---- Phase E: small-input SAT-model enumeration. Runs whenever
    // the input space is small enough that 2^|orig_sampl_cnf| naive
    // enumeration is cheap (≤ kSmallInputThreshold = 16, so ≤ 65k
    // SAT calls). Respects Phase C+D's partial commits via Tseitin
    // encoding. Phase E is just faster than Phase F at this size —
    // no per-iter uniqueness/minimization overhead, just straight
    // model collection.
    if (!done) {
        done = synth_complete_with_models();
    }

    // ---- Phase F: terminal generalized-case completion. ALWAYS
    // succeeds — no input-size threshold, no iter cap. Per-iter cost
    // is bounded by UNSAT-core minimization and per-y uniqueness;
    // total iter count is bounded by 2^|orig_sampl_cnf|. After Phase
    // F the synth contract holds.
    if (!done) {
        done = synth_complete_with_interp_generalization();
    }

    release_assert(done && "Phase F is supposed to be a terminal phase — "
                   "if we land here without completing, that's a regression");

    // Commit. commit_definitions release_asserts every to_define var
    // has a non-null skol[y] — Phase F's guarantee tested loudly.
    commit_definitions();

    if (conf.verb >= 1) {
        cout << "c o [cadet] done — all " << to_define.size()
             << " to_define vars committed. T: "
             << fixed << setprecision(2) << (cpuTime() - my_time) << endl;
    }
    return std::move(cnf);
}

} // namespace ArjunInt
