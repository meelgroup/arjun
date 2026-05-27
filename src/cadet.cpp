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
   Phase C — unique-consequence propagation. For each undet y, walk
   its clauses; when every other literal is already a function of
   inputs / earlier-determined vars, the clause forces y over its
   "negated-other-literals" region. Accumulating those regions over
   all positive-y clauses gives a candidate Skolem; a cycle check
   guards against creating defs[] cycles.

   Phase D — constant-value decisions. When Phase C stalls, pick
   undet vars in least-constrained order and try y=false; if F+y=true
   is UNSAT, y must be false (and vice versa). Commits only when one
   polarity is provably UNSAT — never an unsound guess.

   Phase E — small-input SAT-model enumeration. When |orig_sampl| ≤
   16, repeatedly solve F+Tseitin(prior commits) under "forbid seen
   inputs"; collect each model's undet y values into a per-y table;
   build Shannon trees at the end.

   Phase F — terminal: SAT-model + UNSAT-core generalization with
   per-y uniqueness fallback. No input-size threshold, no iter cap.
   Each iter either drops bits via the joint UNSAT core or, on
   joint-SAT, falls back to per-y uniqueness checks (capped at 30
   undet vars to bound per-iter cost). Total iter count is bounded
   by 2^|orig_sampl_cnf| — finite. Phase F is what backs cadet's
   "always finishes" contract.

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
    // skolem_sat already has F + previously-committed skols. Add the
    // tseitin encoding of skol[y] and the y ↔ root equivalence so the
    // solver knows that y must match skol[y] wherever F is satisfiable.
    assert(skolem_sat != nullptr);
    assert(skol[y] != nullptr);
    if (skol[y]->type == AIGT::t_const) {
        const bool val = !skol[y].neg;
        skolem_sat->add_clause({Lit(y, /*sign=*/!val)});
        return;
    }
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
    if (pos_force->type == AIGT::t_const) {
        mark_clauses_dead_by_constant(y, !pos_force.neg);
    }
    tseitin_skol_into_skolem_sat(y);
    return true;
}

void Cadet::mark_clauses_dead_by_constant(uint32_t v, bool val) {
    // Lit appears as +v when sign=false; that literal is TRUE iff val
    // is true. ¬v has sign=true and is TRUE iff val is false. The
    // satisfying-sign matches `!val` (since sign=true means ¬v).
    const bool sat_sign = !val;
    for (const auto& [ci, sign_v] : var_clauses[v]) {
        if (sign_v == sat_sign) clause_dead[ci] = 1;
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
        mark_clauses_dead_by_constant(y, false);
        tseitin_skol_into_skolem_sat(y);
        return true;
    }
    // Pure: if has_pos and !has_neg, y only appears positively in
    // surviving clauses; setting y=true satisfies all of them.
    // Symmetric for has_neg.
    const bool val = has_pos;
    skol[y] = AIG::new_const(val);
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

    // Seed clause_dead from any already-committed const skol[]. The
    // input set already has skol[v]=lit (non-const leaves), backward
    // has the same — neither kill clauses. But Phase C is allowed to
    // re-enter this function in principle, so a constant left over
    // from a previous pass would need to mark clauses; today this loop
    // is a no-op because skol[] was just reset to nullptr / leaves.
    for (uint32_t y : to_define) {
        if (skol[y] != nullptr && skol[y]->type == AIGT::t_const) {
            mark_clauses_dead_by_constant(y, !skol[y].neg);
        }
    }

    uint32_t total_committed = 0;
    uint32_t total_decisions = 0;
    uint32_t total_pure = 0;
    uint32_t pass = 0;
    while (true) {
        pass++;
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

        // Sort undetermined vars by clause count ascending.
        vector<uint32_t> undet;
        undet.reserve(to_define.size());
        for (uint32_t y : to_define) {
            if (skol[y] == nullptr) undet.push_back(y);
        }
        if (undet.empty()) break; // nothing left undetermined
        std::sort(undet.begin(), undet.end(),
                  [&](uint32_t a, uint32_t b) {
                      return var_clauses[a].size() < var_clauses[b].size();
                  });

        bool any_decided = false;
        vector<Lit> assumps(1);
        for (uint32_t pick : undet) {
            if (skol[pick] != nullptr) continue; // earlier decision propagated

            // SAT call 1: assume pick=true; UNSAT ⇒ pick must be false.
            assumps[0] = Lit(pick, /*sign=*/false);
            if (decision_sat.solve(&assumps) == CMSat::l_False) {
                skol[pick] = AIG::new_const(false);
                mark_clauses_dead_by_constant(pick, false);
                decision_sat.add_clause({Lit(pick, /*sign=*/true)});
                total_decisions++;
                any_decided = true;
                enqueue_neighbours(pick, in_queue, queue);
                if (conf.verb >= 2) {
                    cout << "c o [cadet]   decision: skol[" << (pick + 1)
                         << "] := false (F forces it)" << endl;
                }
                continue; // try the next candidate too in this Phase-D pass
            }
            // SAT call 2: assume pick=false; UNSAT ⇒ pick must be true.
            assumps[0] = Lit(pick, /*sign=*/true);
            if (decision_sat.solve(&assumps) == CMSat::l_False) {
                skol[pick] = AIG::new_const(true);
                mark_clauses_dead_by_constant(pick, true);
                decision_sat.add_clause({Lit(pick, /*sign=*/false)});
                total_decisions++;
                any_decided = true;
                enqueue_neighbours(pick, in_queue, queue);
                if (conf.verb >= 2) {
                    cout << "c o [cadet]   decision: skol[" << (pick + 1)
                         << "] := true (F forces it)" << endl;
                }
                continue;
            }
            // Neither polarity forced — pick is genuinely
            // input-dependent. Skip and try the next candidate.
        }

        if (!any_decided) {
            // No undet var is forced by F under current decisions.
            // Phase C+D can do no more; return so do_cadet runs
            // Phase E / Phase F to finish the remaining undet vars.
            if (conf.verb >= 1) {
                cout << "c o [cadet] Phase D: no undet var forced by F "
                     << "(" << undet.size() << " tried); falling back" << endl;
            }
            break;
        }
        // Loop continues: propagation may make progress now that some
        // picks are committed.
    }

    uint32_t remaining = 0;
    for (uint32_t y : to_define) if (skol[y] == nullptr) remaining++;

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase C+D done. passes: " << pass
             << " props: " << total_committed
             << " (pure: " << total_pure << ")"
             << " decisions: " << total_decisions
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
            for (uint32_t y : undet) {
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
