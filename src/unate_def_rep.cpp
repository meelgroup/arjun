/*
 Arjun

 Copyright (c) 2026, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

// Repair-based extension of the conditional unate-def search.
//
// `synthesis_unate_def` already tries trivial Skolems (constant true/false
// from the standard flip test) and one-literal definitions
// `t = L` / `t = ~L` from the conditional probe. For variables that survive
// both, this pass tries to synthesize a richer Boolean function for `test`
// using a manthan-style counterexample-guided guess+refine loop.
//
// Algorithm per surviving `test`:
//
//   1. Setup is identical to synthesis_unate_def: a miter
//        F(X, Y)  ∧  ¬F(X, Y')
//      with all already-defined vars constrained on the Y' side, and
//      indicator literals tying y_i = y_i' for every other to-define i.
//   2. Maintain a candidate AIG H over allowed leaves. Start with H = FALSE.
//      Allowed leaves are X (always) plus a per-test "aux" set: vars `v`
//      where committing `test = H(..., v)` does NOT close a dependency
//      cycle. See `unate_def_rep_aux` for the policy.
//   3. Each iteration:
//      a. Tseitin-encode H on the Y' side under a fresh activation literal
//         act_i, adding clauses `act_i → (y_test' ⇔ H(...))`. Non-input
//         leaves use the Y'-side var (`var + nVars()`); inputs are shared
//         and use `var`.
//      b. Solve the miter under {indicators TRUE, act_i}.
//         - UNSAT → run a feasibility check in f_solver: encode H there
//                   and ask whether `(current F') ∧ y_test = h_enc` is
//                   SAT. f_solver starts as original F and accumulates
//                   the y_v ⇔ H_v of every prior commit (see step 5), so
//                   this check is against cumulative F', not original F.
//                   SAT → H is at least sometimes a Skolem witness in F';
//                   commit y_test ⇔ H and stop. UNSAT → H is never a
//                   valid value for y_test anywhere in F' (rules out the
//                   vacuous-miter-UNSAT case where committing would lose
//                   X-projections); bump skolem_only_skipped and continue.
//                   UNDEF → undecided; treat as UNSAT and continue.
//                   NOTE: this is intentionally weaker than uniqueness in
//                   F'; see the in-block comment at the check site for
//                   why it is sound on bifunctional benchmarks.
//         - SAT   → CEX. y_test_F = m[test] is a value F admits at X*;
//                   H(...) = m[h_enc_lit] is the value the activation
//                   forced on Y' which broke F. They differ.
//      c. Use a separate F-only solver to confirm "F forces y_test ≠ H(...)
//         when (X, aux) = miter values" and to extract a small unsat core.
//         - Cost-zero (F-solver SAT) → H is actually fine; the miter is
//           over-constrained by the y_other = y_other' pinning. Allowing
//           H to read more aux vars (mode>=1) shrinks the y_other set the
//           miter is sensitive to and tends to eliminate cost-zero
//           false alarms when F is bifunctional. After the budget, bail
//           and let Manthan handle this var.
//         - UNSAT → conflict ⊆ assumed (X ∪ aux) lits. The conjunction of
//           the core lits is a "pattern" P such that F ⊨ (P → y_test = y_F).
//      d. Refine H by covering the bad point:
//           y_test_F = TRUE  →  H = H ∨ P
//           y_test_F = FALSE →  H = H ∧ ¬P
//   4. Disable old activation each iteration (`act_i := FALSE` permanent).
//   5. After per-var loop, mark the var's indicator TRUE permanently —
//      same convention as synthesis_unate_def, regardless of whether we
//      found a def. If we did, we also commit y_test ⇔ H to tighten the
//      miter for subsequent vars (using a Y-side encoding when H has any
//      non-input leaves so the commit clause stays sound after later
//      tests untie an aux var's pinning indicator). The same y_test ⇔ H
//      equivalence is mirrored into f_solver so the next var's
//      feasibility check operates against cumulative F' (= F ∧ all prior
//      commits), letting chained-Skolem commits compose.
//
// AIG correctness invariants:
//
//   - Leaves of H come from X (input) ∪ aux. Aux is selected per-test so
//     that committing `test`'s def cannot create a dependency cycle:
//     for every aux var `v`, either `v` is undefined or `test ∉ deps(v)`.
//     Manthan's existing dependency tracking handles the live-cycle case
//     for undefined aux leaves (it must define `v` without going through
//     `test`).
//   - Inputs are shared across the Y/Y' sides, so an input-only H needs
//     just one encoding for both `act → y_test' ⇔ H` and `y_test ⇔ H`.
//     With aux leaves, those vars differ between sides; we emit two
//     encodings (Y' and Y) on commit.
//   - Translation to ORIG-var-space uses the same sign convention as the
//     conditional-unate code: leaf-sign XOR's `new_to_orig`'s sign flip;
//     the AIG output is XOR'd by `test_orig.sign()`. Works for any leaf.
//
// Knobs (Config):
//   unate_def_rep_iters        — guess+refine iters per var
//   unate_def_rep_max_pattern  — skip CEX whose unsat core is bigger than this
//   unate_def_rep_max_costzero — give up after this many cost-zero CEXes
//   unate_def_rep_max_confl    — conflict budget for each SAT call
//   unate_def_rep_aux          — 0=input only, 1=+backward_defined,
//                                2=+to-define (full)

#include "unate_def_rep.h"
#include "unate_def_common.h"
#include "constants.h"
#include "metasolver.h"
#include "time_mem.h"

#include <functional>
#include <iomanip>
#include <limits>
#include <map>

using namespace ArjunNS;
using namespace CMSat;
using std::setprecision;
using std::fixed;
using std::setw;
using std::vector;
using std::set;
using std::make_unique;
using std::map;

namespace ArjunInt {

Lit UnateDefRep::get_s_true() {
    if (s_true_lit == lit_Undef) {
        s->new_var();
        s_true_lit = Lit(s->nVars()-1, false);
        s->add_clause({s_true_lit});
    }
    return s_true_lit;
}

Lit UnateDefRep::get_f_true() {
    if (f_true_lit == lit_Undef) {
        f_solver->new_var();
        f_true_lit = Lit(f_solver->nVars()-1, false);
        f_solver->add_clause({f_true_lit});
    }
    return f_true_lit;
}

std::pair<Lit, Lit> UnateDefRep::get_cnf_true() {
    if (cnf_true_lit_new == lit_Undef) {
        cnf.new_var();
        const uint32_t v_new = cnf.nVars() - 1;
        const uint32_t v_orig = cnf.num_defs() - 1;
        cnf_true_lit_new = Lit(v_new, false);
        cnf_true_lit_orig = Lit(v_orig, false);
        cnf.add_clause({cnf_true_lit_new});
        // Skolem-mark the helper so check_pre_post_backward_round_synth
        // and get_var_types treat the chain consistently — see comment
        // at the AND-helper set_def_skolem call below.
        cnf.set_def_skolem(v_orig, AIG::new_const(true));
    }
    return {cnf_true_lit_new, cnf_true_lit_orig};
}

void UnateDefRep::setup_yprime_backward_defs() {
    for (const auto& i_new : backward_defined) {
        if (input.count(i_new)) continue;
        assert(new_to_orig.count(i_new) > 0);
        const Lit orig = new_to_orig.at(i_new);
        const auto& aig = cnf.get_def(orig.var());
        assert(aig != nullptr && "Already-defined var must have an AIG definition");

        const Lit out_lit = AIG::tseitin_encode(
            aig, *s,
            [&] { return get_s_true(); },
            [&](uint32_t var_orig) -> Lit {
                const Lit lit_new = cnf.orig_to_new_lit(Lit(var_orig, false));
                if (input.count(lit_new.var())) return lit_new;
                assert(lit_new.var() < cnf.nVars());
                return Lit(lit_new.var() + cnf.nVars(), lit_new.sign());
            });
        const Lit out_in_new_space = out_lit ^ orig.sign();
        const Lit i_copy = Lit(i_new + cnf.nVars(), false);
        s->add_clause({~i_copy, out_in_new_space});
        s->add_clause({i_copy, ~out_in_new_space});
    }
}

void UnateDefRep::build_indicators() {
    var_to_indic.clear();
    var_to_indic.resize(cnf.nVars(), var_Undef);
    for (uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        if (backward_defined.count(i)) continue;
        s->new_var();
        const Lit ind_l = Lit(s->nVars()-1, false);
        const auto y     = Lit(i, false);
        const auto y_hat = Lit(i + cnf.nVars(), false);
        vector<Lit> tmp;
        tmp.push_back(~ind_l); tmp.push_back(y_hat); tmp.push_back(~y);
        s->add_clause(tmp);
        tmp[1] = ~tmp[1]; tmp[2] = ~tmp[2];
        s->add_clause(tmp);
        tmp.clear();
        tmp.push_back(ind_l); tmp.push_back(~y_hat); tmp.push_back(~y);
        s->add_clause(tmp);
        tmp[1] = ~tmp[1]; tmp[2] = ~tmp[2];
        s->add_clause(tmp);
        var_to_indic[i] = ind_l.var();
    }
}

void UnateDefRep::build_f_solver() {
    f_solver = make_unique<ArjunInt::MetaSolver>();
    f_solver->new_vars(cnf.nVars());
    f_solver->set_verbosity(0);
    for (const auto& cl : cnf.get_clauses()) f_solver->add_clause(cl);
}

// `is_y_prime` selects which side the leaf SAT vars live on. Input leaves
// are shared between Y and Y' (same SAT var). Non-input leaves (aux) live
// on separate vars per side; the pinning indicator (asserted in
// base_assumps for every other to-define var) keeps `y == y'` so both
// encodings agree on leaf values. AND helpers are freshly allocated per
// call.
Lit UnateDefRep::encode_h_in_miter(const aig_ptr& h, bool is_y_prime) {
    return AIG::tseitin_encode(
        h, *s,
        [&] { return get_s_true(); },
        [&](uint32_t var) -> Lit {
            // var is in NEW-var space.
            if (input.count(var)) return Lit(var, false);
            return Lit(is_y_prime ? var + cnf.nVars() : var, false);
        },
        &rep_stats.encode_h_nodes_visited,
        &rep_stats.encode_h_nodes_emitted);
}

// Tseitin-encode H into f_solver. Leaves are direct F-vars (inputs and
// aux). AND helpers are fresh vars in f_solver. Returns the top lit.
// Used by the per-iter feasibility check before committing.
Lit UnateDefRep::encode_h_in_f(const aig_ptr& h) {
    // Leaves are direct F-vars (inputs and backward-defined aux are both F-vars
    // in f_solver), so the leaf map is the identity in NEW-var space.
    return AIG::tseitin_encode(
        h, *f_solver,
        [&] { return get_f_true(); },
        [](uint32_t var) { return Lit(var, false); },
        nullptr,
        &rep_stats.encode_h_in_f_emitted);
}

// Count distinct non-input leaves of `h`
size_t UnateDefRep::h_aux_leaf_count(const aig_ptr& h) const {
    std::set<uint32_t> deps;
    AIG::get_dependent_vars(h, deps,
                            std::numeric_limits<uint32_t>::max());
    size_t n = 0;
    for (uint32_t d : deps) if (!input.count(d)) n++;
    return n;
}

// Tseitin-encode H into cnf clauses, allocating AND helpers in cnf and
// setting defs[helper_orig] for each helper. Returns the NEW-space Lit
// representing the top of H. Called once per successful commit. We
// need the def materialized as actual cnf clauses (not just stored in
// cnf.defs) so the fresh SAT solver in find_better_ctx_normal — which
// ingests cnf.get_clauses() but does NOT materialize cnf.defs — sees
// the y_test ⇔ H equivalence directly. Without this, chained-Skolem
// commits can hard-assume y[BW]=ctx[y_hat[BW]] in find_better_ctx_normal
// and fail because original F (without prior commits' clauses) doesn't
// imply the chain.
//
// Helpers are classified by get_var_types based on their dep chain:
// a pure-input H produces extend-defined helpers (treated as inputs by
// Manthan, with cnf clauses constraining their values); an aux-bearing
// H produces backward-synth-defined helpers. Either way the user-
// visible output AIG for `test` itself comes from defs[test_orig] =
// h_in_orig (with original leaves only), set by set_def_skolem above —
// the helpers are SAT-side artifacts.
//
// Caches the NEW-space and ORIG-space lits per AIG node (positive
// form), then applies edge negation. The ORIG-space lit is used to
// construct each helper's def AIG.
Lit UnateDefRep::materialize_h_in_cnf(const aig_ptr& h_root) {
    std::map<const AIG*, std::pair<Lit, Lit>> mat_cache;
    std::function<std::pair<Lit, Lit>(const aig_ptr&)> rec =
      [&](const aig_ptr& a) -> std::pair<Lit, Lit> {
        auto it = mat_cache.find(a.get());
        std::pair<Lit, Lit> pos;
        if (it != mat_cache.end()) {
            pos = it->second;
        } else {
            if (a->type == AIGT::t_const) {
                pos = get_cnf_true();
            } else if (a->type == AIGT::t_lit) {
                const uint32_t v_new = a->var;
                const Lit orig = new_to_orig.at(v_new);
                pos = {Lit(v_new, false), orig};
            } else {
                auto l = rec(a->l);
                auto r = rec(a->r);
                cnf.new_var();
                const uint32_t v_new = cnf.nVars() - 1;
                const uint32_t v_orig = cnf.num_defs() - 1;
                const Lit pos_new(v_new, false);
                const Lit pos_orig(v_orig, false);
                cnf.add_clause({~pos_new, l.first});
                cnf.add_clause({~pos_new, r.first});
                cnf.add_clause({pos_new, ~l.first, ~r.first});
                aig_ptr left_aig  = AIG::new_lit(l.second.var(), l.second.sign());
                aig_ptr right_aig = AIG::new_lit(r.second.var(), r.second.sign());
                // Use set_def_skolem (vs set_def) so:
                //  (a) get_var_types keeps helpers in backward_synth_defined
                //      even when their dep-chain is all input
                //      (a pure-input H produces such helpers); without
                //      this they'd land in extend_defined and Manthan
                //      would treat them as inputs, dropping the
                //      helper = AND constraint we just baked in.
                //  (b) check_pre_post_backward_round_synth's invariant
                //      ("vars in CNF must be defined in terms of
                //      orig_sampl_vars") explicitly exempts Skolem-
                //      marked vars — necessary for chained-Skolem H's
                //      whose aux leaves are themselves non-orig-sampl
                //      backward-defined vars.
                cnf.set_def_skolem(v_orig, AIG::new_and(left_aig, right_aig));
                pos = {pos_new, pos_orig};
            }
            mat_cache[a.get()] = pos;
        }
        return {a.neg ? ~pos.first  : pos.first,
                a.neg ? ~pos.second : pos.second};
    };
    return rec(h_root).first;
}

vector<Lit> UnateDefRep::build_base_assumps(const uint32_t test) {
    vector<Lit> base_assumps;
    // Indicator assumptions: TRUE for every other to-define var that hasn't
    // been pinned yet. Same exclusion logic as synthesis_unate_def.
    for (uint32_t i = 0; i < cnf.nVars(); i++) {
        if (i == test) continue;
        if (already_tested.count(i)) continue;
        if (input.count(i)) continue;
        if (backward_defined.count(i)) continue;
        const auto ind = var_to_indic.at(i);
        assert(ind != var_Undef);
        base_assumps.emplace_back(ind, false);
    }
    // Assume indicator_test = FALSE: forces y_test_Y != y_test_Y' in
    // every miter call. With y_test_Y' pinned to h_val by the per-iter
    // activation, this guarantees y_test_val_f = ~h_val whenever the
    // miter is SAT — i.e. every CEX is "F admits the OPPOSITE of
    // H_curr", which is the only direction useful for refining H.
    const auto ind_test = var_to_indic.at(test);
    assert(ind_test != var_Undef);
    base_assumps.emplace_back(ind_test, true);
    return base_assumps;
}

// Build per-test aux leaf set. A var `v` ≠ test, not in input, may be
// used as an H-leaf iff committing `test = H(..., v)` does NOT close
// a dependency cycle. For backward-defined `v` we check via the
// recursive-deps cache; for currently-undefined to-define `v` there
// is no current cycle (Manthan's set_depends_on tracks the new edge
// and avoids closing it later).
void UnateDefRep::build_allowed_aux_set(const uint32_t test, const Lit test_orig) {
    aux_vars.clear();
    std::fill(aux_mask.begin(), aux_mask.end(), 0);
    if (conf.unate_def_rep_aux > 0) {
        for (uint32_t v_new = 0; v_new < cnf.nVars(); v_new++) {
            if (v_new == test) continue;
            if (input.count(v_new)) continue;
            auto it = new_to_orig.find(v_new);
            if (it == new_to_orig.end()) continue;
            const Lit cand_orig = it->second;
            if (cnf.defined(cand_orig.var())) {
                const auto& deps = cnf.get_dependent_vars_recursive(cand_orig.var(), deps_cache);
                bool has_test = false;
                for (uint32_t d : deps) {
                    if (d == test_orig.var()) { has_test = true; break; }
                }
                if (has_test) continue;
            } else {
                if (conf.unate_def_rep_aux < 2) continue;
            }
            aux_vars.push_back(v_new);
            aux_mask[v_new] = 1;
        }
    }

    assert(aux_vars.size() <= cnf.nVars());
    for (uint32_t a : aux_vars) {
        assert(a != test);
        assert(input.count(a) == 0);
        assert(a < aux_mask.size() && aux_mask[a] == 1);
    }
}

void UnateDefRep::process_test_var(const uint32_t test) {
    assert(test < cnf.nVars());
    assert(input.count(test) == 0);
    assert(already_tested.count(test) == 0);
    assert(var_to_indic.at(test) != var_Undef);
    const Lit y_test_prime = Lit(test + cnf.nVars(), false);

    const Lit test_orig = new_to_orig.at(test);
    if (cnf.defined(test_orig.var())) {
        already_tested.insert(test);
        return;
    }
    tested_num++;
    rep_stats.tests_run++;
    log_progress_periodic();
    const auto base_assumps = build_base_assumps(test);

    VERBOSE_DEBUG_DO(cout << "c o [unate_def_rep][verbose] === test NEW="
        << test+1 << " orig=" << test_orig.var()+1
        << " (sign=" << test_orig.sign() << ") ===" << endl);
    build_allowed_aux_set(test, test_orig);
    VERBOSE_DEBUG_DO({
        cout << "c o [unate_def_rep][verbose]   aux_vars (NEW): {";
        for (uint32_t a : aux_vars) cout << " " << a+1;
        cout << " }" << endl;
    });

    aig_ptr h = AIG::new_const(false);   // start from H ≡ 0
    PerVarStats vstats;

    for (uint32_t iter = 0; iter < conf.unate_def_rep_iters; iter++) {
        rep_stats.total_iters++;
        vstats.iters++;

        const Lit h_enc_lit = encode_h_in_miter(h, /*is_y_prime=*/true);

        // act_i ⇒ y_test' ⇔ h_enc_lit (gating so old encodings can be
        // disabled cheaply between iterations by adding the unit ~act_i).
        s->new_var();
        const Lit act_i = Lit(s->nVars()-1, false);
        s->add_clause({~act_i, ~y_test_prime, h_enc_lit});
        s->add_clause({~act_i,  y_test_prime, ~h_enc_lit});

        vector<Lit> as = base_assumps;
        as.push_back(act_i);

        s->set_max_confl(conf.unate_def_rep_max_confl);
        const double t_miter_start = cpuTime();
        rep_stats.miter_solve_calls++;
        const auto ret = s->solve(&as);
        rep_stats.time_miter_solve += cpuTime() - t_miter_start;

        if (ret == l_False) {
            rep_stats.miter_unsat++;
            vstats.miter_unsat++;
            if (try_commit_h(test, test_orig, h, h_enc_lit, act_i, iter, vstats)) break;
            continue;
        }
        if (ret == l_Undef) {
            rep_stats.miter_undef++;
            vstats.miter_undef++;
            s->add_clause({~act_i});
            vstats.stop_reason = "miter_undef";
            break;
        }
        rep_stats.miter_sat++;
        vstats.miter_sat++;

        const CexAction action = process_cex(test, h_enc_lit, act_i, iter, h, vstats);
        if (action == CexAction::Break) break;
        // Refine and Continue both fall through to the next iteration.
    }

    log_per_var_summary(test, h, vstats);

    already_tested.insert(test);
}

void UnateDefRep::log_progress_periodic() {
    if (tested_num % 100 != 99) return;
    verb_print(1, "[unate_def_rep] test no: " << setw(5) << tested_num
        << "/" << to_define.size()
        << " new defs: " << setw(4) << new_defs
        << " iters: " << setw(7) << rep_stats.total_iters
        << " miter[U=" << rep_stats.miter_unsat
        << " S=" << rep_stats.miter_sat
        << " T=" << rep_stats.miter_undef << "]"
        << " f[U=" << rep_stats.f_unsat
        << " S=" << rep_stats.f_sat
        << " T=" << rep_stats.f_undef << "]"
        << " skip_big=" << rep_stats.skipped_pattern_too_big
        << " T: " << setprecision(2) << fixed << (cpuTime() - t0));
}

// Called when the miter just returned UNSAT. Runs the feasibility check
// and, on success, commits y_test ⇔ H. Returns true iff we committed and
// the iter loop should break; false means infeasible/undecided and the
// caller should `continue`.
bool UnateDefRep::try_commit_h(const uint32_t test, const Lit test_orig,
                                const aig_ptr& h, const Lit h_enc_lit,
                                const Lit act, const uint32_t iter,
                                PerVarStats& vstats) {
    // Feasibility check: ask f_solver whether F' has any model with
    // y_test = h_enc. f_solver carries original F plus every prior
    // commit's y_v ⇔ H_v (mirrored on commit — see the
    // f_solver->add_clause block below), so this is checked against
    // cumulative F', not original F. SAT means H is at least sometimes
    // a Skolem witness in F'; UNSAT means H is never a valid value for
    // y_test anywhere (rules out the vacuous-miter-UNSAT case where
    // blindly committing would lose X-projections); UNDEF means
    // undecided.
    //
    // This is intentionally weaker than full uniqueness in F', but
    // strong enough to pass on bifunctional benchmarks like
    // factorization where strict uniqueness can never hold.
    // CEX-driven refinement keeps H broadly Skolem-like across the
    // iter loop, and the fuzzers exercise this path on every run.
    const Lit h_enc_in_f = encode_h_in_f(h);
    const Lit y_test_in_f = Lit(test, false);
    f_solver->new_var();
    const Lit f_act = Lit(f_solver->nVars()-1, false);
    // Under f_act: y_test_in_f ⇔ h_enc_in_f.
    f_solver->add_clause({~f_act,  y_test_in_f, ~h_enc_in_f});
    f_solver->add_clause({~f_act, ~y_test_in_f,  h_enc_in_f});
    vector<Lit> feas_assumps = {f_act};
    f_solver->set_max_confl(conf.unate_def_rep_max_confl);
    const double t_feas_solve_start = cpuTime();
    rep_stats.feas_solve_calls++;
    const auto feas_ret = f_solver->solve(&feas_assumps);
    rep_stats.time_feas_solve += cpuTime() - t_feas_solve_start;
    f_solver->add_clause({~f_act}); // disable for next iters
    if (feas_ret != l_True) {
        // Infeasible (no F'-model has y_test = H) or undecided: don't
        // commit. Continuing the iter loop refines H further via the
        // next CEX, which can move H into a feasible region.
        s->add_clause({~act});
        rep_stats.skolem_only_skipped++;
        return false;
    }

    // y_test = H(...) is a feasible Skolem witness in cumulative F'
    // (some F'-model has y_test = h_enc). This is weaker than
    // unique-defining; see the feasibility-check comment above for why
    // it is sound on bifunctional benchmarks.

    assert(h != nullptr);
    assert(!cnf.defined(test_orig.var()));
    SLOW_DEBUG_DO(
      std::set<uint32_t> h_leaves;
      AIG::get_dependent_vars(h, h_leaves,
                              std::numeric_limits<uint32_t>::max());
      for (uint32_t lf : h_leaves) {
          assert((input.count(lf)
                 || (lf < aux_mask.size() && aux_mask[lf] != 0))
              && "H leaf must be input or aux");
      }
    );
    const aig_ptr h_in_orig = AIG::translate_leaves(
        h,
        [&](uint32_t v) { return new_to_orig.at(v); },
        test_orig.sign());
    VERBOSE_DEBUG_DO(cout
        << "c o [unate_def_rep][verbose] commit test NEW=" << test+1
        << " orig=" << test_orig.var()+1
        << " sign=" << test_orig.sign()
        << " H_NEW=" << h
        << " H_ORIG=" << h_in_orig << endl);

    // set_def_skolem (vs set_def) records the var as Skolem-committed
    // so get_var_types keeps it in backward_defined even when H_test
    // happens to be a constant or input-only AIG. Otherwise downstream
    // (Manthan) would treat the var as an input and drop the
    // y_test = H_test constraint that a later var's miter UNSAT relied
    // on. The Skolem flag is semantically appropriate here too: the
    // feasibility check only confirms H is at least sometimes a Skolem
    // witness, not that F ⊨ y_test = H, so this is a Skolem-style
    // commit by definition.
    cnf.set_def_skolem(test_orig.var(), h_in_orig);

    // New def changed the dep graph; drop cached recursive deps.
    deps_cache.clear();

    SLOW_DEBUG_DO({
        release_assert(cnf.defs_invariant());
        int bad = cnf.check_synth_funs_sat();
        if (bad >= 0) {
            cout << "c o [unate_def_rep][SLOW_DEBUG] WRONG commit "
                 << "for orig var " << test_orig.var()+1
                 << " (test NEW=" << test+1 << ")"
                 << " H_NEW=" << h
                 << " H_ORIG=" << h_in_orig << endl;
        }
        release_assert(bad == 0):
    });

    // Tighten miter: y_test ⇔ H on Y side. For input-only H, h_enc_lit
    // (Y'-side encoding) and the Y-side encoding are the same SAT lit
    // since inputs are shared. For an H with any aux leaves, the two
    // sides differ when the aux var's pinning indicator is later untied
    // (e.g. when aux becomes a future `test`), so we must encode H
    // explicitly on the Y side here.
    const size_t aux_leaves = h_aux_leaf_count(h);
    const Lit h_enc_lit_for_commit = (aux_leaves == 0)
        ? h_enc_lit
        : encode_h_in_miter(h, /*is_y_prime=*/false);
    const Lit y_test = Lit(test, false);
    s->add_clause({~y_test,  h_enc_lit_for_commit});
    s->add_clause({ y_test, ~h_enc_lit_for_commit});

    // Mirror the y_test ⇔ H commit into f_solver so subsequent
    // feasibility checks for later vars operate against cumulative F'
    // (= original F ∧ all prior commits). Without this the chain of
    // Skolem-only commits wouldn't compose: a later var's "feasible in
    // F" would be checked even when the right question is "feasible in
    // F + prior committed defs". The new clauses are exactly the
    // equivalence we just committed on the s side. The Tseitin chain
    // for H is already in f_solver from the feasibility check above.
    f_solver->add_clause({~y_test_in_f,  h_enc_in_f});
    f_solver->add_clause({ y_test_in_f, ~h_enc_in_f});

    // Defer materializing y_test ⇔ H into cnf clauses until after the
    // per-test loop. cnf.new_var() allocations during the loop would
    // shift cnf.nVars(), and that offset is the anchor for the Y'-side
    // encoding in the miter solver `s` (e.g. Lit(test + cnf.nVars(),
    // false) at the indicator setup). The materialization is only
    // needed downstream by find_better_ctx_normal, which runs inside
    // Manthan after synthesis_unate_def_rep returns — so deferring is
    // sound and avoids threading a "frozen" cnf var count through every
    // Y'-offset use site.
    deferred_materialize.emplace_back(test, h);

    // Lock activation TRUE so the Y'-side equality stays in force for
    // subsequent tests.
    s->add_clause({act});
    new_defs++;
    const uint32_t hit_iter = iter + 1;
    rep_stats.hits++;
    rep_stats.hit_iter_sum += hit_iter;
    if (hit_iter > rep_stats.hit_iter_max) rep_stats.hit_iter_max = hit_iter;
    {
        const size_t nodes = AIG::count_aig_nodes_fast(h);
        rep_stats.hit_aig_nodes_sum += nodes;
        if (nodes > rep_stats.hit_aig_nodes_max) rep_stats.hit_aig_nodes_max = nodes;
    }
    if (aux_leaves > 0) {
        rep_stats.hits_using_aux++;
        rep_stats.aux_leaves_sum += aux_leaves;
        if (aux_leaves > rep_stats.aux_leaves_max)
            rep_stats.aux_leaves_max = aux_leaves;
    }
    vstats.stop_reason = "found";
    return true;
}

// Greedy literal-drop minimization on the F-only conflict. Manthan's
// `minimize_conflict` adapted for the unate_def_rep setting where the
// "to_repair" lit is `force_wrong = Lit(test, h_val == FALSE)` and the
// pattern lits are the negated conflict lits in input ∪ aux.
//
// Loop: walk pattern_lits, attempt to drop each one and re-solve with
// the remaining lits + force_wrong assumed. UNSAT-with-~force_wrong-
// in-conflict ⇒ replace pattern with the smaller conflict; otherwise
// pin the lit (unable to remove). Repeat until a full pass removes
// nothing or the budget is exhausted.
//
// Aux lits are sorted to the front so the minimizer prefers dropping
// aux first — input-only patterns produce smaller, simpler H AIGs at
// commit, and an input-only H avoids the Y-side encode for aux on
// commit (h_aux_leaf_count == 0 → reuse h_enc_lit).
void UnateDefRep::minimize_pattern(vector<Lit>& pattern_lits,
                                    const Lit force_wrong,
                                    PerVarStats& vstats) {
    if (conf.unate_def_rep_minim == 0) return;
    if (pattern_lits.size() <= 1) return;

    rep_stats.minim_attempts++;
    vstats.minim_attempts++;
    const size_t orig_sz = pattern_lits.size();
    rep_stats.minim_lits_in += orig_sz;

    auto is_in_pat_set = [&](const Lit& l) {
        const bool is_input_l = input.count(l.var()) > 0;
        const bool is_aux_l = l.var() < aux_mask.size() && aux_mask[l.var()] != 0;
        return is_input_l || is_aux_l;
    };

    // Sort: drop aux first (so we'd rather lose aux than input lits if
    // both are removable). Stable to avoid run-to-run reordering.
    std::stable_sort(pattern_lits.begin(), pattern_lits.end(),
        [this](const Lit& a, const Lit& b) {
            const bool a_in = input.count(a.var()) > 0;
            const bool b_in = input.count(b.var()) > 0;
            if (a_in != b_in) return !a_in; // aux first
            return a.var() < b.var();       // deterministic
        });

    std::set<Lit> dont_remove;
    uint32_t budget_left = conf.unate_def_rep_minim_budget;
    bool removed_any = true;
    while (removed_any && budget_left > 0 && pattern_lits.size() > 1) {
        removed_any = false;
        for (size_t i = 0; i < pattern_lits.size(); i++) {
            if (budget_left == 0) break;
            const Lit candidate = pattern_lits[i];
            if (dont_remove.count(candidate)) continue;
            VERBOSE_DEBUG_DO(cout
                << "c o [unate_def_rep][minim] try drop " << candidate
                << " from pat sz=" << pattern_lits.size() << endl);
            vector<Lit> as;
            as.reserve(pattern_lits.size());
            for (size_t j = 0; j < pattern_lits.size(); j++) {
                if (i == j) continue;
                as.push_back(pattern_lits[j]);
            }
            as.push_back(force_wrong);
            f_solver->set_max_confl(conf.unate_def_rep_max_confl);
            const double t = cpuTime();
            rep_stats.f_solve_calls++;
            rep_stats.minim_solver_calls++;
            budget_left--;
            const auto r = f_solver->solve(&as);
            const double dt = cpuTime() - t;
            rep_stats.time_f_solve += dt;
            rep_stats.time_minim += dt;
            if (r != l_False) {
                dont_remove.insert(candidate);
                continue;
            }
            // Build a new pattern from the conflict, restricted to
            // input ∪ aux assumption-form lits and excluding force_wrong.
            const auto cf = f_solver->get_conflict();
            bool has_fw = false;
            for (const auto& cl : cf) if (cl == ~force_wrong) { has_fw = true; break; }
            if (!has_fw) {
                // Conflict doesn't depend on force_wrong; this would
                // give us a useless (vacuous) pattern — pin and move on.
                dont_remove.insert(candidate);
                continue;
            }
            vector<Lit> new_pat;
            new_pat.reserve(cf.size());
            for (const auto& cl : cf) {
                if (cl == ~force_wrong) continue;
                if (cl.var() == force_wrong.var()) continue;
                if (!is_in_pat_set(~cl)) continue;
                new_pat.push_back(~cl);
            }
            // Defensive: if the solver gave us back the same set or
            // bigger, treat as a non-removal.
            if (new_pat.size() >= pattern_lits.size()) {
                dont_remove.insert(candidate);
                continue;
            }
            VERBOSE_DEBUG_DO(cout
                << "c o [unate_def_rep][minim]   removed; pat sz "
                << pattern_lits.size() << " -> " << new_pat.size() << endl);
            vstats.minim_lits_dropped += pattern_lits.size() - new_pat.size();
            pattern_lits = std::move(new_pat);
            removed_any = true;
            break;
        }
    }
    rep_stats.minim_lits_out += pattern_lits.size();
    if (pattern_lits.size() < orig_sz) rep_stats.minim_succeeded++;
}

// One SAT call dropping every aux lit from the pattern at once.
// If the pure-input subset still UNSATs with `force_wrong` in the
// conflict, replace `pattern_lits` with the input-only conflict.
// Manthan's "drop y-vars from conflict" — much cheaper than greedy
// elimination when the aux lits are jointly redundant.
void UnateDefRep::drop_aux_oneshot(vector<Lit>& pattern_lits,
                                    const Lit force_wrong,
                                    [[maybe_unused]] PerVarStats& vstats) {
    if (conf.unate_def_rep_drop_aux == 0) return;
    if (pattern_lits.size() <= 1) return;
    // Are there any aux lits to drop? If pattern is already input-only,
    // skip — saves one SAT call per CEX on benchmarks where aux mode is 0
    // or where minim already removed all aux.
    bool any_aux = false;
    for (const Lit& l : pattern_lits) {
        if (input.count(l.var()) == 0) { any_aux = true; break; }
    }
    if (!any_aux) return;
    rep_stats.dropaux_attempts++;
    const size_t orig_sz = pattern_lits.size();
    vector<Lit> as;
    as.reserve(pattern_lits.size());
    for (const Lit& l : pattern_lits) {
        if (input.count(l.var()) == 0) continue;
        as.push_back(l);
    }
    if (as.empty()) return; // nothing to assume; would be vacuous
    as.push_back(force_wrong);
    f_solver->set_max_confl(conf.unate_def_rep_max_confl);
    const double t = cpuTime();
    rep_stats.f_solve_calls++;
    rep_stats.minim_solver_calls++;
    const auto r = f_solver->solve(&as);
    const double dt = cpuTime() - t;
    rep_stats.time_f_solve += dt;
    rep_stats.time_minim += dt;
    if (r != l_False) return;
    const auto cf = f_solver->get_conflict();
    bool has_fw = false;
    for (const auto& cl : cf) if (cl == ~force_wrong) { has_fw = true; break; }
    if (!has_fw) return;
    vector<Lit> new_pat;
    new_pat.reserve(cf.size());
    for (const auto& cl : cf) {
        if (cl == ~force_wrong) continue;
        if (cl.var() == force_wrong.var()) continue;
        if (input.count(cl.var()) == 0) continue; // strictly input-only
        new_pat.push_back(~cl);
    }
    if (new_pat.size() >= pattern_lits.size()) return;
    VERBOSE_DEBUG_DO(cout
        << "c o [unate_def_rep][drop_aux] dropped aux: "
        << pattern_lits.size() << " -> " << new_pat.size() << endl);
    rep_stats.dropaux_lits_dropped += orig_sz - new_pat.size();
    rep_stats.dropaux_succeeded++;
    pattern_lits = std::move(new_pat);
}

// Called when the miter just returned SAT. Runs the F-only CEX call,
// extracts the input/aux pattern from the conflict, and refines `h`
// in-place. Returns Break if the iter loop should stop, Continue if
// the iteration should be skipped (no useful refinement), or Refine on
// successful refinement.
UnateDefRep::CexAction UnateDefRep::process_cex(const uint32_t test, const Lit h_enc_lit,
     const Lit act, [[maybe_unused]] uint32_t iter, aig_ptr& h, PerVarStats& vstats) {
    // CEX. Extract values of test (F-side) and h_enc_lit (forced to H(X*) by `act`)
    const auto& model = s->get_model();
    const lbool y_test_val_f = model[test];
    const lbool h_val        = model_value(model, h_enc_lit);
    assert(y_test_val_f != l_Undef && h_val != l_Undef);
    assert(y_test_val_f != h_val && "Miter SAT must have F-side y_test differ from H(X) "
           "(ensured by indicator_test = FALSE in base_assumps)");

    // F-only call: assume (X*, aux*) values and force y_test = H(...)
    // (the wrong value in F's view).
    // sign convention: Lit(v, true)= ¬v, so Lit(test, h_val == l_False)
    // = (h_val == TRUE ? test : ¬test) — exactly "y_test = H_val".
    const Lit force_wrong = Lit(test, h_val == l_False);

    // Manthan's "input-only conflict first": pin only X to the miter
    // model, force y_test wrong, and try UNSAT. If F is already
    // contradicted by inputs alone, the resulting pattern lives over
    // inputs (smaller H, no Y-side aux encode at commit). Falls back
    // to the input+aux assumption block on SAT or budget. This is
    // weaker than minim (we may even produce a still-large pattern),
    // but a hit here makes the subsequent minim run on a strictly
    // input-shape pattern.
    const bool inp_first_enabled =
        (conf.unate_def_rep_input_only_first == 1) ||
        (conf.unate_def_rep_input_only_first == 2 && !aux_vars.empty());
    bool got_input_only_unsat = false;
    vector<Lit> f_assumps;
    f_assumps.reserve(input.size() + aux_vars.size() + 1);
    if (inp_first_enabled) {
        rep_stats.inpfirst_attempts++;
        vector<Lit> input_assumps;
        input_assumps.reserve(input.size() + 1);
        for (uint32_t x : input) {
            const lbool val = model.at(x);
            assert(val != l_Undef);
            input_assumps.emplace_back(x, val == l_False);
        }
        input_assumps.push_back(force_wrong);
        f_solver->set_max_confl(conf.unate_def_rep_max_confl);
        const double t = cpuTime();
        rep_stats.f_solve_calls++;
        const auto r0 = f_solver->solve(&input_assumps);
        rep_stats.time_f_solve += cpuTime() - t;
        if (r0 == l_False) {
            // Conflict over inputs alone: confirm force_wrong is in it
            // (otherwise the conflict is unrelated). On hit, skip the
            // input+aux call entirely and use this conflict.
            const auto cf0 = f_solver->get_conflict();
            bool has_fw = false;
            for (const auto& cl : cf0) if (cl == ~force_wrong) { has_fw = true; break; }
            if (has_fw) {
                rep_stats.inpfirst_unsat++;
                got_input_only_unsat = true;
                f_assumps = std::move(input_assumps);
            } else {
                // Treat as SAT for accounting; we'll do the full call
                // below.
                rep_stats.inpfirst_sat++;
            }
        } else if (r0 == l_True) {
            rep_stats.inpfirst_sat++;
        } else {
            rep_stats.inpfirst_undef++;
        }
    }

    lbool f_ret = l_Undef;
    if (got_input_only_unsat) {
        // Reuse the input-only UNSAT result; conflict already extractable
        // from f_solver state.
        f_ret = l_False;
    } else {
        for (uint32_t x : input) {
            const lbool val = model.at(x);
            assert(val != l_Undef);
            f_assumps.emplace_back(x, val == l_False);
        }
        // Aux assumptions: pin aux vars to their miter-model values. In the
        // F-solver these vars are otherwise free (the F-solver has no
        // AIG-copy block / indicator structure), so without this pin a CEX
        // where bifunctionality lives in an aux var would surface as a
        // cost-zero alarm.
        for (uint32_t a : aux_vars) {
            const lbool val = model.at(a);
            assert(val != l_Undef);
            f_assumps.emplace_back(a, val == l_False);
        }
        f_assumps.push_back(force_wrong);

        f_solver->set_max_confl(conf.unate_def_rep_max_confl);
        const double t_f_start = cpuTime();
        rep_stats.f_solve_calls++;
        f_ret = f_solver->solve(&f_assumps);
        rep_stats.time_f_solve += cpuTime() - t_f_start;
    }

    // Disable this iteration's activation regardless of outcome.
    s->add_clause({~act});

    if (f_ret == l_True) {
        // Cost-zero: H(X*) is valid in F (some y_other admits it). The
        // miter SAT was an artifact of forcing y_other = y_other'. No
        // safe pattern direction — give up on this var after a few
        // attempts (a single y_other-tied CEX rarely yields a useful
        // pointwise pattern, so we don't bother trying the tighter
        // [X*, y_other*, force_wrong] query: in practice it produces
        // large mixed conflicts whose input projection is rarely the
        // right pattern, and burns iteration budget).
        rep_stats.f_sat++;
        vstats.f_sat++;
        vstats.costzero_count++;
        if (vstats.costzero_count >= conf.unate_def_rep_max_costzero) {
            verb_print(3, "[unate_def_rep] giving up on test " << test+1
                << " after " << vstats.costzero_count << " cost-zero CEXes");
            vstats.stop_reason = "costzero_limit";
            return CexAction::Break;
        }
        return CexAction::Continue;
    }
    if (f_ret == l_Undef) {
        rep_stats.f_undef++;
        vstats.f_undef++;
        vstats.stop_reason = "f_undef";
        return CexAction::Break;
    }
    // f_ret == l_False
    rep_stats.f_unsat++;
    vstats.f_unsat++;

    // Conflict literals are negations of assumed literals. Filter out
    // the test-forcing one; everything else is an input or aux lit (we
    // only assumed input ∪ aux + force_wrong).
    vector<Lit> conflict = f_solver->get_conflict();
    vector<Lit> pattern_lits;
    pattern_lits.reserve(conflict.size());
    for (const Lit& cl : conflict) {
        if (cl == ~force_wrong) continue;
        if (cl.var() == test) continue; // defensive
        const bool is_input = input.count(cl.var()) > 0;
        const bool is_aux = cl.var() < aux_mask.size()
                            && aux_mask[cl.var()] != 0;
        if (!is_input && !is_aux) continue;
        pattern_lits.push_back(~cl);    // assumption form: matches X*
    }
    // Greedy minimization on the conflict before counting / size-gating.
    // Shrinks the pattern, generalising H and shrinking AIG growth.
    minimize_pattern(pattern_lits, force_wrong, vstats);
    // After greedy minim, attempt a single-shot "drop all aux" pass.
    // Cheap fallback for benchmarks where aux is jointly redundant
    // but greedy didn't remove it pair-by-pair.
    drop_aux_oneshot(pattern_lits, force_wrong, vstats);
    vstats.pattern_sum += pattern_lits.size();
    vstats.pattern_count++;
    // Cheap invariant: pattern lits live in input ∪ aux (filter above
    // ensures this). If a non-allowed lit ever leaks through it would
    // make H reference an out-of-scope leaf and break the structural
    // soundness check at commit time.
    for (const Lit& pl : pattern_lits) {
        assert(pl.var() != test);
        assert(input.count(pl.var())
            || (pl.var() < aux_mask.size() && aux_mask[pl.var()] != 0));
    }
    if (pattern_lits.size() > conf.unate_def_rep_max_pattern) {
        rep_stats.skipped_pattern_too_big++;
        vstats.skipped_big++;
        // Same accounting as cost-zero: too-large patterns lead to
        // explosive AIG growth without much generalization.
        vstats.costzero_count++;
        if (vstats.costzero_count >= conf.unate_def_rep_max_costzero) {
            vstats.stop_reason = "costzero_limit";
            return CexAction::Break;
        }
        return CexAction::Continue;
    }

    aig_ptr pattern;
    if (pattern_lits.empty()) {
        // Empty conflict implies F unconditionally forces
        // y_test ≠ H_val — i.e. y_test is a constant we somehow missed
        // in the standard unate test. Refine with a constant.
        pattern = AIG::new_const(true);
    } else {
        pattern = AIG::new_lit(pattern_lits[0].var(), pattern_lits[0].sign());
        for (size_t i = 1; i < pattern_lits.size(); i++) {
            pattern = AIG::new_and(pattern,
                AIG::new_lit(pattern_lits[i].var(), pattern_lits[i].sign()));
        }
    }
    VERBOSE_DEBUG_DO({
        cout << "c o [unate_def_rep][verbose]   iter=" << iter
             << " y_test_val_f=" << y_test_val_f
             << " pattern={ ";
        for (const auto& pl : pattern_lits) cout << pl << " ";
        cout << "} pattern_AIG=" << pattern << endl;
    });

    // Cover X*: when P(X) holds, set H = y_test_val_f there.
    if (y_test_val_f == l_True)  h = AIG::new_or(h, pattern);
    else                         h = AIG::new_and(h, AIG::new_not(pattern));
    VERBOSE_DEBUG_DO(cout << "c o [unate_def_rep][verbose]   H_NEW after refine=" << h << endl);
    return CexAction::Refine;
}

void UnateDefRep::log_per_var_summary(uint32_t test, const aig_ptr& h,
                                       const PerVarStats& vstats) {
    const size_t v_aux_leaves = h_aux_leaf_count(h);
    verb_print(1, "[unate_def_rep] v " << setw(5) << test+1
        << " iters="     << setw(5) << vstats.iters
        << " miter[U="   << setw(3) << vstats.miter_unsat
        << " S="         << setw(3) << vstats.miter_sat
        << " T="         << setw(3) << vstats.miter_undef << "]"
        << " f[U="       << setw(3) << vstats.f_unsat
        << " S="         << setw(3) << vstats.f_sat
        << " T="         << setw(3) << vstats.f_undef << "]"
        << " skip_big="  << setw(3) << vstats.skipped_big
        << " costzero="  << setw(3) << vstats.costzero_count
        << " avg_pat="   << setw(5) << setprecision(1) << fixed
                         << safe_div(vstats.pattern_sum, vstats.pattern_count)
        << " minim["     << setw(2) << vstats.minim_attempts
        << "/-"          << setw(3) << vstats.minim_lits_dropped << "]"
        << " aux["       << setw(4) << aux_vars.size()
        << "/used="      << setw(3) << v_aux_leaves << "]"
        << " AIG_nodes=" << setw(5) << AIG::count_aig_nodes_fast(h)
        << " " << COLCYN << std::left << setw(15) << vstats.stop_reason << std::right << COLDEF
        << " T: " << fixed << setprecision(2) << (cpuTime()-t0));
}

void UnateDefRep::materialize_deferred() {
    // Materialize all deferred y_test ⇔ H equivalences into cnf clauses.
    // Safe to grow cnf.nVars() now: the per-test loop has finished and the
    // miter solver `s` (which depended on cnf.nVars() for Y'-side offsets)
    // is no longer used after this point.
    for (const auto& [test_v, h_aig] : deferred_materialize) {
        const Lit h_enc_in_cnf = materialize_h_in_cnf(h_aig);
        const Lit y_test_in_cnf = Lit(test_v, false);
        cnf.add_clause({~y_test_in_cnf,  h_enc_in_cnf});
        cnf.add_clause({ y_test_in_cnf, ~h_enc_in_cnf});
    }
}

void UnateDefRep::log_pass_summary() {
    auto [input2, to_define2, backward_defined2] = cnf.get_var_types(
        0 | verbose_debug_enabled, "end do_unate_def_rep");
    verb_print(1, COLRED "[unate_def_rep] Done."
        << " tests: " << setw(5) << rep_stats.tests_run
        << " hits: " << setw(5) << rep_stats.hits
        << " iters: " << setw(7) << rep_stats.total_iters
        << " miter[U=" << rep_stats.miter_unsat
        << " S=" << rep_stats.miter_sat
        << " T=" << rep_stats.miter_undef << "]"
        << " f[U=" << rep_stats.f_unsat
        << " S=" << rep_stats.f_sat
        << " T=" << rep_stats.f_undef << "]"
        << " skip_big=" << rep_stats.skipped_pattern_too_big
        << " skolem_skip=" << rep_stats.skolem_only_skipped
        << " avg_hit_iter=" << setprecision(1) << fixed
        << safe_div(rep_stats.hit_iter_sum, rep_stats.hits)
        << " max_hit_iter=" << rep_stats.hit_iter_max
        << " avg_hit_aig=" << setprecision(1) << fixed
        << safe_div(rep_stats.hit_aig_nodes_sum, rep_stats.hits)
        << " max_hit_aig=" << rep_stats.hit_aig_nodes_max
        << " aux_hits=" << rep_stats.hits_using_aux
        << " avg_aux_leaves=" << setprecision(1) << fixed
        << safe_div(rep_stats.aux_leaves_sum, rep_stats.hits_using_aux)
        << " max_aux_leaves=" << rep_stats.aux_leaves_max
        << " still to-define: " << to_define2.size()
        << " T: " << setprecision(2) << fixed << rep_stats.time_total);
    verb_print(1, COLRED "[unate_def_rep] time breakdown:"
        << " encode_h_visited=" << rep_stats.encode_h_nodes_visited
            << " encode_h_and=" << rep_stats.encode_h_nodes_emitted
            << " encode_h_in_f_and=" << rep_stats.encode_h_in_f_emitted
        << " miter_solve=" << setprecision(2) << fixed << rep_stats.time_miter_solve
            << "(calls=" << rep_stats.miter_solve_calls << ")"
        << " feas_solve=" << rep_stats.time_feas_solve
            << "(calls=" << rep_stats.feas_solve_calls << ")"
        << " f_solve=" << rep_stats.time_f_solve
            << "(calls=" << rep_stats.f_solve_calls << ")"
        << " minim_t=" << rep_stats.time_minim
            << "(calls=" << rep_stats.minim_solver_calls
            << " att=" << rep_stats.minim_attempts
            << " ok=" << rep_stats.minim_succeeded
            << " sz_in=" << rep_stats.minim_lits_in
            << " sz_out=" << rep_stats.minim_lits_out << ")"
        << " inpfirst[att=" << rep_stats.inpfirst_attempts
            << " U=" << rep_stats.inpfirst_unsat
            << " S=" << rep_stats.inpfirst_sat
            << " T=" << rep_stats.inpfirst_undef << "]"
        << " dropaux[att=" << rep_stats.dropaux_attempts
            << " ok=" << rep_stats.dropaux_succeeded
            << " lits=" << rep_stats.dropaux_lits_dropped << "]");
}

void UnateDefRep::run() {
    rep_stats = UnateDefRepStats{};
    const double my_time = cpuTime();

    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate_def_rep")
        .unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[unate_def_rep] No variables to-define, skipping");
        return;
    }

    s = setup_f_not_f(cnf, input, conf);
    new_to_orig = cnf.get_new_to_orig_var();
    aux_mask.assign(cnf.nVars(), 0);
    t0 = my_time;

    // ---- Y'-side defs for already-defined vars (mirror of synthesis_unate_def).
    setup_yprime_backward_defs();

    // ---- Indicators for to-define vars.
    build_indicators();

    // ---- F-only solver, used to find input-only conflicts ("why F forces
    //      y_test ≠ H(X*) under X*"). Built once, queried per CEX.
    build_f_solver();

    for (uint32_t test : to_define) process_test_var(test);

    materialize_deferred();

    rep_stats.time_total = cpuTime() - my_time;
    // SLOW_DEBUG: end-of-pass sanity. defs_invariant() catches anything
    // a per-commit slipped (cycles, dangling deps, bad sampling-var
    // categorization) and fails fast at the pass boundary instead of
    // at a downstream consumer.
    SLOW_DEBUG_DO({
        [[maybe_unused]] auto inv_ok = cnf.defs_invariant();
    });
    log_pass_summary();
}

}
