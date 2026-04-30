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
//         - UNSAT → y_test = H is a valid Skolem; commit and stop.
//         - SAT   → CEX. y_test_F = m[test] is a value F admits at X*;
//                   H(...) = m[H_top_lit] is the value the activation
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
//      tests untie an aux var's pinning indicator).
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

#include "unate_def.h"
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

namespace {

// Translate H from NEW-var-space to ORIG-var-space. Leaf sign flips combine
// the leaf var's own NEW→ORIG sign offset and the output sign offset of the
// def's var (`test_orig.sign()`) applied at the end.
aig_ptr translate_to_orig(const aig_ptr& aig,
                          const map<uint32_t, Lit>& new_to_orig,
                          bool out_sign_xor) {
    auto visit = [&](AIGT type, uint32_t var,
                     const aig_ptr* left, const aig_ptr* right) -> aig_ptr {
        if (type == AIGT::t_const) return AIG::new_const(true);
        if (type == AIGT::t_lit) {
            auto it = new_to_orig.find(var);
            assert(it != new_to_orig.end());
            const Lit l = it->second;
            return AIG::new_lit(l.var(), l.sign());
        }
        if (type == AIGT::t_and) {
            return AIG::new_and(*left, *right);
        }
        release_assert(false && "Unhandled AIG type in translate_to_orig");
    };
    map<aig_ptr, aig_ptr> cache;
    aig_ptr ret = AIG::transform<aig_ptr>(aig, visit, cache);
    if (out_sign_xor) ret = ~ret;
    return ret;
}

// Resolve the lbool value of a Lit against a SAT model.
inline lbool model_value(const vector<lbool>& m, const Lit l) {
    if (l.var() >= m.size()) return l_Undef;
    lbool v = m[l.var()];
    if (v == l_Undef) return l_Undef;
    return l.sign() ? (v == l_True ? l_False : l_True) : v;
}

} // namespace

void Unate::synthesis_unate_def_rep(SimplifiedCNF& cnf) {
    rep_stats = UnateDefRepStats{};
    const double my_time = cpuTime();

    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate_def_rep")
        .unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[unate_def_rep] No variables to-define, skipping");
        return;
    }

    auto s = setup_f_not_f(cnf);

    // ---- Y'-side defs for already-defined vars (mirror of synthesis_unate_def).
    const auto new_to_orig = cnf.get_new_to_orig_var();
    Lit true_lit = lit_Undef;
    auto get_true_lit = [&]() -> Lit {
        if (true_lit == lit_Undef) {
            s->new_var();
            true_lit = Lit(s->nVars()-1, false);
            s->add_clause({true_lit});
        }
        return true_lit;
    };

    for (const auto& i_new : backward_defined) {
        if (input.count(i_new)) continue;
        assert(new_to_orig.count(i_new) > 0);
        const Lit orig = new_to_orig.at(i_new);
        const auto& aig = cnf.get_def(orig.var());
        assert(aig != nullptr && "Already-defined var must have an AIG definition");

        vector<Lit> tmp;
        std::function<Lit(AIGT, uint32_t, const Lit*, const Lit*)> aig_to_copy_visitor =
          [&](AIGT type, const uint32_t var_orig,
              const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) return get_true_lit();
            if (type == AIGT::t_lit) {
                const Lit lit_new = cnf.orig_to_new_lit(Lit(var_orig, false));
                if (input.count(lit_new.var())) return lit_new;
                assert(lit_new.var() < cnf.nVars());
                return Lit(lit_new.var() + cnf.nVars(), lit_new.sign());
            }
            if (type == AIGT::t_and) {
                const Lit l_lit = *left;
                const Lit r_lit = *right;
                s->new_var();
                const Lit and_out = Lit(s->nVars() - 1, false);
                tmp = {~and_out, l_lit};       s->add_clause(tmp);
                tmp = {~and_out, r_lit};       s->add_clause(tmp);
                tmp = {~l_lit, ~r_lit, and_out}; s->add_clause(tmp);
                return and_out;
            }
            release_assert(false && "Unhandled AIG type in synthesis_unate_def_rep");
          };
        map<aig_ptr, Lit> cache;
        const Lit out_lit = AIG::transform<Lit>(aig, aig_to_copy_visitor, cache);
        const Lit out_in_new_space = out_lit ^ orig.sign();
        const Lit i_copy = Lit(i_new + cnf.nVars(), false);
        s->add_clause({~i_copy, out_in_new_space});
        s->add_clause({i_copy, ~out_in_new_space});
    }

    // ---- Indicators for to-define vars.
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

    // ---- F-only solver, used to find input-only conflicts ("why F forces
    //      y_test ≠ H(X*) under X*"). Built once, queried per CEX.
    auto f_solver = make_unique<ArjunInt::MetaSolver>();
    f_solver->new_vars(cnf.nVars());
    f_solver->set_verbosity(0);
    for (const auto& cl : cnf.get_clauses()) f_solver->add_clause(cl);

    // ---- H Tseitin encoder. `is_y_prime` selects which side the leaf SAT
    //      vars live on. Input leaves are shared between Y and Y' (same SAT
    //      var). Non-input leaves (aux) live on separate vars per side; the
    //      pinning indicator (asserted in base_assumps for every other
    //      to-define var) keeps `y == y'` so both encodings agree on leaf
    //      values. AND helpers are freshly allocated per call.
    auto encode_h = [&](const aig_ptr& h, bool is_y_prime) -> Lit {
        vector<Lit> tmp;
        auto visit = [&](AIGT type, uint32_t var,
                         const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) return get_true_lit();
            if (type == AIGT::t_lit) {
                // var is in NEW-var space.
                if (input.count(var)) return Lit(var, false);
                return Lit(is_y_prime ? var + cnf.nVars() : var, false);
            }
            if (type == AIGT::t_and) {
                s->new_var();
                const Lit out = Lit(s->nVars()-1, false);
                tmp = {~out, *left};        s->add_clause(tmp);
                tmp = {~out, *right};       s->add_clause(tmp);
                tmp = {~*left, ~*right, out}; s->add_clause(tmp);
                return out;
            }
            release_assert(false && "Unhandled AIG type in encode_h");
        };
        map<aig_ptr, Lit> cache;
        return AIG::transform<Lit>(h, visit, cache);
    };

    // Count distinct non-input leaves of `h`. Used both as a "do we need
    // a Y-side encoding on commit?" check and for telemetry.
    auto h_aux_leaf_count = [&](const aig_ptr& h) -> size_t {
        std::set<uint32_t> deps;
        AIG::get_dependent_vars(h, deps,
                                std::numeric_limits<uint32_t>::max());
        size_t n = 0;
        for (uint32_t d : deps) if (!input.count(d)) n++;
        return n;
    };

    // Lazy true-lit in f_solver, allocated on first use.
    Lit f_true_lit = lit_Undef;
    auto get_f_true_lit = [&]() -> Lit {
        if (f_true_lit == lit_Undef) {
            f_solver->new_var();
            f_true_lit = Lit(f_solver->nVars()-1, false);
            f_solver->add_clause({f_true_lit});
        }
        return f_true_lit;
    };

    // Tseitin-encode H into f_solver. Leaves are direct F-vars (inputs and
    // aux). AND helpers are fresh vars in f_solver. Returns the top lit.
    // Used to verify that H is *unique-defining* under F (`F ⊨ y_test = H`)
    // before committing — the miter UNSAT only proves the Skolem property
    // (F-sat ⇒ exists F-sat with y_test = H), but Manthan's BW-vars-have-
    // unique-defs assumption needs the stronger uniqueness so y[BW] =
    // y_hat[BW] holds in every F-sat model and find_better_ctx never has
    // to "fix" a BW var.
    auto encode_h_in_f = [&](const aig_ptr& h) -> Lit {
        vector<Lit> tmp;
        auto visit = [&](AIGT type, uint32_t var,
                         const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) return get_f_true_lit();
            if (type == AIGT::t_lit) {
                // var is in NEW-var space and is also an F-var (inputs and
                // backward-defined aux are both F-vars in f_solver).
                return Lit(var, false);
            }
            if (type == AIGT::t_and) {
                f_solver->new_var();
                const Lit out = Lit(f_solver->nVars()-1, false);
                tmp = {~out, *left};        f_solver->add_clause(tmp);
                tmp = {~out, *right};       f_solver->add_clause(tmp);
                tmp = {~*left, ~*right, out}; f_solver->add_clause(tmp);
                return out;
            }
            release_assert(false && "Unhandled AIG type in encode_h_in_f");
        };
        map<aig_ptr, Lit> cache;
        return AIG::transform<Lit>(h, visit, cache);
    };

    vector<Lit> assumps;
    set<uint32_t> already_tested;
    uint32_t tested_num = 0;
    uint32_t new_defs = 0;

    // Per-test "aux" leaf candidates. NEW-var-space, sorted ascending for
    // determinism. `aux_mask[v] == 1` iff v is in the current test's
    // aux set (used for fast filtering of conflict-core lits).
    vector<uint32_t> aux_vars;
    vector<char> aux_mask(cnf.nVars(), 0);
    // Recursive-deps cache for the cycle check on backward-defined aux
    // candidates. Cleared after every successful commit since the new
    // def changes deps.
    map<uint32_t, vector<uint32_t>> deps_cache;

    for (uint32_t test : to_define) {
        // Cheap invariants documenting what the loop assumes about `test`:
        //   - it's a real var index;
        //   - it's not an input (those never need a Skolem);
        //   - it's not in already_tested (each var goes through the loop
        //     body at most once);
        //   - it has an indicator (built in the prelude for every to_define
        //     non-input non-original-BW var).
        assert(test < cnf.nVars());
        assert(input.count(test) == 0);
        assert(already_tested.count(test) == 0);
        assert(var_to_indic.at(test) != var_Undef);
        // Skip if a previous pass already defined this (e.g. an earlier
        // iteration of THIS pass, via cnf.set_def on a different orig var
        // that resolves to the same new var — defensive only).
        const Lit test_orig = new_to_orig.at(test);
        if (cnf.defined(test_orig.var())) {
            already_tested.insert(test);
            // Note: we do NOT lock var_to_indic[test] = TRUE here. With
            // aux-leaf H's, locking indicator-prev creates a soundness bug
            // (the locked indicator chains through Y- and Y'-side prev
            // commits and spuriously pins y_t_Y = y_t_Y' during a later
            // test=t whose var appears as aux in some prior H). The Y/Y'-
            // side commit clauses by themselves already pin y_prev to its
            // committed H on each side, which is all we need. See the
            // commit-time block below for the same convention.
            continue;
        }
        tested_num++;
        rep_stats.tests_run++;

        if (tested_num % 100 == 99) {
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
                << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
        }

        // Indicator assumptions: TRUE for every other to-define var that hasn't
        // been pinned yet. Same exclusion logic as synthesis_unate_def.
        vector<Lit> base_assumps;
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
        //
        // Required because we no longer lock indicator-prev for previously
        // committed tests (see end-of-test commit comment): without that
        // lock, prev's Y- and Y'-side H-commits can place y_prev_Y vs
        // y_prev_Y' freely, so a miter SAT could otherwise have y_test_Y
        // == h_val with ¬F-on-Y' achieved through y_prev divergence — a
        // CEX with no useful refinement direction. Asserting indicator_test
        // = FALSE rules that case out and keeps the SAT/UNSAT split
        // matching the soundness condition (see header comment).
        const auto ind_test = var_to_indic.at(test);
        assert(ind_test != var_Undef);
        base_assumps.emplace_back(ind_test, true);

        // Build per-test aux leaf set. A var `v` ≠ test, not in input, may be
        // used as an H-leaf iff committing `test = H(..., v)` does NOT close
        // a dependency cycle. For backward-defined `v` we check via the
        // recursive-deps cache; for currently-undefined to-define `v` there
        // is no current cycle (Manthan's set_depends_on tracks the new edge
        // and avoids closing it later).
        VERBOSE_DEBUG_DO(std::cout << "c o [unate_def_rep][verbose] === test NEW="
            << test+1 << " orig=" << test_orig.var()+1
            << " (sign=" << test_orig.sign() << ") ===" << std::endl);
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
                    const auto& deps = cnf.get_dependent_vars_recursive(
                        cand_orig.var(), deps_cache);
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
        // Cheap aux invariants: aux candidates are always non-input,
        // non-self, distinct (we only pushed once per v_new in the
        // single-pass loop above), and aux_mask agrees with aux_vars.
        assert(aux_vars.size() <= cnf.nVars());
        for (uint32_t a : aux_vars) {
            assert(a != test);
            assert(input.count(a) == 0);
            assert(a < aux_mask.size() && aux_mask[a] == 1);
        }
        VERBOSE_DEBUG_DO({
            std::cout << "c o [unate_def_rep][verbose]   aux_vars (NEW): {";
            for (uint32_t a : aux_vars) std::cout << " " << a+1;
            std::cout << " }" << std::endl;
        });

        aig_ptr h = AIG::new_const(false);   // start from H ≡ 0
        uint32_t costzero_count = 0;
        uint32_t hit_iter = 0;

        // Per-var diagnostics for the verb=2 trace.
        uint32_t v_iters = 0;
        uint32_t v_miter_sat = 0, v_miter_unsat = 0, v_miter_undef = 0;
        uint32_t v_f_sat = 0, v_f_unsat = 0, v_f_undef = 0;
        uint32_t v_skipped_big = 0;
        uint64_t v_pattern_sum = 0;
        uint32_t v_pattern_count = 0;
        const char* stop_reason = "iter_limit";

        for (uint32_t iter = 0; iter < conf.unate_def_rep_iters; iter++) {
            rep_stats.total_iters++;
            v_iters++;

            const Lit h_top_lit = encode_h(h, /*is_y_prime=*/true);

            // act_i ⇒ y_test' ⇔ H_top_lit (gating so old encodings can be
            // disabled cheaply between iterations by adding the unit ~act_i).
            s->new_var();
            const Lit act = Lit(s->nVars()-1, false);
            const Lit y_test_prime = Lit(test + cnf.nVars(), false);
            s->add_clause({~act, ~y_test_prime, h_top_lit});
            s->add_clause({~act,  y_test_prime, ~h_top_lit});

            vector<Lit> as = base_assumps;
            as.push_back(act);

            s->set_max_confl(conf.unate_def_rep_max_confl);
            const auto ret = s->solve(&as);

            if (ret == l_False) {
                rep_stats.miter_unsat++;
                v_miter_unsat++;

                // Uniqueness check: the miter UNSAT only proves Skolem
                // (F-sat ⇒ exists F-sat with y_test = H). Manthan's BW
                // pipeline needs the stronger condition F ⊨ y_test = H
                // — otherwise y[test] in some F-sat models can disagree
                // with y_hat[test] = H, leaving test in needs_repair after
                // find_better_ctx and tripping the BW assertion in
                // find_next_repair_var. Verify in f_solver (no commit
                // clauses): UNSAT under (y_test != H_top) ⇔ uniqueness.
                const Lit h_top_in_f = encode_h_in_f(h);
                const Lit y_test_in_f = Lit(test, false);
                vector<Lit> uniq_assumps;
                f_solver->new_var();
                const Lit ne_act = Lit(f_solver->nVars()-1, false);
                f_solver->add_clause({~ne_act,  y_test_in_f,  h_top_in_f});
                f_solver->add_clause({~ne_act, ~y_test_in_f, ~h_top_in_f});
                uniq_assumps.push_back(ne_act);
                f_solver->set_max_confl(conf.unate_def_rep_max_confl);
                const auto uniq_ret = f_solver->solve(&uniq_assumps);
                f_solver->add_clause({~ne_act}); // disable for next iters
                if (uniq_ret != l_False) {
                    // Skolem-only or undecided: don't commit. Continuing
                    // the iter loop refines H further via the next CEX,
                    // which can sharpen Skolem-only Hs into uniquely-
                    // defining ones in subsequent rounds.
                    s->add_clause({~act});
                    rep_stats.skolem_only_skipped++;
                    continue;
                }

                // y_test = H(...) is a valid unique-defining function.
                // Cheap invariants before commit:
                //   - h is non-null (we always build at least a const FALSE);
                //   - target var has no def yet (set_def_skolem will assert,
                //     but checking here gives a clearer site if it ever
                //     fires);
                //   - H's direct (non-recursive) leaves all live in
                //     input ∪ aux (this is the structural soundness condition
                //     for committing — anything else means the conflict-core
                //     filter let a non-allowed lit through).
                assert(h != nullptr);
                assert(!cnf.defined(test_orig.var()));
                {
                    std::set<uint32_t> h_leaves;
                    AIG::get_dependent_vars(h, h_leaves,
                                            std::numeric_limits<uint32_t>::max());
                    for (uint32_t lf : h_leaves) {
                        assert((input.count(lf)
                               || (lf < aux_mask.size() && aux_mask[lf] != 0))
                            && "H leaf must be input or aux");
                    }
                }
                const aig_ptr h_in_orig = translate_to_orig(h, new_to_orig, test_orig.sign());
                assert(h_in_orig != nullptr);
                VERBOSE_DEBUG_DO(std::cout
                    << "c o [unate_def_rep][verbose] commit test NEW=" << test+1
                    << " orig=" << test_orig.var()+1
                    << " sign=" << test_orig.sign()
                    << " H_NEW=" << h
                    << " H_ORIG=" << h_in_orig << std::endl);
                // set_def_skolem (vs set_def) records the var as Skolem-
                // committed so get_var_types keeps it in backward_defined
                // even when H_test happens to be a constant or input-only
                // AIG. Otherwise downstream (Manthan) would treat the var
                // as an input and drop the y_test = H_test constraint that
                // a later var's miter UNSAT relied on. (We've already
                // checked uniqueness above, but retain the Skolem flag
                // so the categorization stays consistent.)
                cnf.set_def_skolem(test_orig.var(), h_in_orig);
                assert(cnf.defined(test_orig.var())
                    && "set_def_skolem must populate defs[test]");
                assert(cnf.is_skolem_defined(test_orig.var())
                    && "set_def_skolem must add test to skolem_defined_vars");
                // New def changed the dep graph; drop cached recursive deps.
                deps_cache.clear();
                // SLOW_DEBUG: full per-commit verification.
                //   1. defs_invariant() — defs are well-formed (cycle-free,
                //      sampling-var deps unique, etc).
                //   2. check_synth_funs_sat() — F ∧ ¬F[y←y_hat] is UNSAT,
                //      i.e. the AIGs synthesized so far are jointly correct.
                // These catch bad defs at the exact iteration that introduced
                // them; without SLOW_DEBUG the bug would only surface at the
                // unsat_unate_def_rep AIG checkpoint or in Manthan.
                SLOW_DEBUG_DO({
                    [[maybe_unused]] auto inv_ok = cnf.defs_invariant();
                    int bad = cnf.check_synth_funs_sat();
                    if (bad >= 0) {
                        std::cout << "c o [unate_def_rep][SLOW_DEBUG] WRONG commit "
                             << "for orig var " << test_orig.var()+1
                             << " (test NEW=" << test+1 << ")"
                             << " H_NEW=" << h
                             << " H_ORIG=" << h_in_orig << std::endl;
                        release_assert(false &&
                            "unate_def_rep committed a wrong def");
                    }
                });

                // Tighten miter: y_test ⇔ H on Y side. For input-only H,
                // h_top_lit (Y'-side encoding) and the Y-side encoding are
                // the same SAT lit since inputs are shared. For an H with
                // any aux leaves, the two sides differ when the aux var's
                // pinning indicator is later untied (e.g. when aux becomes
                // a future `test`), so we must encode H explicitly on the
                // Y side here.
                const size_t aux_leaves = h_aux_leaf_count(h);
                const Lit h_top_lit_for_commit = (aux_leaves == 0)
                    ? h_top_lit
                    : encode_h(h, /*is_y_prime=*/false);
                const Lit y_test = Lit(test, false);
                s->add_clause({~y_test,  h_top_lit_for_commit});
                s->add_clause({ y_test, ~h_top_lit_for_commit});

                // Lock activation TRUE so the Y'-side equality stays in force
                // for subsequent tests.
                s->add_clause({act});
                new_defs++;
                hit_iter = iter + 1;
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
                stop_reason = "found";
                break;
            }
            if (ret == l_Undef) {
                rep_stats.miter_undef++;
                v_miter_undef++;
                s->add_clause({~act});
                stop_reason = "miter_undef";
                break;
            }
            rep_stats.miter_sat++;
            v_miter_sat++;

            // CEX. Extract values of test (F-side) and h_top_lit (forced to
            // H(X*) by `act`).
            const auto& m = s->get_model();
            const lbool y_test_val_f = m[test];
            const lbool h_val        = model_value(m, h_top_lit);
            if (y_test_val_f == l_Undef || h_val == l_Undef) {
                // Solver didn't pin one of the literals — bail out cleanly.
                s->add_clause({~act});
                stop_reason = "miter_pin_undef";
                break;
            }
            // y_test_Y' = h_val (act_curr); indicator_test = FALSE
            // (base_assumps) forces y_test_Y != y_test_Y'. So
            // y_test_val_f = ~h_val whenever the miter is SAT.
            assert(y_test_val_f != h_val
                && "Miter SAT must have F-side y_test differ from H(X) "
                   "(ensured by indicator_test = FALSE in base_assumps)");

            // F-only call: assume (X*, aux*) values and force y_test = H(...)
            // (the wrong value in F's view).
            // sign convention: Lit(v, true)= ¬v, so Lit(test, h_val == l_False)
            // = (h_val == TRUE ? test : ¬test) — exactly "y_test = H_val".
            const Lit force_wrong = Lit(test, h_val == l_False);
            vector<Lit> f_assumps;
            f_assumps.reserve(input.size() + aux_vars.size() + 1);
            for (uint32_t x : input) {
                if (x >= m.size()) continue;
                const lbool v = m[x];
                if (v == l_Undef) continue;
                f_assumps.emplace_back(x, v == l_False);
            }
            // Aux assumptions: pin aux vars to their miter-model values.
            // In the F-solver these vars are otherwise free (the F-solver
            // has no AIG-copy block / indicator structure), so without
            // this pin a CEX where bifunctionality lives in an aux var
            // would surface as a cost-zero alarm.
            for (uint32_t a : aux_vars) {
                if (a >= m.size()) continue;
                const lbool v = m[a];
                if (v == l_Undef) continue;
                f_assumps.emplace_back(a, v == l_False);
            }
            f_assumps.push_back(force_wrong);

            f_solver->set_max_confl(conf.unate_def_rep_max_confl);
            const auto f_ret = f_solver->solve(&f_assumps);

            // Disable this iteration's activation regardless of outcome.
            s->add_clause({~act});

            if (f_ret == l_True) {
                // Cost-zero: H(X*) is valid in F (some y_other admits it).
                // The miter SAT was an artifact of forcing y_other = y_other'.
                // No safe pattern direction — give up on this var after a
                // few attempts (a single y_other-tied CEX rarely yields a
                // useful pointwise pattern, so we don't bother trying the
                // tighter [X*, y_other*, force_wrong] query: in practice it
                // produces large mixed conflicts whose input projection is
                // rarely the right pattern, and burns iteration budget).
                rep_stats.f_sat++;
                v_f_sat++;
                costzero_count++;
                if (costzero_count >= conf.unate_def_rep_max_costzero) {
                    verb_print(3, "[unate_def_rep] giving up on test " << test+1
                        << " after " << costzero_count << " cost-zero CEXes");
                    stop_reason = "costzero_limit";
                    break;
                }
                continue;
            }
            if (f_ret == l_Undef) {
                rep_stats.f_undef++;
                v_f_undef++;
                stop_reason = "f_undef";
                break;
            }
            // f_ret == l_False
            rep_stats.f_unsat++;
            v_f_unsat++;

            // Conflict literals are negations of assumed literals. Filter
            // out the test-forcing one; everything else is an input or aux
            // lit (we only assumed input ∪ aux + force_wrong).
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
            v_pattern_sum += pattern_lits.size();
            v_pattern_count++;
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
                v_skipped_big++;
                // Same accounting as cost-zero: too-large patterns lead to
                // explosive AIG growth without much generalization.
                costzero_count++;
                if (costzero_count >= conf.unate_def_rep_max_costzero) {
                    stop_reason = "costzero_limit";
                    break;
                }
                continue;
            }

            aig_ptr pattern;
            if (pattern_lits.empty()) {
                // Empty conflict implies F unconditionally forces
                // y_test ≠ H_val — i.e. y_test is a constant we somehow
                // missed in the standard unate test. Refine with a constant.
                pattern = AIG::new_const(true);
            } else {
                pattern = AIG::new_lit(pattern_lits[0].var(), pattern_lits[0].sign());
                for (size_t i = 1; i < pattern_lits.size(); i++) {
                    pattern = AIG::new_and(pattern,
                        AIG::new_lit(pattern_lits[i].var(), pattern_lits[i].sign()));
                }
            }
            VERBOSE_DEBUG_DO({
                std::cout << "c o [unate_def_rep][verbose]   iter=" << iter
                     << " y_test_val_f=" << y_test_val_f
                     << " pattern={ ";
                for (const auto& pl : pattern_lits) std::cout << pl << " ";
                std::cout << "} pattern_AIG=" << pattern << std::endl;
            });

            // Cover X*: when P(X) holds, set H = y_test_val_f there.
            if (y_test_val_f == l_True)  h = AIG::new_or(h, pattern);
            else                         h = AIG::new_and(h, AIG::new_not(pattern));
            VERBOSE_DEBUG_DO(std::cout << "c o [unate_def_rep][verbose]   H_NEW after refine="
                << h << std::endl);
        }

        const size_t v_aux_leaves = h_aux_leaf_count(h);
        verb_print(1, "[unate_def_rep] var NEW " << setw(5) << test+1
            << " orig " << setw(5) << test_orig.var()+1
            << " iters="     << setw(5) << v_iters
            << " miter[U="   << setw(3) << v_miter_unsat
            << " S="         << setw(3) << v_miter_sat
            << " T="         << setw(3) << v_miter_undef << "]"
            << " f[U="       << setw(3) << v_f_unsat
            << " S="         << setw(3) << v_f_sat
            << " T="         << setw(3) << v_f_undef << "]"
            << " skip_big="  << setw(3) << v_skipped_big
            << " costzero="  << setw(3) << costzero_count
            << " avg_pat="   << setw(5) << setprecision(1) << fixed
                             << safe_div(v_pattern_sum, v_pattern_count)
            << " aux["       << setw(4) << aux_vars.size()
            << "/used="      << setw(3) << v_aux_leaves << "]"
            << " AIG_nodes=" << setw(5) << AIG::count_aig_nodes_fast(h)
            << " result=" << std::left << setw(15) << stop_reason << std::right
            << " T: " << fixed << setprecision(2) << (cpuTime()-my_time));

        already_tested.insert(test);
        // IMPORTANT: do NOT add `s->add_clause({var_to_indic[test] = TRUE})`
        // here, even though synthesis_unate_def does. With aux-leaf H, the
        // indicator-lock creates a soundness bug:
        //
        //   - Y-side commit:  y_prev_Y  = H_prev(y_aux_Y)
        //   - Y'-side commit: y_prev_Y' = H_prev(y_aux_Y')   (act_prev locked)
        //   - Indicator-prev locked TRUE: y_prev_Y = y_prev_Y'
        //
        // When a later test=t has its var appear in aux_prev (because an
        // earlier H_prev was committed with t as aux), the chain
        //   H_prev(y_t_Y, ...) = H_prev(y_t_Y', ...)
        // forces y_t_Y = y_t_Y' whenever H_prev is sensitive to y_t — but
        // test=t's miter requires y_t_Y vs y_t_Y' to be free. The result is
        // a spurious miter UNSAT and a wrong commit.
        //
        // The Y- and Y'-side commit clauses on their own already pin y_prev
        // to H_prev on each side, so the indicator-lock is redundant for
        // input-only / backward-only H's anyway, and harmful otherwise.
        // Without the lock, the SAT solver picks indicator-prev consistently
        // with the per-side y_prev values, and the miter stays sound.
    }

    rep_stats.time_total = cpuTime() - my_time;
    // SLOW_DEBUG: end-of-pass sanity. defs_invariant() catches anything
    // a per-commit slipped (cycles, dangling deps, bad sampling-var
    // categorization) and fails fast at the pass boundary instead of
    // at a downstream consumer.
    SLOW_DEBUG_DO({
        [[maybe_unused]] auto inv_ok = cnf.defs_invariant();
    });
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
}
