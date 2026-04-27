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
// both, this pass tries to synthesize a richer Boolean function over the
// input vars using a manthan-style counterexample-guided guess+refine loop.
//
// Algorithm per surviving `test`:
//
//   1. Setup is identical to synthesis_unate_def: a miter
//        F(X, Y)  ∧  ¬F(X, Y')
//      with all already-defined vars constrained on the Y' side, and
//      indicator literals tying y_i = y_i' for every other to-define i.
//   2. Maintain a candidate AIG H(X) over input vars. Start with H = FALSE.
//   3. Each iteration:
//      a. Tseitin-encode H on the Y' side under a fresh activation literal
//         act_i, adding clauses `act_i → (y_test' ⇔ H(X))`.
//      b. Solve the miter under {indicators TRUE, act_i}.
//         - UNSAT → y_test = H(X) is a valid Skolem; commit and stop.
//         - SAT   → CEX (X*, Y*, Y'*). y_test_F = m[test] is a value F
//                   admits at X*; H(X*) = m[H_top_lit] is the value the
//                   activation forced on Y' which broke F. They differ.
//      c. Use a separate F-only solver to confirm "F forces y_test ≠ H(X*)
//         when X = X*" and to extract a small input-only unsat core.
//         - Cost-zero (F-solver SAT) → H(X*) is actually fine; the miter
//           is over-constrained by y_other = y_other'. Give up after a
//           small budget of cost-zero CEXes.
//         - UNSAT → conflict ⊆ assumed input lits. The conjunction of the
//           assumed lits in the core is a "pattern" P(X) such that
//             F(X) ⊨ (P(X) → y_test = y_test_F).
//      d. Refine H by covering the bad point:
//           y_test_F = TRUE  →  H = H ∨ P
//           y_test_F = FALSE →  H = H ∧ ¬P
//   4. Disable old activation each iteration (`act_i := FALSE` permanent).
//   5. After per-var loop, mark the var's indicator TRUE permanently —
//      same convention as synthesis_unate_def, regardless of whether we
//      found a def. If we did, we also commit y_test ⇔ H_top_lit to
//      tighten the miter for subsequent vars.
//
// AIG correctness invariants:
//
//   - Every leaf of H is an input var (since we only assume input lits in
//     the F-solver call, the unsat-core lits are always inputs).
//   - Inputs are shared across the Y/Y' sides, so the encoded H_top_lit is
//     the same on both sides. This lets us emit y_test ⇔ H_top_lit on the
//     Y side without re-encoding.
//   - Translation to ORIG-var-space uses the same sign convention as the
//     existing conditional-unate code: leaf-sign XOR's `new_to_orig`'s
//     sign flip; the AIG output is XOR'd by `test_orig.sign()`.
//
// Knobs (Config):
//   unate_def_rep_iters        — guess+refine iters per var
//   unate_def_rep_max_pattern  — skip CEX whose unsat core is bigger than this
//   unate_def_rep_max_costzero — give up after this many cost-zero CEXes
//   unate_def_rep_max_confl    — conflict budget for each SAT call

#include "unate_def.h"
#include "constants.h"
#include "metasolver.h"
#include "time_mem.h"

#include <functional>
#include <iomanip>
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
// the visitor's edge sign (always false in the new transform API), the leaf
// var's own NEW→ORIG sign offset, and the output sign offset of the def's
// var (`test_orig.sign()`) applied at the end.
aig_ptr translate_to_orig(const aig_ptr& aig,
                          const map<uint32_t, Lit>& new_to_orig,
                          bool out_sign_xor) {
    auto visit = [&](AIGT type, uint32_t var, bool /*neg*/,
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
        std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> aig_to_copy_visitor =
          [&](AIGT type, const uint32_t var_orig, const bool neg,
              const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) return neg ? ~get_true_lit() : get_true_lit();
            if (type == AIGT::t_lit) {
                const Lit lit_new = cnf.orig_to_new_lit(Lit(var_orig, neg));
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
                return neg ? ~and_out : and_out;
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

    // ---- H Tseitin encoder, Y' side. H only references input vars (enforced
    //      by pattern construction below), and inputs are shared, so the
    //      encoded helper var is valid on both sides simultaneously.
    auto encode_h_y_prime = [&](const aig_ptr& h) -> Lit {
        vector<Lit> tmp;
        auto visit = [&](AIGT type, uint32_t var, bool /*neg*/,
                         const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) return get_true_lit();
            if (type == AIGT::t_lit) {
                // var is in NEW-var space and (by construction) an input.
                assert(input.count(var) && "H must only reference input vars");
                return Lit(var, false);
            }
            if (type == AIGT::t_and) {
                s->new_var();
                const Lit out = Lit(s->nVars()-1, false);
                tmp = {~out, *left};        s->add_clause(tmp);
                tmp = {~out, *right};       s->add_clause(tmp);
                tmp = {~*left, ~*right, out}; s->add_clause(tmp);
                return out;
            }
            release_assert(false && "Unhandled AIG type in encode_h_y_prime");
        };
        map<aig_ptr, Lit> cache;
        return AIG::transform<Lit>(h, visit, cache);
    };

    vector<Lit> assumps;
    set<uint32_t> already_tested;
    uint32_t tested_num = 0;
    uint32_t new_defs = 0;

    for (uint32_t test : to_define) {
        assert(input.count(test) == 0);
        // Skip if a previous pass already defined this (e.g. an earlier
        // iteration of THIS pass, via cnf.set_def on a different orig var
        // that resolves to the same new var — defensive only).
        const Lit test_orig = new_to_orig.at(test);
        if (cnf.defined(test_orig.var())) {
            already_tested.insert(test);
            s->add_clause({Lit(var_to_indic.at(test), false)});
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

            const Lit h_top_lit = encode_h_y_prime(h);

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
                // y_test = H(X) is a valid Skolem.
                const aig_ptr h_in_orig = translate_to_orig(h, new_to_orig, test_orig.sign());
                cnf.set_def(test_orig.var(), h_in_orig);

                // Tighten miter: y_test ⇔ H_top_lit on Y side. H_top_lit's
                // helper var is shared (only references input vars) so this
                // reuses the same encoding.
                const Lit y_test = Lit(test, false);
                s->add_clause({~y_test,  h_top_lit});
                s->add_clause({ y_test, ~h_top_lit});

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
            // Activation was assumed TRUE, so y_test' = h_val. The miter
            // requires F holds on Y side and ¬F on Y' side; with y_other'
            // = y_other (indicators), the only flexibility is y_test vs
            // y_test' — so they must differ.
            assert(y_test_val_f != h_val
                    && "Miter SAT must have F-side y_test differ from H(X)");

            // F-only call: assume X* values and force y_test = H(X*) (the
            // wrong value in F's view at X*).
            // sign convention: Lit(v, true)= ¬v, so Lit(test, h_val == l_False)
            // = (h_val == TRUE ? test : ¬test) — exactly "y_test = H_val".
            const Lit force_wrong = Lit(test, h_val == l_False);
            vector<Lit> f_assumps;
            f_assumps.reserve(input.size() + 1);
            for (uint32_t x : input) {
                if (x >= m.size()) continue;
                const lbool v = m[x];
                if (v == l_Undef) continue;
                f_assumps.emplace_back(x, v == l_False);
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
            // out the test-forcing one; everything else is an input lit
            // (we only assumed inputs + force_wrong).
            vector<Lit> conflict = f_solver->get_conflict();
            vector<Lit> pattern_lits;
            pattern_lits.reserve(conflict.size());
            for (const Lit& cl : conflict) {
                if (cl == ~force_wrong) continue;
                if (cl.var() == test) continue; // defensive
                if (!input.count(cl.var())) continue;
                pattern_lits.push_back(~cl);    // assumption form: matches X*
            }
            v_pattern_sum += pattern_lits.size();
            v_pattern_count++;
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

            // Cover X*: when P(X) holds, set H = y_test_val_f there.
            if (y_test_val_f == l_True)  h = AIG::new_or(h, pattern);
            else                         h = AIG::new_and(h, AIG::new_not(pattern));
        }

        verb_print(2, "[unate_def_rep] var NEW " << setw(5) << test+1
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
            << " AIG_nodes=" << setw(5) << AIG::count_aig_nodes_fast(h)
            << " result=" << std::left << setw(15) << stop_reason << std::right
            << " T: " << fixed << setprecision(2) << (cpuTime()-my_time));

        already_tested.insert(test);
        s->add_clause({Lit(var_to_indic.at(test), false)});
    }

    rep_stats.time_total = cpuTime() - my_time;
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
        << " avg_hit_iter=" << setprecision(1) << fixed
        << safe_div(rep_stats.hit_iter_sum, rep_stats.hits)
        << " max_hit_iter=" << rep_stats.hit_iter_max
        << " avg_hit_aig=" << setprecision(1) << fixed
        << safe_div(rep_stats.hit_aig_nodes_sum, rep_stats.hits)
        << " max_hit_aig=" << rep_stats.hit_aig_nodes_max
        << " still to-define: " << to_define2.size()
        << " T: " << setprecision(2) << fixed << rep_stats.time_total);
}
