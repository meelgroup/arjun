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

#include "unate_def.h"
#include "unate_def_common.h"
#include "constants.h"
#include "metasolver.h"
#include "time_mem.h"
#include <algorithm>
#include <iomanip>
#include <limits>

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::setprecision;
using std::fixed;
using std::setw;
using std::vector;


constexpr uint32_t NOT_INPUT = std::numeric_limits<uint32_t>::max();

void Unate::synthesis_unate_def(SimplifiedCNF& cnf) {
    eq_stats = UnateDefEqStats{};
    eq_my_time = cpuTime();
    my_time = eq_my_time;
    new_units = 0;
    eq_new_defs = 0;
    tested_num = 0;
    true_lit = lit_Undef;
    cnf_ptr = &cnf;
    already_tested.clear();

    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate_def")
        .unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[unate_def] No variables to-define, skipping");
        return;
    }
    s = ArjunInt::setup_f_not_f(cnf, input, conf);
    new_to_orig = cnf.get_new_to_orig_var();

    setup_y_prime_backward_defs();
    build_indicators();
    build_eq_state();

    // Adaptive disable: turn eq probing off if it stays unproductive.
    eq_enabled = (conf.unate_def_eq != 0);
    eq_attempts_since_last_hit = 0;

    const uint32_t to_define_size_before = to_define.size();
    for (uint32_t test : to_define) process_test_var(test);

    log_pass_summary(to_define_size_before);
}

Lit Unate::get_true_lit() {
    if (true_lit == lit_Undef) {
        s->new_var();
        true_lit = Lit(s->nVars()-1, false);
        s->add_clause({true_lit});
    }
    return true_lit;
}

// Add copied-side definition constraints: i' <-> H_i(X, Y') for each
// already-defined var in `backward_defined`.
void Unate::setup_y_prime_backward_defs() {
    const auto& cnf = *cnf_ptr;
    for (const auto& i_new : backward_defined) {
        if (input.count(i_new)) continue;

        assert(new_to_orig.count(i_new) > 0);
        const Lit orig = new_to_orig.at(i_new);
        const auto& aig = cnf.get_def(orig.var());
        assert(aig != nullptr && "Already-defined var must have an AIG definition");

        const Lit out_lit = AIG::tseitin_encode(
            aig, *s,
            [this] { return get_true_lit(); },
            [&](uint32_t var_orig) -> Lit {
                const Lit lit_new = cnf.orig_to_new_lit(Lit(var_orig, false));
                if (input.count(lit_new.var())) return lit_new;
                assert(lit_new.var() < cnf.nVars());
                return Lit(lit_new.var() + cnf.nVars(), lit_new.sign());
            });

        // new_to_orig stores whether CNF var is sign-flipped wrt orig var.
        const Lit out_in_new_space = out_lit ^ orig.sign();
        const Lit i_copy = Lit(i_new + cnf.nVars(), false);
        s->add_clause({~i_copy, out_in_new_space});
        s->add_clause({i_copy, ~out_in_new_space});
    }
}

// Allocate one indicator var per non-input, non-backward-defined var, with
// clauses making it TRUE iff y_i == y_i'.
void Unate::build_indicators() {
    auto& cnf = *cnf_ptr;
    assert(var_to_indic.empty());
    var_to_indic.resize(cnf.nVars(), var_Undef);
    for (uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        if (backward_defined.count(i)) continue;
        s->new_var();
        const Lit ind_l = Lit(s->nVars()-1, false);

        // when indic is TRUE, they are equal
        const auto y = Lit(i, false);
        const auto y_hat = Lit(i + cnf.nVars(), false);
        vector<Lit> tmp;
        tmp.push_back(~ind_l);
        tmp.push_back(y_hat);
        tmp.push_back(~y);
        s->add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        s->add_clause(tmp);

        tmp.clear();
        tmp.push_back(ind_l);
        tmp.push_back(~y_hat);
        tmp.push_back(~y);
        s->add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        s->add_clause(tmp);
        var_to_indic[i] = ind_l.var();
    }
}

// Populate try_eq_unate_def's scratch state: sorted input/non-input
// candidate lists, position lookup, per-to-define "related" prefixes
// (inputs/non-inputs kept separate for inputs-first iteration), and the
// dedup buffer. Non-input candidates are indicator-carrying vars (neither
// input nor backward-defined); their indicator forces y_v == y_v' on both
// miter copies, so a single Y-side literal fixes v — as inputs get via sharing.
void Unate::build_eq_state() {
    auto& cnf = *cnf_ptr;

    // Sorted candidate lists: inputs (shared between Y and Y') and
    // non-inputs (Y/Y' kept consistent by indicators).
    eq_input_vars_list.assign(input.begin(), input.end());
    std::sort(eq_input_vars_list.begin(), eq_input_vars_list.end());

    eq_noninput_vars_list.clear();
    for (uint32_t v = 0; v < cnf.nVars(); v++) {
        if (input.count(v)) continue;
        if (backward_defined.count(v)) continue;
        eq_noninput_vars_list.push_back(v);
    }
    // Already in sorted order from the index-ascending loop.

    // Dense position lookup: inputs at [0, n_inp), non-inputs after;
    // NOT_INPUT marks a non-candidate (backward-defined, no indicator).
    eq_cand_pos.assign(cnf.nVars(), NOT_INPUT);
    for (uint32_t i = 0; i < eq_input_vars_list.size(); i++)
        eq_cand_pos[eq_input_vars_list[i]] = i;
    const uint32_t n_inp = eq_input_vars_list.size();
    for (uint32_t i = 0; i < eq_noninput_vars_list.size(); i++)
        eq_cand_pos[eq_noninput_vars_list[i]] = n_inp + i;

    // Per to-define var: co-occurring inputs and non-inputs (ordered by
    // co-occurrence count desc) — more likely single-literal definers, so
    // examined first. Kept separate to iterate [related_in, related_ni,
    // all_in, all_ni] (all related-input work before any non-input).
    eq_related_inputs.assign(cnf.nVars(), {});
    eq_related_noninputs.assign(cnf.nVars(), {});
    vector<uint8_t> in_cl(cnf.nVars(), 0); // scratch, cleared per clause
    vector<uint32_t> ins_in_cl;
    vector<uint32_t> ninps_in_cl;
    for (const auto& cl : cnf.get_clauses()) {
        ins_in_cl.clear();
        ninps_in_cl.clear();
        for (const auto& l : cl) {
            const uint32_t v = l.var();
            if (in_cl[v]) continue;
            if (input.count(v)) {
                in_cl[v] = 1;
                ins_in_cl.push_back(v);
            } else if (!backward_defined.count(v)) {
                in_cl[v] = 1;
                ninps_in_cl.push_back(v);
            }
        }
        // For each non-input candidate v, record co-occurring inputs and
        // other non-inputs (v itself excluded from the non-input list).
        for (uint32_t v : ninps_in_cl) {
            if (!ins_in_cl.empty()) {
                auto& dst = eq_related_inputs[v];
                dst.insert(dst.end(), ins_in_cl.begin(), ins_in_cl.end());
            }
            if (ninps_in_cl.size() >= 2) {
                auto& dst = eq_related_noninputs[v];
                for (uint32_t w : ninps_in_cl) {
                    if (w != v) dst.push_back(w);
                }
            }
        }
        for (uint32_t v : ins_in_cl)   in_cl[v] = 0;
        for (uint32_t v : ninps_in_cl) in_cl[v] = 0;
    }

    // Reorder each per-var list by co-occurrence count desc, ties by
    // lower var id for determinism.
    auto reorder_by_cooccur = [](vector<uint32_t>& lst) {
        if (lst.empty()) return;
        std::sort(lst.begin(), lst.end());
        vector<std::pair<uint32_t, uint32_t>> counts; // (count, var)
        for (size_t i = 0; i < lst.size(); ) {
            size_t j = i;
            while (j < lst.size() && lst[j] == lst[i]) j++;
            counts.emplace_back((uint32_t)(j - i), lst[i]);
            i = j;
        }
        std::sort(counts.begin(), counts.end(),
            [](const auto& a, const auto& b) {
                if (a.first != b.first) return a.first > b.first;
                return a.second < b.second;
            });
        lst.clear();
        lst.reserve(counts.size());
        for (const auto& p : counts) lst.push_back(p.second);
    };
    for (uint32_t v = 0; v < cnf.nVars(); v++) {
        reorder_by_cooccur(eq_related_inputs[v]);
        reorder_by_cooccur(eq_related_noninputs[v]);
    }

    // Generation-counter dedup for the per-test candidate list.
    eq_cand_seen_gen.assign(cnf.nVars(), 0);
    eq_cand_gen = 0;
    eq_cur_cands.clear();
    eq_cur_cands.reserve(eq_input_vars_list.size() + eq_noninput_vars_list.size());

    // Fresh deps cache for this pass.
    eq_deps_cache.clear();
}

// Run both standard-unate flips on `test`, then dispatch to the equiv
// probe if both flips were SAT. Updates new_units / eq_new_defs as a side
// effect. Returns true if any def was found.
bool Unate::process_test_var(const uint32_t test) {
    auto& cnf = *cnf_ptr;
    assert(input.count(test) == 0);
    verb_print(3, "[unate_def] testing var: " << test+1);
    tested_num++;
    if (tested_num % 300 == 299) {
        verb_print(1, "[unate_def] test no: " << setw(5) << tested_num
            << " new units: " << setw(4) << new_units
            << " new eq defs: " << setw(4) << eq_new_defs
            << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
    }

    assumps.clear();
    for (uint32_t i = 0; i < cnf.nVars(); i++) {
        if (i == test) continue;
        if (already_tested.count(i)) continue;
        if (input.count(i)) continue;
        if (backward_defined.count(i)) continue;
        auto ind = var_to_indic.at(i);
        assert(ind != var_Undef);
        assumps.emplace_back(ind, false);
    }
    bool found_def = false;
    // Flip-attempt models, projected to candidate vars only (avoids
    // keeping the full ~2*nVars + helpers SAT model).
    model_valid[0] = false;
    model_valid[1] = false;
    for (int flip = 0; flip < 2; flip++) {
        assumps.emplace_back(test, !flip);
        assumps.emplace_back(test+cnf.nVars(), flip);
        verb_print(3, "[unate_def] assumps : " << assumps);
        s->set_max_confl(conf.unate_def_max_confl);
        const auto ret = s->solve(&assumps);
        if (ret == l_False) {
            const Lit l = Lit(test, flip);
            const Lit test_orig = new_to_orig.at(test);
            // l forces NEW test to value !flip; in ORIG space the var
            // gets the constant !(test_orig.sign() ^ flip).
            cnf.set_def(test_orig.var(),
                AIG::new_const(!(test_orig.sign() ^ (bool)flip)));
            verb_print(2, "[unate_def] good test. Setting: " << std::setw(3)  << l
                << " T: " << fixed << setprecision(2) << (cpuTime() - my_time));
            // Tighten both sides of the miter so subsequent tests
            // benefit from the now-forced value.
            s->add_clause({l});
            s->add_clause({Lit(test+cnf.nVars(), flip)});
            new_units++;
            found_def = true;
            assumps.pop_back();
            assumps.pop_back();
            break;
        }
        // SAT: project the model to all candidate vars. m[v] is the Y-side
        // value; inputs share Y/Y', non-inputs are pinned equal by their
        // indicator, so one value per candidate is unambiguous.
        if (ret == l_True) {
            const auto& m = s->get_model();
            const size_t total = eq_input_vars_list.size() + eq_noninput_vars_list.size();
            input_vals[flip].assign(total, l_Undef);
            for (size_t i = 0; i < eq_input_vars_list.size(); i++) {
                const uint32_t v = eq_input_vars_list[i];
                if (v < m.size()) input_vals[flip][i] = m[v];
            }
            const size_t n_inp = eq_input_vars_list.size();
            for (size_t i = 0; i < eq_noninput_vars_list.size(); i++) {
                const uint32_t v = eq_noninput_vars_list[i];
                if (v < m.size()) input_vals[flip][n_inp + i] = m[v];
            }
            model_valid[flip] = true;
        }
        assumps.pop_back();
        assumps.pop_back();
    }

    if (!found_def && eq_enabled && model_valid[0] && model_valid[1]) {
        if (try_eq_unate_def(test)) found_def = true;
    }
    already_tested.insert(test);
    s->add_clause({Lit(var_to_indic.at(test), false)});
    return found_def;
}

void Unate::log_pass_summary(const uint32_t to_define_size_before) {
    const double total_time = cpuTime() - my_time;
    verb_print(1, COLYEL "[unate_def] "
            << " units: " << setw(7) << new_units
            << " eq defs: " << setw(7) << eq_new_defs
            << " eq calls: " << setw(7) << eq_stats.eq_sat_calls
            << " tested: " << setw(7) << tested_num
            << " tests/s: " << setprecision(2) << fixed << setw(6) << safe_div(tested_num, total_time));

    if (conf.unate_def_eq) {
        const auto& cs = eq_stats;
        verb_print(1, COLYEL "[unate_def] eq stats:"
            << " elig=" << cs.tests_eligible
            << " hits=" << cs.hits
            << " hits_in_related=" << cs.hits_in_related
            << " hits_noninput=" << cs.hits_using_noninput
            << " cands[exam=" << cs.cands_examined
            << " skip_v_eq=" << cs.cands_skipped_v_eq
            << " skip_undef=" << cs.cands_skipped_undef
            << " skip_budget=" << cs.cands_skipped_budget
            << " skip_cycle=" << cs.cands_skipped_cycle << "]"
            << " p1[U=" << cs.p1_unsat << " S=" << cs.p1_sat << " T=" << cs.p1_undef << "]"
            << " p2[U=" << cs.p2_unsat << " S=" << cs.p2_sat << " T=" << cs.p2_undef << "]"
            << " avg_win_depth=" << setprecision(1) << fixed << safe_div(cs.winning_depth_sum, cs.hits)
            << " max_win_depth=" << cs.winning_depth_max
            << " eq_T=" << setprecision(2) << fixed << cs.time_in_eq);
    }

    auto [input2, to_define2, backward_defined2] =
        cnf_ptr->get_var_types(0 | verbose_debug_enabled, "end do_unate_def");
    verb_print(1, COLRED "[unate_def] Done. synthesis_unate_def"
        << " tested: " << tested_num
        << " defined: " << to_define_size_before - to_define2.size()
        << " still to-define: " << to_define2.size()
        << " T: " << total_time);
}

// Try to express `test` as a single literal (test = L or test = ~L) over a
// candidate L: for each L check whether forcing L=v1 forces test to a value
// and L=!v1 forces the opposite. The standard flips give free witnesses
// (in `input_vals`), so only the opposite flip is issued: 2 SAT calls per L.
// L is an input (shared Y/Y') or a non-input candidate (indicator pins
// y_L == y_L'); inputs iterated first, non-inputs only after and gated by
// `unate_def_eq_noninput`.
bool Unate::try_eq_unate_def(const uint32_t test) {
    auto& cnf = *cnf_ptr;
    const double eq_t0 = cpuTime();
    eq_stats.tests_eligible++;
    const uint32_t nv = cnf.nVars();
    eq_attempts_since_last_hit++;
    const bool noninput_enabled = conf.unate_def_eq_noninput != 0;
    const Lit test_orig = new_to_orig.at(test);

    // Per-test candidate list in priority order: (1) related inputs,
    // (2) related non-inputs, (3) rest of inputs, (4) rest of non-inputs
    // (2/4 only if enabled). `related_count` covers (1)+(2).
    eq_cand_gen++;
    eq_cur_cands.clear();
    for (uint32_t iv : eq_related_inputs[test]) {
        if (eq_cand_seen_gen[iv] != eq_cand_gen) {
            eq_cand_seen_gen[iv] = eq_cand_gen;
            eq_cur_cands.push_back(iv);
        }
    }
    if (noninput_enabled) {
        for (uint32_t iv : eq_related_noninputs[test]) {
            if (iv == test) continue;
            if (eq_cand_seen_gen[iv] != eq_cand_gen) {
                eq_cand_seen_gen[iv] = eq_cand_gen;
                eq_cur_cands.push_back(iv);
            }
        }
    }
    const uint32_t related_count = eq_cur_cands.size();
    for (uint32_t iv : eq_input_vars_list) {
        if (eq_cand_seen_gen[iv] != eq_cand_gen) {
            eq_cand_seen_gen[iv] = eq_cand_gen;
            eq_cur_cands.push_back(iv);
        }
    }
    if (noninput_enabled) {
        for (uint32_t iv : eq_noninput_vars_list) {
            if (iv == test) continue;
            if (eq_cand_seen_gen[iv] != eq_cand_gen) {
                eq_cand_seen_gen[iv] = eq_cand_gen;
                eq_cur_cands.push_back(iv);
            }
        }
    }

    bool found_def = false;
    uint32_t cand_count = 0;
    uint32_t cand_depth = 0; // 1-based position of the winner
    for (const uint32_t l_var : eq_cur_cands) {
        cand_depth++;
        if (cand_count >= conf.unate_def_eq_max_per_var) {
            eq_stats.cands_skipped_budget +=
                (uint64_t)(eq_cur_cands.size() - (cand_depth - 1));
            break;
        }
        const uint32_t pos = eq_cand_pos[l_var];
        assert(pos != NOT_INPUT);
        lbool v1 = input_vals[0][pos]; // M1: test_x=0 was SAT
        lbool v2 = input_vals[1][pos]; // M2: test_x=1 was SAT
        if (v1 == l_Undef || v2 == l_Undef) {
            eq_stats.cands_skipped_undef++;
            continue;
        }
        if (v1 == v2) {
            eq_stats.cands_skipped_v_eq++;
            continue;
        }

        // Dep-graph safety for non-input L: set_def(test, L) makes test
        // backward_defined, which Manthan requires to bottom out at orig
        // sampling vars. Accept non-input L only when (i) L is defined,
        // (ii) deps_recursive(L_orig) ⊆ orig_sampl_vars, and (iii) test_orig
        // ∉ deps_recursive(L_orig) (cycle check). (i) is checked first since
        // get_dependent_vars_recursive asserts defined(l_orig). Inputs pass
        // trivially (no incoming defs).
        const bool l_is_input = input.count(l_var) > 0;
        const Lit l_orig = new_to_orig.at(l_var);
        if (!l_is_input) {
            if (!cnf.defined(l_orig.var())) {
                eq_stats.cands_skipped_cycle++;
                continue;
            }
            const auto& deps = cnf.get_dependent_vars_recursive(
                l_orig.var(), eq_deps_cache);
            const auto& orig_inputs = cnf.get_orig_sampl_vars();
            bool unsafe = false;
            for (uint32_t d : deps) {
                if (d == test_orig.var() || !orig_inputs.count(d)) {
                    unsafe = true;
                    break;
                }
            }
            if (unsafe) {
                eq_stats.cands_skipped_cycle++;
                continue;
            }
        }

        cand_count++;
        eq_stats.cands_examined++;

        // l_eq_v1/v2 are Y-side lits; for inputs also the Y' lit (shared),
        // for non-inputs the indicator forces y_L == y_L' on both sides.
        Lit l_eq_v1 = Lit(l_var, v1 != l_True);
        Lit l_eq_v2 = Lit(l_var, v2 != l_True);

        // Probe (test_x=1, test_y'=0) under L=v1: UNSAT (with M1's test_x=0
        // SAT) pins test=0 under L=v1.
        assumps.push_back(l_eq_v1);
        assumps.emplace_back(test, false);
        assumps.emplace_back(test + nv, true);
        s->set_max_confl(conf.unate_def_eq_max_confl);
        eq_stats.eq_sat_calls++;
        auto r1 = s->solve(&assumps);
        assumps.pop_back(); assumps.pop_back(); assumps.pop_back();
        if (r1 == l_False) eq_stats.p1_unsat++;
        else if (r1 == l_True) eq_stats.p1_sat++;
        else eq_stats.p1_undef++;
        if (r1 != l_False) continue;

        // Mirror probe under L=v2: pins test=1 under L=v2.
        assumps.push_back(l_eq_v2);
        assumps.emplace_back(test, true);
        assumps.emplace_back(test + nv, false);
        s->set_max_confl(conf.unate_def_eq_max_confl);
        eq_stats.eq_sat_calls++;
        auto r2 = s->solve(&assumps);
        assumps.pop_back(); assumps.pop_back(); assumps.pop_back();
        if (r2 == l_False) eq_stats.p2_unsat++;
        else if (r2 == l_True) eq_stats.p2_sat++;
        else eq_stats.p2_undef++;
        if (r2 != l_False) continue;

        // Under L=v1 → test=0, under L=v2 → test=1, and v1≠v2.
        // So test = L if v1=l_False, else test = ~L.
        const bool test_equals_l = (v1 == l_False);

        // Set the AIG def (in ORIG variable space).
        assert(new_to_orig.count(test) > 0);
        assert(new_to_orig.count(l_var) > 0);
        assert(test_orig.var() != l_orig.var());

        // NEW test == NEW l_var XOR !test_equals_l; translating both to
        // ORIG vars gives the sign below.
        const bool def_neg = l_orig.sign() ^ (!test_equals_l) ^ test_orig.sign();
        cnf.set_def(test_orig.var(), AIG::new_lit(l_orig.var(), def_neg));
        // New def changed the dep graph; drop cached recursive deps.
        eq_deps_cache.clear();
        eq_new_defs++;
        eq_stats.hits++;
        eq_stats.winning_depth_sum += cand_depth;
        if ((uint64_t)cand_depth > eq_stats.winning_depth_max)
            eq_stats.winning_depth_max = cand_depth;
        if (cand_depth <= related_count) eq_stats.hits_in_related++;
        if (!l_is_input) eq_stats.hits_using_noninput++;
        verb_print(2, "[unate_def] eq def: NEW test " << test+1
            << " = " << (test_equals_l ? "" : "~") << "NEW " << (l_var+1)
            << " (orig: " << test_orig.var()+1 << " "
            << (def_neg ? "-" : "+") << l_orig.var()+1
            << ") depth=" << cand_depth
            << (l_is_input ? " input" : " noninput")
            << " T: " << fixed << setprecision(2) << (cpuTime()-eq_my_time));

        // Tighten the solver: equate test to L (or ~L) on both sides,
        // helping subsequent tests. Input L shares the Y/Y' lit; non-input
        // L needs the equivalence added per side.
        {
            const Lit lit_t_x = Lit(test, false);
            const Lit lit_t_y = Lit(test + nv, false);
            const Lit lit_l_y = Lit(l_var, !test_equals_l);
            const Lit lit_l_yp = l_is_input
                ? lit_l_y
                : Lit(l_var + nv, !test_equals_l);
            s->add_clause({~lit_t_x, lit_l_y});
            s->add_clause({lit_t_x, ~lit_l_y});
            s->add_clause({~lit_t_y, lit_l_yp});
            s->add_clause({lit_t_y, ~lit_l_yp});
        }
        found_def = true;
        eq_attempts_since_last_hit = 0;
        break;
    }
    eq_stats.time_in_eq += cpuTime() - eq_t0;
    if (eq_enabled
            && eq_attempts_since_last_hit >= conf.unate_def_eq_dry_streak
            && eq_new_defs == 0) {
        verb_print(1, "[unate_def] disabling eq probe after "
                << eq_attempts_since_last_hit
                << " dry attempts");
        eq_enabled = false;
    }
    return found_def;
}
