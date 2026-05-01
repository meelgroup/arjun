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
using std::set;
using std::unique_ptr;


constexpr uint32_t NOT_INPUT = std::numeric_limits<uint32_t>::max();

void Unate::synthesis_unate_def(SimplifiedCNF& cnf) {
    cond_stats = UnateDefCondStats{};
    cond_my_time = cpuTime();
    double my_time = cond_my_time;
    uint32_t new_units = 0;
    cond_new_defs = 0;
    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate_def").unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[unate_def] No variables to-define, skipping");
        return;
    }
    auto s = ArjunInt::setup_f_not_f(cnf, input, conf);

    // Add copied-side definition constraints: i' <-> H_i(X, Y') for all i in I.
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

    for(const auto& i_new: backward_defined) {
        if (input.count(i_new)) continue;

        assert(new_to_orig.count(i_new) > 0);
        const Lit orig = new_to_orig.at(i_new);
        const auto& aig = cnf.get_def(orig.var());
        assert(aig != nullptr && "Already-defined var must have an AIG definition");

        std::vector<Lit> tmp;
        std::function<Lit(AIGT, uint32_t, const Lit*, const Lit*)> aig_to_copy_visitor =
          [&](AIGT type, const uint32_t var_orig, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                return get_true_lit();
            }
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
                tmp.clear();
                tmp = {~and_out, l_lit};
                s->add_clause(tmp);
                tmp = {~and_out, r_lit};
                s->add_clause(tmp);
                tmp = {~l_lit, ~r_lit, and_out};
                s->add_clause(tmp);
                return and_out;
            }
            release_assert(false && "Unhandled AIG type in synthesis_unate_def");
          };

        std::map<aig_ptr, Lit> cache;
        const Lit out_lit = AIG::transform<Lit>(aig, aig_to_copy_visitor, cache);

        // new_to_orig stores whether CNF var is sign-flipped wrt orig var.
        const Lit out_in_new_space = out_lit ^ orig.sign();
        const Lit i_copy = Lit(i_new + cnf.nVars(), false);
        s->add_clause({~i_copy, out_in_new_space});
        s->add_clause({i_copy, ~out_in_new_space});
    }

    verb_print(2, "[unate_def] already-defined vars in CNF: " << backward_defined.size());

    assert(var_to_indic.empty());
    var_to_indic.resize(cnf.nVars(), var_Undef);
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        if (backward_defined.count(i)) continue;
        s->new_var();
        const Lit ind_l = Lit(s->nVars()-1, false);

        // when indic is TRUE, they are equal
        const auto y = Lit (i, false);
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
    /* if (conf.verb >= 3) dump_cnf<Lit>(*s, "unate_def-start.cnf", input); */

    // Deterministic candidate list of input vars used for conditional tests.
    // Inputs are shared across copies in setup_f_not_f, so a single literal
    // assumption fixes the value on both sides simultaneously.
    cond_input_vars_list.assign(input.begin(), input.end());
    std::sort(cond_input_vars_list.begin(), cond_input_vars_list.end());

    // Dense lookup: cond_input_pos[v] = index of v in cond_input_vars_list,
    // or NOT_INPUT if v is not an input. Used to project SAT models down to
    // just input vars without keeping the full ~2*nVars model.
    cond_input_pos.assign(cnf.nVars(), NOT_INPUT);
    for (uint32_t i = 0; i < cond_input_vars_list.size(); i++)
        cond_input_pos[cond_input_vars_list[i]] = i;

    // Per to-define var, the inputs that share at least one CNF clause
    // with it, in first-encountered order. These are the most likely
    // single-literal definers, so we examine them before the rest of
    // the input list.
    cond_related_inputs.assign(cnf.nVars(), {});
    {
        vector<uint8_t> in_cl(cnf.nVars(), 0); // scratch, cleared per clause
        vector<uint32_t> ins_in_cl;
        for (const auto& cl_ : cnf.get_clauses()) {
            ins_in_cl.clear();
            for (const auto& l : cl_) {
                const uint32_t v = l.var();
                if (input.count(v) && !in_cl[v]) {
                    in_cl[v] = 1;
                    ins_in_cl.push_back(v);
                }
            }
            if (!ins_in_cl.empty()) {
                for (const auto& l : cl_) {
                    const uint32_t v = l.var();
                    if (input.count(v)) continue;
                    if (backward_defined.count(v)) continue;
                    auto& dst = cond_related_inputs[v];
                    dst.insert(dst.end(), ins_in_cl.begin(), ins_in_cl.end());
                }
            }
            for (uint32_t iv : ins_in_cl) in_cl[iv] = 0;
        }
        // Dedup each per-var list, preserving first-seen order.
        vector<uint8_t> seen(cnf.nVars(), 0);
        for (uint32_t v = 0; v < cnf.nVars(); v++) {
            auto& lst = cond_related_inputs[v];
            if (lst.empty()) continue;
            vector<uint32_t> ded; ded.reserve(lst.size());
            for (uint32_t iv : lst) {
                if (!seen[iv]) { seen[iv] = 1; ded.push_back(iv); }
            }
            for (uint32_t iv : ded) seen[iv] = 0;
            lst = std::move(ded);
        }
    }

    // Generation-counter dedup for the per-test candidate list.
    cond_cand_seen_gen.assign(cnf.nVars(), 0);
    cond_cand_gen = 0;
    cond_cur_cands.clear();
    cond_cur_cands.reserve(cond_input_vars_list.size());

    vector<Lit> assumps;
    set<uint32_t> already_tested;

    uint32_t tested_num = 0;
    // Adaptive disable: if conditional probing finds nothing for long,
    // turn it off for the rest of the run so we don't waste SAT calls
    // on inputs that obviously won't yield a single-literal definition.
    cond_enabled = (conf.unate_def_cond != 0);
    cond_attempts_since_last_hit = 0;
    for(uint32_t test: to_define) {
        assert(input.count(test) == 0);
        verb_print(3, "[unate_def] testing var: " << test+1);
        tested_num++;
        if (tested_num % 300 == 299) {
            verb_print(1, "[unate_def] test no: " << setw(5) << tested_num
                << " new units: " << setw(4) << new_units
                << " new cond defs: " << setw(4) << cond_new_defs
                << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
        }

        assumps.clear();
        for(uint32_t i = 0; i < cnf.nVars(); i++) {
            if (i == test) continue;
            if (already_tested.count(i)) continue;
            if (input.count(i)) continue;
            if (backward_defined.count(i)) continue;
            auto ind = var_to_indic.at(i);
            assert(ind != var_Undef);
            assumps.emplace_back(ind, false);
        }
        bool found_def = false;
        // Models from the standard-unate flip attempts, projected down
        // to just input vars (input_vars_list[i] -> input_vals[flip][i]).
        // Avoids keeping the full ~2*nVars + helpers SAT model around.
        vector<lbool> input_vals[2];
        bool model_valid[2] = {false, false};
        for(int flip = 0; flip < 2; flip++) {
            assumps.emplace_back(test, !flip);
            assumps.emplace_back(test+cnf.nVars(), flip);
            verb_print(3, "[unate_def] assumps : " << assumps);
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
            // SAT: project the model down to input vars. We only ever
            // read these positions when picking conditional candidates.
            if (ret == l_True) {
                const auto& m = s->get_model();
                input_vals[flip].assign(cond_input_vars_list.size(), l_Undef);
                for (size_t i = 0; i < cond_input_vars_list.size(); i++) {
                    const uint32_t v = cond_input_vars_list[i];
                    if (v < m.size()) input_vals[flip][i] = m[v];
                }
                model_valid[flip] = true;
            }
            assumps.pop_back();
            assumps.pop_back();
        }

        if (!found_def && cond_enabled
                && model_valid[0] && model_valid[1]) {
            if (try_cond_unate_def(cnf, *s, test, input_vals, assumps, new_to_orig)) {
                found_def = true;
            }
        }
        already_tested.insert(test);
        s->add_clause({Lit(var_to_indic.at(test), false)});
    }

    double total_time = cpuTime() - my_time;
    verb_print(1, COLYEL "[unate_def] "
            << " units: " << setw(7) << new_units
            << " cond defs: " << setw(7) << cond_new_defs
            << " cond calls: " << setw(7) << cond_stats.cond_sat_calls
            << " tested: " << setw(7) << tested_num
            << " tests/s: " << setprecision(2) << fixed << setw(6) << safe_div(tested_num, total_time));

    if (conf.unate_def_cond) {
        const auto& cs = cond_stats;
        verb_print(1, COLYEL "[unate_def] cond stats:"
            << " elig=" << cs.tests_eligible
            << " hits=" << cs.hits
            << " hits_in_related=" << cs.hits_in_related
            << " cands[exam=" << cs.cands_examined
            << " skip_v_eq=" << cs.cands_skipped_v_eq
            << " skip_undef=" << cs.cands_skipped_undef
            << " skip_budget=" << cs.cands_skipped_budget << "]"
            << " p1[U=" << cs.p1_unsat << " S=" << cs.p1_sat << " T=" << cs.p1_undef << "]"
            << " p2[U=" << cs.p2_unsat << " S=" << cs.p2_sat << " T=" << cs.p2_undef << "]"
            << " avg_win_depth=" << setprecision(1) << fixed << safe_div(cs.winning_depth_sum, cs.hits)
            << " max_win_depth=" << cs.winning_depth_max
            << " cond_T=" << setprecision(2) << fixed << cs.time_in_cond);
    }

    auto [input2, to_define2, backward_defined2] = cnf.get_var_types(0 | verbose_debug_enabled, "end do_unate_def");
    verb_print(1, COLRED "[unate_def] Done. synthesis_unate_def"
        << " tested: " << tested_num
        << " defined: " << to_define.size() - to_define2.size()
        << " still to-define: " << to_define2.size()
        << " T: " << total_time);
}

// Try to express `test` as a single input literal (test = L or test = ~L) by
// checking, for each candidate input L, whether forcing L to v1 makes test
// forced to a specific value, and similarly for L = !v1. The two flips of the
// standard test give us free SAT witnesses (passed as `input_vals`); we only
// have to issue the OPPOSITE flip per L value, i.e. 2 SAT calls per candidate.
bool Unate::try_cond_unate_def(
        SimplifiedCNF& cnf,
        ArjunInt::MetaSolver& s,
        const uint32_t test,
        const vector<lbool> (&input_vals)[2],
        vector<Lit>& assumps,
        const std::map<uint32_t, Lit>& new_to_orig) {

    const double cond_t0 = cpuTime();
    cond_stats.tests_eligible++;
    const uint32_t nv = cnf.nVars();
    cond_attempts_since_last_hit++;

    // Build per-test candidate list: inputs sharing a clause with `test`
    // first (most likely definers), then the rest. `related_count` is the
    // size of the related-inputs prefix so we can attribute hits to it.
    cond_cand_gen++;
    cond_cur_cands.clear();
    if (conf.unate_def_cond_relfirst) {
        for (uint32_t iv : cond_related_inputs[test]) {
            if (cond_cand_seen_gen[iv] != cond_cand_gen) {
                cond_cand_seen_gen[iv] = cond_cand_gen;
                cond_cur_cands.push_back(iv);
            }
        }
    }
    const uint32_t related_count = cond_cur_cands.size();
    for (uint32_t iv : cond_input_vars_list) {
        if (cond_cand_seen_gen[iv] != cond_cand_gen) {
            cond_cand_seen_gen[iv] = cond_cand_gen;
            cond_cur_cands.push_back(iv);
        }
    }

    bool found_def = false;
    uint32_t cand_count = 0;
    uint32_t cand_depth = 0; // 1-based position of the winner
    for (const uint32_t l_var : cond_cur_cands) {
        cand_depth++;
        if (cand_count >= conf.unate_def_cond_max_per_var) {
            cond_stats.cands_skipped_budget +=
                (uint64_t)(cond_cur_cands.size() - (cand_depth - 1));
            break;
        }
        const uint32_t pos = cond_input_pos[l_var];
        assert(pos != NOT_INPUT);
        lbool v1 = input_vals[0][pos]; // M1: test_x=0 was SAT
        lbool v2 = input_vals[1][pos]; // M2: test_x=1 was SAT
        if (v1 == l_Undef || v2 == l_Undef) {
            cond_stats.cands_skipped_undef++;
            continue;
        }
        if (v1 == v2) {
            cond_stats.cands_skipped_v_eq++;
            continue;
        }
        cand_count++;
        cond_stats.cands_examined++;

        // Under L = v1, the SAT witness M1 had flip=0 SAT
        // (test_x=0, test_y'=1). Try flip=1 (test_x=1, test_y'=0)
        // under L=v1 — UNSAT means test is forced to 0 under L=v1.
        Lit l_eq_v1 = Lit(l_var, v1 != l_True);
        Lit l_eq_v2 = Lit(l_var, v2 != l_True);

        // Probe (test_x=1, test_y'=0) under L=v1: UNSAT here means test
        // cannot be 1 under L=v1. Combined with M1 (which had test_x=0
        // SAT under L=v1), this pins test=0 under L=v1.
        assumps.push_back(l_eq_v1);
        assumps.emplace_back(test, false);
        assumps.emplace_back(test + nv, true);
        s.set_max_confl(conf.unate_def_cond_max_confl);
        cond_stats.cond_sat_calls++;
        auto r1 = s.solve(&assumps);
        assumps.pop_back(); assumps.pop_back(); assumps.pop_back();
        if (r1 == l_False) cond_stats.p1_unsat++;
        else if (r1 == l_True) cond_stats.p1_sat++;
        else cond_stats.p1_undef++;
        if (r1 != l_False) continue;

        // Mirror probe under L=v2: pins test=1 under L=v2.
        assumps.push_back(l_eq_v2);
        assumps.emplace_back(test, true);
        assumps.emplace_back(test + nv, false);
        s.set_max_confl(conf.unate_def_cond_max_confl);
        cond_stats.cond_sat_calls++;
        auto r2 = s.solve(&assumps);
        assumps.pop_back(); assumps.pop_back(); assumps.pop_back();
        if (r2 == l_False) cond_stats.p2_unsat++;
        else if (r2 == l_True) cond_stats.p2_sat++;
        else cond_stats.p2_undef++;
        if (r2 != l_False) continue;

        // Under L=v1 → test=0, under L=v2 → test=1, and v1≠v2.
        // So test = L if v1=l_False, else test = ~L.
        const bool test_equals_l = (v1 == l_False);

        // Set the AIG def (in ORIG variable space).
        assert(new_to_orig.count(test) > 0);
        assert(new_to_orig.count(l_var) > 0);
        const Lit test_orig = new_to_orig.at(test);
        const Lit l_orig    = new_to_orig.at(l_var);
        // Defensive: never produce a self-referential def. Distinct NEW
        // vars should map to distinct ORIG vars after the usual
        // simplification passes, but skip just in case.
        if (test_orig.var() == l_orig.var()) continue;
        // NEW positive `test` corresponds to ORIG lit
        //   Lit(test_orig.var(), test_orig.sign()).
        // We've established NEW test == NEW l_var XOR (!test_equals_l).
        // Translating to ORIG vars:
        //   NEW test = ORIG-var-of-test-pos ⊕ test_orig.sign()
        //   NEW l_var = ORIG-var-of-L-pos ⊕ l_orig.sign()
        // So ORIG-var-of-test = ORIG-var-of-L XOR
        //   (l_orig.sign() ⊕ !test_equals_l ⊕ test_orig.sign())
        const bool def_neg = l_orig.sign() ^ (!test_equals_l) ^ test_orig.sign();
        cnf.set_def(test_orig.var(), AIG::new_lit(l_orig.var(), def_neg));
        cond_new_defs++;
        cond_stats.hits++;
        cond_stats.winning_depth_sum += cand_depth;
        if ((uint64_t)cand_depth > cond_stats.winning_depth_max)
            cond_stats.winning_depth_max = cand_depth;
        if (cand_depth <= related_count) cond_stats.hits_in_related++;
        verb_print(2, "[unate_def] cond def: NEW test " << test+1
            << " = " << (test_equals_l ? "" : "~") << "NEW " << (l_var+1)
            << " (orig: " << test_orig.var()+1 << " "
            << (def_neg ? "-" : "+") << l_orig.var()+1
            << ") depth=" << cand_depth
            << " T: " << fixed << setprecision(2) << (cpuTime()-cond_my_time));

        // Tighten the SAT solver: equate test on both sides to L (or its
        // negation). Implies the indicator becoming TRUE, and helps
        // subsequent tests prove more.
        // NEW lit `test_x ⇔ (test_equals_l ? l_var : ~l_var)`
        {
            const Lit lit_t_x = Lit(test, false);
            const Lit lit_t_y = Lit(test + nv, false);
            const Lit lit_l   = Lit(l_var, !test_equals_l);
            s.add_clause({~lit_t_x, lit_l});
            s.add_clause({lit_t_x, ~lit_l});
            s.add_clause({~lit_t_y, lit_l});
            s.add_clause({lit_t_y, ~lit_l});
        }
        found_def = true;
        cond_attempts_since_last_hit = 0;
        break;
    }
    cond_stats.time_in_cond += cpuTime() - cond_t0;
    if (cond_enabled
            && cond_attempts_since_last_hit >= conf.unate_def_cond_dry_streak
            && cond_new_defs == 0) {
        verb_print(1, "[unate_def] disabling cond probe after "
                << cond_attempts_since_last_hit
                << " dry attempts");
        cond_enabled = false;
    }
    return found_def;
}
