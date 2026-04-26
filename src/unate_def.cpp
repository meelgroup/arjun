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
#include "constants.h"
#include "metasolver.h"
#include "time_mem.h"
#include <algorithm>
#include <iomanip>

using namespace ArjunNS;
using namespace CMSat;
using std::setprecision;
using std::fixed;
using std::setw;
using std::vector;
using std::set;
using std::unique_ptr;

void Unate::synthesis_unate_def(SimplifiedCNF& cnf) {
    double my_time = cpuTime();
    uint32_t new_units = 0;
    uint32_t new_cond_defs = 0;
    uint32_t cond_calls = 0;
    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate_def").unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[unate_def] No variables to define, skipping");
        return;
    }
    auto s = setup_f_not_f(cnf);

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
        std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> aig_to_copy_visitor =
          [&](AIGT type, const uint32_t var_orig, const bool neg, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                return neg ? ~get_true_lit() : get_true_lit();
            }
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
                tmp.clear();
                tmp = {~and_out, l_lit};
                s->add_clause(tmp);
                tmp = {~and_out, r_lit};
                s->add_clause(tmp);
                tmp = {~l_lit, ~r_lit, and_out};
                s->add_clause(tmp);
                return neg ? ~and_out : and_out;
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
    vector<uint32_t> input_vars_list(input.begin(), input.end());
    std::sort(input_vars_list.begin(), input_vars_list.end());

    vector<Lit> assumps;
    vector<Lit> cl;
    set<uint32_t> already_tested;

    uint32_t tested_num = 0;
    vector<Lit> unates;
    // Adaptive disable: if conditional probing finds nothing for long,
    // turn it off for the rest of the run so we don't waste SAT calls
    // on inputs that obviously won't yield a single-literal definition.
    bool cond_enabled = (conf.unate_def_cond != 0);
    uint32_t cond_attempts_since_last_hit = 0;
    constexpr uint32_t cond_dry_streak_disable = 64;
    for(uint32_t test: to_define) {
        assert(input.count(test) == 0);
        verb_print(3, "[unate_def] testing var: " << test+1);
        tested_num++;
        if (tested_num % 300 == 299) {
            verb_print(1, "[unate_def] test no: " << setw(5) << tested_num
                << " new units: " << setw(4) << new_units
                << " new cond defs: " << setw(4) << new_cond_defs
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
            assumps.push_back(Lit(ind, false));
        }
        bool found_def = false;
        // Models from the standard-unate flip attempts; used to pick
        // conditional candidates without scanning every input.
        // model_for_flip[k] is the model returned when flip=k was SAT.
        vector<lbool> model_for_flip[2];
        bool model_valid[2] = {false, false};
        for(int flip = 0; flip < 2; flip++) {
            assumps.push_back(Lit(test, !flip));
            assumps.push_back(Lit(test+cnf.nVars(), flip));
            verb_print(3, "[unate_def] assumps : " << assumps);
            const auto ret = s->solve(&assumps);
            if (ret == l_False) {
                Lit l = {Lit(test, flip)};
                unates.push_back(l);
                cnf.add_clause({l});
                verb_print(2, "[unate_def] good test. Setting: " << std::setw(3)  << l
                    << " T: " << fixed << setprecision(2) << (cpuTime() - my_time));
                l = Lit(test+cnf.nVars(), flip);
                cl = {l};
                s->add_clause(cl);
                new_units++;
                found_def = true;
                assumps.pop_back();
                assumps.pop_back();
                break;
            }
            // SAT: capture the model so we can use it to choose conditional
            // candidates below. Copy out before issuing more solve calls.
            if (ret == l_True) {
                model_for_flip[flip] = s->get_model();
                model_valid[flip] = true;
            }
            assumps.pop_back();
            assumps.pop_back();
        }

        // Conditional unate definition: try to express test as a single
        // input literal (test = L or test = ~L) by checking, for each
        // candidate input L, whether forcing L to v1 makes test forced to a
        // specific value, and similarly for L = !v1. The two flips of the
        // standard test give us free SAT witnesses: we only have to issue
        // the OPPOSITE flip per L value, i.e. 2 SAT calls per candidate.
        if (!found_def && cond_enabled
                && model_valid[0] && model_valid[1]) {
            const uint32_t nv = cnf.nVars();
            cond_attempts_since_last_hit++;

            uint32_t cand_count = 0;
            for (const uint32_t l_var : input_vars_list) {
                if (cand_count >= conf.unate_def_cond_max_per_var) break;
                if (l_var >= model_for_flip[0].size()) continue;
                if (l_var >= model_for_flip[1].size()) continue;
                lbool v1 = model_for_flip[0][l_var]; // M1: test_x=0 was SAT
                lbool v2 = model_for_flip[1][l_var]; // M2: test_x=1 was SAT
                if (v1 == l_Undef || v2 == l_Undef) continue;
                if (v1 == v2) continue; // L's value didn't change; no chance
                cand_count++;

                // Under L = v1, the SAT witness M1 had flip=0 SAT
                // (test_x=0, test_y'=1). Try flip=1 (test_x=1, test_y'=0)
                // under L=v1 — UNSAT means test is forced to 0 under L=v1.
                Lit l_eq_v1 = Lit(l_var, v1 != l_True);
                Lit l_eq_v2 = Lit(l_var, v2 != l_True);

                // Probe (test_x=1, test_y'=0) under L=v1: UNSAT here means
                // test cannot be 1 under L=v1. Combined with M1 (which had
                // test_x=0 SAT under L=v1), this pins test=0 under L=v1.
                assumps.push_back(l_eq_v1);
                assumps.push_back(Lit(test, false));
                assumps.push_back(Lit(test + nv, true));
                s->set_max_confl(conf.unate_def_cond_max_confl);
                cond_calls++;
                auto r1 = s->solve(&assumps);
                assumps.pop_back(); assumps.pop_back(); assumps.pop_back();
                if (r1 != l_False) continue;

                // Mirror probe under L=v2: pins test=1 under L=v2.
                assumps.push_back(l_eq_v2);
                assumps.push_back(Lit(test, true));
                assumps.push_back(Lit(test + nv, false));
                s->set_max_confl(conf.unate_def_cond_max_confl);
                cond_calls++;
                auto r2 = s->solve(&assumps);
                assumps.pop_back(); assumps.pop_back(); assumps.pop_back();
                if (r2 != l_False) continue;

                // Under L=v1 → test=0, under L=v2 → test=1, and v1≠v2.
                // So test = L if v1=l_False, else test = ~L.
                const bool test_equals_l = (v1 == l_False);

                // Set the AIG def (in ORIG variable space).
                assert(new_to_orig.count(test) > 0);
                assert(new_to_orig.count(l_var) > 0);
                const Lit test_orig = new_to_orig.at(test);
                const Lit l_orig    = new_to_orig.at(l_var);
                // Defensive: never produce a self-referential def. Distinct
                // NEW vars should map to distinct ORIG vars after the usual
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
                new_cond_defs++;
                verb_print(2, "[unate_def] cond def: NEW test " << test+1
                    << " = " << (test_equals_l ? "" : "~") << "NEW " << (l_var+1)
                    << " (orig: " << test_orig.var()+1 << " "
                    << (def_neg ? "-" : "+") << l_orig.var()+1
                    << ") T: " << fixed << setprecision(2) << (cpuTime()-my_time));

                // Tighten the SAT solver: equate test on both sides to L
                // (or its negation). Implies the indicator becoming TRUE,
                // and helps subsequent tests prove more.
                // NEW lit `test_x ⇔ (test_equals_l ? l_var : ~l_var)`
                {
                    const Lit lit_t_x = Lit(test, false);
                    const Lit lit_t_y = Lit(test + nv, false);
                    const Lit lit_l   = Lit(l_var, !test_equals_l);
                    s->add_clause({~lit_t_x, lit_l});
                    s->add_clause({lit_t_x, ~lit_l});
                    s->add_clause({~lit_t_y, lit_l});
                    s->add_clause({lit_t_y, ~lit_l});
                }
                found_def = true;
                cond_attempts_since_last_hit = 0;
                break;
            }
            if (cond_enabled
                    && cond_attempts_since_last_hit >= cond_dry_streak_disable
                    && new_cond_defs == 0) {
                verb_print(1, "[unate_def] disabling cond probe after "
                        << cond_attempts_since_last_hit
                        << " dry attempts");
                cond_enabled = false;
            }
        }
        already_tested.insert(test);
        s->add_clause({Lit(var_to_indic.at(test), false)});
    }

    double total_time = cpuTime() - my_time;
    verb_print(1, COLYEL "[unate_def] "
            << " units: " << setw(7) << new_units
            << " cond defs: " << setw(7) << new_cond_defs
            << " cond calls: " << setw(7) << cond_calls
            << " tested: " << setw(7) << tested_num
            << " tests/s: " << setprecision(2) << fixed << setw(6) << safe_div(tested_num, total_time));

    cnf.add_fixed_values(unates);
    auto [input2, to_define2, backward_defined2] = cnf.get_var_types(0 | verbose_debug_enabled, "end do_unate_def");
    verb_print(1, COLRED "[unate_def] Done. synthesis_unate_def"
        << " tested: " << tested_num
        << " defined: " << to_define.size() - to_define2.size()
        << " still to define: " << to_define2.size()
        << " T: " << total_time);
}

void Unate::synthesis_unate(SimplifiedCNF& cnf) {
    double my_time = cpuTime();
    uint32_t new_units = 0;
    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate").unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[unate] No variables to define, skipping");
        return;
    }

    auto s = setup_f_not_f(cnf);
    var_to_indic.clear();
    var_to_indic.resize(cnf.nVars(), var_Undef);
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
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
    /* if (conf.verb >= 3) dump_cnf<Lit>(*s, "unate-start.cnf", input); */

    vector<Lit> assumps;
    vector<Lit> cl;

    uint32_t tested_num = 0;
    vector<Lit> unates;
    for(uint32_t test: to_define) {
        assert(input.count(test) == 0);
        verb_print(3, "[unate] testing var: " << test+1);
        /* if (s->removed_var(test)) continue; */
        tested_num++;
        if (tested_num % 300 == 299) {
            verb_print(1, "[unate] test no: " << setw(5) << tested_num
                << " new units: " << setw(4) << new_units
                << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
        }

        for(int flip = 0; flip < 2; flip++) {
            assumps.clear();
            assumps.push_back(Lit(test, !flip));
            assumps.push_back(Lit(test+cnf.nVars(), flip));
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                if (i == test) continue;
                if (input.count(i)) continue;
                auto ind = var_to_indic.at(i);
                assert(ind != var_Undef);
                assumps.push_back(Lit(ind, false));
            }
            verb_print(3, "[unate] assumps : " << assumps);
            const auto ret = s->solve(&assumps);
            if (ret == l_False) {

                Lit l = {Lit(test, flip)};
                unates.push_back(l);
                cnf.add_clause({l});
                verb_print(2, "[unate] good test. Setting: " << std::setw(3)  << l
                    << " T: " << fixed << setprecision(2) << (cpuTime() - my_time));

                l = Lit(test+cnf.nVars(), flip);
                cl = {l};
                s->add_clause(cl);
                new_units++;
                break;
            }
        }
    }

    cnf.add_fixed_values(unates);
    auto [input2, to_define2, backward_defined2] = cnf.get_var_types(0 | verbose_debug_enabled, "end do_unate");
    verb_print(1, COLRED "[unate] Done. synthesis_unate"
        << " tested: " << tested_num
        << " defined: " << to_define.size() - to_define2.size()
        << " still to define: " << to_define2.size()
        << " T: " << (cpuTime() - my_time));
}

unique_ptr<ArjunInt::MetaSolver> Unate::setup_f_not_f(const SimplifiedCNF& cnf) {
    double my_time = cpuTime();

    vector<Lit> tmp;
    auto s = std::make_unique<ArjunInt::MetaSolver>();
    s->new_vars(cnf.nVars()*2); // one for orig, one for copy
    s->set_verbosity(0);

    vector<Lit> not_f_cls;
    for(const auto& cl: cnf.get_clauses()) {
        // F(x)
        s->add_clause(cl);

        // !F(y)
        s->new_var(); // new var for each clause
                      // z is true iff clause is TRUE
        const Lit z = Lit(s->nVars()-1, false);

        // (C shifted) V -z
        tmp.clear();
        for(const auto& l: cl) {
            if (input.count(l.var())) tmp.push_back(l);
            else tmp.push_back(Lit(l.var()+cnf.nVars(), l.sign()));
        }
        tmp.push_back(~z);
        s->add_clause(tmp);

        // (each -lit in C, shifted) V z
        for(const auto& l: cl) {
            tmp.clear();
            if (input.count(l.var())) tmp = {~l,  z};
            else tmp = {Lit(l.var()+cnf.nVars(), !l.sign()),  z};
            s->add_clause(tmp);
        }
        not_f_cls.push_back(~z);
    }

    // At least ONE clause must be FALSE
    s->add_clause(not_f_cls);

    verb_print(1, "[unate/def] Built up the F and ~F_x_y solver. T: "
            << fixed << setprecision(2) << (cpuTime() - my_time));
    return s;
}
