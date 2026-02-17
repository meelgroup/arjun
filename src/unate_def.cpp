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
#include "time_mem.h"
#include <iomanip>

using namespace ArjunNS;
using std::setprecision;
using std::fixed;

void Unate::synthesis_unate_def(SimplifiedCNF& cnf) {
    double my_time = cpuTime();
    uint32_t new_units = 0;
    std::tie(input, to_define, backward_defined) = cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate_def");
    if (to_define.empty()) {
        verb_print(1, "[unate_def] No variables to define, skipping");
        return;
    }
    sampl_set.clear();
    for(const auto& v: cnf.get_opt_sampl_vars()) sampl_set.insert(v);

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
        if (sampl_set.count(i_new)) continue;

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
                if (sampl_set.count(lit_new.var())) return lit_new;
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
            assert(false && "Unhandled AIG type in synthesis_unate_def");
            exit(EXIT_FAILURE);
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
        if (sampl_set.count(i)) continue;
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
    if (conf.verb >= 3) dump_cnf<Lit>(*s, "unate_def-start.cnf", sampl_set);

    vector<Lit> assumps;
    vector<Lit> cl;
    s->set_bve(false);

    uint32_t tested_num = 0;
    vector<Lit> unates;
    for(uint32_t test: to_define) {
        assert(sampl_set.count(test) == 0);
        verb_print(3, "[unate_def] testing var: " << test+1);
        tested_num++;
        if (tested_num % 300 == 299) {
            verb_print(1, "[unate_def] test no: " << setw(5) << tested_num
                << " confl K: " << setw(4) << s->get_sum_conflicts()/1000
                << " new units: " << setw(4) << new_units
                << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
        }

        for(int flip = 0; flip < 2; flip++) {
            assumps.clear();
            assumps.push_back(Lit(test, !flip));
            assumps.push_back(Lit(test+cnf.nVars(), flip));
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                if (i == test) continue;
                if (sampl_set.count(i)) continue;
                if (backward_defined.count(i)) continue;
                auto ind = var_to_indic.at(i);
                assert(ind != var_Undef);
                assumps.push_back(Lit(ind, false));
            }
            verb_print(3, "[unate_def] assumps : " << assumps);
            s->set_no_confl_needed();
            s->set_max_confl(conf.backw_max_confl);
            const auto ret = s->solve(&assumps, true);
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
                break;
            }
        }
    }

    cnf.add_fixed_values(unates);
    auto [input2, to_define2, backward_defined2] = cnf.get_var_types(0 | verbose_debug_enabled, "end do_unate_def");
    verb_print(1, COLRED "[unate_def] Done. synthesis_unate_def"
        << " tested: " << tested_num
        << " defined: " << to_define.size() - to_define2.size()
        << " still to define: " << to_define2.size()
        << " T: " << (cpuTime() - my_time));
}

void Unate::synthesis_unate(SimplifiedCNF& cnf) {
    double my_time = cpuTime();
    uint32_t new_units = 0;
    std::tie(input, to_define, backward_defined) = cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate");
    if (to_define.empty()) {
        verb_print(1, "[unate] No variables to define, skipping");
        return;
    }
    sampl_set.clear();
    for(const auto& v: cnf.get_opt_sampl_vars()) sampl_set.insert(v);

    auto s = setup_f_not_f(cnf);
    var_to_indic.clear();
    var_to_indic.resize(cnf.nVars(), var_Undef);
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (sampl_set.count(i)) continue;
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
    if (conf.verb >= 3) dump_cnf<Lit>(*s, "unate-start.cnf", sampl_set);

    vector<Lit> assumps;
    vector<Lit> cl;
    s->set_bve(false);

    uint32_t tested_num = 0;
    vector<Lit> unates;
    for(uint32_t test: to_define) {
        assert(sampl_set.count(test) == 0);
        verb_print(3, "[unate] testing var: " << test+1);
        /* if (s->removed_var(test)) continue; */
        tested_num++;
        if (tested_num % 300 == 299) {
            verb_print(1, "[unate] test no: " << setw(5) << tested_num
                << " confl K: " << setw(4) << s->get_sum_conflicts()/1000
                << " new units: " << setw(4) << new_units
                << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
        }

        for(int flip = 0; flip < 2; flip++) {
            assumps.clear();
            assumps.push_back(Lit(test, !flip));
            assumps.push_back(Lit(test+cnf.nVars(), flip));
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                if (i == test) continue;
                if (sampl_set.count(i)) continue;
                auto ind = var_to_indic.at(i);
                assert(ind != var_Undef);
                assumps.push_back(Lit(ind, false));
            }
            verb_print(3, "[unate] assumps : " << assumps);
            s->set_no_confl_needed();
            s->set_max_confl(conf.unate_max_confl);
            const auto ret = s->solve(&assumps, true);
            if (ret == l_False) {

                Lit l = {Lit(test, flip)};
                unates.push_back(l);
                cnf.add_clause({l});
                verb_print(2, "[unate] good test. Setting: " << std::setw(3)  << l
                    << " T: " << fixed << setprecision(2) << (cpuTime() - my_time));

                /* cl = {Lit(test, flip)}; */
                /* cnf.add_clause(cl); */
                /* s->add_clause(cl); */
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

unique_ptr<SATSolver> Unate::setup_f_not_f(const SimplifiedCNF& cnf) {
    double my_time = cpuTime();

    vector<Lit> tmp;
    auto s = std::make_unique<SATSolver>();
    s->new_vars(cnf.nVars()*2); // one for orig, one for copy
    s->set_verbosity(0);
    s->set_prefix("c o ");
    s->set_bve(false);
    s->set_bva(false);
    s->set_no_simplify_at_startup();
    s->set_simplify(false);
    s->set_sls(false);
    s->set_find_xors(false);

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
            if (sampl_set.count(l.var())) tmp.push_back(l);
            else tmp.push_back(Lit(l.var()+cnf.nVars(), l.sign()));
        }
        tmp.push_back(~z);
        s->add_clause(tmp);

        // (each -lit in C, shifted) V z
        for(const auto& l: cl) {
            tmp.clear();
            if (sampl_set.count(l.var())) tmp = {~l,  z};
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
