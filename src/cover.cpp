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


#include "cover.h"
#include "metasolver.h"
#include "time_mem.h"
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <limits>
#include <map>

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::vector;
using std::map;

lbool ArjunInt::cover(SimplifiedCNF& cnf, const vector<vector<Lit>>& cls, const double budget,
        const uint64_t max_ticks,
        const bool stop_at_cex, const bool need_funs, const bool minim, vector<lbool>& cex,
        const uint32_t verb) {
    const double my_time = cpuTime();
    const auto& orig_sampl_vars = cnf.get_orig_sampl_vars();
    const auto& aig_mng = cnf.get_aig_mng();
    const uint32_t num_defs = cnf.num_defs();
    MetaSolver abs, f;
    abs.set_no_lucky();
    f.set_no_lucky();
    f.set_decide(false);
    // The solvers only get the vars they have clauses on: the universals,
    // at the same index in both, then for f the existentials of cls
    const uint32_t none = std::numeric_limits<uint32_t>::max();
    vector<uint32_t> to_f(num_defs, none), ys;
    for (const auto& v : orig_sampl_vars) {
        to_f[v] = f.nVars();
        f.new_var();
        abs.new_var();
    }
    auto in_f = [&](const Lit l) { return Lit(to_f[l.var()], l.sign()); };
    for (const auto& cl : cls) {
        vector<Lit> cl2;
        for (const auto& l : cl) {
            if (to_f[l.var()] == none) {
                to_f[l.var()] = f.nVars();
                f.new_var();
                ys.push_back(l.var());
            }
            cl2.push_back(in_f(l));
        }
        f.add_clause(cl2);
    }

    // per clause with universals: its existentials, and a helper that
    // implies all of its universal literals are false
    map<vector<Lit>, Lit> univ_to_helper;
    vector<std::pair<vector<Lit>, Lit>> mixed;
    vector<aig_lit> univ_true; // per helper: some universal literal of it is true
    for (const auto& cl : cls) {
        vector<Lit> univ, exist;
        for (const auto& l : cl) {
            if (orig_sampl_vars.count(l.var())) univ.push_back(l);
            else exist.push_back(in_f(l));
        }
        if (univ.empty()) continue;
        std::sort(univ.begin(), univ.end());
        const auto [it, inserted] = univ_to_helper.try_emplace(univ, lit_Undef);
        if (inserted) {
            abs.new_var();
            it->second = Lit(abs.nVars()-1, false);
            univ_true.push_back(aig_mng.new_const(false));
            for (const auto& l : univ) {
                abs.add_clause({~it->second, ~in_f(l)});
                univ_true.back() = AIG::new_or(univ_true.back(), AIG::new_lit(l));
            }
        }
        mixed.emplace_back(exist, it->second);
    }
    const uint32_t num_helpers = univ_to_helper.size();
    auto hidx = [&](const Lit h) { return h.var() - orig_sampl_vars.size(); };

    // selector of a helper, in f: the existentials satisfy all of its clauses
    const uint32_t sel_at = f.nVars();
    auto sel = [&](const uint32_t i) { return Lit(sel_at + i, false); };
    if (minim) {
        for (uint32_t i = 0; i < num_helpers; i++) f.new_var();
        for (const auto& [exist, helper] : mixed) {
            auto cl = exist;
            cl.push_back(~sel(hidx(helper)));
            f.add_clause(cl);
        }
    }
    // a helper that a core kept out of the model sits out 1, 3, 7.. of its next tries
    const uint32_t max_wait = 7;
    vector<uint32_t> wait(num_helpers, 0), skip(num_helpers, 0);
    vector<char> is_false(num_helpers), in_core(num_helpers);

    // a model that satisfies many existential parts makes a short refinement
    vector<int> pos_occ(f.nVars(), 0);
    for (const auto& [exist, helper] : mixed) for (const auto& l : exist) pos_occ[l.var()] += l.sign() ? -1 : 1;
    for (const auto& v : ys) f.set_phase(Lit(to_f[v], pos_occ[to_f[v]] <= 0));

    // per refinement, for the Skolem functions: its helpers, and the model's Y
    vector<vector<Lit>> ref_helpers;
    vector<bool> ref_ys;

    vector<Lit> assumps, some_false;
    auto sq_frac = [](const double num, const double of) { return num == 0 ? 0 : (num / of) * (num / of); };
    double cost = 0;
    uint64_t rounds = 0, ref_lits = 0, cubes = 0, cube_lits = 0, minim_calls = 0, minim_removed = 0;
    double abs_time = 0, f_time = 0, refine_time = 0, funs_time = 0;
    const double setup_time = cpuTime() - my_time;
    auto ticks = [&] { return abs.get_sum_ticks() + f.get_sum_ticks(); };
    auto stats = [&](const char* what) {
        if (!verb) return;
        const uint64_t refs = rounds - cubes;
        std::cout << "c o [cover] " << what << " rounds: " << rounds << " no-Y cubes: " << cubes
            << " helpers: " << num_helpers << std::fixed
            << " avg refinement: " << std::setprecision(1) << (refs ? (double)ref_lits / refs : 0)
            << " avg cube: " << (cubes ? (double)cube_lits / cubes : 0)
            << " minim calls: " << minim_calls << " removed: " << minim_removed
            << " cost: " << std::setprecision(2) << cost << " of " << budget
            << " ticks(M) abs: " << abs.get_sum_ticks() / 1e6 << " f: " << f.get_sum_ticks() / 1e6
            << " confl abs: " << abs.get_sum_conflicts() << " f: " << f.get_sum_conflicts()
            << " T: " << (cpuTime() - my_time) << " (setup: " << setup_time << " abs: " << abs_time
            << " f: " << f_time << " refine: " << refine_time << " funs: " << funs_time << ")" << std::endl;
    };
    auto finish = [&](const lbool ret) {
        stats(ret == l_True ? "all X covered" : ret == l_False ? "X with no Y" : "gave up");
        return ret;
    };
    auto timed = [](double& sum, auto&& fun) {
        const double start = cpuTime();
        const auto ret = fun();
        sum += cpuTime() - start;
        return ret;
    };
    // y takes its value from the first model that works for X. Built from
    // the rarer value of y, the other one is the default
    auto build_funs = [&] {
        vector<aig_lit> first;
        aig_lit covered = aig_mng.new_const(false);
        for (const auto& ref : ref_helpers) {
            aig_lit works = aig_mng.new_const(true);
            for (const auto& h : ref) works = AIG::new_and(works, univ_true[hidx(h)]);
            first.push_back(AIG::new_and(works, ~covered));
            covered = AIG::new_or(covered, works);
        }
        for (uint32_t i = 0; i < ys.size(); i++) {
            if (cnf.defined(ys[i])) continue;
            uint32_t num_true = 0;
            for (uint32_t r = 0; r < ref_helpers.size(); r++) num_true += ref_ys[r * ys.size() + i];
            const bool val = num_true * 2 <= ref_helpers.size();
            aig_lit fun = aig_mng.new_const(false);
            for (uint32_t r = 0; r < ref_helpers.size(); r++)
                if (ref_ys[r * ys.size() + i] == val) fun = AIG::new_or(fun, first[r]);
            cnf.set_def(ys[i], val ? fun : ~fun);
        }
        for (uint32_t v = 0; v < num_defs; v++)
            if (!orig_sampl_vars.count(v) && !cnf.defined(v)) cnf.set_def(v, aig_mng.new_const(false));
    };
    auto get_some_false = [&](const vector<lbool>& model) {
        some_false.clear();
        for (const auto& [exist, helper] : mixed) {
            const bool sat = std::any_of(exist.begin(), exist.end(),
                    [&](const Lit l) { return model[l.var()] == boolToLBool(!l.sign()); });
            if (!sat) some_false.push_back(helper);
        }
        std::sort(some_false.begin(), some_false.end());
        some_false.erase(std::unique(some_false.begin(), some_false.end()), some_false.end());
    };
    // A model for the X of assumps whose existentials satisfy what those of
    // `model` do, and as many more helpers' clauses as the cores allow
    auto minimize = [&](vector<lbool> model) {
        const size_t num_x = assumps.size();
        std::fill(is_false.begin(), is_false.end(), 0);
        for (const auto& h : some_false) is_false[hidx(h)] = 1;
        for (uint32_t i = 0; i < num_helpers; i++) if (!is_false[i]) assumps.push_back(sel(i));
        const size_t base = assumps.size();
        vector<uint32_t> cand, cand2;
        for (const auto& h : some_false) {
            if (skip[hidx(h)]) skip[hidx(h)]--;
            else cand.push_back(hidx(h));
        }
        while (!cand.empty()) {
            assumps.resize(base);
            for (const auto& i : cand) assumps.push_back(sel(i));
            minim_calls++;
            if (f.solve(&assumps) == l_True) {
                model = f.get_model();
                for (const auto& i : cand) wait[i] = 0;
                break;
            }
            const auto core = f.get_conflict();
            for (const auto& l : core) if (l.var() >= sel_at) in_core[l.var() - sel_at] = 1;
            cand2.clear();
            for (const auto& i : cand) {
                if (!in_core[i]) { cand2.push_back(i); continue; }
                wait[i] = std::min(wait[i] * 2 + 1, max_wait);
                skip[i] = wait[i];
            }
            for (const auto& l : core) if (l.var() >= sel_at) in_core[l.var() - sel_at] = 0;
            assert(cand2.size() < cand.size());
            std::swap(cand, cand2);
        }
        assumps.resize(num_x);
        return model;
    };
    for (; cost < budget && (max_ticks == 0 || ticks() < max_ticks); rounds++) {
        if (rounds && rounds % 1000 == 0) stats("progress");
        if (timed(abs_time, [&] { return abs.solve(); }) == l_False) {
            if (need_funs) timed(funs_time, [&] { build_funs(); return 0; });
            return finish(l_True);
        }
        assumps.clear();
        for (const auto& v : orig_sampl_vars) assumps.emplace_back(to_f[v], abs.get_model()[to_f[v]] != l_True);
        if (timed(f_time, [&] { return f.solve(&assumps); }) == l_False) {
            if (stop_at_cex) {
                cex.assign(num_defs, l_Undef);
                for (const auto& v : orig_sampl_vars) cex[v] = abs.get_model()[to_f[v]];
                return finish(l_False);
            }
            // no X in this cube has a Y, so any function will do there
            auto cube = f.get_conflict();
            cube_lits += cube.size();
            cost += sq_frac(cube.size(), orig_sampl_vars.size());
            abs.add_clause(cube);
            cubes++;
            continue;
        }

        const double refine_start = cpuTime();
        auto model = f.get_model();
        get_some_false(model);
        if (minim && some_false.size() > 1) {
            const size_t before = some_false.size();
            model = minimize(model);
            get_some_false(model);
            assert(some_false.size() <= before);
            minim_removed += before - some_false.size();
        }
        abs.add_clause(some_false);
        cost += sq_frac(some_false.size(), num_helpers);
        ref_lits += some_false.size();

        if (need_funs) {
            ref_helpers.push_back(some_false);
            for (const auto& v : ys) ref_ys.push_back(model[to_f[v]] == l_True);
        }
        refine_time += cpuTime() - refine_start;
    }
    return finish(l_Undef);
}
