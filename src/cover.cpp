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

// Model covering: decides ∀X ∃Y φ(X,Y), φ a CNF, by CEGAR over two solvers.
// y_solver holds φ and, for an X given as assumptions, finds a Y or proves
// there is none. x_solver is over X only and proposes the next X that no Y
// found so far covers. Split each clause into its X part U and its Y part E:
// a Y from y_solver works for exactly the X that satisfy U of every clause
// whose E it leaves false, so x_solver gets "one of those U is false". A
// helper var per distinct U (true: all of U is false) keeps these refinements
// short. The fewer U a Y
// needs, the more X it covers: RefinementMinimizer looks for such Y.
// x_solver UNSAT: every X has a Y, and the models, first one that works wins,
// are the Skolem functions. y_solver UNSAT for an X: the cube of its failed
// assumptions has no Y.
//
// This is the abstraction refinement of AReQS [1], generalised to any number
// of quantifier levels by RAReQS [2], with the clauses' universal parts
// selected by variables as in QESTO [3] and CAQE [4]. An earlier comparison
// of 2QBF algorithms, CEGAR among them, is [5].
//
// For counting (Cover::drop_covered), X are the sampling vars and the
// clauses of X only are assumed, not checked. A component whose X all have
// a Y is removed. With keep_cubes, the X-cubes with no Y are kept, minimized,
// as clauses: when x_solver is UNSAT they are ∃Y of the component, which replaces
// it. That is quantifier elimination by minimal blocking clauses, as in [6].
//
// [1] M. Janota, J. Marques-Silva: Abstraction-Based Algorithm for 2QBF. SAT 2011
// [2] M. Janota, W. Klieber, J. Marques-Silva, E. Clarke: Solving QBF with
//     Counterexample Guided Refinement. SAT 2012, and AIJ 234, 2016
// [3] M. Janota, J. Marques-Silva: Solving QBF by Clause Selection. IJCAI 2015
// [4] M. N. Rabe, L. Tentrup: CAQE: A Certifying QBF Solver. FMCAD 2015
// [5] D. P. Ranjan, D. Tang, S. Malik: A Comparative Study of 2QBF Algorithms. SAT 2004
// [6] J. Brauer, A. King, J. Kriener: Existential Quantification as Incremental SAT. CAV 2011

#include "cover.h"
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <cmath>
#include <functional>
#include <numeric>

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::vector;
using std::map;
using std::set;

// Per var of cls: X, a function of X only, or a y; and which ones have a def or no clause
CoverComponent::Classified CoverComponent::classify_defined(const CoverProblem& problem, const vector<vector<Lit>>& cls) {
    SLOW_DEBUG_DO(for (const auto& cl : cls) for (const auto& l : cl) assert(l.var() < problem.size()));
    Classified ret;
    auto& state = ret.kind;
    auto& defined = ret.defined;
    auto& unconstrained = ret.unconstrained;
    vector<char> in_cls(problem.size(), 0);
    state.assign(problem.size(), VarKind::unseen);
    for (const auto& cl : cls) for (const auto& l : cl) in_cls[l.var()] = 1;
    std::function<bool(uint32_t)> fun_of_x = [&](const uint32_t v) {
        if (problem.is_x[v]) return true;
        if (state[v] != VarKind::unseen) return state[v] == VarKind::fun_of_x;
        if (!problem.defined(v)) {
            state[v] = in_cls[v] ? VarKind::y : VarKind::fun_of_x;
            if (!in_cls[v]) unconstrained.push_back(v);
            return state[v] == VarKind::fun_of_x;
        }
        set<uint32_t> deps;
        AIG::get_dependent_vars(problem.def[v], deps, v);
        bool all_x = true;
        for (const auto& d : deps) all_x &= fun_of_x(d);
        state[v] = all_x ? VarKind::fun_of_x : VarKind::y;
        defined.push_back(v);
        return all_x;
    };
    for (const auto& cl : cls) for (const auto& l : cl) fun_of_x(l.var());
    return ret;
}

// The x side and the ys get their solver vars; y_solver gets the clauses
void CoverComponent::add_vars_and_cls() {
    assert(x_side.empty() && y_vars.empty() && solver_var.empty());
    assert(x_solver.nVars() == 0 && y_solver.nVars() == 0);
    auto classified = classify_defined(problem, comp_cls);
    state = std::move(classified.kind);
    defined = std::move(classified.defined);
    unconstrained = std::move(classified.unconstrained);
    // a component of a counted CNF: the universals of the rest are no matter
    vector<char> in_cls(num_vars, !cconf.assume_outer);
    for (const auto& cl : comp_cls) for (const auto& l : cl) in_cls[l.var()] = 1;
    for (uint32_t v = 0; v < num_vars; v++) if (problem.is_x[v] && in_cls[v]) x_side.push_back(v);
    num_x = x_side.size();
    for (const auto& v : defined) if (state[v] == VarKind::fun_of_x) x_side.push_back(v);
    on_x_side.assign(num_vars, 0);
    for (const auto& v : x_side) on_x_side[v] = 1;

    solver_var.assign(num_vars, none);
    for (const auto& v : x_side) {
        new_y_var(v);
        x_solver.new_var();
    }
    for (const auto& cl : comp_cls) {
        // only x_solver gets them: y_solver's cubes are then over the X of the y
        // clauses, and do not tie together X the rest of the CNF keeps apart
        if (cconf.assume_outer && std::all_of(cl.begin(), cl.end(), [&](const Lit l) { return on_x_side[l.var()]; }))
            continue;
        vector<Lit> cl_y;
        for (const auto& l : cl) {
            if (solver_var[l.var()] == none) {
                new_y_var(l.var());
                y_vars.push_back(l.var());
            }
            cl_y.push_back(in_solvers(l));
        }
        y_solver.add_clause(cl_y);
    }
    for (const auto& v : defined) if (solver_var[v] == none) new_y_var(v);
    for (const auto& v : unconstrained) {
        new_y_var(v);
        y_solver.add_clause({Lit(solver_var[v], true)});
    }
    // the x side has the same index in both solvers, X first
    assert(num_x <= x_side.size());
    for (uint32_t i = 0; i < x_side.size(); i++) assert(solver_var[x_side[i]] == i);
}

// the X of the assumptions with the ys of model satisfy what y_solver got of comp_cls
bool CoverComponent::model_satisfies(const vector<lbool>& model) const {
    assert(assumps.size() == num_x);
    assert(model.size() == y_solver.nVars());
    for (const auto& a : assumps)
        if (model[a.var()] != boolToLBool(!a.sign())) return false;
    for (const auto& cl : comp_cls) {
        if (cconf.assume_outer && std::all_of(cl.begin(), cl.end(), [&](const Lit l) { return on_x_side[l.var()]; }))
            continue;
        if (std::none_of(cl.begin(), cl.end(), [&](const Lit l) { return model[solver_var[l.var()]] == boolToLBool(!l.sign()); }))
            return false;
    }
    return true;
}

// y_solver keeps to the functions, so that its models are ones x_solver can rule out
void CoverComponent::tie_defs() {
    assert(solver_var.size() == num_vars);
    assert(aig_refs.empty());
    for (uint32_t v = 0; v < num_vars; v++) if (solver_var[v] != none) defs_in_y.leaf[v] = AIG::new_lit(solver_var[v]);
    for (const auto& v : x_side) {
        defs_in_x.leaf[v] = AIG::new_lit(solver_var[v]);
        defs_in_vars.leaf[v] = AIG::new_lit(v);
    }
    for (const auto& v : unconstrained) defs_in_x.leaf[v] = defs_in_vars.leaf[v] = aig_mng.new_const(false);
    auto tie_to_def = [&](MetaSolver& s, AIGToCNF<MetaSolver>& enc, const uint32_t v) {
        aig_refs.push_back(defs_in_y.of_aig(problem.def[v]).a);
        const Lit out = enc.encode(aig_refs.back());
        const Lit me = Lit(solver_var[v], false);
        s.add_clause({~out, me});
        s.add_clause({out, ~me});
    };
    for (const auto& v : defined) tie_to_def(y_solver, enc_y, v);
    for (uint32_t i = num_x; i < x_side.size(); i++) tie_to_def(x_solver, enc_x, x_side[i]);
}

// A helper per distinct x part of the clauses with ys, in x_solver, and the clauses split by it
void CoverComponent::add_helpers() {
    assert(helpers.empty() && split_cls.empty() && y_def_cls.empty() && x_cls_solver.empty());
    assert(x_solver.nVars() >= x_side.size());
    helper_base = x_solver.nVars();
    map<vector<Lit>, uint32_t> helper_of;
    for (const auto& cl : comp_cls) {
        if (std::any_of(cl.begin(), cl.end(), [&](const Lit l) { return problem.defined(l.var()) && !on_x_side[l.var()]; })) {
            y_def_cls.push_back(cl);
            continue;
        }
        vector<Lit> x_part, y_part;
        for (const auto& l : cl) {
            if (on_x_side[l.var()]) x_part.push_back(l);
            else y_part.push_back(in_solvers(l));
        }
        if (x_part.empty()) continue;
        if (y_part.empty()) {
            for (auto& l : x_part) l = in_solvers(l);
            x_cls_solver.push_back(x_part);
            continue;
        }
        std::sort(x_part.begin(), x_part.end());
        const auto [it, inserted] = helper_of.try_emplace(x_part, helpers.size());
        if (inserted) {
            x_solver.new_var();
            Helper h{x_part, Lit(x_solver.nVars()-1, false), aig_mng.new_const(false)};
            for (const auto& l : x_part) {
                x_solver.add_clause({~h.lit, ~in_solvers(l)});
                h.x_part_true = AIG::new_or(h.x_part_true, AIG::new_lit(l));
            }
            helpers.push_back(std::move(h));
        }
        split_cls.push_back({y_part, it->second});
    }
}

// A selector per helper in y_solver: true, the y parts of its clauses hold
RefinementMinimizer::RefinementMinimizer(MetaSolver& _y_solver, const vector<SplitClause>& split_cls,
        const uint32_t num_helpers, const Arjun::CoverConf& cconf) :
        y_solver(&_y_solver), sel_base(_y_solver.nVars()), max_calls(cconf.max_minim_calls),
        max_wait(cconf.max_minim_wait), backoff(num_helpers, 0), skip_rounds(num_helpers, 0),
        is_false_helper(num_helpers, 0), in_core(num_helpers, 0) {
    for (const auto& split : split_cls) assert(split.helper < num_helpers);
    for (uint32_t i = 0; i < num_helpers; i++) y_solver->new_var();
    for (const auto& split : split_cls) {
        auto cl = split.y_part;
        cl.push_back(~selector(split.helper));
        y_solver->add_clause(cl);
    }
}

// a model that satisfies many existential parts makes a short refinement
void CoverComponent::set_phases() {
    for (const auto& v : y_vars) assert(solver_var[v] != none);
    vector<int> pos_occ(y_solver.nVars(), 0);
    for (const auto& split : split_cls) for (const auto& l : split.y_part) pos_occ[l.var()] += l.sign() ? -1 : 1;
    for (const auto& v : y_vars) if (!problem.defined(v)) y_solver.set_phase(Lit(solver_var[v], pos_occ[solver_var[v]] <= 0));
}

// Asks y_solver for a model of the same X that leaves fewer helpers' y parts false
vector<lbool> RefinementMinimizer::minimize(vector<lbool> model, vector<Lit>& assumps,
        const vector<uint32_t>& false_helpers, const std::function<lbool(vector<Lit>&)>& solve,
        const std::function<bool()>& out_of_ticks) {
    assert(!false_helpers.empty());
    for (const auto& i : false_helpers) assert(i < is_false_helper.size());
    for (const auto& a : assumps) assert(a.var() < sel_base);
    assert(model.size() >= sel_base + is_false_helper.size());
    SLOW_DEBUG_DO(for (const auto& f : in_core) assert(!f));
    const size_t num_x = assumps.size();
    std::fill(is_false_helper.begin(), is_false_helper.end(), 0);
    for (const auto& i : false_helpers) is_false_helper[i] = 1;
    for (uint32_t i = 0; i < is_false_helper.size(); i++)
      if (!is_false_helper[i]) assumps.push_back(selector(i));
    const size_t base = assumps.size();
    vector<uint32_t> to_try, still_to_try;
    for (const auto& i : false_helpers) {
        if (skip_rounds[i]) skip_rounds[i]--;
        else to_try.push_back(i);
    }

    // Capped: with every core a single helper, it is a call per helper
    for (uint32_t n = 0; !to_try.empty() && n < max_calls && !out_of_ticks(); n++) {
        assumps.resize(base);
        for (const auto& i : to_try) assumps.push_back(selector(i));
        calls++;
        const auto ret = solve(assumps);
        if (ret == l_Undef) break;
        if (ret == l_True) {
            model = y_solver->get_model();
            for (const auto& i : to_try) backoff[i] = 0;
            break;
        }
        const auto core = y_solver->get_conflict();
        for (const auto& l : core) if (l.var() >= sel_base) in_core[l.var() - sel_base] = 1;
        still_to_try.clear();
        for (const auto& i : to_try) {
            if (!in_core[i]) { still_to_try.push_back(i); continue; }
            backoff[i] = std::min(backoff[i] * 2 + 1, max_wait);
            skip_rounds[i] = backoff[i];
        }
        for (const auto& l : core) if (l.var() >= sel_base) in_core[l.var() - sel_base] = 0;
        assert(still_to_try.size() < to_try.size());
        std::swap(to_try, still_to_try);
    }
    assumps.resize(num_x);
    return model;
}

// The helpers of the clauses whose y part model leaves false
void CoverComponent::compute_refinement(const vector<lbool>& model) {
    assert(model.size() == y_solver.nVars());
    refinement.clear();
    for (const auto& split : split_cls) {
        const bool sat = std::any_of(split.y_part.begin(), split.y_part.end(),
                [&](const Lit l) { return model[l.var()] == boolToLBool(!l.sign()); });
        if (!sat) refinement.push_back(helpers[split.helper].lit);
    }
    std::sort(refinement.begin(), refinement.end());
    refinement.erase(std::unique(refinement.begin(), refinement.end()), refinement.end());
}

// the X that satisfy the y_def_cls, given the ys in s.val
aig_lit CoverComponent::y_def_cls_hold(Subst& s) {
    assert(!y_def_cls.empty());
    s.new_round();
    aig_lit ret = aig_mng.new_const(true);
    for (const auto& cl : y_def_cls) {
        aig_lit cl_true = aig_mng.new_const(false);
        for (const auto& l : cl) {
            const auto a = s.of_var(l.var()).a;
            cl_true = AIG::new_or(cl_true, l.sign() ? ~a : a);
        }
        ret = AIG::new_and(ret, cl_true);
    }
    return ret;
}

// y takes its value from the first model that works for X. Built from
// the rarer value of y, the other one is the default
void CoverComponent::build_funs(Funs& funs) {
    assert(cconf.need_funs);
    assert(ref_models.size() == refinements.size() * y_vars.size());
    assert(funs.empty());
    // `before`: an earlier model works. In blocks, a chain would be as deep as the rounds
    const uint32_t num_refs = refinements.size();
    const uint32_t block_size = std::max<uint32_t>(1, std::sqrt(num_refs));
    vector<aig_lit> first_works;
    aig_lit before_block = aig_mng.new_const(false), in_block = aig_mng.new_const(false);
    for (uint32_t r = 0; r < num_refs; r++) {
        if (r % block_size == 0) {
            before_block = AIG::new_or(before_block, in_block);
            in_block = aig_mng.new_const(false);
        }
        for (uint32_t i = 0; i < y_vars.size(); i++) defs_in_vars.val[y_vars[i]] = boolToLBool(ref_models[r * y_vars.size() + i]);
        aig_lit model_works = y_def_cls.empty() ? aig_mng.new_const(true) : y_def_cls_hold(defs_in_vars);
        for (const auto& h : refinements[r]) model_works = AIG::new_and(model_works, helpers[helper_idx(h)].x_part_true);
        first_works.push_back(AIG::new_and(model_works, ~AIG::new_or(before_block, in_block)));
        in_block = AIG::new_or(in_block, model_works);
    }
    vector<aig_lit> when_val;
    for (uint32_t i = 0; i < y_vars.size(); i++) {
        if (problem.defined(y_vars[i])) continue;
        uint32_t num_ones = 0;
        for (uint32_t r = 0; r < num_refs; r++) num_ones += ref_models[r * y_vars.size() + i];
        const bool val = num_ones * 2 <= num_refs;
        when_val.clear();
        for (uint32_t r = 0; r < num_refs; r++) if (ref_models[r * y_vars.size() + i] == val) when_val.push_back(first_works[r]);
        for (uint32_t step = 1; step < when_val.size(); step *= 2)
            for (uint32_t j = 0; j + step < when_val.size(); j += 2 * step) when_val[j] = AIG::new_or(when_val[j], when_val[j + step]);
        const aig_lit fun = when_val.empty() ? aig_mng.new_const(false) : when_val[0];
        funs.emplace_back(y_vars[i], val ? fun : ~fun);
    }
}

// One [cover] line of the component's progress, with what it ended with
void CoverComponent::print_stats(const char* what) {
    if (!verb) return;
    const uint64_t refs = stats.rounds - stats.num_cubes;
    std::cout << "c o [cover] " << what << " rounds: " << stats.rounds << " no-Y cubes: " << stats.num_cubes
        << " outer defs: " << x_side.size() - num_x << " y-def cls: " << y_def_cls.size()
        << " outer cls: " << x_cls_solver.size()
        << " helpers: " << helpers.size() << std::fixed
        << " avg refinement: " << std::setprecision(1) << (refs ? (double)stats.ref_lits / refs : 0)
        << " avg cube: " << (stats.num_cubes ? (double)stats.cube_lits / stats.num_cubes : 0)
        << " minim calls: " << minimizer.calls << " removed: " << stats.minim_removed
        << " cost: " << std::setprecision(2) << budget_used << " of " << cconf.budget
        << " ticks(M) x: " << x_solver.get_sum_ticks() / 1e6 << " y: " << y_solver.get_sum_ticks() / 1e6
        << " y-def: " << defs_in_x.work * 10 / 1e6
        << " confl x: " << x_solver.get_sum_conflicts() << " y: " << y_solver.get_sum_conflicts()
        << " T: " << (cpuTime() - stats.start_time) << " (setup: " << stats.setup_time << " x: " << stats.x_time
        << " y: " << stats.y_time << " refine: " << stats.refine_time << " y-def: " << stats.y_def_time
        << " funs: " << stats.funs_time << ")" << std::endl;
}

// A call that would go over max_ticks stops and gives up the component
lbool CoverComponent::solve(MetaSolver& solver, vector<Lit>* assumptions) {
    if (assumptions) for (const auto& a : *assumptions) assert(a.var() < solver.nVars());
    if (max_ticks) {
        const uint64_t used = ticks();
        if (used >= max_ticks) gave_up = true;
        if (gave_up) return l_Undef;
        solver.set_max_ticks(max_ticks - used);
    }
    const auto ret = assumptions ? solver.solve(assumptions) : solver.solve();
    if (ret == l_Undef) gave_up = true;
    return ret;
}

// Prints the outcome, returns it
lbool CoverComponent::finish(const lbool ret) {
    print_stats(ret == l_True ? "all X covered" : ret == l_False ? "X with no Y" : "gave up");
    return ret;
}

// The X of x_solver's model, in the numbering of problem
void CoverComponent::cex_from_x_solver(vector<lbool>& cex) {
    assert(cex.empty());
    cex.assign(num_vars, l_Undef);
    for (uint32_t i = 0; i < num_x; i++) cex[x_side[i]] = x_solver.get_model()[solver_var[x_side[i]]];
}

// A clause of x side vars only: an X that falsifies it has no Y. As a
// helper it would be in every refinement
bool CoverComponent::x_cls_cex(vector<lbool>& cex) {
    assert(cex.empty());
    assert(cconf.stop_at_cex && !cconf.assume_outer);
    assert(stats.rounds == 0);
    if (x_cls_solver.empty()) return false;
    x_solver.new_var();
    vector<Lit> falsified = {Lit(x_solver.nVars()-1, true)};
    for (const auto& cl : x_cls_solver) {
        x_solver.new_var();
        falsified.emplace_back(x_solver.nVars()-1, false);
        for (const auto& l : cl) x_solver.add_clause({~falsified.back(), ~l});
    }
    x_solver.add_clause(falsified);
    assumps = {~falsified[0]};
    const auto ret = timed(stats.x_time, [&] { return solve(x_solver, &assumps); });
    if (ret == l_True) {
        cex_from_x_solver(cex);
        return true;
    }
    if (ret == l_Undef) return false;
    x_solver.add_clause({falsified[0]});
    return false;
}

// no X in the cube of y_solver's conflict has a Y, so any function will do there
void CoverComponent::block_no_y_cube() {
    // y_solver just found no Y for the X in assumps
    assert(!cconf.stop_at_cex);
    assert(assumps.size() == num_x);
    auto cube = y_solver.get_conflict();
    // A kept cube becomes a clause of the counted CNF: the shorter, the more it propagates
    if (cconf.keep_cubes && cconf.minim_cubes) {
        vector<Lit> cand = cube, without_l;
        for (const auto& l : cand) {
            if (out_of_ticks()) break;
            if (std::find(cube.begin(), cube.end(), l) == cube.end()) continue;
            without_l.clear();
            for (const auto& l2 : cube) if (l2 != l) without_l.push_back(~l2);
            if (timed(stats.y_time, [&] { return solve(y_solver, &without_l); }) == l_False) cube = y_solver.get_conflict();
        }
    }
    for (const auto& l : cube) assert(l.var() < num_x);
    SLOW_DEBUG_DO({
        vector<Lit> cube_negated;
        for (const auto& l : cube) cube_negated.push_back(~l);
        assert(y_solver.solve(&cube_negated) == l_False);
    });
    stats.cube_lits += cube.size();
    budget_used += frac_squared(cube.size(), num_x);
    x_solver.add_clause(cube);
    stats.num_cubes++;
    if (cconf.keep_cubes) {
        kept_cubes.emplace_back();
        for (const auto& l : cube) kept_cubes.back().emplace_back(x_side[l.var()], l.sign());
        return;
    }
    // From here on x_solver only picks an X that has a Y: cubes say
    // little, the files that have them need 100k+ of them
    if (stats.num_cubes == 1) x_solver_gets_cls();
}

// x_solver gets all of comp_cls, ys included, so it only proposes X that have a Y
void CoverComponent::x_solver_gets_cls() {
    assert(!cconf.keep_cubes);
    assert(stats.num_cubes == 1);
    vector<uint32_t> to_x(num_vars, none);
    for (const auto& v : x_side) to_x[v] = solver_var[v];
    for (const auto& v : y_vars) {
        to_x[v] = x_solver.nVars();
        x_solver.new_var();
    }
    vector<Lit> cl2;
    for (const auto& cl : comp_cls) {
        cl2.clear();
        for (const auto& l : cl) cl2.emplace_back(to_x[l.var()], l.sign());
        x_solver.add_clause(cl2);
    }
}

// x_solver gets the X that the model of y_solver settles
void CoverComponent::refine() {
    const double refine_start = cpuTime();
    auto model = y_solver.get_model();
    assert(assumps.size() == num_x);
    SLOW_DEBUG_DO(assert(model_satisfies(model)));
    compute_refinement(model);
    if (sat_minim && refinement.size() > 1) {
        const size_t before = refinement.size();
        vector<uint32_t> false_helper_idxs;
        for (const auto& h : refinement) false_helper_idxs.push_back(helper_idx(h));
        model = minimizer.minimize(model, assumps, false_helper_idxs,
                [&](vector<Lit>& assumptions) { return solve(y_solver, &assumptions); },
                [&] { return out_of_ticks(); });
        assert(assumps.size() == num_x);
        SLOW_DEBUG_DO(assert(model_satisfies(model)));
        compute_refinement(model);
        assert(refinement.size() <= before);
        stats.minim_removed += before - refinement.size();
    }
    budget_used += frac_squared(refinement.size(), helpers.size());
    // progress: the X at hand satisfies every x part named, so it is now ruled out
    SLOW_DEBUG_DO(for (const auto& h : refinement) {
        assert(h.var() >= helper_base && helper_idx(h) < helpers.size());
        const auto& xp = helpers[helper_idx(h)].x_part;
        assert(std::any_of(xp.begin(), xp.end(), [&](const Lit l) { return model[solver_var[l.var()]] == boolToLBool(!l.sign()); }));
    });
    stats.ref_lits += refinement.size();
    if (cconf.need_funs) {
        refinements.push_back(refinement);
        for (const auto& v : y_vars) ref_models.push_back(model[solver_var[v]] == l_True);
    }
    stats.refine_time += cpuTime() - refine_start;
    if (!y_def_cls.empty()) {
        const double y_def_start = cpuTime();
        for (const auto& v : y_vars) defs_in_x.val[v] = model[solver_var[v]];
        aig_refs.push_back(y_def_cls_hold(defs_in_x));
        if (aig_refs.back()->type != AIGT::t_const) refinement.push_back(~enc_x.encode(aig_refs.back()));
        else assert(!aig_refs.back().neg);
        stats.y_def_time += cpuTime() - y_def_start;
    }
    x_solver.add_clause(refinement);
}

// The CEGAR loop: x_solver proposes an X, y_solver finds it a Y or proves there is none
CoverComponent::Result CoverComponent::cegar_run() {
    assert(stats.rounds == 0);
    Result result;
    auto done = [&](const lbool ret) {
        result.ret = finish(ret);
        return std::move(result);
    };
    stats.start_time = cpuTime();
    x_solver.set_no_lucky();
    y_solver.set_no_lucky();
    y_solver.set_decide(false);
    add_vars_and_cls();
    tie_defs();
    add_helpers();
    if (sat_minim) minimizer = RefinementMinimizer(y_solver, split_cls, helpers.size(), cconf);
    set_phases();
    stats.setup_time = cpuTime() - stats.start_time;

    if (cconf.stop_at_cex && !cconf.assume_outer && x_cls_cex(result.cex)) return done(l_False);
    for (const auto& cl : x_cls_solver) x_solver.add_clause(cl);
    for (; budget_used < cconf.budget && !out_of_ticks(); stats.rounds++) {
        if (stats.rounds && stats.rounds % cconf.stats_every == 0) print_stats("progress");
        const auto x_ret = timed(stats.x_time, [&] { return solve(x_solver); });
        if (x_ret == l_Undef) break;
        if (x_ret == l_False) {
            if (cconf.need_funs) timed(stats.funs_time, [&] { build_funs(result.funs); return 0; });
            // a function of X is tied to its def here, which these clauses may be what enforce
            result.every_x_has_y = stats.num_cubes == 0 && x_side.size() == num_x;
            return done(l_True);
        }
        assumps.clear();
        for (uint32_t i = 0; i < num_x; i++) assumps.emplace_back(solver_var[x_side[i]], x_solver.get_model()[solver_var[x_side[i]]] != l_True);
        const auto y_ret = timed(stats.y_time, [&] { return solve(y_solver, &assumps); });
        if (y_ret == l_Undef) break;
        if (y_ret == l_False) {
            if (cconf.stop_at_cex) {
                cex_from_x_solver(result.cex);
                return done(l_False);
            }
            const auto cubes_before = kept_cubes.size();
            block_no_y_cube();
            if (cconf.keep_cubes) assert(kept_cubes.size() == cubes_before + 1);
            else assert(kept_cubes.empty());
            if (cconf.keep_cubes && stats.num_cubes > cconf.max_cubes) return done(l_Undef);
            continue;
        }
        refine();
    }
    return done(l_Undef);
}

// Clauses that share no y, directly or through a function, are
// covered apart: together they need the product of their models
void Cover::split_into_components() {
    assert(components.empty() && x_cls.empty());
    const uint32_t num_vars = problem.size();
    const auto [state, defined, unconstrained] = CoverComponent::classify_defined(problem, cnf.get_clauses());
    on_x_side.assign(num_vars, 0);
    for (uint32_t v = 0; v < num_vars; v++) if (problem.is_x[v] || state[v] == CoverComponent::VarKind::fun_of_x) on_x_side[v] = 1;

    UnionFind uf(num_vars);
    auto first_y = [&](const vector<Lit>& cl) {
        for (const auto& l : cl) if (!on_x_side[l.var()]) return l.var();
        return CoverComponent::none;
    };
    for (const auto& cl : cnf.get_clauses()) {
        const uint32_t first = first_y(cl);
        for (const auto& l : cl) if (!on_x_side[l.var()]) uf.join(l.var(), first);
    }
    for (const auto& v : defined) if (state[v] == CoverComponent::VarKind::y) {
        set<uint32_t> deps;
        AIG::get_dependent_vars(problem.def[v], deps, v);
        for (const auto& d : deps) if (!on_x_side[d]) uf.join(d, v);
    }
    vector<uint32_t> comp_of(num_vars, CoverComponent::none);
    for (const auto& cl : cnf.get_clauses()) {
        const uint32_t first = first_y(cl);
        if (first == CoverComponent::none) { x_cls.push_back(cl); continue; }
        uint32_t& c = comp_of[uf.find(first)];
        if (c == CoverComponent::none) {
            c = components.size();
            components.emplace_back();
        }
        components[c].push_back(cl);
    }
    assert(std::accumulate(components.begin(), components.end(), x_cls.size(),
        [](const size_t s, const auto& comp) { return s + comp.size(); }) == cnf.get_clauses().size());
    // x_cls are over the x side only, and no y is in two components
    SLOW_DEBUG_DO({
        for (const auto& cl : x_cls) for (const auto& l : cl) assert(on_x_side[l.var()]);
        vector<uint32_t> comp_of_y(num_vars, CoverComponent::none);
        for (uint32_t c = 0; c < components.size(); c++) for (const auto& cl : components[c]) for (const auto& l : cl) {
            if (on_x_side[l.var()]) continue;
            assert(comp_of_y[l.var()] == CoverComponent::none || comp_of_y[l.var()] == c);
            comp_of_y[l.var()] = c;
        }
    });
}

// Covers one component with what is left of the ticks, at most max_comp_ticks if set
CoverComponent::Result Cover::cover_one(const Cls& comp_cls, const uint32_t verb, const uint64_t max_comp_ticks) {
    if (cconf.max_ticks) assert(used_ticks < cconf.max_ticks);
    uint64_t ticks = cconf.max_ticks ? cconf.max_ticks - used_ticks : 0;
    if (max_comp_ticks) ticks = std::min(ticks, max_comp_ticks);
    CoverComponent comp(problem, cnf.get_aig_mng(), comp_cls, cconf, ticks, verb);
    auto r = comp.cegar_run();
    used_ticks += comp.ticks();
    return r;
}

// Covers the components one by one, smallest first, until an X has no Y.
// One that gives up does not stop the rest: removable[i] says which every X has a Y of
lbool Cover::cover_components(vector<lbool>& cex, vector<char>& removable) {
    assert(components.size() > 1);
    assert(cex.empty() && removable.empty() && found_funs.empty());
    const uint32_t verb = conf.verb;
    std::stable_sort(components.begin(), components.end(), [](const auto& a, const auto& b) { return a.size() < b.size(); });
    components.back().insert(components.back().end(), x_cls.begin(), x_cls.end());
    if (verb) std::cout << "c o [cover] components: " << components.size() << " clauses of the largest: "
        << components.back().size() << " of " << cnf.get_clauses().size() << std::endl;
    removable.assign(components.size(), 0);
    found_funs.resize(components.size());
    lbool ret = l_True;
    for (uint32_t i = 0; i < components.size(); i++) {
        if (cconf.max_ticks && used_ticks >= cconf.max_ticks) return l_Undef;
        const bool last = i + 1 == components.size();
        // one hopeless component does not use it all up, the last gets the rest
        const uint64_t max_comp_ticks = last || !cconf.max_ticks ? 0 : cconf.max_ticks / 4 + 1;
        auto r = cover_one(components[i], last ? verb : (verb ? verb - 1 : 0), max_comp_ticks);
        if (verb && !last && r.ret != l_True) std::cout << "c o [cover] component " << i << " with "
            << components[i].size() << " clauses: " << (r.ret == l_False ? "X with no Y" : "gave up") << std::endl;
        if (r.ret == l_False) {
            cex = std::move(r.cex);
            return l_False;
        }
        if (r.ret == l_Undef) ret = l_Undef;
        removable[i] = r.every_x_has_y;
        found_funs[i] = std::move(r.funs);
    }
    return ret;
}

// The Skolem functions found go to cnf as defs, in the original numbering:
// those of the components in only, or all, and then the vars left undefined are free and get one
void Cover::set_funs(const vector<char>& only) {
    assert(cconf.need_funs && trans);
    assert(only.empty() || only.size() == found_funs.size());
    // A defined leaf becomes its def: the orig def may name a y that this
    // def does not, the translation having folded it away, and a y whose
    // function names the leaf would close a cycle
    Subst over_x(problem);
    for (uint32_t v = 0; v < problem.size(); v++) if (!problem.defined(v)) over_x.leaf[v] = AIG::new_lit(v);
    vector<uint32_t> vars;
    vector<aig_lit> funs;
    for (uint32_t i = 0; i < found_funs.size(); i++) if (only.empty() || only[i])
        for (const auto& [v, f] : found_funs[i]) {
            vars.push_back(v);
            funs.push_back(over_x.of_aig(f).a);
        }
    trans->funs_to_orig(funs);
    for (uint32_t i = 0; i < funs.size(); i++) {
        const Lit o = trans->orig_of(vars[i]);
        cnf.set_def(o.var(), o.sign() ? ~funs[i] : funs[i]);
    }
    if (!only.empty()) return;
    const auto& sampl = cnf.get_orig_sampl_vars();
    for (uint32_t v = 0; v < cnf.num_defs(); v++)
        if (!sampl.count(v) && !cnf.defined(v)) cnf.set_def(v, cnf.get_aig_mng().new_const(false));
}

// The CNF is psi (clauses over X only) and components C_i over disjoint
// existentials Y_i. The count is of psi ∧ ∃Y_1 C_1 ∧ ... ∧ ∃Y_n C_n, so
// each component, checked against the part of psi its X reach, ends up:
// - removed: every X satisfying psi has a Y_i, so ∃Y_i C_i is true
// - replaced (keep_cubes): the minimized X-cubes with no Y_i, as clauses,
//   which together are exactly ∃Y_i C_i. Not if there are over max_cubes of
//   them, nor if C_i has a defined var and they do not make it much smaller
// - kept: it has a weighted Y (its weight would be lost), or the ticks ran out
// Each component gets at most a quarter of max_ticks.
int64_t Cover::drop_covered() {
    assert(!trans);
    assert(components.empty() && used_ticks == 0);
    const double start = cpuTime();
    const uint32_t num_vars = problem.size();

    // UNSAT CNF, return
    if (std::any_of(cnf.get_clauses().begin(), cnf.get_clauses().end(), [](const auto& cl) { return cl.empty(); }))
        return 0;

    split_into_components();
    std::stable_sort(components.begin(), components.end(), [](const auto& a, const auto& b) { return a.size() < b.size(); });

    vector<char> weighted_y(num_vars, 0);
    if (cnf.get_weighted()) for (uint32_t v = 0; v < num_vars; v++)
        if (!problem.is_x[v] && cnf.weight_set(v)) weighted_y[v] = 1;
    // A defined var is a good one for the counter to branch on, and its
    // defining clauses propagate better than cubes: a component with one is
    // replaced only if its clauses mostly go away. Also when the var is taken
    // as a universal, being weighted
    vector<char> is_def(num_vars, 0);
    for (const auto& v : cnf.get_opt_sampl_vars()) is_def[v] = 1;
    for (const auto& v : cnf.get_sampl_vars()) is_def[v] = 0;
    const auto has_var = [](const Cls& cls, const vector<char>& flag) {
        return std::any_of(cls.begin(), cls.end(), [&](const auto& cl) {
            return std::any_of(cl.begin(), cl.end(), [&](const Lit l) { return flag[l.var()]; }); }); };

    PsiReach psi(x_cls, num_vars);
    DropStats drop_stats;
    vector<char> gone(num_vars, 0);
    Cls cubes;
    for (auto& comp_cls : components) {
        const bool has_weight = has_var(comp_cls, weighted_y);
        const bool has_def = cconf.keep_cubes && has_var(comp_cls, is_def);
        drop_stats.weighted += has_weight;
        Covered covered;
        if (has_weight) {
          // its Y weights are part of the count, so it must stay: ret stays l_Undef, which keeps it
        } else if (cconf.max_ticks && used_ticks >= cconf.max_ticks) drop_stats.out_of_budget++;
        else covered = cover_for_drop(comp_cls, has_def, psi, drop_stats);

        // keep the component, drop it (every X has a Y), or replace it by the cubes ruling out the Xs that have none
        const Action action = choose_action(covered, has_def, comp_cls.size());
        if (action == Action::keep_def) drop_stats.kept_def++;
        if (action == Action::keep || action == Action::keep_def) continue;
        if (action == Action::drop) drop_stats.dropped++;
        else drop_stats.replaced++;

        // drop and replace both: its cubes (none on drop) are added and its Ys marked gone, rewrite_cnf_with_cubes() removes their clauses
        drop_stats.cube_cls += covered.cubes.size();
        for (const auto& cl : covered.cubes) drop_stats.cube_lits += cl.size();
        for (auto& cl : covered.cubes) cubes.push_back(std::move(cl));
        for (const auto& cl : comp_cls) for (const auto& l : cl) if (!problem.is_x[l.var()]) gone[l.var()] = 1;
    }

    const int64_t removed = rewrite_cnf_with_cubes(gone, std::move(cubes));
    if (conf.verb) drop_stats.print(components.size(), removed, std::count(gone.begin(), gone.end(), 1), used_ticks, start);
    return removed;
}

// Covers the component with the part of psi it reaches. With a defined var
// and few clauses, cubes would not replace it: then it can only be dropped
Cover::Covered Cover::cover_for_drop(Cls& comp_cls, const bool has_def, PsiReach& psi, DropStats& drop_stats) {
    assert(cconf.assume_outer);
    if (cconf.max_ticks) assert(used_ticks < cconf.max_ticks);
    drop_stats.tried++;
    const size_t num_comp_cls = comp_cls.size();
    psi.add_reached(problem.is_x, comp_cls);
    auto drop_conf = cconf;
    drop_conf.stop_at_cex = true;
    drop_conf.keep_cubes = false;
    const bool only_drop = has_def && num_comp_cls < cconf.def_replace_min_cls;
    // a quarter of it at most, one hopeless component does not use it all up
    const uint64_t ticks = cconf.max_ticks ? std::min(cconf.max_ticks - used_ticks, cconf.max_ticks / 4 + 1) : 0;
    CoverComponent comp(problem, cnf.get_aig_mng(), comp_cls, only_drop ? drop_conf : cconf,
        ticks, conf.verb >= 2 ? conf.verb - 1 : 0);
    const double comp_start = cpuTime();
    Covered covered;
    covered.ret = comp.cegar_run().ret;
    drop_stats.max_comp_t = std::max(drop_stats.max_comp_t, cpuTime() - comp_start);
    const uint64_t comp_ticks = comp.ticks();
    used_ticks += comp_ticks;
    drop_stats.confl += comp.conflicts();
    assert(comp_cls.size() >= num_comp_cls);
    // an X with no Y only ends the run when its cube is not kept
    if (cconf.keep_cubes && !only_drop) assert(covered.ret != l_False);
    comp_cls.resize(num_comp_cls);
    drop_stats.no_y += covered.ret == l_False;
    if (covered.ret == l_Undef) {
        drop_stats.gave_up++;
        drop_stats.up_ticks_used += comp_ticks;
        if (comp.out_of_ticks()) drop_stats.up_ticks++;
        else if (comp.kept_cubes.size() > cconf.max_cubes) drop_stats.up_cubes++;
    } else {
        drop_stats.done_ticks += comp_ticks;
        drop_stats.max_done_ticks = std::max(drop_stats.max_done_ticks, comp_ticks);
    }
    covered.cubes = std::move(comp.kept_cubes);
    return covered;
}

// Whether a covered component goes, is replaced by its cubes, or stays
Cover::Action Cover::choose_action(const Covered& covered, const bool has_def, const size_t num_cls) const {
    assert(covered.cubes.empty() || cconf.keep_cubes);
    if (covered.ret != l_True) return Action::keep;
    // an empty cube: no X has a Y, let the rest of Arjun find that out
    if (std::any_of(covered.cubes.begin(), covered.cubes.end(), [](const auto& cl) { return cl.empty(); })) return Action::keep;
    if (has_def && covered.cubes.size() * cconf.def_replace_ratio > num_cls) return Action::keep_def;
    return covered.cubes.empty() ? Action::drop : Action::replace;
}

// The ys of different components are disjoint: a clause goes iff it has a
// gone y. The rest keep their order, which the counter is sensitive to
int64_t Cover::rewrite_cnf_with_cubes(const vector<char>& gone, Cls&& cubes) {
    assert(gone.size() == problem.size());
    for (const auto& v : cnf.get_sampl_vars()) assert(!gone[v]);
    if (cubes.empty() && std::none_of(gone.begin(), gone.end(), [](const char g) { return g; })) return 0;
    const auto has_gone = [&](const vector<Lit>& cl) {
        return std::any_of(cl.begin(), cl.end(), [&](const Lit l) { return gone[l.var()]; }); };
    Cls kept;
    for (const auto& cl : cnf.get_clauses()) if (!has_gone(cl)) kept.push_back(cl);
    for (auto& cl : cubes) kept.push_back(std::move(cl));
    const int64_t removed = (int64_t)cnf.get_clauses().size() - (int64_t)kept.size();
    SLOW_DEBUG_DO(for (const auto& cl : kept) for (const auto& l : cl) assert(!gone[l.var()]));
    Cls red;
    for (const auto& cl : cnf.get_red_clauses()) if (!has_gone(cl)) red.push_back(cl);
    vector<uint32_t> opt_sampl;
    for (const auto& v : cnf.get_opt_sampl_vars()) if (!gone[v]) opt_sampl.push_back(v);
    cnf.set_all_clauses(std::move(kept), std::move(red));
    cnf.set_opt_sampl_vars(opt_sampl);
    return removed;
}

// Groups psi's clauses by the X they share
Cover::PsiReach::PsiReach(const Cls& _psi, const uint32_t num_vars) :
        psi(_psi), uf(num_vars), psi_of(num_vars), root_seen(num_vars, 0) {
    for (const auto& cl : psi) assert(!cl.empty());
    for (const auto& cl : psi) for (const auto& l : cl) uf.join(l.var(), cl[0].var());
    for (uint32_t i = 0; i < psi.size(); i++) psi_of[uf.find(psi[i][0].var())].push_back(i);
}

// Appends to comp_cls the clauses of psi that its X reach
void Cover::PsiReach::add_reached(const vector<char>& is_x, Cls& comp_cls) {
    assert(roots.empty());
    SLOW_DEBUG_DO(for (const auto& s : root_seen) assert(!s));
    for (const auto& cl : comp_cls) for (const auto& l : cl) {
        if (!is_x[l.var()]) continue;
        const uint32_t r = uf.find(l.var());
        if (!root_seen[r]) { root_seen[r] = 1; roots.push_back(r); }
    }
    for (const auto& r : roots) {
        root_seen[r] = 0;
        for (const auto& i : psi_of[r]) comp_cls.push_back(psi[i]);
    }
    roots.clear();
}

// The [cover-drop] summary line
void Cover::DropStats::print(const size_t num_comps, const int64_t removed, const size_t vars_gone,
        const uint64_t used_ticks, const double start) const {
    std::cout << "c o [cover-drop] components: " << num_comps << " tried: " << tried
        << " dropped: " << dropped << " replaced: " << replaced << " by cls: " << cube_cls
        << " avg sz: " << std::setprecision(1) << std::fixed << (cube_cls ? (double)cube_lits / cube_cls : 0)
        << " no-Y: " << no_y << " gave up: " << gave_up << " (ticks: " << up_ticks << " cubes: " << up_cubes
        << ") no budget: " << out_of_budget << " weighted: " << weighted << " kept defined: " << kept_def
        << " cls removed: " << removed << " vars gone: " << vars_gone
        << " Mticks: " << std::setprecision(1) << std::fixed << used_ticks / 1e6
        << " (done: " << done_ticks / 1e6 << " max done: " << max_done_ticks / 1e6
        << " gave up: " << up_ticks_used / 1e6 << ") confl: " << confl
        << " T: " << std::setprecision(2) << cpuTime() - start << " max comp T: " << max_comp_t << std::endl;
}

// Decides ∀X ∃Y of the whole CNF, component by component; sets the defs if asked
lbool Cover::run(vector<lbool>& cex) {
    assert(trans);
    assert(cex.empty());
    split_into_components();
    vector<lbool> cex_internal;
    vector<char> removable;
    lbool ret;
    if (components.size() <= 1) {
        auto r = cover_one(cnf.get_clauses(), conf.verb);
        ret = r.ret;
        cex_internal = std::move(r.cex);
        found_funs.push_back(std::move(r.funs));
    } else ret = cover_components(cex_internal, removable);
    if (ret == l_False) assert(!cex_internal.empty());
    else assert(cex_internal.empty());
    if (ret == l_True && cconf.need_funs) set_funs({});
    if (ret == l_Undef && cconf.need_funs && cconf.partial) keep_covered(removable);
    if (ret == l_False) cex = trans->x_to_orig(cnf, cex_internal);
    return ret;
}

// A component covered with no X-cube blocked and no function of X has a Y
// for every X, so its clauses go, and its functions, whatever the ys of the
// others are, become defs. Any other stays: its clauses may restrict X. The
// rest is left to the passes after. The clauses of X only stay
void Cover::keep_covered(const vector<char>& removable) {
    assert(cconf.need_funs && cconf.partial);
    assert(removable.empty() || removable.size() == components.size());
    if (std::none_of(removable.begin(), removable.end(), [](const char c) { return c; })) return;
    set_funs(removable);
    vector<char> gone(problem.size(), 0);
    for (uint32_t i = 0; i < components.size(); i++) if (removable[i])
        for (const auto& cl : components[i]) for (const auto& l : cl) if (!on_x_side[l.var()]) gone[l.var()] = 1;
    const int64_t removed = rewrite_cnf_with_cubes(gone, {});
    // the ys leave the CNF as BVE's do: the passes after take a defined var in it as one its clauses define
    constexpr uint32_t m = std::numeric_limits<uint32_t>::max();
    vector<uint32_t> map_here_to_there(cnf.nVars(), m);
    uint32_t new_nvars = 0;
    for (uint32_t v = 0; v < cnf.nVars(); v++) if (!gone[v]) map_here_to_there[v] = new_nvars++;
    cnf.renumber_vars(map_here_to_there, new_nvars);
    if (conf.verb) std::cout << "c o [cover] removed " << std::count(removable.begin(), removable.end(), 1)
        << " of " << components.size() << " components, cls removed: " << removed
        << " vars gone: " << std::count(gone.begin(), gone.end(), 1) << std::endl;
}
