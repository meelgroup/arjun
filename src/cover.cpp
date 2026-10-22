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
// short, and lets one imply another (find_subsumed). The fewer U a Y needs,
// the more X it covers: minimize_refinement() and flip() look for such Y.
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

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::vector;
using std::map;
using std::set;

void CoverComponent::classify_defined(const CnfVars& vars, const vector<vector<Lit>>& cls, vector<VarKind>& state,
        vector<uint32_t>& defined, vector<uint32_t>& unconstrained) {
    vector<char> in_cls(vars.size(), 0);
    state.assign(vars.size(), VarKind::unseen);
    for (const auto& cl : cls) for (const auto& l : cl) in_cls[l.var()] = 1;
    std::function<bool(uint32_t)> fun_of_x = [&](const uint32_t v) {
        if (vars.univ[v]) return true;
        if (state[v] != VarKind::unseen) return state[v] == VarKind::fun_of_x;
        if (!vars.defined(v)) {
            state[v] = in_cls[v] ? VarKind::y : VarKind::fun_of_x;
            if (!in_cls[v]) unconstrained.push_back(v);
            return state[v] == VarKind::fun_of_x;
        }
        set<uint32_t> deps;
        AIG::get_dependent_vars(vars.def[v], deps, v);
        bool ret = true;
        for (const auto& d : deps) ret &= fun_of_x(d);
        state[v] = ret ? VarKind::fun_of_x : VarKind::y;
        defined.push_back(v);
        return ret;
    };
    for (const auto& cl : cls) for (const auto& l : cl) fun_of_x(l.var());
}

void CoverComponent::add_vars_and_cls() {
    classify_defined(vars, comp_cls, state, defined, unconstrained);
    // a component of a counted CNF: the universals of the rest are no matter
    vector<char> in_cls(num_vars, !cconf.assume_outer);
    for (const auto& cl : comp_cls) for (const auto& l : cl) in_cls[l.var()] = 1;
    for (uint32_t v = 0; v < num_vars; v++) if (vars.univ[v] && in_cls[v]) x_side.push_back(v);
    num_xs = x_side.size();
    for (const auto& v : defined) if (state[v] == VarKind::fun_of_x) x_side.push_back(v);
    on_x_side.assign(num_vars, 0);
    for (const auto& v : x_side) on_x_side[v] = 1;

    to_y.assign(num_vars, none);
    for (const auto& v : x_side) {
        new_y_var(v);
        x_solver.new_var();
    }
    for (const auto& cl : comp_cls) {
        // only x_solver gets them: y_solver's cubes are then over the X of the y
        // clauses, and do not tie together X the rest of the CNF keeps apart
        if (cconf.assume_outer && std::all_of(cl.begin(), cl.end(), [&](const Lit l) { return on_x_side[l.var()]; }))
            continue;
        vector<Lit> cl2;
        for (const auto& l : cl) {
            if (to_y[l.var()] == none) {
                new_y_var(l.var());
                ys.push_back(l.var());
            }
            cl2.push_back(in_y(l));
        }
        y_solver.add_clause(cl2);
    }
    for (const auto& v : defined) if (to_y[v] == none) new_y_var(v);
    for (const auto& v : unconstrained) {
        new_y_var(v);
        y_solver.add_clause({Lit(to_y[v], true)});
    }
}

// y_solver keeps to the functions, so that its models are ones x_solver can rule out
void CoverComponent::tie_defs() {
    for (uint32_t v = 0; v < num_vars; v++) if (to_y[v] != none) defs_in_y.leaf[v] = AIG::new_lit(to_y[v]);
    for (const auto& v : x_side) {
        defs_in_x.leaf[v] = AIG::new_lit(to_y[v]);
        defs_in_vars.leaf[v] = AIG::new_lit(v);
    }
    for (const auto& v : unconstrained) defs_in_x.leaf[v] = defs_in_vars.leaf[v] = aig_mng.new_const(false);
    auto tie = [&](MetaSolver& s, AIGToCNF<MetaSolver>& enc, const uint32_t v) {
        keep.push_back(defs_in_y.of_aig(vars.def[v]).a);
        const Lit out = enc.encode(keep.back());
        const Lit me = Lit(to_y[v], false);
        s.add_clause({~out, me});
        s.add_clause({out, ~me});
    };
    for (const auto& v : defined) tie(y_solver, enc_y, v);
    for (uint32_t i = num_xs; i < x_side.size(); i++) tie(x_solver, enc_x, x_side[i]);
}

void CoverComponent::add_helpers() {
    helper_base = x_solver.nVars();
    for (const auto& cl : comp_cls) {
        if (std::any_of(cl.begin(), cl.end(), [&](const Lit l) { return vars.defined(l.var()) && !on_x_side[l.var()]; })) {
            y_def_cls.push_back(cl);
            continue;
        }
        vector<Lit> univ, y_part;
        for (const auto& l : cl) {
            if (on_x_side[l.var()]) univ.push_back(l);
            else y_part.push_back(in_y(l));
        }
        if (univ.empty()) continue;
        if (y_part.empty()) {
            for (auto& l : univ) l = in_y(l);
            x_cls_solver.push_back(univ);
            continue;
        }
        std::sort(univ.begin(), univ.end());
        const auto [it, inserted] = helper_of.try_emplace(univ, lit_Undef);
        if (inserted) {
            x_solver.new_var();
            it->second = Lit(x_solver.nVars()-1, false);
            x_part_true.push_back(aig_mng.new_const(false));
            for (const auto& l : univ) {
                x_solver.add_clause({~it->second, ~in_y(l)});
                x_part_true.back() = AIG::new_or(x_part_true.back(), AIG::new_lit(l));
            }
        }
        split_cls.emplace_back(y_part, it->second);
    }
    num_helpers = helper_of.size();
    subsumed_by.resize(num_helpers);
    in_refinement.assign(num_helpers, 0);
}

void CoverComponent::find_subsumed() {
    vector<const vector<Lit>*> x_part_of(num_helpers);
    for (const auto& [univ, h] : helper_of) x_part_of[helper_idx(h)] = &univ;
    map<Lit, vector<uint32_t>> occ;
    for (uint32_t i = 0; i < num_helpers; i++) for (const auto& l : *x_part_of[i]) occ[l].push_back(i);
    int64_t work = cconf.subs_work;
    for (uint32_t a = 0; a < num_helpers && work > 0; a++) {
        const vector<uint32_t>* rarest = nullptr;
        for (const auto& l : *x_part_of[a]) if (!rarest || occ[l].size() < rarest->size()) rarest = &occ[l];
        if (!rarest) continue;
        for (const auto& b : *rarest) {
            if (x_part_of[b]->size() <= x_part_of[a]->size()) continue;
            work -= x_part_of[b]->size();
            if (std::includes(x_part_of[b]->begin(), x_part_of[b]->end(), x_part_of[a]->begin(), x_part_of[a]->end()))
                subsumed_by[b].push_back(a);
        }
    }
}

void CoverComponent::drop_subsumed(vector<Lit>& hs) {
    for (const auto& h : hs) in_refinement[helper_idx(h)] = 1;
    kept_helpers.clear();
    for (const auto& h : hs) {
        const auto& sub = subsumed_by[helper_idx(h)];
        if (std::none_of(sub.begin(), sub.end(), [&](const uint32_t a) { return in_refinement[a]; })) kept_helpers.push_back(h);
    }
    for (const auto& h : hs) in_refinement[helper_idx(h)] = 0;
    stats.subsumed += hs.size() - kept_helpers.size();
    std::swap(hs, kept_helpers);
}

void CoverComponent::add_selectors() {
    sel_base = y_solver.nVars();
    backoff.assign(num_helpers, 0);
    skip_rounds.assign(num_helpers, 0);
    is_false.assign(num_helpers, 0);
    in_core.assign(num_helpers, 0);
    if (!sat_minim) return;
    for (uint32_t i = 0; i < num_helpers; i++) y_solver.new_var();
    for (const auto& [y_part, helper] : split_cls) {
        auto cl = y_part;
        cl.push_back(~selector(helper_idx(helper)));
        y_solver.add_clause(cl);
    }
}

// a model that satisfies many existential parts makes a short refinement
void CoverComponent::set_phases() {
    vector<int> pos_occ(y_solver.nVars(), 0);
    for (const auto& [y_part, helper] : split_cls) for (const auto& l : y_part) pos_occ[l.var()] += l.sign() ? -1 : 1;
    for (const auto& v : ys) if (!vars.defined(v)) y_solver.set_phase(Lit(to_y[v], pos_occ[to_y[v]] <= 0));
}

void CoverComponent::init_flip() {
    can_flip.assign(y_solver.nVars(), 0);
    if (flip_minim) for (const auto& v : ys) if (!vars.defined(v)) can_flip[to_y[v]] = 1;
    for (const auto& cl : y_def_cls) for (const auto& l : cl) can_flip[to_y[l.var()]] = 0;
    for (const auto& v : defined) {
        set<uint32_t> deps;
        AIG::get_dependent_vars(vars.def[v], deps, v);
        for (const auto& d : deps) if (to_y[d] != none) can_flip[to_y[d]] = 0;
    }
    flip_occ.resize(y_solver.nVars() * 2);
    for (const auto& cl : comp_cls) {
        bool has_flip = false, has_outer = false;
        for (const auto& l : cl) {
            has_flip |= can_flip[to_y[l.var()]];
            has_outer |= on_x_side[l.var()];
        }
        if (!has_flip) continue;
        flip_cls.emplace_back();
        for (const auto& l : cl) {
            flip_cls.back().push_back(in_y(l));
            if (can_flip[to_y[l.var()]]) flip_occ[in_y(l).toInt()].push_back(flip_cls.size() - 1);
        }
        flip_mixed.push_back(has_outer);
    }
    for (uint32_t v = 0; v < can_flip.size(); v++) if (can_flip[v]) flip_vars.push_back(v);
    num_true.resize(flip_cls.size());
    num_true_ex.resize(flip_cls.size());
}

bool CoverComponent::flip(vector<lbool>& model) {
    for (uint32_t c = 0; c < flip_cls.size(); c++) {
        num_true[c] = num_true_ex[c] = 0;
        for (const auto& l : flip_cls[c]) if (model[l.var()] == boolToLBool(!l.sign())) {
            num_true[c]++;
            num_true_ex[c] += l.var() >= x_side.size();
        }
    }
    const uint64_t before = stats.flips;
    for (bool changed = true; changed;) {
        changed = false;
        for (const auto& v : flip_vars) {
            const Lit t = Lit(v, model[v] != l_True);
            const auto& loses = flip_occ[t.toInt()];
            const auto& gains = flip_occ[(~t).toInt()];
            if (std::any_of(loses.begin(), loses.end(), [&](const uint32_t c) { return num_true[c] < 2; })) continue;
            int gain = 0;
            for (const auto& c : gains) gain += flip_mixed[c] && num_true_ex[c] == 0;
            for (const auto& c : loses) gain -= flip_mixed[c] && num_true_ex[c] == 1;
            if (gain <= 0) continue;
            model[v] = t.sign() ? l_True : l_False;
            for (const auto& c : loses) { num_true[c]--; num_true_ex[c]--; }
            for (const auto& c : gains) { num_true[c]++; num_true_ex[c]++; }
            stats.flips++;
            changed = true;
        }
    }
    return stats.flips != before;
}

// A model for the X of assumps whose existentials satisfy what those of
// `model` do, and as many more helpers' clauses as the cores allow
vector<lbool> CoverComponent::minimize_refinement(vector<lbool> model) {
    const size_t num_x = assumps.size();
    std::fill(is_false.begin(), is_false.end(), 0);
    for (const auto& h : refinement) is_false[helper_idx(h)] = 1;
    for (uint32_t i = 0; i < num_helpers; i++) if (!is_false[i]) assumps.push_back(selector(i));
    const size_t base = assumps.size();
    vector<uint32_t> cand, cand2;
    for (const auto& h : refinement) {
        if (skip_rounds[helper_idx(h)]) skip_rounds[helper_idx(h)]--;
        else cand.push_back(helper_idx(h));
    }
    // Capped: with every core a single helper, it is a call per helper
    for (uint32_t calls = 0; !cand.empty() && calls < cconf.max_minim_calls && !out_of_ticks(); calls++) {
        assumps.resize(base);
        for (const auto& i : cand) assumps.push_back(selector(i));
        stats.minim_calls++;
        const auto ret = solve(y_solver, &assumps);
        if (ret == l_Undef) break;
        if (ret == l_True) {
            model = y_solver.get_model();
            for (const auto& i : cand) backoff[i] = 0;
            break;
        }
        const auto core = y_solver.get_conflict();
        for (const auto& l : core) if (l.var() >= sel_base) in_core[l.var() - sel_base] = 1;
        cand2.clear();
        for (const auto& i : cand) {
            if (!in_core[i]) { cand2.push_back(i); continue; }
            backoff[i] = std::min(backoff[i] * 2 + 1, cconf.max_minim_wait);
            skip_rounds[i] = backoff[i];
        }
        for (const auto& l : core) if (l.var() >= sel_base) in_core[l.var() - sel_base] = 0;
        assert(cand2.size() < cand.size());
        std::swap(cand, cand2);
    }
    assumps.resize(num_x);
    return model;
}

void CoverComponent::compute_refinement(const vector<lbool>& model) {
    refinement.clear();
    for (const auto& [y_part, helper] : split_cls) {
        const bool sat = std::any_of(y_part.begin(), y_part.end(),
                [&](const Lit l) { return model[l.var()] == boolToLBool(!l.sign()); });
        if (!sat) refinement.push_back(helper);
    }
    std::sort(refinement.begin(), refinement.end());
    refinement.erase(std::unique(refinement.begin(), refinement.end()), refinement.end());
}

// the X that satisfy the y_def_cls, given the ys in s.val
aig_lit CoverComponent::y_def_cls_hold(Subst& s) {
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
void CoverComponent::build_funs(vector<std::pair<uint32_t, aig_lit>>& found_funs) {
    // `before`: an earlier model works. In blocks, a chain would be as deep as the rounds
    const uint32_t num_refs = refinements.size();
    const uint32_t block = std::max<uint32_t>(1, std::sqrt(num_refs));
    vector<aig_lit> first_works;
    aig_lit before_block = aig_mng.new_const(false), in_block = aig_mng.new_const(false);
    for (uint32_t r = 0; r < num_refs; r++) {
        if (r % block == 0) {
            before_block = AIG::new_or(before_block, in_block);
            in_block = aig_mng.new_const(false);
        }
        for (uint32_t i = 0; i < ys.size(); i++) defs_in_vars.val[ys[i]] = boolToLBool(ref_models[r * ys.size() + i]);
        aig_lit works = y_def_cls.empty() ? aig_mng.new_const(true) : y_def_cls_hold(defs_in_vars);
        for (const auto& h : refinements[r]) works = AIG::new_and(works, x_part_true[helper_idx(h)]);
        first_works.push_back(AIG::new_and(works, ~AIG::new_or(before_block, in_block)));
        in_block = AIG::new_or(in_block, works);
    }
    vector<aig_lit> ors;
    for (uint32_t i = 0; i < ys.size(); i++) {
        if (vars.defined(ys[i])) continue;
        uint32_t num_ones = 0;
        for (uint32_t r = 0; r < num_refs; r++) num_ones += ref_models[r * ys.size() + i];
        const bool val = num_ones * 2 <= num_refs;
        ors.clear();
        for (uint32_t r = 0; r < num_refs; r++) if (ref_models[r * ys.size() + i] == val) ors.push_back(first_works[r]);
        for (uint32_t step = 1; step < ors.size(); step *= 2)
            for (uint32_t j = 0; j + step < ors.size(); j += 2 * step) ors[j] = AIG::new_or(ors[j], ors[j + step]);
        const aig_lit fun = ors.empty() ? aig_mng.new_const(false) : ors[0];
        found_funs.emplace_back(ys[i], val ? fun : ~fun);
    }
}

void CoverComponent::print_stats(const char* what) {
    if (!verb) return;
    const uint64_t refs = stats.rounds - stats.num_cubes;
    std::cout << "c o [cover] " << what << " rounds: " << stats.rounds << " no-Y cubes: " << stats.num_cubes
        << " outer defs: " << x_side.size() - num_xs << " deep cls: " << y_def_cls.size()
        << " outer cls: " << x_cls_solver.size()
        << " helpers: " << num_helpers << std::fixed
        << " avg refinement: " << std::setprecision(1) << (refs ? (double)stats.ref_lits / refs : 0)
        << " avg cube: " << (stats.num_cubes ? (double)stats.cube_lits / stats.num_cubes : 0)
        << " minim calls: " << stats.minim_calls << " removed: " << stats.minim_removed
        << " flips: " << stats.flips << " subsumed: " << stats.subsumed
        << " cost: " << std::setprecision(2) << budget_used << " of " << cconf.budget
        << " ticks(M) abs: " << x_solver.get_sum_ticks() / 1e6 << " f: " << y_solver.get_sum_ticks() / 1e6
        << " deep: " << defs_in_x.work * 10 / 1e6
        << " confl abs: " << x_solver.get_sum_conflicts() << " f: " << y_solver.get_sum_conflicts()
        << " T: " << (cpuTime() - stats.start_time) << " (setup: " << stats.setup_time << " abs: " << stats.x_time
        << " f: " << stats.y_time << " refine: " << stats.refine_time << " deep: " << stats.y_def_time
        << " funs: " << stats.funs_time << ")" << std::endl;
}

// A call that would go over max_ticks stops and gives up the component
lbool CoverComponent::solve(MetaSolver& s, vector<Lit>* as) {
    if (max_ticks) {
        const uint64_t used = ticks();
        if (used >= max_ticks) gave_up = true;
        if (gave_up) return l_Undef;
        s.set_max_ticks(max_ticks - used);
    }
    const auto ret = as ? s.solve(as) : s.solve();
    if (ret == l_Undef) gave_up = true;
    return ret;
}

lbool CoverComponent::finish(const lbool ret) {
    print_stats(ret == l_True ? "all X covered" : ret == l_False ? "X with no Y" : "gave up");
    return ret;
}

void CoverComponent::cex_from_x_solver(vector<lbool>& cex) {
    cex.assign(num_vars, l_Undef);
    for (uint32_t i = 0; i < num_xs; i++) cex[x_side[i]] = x_solver.get_model()[to_y[x_side[i]]];
}

// A clause of x side vars only: an X that falsifies it has no Y. As a
// helper it would be in every refinement
bool CoverComponent::x_cls_cex(vector<lbool>& cex) {
    if (x_cls_solver.empty()) return false;
    x_solver.new_var();
    vector<Lit> some = {Lit(x_solver.nVars()-1, true)};
    for (const auto& cl : x_cls_solver) {
        x_solver.new_var();
        some.emplace_back(x_solver.nVars()-1, false);
        for (const auto& l : cl) x_solver.add_clause({~some.back(), ~l});
    }
    x_solver.add_clause(some);
    assumps = {~some[0]};
    const auto ret = timed(stats.x_time, [&] { return solve(x_solver, &assumps); });
    if (ret == l_True) {
        cex_from_x_solver(cex);
        return true;
    }
    if (ret == l_Undef) return false;
    x_solver.add_clause({some[0]});
    return false;
}

// no X in the cube of y_solver's conflict has a Y, so any function will do there
void CoverComponent::block_no_y_cube() {
    auto cube = y_solver.get_conflict();
    // A kept cube becomes a clause of the counted CNF: the shorter, the more it propagates
    if (cconf.keep_cubes && cconf.minim_cubes) {
        vector<Lit> cand = cube, as;
        for (const auto& l : cand) {
            if (out_of_ticks()) break;
            if (std::find(cube.begin(), cube.end(), l) == cube.end()) continue;
            as.clear();
            for (const auto& l2 : cube) if (l2 != l) as.push_back(~l2);
            if (timed(stats.y_time, [&] { return solve(y_solver, &as); }) == l_False) cube = y_solver.get_conflict();
        }
    }
    stats.cube_lits += cube.size();
    budget_used += sq_frac(cube.size(), num_xs);
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

void CoverComponent::x_solver_gets_cls() {
    vector<uint32_t> to_x(num_vars, none);
    for (const auto& v : x_side) to_x[v] = to_y[v];
    for (const auto& v : ys) {
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
    compute_refinement(model);
    if (flip_minim && refinement.size() > 1 && flip(model)) compute_refinement(model);
    if (sat_minim && refinement.size() > 1) {
        const size_t before = refinement.size();
        model = minimize_refinement(model);
        compute_refinement(model);
        assert(refinement.size() <= before);
        stats.minim_removed += before - refinement.size();
    }
    budget_used += sq_frac(refinement.size(), num_helpers);
    if (subs_minim) drop_subsumed(refinement);
    stats.ref_lits += refinement.size();
    if (cconf.need_funs) {
        refinements.push_back(refinement);
        for (const auto& v : ys) ref_models.push_back(model[to_y[v]] == l_True);
    }
    stats.refine_time += cpuTime() - refine_start;
    if (!y_def_cls.empty()) {
        const double y_def_start = cpuTime();
        for (const auto& v : ys) defs_in_x.val[v] = model[to_y[v]];
        keep.push_back(y_def_cls_hold(defs_in_x));
        if (keep.back()->type != AIGT::t_const) refinement.push_back(~enc_x.encode(keep.back()));
        else assert(!keep.back().neg);
        stats.y_def_time += cpuTime() - y_def_start;
    }
    x_solver.add_clause(refinement);
}

lbool CoverComponent::run(vector<lbool>& cex, vector<std::pair<uint32_t, aig_lit>>& found_funs) {
    stats.start_time = cpuTime();
    x_solver.set_no_lucky();
    y_solver.set_no_lucky();
    y_solver.set_decide(false);
    add_vars_and_cls();
    tie_defs();
    add_helpers();
    if (subs_minim) find_subsumed();
    add_selectors();
    set_phases();
    init_flip();
    stats.setup_time = cpuTime() - stats.start_time;

    if (cconf.stop_at_cex && !cconf.assume_outer && x_cls_cex(cex)) return finish(l_False);
    for (const auto& cl : x_cls_solver) x_solver.add_clause(cl);
    for (; budget_used < cconf.budget && !out_of_ticks(); stats.rounds++) {
        if (stats.rounds && stats.rounds % cconf.stats_every == 0) print_stats("progress");
        const auto x_ret = timed(stats.x_time, [&] { return solve(x_solver); });
        if (x_ret == l_Undef) break;
        if (x_ret == l_False) {
            if (cconf.need_funs) timed(stats.funs_time, [&] { build_funs(found_funs); return 0; });
            return finish(l_True);
        }
        assumps.clear();
        for (uint32_t i = 0; i < num_xs; i++) assumps.emplace_back(to_y[x_side[i]], x_solver.get_model()[to_y[x_side[i]]] != l_True);
        const auto y_ret = timed(stats.y_time, [&] { return solve(y_solver, &assumps); });
        if (y_ret == l_Undef) break;
        if (y_ret == l_False) {
            if (cconf.stop_at_cex) {
                cex_from_x_solver(cex);
                return finish(l_False);
            }
            block_no_y_cube();
            if (cconf.keep_cubes && stats.num_cubes > cconf.max_cubes) return finish(l_Undef);
            continue;
        }
        refine();
    }
    return finish(l_Undef);
}

// Clauses that share no y, directly or through a function, are
// covered apart: together they need the product of their models
void Cover::split_by_ys() {
    const uint32_t num_vars = vars.size();
    vector<CoverComponent::VarKind> state;
    vector<uint32_t> defined, unconstrained;
    CoverComponent::classify_defined(vars, cnf.get_clauses(), state, defined, unconstrained);
    vector<char> on_x_side(num_vars, 0);
    for (uint32_t v = 0; v < num_vars; v++) if (vars.univ[v] || state[v] == CoverComponent::VarKind::fun_of_x) on_x_side[v] = 1;

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
        AIG::get_dependent_vars(vars.def[v], deps, v);
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
}

lbool Cover::cover_one(const vector<vector<Lit>>& comp_cls, const uint32_t verb, vector<lbool>& cex) {
    CoverComponent comp(vars, cnf.get_aig_mng(), comp_cls, cconf, cconf.max_ticks ? cconf.max_ticks - used_ticks : 0, verb);
    const lbool ret = comp.run(cex, found_funs);
    used_ticks += comp.ticks();
    return ret;
}

lbool Cover::cover_components(vector<lbool>& cex) {
    const uint32_t verb = conf.verb;
    std::stable_sort(components.begin(), components.end(), [](const auto& a, const auto& b) { return a.size() < b.size(); });
    components.back().insert(components.back().end(), x_cls.begin(), x_cls.end());
    if (verb) std::cout << "c o [cover] components: " << components.size() << " clauses of the largest: "
        << components.back().size() << " of " << cnf.get_clauses().size() << std::endl;
    lbool ret = l_True;
    for (uint32_t i = 0; i < components.size() && ret == l_True; i++) {
        if (cconf.max_ticks && used_ticks >= cconf.max_ticks) return l_Undef;
        const bool last = i + 1 == components.size();
        ret = cover_one(components[i], last ? verb : (verb ? verb - 1 : 0), cex);
        if (verb && !last && ret != l_True) std::cout << "c o [cover] component " << i << " with "
            << components[i].size() << " clauses: " << (ret == l_False ? "X with no Y" : "gave up") << std::endl;
    }
    return ret;
}

void Cover::set_funs() {
    vector<aig_lit> funs;
    for (const auto& d : found_funs) funs.push_back(d.second);
    vars.to_orig(funs);
    for (uint32_t i = 0; i < funs.size(); i++) {
        const Lit o = vars.orig[found_funs[i].first];
        cnf.set_def(o.var(), o.sign() ? ~funs[i] : funs[i]);
    }
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
    const double start = cpuTime();
    const uint32_t num_vars = vars.size();
    if (std::any_of(cnf.get_clauses().begin(), cnf.get_clauses().end(), [](const auto& cl) { return cl.empty(); }))
        return 0;
    split_by_ys();
    std::stable_sort(components.begin(), components.end(), [](const auto& a, const auto& b) { return a.size() < b.size(); });

    vector<char> fixed_weight(num_vars, 0);
    if (cnf.get_weighted()) for (uint32_t v = 0; v < num_vars; v++)
        if (!vars.univ[v] && cnf.weight_set(v)) fixed_weight[v] = 1;

    // A component only needs the part of psi that its X reach: the rest is
    // satisfiable apart from it, or nothing is counted anyway
    UnionFind uf(num_vars);
    for (const auto& cl : x_cls) for (const auto& l : cl) uf.join(l.var(), cl[0].var());
    vector<vector<uint32_t>> psi_of(num_vars);
    for (uint32_t i = 0; i < x_cls.size(); i++) psi_of[uf.find(x_cls[i][0].var())].push_back(i);
    vector<char> root_seen(num_vars, 0);
    vector<uint32_t> roots;

    vector<char> gone(num_vars, 0);
    vector<vector<Lit>> kept = x_cls;
    vector<lbool> cex;
    vector<std::pair<uint32_t, aig_lit>> no_defs;
    struct {
        uint32_t tried = 0, dropped = 0, replaced = 0, no_y = 0, gave_up = 0, weighted = 0, kept_def = 0;
        uint64_t cube_cls = 0, cube_lits = 0;
        uint32_t up_ticks = 0, up_cubes = 0, no_budget = 0;
        uint64_t done_ticks = 0, max_done_ticks = 0, up_ticks_used = 0, confl = 0;
        double max_comp_t = 0;
    } ds;
    // A defined var is a good one for the counter to branch on, and its
    // defining clauses propagate better than cubes: a component with one is
    // replaced only if its clauses mostly go away. Also when the var is taken
    // as a universal, being weighted
    vector<char> is_def(num_vars, 0);
    for (const auto& v : cnf.get_opt_sampl_vars()) is_def[v] = 1;
    for (const auto& v : cnf.get_sampl_vars()) is_def[v] = 0;
    auto drop_conf = cconf;
    drop_conf.stop_at_cex = true;
    drop_conf.keep_cubes = false;
    for (auto& comp_cls : components) {
        lbool ret = l_Undef;
        const auto any_var = [&](const vector<char>& flag) {
            return std::any_of(comp_cls.begin(), comp_cls.end(), [&](const auto& cl) {
                return std::any_of(cl.begin(), cl.end(), [&](const Lit l) { return flag[l.var()]; }); }); };
        const bool has_weight = any_var(fixed_weight);
        const bool has_def = cconf.keep_cubes && any_var(is_def);
        const bool only_drop = has_def && comp_cls.size() < cconf.def_replace_min_cls;
        ds.weighted += has_weight;
        std::unique_ptr<CoverComponent> comp;
        if (!has_weight && (!cconf.max_ticks || used_ticks < cconf.max_ticks)) {
            ds.tried++;
            const size_t sz = comp_cls.size();
            for (const auto& cl : comp_cls) for (const auto& l : cl) {
                if (!vars.univ[l.var()]) continue;
                const uint32_t r = uf.find(l.var());
                if (!root_seen[r]) { root_seen[r] = 1; roots.push_back(r); }
            }
            for (const auto& r : roots) {
                root_seen[r] = 0;
                for (const auto& i : psi_of[r]) comp_cls.push_back(x_cls[i]);
            }
            roots.clear();
            // a quarter of it at most, one hopeless component does not use it all up
            const uint64_t ticks = cconf.max_ticks ? std::min(cconf.max_ticks - used_ticks, cconf.max_ticks / 4 + 1) : 0;
            comp = std::make_unique<CoverComponent>(vars, cnf.get_aig_mng(), comp_cls, only_drop ? drop_conf : cconf,
                ticks, conf.verb >= 2 ? conf.verb - 1 : 0);
            const double comp_start = cpuTime();
            ret = comp->run(cex, no_defs);
            ds.max_comp_t = std::max(ds.max_comp_t, cpuTime() - comp_start);
            const uint64_t t = comp->ticks();
            used_ticks += t;
            ds.confl += comp->conflicts();
            comp_cls.resize(sz);
            ds.no_y += ret == l_False;
            if (ret == l_Undef) {
                ds.gave_up++;
                ds.up_ticks_used += t;
                if (comp->out_of_ticks()) ds.up_ticks++;
                else if (comp->kept_cubes.size() > cconf.max_cubes) ds.up_cubes++;
            } else {
                ds.done_ticks += t;
                ds.max_done_ticks = std::max(ds.max_done_ticks, t);
            }
        } else if (!has_weight) ds.no_budget++;
        // an empty cube: no X has a Y, let the rest of Arjun find that out
        if (ret == l_True && std::any_of(comp->kept_cubes.begin(), comp->kept_cubes.end(),
                [](const auto& cl) { return cl.empty(); })) ret = l_Undef;
        if (ret == l_True && has_def && comp->kept_cubes.size() * cconf.def_replace_ratio > comp_cls.size()) {
            ret = l_Undef;
            ds.kept_def++;
        }
        if (ret != l_True) {
            for (auto& cl : comp_cls) kept.push_back(std::move(cl));
            continue;
        }
        if (comp->kept_cubes.empty()) ds.dropped++;
        else ds.replaced++;
        ds.cube_cls += comp->kept_cubes.size();
        for (const auto& cl : comp->kept_cubes) ds.cube_lits += cl.size();
        for (auto& cl : comp->kept_cubes) kept.push_back(std::move(cl));
        for (const auto& cl : comp_cls) for (const auto& l : cl) if (!vars.univ[l.var()]) gone[l.var()] = 1;
    }

    const int64_t removed = (int64_t)cnf.get_clauses().size() - (int64_t)kept.size();
    vector<vector<Lit>> red;
    for (const auto& cl : cnf.get_red_clauses())
        if (std::none_of(cl.begin(), cl.end(), [&](const Lit l) { return gone[l.var()]; })) red.push_back(cl);
    vector<uint32_t> opt_sampl;
    for (const auto& v : cnf.get_opt_sampl_vars()) if (!gone[v]) opt_sampl.push_back(v);
    cnf.set_all_clauses(std::move(kept), std::move(red));
    cnf.set_opt_sampl_vars(opt_sampl);

    if (conf.verb) std::cout << "c o [cover-drop] components: " << components.size() << " tried: " << ds.tried
        << " dropped: " << ds.dropped << " replaced: " << ds.replaced << " by cls: " << ds.cube_cls
        << " avg sz: " << std::setprecision(1) << std::fixed << (ds.cube_cls ? (double)ds.cube_lits / ds.cube_cls : 0)
        << " no-Y: " << ds.no_y << " gave up: " << ds.gave_up << " (ticks: " << ds.up_ticks << " cubes: " << ds.up_cubes
        << ") no budget: " << ds.no_budget << " weighted: " << ds.weighted << " kept defined: " << ds.kept_def
        << " cls removed: " << removed << " vars gone: " << std::count(gone.begin(), gone.end(), 1)
        << " Mticks: " << std::setprecision(1) << std::fixed << used_ticks / 1e6
        << " (done: " << ds.done_ticks / 1e6 << " max done: " << ds.max_done_ticks / 1e6
        << " gave up: " << ds.up_ticks_used / 1e6 << ") confl: " << ds.confl
        << " T: " << std::setprecision(2) << cpuTime() - start << " max comp T: " << ds.max_comp_t << std::endl;
    return removed;
}

lbool Cover::run(vector<lbool>& cex) {
    split_by_ys();
    vector<lbool> vars_cex;
    const lbool ret = components.size() <= 1 ? cover_one(cnf.get_clauses(), conf.verb, vars_cex) : cover_components(vars_cex);
    if (ret == l_True && cconf.need_funs) set_funs();
    if (ret == l_False) cex = vars.univ_to_orig(cnf, vars_cex);
    return ret;
}
