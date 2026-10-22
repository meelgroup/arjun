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
// f holds φ and, for an X given as assumptions, finds a Y or proves there is
// none. abs is over X only and proposes the next X that no Y found so far
// covers. Split each clause into its X part U and its Y part E: a Y from f
// works for exactly the X that satisfy U of every clause whose E it leaves
// false, so abs gets "one of those U is false". A helper var per distinct U
// (true: all of U is false) keeps these refinements short, and lets one
// imply another (find_subsumed). The fewer U a Y needs, the more X it covers:
// minimize() and flip() look for such Y. abs UNSAT: every X has a Y, and the
// models, first one that works wins, are the Skolem functions. f UNSAT for
// an X: the cube of its failed assumptions has no Y.
//
// This is the abstraction refinement of AReQS [1], generalised to any number
// of quantifier levels by RAReQS [2], with the clauses' universal parts
// selected by variables as in QESTO [3] and CAQE [4]. An earlier comparison
// of 2QBF algorithms, CEGAR among them, is [5].
//
// For counting (Cover::drop_covered), X are the sampling vars and the
// clauses of X only are assumed, not checked. A component whose X all have
// a Y is removed. With keep_cubes, the X-cubes with no Y are kept, minimized,
// as clauses: when abs is UNSAT they are ∃Y of the component, which replaces
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

void CoverComp::classify(const CnfVars& vs, const vector<vector<Lit>>& cls, vector<char>& state,
        vector<uint32_t>& defined, vector<uint32_t>& free_leaves) {
    vector<char> in_cls(vs.size(), 0);
    state.assign(vs.size(), 0);
    for (const auto& cl : cls) for (const auto& l : cl) in_cls[l.var()] = 1;
    std::function<bool(uint32_t)> fun_of_univ = [&](const uint32_t v) {
        if (vs.univ[v]) return true;
        if (state[v]) return state[v] == 1;
        if (!vs.defined(v)) {
            // not in cls: nothing constrains it, false is its function
            state[v] = in_cls[v] ? 2 : 1;
            if (!in_cls[v]) free_leaves.push_back(v);
            return state[v] == 1;
        }
        set<uint32_t> deps;
        AIG::get_dependent_vars(vs.def[v], deps, v);
        bool ret = true;
        for (const auto& d : deps) ret &= fun_of_univ(d);
        state[v] = ret ? 1 : 2;
        defined.push_back(v);
        return ret;
    };
    for (const auto& cl : cls) for (const auto& l : cl) fun_of_univ(l.var());
}

void CoverComp::add_vars_and_cls() {
    classify(vs, cls, state, defined, free_leaves);
    // a component of a counted CNF: the universals of the rest are no matter
    vector<char> in_cls(num_vars, !mconf.assume_outer);
    for (const auto& cl : cls) for (const auto& l : cl) in_cls[l.var()] = 1;
    for (uint32_t v = 0; v < num_vars; v++) if (vs.univ[v] && in_cls[v]) outer.push_back(v);
    num_univ = outer.size();
    for (const auto& v : defined) if (state[v] == 1) outer.push_back(v);
    is_outer.assign(num_vars, 0);
    for (const auto& v : outer) is_outer[v] = 1;

    to_f.assign(num_vars, none);
    for (const auto& v : outer) {
        new_f_var(v);
        abs.new_var();
    }
    for (const auto& cl : cls) {
        // only abs gets them: f's cubes are then over the X of the existential
        // clauses, and do not tie together X the rest of the CNF keeps apart
        if (mconf.assume_outer && std::all_of(cl.begin(), cl.end(), [&](const Lit l) { return is_outer[l.var()]; }))
            continue;
        vector<Lit> cl2;
        for (const auto& l : cl) {
            if (to_f[l.var()] == none) {
                new_f_var(l.var());
                ys.push_back(l.var());
            }
            cl2.push_back(in_f(l));
        }
        f.add_clause(cl2);
    }
    for (const auto& v : defined) if (to_f[v] == none) new_f_var(v);
    for (const auto& v : free_leaves) {
        new_f_var(v);
        f.add_clause({Lit(to_f[v], true)});
    }
}

// f keeps to the functions, so that its models are ones abs can rule out
void CoverComp::tie_defs() {
    for (uint32_t v = 0; v < num_vars; v++) if (to_f[v] != none) in_f_vars.leaf[v] = AIG::new_lit(to_f[v]);
    for (const auto& v : outer) {
        in_abs_vars.leaf[v] = AIG::new_lit(to_f[v]);
        in_vars.leaf[v] = AIG::new_lit(v);
    }
    for (const auto& v : free_leaves) in_abs_vars.leaf[v] = in_vars.leaf[v] = aig_mng.new_const(false);
    auto tie = [&](MetaSolver& s, AIGToCNF<MetaSolver>& enc, const uint32_t v) {
        keep.push_back(in_f_vars.of_aig(vs.def[v]).a);
        const Lit out = enc.encode(keep.back());
        const Lit me = Lit(to_f[v], false);
        s.add_clause({~out, me});
        s.add_clause({out, ~me});
    };
    for (const auto& v : defined) tie(f, enc_f, v);
    for (uint32_t i = num_univ; i < outer.size(); i++) tie(abs, enc_abs, outer[i]);
}

void CoverComp::add_helpers() {
    helper_at = abs.nVars();
    for (const auto& cl : cls) {
        if (std::any_of(cl.begin(), cl.end(), [&](const Lit l) { return vs.defined(l.var()) && !is_outer[l.var()]; })) {
            deep.push_back(cl);
            continue;
        }
        vector<Lit> univ, exist;
        for (const auto& l : cl) {
            if (is_outer[l.var()]) univ.push_back(l);
            else exist.push_back(in_f(l));
        }
        if (univ.empty()) continue;
        if (exist.empty()) {
            for (auto& l : univ) l = in_f(l);
            outer_only.push_back(univ);
            continue;
        }
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
    num_helpers = univ_to_helper.size();
    subs.resize(num_helpers);
    present.assign(num_helpers, 0);
}

void CoverComp::find_subsumed() {
    vector<const vector<Lit>*> univ_of(num_helpers);
    for (const auto& [univ, h] : univ_to_helper) univ_of[hidx(h)] = &univ;
    map<Lit, vector<uint32_t>> occ;
    for (uint32_t i = 0; i < num_helpers; i++) for (const auto& l : *univ_of[i]) occ[l].push_back(i);
    int64_t work = mconf.subs_work;
    for (uint32_t a = 0; a < num_helpers && work > 0; a++) {
        const vector<uint32_t>* rarest = nullptr;
        for (const auto& l : *univ_of[a]) if (!rarest || occ[l].size() < rarest->size()) rarest = &occ[l];
        if (!rarest) continue;
        for (const auto& b : *rarest) {
            if (univ_of[b]->size() <= univ_of[a]->size()) continue;
            work -= univ_of[b]->size();
            if (std::includes(univ_of[b]->begin(), univ_of[b]->end(), univ_of[a]->begin(), univ_of[a]->end()))
                subs[b].push_back(a);
        }
    }
}

void CoverComp::drop_subsumed(vector<Lit>& hs) {
    for (const auto& h : hs) present[hidx(h)] = 1;
    kept.clear();
    for (const auto& h : hs) {
        const auto& sub = subs[hidx(h)];
        if (std::none_of(sub.begin(), sub.end(), [&](const uint32_t a) { return present[a]; })) kept.push_back(h);
    }
    for (const auto& h : hs) present[hidx(h)] = 0;
    subsumed += hs.size() - kept.size();
    std::swap(hs, kept);
}

void CoverComp::add_selectors() {
    sel_at = f.nVars();
    wait.assign(num_helpers, 0);
    skip.assign(num_helpers, 0);
    is_false.assign(num_helpers, 0);
    in_core.assign(num_helpers, 0);
    if (!sat_minim) return;
    for (uint32_t i = 0; i < num_helpers; i++) f.new_var();
    for (const auto& [exist, helper] : mixed) {
        auto cl = exist;
        cl.push_back(~sel(hidx(helper)));
        f.add_clause(cl);
    }
}

// a model that satisfies many existential parts makes a short refinement
void CoverComp::set_phases() {
    vector<int> pos_occ(f.nVars(), 0);
    for (const auto& [exist, helper] : mixed) for (const auto& l : exist) pos_occ[l.var()] += l.sign() ? -1 : 1;
    for (const auto& v : ys) if (!vs.defined(v)) f.set_phase(Lit(to_f[v], pos_occ[to_f[v]] <= 0));
}

void CoverComp::init_flip() {
    can_flip.assign(f.nVars(), 0);
    if (flip_minim) for (const auto& v : ys) if (!vs.defined(v)) can_flip[to_f[v]] = 1;
    for (const auto& cl : deep) for (const auto& l : cl) can_flip[to_f[l.var()]] = 0;
    for (const auto& v : defined) {
        set<uint32_t> deps;
        AIG::get_dependent_vars(vs.def[v], deps, v);
        for (const auto& d : deps) if (to_f[d] != none) can_flip[to_f[d]] = 0;
    }
    flip_occ.resize(f.nVars() * 2);
    for (const auto& cl : cls) {
        bool has_flip = false, has_outer = false;
        for (const auto& l : cl) {
            has_flip |= can_flip[to_f[l.var()]];
            has_outer |= is_outer[l.var()];
        }
        if (!has_flip) continue;
        flip_cls.emplace_back();
        for (const auto& l : cl) {
            flip_cls.back().push_back(in_f(l));
            if (can_flip[to_f[l.var()]]) flip_occ[in_f(l).toInt()].push_back(flip_cls.size() - 1);
        }
        flip_mixed.push_back(has_outer);
    }
    for (uint32_t v = 0; v < can_flip.size(); v++) if (can_flip[v]) flip_vars.push_back(v);
    num_true.resize(flip_cls.size());
    num_true_ex.resize(flip_cls.size());
}

bool CoverComp::flip(vector<lbool>& model) {
    for (uint32_t c = 0; c < flip_cls.size(); c++) {
        num_true[c] = num_true_ex[c] = 0;
        for (const auto& l : flip_cls[c]) if (model[l.var()] == boolToLBool(!l.sign())) {
            num_true[c]++;
            num_true_ex[c] += l.var() >= outer.size();
        }
    }
    const uint64_t before = flips;
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
            flips++;
            changed = true;
        }
    }
    return flips != before;
}

// A model for the X of assumps whose existentials satisfy what those of
// `model` do, and as many more helpers' clauses as the cores allow
vector<lbool> CoverComp::minimize(vector<lbool> model) {
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
    // Capped: with every core a single helper, it is a call per helper
    for (uint32_t calls = 0; !cand.empty() && calls < mconf.max_minim_calls && !out_of_ticks(); calls++) {
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
            wait[i] = std::min(wait[i] * 2 + 1, mconf.max_minim_wait);
            skip[i] = wait[i];
        }
        for (const auto& l : core) if (l.var() >= sel_at) in_core[l.var() - sel_at] = 0;
        assert(cand2.size() < cand.size());
        std::swap(cand, cand2);
    }
    assumps.resize(num_x);
    return model;
}

void CoverComp::get_some_false(const vector<lbool>& model) {
    some_false.clear();
    for (const auto& [exist, helper] : mixed) {
        const bool sat = std::any_of(exist.begin(), exist.end(),
                [&](const Lit l) { return model[l.var()] == boolToLBool(!l.sign()); });
        if (!sat) some_false.push_back(helper);
    }
    std::sort(some_false.begin(), some_false.end());
    some_false.erase(std::unique(some_false.begin(), some_false.end()), some_false.end());
}

// the X that satisfy the deep clauses, given the existentials in s.val
aig_lit CoverComp::deep_true(Subst& s) {
    s.new_round();
    aig_lit ret = aig_mng.new_const(true);
    for (const auto& cl : deep) {
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
void CoverComp::build_funs(vector<std::pair<uint32_t, aig_lit>>& new_defs) {
    // `before`: an earlier model works. In blocks, a chain would be as deep as the rounds
    const uint32_t num_refs = ref_helpers.size();
    const uint32_t block = std::max<uint32_t>(1, std::sqrt(num_refs));
    vector<aig_lit> first;
    aig_lit before_block = aig_mng.new_const(false), in_block = aig_mng.new_const(false);
    for (uint32_t r = 0; r < num_refs; r++) {
        if (r % block == 0) {
            before_block = AIG::new_or(before_block, in_block);
            in_block = aig_mng.new_const(false);
        }
        for (uint32_t i = 0; i < ys.size(); i++) in_vars.val[ys[i]] = boolToLBool(ref_ys[r * ys.size() + i]);
        aig_lit works = deep.empty() ? aig_mng.new_const(true) : deep_true(in_vars);
        for (const auto& h : ref_helpers[r]) works = AIG::new_and(works, univ_true[hidx(h)]);
        first.push_back(AIG::new_and(works, ~AIG::new_or(before_block, in_block)));
        in_block = AIG::new_or(in_block, works);
    }
    vector<aig_lit> ors;
    for (uint32_t i = 0; i < ys.size(); i++) {
        if (vs.defined(ys[i])) continue;
        uint32_t num_ones = 0;
        for (uint32_t r = 0; r < num_refs; r++) num_ones += ref_ys[r * ys.size() + i];
        const bool val = num_ones * 2 <= num_refs;
        ors.clear();
        for (uint32_t r = 0; r < num_refs; r++) if (ref_ys[r * ys.size() + i] == val) ors.push_back(first[r]);
        for (uint32_t step = 1; step < ors.size(); step *= 2)
            for (uint32_t j = 0; j + step < ors.size(); j += 2 * step) ors[j] = AIG::new_or(ors[j], ors[j + step]);
        const aig_lit fun = ors.empty() ? aig_mng.new_const(false) : ors[0];
        new_defs.emplace_back(ys[i], val ? fun : ~fun);
    }
}

void CoverComp::print_stats(const char* what) {
    if (!verb) return;
    const uint64_t refs = rounds - cubes;
    std::cout << "c o [cover] " << what << " rounds: " << rounds << " no-Y cubes: " << cubes
        << " outer defs: " << outer.size() - num_univ << " deep cls: " << deep.size()
        << " outer cls: " << outer_only.size()
        << " helpers: " << num_helpers << std::fixed
        << " avg refinement: " << std::setprecision(1) << (refs ? (double)ref_lits / refs : 0)
        << " avg cube: " << (cubes ? (double)cube_lits / cubes : 0)
        << " minim calls: " << minim_calls << " removed: " << minim_removed
        << " flips: " << flips << " subsumed: " << subsumed
        << " cost: " << std::setprecision(2) << cost << " of " << mconf.budget
        << " ticks(M) abs: " << abs.get_sum_ticks() / 1e6 << " f: " << f.get_sum_ticks() / 1e6
        << " deep: " << in_abs_vars.work * 10 / 1e6
        << " confl abs: " << abs.get_sum_conflicts() << " f: " << f.get_sum_conflicts()
        << " T: " << (cpuTime() - start_time) << " (setup: " << setup_time << " abs: " << abs_time
        << " f: " << f_time << " refine: " << refine_time << " deep: " << deep_time
        << " funs: " << funs_time << ")" << std::endl;
}

lbool CoverComp::finish(const lbool ret) {
    print_stats(ret == l_True ? "all X covered" : ret == l_False ? "X with no Y" : "gave up");
    return ret;
}

void CoverComp::set_cex(vector<lbool>& cex) {
    cex.assign(num_vars, l_Undef);
    for (uint32_t i = 0; i < num_univ; i++) cex[outer[i]] = abs.get_model()[to_f[outer[i]]];
}

// A clause of outer vars only: an X that falsifies it has no Y. As a
// helper it would be in every refinement
bool CoverComp::outer_only_cex(vector<lbool>& cex) {
    if (outer_only.empty()) return false;
    abs.new_var();
    vector<Lit> some = {Lit(abs.nVars()-1, true)};
    for (const auto& cl : outer_only) {
        abs.new_var();
        some.emplace_back(abs.nVars()-1, false);
        for (const auto& l : cl) abs.add_clause({~some.back(), ~l});
    }
    abs.add_clause(some);
    assumps = {~some[0]};
    if (timed(abs_time, [&] { return abs.solve(&assumps); }) == l_True) {
        set_cex(cex);
        return true;
    }
    abs.add_clause({some[0]});
    return false;
}

// no X in the cube of f's conflict has a Y, so any function will do there
void CoverComp::skip_cube() {
    auto cube = f.get_conflict();
    // A kept cube becomes a clause of the counted CNF: the shorter, the more it propagates
    if (mconf.keep_cubes && mconf.minim_cubes) {
        vector<Lit> cand = cube, as;
        for (const auto& l : cand) {
            if (out_of_ticks()) break;
            if (std::find(cube.begin(), cube.end(), l) == cube.end()) continue;
            as.clear();
            for (const auto& l2 : cube) if (l2 != l) as.push_back(~l2);
            if (timed(f_time, [&] { return f.solve(&as); }) == l_False) cube = f.get_conflict();
        }
    }
    cube_lits += cube.size();
    cost += sq_frac(cube.size(), num_univ);
    abs.add_clause(cube);
    cubes++;
    if (mconf.keep_cubes) {
        kept_cubes.emplace_back();
        for (const auto& l : cube) kept_cubes.back().emplace_back(outer[l.var()], l.sign());
        return;
    }
    // From here on abs only picks an X that has a Y: cubes say
    // little, the files that have them need 100k+ of them
    if (cubes == 1) add_cls_to_abs();
}

void CoverComp::add_cls_to_abs() {
    vector<uint32_t> to_abs(num_vars, none);
    for (const auto& v : outer) to_abs[v] = to_f[v];
    for (const auto& v : ys) {
        to_abs[v] = abs.nVars();
        abs.new_var();
    }
    vector<Lit> cl2;
    for (const auto& cl : cls) {
        cl2.clear();
        for (const auto& l : cl) cl2.emplace_back(to_abs[l.var()], l.sign());
        abs.add_clause(cl2);
    }
}

// abs gets the X that the model of f settles
void CoverComp::refine() {
    const double refine_start = cpuTime();
    auto model = f.get_model();
    get_some_false(model);
    if (flip_minim && some_false.size() > 1 && flip(model)) get_some_false(model);
    if (sat_minim && some_false.size() > 1) {
        const size_t before = some_false.size();
        model = minimize(model);
        get_some_false(model);
        assert(some_false.size() <= before);
        minim_removed += before - some_false.size();
    }
    cost += sq_frac(some_false.size(), num_helpers);
    if (subs_minim) drop_subsumed(some_false);
    ref_lits += some_false.size();
    if (mconf.need_funs) {
        ref_helpers.push_back(some_false);
        for (const auto& v : ys) ref_ys.push_back(model[to_f[v]] == l_True);
    }
    refine_time += cpuTime() - refine_start;
    if (!deep.empty()) {
        const double deep_start = cpuTime();
        for (const auto& v : ys) in_abs_vars.val[v] = model[to_f[v]];
        keep.push_back(deep_true(in_abs_vars));
        if (keep.back()->type != AIGT::t_const) some_false.push_back(~enc_abs.encode(keep.back()));
        else assert(!keep.back().neg);
        deep_time += cpuTime() - deep_start;
    }
    abs.add_clause(some_false);
}

lbool CoverComp::run(vector<lbool>& cex, vector<std::pair<uint32_t, aig_lit>>& new_defs) {
    start_time = cpuTime();
    abs.set_no_lucky();
    f.set_no_lucky();
    f.set_decide(false);
    add_vars_and_cls();
    tie_defs();
    add_helpers();
    if (subs_minim) find_subsumed();
    add_selectors();
    set_phases();
    init_flip();
    setup_time = cpuTime() - start_time;

    if (mconf.stop_at_cex && !mconf.assume_outer && outer_only_cex(cex)) return finish(l_False);
    for (const auto& cl : outer_only) abs.add_clause(cl);
    for (; cost < mconf.budget && !out_of_ticks(); rounds++) {
        if (rounds && rounds % mconf.stats_every == 0) print_stats("progress");
        if (timed(abs_time, [&] { return abs.solve(); }) == l_False) {
            if (mconf.need_funs) timed(funs_time, [&] { build_funs(new_defs); return 0; });
            return finish(l_True);
        }
        assumps.clear();
        for (uint32_t i = 0; i < num_univ; i++) assumps.emplace_back(to_f[outer[i]], abs.get_model()[to_f[outer[i]]] != l_True);
        if (timed(f_time, [&] { return f.solve(&assumps); }) == l_False) {
            if (mconf.stop_at_cex) {
                set_cex(cex);
                return finish(l_False);
            }
            skip_cube();
            if (mconf.keep_cubes && cubes > mconf.max_cubes) return finish(l_Undef);
            continue;
        }
        refine();
    }
    return finish(l_Undef);
}

// Clauses that share no existential, directly or through a function, are
// covered apart: together they need the product of their models
void Cover::split_components() {
    const uint32_t num_vars = vs.size();
    vector<char> state;
    vector<uint32_t> defined, free_leaves;
    CoverComp::classify(vs, cnf.get_clauses(), state, defined, free_leaves);
    vector<char> is_outer(num_vars, 0);
    for (uint32_t v = 0; v < num_vars; v++) if (vs.univ[v] || state[v] == 1) is_outer[v] = 1;

    vector<uint32_t> par(num_vars);
    for (uint32_t v = 0; v < num_vars; v++) par[v] = v;
    auto find = [&](uint32_t v) {
        while (par[v] != v) v = par[v] = par[par[v]];
        return v;
    };
    auto first_inner = [&](const vector<Lit>& cl) {
        for (const auto& l : cl) if (!is_outer[l.var()]) return l.var();
        return CoverComp::none;
    };
    for (const auto& cl : cnf.get_clauses()) {
        const uint32_t first = first_inner(cl);
        for (const auto& l : cl) if (!is_outer[l.var()]) par[find(l.var())] = find(first);
    }
    for (const auto& v : defined) if (state[v] == 2) {
        set<uint32_t> deps;
        AIG::get_dependent_vars(vs.def[v], deps, v);
        for (const auto& d : deps) if (!is_outer[d]) par[find(d)] = find(v);
    }
    vector<uint32_t> comp_of(num_vars, CoverComp::none);
    for (const auto& cl : cnf.get_clauses()) {
        const uint32_t first = first_inner(cl);
        if (first == CoverComp::none) { outer_only.push_back(cl); continue; }
        uint32_t& c = comp_of[find(first)];
        if (c == CoverComp::none) {
            c = comps.size();
            comps.emplace_back();
        }
        comps[c].push_back(cl);
    }
}

lbool Cover::cover_one(const vector<vector<Lit>>& comp_cls, const uint32_t verb, vector<lbool>& cex) {
    CoverComp comp(vs, cnf.get_aig_mng(), comp_cls, mconf, mconf.max_ticks ? mconf.max_ticks - used_ticks : 0, verb);
    const lbool ret = comp.run(cex, new_defs);
    used_ticks += comp.ticks();
    return ret;
}

lbool Cover::cover_components(vector<lbool>& cex) {
    const uint32_t verb = conf.verb;
    std::stable_sort(comps.begin(), comps.end(), [](const auto& a, const auto& b) { return a.size() < b.size(); });
    comps.back().insert(comps.back().end(), outer_only.begin(), outer_only.end());
    if (verb) std::cout << "c o [cover] components: " << comps.size() << " clauses of the largest: "
        << comps.back().size() << " of " << cnf.get_clauses().size() << std::endl;
    lbool ret = l_True;
    for (uint32_t i = 0; i < comps.size() && ret == l_True; i++) {
        if (mconf.max_ticks && used_ticks >= mconf.max_ticks) return l_Undef;
        const bool last = i + 1 == comps.size();
        ret = cover_one(comps[i], last ? verb : (verb ? verb - 1 : 0), cex);
        if (verb && !last && ret != l_True) std::cout << "c o [cover] component " << i << " with "
            << comps[i].size() << " clauses: " << (ret == l_False ? "X with no Y" : "gave up") << std::endl;
    }
    return ret;
}

void Cover::set_funs() {
    vector<aig_lit> funs;
    for (const auto& d : new_defs) funs.push_back(d.second);
    vs.to_orig(funs);
    for (uint32_t i = 0; i < funs.size(); i++) {
        const Lit o = vs.orig[new_defs[i].first];
        cnf.set_def(o.var(), o.sign() ? ~funs[i] : funs[i]);
    }
    const auto& sampl = cnf.get_orig_sampl_vars();
    for (uint32_t v = 0; v < cnf.num_defs(); v++)
        if (!sampl.count(v) && !cnf.defined(v)) cnf.set_def(v, cnf.get_aig_mng().new_const(false));
}

int64_t Cover::drop_covered() {
    const double start = cpuTime();
    const uint32_t num_vars = vs.size();
    if (std::any_of(cnf.get_clauses().begin(), cnf.get_clauses().end(), [](const auto& cl) { return cl.empty(); }))
        return 0;
    split_components();
    std::stable_sort(comps.begin(), comps.end(), [](const auto& a, const auto& b) { return a.size() < b.size(); });

    vector<char> fixed_weight(num_vars, 0);
    if (cnf.get_weighted()) for (uint32_t v = 0; v < num_vars; v++)
        if (!vs.univ[v] && cnf.weight_set(v)) fixed_weight[v] = 1;

    // A component only needs the part of psi that its X reach: the rest is
    // satisfiable apart from it, or nothing is counted anyway
    vector<uint32_t> par(num_vars);
    for (uint32_t v = 0; v < num_vars; v++) par[v] = v;
    auto find = [&](uint32_t v) {
        while (par[v] != v) v = par[v] = par[par[v]];
        return v;
    };
    for (const auto& cl : outer_only) for (const auto& l : cl) par[find(l.var())] = find(cl[0].var());
    vector<vector<uint32_t>> psi_of(num_vars);
    for (uint32_t i = 0; i < outer_only.size(); i++) psi_of[find(outer_only[i][0].var())].push_back(i);
    vector<char> root_seen(num_vars, 0);
    vector<uint32_t> roots;

    vector<char> gone(num_vars, 0);
    vector<vector<Lit>> kept = outer_only;
    vector<lbool> cex;
    vector<std::pair<uint32_t, aig_lit>> no_defs;
    uint32_t tried = 0, dropped = 0, replaced = 0, no_y = 0, gave_up = 0, weighted = 0;
    uint64_t cube_cls = 0, cube_lits = 0;
    // A defined var is a good one for the counter to branch on, and its
    // defining clauses propagate better than cubes: a component with one is
    // replaced only if its clauses mostly go away. Also when the var is taken
    // as a universal, being weighted
    vector<char> is_def(num_vars, 0);
    for (const auto& v : cnf.get_opt_sampl_vars()) is_def[v] = 1;
    for (const auto& v : cnf.get_sampl_vars()) is_def[v] = 0;
    auto drop_conf = mconf;
    drop_conf.stop_at_cex = true;
    drop_conf.keep_cubes = false;
    uint32_t kept_def = 0;
    for (auto& comp_cls : comps) {
        lbool ret = l_Undef;
        const auto any_var = [&](const vector<char>& flag) {
            return std::any_of(comp_cls.begin(), comp_cls.end(), [&](const auto& cl) {
                return std::any_of(cl.begin(), cl.end(), [&](const Lit l) { return flag[l.var()]; }); }); };
        const bool has_weight = any_var(fixed_weight);
        const bool has_def = mconf.keep_cubes && any_var(is_def);
        const bool only_drop = has_def && comp_cls.size() < mconf.def_replace_min_cls;
        weighted += has_weight;
        std::unique_ptr<CoverComp> comp;
        if (!has_weight && (!mconf.max_ticks || used_ticks < mconf.max_ticks)) {
            tried++;
            const size_t sz = comp_cls.size();
            for (const auto& cl : comp_cls) for (const auto& l : cl) {
                if (!vs.univ[l.var()]) continue;
                const uint32_t r = find(l.var());
                if (!root_seen[r]) { root_seen[r] = 1; roots.push_back(r); }
            }
            for (const auto& r : roots) {
                root_seen[r] = 0;
                for (const auto& i : psi_of[r]) comp_cls.push_back(outer_only[i]);
            }
            roots.clear();
            // a quarter of it at most, one hopeless component does not use it all up
            const uint64_t ticks = mconf.max_ticks ? std::min(mconf.max_ticks - used_ticks, mconf.max_ticks / 4 + 1) : 0;
            comp = std::make_unique<CoverComp>(vs, cnf.get_aig_mng(), comp_cls, only_drop ? drop_conf : mconf,
                ticks, conf.verb >= 2 ? conf.verb - 1 : 0);
            ret = comp->run(cex, no_defs);
            used_ticks += comp->ticks();
            comp_cls.resize(sz);
            no_y += ret == l_False;
            gave_up += ret == l_Undef;
        }
        // an empty cube: no X has a Y, let the rest of Arjun find that out
        if (ret == l_True && std::any_of(comp->kept_cubes.begin(), comp->kept_cubes.end(),
                [](const auto& cl) { return cl.empty(); })) ret = l_Undef;
        if (ret == l_True && has_def && comp->kept_cubes.size() * mconf.def_replace_ratio > comp_cls.size()) {
            ret = l_Undef;
            kept_def++;
        }
        if (ret != l_True) {
            for (auto& cl : comp_cls) kept.push_back(std::move(cl));
            continue;
        }
        if (comp->kept_cubes.empty()) dropped++;
        else replaced++;
        cube_cls += comp->kept_cubes.size();
        for (const auto& cl : comp->kept_cubes) cube_lits += cl.size();
        for (auto& cl : comp->kept_cubes) kept.push_back(std::move(cl));
        for (const auto& cl : comp_cls) for (const auto& l : cl) if (!vs.univ[l.var()]) gone[l.var()] = 1;
    }

    const int64_t removed = (int64_t)cnf.get_clauses().size() - (int64_t)kept.size();
    vector<vector<Lit>> red;
    for (const auto& cl : cnf.get_red_clauses())
        if (std::none_of(cl.begin(), cl.end(), [&](const Lit l) { return gone[l.var()]; })) red.push_back(cl);
    vector<uint32_t> opt_sampl;
    for (const auto& v : cnf.get_opt_sampl_vars()) if (!gone[v]) opt_sampl.push_back(v);
    cnf.set_all_clauses(std::move(kept), std::move(red));
    cnf.set_opt_sampl_vars(opt_sampl);

    if (conf.verb) std::cout << "c o [cover-drop] components: " << comps.size() << " tried: " << tried
        << " dropped: " << dropped << " replaced: " << replaced << " by cls: " << cube_cls
        << " avg sz: " << std::setprecision(1) << std::fixed << (cube_cls ? (double)cube_lits / cube_cls : 0)
        << " no-Y: " << no_y << " gave up: " << gave_up << " weighted: " << weighted << " kept defined: " << kept_def
        << " cls removed: " << removed << " vars gone: " << std::count(gone.begin(), gone.end(), 1)
        << " Mticks: " << std::setprecision(1) << std::fixed << used_ticks / 1e6
        << " T: " << std::setprecision(2) << cpuTime() - start << std::endl;
    return removed;
}

lbool Cover::run(vector<lbool>& cex) {
    split_components();
    vector<lbool> vs_cex;
    const lbool ret = comps.size() <= 1 ? cover_one(cnf.get_clauses(), conf.verb, vs_cex) : cover_components(vs_cex);
    if (ret == l_True && mconf.need_funs) set_funs();
    if (ret == l_False) cex = vs.univ_to_orig(cnf, vs_cex);
    return ret;
}
