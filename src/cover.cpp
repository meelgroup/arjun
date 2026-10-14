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

CoverVars::CoverVars(const SimplifiedCNF& cnf) {
    of_orig.assign(cnf.num_defs(), lit_Undef);
    const auto new_to_orig = cnf.get_new_to_orig_var();
    for (uint32_t v = 0; v < cnf.nVars(); v++) {
        const auto it = new_to_orig.find(v);
        release_assert(it != new_to_orig.end() && "every var of the CNF must have an orig var");
        orig.push_back(it->second);
        of_orig[it->second.var()] = Lit(v, it->second.sign());
    }
    for (uint32_t v = 0; v < orig.size(); v++) {
        const uint32_t o = orig[v].var();
        if (!cnf.defined(o)) continue;
        set<uint32_t> deps;
        AIG::get_dependent_vars(cnf.get_def(o), deps, o);
        for (const auto& d : deps) if (of_orig[d] == lit_Undef) {
            of_orig[d] = Lit(orig.size(), false);
            orig.emplace_back(d, false);
        }
    }
    def.resize(orig.size());
    univ.resize(orig.size());
    Cache cache;
    for (uint32_t v = 0; v < orig.size(); v++) {
        const uint32_t o = orig[v].var();
        univ[v] = cnf.get_orig_sampl_vars().count(o);
        if (!cnf.defined(o)) continue;
        const aig_lit d = translate(cnf.get_def(o), cache, [&](const uint32_t u) { return of_orig[u]; });
        def[v] = orig[v].sign() ? ~d : d;
    }
}

void CoverVars::to_orig(vector<aig_lit>& funs) const {
    Cache cache;
    for (auto& fun : funs) fun = translate(fun, cache, [&](const uint32_t v) { return orig[v]; });
}

void CoverComp::classify(const CoverVars& vs, const vector<vector<Lit>>& cls, vector<char>& state,
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
    for (uint32_t v = 0; v < num_vars; v++) if (vs.univ[v]) outer.push_back(v);
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
    cube_lits += cube.size();
    cost += sq_frac(cube.size(), num_univ);
    abs.add_clause(cube);
    cubes++;
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

    if (mconf.stop_at_cex && outer_only_cex(cex)) return finish(l_False);
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
    CoverComp::classify(vs, cls, state, defined, free_leaves);
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
    for (const auto& cl : cls) {
        const uint32_t first = first_inner(cl);
        for (const auto& l : cl) if (!is_outer[l.var()]) par[find(l.var())] = find(first);
    }
    for (const auto& v : defined) if (state[v] == 2) {
        set<uint32_t> deps;
        AIG::get_dependent_vars(vs.def[v], deps, v);
        for (const auto& d : deps) if (!is_outer[d]) par[find(d)] = find(v);
    }
    vector<uint32_t> comp_of(num_vars, CoverComp::none);
    for (const auto& cl : cls) {
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
        << comps.back().size() << " of " << cls.size() << std::endl;
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

lbool Cover::run(vector<lbool>& cex) {
    split_components();
    vector<lbool> vs_cex;
    const lbool ret = comps.size() <= 1 ? cover_one(cls, conf.verb, vs_cex) : cover_components(vs_cex);
    if (ret == l_True && mconf.need_funs) set_funs();
    if (ret == l_False) {
        cex.assign(cnf.num_defs(), l_Undef);
        for (const auto& o : cnf.get_orig_sampl_vars()) {
            const Lit l = vs.of_orig[o];
            cex[o] = l == lit_Undef ? l_False : vs_cex[l.var()] ^ l.sign();
        }
    }
    return ret;
}
