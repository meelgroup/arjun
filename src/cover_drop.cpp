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

#include "cover_drop.h"
#include <iomanip>
#include <iostream>
#include <algorithm>

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::vector;
using NoY = CoverComponent::Conf::NoY;

CoverDrop::CoverDrop(const Config& _conf, SimplifiedCNF& _cnf, const vector<uint32_t>& xs,
        const uint64_t max_ticks, const uint32_t max_cubes) :
        conf(_conf), cnf(_cnf), problem(_cnf.nVars(), xs) {
    cconf.max_ticks = max_ticks;
    cconf.no_y = max_cubes ? NoY::keep : NoY::stop;
    cconf.max_cubes = max_cubes;
    cconf.assume_outer = true;
    cconf.need_funs = false;
}

// The CNF is psi (clauses over X only) and components C_i over disjoint
// existentials Y_i. The count is of psi ∧ ∃Y_1 C_1 ∧ ... ∧ ∃Y_n C_n, so
// each component, checked against the part of psi its X reach, ends up:
// - removed: every X satisfying psi has a Y_i, so ∃Y_i C_i is true
// - replaced (NoY::keep): the minimized X-cubes with no Y_i, as clauses,
//   which together are exactly ∃Y_i C_i. Not if there are over max_cubes of
//   them, nor if C_i has a defined var and they do not make it much smaller
// - kept: it has a weighted Y (its weight would be lost), or the ticks ran out
// Each component gets at most a quarter of max_ticks.
int64_t CoverDrop::run() {
    assert(used_ticks == 0);
    const double start = cpuTime();
    const uint32_t num_vars = problem.size();

    // UNSAT CNF, return
    if (std::any_of(cnf.get_clauses().begin(), cnf.get_clauses().end(), [](const auto& cl) { return cl.empty(); }))
        return 0;

    auto comps = split_into_components(problem, cnf.get_clauses());
    auto& components = comps.comps;
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

    PsiReach psi(comps.x_cls, num_vars);
    DropStats drop_stats;
    vector<char> gone(num_vars, 0);
    Cls cubes;
    for (auto& comp_cls : components) {
        const bool has_weight = has_var(comp_cls, weighted_y);
        const bool has_def = cconf.no_y == NoY::keep && has_var(comp_cls, is_def);
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

    const int64_t removed = rewrite_cnf_with_cubes(cnf, gone, std::move(cubes));
    if (conf.verb) drop_stats.print(components.size(), removed, std::count(gone.begin(), gone.end(), 1), used_ticks, start);
    return removed;
}

// Covers the component with the part of psi it reaches. With a defined var
// and few clauses, cubes would not replace it: then it can only be dropped
CoverDrop::Covered CoverDrop::cover_for_drop(Cls& comp_cls, const bool has_def, PsiReach& psi, DropStats& drop_stats) {
    assert(cconf.assume_outer);
    if (cconf.max_ticks) assert(used_ticks < cconf.max_ticks);
    drop_stats.tried++;
    const size_t num_comp_cls = comp_cls.size();
    psi.add_reached(problem.is_x, comp_cls);
    auto drop_conf = cconf;
    drop_conf.no_y = NoY::stop;
    const bool only_drop = has_def && num_comp_cls < def_replace_min_cls;
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
    if (cconf.no_y == NoY::keep && !only_drop) assert(covered.ret != l_False);
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
CoverDrop::Action CoverDrop::choose_action(const Covered& covered, const bool has_def, const size_t num_cls) const {
    assert(covered.cubes.empty() || cconf.no_y == NoY::keep);
    if (covered.ret != l_True) return Action::keep;
    // an empty cube: no X has a Y, let the rest of Arjun find that out
    if (std::any_of(covered.cubes.begin(), covered.cubes.end(), [](const auto& cl) { return cl.empty(); })) return Action::keep;
    if (has_def && covered.cubes.size() * def_replace_ratio > num_cls) return Action::keep_def;
    return covered.cubes.empty() ? Action::drop : Action::replace;
}

// Groups psi's clauses by the X they share
CoverDrop::PsiReach::PsiReach(const Cls& _psi, const uint32_t num_vars) :
        psi(_psi), uf(num_vars), psi_of(num_vars), root_seen(num_vars, 0) {
    for (const auto& cl : psi) assert(!cl.empty());
    for (const auto& cl : psi) for (const auto& l : cl) uf.join(l.var(), cl[0].var());
    for (uint32_t i = 0; i < psi.size(); i++) psi_of[uf.find(psi[i][0].var())].push_back(i);
}

// Appends to comp_cls the clauses of psi that its X reach
void CoverDrop::PsiReach::add_reached(const vector<char>& is_x, Cls& comp_cls) {
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
void CoverDrop::DropStats::print(const size_t num_comps, const int64_t removed, const size_t vars_gone,
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
