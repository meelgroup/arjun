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

#include "cover_synth.h"
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <limits>

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::vector;

// Covers one component with what is left of the ticks, at most max_comp_ticks if set
CoverComponent::Result CoverSynth::cover_one(const Cls& comp_cls, const uint32_t verb, const uint64_t max_comp_ticks) {
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
lbool CoverSynth::cover_components(vector<lbool>& cex, vector<char>& removable) {
    assert(comps.comps.size() > 1);
    assert(cex.empty() && removable.empty() && found_funs.empty());
    const uint32_t verb = conf.verb;
    std::stable_sort(comps.comps.begin(), comps.comps.end(), [](const auto& a, const auto& b) { return a.size() < b.size(); });
    comps.comps.back().insert(comps.comps.back().end(), comps.x_cls.begin(), comps.x_cls.end());
    if (verb) std::cout << "c o [cover] components: " << comps.comps.size() << " clauses of the largest: "
        << comps.comps.back().size() << " of " << cnf.get_clauses().size() << std::endl;
    removable.assign(comps.comps.size(), 0);
    found_funs.resize(comps.comps.size());
    lbool ret = l_True;
    for (uint32_t i = 0; i < comps.comps.size(); i++) {
        if (cconf.max_ticks && used_ticks >= cconf.max_ticks) return l_Undef;
        const bool last = i + 1 == comps.comps.size();
        // one hopeless component does not use it all up, the last gets the rest
        const uint64_t max_comp_ticks = last || !cconf.max_ticks ? 0 : cconf.max_ticks / 4 + 1;
        auto r = cover_one(comps.comps[i], last ? verb : (verb ? verb - 1 : 0), max_comp_ticks);
        if (verb && !last && r.ret != l_True) std::cout << "c o [cover] component " << i << " with "
            << comps.comps[i].size() << " clauses: " << (r.ret == l_False ? "X with no Y" : "gave up") << std::endl;
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
void CoverSynth::set_funs(const vector<char>& only) {
    assert(cconf.need_funs);
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
    trans.funs_to_orig(funs);
    for (uint32_t i = 0; i < funs.size(); i++) {
        const Lit o = trans.orig_of(vars[i]);
        cnf.set_def(o.var(), o.sign() ? ~funs[i] : funs[i]);
    }
    if (!only.empty()) return;
    const auto& sampl = cnf.get_orig_sampl_vars();
    for (uint32_t v = 0; v < cnf.num_defs(); v++)
        if (!sampl.count(v) && !cnf.defined(v)) cnf.set_def(v, cnf.get_aig_mng().new_const(false));
}

// Decides ∀X ∃Y of the whole CNF, component by component; sets the defs if asked
lbool CoverSynth::run(vector<lbool>& cex) {
    assert(cex.empty());
    comps = split_into_components(problem, cnf.get_clauses());
    vector<lbool> cex_internal;
    vector<char> removable;
    lbool ret;
    if (comps.comps.size() <= 1) {
        auto r = cover_one(cnf.get_clauses(), conf.verb);
        ret = r.ret;
        cex_internal = std::move(r.cex);
        found_funs.push_back(std::move(r.funs));
    } else ret = cover_components(cex_internal, removable);
    if (ret == l_False) assert(!cex_internal.empty());
    else assert(cex_internal.empty());
    if (ret == l_True && cconf.need_funs) set_funs({});
    if (ret == l_Undef && cconf.need_funs) keep_covered(removable);
    if (ret == l_False) cex = trans.x_to_orig(cnf, cex_internal);
    return ret;
}

// A component covered with no X-cube blocked and no function of X has a Y
// for every X, so its clauses go, and its functions, whatever the ys of the
// others are, become defs. Any other stays: its clauses may restrict X. The
// rest is left to the passes after. The clauses of X only stay
void CoverSynth::keep_covered(const vector<char>& removable) {
    assert(cconf.need_funs);
    assert(removable.empty() || removable.size() == comps.comps.size());
    if (std::none_of(removable.begin(), removable.end(), [](const char c) { return c; })) return;
    set_funs(removable);
    vector<char> gone(problem.size(), 0);
    for (uint32_t i = 0; i < comps.comps.size(); i++) if (removable[i])
        for (const auto& cl : comps.comps[i]) for (const auto& l : cl) if (!comps.on_x_side[l.var()]) gone[l.var()] = 1;
    const int64_t removed = rewrite_cnf_with_cubes(cnf, gone, {});
    // the ys leave the CNF as BVE's do: the passes after take a defined var in it as one its clauses define
    constexpr uint32_t m = std::numeric_limits<uint32_t>::max();
    vector<uint32_t> map_here_to_there(cnf.nVars(), m);
    uint32_t new_nvars = 0;
    for (uint32_t v = 0; v < cnf.nVars(); v++) if (!gone[v]) map_here_to_there[v] = new_nvars++;
    cnf.renumber_vars(map_here_to_there, new_nvars);
    if (conf.verb) std::cout << "c o [cover] removed " << std::count(removable.begin(), removable.end(), 1)
        << " of " << comps.comps.size() << " components, cls removed: " << removed
        << " vars gone: " << std::count(gone.begin(), gone.end(), 1) << std::endl;
}
