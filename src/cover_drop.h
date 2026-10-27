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

#pragma once

#include "cover.h"

namespace ArjunInt {

// For counting: no defs, the CNF's own numbering, xs are X. A component C
// whose existentials Y_C occur nowhere else, with every X of the clauses of
// X only, psi, having a Y_C, is removed: ∃Y psi ∧ C ∧ rest = psi ∧ ∃Y rest.
// With max_cubes, C is replaced by the clauses that rule out the cubes of X
// with no Y_C, if they are few. Each one is checked against psi only, never
// against the others, which may go too. A component with a weighted
// existential stays: its weights would go.
class CoverDrop {
public:
    // max_cubes 0: only remove
    CoverDrop(const Config& _conf, ArjunNS::SimplifiedCNF& _cnf, const std::vector<uint32_t>& xs,
            uint64_t max_ticks, uint32_t max_cubes);
    // Returns the clauses removed, net
    int64_t run();

private:
    // a component with a var of the opt sampling set, defined, is replaced
    // only if it has this many clauses, and the cubes are 1/ratio of them at most
    static constexpr uint32_t def_replace_min_cls = 1000;
    static constexpr uint32_t def_replace_ratio = 50;

    struct DropStats {
        uint32_t tried = 0, dropped = 0, replaced = 0, no_y = 0, gave_up = 0, weighted = 0, kept_def = 0;
        uint64_t cube_cls = 0, cube_lits = 0;
        uint32_t up_ticks = 0, up_cubes = 0, out_of_budget = 0;
        uint64_t done_ticks = 0, max_done_ticks = 0, up_ticks_used = 0, confl = 0;
        double max_comp_t = 0;
        void print(size_t num_comps, int64_t removed, size_t vars_gone, uint64_t used_ticks, double start) const;
    };
    // A component only needs the part of psi that its X reach, through the X
    // psi's clauses share: the rest is satisfiable apart from it, or nothing
    // is counted anyway
    class PsiReach {
    public:
        PsiReach(const Cls& psi, uint32_t num_vars);
        // appends to comp_cls the clauses of psi its X reach
        void add_reached(const std::vector<char>& is_x, Cls& comp_cls);
    private:
        const Cls& psi;
        UnionFind uf;
        std::vector<std::vector<uint32_t>> psi_of; // per root, its clauses
        std::vector<char> root_seen;
        std::vector<uint32_t> roots;
    };
    struct Covered {
        CMSat::lbool ret = CMSat::l_Undef;
        Cls cubes; // keep_cubes: per X-cube with no Y, a clause that rules it out
    };
    // what becomes of a component. keep_def: kept as its defined var beats the cubes
    enum class Action { keep, keep_def, drop, replace };
    Covered cover_for_drop(Cls& comp_cls, bool has_def, PsiReach& psi, DropStats& drop_stats);
    Action choose_action(const Covered& covered, bool has_def, size_t num_cls) const;

    const Config& conf;
    ArjunNS::SimplifiedCNF& cnf;
    const CoverProblem problem;
    CoverComponent::Conf cconf;
    uint64_t used_ticks = 0;
};

}
