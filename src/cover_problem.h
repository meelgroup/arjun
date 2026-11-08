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

#include "arjun.h"
#include <map>
#include <set>
#include <vector>

namespace ArjunInt {

// What cover works on: per var, whether it is an X, and the function it
// already has, if any. In the CNF's numbering, see OrigTranslation
struct CoverProblem {
    std::vector<char> is_x;
    std::vector<ArjunNS::aig_lit> def;

    // no defs, the CNF's own numbering: for counting
    CoverProblem(const uint32_t nvars, const std::vector<uint32_t>& xs) : is_x(nvars, 0), def(nvars) {
        for (const auto& v : xs) is_x[v] = 1;
    }
    CoverProblem() = default;
    [[nodiscard]] uint32_t size() const { return is_x.size(); }
    [[nodiscard]] bool defined(const uint32_t v) const { return def[v] != nullptr; }
};

// Between the orig vars, which the defs and the results are over, and the
// CNF's numbering cover works in, as Cegr does: the CNF's vars, numbered as
// there, then the orig vars that the defs reach and that are not in it.
// Used at the entrance (problem()) and at the exit (the rest) only
class OrigTranslation {
public:
    explicit OrigTranslation(const ArjunNS::SimplifiedCNF& cnf);
    // the defs translated once
    [[nodiscard]] CoverProblem problem(const ArjunNS::SimplifiedCNF& cnf) const;
    [[nodiscard]] CMSat::Lit orig_of(const uint32_t v) const { return orig[v]; }
    void funs_to_orig(std::vector<ArjunNS::aig_lit>& funs) const;
    // The X's values, from those of the vars. False for one that is not
    // reached: it is free
    [[nodiscard]] std::vector<CMSat::lbool> x_to_orig(const ArjunNS::SimplifiedCNF& cnf,
            const std::vector<CMSat::lbool>& vals) const {
        std::vector<CMSat::lbool> ret(cnf.num_defs(), CMSat::l_Undef);
        for (const auto& o : cnf.get_orig_sampl_vars()) {
            const CMSat::Lit l = of_orig[o];
            ret[o] = l == CMSat::lit_Undef ? CMSat::l_False : vals[l.var()] ^ l.sign();
        }
        return ret;
    }

private:
    std::vector<CMSat::Lit> orig; // value(v) = value(orig[v].var()) ^ orig[v].sign()
    std::vector<CMSat::Lit> of_orig; // the other way, lit_Undef if not reached

    // One cache for all the AIGs: they share most of their nodes, and
    // translating them one by one copies those into each
    using Cache = std::map<ArjunNS::aig_lit, ArjunNS::aig_lit>;
    template<class F> static ArjunNS::aig_lit translate(const ArjunNS::aig_lit& a, Cache& cache, F&& lit_of_var) {
        return ArjunNS::AIG::transform<ArjunNS::aig_lit>(a,
            [&](const ArjunNS::AIGT type, const uint32_t var, const ArjunNS::aig_lit* l, const ArjunNS::aig_lit* r) {
                if (type == ArjunNS::AIGT::t_const) return ArjunNS::AIG::new_const(true);
                if (type == ArjunNS::AIGT::t_lit) return ArjunNS::AIG::new_lit(lit_of_var(var));
                return ArjunNS::AIG::new_and(*l, *r);
            }, cache);
    }
};

inline OrigTranslation::OrigTranslation(const ArjunNS::SimplifiedCNF& cnf) {
    of_orig.assign(cnf.num_defs(), CMSat::lit_Undef);
    const auto new_to_orig = cnf.get_new_to_orig_var();
    for (uint32_t v = 0; v < cnf.nVars(); v++) {
        const auto it = new_to_orig.find(v);
        release_assert(it != new_to_orig.end() && "every var of the CNF must have an orig var");
        orig.push_back(it->second);
        of_orig[it->second.var()] = CMSat::Lit(v, it->second.sign());
    }
    for (uint32_t v = 0; v < orig.size(); v++) {
        const uint32_t o = orig[v].var();
        if (!cnf.defined(o)) continue;
        std::set<uint32_t> deps;
        ArjunNS::AIG::get_dependent_vars(cnf.get_def(o), deps, o);
        for (const auto& d : deps) if (of_orig[d] == CMSat::lit_Undef) {
            of_orig[d] = CMSat::Lit(orig.size(), false);
            orig.emplace_back(d, false);
        }
    }
}

inline CoverProblem OrigTranslation::problem(const ArjunNS::SimplifiedCNF& cnf) const {
    CoverProblem p;
    p.is_x.resize(orig.size());
    p.def.resize(orig.size());
    Cache cache;
    for (uint32_t v = 0; v < orig.size(); v++) {
        const uint32_t o = orig[v].var();
        p.is_x[v] = cnf.get_orig_sampl_vars().count(o);
        if (!cnf.defined(o)) continue;
        const ArjunNS::aig_lit d = translate(cnf.get_def(o), cache, [&](const uint32_t u) { return of_orig[u]; });
        p.def[v] = orig[v].sign() ? ~d : d;
    }
    return p;
}

inline void OrigTranslation::funs_to_orig(std::vector<ArjunNS::aig_lit>& funs) const {
    Cache cache;
    for (auto& fun : funs) fun = translate(fun, cache, [&](const uint32_t v) { return orig[v]; });
}

}
