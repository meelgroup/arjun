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

// Covers the X space with models of cnf's clauses: a model settles
// every X that satisfies the universal parts of the clauses its Y leaves
// unsatisfied. This is the CEGAR of the 2QBF literature. l_True: the
// vars with no def yet got their Skolem functions, l_Undef: gave up. An X
// with no Y is returned in `cex` with l_False if stop_at_cex, else its
// cube is skipped, and x_solver gets the clauses so that no more come up.
// The limits and the ways a refinement is shortened: see Arjun::CoverConf.
//
// The defs that cnf already has are kept, and used: a model is then the
// values of the vars with no def, and it settles the X for which the
// clauses hold with the defined vars following their defs.
class CoverSynth {
public:
    CoverSynth(const Config& _conf, const ArjunNS::Arjun::CoverConf& _cconf, ArjunNS::SimplifiedCNF& _cnf) :
        conf(_conf), cnf(_cnf), trans(_cnf), problem(trans.problem(_cnf)) {
        static_cast<ArjunNS::Arjun::CoverConf&>(cconf) = _cconf;
    }
    CMSat::lbool run(std::vector<CMSat::lbool>& cex);

private:
    CMSat::lbool cover_components(std::vector<CMSat::lbool>& cex, std::vector<char>& removable);
    CoverComponent::Result cover_one(const Cls& comp_cls, const uint32_t verb, uint64_t max_comp_ticks = 0);
    void set_funs(const std::vector<char>& only);
    void keep_covered(const std::vector<char>& removable);

    const Config& conf;
    CoverComponent::Conf cconf;
    ArjunNS::SimplifiedCNF& cnf;
    const OrigTranslation trans;
    const CoverProblem problem;

    Components comps;
    std::vector<CoverComponent::Funs> found_funs; // per component
    uint64_t used_ticks = 0;
};

}
