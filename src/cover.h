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

namespace ArjunInt {

// Covers the X space with models of `cls`, over ORIG vars: a model settles
// every X that satisfies the universal parts of the clauses its Y leaves
// unsatisfied. This is the CEGAR of the 2QBF literature. l_True: the
// vars with no def yet got their Skolem functions, l_Undef: gave up. An X
// with no Y is returned in `cex` with l_False if stop_at_cex, else its
// cube is skipped. A refinement naming fraction f of the helpers costs
// f^2 of the budget: next to nothing while it converges. max_ticks limits
// the SAT solvers' work, 0 = no limit. Without need_funs, l_True comes
// with no Skolem functions: only the verdict. minim: a refinement is
// shortened by asking for a model, of the same X, whose existentials satisfy
// more of the clauses.
CMSat::lbool cover(ArjunNS::SimplifiedCNF& cnf, const std::vector<std::vector<CMSat::Lit>>& cls,
        const double budget, const uint64_t max_ticks, const bool stop_at_cex, const bool need_funs, const bool minim,
        std::vector<CMSat::lbool>& cex,
        const uint32_t verb);

}
