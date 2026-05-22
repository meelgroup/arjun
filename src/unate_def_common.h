/*
 Arjun

 Copyright (c) 2026, Mate Soos and Kuldeep S. Meel. All rights reserved.

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
#include <cstdint>
#include <memory>
#include <set>
#include "arjun.h"
#include "config.h"
#include "metasolver.h"

namespace ArjunInt {

// Build the miter solver `F(X, Y) ∧ ¬F(X, Y')` shared by synthesis_unate_def
// and UnateDefRep. Inputs (vars in `input`) live in NEW-var-space and are
// shared between the Y and Y' sides; non-input vars get a parallel Y'-side
// var at offset `cnf.nVars()`. Each F-clause `cl` gets a fresh selector
// `z_cl` such that z_cl ⇔ cl-on-Y'; the disjunction of `~z_cl` across all
// clauses asserts "at least one clause is FALSE on Y'", giving ¬F(X, Y').
std::unique_ptr<ArjunInt::MetaSolver> setup_f_not_f(
    const ArjunNS::SimplifiedCNF& cnf,
    const std::set<uint32_t>& input,
    const ArjunInt::Config& conf);

}
