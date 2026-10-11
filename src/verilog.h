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
#include <iosfwd>
#include <set>
#include <string>
#include <vector>

// One module of single-bit nets: port xN is variable N-1, every other net is
// an internal wire. Vectors, instances and always blocks are not handled.
namespace ArjunInt {

// The outputs are the defs that are set and not in inputs
void write_verilog(std::ostream& out, const std::vector<ArjunNS::aig_lit>& defs,
        const std::set<uint32_t>& inputs);

// Reads continuous assignments over ~ ! & ^ | ?: and parentheses, in any
// order. A port inside an expression becomes a literal of its variable.
// Returns false and fills err (with the line number) on anything else.
bool read_verilog(std::istream& in, std::vector<ArjunNS::aig_lit>& defs,
        std::set<uint32_t>& inputs, std::string& err);

}
