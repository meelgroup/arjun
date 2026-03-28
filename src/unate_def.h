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
#include <cstdint>
#include <set>
#include <vector>
#include <memory>
#include <cryptominisat5/solvertypesmini.h>
#include <cryptominisat5/cryptominisat.h>
#include "arjun.h"
#include "config.h"
#include "metasolver.h"

class Unate {
    public:
        Unate(const ArjunInt::Config& _conf) : conf(_conf) {}
        ~Unate() = default;

        void synthesis_unate_def(ArjunNS::SimplifiedCNF& cnf);
        void synthesis_unate(ArjunNS::SimplifiedCNF& cnf);
    private:

        ArjunInt::Config conf;
        std::set<uint32_t> input;
        std::set<uint32_t> to_define;
        std::set<uint32_t> backward_defined;

        std::vector<uint32_t> var_to_indic; // for each var, the indicator
                                            // variable in the SAT solver that is true iff the var is equal to its copy (i.e. not flipped)
        std::unique_ptr<ArjunInt::MetaSolver> setup_f_not_f(const ArjunNS::SimplifiedCNF& cnf);
};
