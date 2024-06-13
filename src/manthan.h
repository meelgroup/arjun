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

#include "arjun.h"
#include "config.h"

#include <cstdint>
#include <vector>
#include <set>

using std::vector;
using std::set;

using namespace ArjunInt;
using namespace ArjunNS;

class Manthan {
    public:
        Manthan(Config& _conf) : conf(_conf) {}
        void do_manthan(SimplifiedCNF& cnf);

    private:
        const Config& conf;
        CMSat::SATSolver sample_solver;
        set<uint32_t> input;
        set<uint32_t> output;

        void add_sample_clauses(SimplifiedCNF& cnf);
        vector<vector<CMSat::lbool>> get_samples(const SimplifiedCNF& cnf, uint32_t num_samples);
        void train(const vector<vector<CMSat::lbool>>& samples, uint32_t v)
};
