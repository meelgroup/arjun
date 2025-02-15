/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file <soos.mate@gmail.com>

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
***********************************************/

#pragma once

#include <cstdint>
#include <cstdio>
#include <utility>
#include <vector>

using std::pair;
using std::make_pair;
using std::vector;

namespace ArjunNS {
  struct SimplifiedCNF;
}

namespace CCNR {

class LSSolver;

struct CCNRConf {
  uint32_t verb = 1;
  int64_t yalsat_max_mems = 1000;
};

class Ganak_ccnr {
public:
    int main(ArjunNS::SimplifiedCNF const* cnf);
    Ganak_ccnr(uint32_t verb);
    ~Ganak_ccnr();

private:
    void flipvar(uint32_t toflip);
    void parse_parameters();
    void init_for_round();
    bool init_problem();
    LSSolver* ls_s = nullptr;
    uint32_t cl_num = 0;

    template<class T> void add_this_clause(const T& cl);
    vector<int> yals_lits;

    CCNRConf conf;
    const ArjunNS::SimplifiedCNF* cnf;
};

}
