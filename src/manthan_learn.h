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

#include "manthan.h"
#include <cstdint>
#include <vector>
#include <string>

using std::vector;
using std::uint32_t;
using std::string;
using sample = vector<lbool>;

// These ask mlpack to give more info & warnings
//#define MLPACK_PRINT_INFO
//#define MLPACK_PRINT_WARN
#include <mlpack.hpp>

namespace ArjunInt {

class ManthanLearn {
public:
    ManthanLearn(Manthan& _manthan, const Config& _conf, const ArjunNS::Arjun::ManthanConf& _mconf) :
        m(_manthan), conf(_conf), mconf(_mconf) {
            point_0.zeros(m.cnf.nVars());
            point_1.ones(m.cnf.nVars());
        }
    void full_train();
private:
    double train(const vector<sample>& orig_samples, const uint32_t v);
    FHolder<MetaSolver2>::Formula recur(
            mlpack::tree::DecisionTree<>* node, const uint32_t learned_v, const vector<uint32_t>& var_remap, uint32_t depth, uint32_t& max_depth);
    arma::vec point_0;
    arma::vec point_1;

    Manthan& m;
    const Config& conf;
    const ArjunNS::Arjun::ManthanConf& mconf;
};
}
