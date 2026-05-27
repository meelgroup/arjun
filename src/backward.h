/*
 Arjun

 Copyright (c) 2019, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#include "minimize.h"

namespace ArjunInt {

struct Backward : public Minimize
{
    Backward(const Config& _conf) : Minimize(_conf) {}
    ~Backward() = default;

    void run_backward(ArjunNS::SimplifiedCNF& cnf, bool all_indep);
    ArjunNS::Arjun::IndepInfo run_backward_info(ArjunNS::SimplifiedCNF& cnf, bool all_indep);

    template<typename T>
    void fill_assumptions_backward(
        std::vector<CMSat::Lit>& assumptions,
        std::vector<uint32_t>& unknown,
        const std::vector<char>& unknown_set,
        const T& indep,
        const std::optional<std::set<uint32_t>>& ignore = std::nullopt);
    void backward_round();
    void backward_round_synth(ArjunNS::SimplifiedCNF& cnf, const ArjunNS::Arjun::ManthanConf& mconf);
    void add_all_indics_except(const std::set<uint32_t>& except);
    void order_by_file(const std::string& fname, std::vector<uint32_t>& unknown);
    void print_sorted_unknown(const std::vector<uint32_t>& unknown) const;
};

}
