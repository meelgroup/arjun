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

#include "backward.h"

namespace ArjunInt {

struct Minimize : public Backward
{
    Minimize(const Config& _conf, const ArjunNS::Arjun::InterpConf& _iconf) : Backward(_conf, _iconf) {}
    ~Minimize() = default;

    //simp
    std::vector<uint32_t> toClear;
    bool simplify();
    bool remove_definable_by_gates();
    void remove_definable_by_irreg_gates();
    void remove_zero_assigned_literals(bool print = true);
    void remove_eq_literals();
    void get_empty_occs();
    bool probe_all();
    bool simplify_bve_only();
    bool run_gauss_jordan();
    void check_no_duplicate_in_sampling_set();
    void order_sampl_set_for_simp();

    [[nodiscard]] bool set_zero_weight_lits(const ArjunNS::SimplifiedCNF& cnf) const;
    bool preproc_and_duplicate(const ArjunNS::SimplifiedCNF& orig_cnf);

    void run_minimize(ArjunNS::SimplifiedCNF& cnf, bool all_indep);
    ArjunNS::Arjun::IndepInfo run_minimize_info(ArjunNS::SimplifiedCNF& cnf, bool all_indep);
};

}
