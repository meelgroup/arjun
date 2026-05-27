/*
 Arjun

 cadet.h — Phase-E-only synthesis driver. Enumerate every consistent
 input pattern, record undet-y values per SAT model, build per-y
 Shannon trees over the orig sampling vars. Only runs when
 |orig_sampl_cnf| ≤ cadet_phase_e_threshold.

 Copyright (c) 2026, Mate Soos. All rights reserved.

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
#include "config.h"

#include <cstdint>
#include <set>
#include <vector>

namespace ArjunInt {

class Cadet {
public:
    Cadet(const ArjunInt::Config& _conf,
          const ArjunNS::Arjun::ManthanConf& _mconf,
          ArjunNS::SimplifiedCNF&& _cnf);

    ArjunNS::SimplifiedCNF do_cadet();

private:
    const ArjunInt::Config& conf;
    const ArjunNS::Arjun::ManthanConf& mconf;
    ArjunNS::SimplifiedCNF cnf;

    // `input` includes extend-defined vars; `orig_sampl_cnf` is the
    // narrower set we actually enumerate over.
    std::set<uint32_t> input;
    std::set<uint32_t> to_define;
    std::set<uint32_t> backward_defined;
    std::set<uint32_t> orig_sampl_cnf;

    std::vector<ArjunNS::aig_ptr> skol;

    void synth_complete_with_models();

    // Shannon decomposition over sorted_inputs; collapses identical
    // sibling subtrees via AIG::new_ite folding.
    ArjunNS::aig_ptr build_shannon_tree(const std::vector<bool>& table,
                                        const std::vector<uint32_t>& sorted_inputs);

    template<typename S>
    void inject_cnf(S& s) const;

    void commit_definitions();
};

} // namespace ArjunInt
