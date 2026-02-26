/*
 Arjun

 Copyright (c) 2019-2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#include <string>
#include <vector>
#include <map>
#include <cstdint>
#include "arjun.h"
#include "config.h"

struct SynthStrategy {
    std::string type;   // "learn" or "bve"
    std::string raw;    // original strategy string as parsed
    std::map<std::string, std::string> overrides; // param name -> string value
};

class SynthRunner {
public:
    enum class ParamType { UInt, Int, Double };

    SynthRunner(const ArjunInt::Config& conf, std::unique_ptr<ArjunNS::Arjun>& arjun);

    // Parse a comma-separated strategy string, e.g.:
    //   "learn(samples=1,max_repairs=4), learn(max_repairs=20), bve"
    // The last strategy always runs with unlimited tries.
    std::vector<SynthStrategy> parse_mstrategy(const std::string& s);

    // Run strategies in sequence on cnf. Skips finished strategies if cnf.synth_done().
    // Each non-last strategy runs for 20*max_repairs tries; the last runs unlimited.
    void run_manthan_strategies(
        ArjunNS::SimplifiedCNF& cnf,
        const ArjunNS::Arjun::ManthanConf& mconf_orig,
        const std::vector<SynthStrategy>& strategies);

private:
    const ArjunInt::Config& conf;
    std::unique_ptr<ArjunNS::Arjun>& arjun;

    static std::string trim(const std::string& s);
    static std::vector<std::string> split_top_level(const std::string& s);
    static bool validate_param_value(ParamType type, const std::string& v);
    SynthStrategy parse_one_strategy(const std::string& raw);
    ArjunNS::Arjun::ManthanConf apply_strategy(
        const ArjunNS::Arjun::ManthanConf& base,
        const SynthStrategy& strat);
};
