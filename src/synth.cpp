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

#include "synth.h"

#include <charconv>
#include <functional>
#include <iostream>
#include <limits>
#include <string>
#include "constants.h"

using std::string;
using std::vector;
using std::cout;
using std::endl;

namespace {
using MC = ArjunNS::Arjun::ManthanConf;

template<typename T> T parse_val(const string& s) {
    T v{}; std::from_chars(s.data(), s.data() + s.size(), v); return v;
}
template<> double parse_val<double>(const string& s) {
    return std::stod(s);
}

template<typename T> bool validate_val(const string& v) {
    T x; auto [p,e] = std::from_chars(v.data(), v.data()+v.size(), x);
    return e == std::errc{} && p == v.data()+v.size();
}
template<> bool validate_val<double>(const string& v) {
    try { size_t pos; std::stod(v, &pos); return pos == v.size(); }
    catch (...) { return false; }
}

using PT = SynthRunner::ParamType;
struct ParamDef { PT type; std::function<void(MC&, const string&)> setter; };

const std::map<string, ParamDef> param_table = {
    {"max_repairs",              {PT::UInt,   [](MC& c, const string& v) { c.max_repairs              = parse_val<uint32_t>(v); }}},
    {"samples",                  {PT::UInt,   [](MC& c, const string& v) { c.samples                  = parse_val<uint32_t>(v); }}},
    {"samples_ccnr",             {PT::UInt,   [](MC& c, const string& v) { c.samples_ccnr             = parse_val<uint32_t>(v); }}},
    {"min_gain_split",           {PT::Double, [](MC& c, const string& v) { c.min_gain_split           = parse_val<double>(v); }}},
    {"max_depth",                {PT::UInt,   [](MC& c, const string& v) { c.max_depth                = parse_val<uint32_t>(v); }}},
    {"sampler_fixed_conflicts",  {PT::UInt,   [](MC& c, const string& v) { c.sampler_fixed_conflicts  = parse_val<uint32_t>(v); }}},
    {"min_leaf_size",            {PT::UInt,   [](MC& c, const string& v) { c.min_leaf_size            = parse_val<uint32_t>(v); }}},
    {"filter_samples",           {PT::Int,    [](MC& c, const string& v) { c.filter_samples           = parse_val<int>(v); }}},
    {"biased_sampling",          {PT::Int,    [](MC& c, const string& v) { c.biased_sampling          = parse_val<int>(v); }}},
    {"minimize_conflict",        {PT::Int,    [](MC& c, const string& v) { c.minimize_conflict        = parse_val<int>(v); }}},
    {"simplify_every",           {PT::UInt,   [](MC& c, const string& v) { c.simplify_every           = parse_val<uint32_t>(v); }}},
    {"maxsat_better_ctx",        {PT::Int,    [](MC& c, const string& v) { c.maxsat_better_ctx        = parse_val<int>(v); }}},
    {"maxsat_order",             {PT::Int,    [](MC& c, const string& v) { c.maxsat_order             = parse_val<int>(v); }}},
    {"use_all_vars_as_feats",    {PT::Int,    [](MC& c, const string& v) { c.use_all_vars_as_feats    = parse_val<int>(v); }}},
    {"ctx_solver_type",          {PT::Int,    [](MC& c, const string& v) { c.ctx_solver_type          = parse_val<int>(v); }}},
    {"repair_solver_type",       {PT::Int,    [](MC& c, const string& v) { c.repair_solver_type       = parse_val<int>(v); }}},
    {"repair_cache_size",        {PT::Int,    [](MC& c, const string& v) { c.repair_cache_size        = parse_val<int>(v); }}},
    {"backward_synth_order",     {PT::Int,    [](MC& c, const string& v) { c.backward_synth_order     = parse_val<int>(v); }}},
    {"manthan_order",            {PT::Int,    [](MC& c, const string& v) { c.manthan_order            = parse_val<int>(v); }}},
    {"manthan_on_the_fly_order", {PT::Int,    [](MC& c, const string& v) { c.manthan_on_the_fly_order = parse_val<int>(v); }}},
    {"one_repair_per_loop",      {PT::Int,    [](MC& c, const string& v) { c.one_repair_per_loop      = parse_val<int>(v); }}},
    {"force_bw_equal",           {PT::Int,    [](MC& c, const string& v) { c.force_bw_equal           = parse_val<int>(v); }}},
    {"bva_xor_vars",             {PT::Int,    [](MC& c, const string& v) { c.bva_xor_vars             = parse_val<int>(v); }}},
    {"silent_var_update",        {PT::Int,    [](MC& c, const string& v) { c.silent_var_update        = parse_val<int>(v); }}},
    {"inv_learnt",               {PT::Int,    [](MC& c, const string& v) { c.inv_learnt               = parse_val<int>(v); }}},
};
} // namespace

SynthRunner::SynthRunner(const ArjunInt::Config& _conf, std::unique_ptr<ArjunNS::Arjun>& _arjun) :
    conf(_conf), arjun(_arjun) {}

string SynthRunner::trim(const string& s) {
    string result;
    for (char c : s) {
        if (isalnum(c) || c == '.' || c == ',' || c == '=' || c == '(' || c == ')' || c == ' ' || c == '_')
            result += c;
        else {
            cout << "ERROR: invalid character '" << c << "' in strategy string: " << s << endl;
            exit(EXIT_FAILURE);
        }
    }
    auto start = result.find_first_not_of(' ');
    if (start == string::npos) return "";
    auto end = result.find_last_not_of(' ');
    return result.substr(start, end - start + 1);
}

// Split s by commas at parenthesis
vector<string> SynthRunner::split_top_level(const string& s) {
    vector<string> parts;
    int depth = 0;
    string current;
    for (char c : s) {
        if (c == '(') {
            depth++;
            if (depth > 1) {
                cout << "ERROR: nested parentheses are not allowed in strategy string: " << s << endl;
                exit(EXIT_FAILURE);
            }
        } else if (c == ')') {
            depth--;
            if (depth < 0) {
                cout << "ERROR: unmatched ')' in strategy string: " << s << endl;
                exit(EXIT_FAILURE);
            }
        }
        if (c == ',' && depth == 0) {
            parts.push_back(trim(current));
            current.clear();
        } else {
            current += c;
        }
    }
    if (!trim(current).empty()) parts.push_back(trim(current));
    return parts;
}

bool SynthRunner::validate_param_value(ParamType type, const string& v) {
    switch (type) {
        case ParamType::UInt:   return validate_val<uint32_t>(v);
        case ParamType::Int:    return validate_val<int>(v);
        case ParamType::Double: return validate_val<double>(v);
    }
    return false;
}

SynthStrategy SynthRunner::parse_one_strategy(const string& raw) {
    SynthStrategy strat;
    string s = trim(raw);
    strat.raw = s;

    auto paren_pos = s.find('(');
    if (paren_pos == string::npos) {
        strat.type = s;
    } else {
        strat.type = trim(s.substr(0, paren_pos));
        auto rparen = s.rfind(')');
        if (rparen == string::npos) {
            cout << "ERROR: missing closing ')' in strategy: " << raw << endl;
            exit(EXIT_FAILURE);
        }
        string params_str = s.substr(paren_pos + 1, rparen - paren_pos - 1);
        for (const auto& param : split_top_level(params_str)) {
            if (param.empty()) continue;
            auto eq = param.find('=');
            if (eq == string::npos) {
                cout << "ERROR: missing '=' in strategy param: " << param << endl;
                exit(EXIT_FAILURE);
            }
            string k = trim(param.substr(0, eq));
            string v = trim(param.substr(eq + 1));

            auto it = param_table.find(k);
            if (it == param_table.end()) {
                cout << "ERROR: unknown strategy parameter '" << k << "'" << endl;
                exit(EXIT_FAILURE);
            }

            if (!validate_param_value(it->second.type, v)) {
                cout << "ERROR: cannot parse value '" << v
                     << "' for parameter '" << k << "'" << endl;
                exit(EXIT_FAILURE);
            }

            strat.overrides[k] = v;
        }
    }

    if (strat.type != "learn" && strat.type != "bve" && strat.type != "const") {
        cout << "ERROR: unknown strategy type '" << strat.type << "'. Use 'learn', 'bve', or 'const'." << endl;
        exit(EXIT_FAILURE);
    }
    return strat;
}

vector<SynthStrategy> SynthRunner::parse_mstrategy(const string& s) {
    vector<SynthStrategy> strategies;
    for (const auto& tok : split_top_level(s)) {
        if (!tok.empty()) strategies.push_back(parse_one_strategy(tok));
    }
    if (strategies.empty()) {
        cout << "ERROR: --mstrategy string is empty" << endl;
        exit(EXIT_FAILURE);
    }
    return strategies;
}

ArjunNS::Arjun::ManthanConf SynthRunner::apply_strategy(const ArjunNS::Arjun::ManthanConf& base,
        const SynthStrategy& strat) {
    auto mconf = base;
    if (strat.type == "learn") {
#ifndef EXTRA_SYNTH
        cout << "ERROR: strategy type 'learn' is only supported in EXTRA_SYNTH mode!" << endl;
        exit(EXIT_FAILURE);
#endif
        mconf.manthan_base = 0;
    } else if (strat.type == "const") {
        mconf.manthan_base = 1;
    } else if (strat.type == "bve") {
        mconf.manthan_base = 2;
    } else {
        cout << "ERROR: unknown strategy type '" << strat.type << "'" << endl;
        exit(EXIT_FAILURE);
    }

    for (const auto& [k, v] : strat.overrides)
        param_table.at(k).setter(mconf, v);
    return mconf;
}

void SynthRunner::run_manthan_strategies(
        ArjunNS::SimplifiedCNF& cnf,
        const ArjunNS::Arjun::ManthanConf& mconf_orig,
        const vector<SynthStrategy>& strategies)
{
    if (strategies.empty()) {
        cout << "ERROR: no strategies to run" << endl;
        exit(EXIT_FAILURE);
    }
    for (size_t i = 0; i + 1 < strategies.size(); i++) {
        if (strategies[i].overrides.count("max_repairs") == 0) {
            cout << "ERROR: strategy " << i+1 << " (" << strategies[i].raw
                 << ") must set max_repairs (only the last strategy may omit it)" << endl;
            exit(EXIT_FAILURE);
        }
    }
    if (cnf.synth_done()) return;
    for (size_t i = 0; i < strategies.size(); i++) {
        const auto& strat = strategies[i];
        const bool is_last = (i == strategies.size() - 1);

        auto mconf = apply_strategy(mconf_orig, strat);
        if (is_last && strat.overrides.count("max_repairs") == 0)
            mconf.max_repairs = std::numeric_limits<uint32_t>::max();

        verb_print(1, "Running Manthan strategy " << i+1 << "/" << strategies.size()
            << " -- " << strat.raw << " with max_repairs="
            << (mconf.max_repairs == std::numeric_limits<uint32_t>::max() ? std::string("unlimited") : std::to_string(mconf.max_repairs)));
        cnf = arjun->standalone_manthan(cnf, mconf);
        if (cnf.synth_done()) {
            verb_print(1,"Manthan finished with strategy " << i+1 << "/" << strategies.size()
                    << " -- " << strat.raw);
            break;
        }
    }
}
