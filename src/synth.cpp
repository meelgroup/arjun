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
    {"bias_samples",             {PT::UInt,   [](MC& c, const string& v) { c.bias_samples             = parse_val<uint32_t>(v); }}},
    {"const_vote_samples",       {PT::UInt,   [](MC& c, const string& v) { c.const_vote_samples       = parse_val<uint32_t>(v); }}},
    {"stats_every",              {PT::UInt,   [](MC& c, const string& v) { c.stats_every              = parse_val<uint32_t>(v); }}},
    {"detailed_stats_every",     {PT::UInt,   [](MC& c, const string& v) { c.detailed_stats_every     = parse_val<uint32_t>(v); }}},
    {"rebuild_min_loops",        {PT::UInt,   [](MC& c, const string& v) { c.rebuild_min_loops        = parse_val<uint32_t>(v); }}},
    {"rebuild_min_clauses",      {PT::UInt,   [](MC& c, const string& v) { c.rebuild_min_clauses      = parse_val<uint32_t>(v); }}},
    {"rebuild_growth_num",       {PT::UInt,   [](MC& c, const string& v) { c.rebuild_growth_num       = parse_val<uint32_t>(v); }}},
    {"rebuild_growth_den",       {PT::UInt,   [](MC& c, const string& v) { c.rebuild_growth_den       = parse_val<uint32_t>(v); }}},
    {"reduce_cex_gen_ok",        {PT::UInt,   [](MC& c, const string& v) { c.reduce_cex_gen_ok        = parse_val<uint32_t>(v); }}},
    {"reduce_cex_tot_rep",       {PT::UInt,   [](MC& c, const string& v) { c.reduce_cex_tot_rep       = parse_val<uint32_t>(v); }}},
    {"reduce_cex_need_rep",      {PT::UInt,   [](MC& c, const string& v) { c.reduce_cex_need_rep      = parse_val<uint32_t>(v); }}},
    {"reduce_cex_cz_min_rep",    {PT::UInt,   [](MC& c, const string& v) { c.reduce_cex_cz_min_rep    = parse_val<uint32_t>(v); }}},
    {"simplify_repair_every",    {PT::UInt,   [](MC& c, const string& v) { c.simplify_repair_every    = parse_val<uint32_t>(v); }}},
    {"skip_input_only_min_rep",  {PT::UInt,   [](MC& c, const string& v) { c.skip_input_only_min_rep  = parse_val<uint32_t>(v); }}},
    {"skip_input_only_ratio",    {PT::UInt,   [](MC& c, const string& v) { c.skip_input_only_ratio    = parse_val<uint32_t>(v); }}},
    {"conflict_drop_y_max",      {PT::UInt,   [](MC& c, const string& v) { c.conflict_drop_y_max      = parse_val<uint32_t>(v); }}},
    {"extra_minim_hot",          {PT::UInt,   [](MC& c, const string& v) { c.extra_minim_hot          = parse_val<uint32_t>(v); }}},
    {"extra_minim_very_hot",     {PT::UInt,   [](MC& c, const string& v) { c.extra_minim_very_hot     = parse_val<uint32_t>(v); }}},
    {"conflict_cap",             {PT::UInt,   [](MC& c, const string& v) { c.conflict_cap             = parse_val<uint32_t>(v); }}},
    {"conflict_cap_keep",        {PT::UInt,   [](MC& c, const string& v) { c.conflict_cap_keep        = parse_val<uint32_t>(v); }}},
    {"batch_minim_min",          {PT::UInt,   [](MC& c, const string& v) { c.batch_minim_min          = parse_val<uint32_t>(v); }}},
    {"minim_budget_threshold",   {PT::UInt,   [](MC& c, const string& v) { c.minim_budget_threshold   = parse_val<uint32_t>(v); }}},
    {"minim_budget_max",         {PT::UInt,   [](MC& c, const string& v) { c.minim_budget_max         = parse_val<uint32_t>(v); }}},
    {"minim_budget_mult",        {PT::UInt,   [](MC& c, const string& v) { c.minim_budget_mult        = parse_val<uint32_t>(v); }}},
    {"aig_simplify_every",       {PT::UInt,   [](MC& c, const string& v) { c.aig_simplify_every       = parse_val<uint32_t>(v); }}},
    {"td_steps",                 {PT::UInt,   [](MC& c, const string& v) { c.td_steps                 = parse_val<uint64_t>(v); }}},
    {"td_lookahead_iters",       {PT::UInt,   [](MC& c, const string& v) { c.td_lookahead_iters       = parse_val<uint32_t>(v); }}},
    {"better_ctx_remove_all",    {PT::UInt,   [](MC& c, const string& v) { c.better_ctx_remove_all    = parse_val<uint32_t>(v); }}},
    {"td_max_edges",             {PT::UInt,   [](MC& c, const string& v) { c.td_max_edges             = parse_val<uint32_t>(v); }}},
    {"do_td_contract",           {PT::Int,    [](MC& c, const string& v) { c.do_td_contract           = parse_val<int>(v); }}},
    {"ccnr_mems_per_sample",     {PT::UInt,   [](MC& c, const string& v) { c.ccnr_mems_per_sample     = parse_val<uint64_t>(v); }}},
    {"ccnr_per_call_limit",      {PT::UInt,   [](MC& c, const string& v) { c.ccnr_per_call_limit      = parse_val<uint32_t>(v); }}},
    {"bias_w_high",              {PT::Double, [](MC& c, const string& v) { c.bias_w_high              = parse_val<double>(v); }}},
    {"bias_p_low",               {PT::Double, [](MC& c, const string& v) { c.bias_p_low               = parse_val<double>(v); }}},
    {"bias_p_high",              {PT::Double, [](MC& c, const string& v) { c.bias_p_high              = parse_val<double>(v); }}},
    {"reduce_cex_gen_ratio_num", {PT::UInt,   [](MC& c, const string& v) { c.reduce_cex_gen_ratio_num = parse_val<uint32_t>(v); }}},
    {"reduce_cex_gen_ratio_den", {PT::UInt,   [](MC& c, const string& v) { c.reduce_cex_gen_ratio_den = parse_val<uint32_t>(v); }}},
    {"cz_high_ratio",            {PT::UInt,   [](MC& c, const string& v) { c.cz_high_ratio            = parse_val<uint32_t>(v); }}},
    {"cz_low_ratio",             {PT::UInt,   [](MC& c, const string& v) { c.cz_low_ratio             = parse_val<uint32_t>(v); }}},
    {"cz_threshold_high",        {PT::UInt,   [](MC& c, const string& v) { c.cz_threshold_high        = parse_val<uint32_t>(v); }}},
    {"cz_threshold_mid",         {PT::UInt,   [](MC& c, const string& v) { c.cz_threshold_mid         = parse_val<uint32_t>(v); }}},
    {"cz_threshold_low",         {PT::UInt,   [](MC& c, const string& v) { c.cz_threshold_low         = parse_val<uint32_t>(v); }}},
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
        if (rparen != s.size() - 1) {
            cout << "ERROR: unexpected characters after ')' in strategy: " << raw << endl;
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
    if (!strategies.empty() && strategies.back().overrides.count("max_repairs") != 0) {
        cout << "ERROR: the last strategy (" << strategies.back().raw
             << ") must not set max_repairs (it must always run to completion)" << endl;
        exit(EXIT_FAILURE);
    }
    if (cnf.synth_done()) return;
    bool prev_hit_max_repairs = false;
    for (size_t i = 0; i < strategies.size(); i++) {
        const auto& strat = strategies[i];
        const bool is_last = (i == strategies.size() - 1);

        auto mconf = apply_strategy(mconf_orig, strat);
        if (is_last && strat.overrides.count("max_repairs") == 0)
            mconf.max_repairs = std::numeric_limits<uint32_t>::max();

        // If the previous non-final strategy hit max_repairs without finishing,
        // reduce the budget for subsequent non-final strategies to avoid wasting
        // time on strategies that are unlikely to help this instance.
        if (!is_last && prev_hit_max_repairs) {
            auto orig = mconf.max_repairs;
            mconf.max_repairs = std::max(50u, orig / 4);
            verb_print(1, "[synth] Reducing max_repairs " << orig << " -> " << mconf.max_repairs
                    << " (previous strategy hit limit without finishing)");
        }

        verb_print(1, "Running Manthan strategy " << i+1 << "/" << strategies.size()
            << " -- " << strat.raw << " with max_repairs="
            << (mconf.max_repairs == std::numeric_limits<uint32_t>::max() ? std::string("unlimited") : std::to_string(mconf.max_repairs)));
        cnf = arjun->standalone_manthan(std::move(cnf), mconf);
        if (cnf.synth_done()) {
            verb_print(1,"Manthan finished with strategy " << i+1 << "/" << strategies.size()
                    << " -- " << strat.raw);
            break;
        }
        // A non-final strategy that didn't finish likely hit max_repairs
        if (!is_last) prev_hit_max_repairs = true;
    }
}
