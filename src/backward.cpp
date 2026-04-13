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

#include "constants.h"
#include "minimize.h"
#include "interpolant.h"
#include "time_mem.h"
#include <random>
#include <algorithm>
#include <cstdint>
#include <optional>
#include <set>
#include <numeric>
#include <functional>

using namespace ArjunInt;
using namespace CMSat;
using namespace ArjunNS;
using std::vector;
using std::set;
using std::string;
using std::cout;
using std::endl;
using std::optional;
using std::setw;

namespace {
using VarFeats = Minimize::VarFeats;

// Print quartile statistics about an ordering's per-variable score and
// (optionally) report which quartile each var ended up in (indep vs not).
static void print_score_quartiles(const string& name, const vector<double>& scores,
        const vector<uint32_t>& order) {
    if (order.empty()) return;
    vector<double> s; s.reserve(order.size());
    for (auto v : order) s.push_back(scores[v]);
    std::sort(s.begin(), s.end());
    auto q = [&](double frac) { return s[(size_t)(frac * (s.size()-1))]; };
    cout << "c o [bw-order:" << name << "] N=" << order.size()
         << " min=" << s.front()
         << " q25=" << q(0.25)
         << " med=" << q(0.5)
         << " q75=" << q(0.75)
         << " max=" << s.back()
         << " mean=" << (std::accumulate(s.begin(), s.end(), 0.0) / s.size())
         << endl;
}

// Rank vars by `score`: HIGHER score => place at FRONT of `unknown` (so it is
// tested LAST, i.e. ends up in independent set). LOWER score => placed at
// BACK and tested first (i.e. is the first candidate to be removed/defined).
// Tie-break: lower var id at front (deterministic, mimics existing tiebreaker).
static void apply_score_order(vector<uint32_t>& unknown, const vector<double>& score) {
    std::sort(unknown.begin(), unknown.end(), [&](uint32_t a, uint32_t b) {
        if (score[a] != score[b]) return score[a] > score[b];
        return a < b;
    });
}

// Compute a per-variable score from a chosen strategy id, then sort.
static const char* order_name(int id) {
    switch(id) {
        case 0: return "min(p,n)-desc";
        case 1: return "sum-desc";
        case 2: return "max(p,n)-desc";
        case 3: return "min(p,n)-asc";
        case 4: return "sum-asc";
        case 5: return "balance+min";
        case 6: return "binary-desc";
        case 7: return "invsz-desc";
        case 8: return "longcls-desc";
        case 9: return "p*n-desc";
        case 10: return "random";
        case 11: return "neighbors-desc";
        case 12: return "min-desc + bin tiebreak";
        case 13: return "log(min)-then-bin";
        case 14: return "min-desc + sum-tiebreak";
        case 15: return "min-desc + invsz-tiebreak";
        case 16: return "weighted(min,invsz,bin)";
        case 17: return "log(min)-then-sum";
        case 18: return "min-desc + p*n-tiebreak";
        case 19: return "sqrt(p*n)-desc";
        case 20: return "min/(longcls+1)-desc";
        default: return "unknown";
    }
}

static vector<double> compute_score(int id, const vector<VarFeats>& f, uint32_t seed) {
    const uint32_t N = f.size();
    vector<double> s(N, 0.0);
    std::mt19937_64 rng(seed);
    // Precompute maxes for normalization-based combos.
    double max_min = 1, max_sum = 1, max_inv = 1, max_bin = 1, max_long = 1;
    for (uint32_t v = 0; v < N; v++) {
        max_min  = std::max(max_min, (double)f[v].mn());
        max_sum  = std::max(max_sum, (double)f[v].sum());
        max_inv  = std::max(max_inv, f[v].inv_sz_sum);
        max_bin  = std::max(max_bin, (double)f[v].bin);
        max_long = std::max(max_long, (double)f[v].longcls);
    }
    for (uint32_t v = 0; v < N; v++) {
        const auto& x = f[v];
        switch (id) {
            case 0: s[v] = (double)x.mn(); break;
            case 1: s[v] = (double)x.sum(); break;
            case 2: s[v] = (double)x.mx(); break;
            case 3: s[v] = -(double)x.mn(); break;
            case 4: s[v] = -(double)x.sum(); break;
            // balance+min: prefer balanced & high-incidence at front
            case 5: s[v] = (double)x.mn() - 0.25 * (double)x.bal(); break;
            case 6: s[v] = (double)x.bin; break;
            case 7: s[v] = x.inv_sz_sum; break;
            case 8: s[v] = (double)x.longcls; break;
            case 9: s[v] = (double)x.pos * (double)x.neg; break;
            case 10: s[v] = (double)(rng() & 0xffffffu); break;
            case 11: s[v] = (double)x.neighbors; break;
            // min(p,n) primary, binary count secondary (small linear weight)
            case 12: s[v] = (double)x.mn() * 1000.0 + (double)x.bin; break;
            // log-binned min, ties broken by binary count
            case 13: {
                double lm = x.mn() > 0 ? std::log2((double)x.mn()) : 0.0;
                s[v] = std::floor(lm) * 1e6 + (double)x.bin;
                break;
            }
            // min(p,n) primary, sum() tiebreak (when many vars share min)
            case 14: s[v] = (double)x.mn() * 1e6 + (double)x.sum(); break;
            // min(p,n) primary, inv_sz_sum tiebreak
            case 15: s[v] = (double)x.mn() * 1e6 + x.inv_sz_sum * 1e3; break;
            // weighted normalized combination
            case 16: s[v] = 0.5 * (double)x.mn()/max_min
                          + 0.3 * x.inv_sz_sum/max_inv
                          + 0.2 * (double)x.bin/max_bin; break;
            // log-binned min, sum tiebreak
            case 17: {
                double lm = x.mn() > 0 ? std::log2((double)x.mn()) : 0.0;
                s[v] = std::floor(lm) * 1e9 + (double)x.sum();
                break;
            }
            // min(p,n) primary, p*n tiebreak
            case 18: s[v] = (double)x.mn() * 1e9 + (double)x.pos*(double)x.neg; break;
            // sqrt(p*n) — geometric mean of pos/neg, like a soft min
            case 19: s[v] = std::sqrt((double)x.pos * (double)x.neg); break;
            // min divided by long-clause count: prefer balanced AND constrained
            case 20: s[v] = (double)x.mn() / ((double)x.longcls + 1.0); break;
            default: s[v] = (double)x.mn();
        }
    }
    return s;
}

} // namespace

template<typename T>
void Minimize::fill_assumptions_backward(
    vector<Lit>& assumptions,
    vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const T& indep,
    const optional<set<uint32_t>>& ignore)
{
    verb_print(5, "Filling assumps BEGIN");
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);
        if (ignore && ignore->count(var)) {
            verb_print(5, "Skipping indep var: " << var+1);
            continue;
        }

        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);
        assumptions.push_back(Lit(indic, false));
        verb_print(5, "Filled assump with indep: " << var+1);
    }

    //Add unknown as assumptions, clean "unknown"
    uint32_t j = 0;
    for(uint32_t i = 0; i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        if (unknown_set[var] == 0) continue;
        else unknown[j++] = var;
        verb_print(5, "Filled assump with unknown: " << var+1);

        assert(var < orig_num_vars);
        uint32_t indic = var_to_indic[var];
        assert(indic != var_Undef);
        assumptions.push_back(Lit(indic, false));
    }
    unknown.resize(j);
    verb_print(5, "Filling assumps END, total assumps size: " << assumptions.size());
}

void Minimize::order_by_file(const string& fname, vector<uint32_t>& unknown) {
    std::set<uint32_t> old_unknown(unknown.begin(), unknown.end());
    unknown.clear();

    std::ifstream infile(fname);
    std::string line;
    uint32_t line_num = 1;
    while (std::getline(infile, line))
    {
        std::istringstream iss(line);
        int a;
        if (!(iss >> a)) {
            cout << "ERROR: the file '" << fname << "' contains a line we cannot parse to be a variable number" << endl;
            cout << "ERROR line number: " << line_num << std::endl;
            cout << "ERROR: lines should ONLY contain a single variable" << endl;
            exit(EXIT_FAILURE);
        }
        if (old_unknown.find(a) == old_unknown.end()) {
            cout << "WARNING: the variable " << a << " is in the order file but not in the original order." << endl;
        }
        unknown.push_back(a);
        line_num++;
    }
}

void Minimize::print_sorted_unknown(const vector<uint32_t>& unknown) const {
    if (conf.verb >= 4) {
        cout << "c o Sorted output: "<< endl;
        for (const auto& v: unknown) {
            cout << "c o var: " << v+1 << " occ: " << incidence[v]
            //<< " prop-inc: " << std::setw(6) << incidence_probing[v]
            << endl;
        }
    }
}

void Minimize::backward_round() {
    SLOW_DEBUG_DO( for(const auto& x: seen) assert(x == 0));
    double start_round_time = cpuTime();
    //start with empty independent set
    vector<uint32_t> indep;

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    vector<char> unknown_set(orig_num_vars, 0);
    for(const auto& x: sampling_vars) {
        assert(x < orig_num_vars);
        assert(unknown_set[x] == 0 && "No var should be in 'sampling_vars' twice!");
        unknown.push_back(x);
        unknown_set[x] = 1;
    }
    // Use richer per-variable features computed at get_incidence() time
    // (BEFORE problem duplication, so describing the original CNF only).
    const vector<VarFeats>& feats = var_feats;
    assert(feats.size() == orig_num_vars && "var_feats must be filled by get_incidence()");
    vector<double> score = compute_score(conf.backw_order, feats, conf.seed);
    apply_score_order(unknown, score);
    if (!conf.specified_order_fname.empty()) order_by_file(conf.specified_order_fname, unknown);
    print_sorted_unknown(unknown);
    verb_print(1, "[backward FAST] order=" << conf.backw_order << " (" << order_name(conf.backw_order)
            << ") Start unknown size: " << unknown.size());

    if (conf.backw_order_stats) {
        // Stats over the *unknown* set only.
        vector<uint32_t> all = unknown;
        vector<double> mn(orig_num_vars, 0), sum_s(orig_num_vars, 0),
                       binc(orig_num_vars, 0), invs(orig_num_vars, 0);
        for (uint32_t v = 0; v < orig_num_vars; v++) {
            mn[v] = feats[v].mn();
            sum_s[v] = feats[v].sum();
            binc[v] = feats[v].bin;
            invs[v] = feats[v].inv_sz_sum;
        }
        print_score_quartiles("min(p,n)", mn, all);
        print_score_quartiles("sum",      sum_s, all);
        print_score_quartiles("bin",      binc, all);
        print_score_quartiles("invsz",    invs, all);
    }
    // Snapshot of vars eligible at start of round, for end-of-round breakdown.
    vector<uint32_t> initial_unknown = unknown;
    solver->set_verbosity(0);

    vector<Lit> assumptions;
    uint32_t iter = 0;
    uint32_t not_indep = 0;
    double my_time = cpuTime();

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_vars.size()) > 20 ) {
        uint32_t will_do_iters = sampling_vars.size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    bool quick_pop_ok = false;
    uint32_t fast_backw_calls = 0;
    uint32_t fast_backw_max = 0;
    uint32_t fast_backw_tot = 0;
    uint32_t indic_var = var_Undef;
    vector<uint32_t> non_indep_vars;
    while(true) {
        uint32_t test_var = var_Undef;
        if (quick_pop_ok) {
            //Remove 2 last
            assumptions.pop_back();
            assumptions.pop_back();

            //No more left, try again with full
            if (assumptions.empty()) {
                verb_print(5, "[arjun] No more left, try again with full");
                break;
            }

            indic_var = assumptions[assumptions.size()-1].var();
            assumptions.pop_back();
            assert(indic_var < indic_to_var.size());
            test_var = indic_to_var[indic_var];
            assert(test_var != var_Undef);
            assert(test_var < orig_num_vars);

            //something is messed up
            if (!unknown_set[test_var]) {
                quick_pop_ok = false;
                continue;
            }
            uint32_t last_unkn = unknown[unknown.size()-1];
            assert(last_unkn == test_var);
            unknown.pop_back();
        } else {
            while(!unknown.empty()) {
                uint32_t var = unknown[unknown.size()-1];
                if (unknown_set[var]) {
                    test_var = var;
                    unknown.pop_back();
                    break;
                } else {
                    unknown.pop_back();
                }
            }

            if (test_var == var_Undef) {
                //we are done, backward is finished
                verb_print(5, "[arjun] we are done, backward is finished");
                break;
            }
            indic_var = var_to_indic[test_var];
        }
        assert(test_var < orig_num_vars);
        assert(unknown_set[test_var] == 1);
        unknown_set[test_var] = 0;
        verb_print(5, "[arjun] Testing: " << test_var+1);

        //Assumption filling
        assert(test_var != var_Undef);
        if (!quick_pop_ok) {
            fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
        }
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        FastBackwData b;
        b._assumptions = &assumptions;
        b.indic_to_var  = &indic_to_var;
        b.orig_num_vars = orig_num_vars;
        b.non_indep_vars = &non_indep_vars;
        b.indep_vars = &indep;
        b.fast_backw_on = true;
        b.test_indic = &indic_var;
        b.test_var = &test_var;
        b.max_confl = conf.backw_max_confl;

        fast_backw_calls++;
        if (conf.verb > 5) {
            cout << "test var is: " << test_var << endl;
            cout << "find_fast_backw BEGIN " << endl;
        }
        non_indep_vars.clear();
        uint32_t indep_vars_last_pos = indep.size();
        ret = solver->find_fast_backw(b);

        verb_print(3, "[arjun] non_indep_vars.size(): " << non_indep_vars.size()
            << " indep.size(): " << indep.size() << " ret: " << ret << " test_var: " << test_var);
        if (ret == l_False) {
            verb_print(5, "[arjun] Problem is UNSAT");
            for(auto& x: unknown_set) x = 0;
            unknown.clear();
            indep.clear();
            assumptions.clear();
            break;
        }

        fast_backw_tot += non_indep_vars.size();
        fast_backw_max = std::max<uint32_t>(non_indep_vars.size(), fast_backw_max);
        for(uint32_t i = indep_vars_last_pos; i < indep.size(); i ++) {
            uint32_t var = indep[i];
            unknown_set[var] = 0;
        }

        for(const auto& var: non_indep_vars) {
            assert(var < orig_num_vars);
            unknown_set[var] = 0;
            not_indep++;
        }
        quick_pop_ok = false;

        //We have finished it all off
        if (test_var == var_Undef) {
            assert(indic_var == var_Undef);
            continue;
        }
        unknown_set[test_var] = 0;
        if (ret == l_False) {
            ret_false++;
            verb_print(5, "[arjun] backw solve(): False");
        } else if (ret == l_True) {
            ret_true++;
            verb_print(5, "[arjun] backw solve(): True");
        } else if (ret == l_Undef) {
            verb_print(5, "[arjun] backw solve(): Undef");
            ret_undef++;
        }

        assert(unknown_set[test_var] == 0);
        if (ret == l_Undef) {
            //Timed out, we'll treat is as unknown
            quick_pop_ok = false;
            assert(test_var < orig_num_vars);
            indep.push_back(test_var);
        } else if (ret == l_True) {
            //Independent
            quick_pop_ok = false;
            indep.push_back(test_var);
        } else if (ret == l_False) {
            //not independent
            //i.e. given that all in indep+unkown is equivalent, it's not possible that a1 != b1
            not_indep++;
            quick_pop_ok = true;
        }

        if (iter % mod == (mod-1) && conf.verb) {
            //solver->remove_and_clean_all();
            cout
            << "c [arjun] iter: " << std::setw(5) << iter;
            if (mod == 1) {
                cout
                << " ret: " << std::setw(8) << ret;
            } else {
                cout
                << " T/F/U: ";
                std::stringstream ss;
                ss << ret_true << "/" << ret_false << "/" << ret_undef;
                cout << std::setw(10) << std::left << ss.str() << std::right;
                ret_true = 0;
                ret_false = 0;
                ret_undef = 0;
            }
            cout
            << " by: " << std::setw(3) << 1
            << " U: " << std::setw(7) << unknown.size()
            << " I: " << std::setw(7) << indep.size()
            << " N: " << std::setw(7) << not_indep
            ;
            cout << " backb avg:" << std::setprecision(1) << std::setw(7)
            << (double)fast_backw_tot/(double)fast_backw_calls
            << " backb max:" << std::setw(7) << fast_backw_max;
            cout << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - my_time)
            << endl;
            my_time = cpuTime();
            fast_backw_tot = 0;
            fast_backw_calls = 0;
            fast_backw_max = 0;
        }
        iter++;

        if (iter % 500 == 499) {
            update_sampling_set(unknown, unknown_set, indep);
        }
    }
    update_sampling_set(unknown, unknown_set, indep);

    if (conf.backw_order_stats) {
        // Per-feature-quartile breakdown of "ended up indep" vs not. Computed
        // over the initial-unknown set so it tells us which features actually
        // predict membership in the final independent set.
        std::set<uint32_t> indep_set(sampling_vars.begin(), sampling_vars.end());
        auto report = [&](const string& name, std::function<double(const VarFeats&)> get) {
            vector<std::pair<double, uint32_t>> by_score;
            for (auto v : initial_unknown) by_score.emplace_back(get(feats[v]), v);
            std::sort(by_score.begin(), by_score.end());
            const uint32_t N = by_score.size();
            if (N == 0) return;
            uint32_t buckets = 4;
            cout << "c o [bw-stats:" << name << "] indep-count per quartile (low->high):";
            for (uint32_t b = 0; b < buckets; b++) {
                uint32_t lo = (uint64_t)b * N / buckets;
                uint32_t hi = (uint64_t)(b+1) * N / buckets;
                uint32_t cnt = 0;
                for (uint32_t i = lo; i < hi; i++) if (indep_set.count(by_score[i].second)) cnt++;
                cout << " " << cnt << "/" << (hi-lo);
            }
            cout << endl;
        };
        report("min(p,n)", [](const VarFeats& f){ return (double)f.mn(); });
        report("sum",      [](const VarFeats& f){ return (double)f.sum(); });
        report("bin",      [](const VarFeats& f){ return (double)f.bin; });
        report("longcls",  [](const VarFeats& f){ return (double)f.longcls; });
        report("invsz",    [](const VarFeats& f){ return f.inv_sz_sum; });
        report("balance",  [](const VarFeats& f){ return -(double)f.bal(); });
        report("p*n",      [](const VarFeats& f){ return (double)f.pos*(double)f.neg; });
    }

    verb_print(1, COLRED "[arjun] backward round finished. U: " <<
            " I: " << sampling_vars.size() << " T: "
        << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 4) solver->print_stats();
}

void Minimize::add_all_indics_except(const set<uint32_t>& except) {
    ::add_all_indics_except(*solver, orig_num_vars, except,
        var_to_indic, indic_to_var, dont_elim, seen, conf.verb);
}

void Minimize::backward_round_synth(SimplifiedCNF& cnf, const Arjun::ManthanConf& mconf) {
    SLOW_DEBUG_DO(for(const auto& x: seen) assert(x == 0));
    SLOW_DEBUG_DO(assert(cnf.get_need_aig() && cnf.defs_invariant()));

    const double start_time = cpuTime();
    fill_solver_synth(cnf);
    init();
    get_incidence();
    duplicate_problem(cnf);

    // Initially, all of opt_samping_set is known, we do NOT want to minimize those
    // Instead, all non-sampling-set vars, get definitions for them
    // in terms of ANY other variables, but NOT in a self-referential way
    vector<char> unknown_set(orig_num_vars, 0);
    vector<uint32_t> unknown;
    auto [input, to_define, backward_defined] = cnf.get_var_types(conf.verb | verbose_debug_enabled, "start backward_round_synth");
    set<uint32_t> pretend_input;
    if (to_define.empty()) {
        verb_print(1, "[backw-synth] No variables to define, returning original CNF");
        return;
    }
    assert(backward_defined.empty());

    add_all_indics_except(input);
    for(const auto& v: input) {
        vector<Lit> cl;
        cl.push_back(Lit(v, false));
        cl.push_back(Lit(v+orig_num_vars, true));
        solver->add_clause(cl);
        cl[0] = ~cl[0];
        cl[1] = ~cl[1];
        solver->add_clause(cl);
    }

    // set up interpolant
    Interpolant interp(conf, cnf.nVars());
    interp.solver = solver.get();
    interp.fill_picolsat(orig_num_vars);
    interp.fill_var_to_indic(var_to_indic);

    for(uint32_t x = 0; x < orig_num_vars; x++) {
        pretend_input.insert(x); // we pretend that all vars are input vars
        if (input.count(x)) continue;
        unknown.push_back(x);
        unknown_set[x] = 1;
    }
    sort_unknown(unknown, incidence);
    if (mconf.backward_synth_order)
        std::reverse(unknown.begin(), unknown.end());
    print_sorted_unknown(unknown);
    verb_print(1, "[backward SYNTH] Start unknown size: " << unknown.size()
                    << " mem: " << memUsedTotal()/(1024*1024) << " MB");
    solver->set_verbosity(0);

    vector<Lit> assumptions;
    uint32_t ret_true = 0;
    uint32_t ret_false = 0;
    uint32_t ret_undef = 0;
    while(true) {
        uint32_t num_done = ret_true + ret_false + ret_undef;
        if (num_done % 100 == 99) {
            verb_print(1, "[backw-synth] done: " << setw(4) << num_done
                    << " unsat: " << setw(4) << ret_false
                    << " left: " << setw(4) << unknown.size()
                    << " T: " << std::setprecision(2) << std::fixed << setw(6)
                    << (cpuTime() - start_time)
                    << " var/s: " << setw(6) << safe_div(num_done, cpuTime() - start_time)
                    << " mem: " << memUsedTotal()/(1024*1024) << " MB");
        }

        // Find a variable to test
        uint32_t test_var = var_Undef;
        while(!unknown.empty()) {
            uint32_t var = unknown.back();
            if (unknown_set[var]) {
                test_var = var;
                unknown.pop_back();
                break;
            } else {
                unknown.pop_back();
            }
        }

        if (test_var == var_Undef) {
            //we are done, backward is finished
            verb_print(5, "[backw-synth] we are done, " << __PRETTY_FUNCTION__ << " is finished");
            break;
        }
        assert(test_var < orig_num_vars);
        assert(!input.count(test_var));
        assert(unknown_set[test_var]);
        unknown_set[test_var] = 0;
        pretend_input.erase(test_var);
        verb_print(3, "Testing: " << test_var+1);

        //Assumption filling
        assert(test_var != var_Undef);
        fill_assumptions_backward(assumptions, unknown, unknown_set, pretend_input, input);
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));
        solver->set_no_confl_needed();
        const uint32_t indic = var_to_indic[test_var];

        // See if it can be defined by anything
        lbool ret = l_Undef;
        solver->set_max_confl(conf.backw_max_confl);
        ret = solver->solve(&assumptions);

        if (ret == l_False) {
            ret_false++;
            verb_print(3, "[backw-synth] " << __PRETTY_FUNCTION__ << " solve(): False");
        } else if (ret == l_True) {
            ret_true++;
            verb_print(3, "[backw-synth] " << __PRETTY_FUNCTION__ << " solve(): True");
        } else if (ret == l_Undef) {
            verb_print(3, "[backw-synth] " << __PRETTY_FUNCTION__ << " solve(): Undef");
            ret_undef++;
        }

        assert(unknown_set[test_var] == 0);
        if (ret == l_Undef) {
            //Timed out, we'll treat is as unknown
            assert(test_var < orig_num_vars);
            pretend_input.insert(test_var);
            solver->add_clause({Lit(indic, false)});
            interp.add_unit_cl({Lit(indic, false)});
        } else if (ret == l_True) {
            //Independent
            pretend_input.insert(test_var);
            solver->add_clause({Lit(indic, false)});
            interp.add_unit_cl({Lit(indic, false)});
        } else if (ret == l_False) {
            //not independent
            //i.e. given that all in indep+unkown is equivalent, it's not possible that a1 != b1
            interp.generate_interpolant(assumptions, test_var, cnf, pretend_input);
        }
    }
    verb_print(3, __PRETTY_FUNCTION__ << " pretend_input size: " << pretend_input.size());

    if (conf.verb >= 1) {
        solver->print_stats();
        for(uint32_t v = 0; v < interp.get_defs().size(); v++) {
            auto& aig = interp.get_defs()[v];
            if (aig == nullptr) continue;

            set<uint32_t> dep_vars;
            AIG::get_dependent_vars(aig, dep_vars, v);
            vector<Lit> deps_lits; deps_lits.reserve(dep_vars.size());
            for(const auto& dv: dep_vars) deps_lits.push_back(Lit(dv, false));
            verb_print(2, "[backw-synth] var: " << v+1 << " depends on vars: " << deps_lits); // << " aig: " << aig);
        }
    }

    for(uint32_t v = 0; v < cnf.nVars(); v++) {
        const auto& aig = interp.get_defs()[v];
        if (aig == nullptr) continue;
        assert(input.count(v) == 0);
    }
    cnf.map_aigs_to_orig(interp.get_defs(), orig_num_vars);
    cnf.set_after_backward_round_synth();
    auto [input2, to_define2, backward_defined2] = cnf.get_var_types(0 | verbose_debug_enabled, "end backward_round_synth");

    verb_print(1, COLRED "[backward SYNTH] Done. "
        << " TR: " << ret_true << " UN: " << ret_undef << " FA: " << ret_false
        << " defined: " << to_define.size()-to_define2.size()
        << " still to define: " << to_define2.size()
        << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_time)
        << " mem: " << memUsedTotal()/(1024*1024) << " MB");
    SLOW_DEBUG_DO(assert(cnf.get_need_aig() && cnf.defs_invariant()));
}
