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
#include <oracle/oracle.h>
#include <algorithm>
#include <cstdint>
#include <optional>
#include <set>

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

static inline sspp::Lit cms_to_sspp(const Lit& l) {
    return l.sign() ? ((l.var()+1)*2+1) : ((l.var()+1)*2);
}

void Minimize::backward_round_slow() {
    SLOW_DEBUG_DO( for(const auto& x: seen) assert(x == 0));
    double start_round_time = cpuTime();

    // Build oracle from the CMS solver's current clauses. The oracle uses
    // 1-indexed vars internally, so cms var V maps to oracle var V+1.
    // We pass BOTH irredundant and redundant (learned) clauses so the
    // oracle starts with all the learning CMS has accumulated during
    // simplification — matches what the FAST path benefits from.
    vector<vector<sspp::Lit>> ocls;
    vector<vector<sspp::Lit>> ored;
    {
        vector<Lit> cl;
        bool is_xor, rhs;
        solver->start_getting_constraints(false);  // irred
        while(solver->get_next_constraint(cl, is_xor, rhs)) {
            assert(!is_xor); assert(rhs);
            vector<sspp::Lit> ocl;
            ocl.reserve(cl.size());
            for(const auto& l: cl) ocl.push_back(cms_to_sspp(l));
            ocls.push_back(std::move(ocl));
        }
        solver->end_getting_constraints();
        // Learned clauses with low glue are reusable — pull them in too.
        // Higher glue clauses tend not to survive the oracle's reduction
        // anyway and add to import time. Cap glue at 4 for the seed.
        solver->start_getting_constraints(true /*red*/, false,
                std::numeric_limits<uint32_t>::max() /*max len*/,
                4 /*max glue*/);
        while(solver->get_next_constraint(cl, is_xor, rhs)) {
            if (is_xor) continue;
            vector<sspp::Lit> ocl;
            ocl.reserve(cl.size());
            for(const auto& l: cl) ocl.push_back(cms_to_sspp(l));
            ored.push_back(std::move(ocl));
        }
        solver->end_getting_constraints();
    }
    // Count unique vars in the imported clauses to measure space waste.
    {
        std::vector<char> seen_var(solver->nVars() + 2, 0);
        int used = 0;
        for (const auto& cl : ocls) for (auto l : cl) {
            int v = l / 2;
            if (v > 0 && v <= (int)solver->nVars() && !seen_var[v]) {
                seen_var[v] = 1; used++;
            }
        }
        for (const auto& cl : ored) for (auto l : cl) {
            int v = l / 2;
            if (v > 0 && v <= (int)solver->nVars() && !seen_var[v]) {
                seen_var[v] = 1; used++;
            }
        }
        verb_print(1, "[backward SLOW] Oracle vars: " << solver->nVars()
                << " allocated, " << used << " used in clauses ("
                << (100*used/std::max((uint32_t)1,solver->nVars())) << "%)"
                << " irred_cls: " << ocls.size()
                << " red_cls: " << ored.size());
    }
    sspp::oracle::Oracle oracle(solver->nVars(), ocls, ored);
    oracle.SetVerbosity(conf.verb >= 2 ? 2 : 0);

    // Opt-in bounded variable elimination. Gated by --slowbve because
    // BVE is destructive and only safe for variables the caller is
    // sure will never appear in the independent support.
    //
    // Eliminable set = variables NOT in sampling_vars and NOT their
    // duals (sampling_vars[i] + orig_num_vars) and NOT the indicator
    // vars. These are internal formula vars (Tseitin helpers etc.) —
    // arjun's independence test never queries them directly.
    if (conf.slow_bve) {
        std::vector<bool> eliminable(solver->nVars() + 2, false);
        std::vector<char> in_sampling(orig_num_vars, 0);
        for (uint32_t v : sampling_vars) in_sampling[v] = 1;
        for (uint32_t v = 0; v < orig_num_vars; v++) {
            if (in_sampling[v]) continue;
            // Oracle uses 1-indexed vars.
            eliminable[v + 1] = true;                    // primary copy
            eliminable[v + orig_num_vars + 1] = true;    // dual copy
        }
        // Explicitly forbid eliminating indicator vars (which live
        // above 2*orig_num_vars). We only flagged below 2*orig_num_vars
        // so those remain false by construction.
        double bve_start = cpuTime();
        int elim = oracle.BVE(eliminable, conf.slow_bve_grow, 1000LL*1000LL*1000LL);
        verb_print(1, "[backward SLOW] BVE eliminated " << elim
                << " vars T: " << std::setprecision(2) << std::fixed
                << (cpuTime() - bve_start));

        // After BVE, run SCC to find new equivalences exposed by
        // the resolution. Protected mask: all sampling indicators
        // + all sampling vars + duals must NOT be replaced.
        {
            std::vector<bool> scc_prot(solver->nVars() + 2, false);
            for (uint32_t v : sampling_vars) {
                if (v >= orig_num_vars) continue;
                uint32_t indic = var_to_indic[v];
                if (indic != var_Undef) scc_prot[indic + 1] = true;
                scc_prot[v + 1] = true;
                scc_prot[v + orig_num_vars + 1] = true;
            }
            double scc_start = cpuTime();
            int scc_elim = oracle.SCCEquivLitElim(scc_prot);
            verb_print(1, "[backward SLOW] post-BVE SCC eliminated " << scc_elim
                    << " vars T: " << std::setprecision(2) << std::fixed
                    << (cpuTime() - scc_start));
        }
    }

    // Inprocess the seed clause database before the main solve.
    {
        double t0 = cpuTime();
        int removed = oracle.Vivify(500LL*1000LL*1000LL);
        verb_print(1, "[backward SLOW] Vivify removed " << removed
                << " lits T: " << std::setprecision(2) << std::fixed
                << (cpuTime() - t0));
    }

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    vector<char> unknown_set(orig_num_vars, 0);
    unknown.reserve(sampling_vars.size());
    for(const auto& x: sampling_vars) {
        assert(x < orig_num_vars);
        assert(unknown_set[x] == 0 && "No var should be in 'sampling_vars' twice!");
        unknown.push_back(x);
        unknown_set[x] = 1;
    }
    sort_unknown(unknown, incidence);
    if (!conf.specified_order_fname.empty()) order_by_file(conf.specified_order_fname, unknown);
    print_sorted_unknown(unknown);
    verb_print(1, "[backward SLOW] Start unknown size: " << unknown.size());

    // Pre-compute oracle Lits per CMS var:
    //  - indic_pos_sspp[v]      — positive indicator literal (for the assumption stack)
    //  - test_pos_sspp[v]       — v=TRUE  (test pair, half 1)
    //  - test_dual_neg_sspp[v]  — (v+N)=FALSE (test pair, half 2)
    vector<sspp::Lit> indic_pos_sspp(orig_num_vars, 0);
    vector<sspp::Lit> test_pos_sspp(orig_num_vars, 0);
    vector<sspp::Lit> test_dual_neg_sspp(orig_num_vars, 0);
    for (const auto& v : unknown) {
        uint32_t indic = var_to_indic[v];
        assert(indic != var_Undef);
        indic_pos_sspp[v] = cms_to_sspp(Lit(indic, false));
        test_pos_sspp[v] = cms_to_sspp(Lit(v, false));
        test_dual_neg_sspp[v] = cms_to_sspp(Lit(v + orig_num_vars, true));
    }
    // indic-var (oracle) -> caller's CMS var index. The oracle stores indic
    // var as oracle var index `indic+1` (1-based). We need a lookup from
    // *oracle var* (= indic+1) to caller var.
    vector<int> oracle_indic_to_var(solver->nVars()+2, -1);
    for (uint32_t v = 0; v < orig_num_vars; v++) {
        uint32_t indic = var_to_indic[v];
        if (indic == var_Undef) continue;
        oracle_indic_to_var[indic+1] = (int)v;  // oracle var = indic+1
    }

    // Build the initial assumption stack: all indic_pos lits, in the
    // sort_unknown order (so popping from the back tests in incidence order).
    // The first test_var is unknown.back(); we pop it from the indic stack
    // and push its test pair on top.
    vector<sspp::Lit> assumptions;
    assumptions.reserve(unknown.size() + 2);
    for (size_t i = 0; i < unknown.size(); i++) {
        const uint32_t v = unknown[i];
        // Skip the last var here — it becomes the first test_var instead of
        // an indicator decision.
        if (i + 1 == unknown.size()) break;
        assumptions.push_back(indic_pos_sspp[v]);
    }
    int initial_test_var = -1;
    int initial_test_indic = -1;
    if (!unknown.empty()) {
        initial_test_var = (int)unknown.back();
        initial_test_indic = (int)var_to_indic[initial_test_var] + 1;  // oracle 1-based
        assumptions.push_back(test_pos_sspp[initial_test_var]);
        assumptions.push_back(test_dual_neg_sspp[initial_test_var]);
    }

    vector<int> indep_oracle_vars;       // caller-side var indices
    vector<int> non_indep_oracle_vars;
    int test_var_oracle = initial_test_var;
    int test_indic_oracle = initial_test_indic;

    sspp::oracle::SlowBackwData data;
    data._assumptions = &assumptions;
    data.indic_to_var = &oracle_indic_to_var;
    data.test_pos_lit = &test_pos_sspp;
    data.test_dual_neg_lit = &test_dual_neg_sspp;
    data.indep_vars = &indep_oracle_vars;
    data.non_indep_vars = &non_indep_oracle_vars;
    data.test_indic = &test_indic_oracle;
    data.test_var = &test_var_oracle;
    data.max_confl = (int64_t)conf.backw_max_confl;

    // Single mega-call: SlowBackwSolve runs the entire backward round
    // in one persistent solve session.
    const int64_t mems_per_call = (int64_t)1000LL*1000LL*1000LL*1000LL;

    if (!unknown.empty()) {
        oracle.reset_mems();
        sspp::oracle::TriState ret = oracle.SlowBackwSolve(data, mems_per_call);
        if (ret.isFalse()) {
            verb_print(1, "[arjun] [backward SLOW] formula UNSAT, all indep set cleared");
            indep_oracle_vars.clear();
            non_indep_oracle_vars.clear();
        }

        // Anything still unclassified: treat as indep.
        {
            bool any_unclassified = false;
            for (size_t i = indep_oracle_vars.size(); i < assumptions.size(); i++) {
                const sspp::Lit ind = assumptions[i];
                if (ind <= 1) continue;
                const int oracle_var = ind / 2;
                if (oracle_var <= 0 || oracle_var >= (int)oracle_indic_to_var.size()) continue;
                const int real_var = oracle_indic_to_var[oracle_var];
                if (real_var < 0) continue;
                indep_oracle_vars.push_back(real_var);
                any_unclassified = true;
            }
        }
    }

    // Translate results back to arjun's data structures.
    vector<uint32_t> indep;
    indep.reserve(indep_oracle_vars.size());
    for (auto v : indep_oracle_vars) indep.push_back((uint32_t)v);
    for (auto v : non_indep_oracle_vars) {
        // Mark removed in unknown_set
        if ((uint32_t)v < orig_num_vars) unknown_set[v] = 0;
    }
    for (auto v : indep_oracle_vars) {
        if ((uint32_t)v < orig_num_vars) unknown_set[v] = 0;
    }

    // Compact unknown to only those still flagged
    {
        vector<uint32_t> new_unknown;
        for (auto v : unknown) {
            if (unknown_set[v]) new_unknown.push_back(v);
        }
        unknown = std::move(new_unknown);
    }

    update_sampling_set(unknown, unknown_set, indep);

    verb_print(1, COLRED "[arjun] backward round finished. U: " <<
            " I: " << sampling_vars.size() << " T: "
        << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 4) oracle.PrintStats();
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
    sort_unknown(unknown, incidence);
    /* std::reverse(unknown.begin(), unknown.end()); */
    /* std::mt19937_64 rand(33); */
    /* std::shuffle(unknown.begin(), unknown.end(), rand); */
    if (!conf.specified_order_fname.empty()) order_by_file(conf.specified_order_fname, unknown);
    print_sorted_unknown(unknown);
    verb_print(1, "[backward FAST] Start unknown size: " << unknown.size());
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
