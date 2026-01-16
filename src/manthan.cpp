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

#include "manthan.h"
#include <armadillo>
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>
#include "src/arjun.h"
#include <cstdlib>
#include <cstdint>
#include <ensmallen_bits/sgdr/cyclical_decay.hpp>
#include <iomanip>
#include <ios>
#include <mlpack/methods/decision_tree/decision_tree.hpp>
#include <vector>
#include <array>
#include <algorithm>
#include <ranges>
#include "constants.h"
#include "time_mem.h"
#include "ccnr/ccnr.h"

// These ask mlpack to give more info & warnings
//#define MLPACK_PRINT_INFO
//#define MLPACK_PRINT_WARN
#include <mlpack.hpp>

#include "EvalMaxSAT.h"

using namespace arma;
using namespace mlpack;
using namespace mlpack::tree;

using std::vector;
using std::array;
using std::set;
using std::setprecision;
using std::fixed;

using namespace ArjunInt;
using namespace ArjunNS;
using namespace CMSat;
constexpr uint32_t MAX_UINT32_T = std::numeric_limits<uint32_t>::max();


int lit_to_int(const Lit& l) {
    int v = l.var()+1;
    if (l.sign()) v = -v;
    return v;
}

vector<int> lits_to_ints(const vector<Lit>& lits) {
    vector<int> ret;
    ret.reserve(lits.size());
    for(const auto& l: lits) {
        ret.push_back(lit_to_int(l));
    }
    return ret;
}

// good: qdimacs/small-bug1-fixpoint-10.qdimacs.cnf
// also good: simplify qdimacs/amba2f9n.sat.qdimacs.cnf then run manthan

void Manthan::inject_cnf(SATSolver& s, bool also_vars) const {
    if (also_vars) s.new_vars(cnf.nVars());
    for(const auto& c: cnf.get_clauses()) s.add_clause(c);
    for(const auto& c: cnf.get_red_clauses()) s.add_red_clause(c);
}

vector<sample> Manthan::get_samples(const uint32_t num) {
    const double my_time = cpuTime();
    SATSolver solver_samp;
    solver_samp.set_seed(conf.seed);
    solver_samp.set_up_for_sample_counter(mconf.sampler_fixed_conflicts);
    inject_cnf(solver_samp);

    if (mconf.do_biased_sampling) {
        array<vector<sample>,2> biased_samp;
        array<vector<double>,2> dist;
        dist[0].resize(cnf.nVars(), 0.0);
        dist[1].resize(cnf.nVars(), 0.0);

        // get 500 of each biased 0/1
        const uint32_t bias_samples = 500;
        for(int bias = 0; bias <= 1; bias++) {
            for(const auto& y: to_define) {
                double bias_w = bias ? 0.9 : 0.1;
                solver_samp.set_lit_weight(Lit(y, false), bias_w);
                solver_samp.set_lit_weight(Lit(y, true), 1.0-bias_w);
            }
            vector<uint32_t> got_ones(cnf.nVars(), 0);
            for (uint32_t i = 0; i < bias_samples; i++) {
                solver_samp.solve();
                assert(solver_samp.get_model().size() == cnf.nVars());
                /// TODO: old idea of CMS, make them zero if they are all the last decision and I can do it.
                biased_samp[bias].push_back(solver_samp.get_model());

                for(const auto& v: to_define) {
                    if (solver_samp.get_model()[v] == l_True) got_ones[v]++;
                }
            }
            //print distribution
            verb_print(2, "[sampling] Bias " << bias << " distribution for to_define vars:");
            for(const auto& v: to_define) {
                dist[bias][v] = (double)got_ones[v]/(double)bias_samples;
                verb_print(1, "  var " << setw(5) << v+1 << ": "
                    << setw(6) << got_ones[v] << "/" << setw(6) << bias_samples
                    << " = " << fixed << setprecision(0) << (dist[bias][v] * 100.0) << setprecision(2) << "% ones");
            }
        }

        // compute bias from p/q as per manthan.py
        verb_print(2, "[sampling] Final biases for to_define vars:");
        for(const auto& y: to_define) {
            double p = dist[1][y];
            double q = dist[0][y];
            double bias;
            if (0.35 < p  && p < 0.65 && 0.35 < q && p < 0.65) {
              bias = p;
            } else if (q <= 0.35) {
              if (q == 0.0) q = 0.001;
              bias = q;
            } else {
              if (p == 1.0) p = 0.99;
              bias = p;
            }
            verb_print(2, "[sampling] For var " << y+1 << ": p=" << fixed << setprecision(3) << p
                << " q=" << fixed << setprecision(3) << q
                << " -- final bias: "
                << fixed << setprecision(3) << bias);
            solver_samp.set_lit_weight(Lit(y, false), bias);
            solver_samp.set_lit_weight(Lit(y, true), 1.0-bias);
        }
    }

    // get final samples
    vector<sample> samples;
    for (uint32_t i = 0; i < num; i++) {
        solver_samp.solve();
        assert(solver_samp.get_model().size() == cnf.nVars());
        samples.push_back(solver_samp.get_model());
    }
    verb_print(1, COLYEL "[manthan] Got " << samples.size() << " samples. Biased: " << (bool)mconf.do_biased_sampling
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - my_time));
    return samples;
}

vector<sample> Manthan::get_samples_ccnr(const uint32_t num) {
    const double my_time = cpuTime();

    vector<sample> samples;
    ::Arjun::CCNR::ls_solver ls_s(true, conf.seed);
    uint32_t cl_num = 0;
    ls_s._num_vars = cnf.nVars();
    ls_s._num_clauses = cnf.get_clauses().size();
    ls_s.make_space();
    vector<int> yals_lits;

    auto add_this_clause = [&](const vector<Lit>& cl) -> bool {
        yals_lits.clear();
        for(auto lit : cl) {
            int l = lit.var()+1;
            l *= lit.sign() ? -1 : 1;
            yals_lits.push_back(l);
        }

        for(auto& lit: yals_lits) {
            ls_s._clauses[cl_num].literals.push_back(::Arjun::CCNR::lit(lit, cl_num));
        }
        cl_num++;
        return true;
    };

    for(const auto& cl: cnf.get_clauses()) add_this_clause(cl);

    //Shrink the space if we have to
    assert(ls_s._num_clauses >= (int)cl_num);
    ls_s._num_clauses = (int)cl_num;
    ls_s.make_space();

    for (int c=0; c < ls_s._num_clauses; c++) {
        for(auto& item: ls_s._clauses[c].literals) {
            int v = item.var_num;
            ls_s._vars[v].literals.push_back(item);
        }
    }
    ls_s.build_neighborhood();


    sample s;
    long long int mems = num*100*1000ULL;
    for(uint32_t si = 0; si < num; si++) {
        /* ls_s.reset_mems(); */
        int res = ls_s.local_search(nullptr, mems, "c o", 50LL*1000);
        if (res) {
          s.clear();
          s.resize(cnf.nVars(), l_Undef);
          for(uint32_t i = 0; i < cnf.nVars(); i++) s[i] = ls_s._solution[i+1] ? l_True : l_False;
          samples.push_back(s);
        }
    }

    verb_print(1, COLYEL "[manthan] ccnr got " << samples.size() << " / " << num << " samples. T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - my_time));
    return samples;
}

string Manthan::pr(const lbool val) const {
    if (val == l_True) return "1";
    if (val == l_False) return "0";
    if (val == l_Undef) assert(false);
    exit(EXIT_FAILURE);
};

void Manthan::fill_dependency_mat_with_backward() {
    dependency_mat.clear();
    dependency_mat.resize(cnf.nVars());
    for(auto& m: dependency_mat) m.resize(cnf.nVars(), 0);

    const auto backw_deps = cnf.compute_backw_dependencies();
    for(const auto& [backw_var, dep_set]: backw_deps) assert(backward_defined.count(backw_var) == 1);

    assert(backw_deps.size() == backward_defined.size());
    for(const auto& v: to_define_full) {
        assert(input.count(v) == 0);
        set<uint32_t> deps_for_var; // these vars depend on v
        for(const auto& [backw_var, dep_set]: backw_deps) {
            if (dep_set.count(v)) deps_for_var.insert(backw_var);
        }
        for(const auto& d: deps_for_var) {
            assert(input.count(d) == 0);
            dependency_mat[d][v] = 1;

            // recursive update
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                if (input.count(i)) continue;
                dependency_mat[d][i] |= dependency_mat[v][i];
            }
        }
        assert(check_map_dependency_cycles());
    }

    assert(check_transitive_closure_correctness());
    assert(check_map_dependency_cycles());
}

bool Manthan::check_transitive_closure_correctness() const {
    // Then, compute transitive closure to ensure transitivity
    // If A depends on B and B depends on C, then A depends on C
    verb_print(3, "[fill-dep] Checking transitive closure");
    bool changed = true;
    while(changed) {
        changed = false;
        for(uint32_t i = 0; i < cnf.nVars(); i++) {
            if (input.count(i)) continue;
            for(uint32_t j = 0; j < cnf.nVars(); j++) {
                if (input.count(j)) continue;
                if (dependency_mat[i][j] == 0) continue;

                // i depends on j, so i should depend on everything j depends on
                for(uint32_t k = 0; k < cnf.nVars(); k++) {
                    if (input.count(k)) continue;
                    if (dependency_mat[j][k] == 1 && dependency_mat[i][k] == 0) {
                        changed = true;
                        verb_print(0, "ERROR: [fill-dep] transitive: " << i+1 << " depends on " << k+1
                            << " (via " << j+1 << ") -- but WE had to add it!!");
                        return false;
                    }
                }
            }
        }
    }
    return true;
}

void Manthan::fill_var_to_formula_with_backward() {
    const auto new_to_orig = cnf.get_new_to_orig_var();

    for(const auto& v: backward_defined) {
        FHolder::Formula f;

        // Get the original variable number
        const uint32_t v_orig = new_to_orig.at(v).var();
        const auto& aig = cnf.get_def(v_orig);
        assert(aig != nullptr);

        // Create a lambda to transform AIG to CNF using the transform function
        std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> aig_to_cnf_visitor =
          [&](AIGT type, const uint32_t var_orig, const bool neg, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                return neg ? ~fh->get_true_lit() : fh->get_true_lit();
            }

            if (type == AIGT::t_lit) {
                const auto& orig_to_new = cnf.get_orig_to_new_var();
                const auto it = orig_to_new.find(var_orig);

                Lit lit_new;
                if (it != orig_to_new.end()) lit_new = it->second;
                else {
                    assert(false);
                    /* const auto& sub_aig = cnf.get_def(var_orig); */
                    /* lit_new = AIG::transform<Lit>(sub_aig, aig_to_cnf_visitor); */
                }

                // Check if this is an input variable or needs y_to_y_hat mapping
                Lit result_lit;
                if (input.count(lit_new.var())) result_lit = lit_new ^ neg;
                else {
                    assert(to_define_full.count(lit_new.var()));
                    const uint32_t y_hat = y_to_y_hat.at(lit_new.var());
                    result_lit = Lit(y_hat, neg);
                }
                return result_lit;
            }

            if (type == AIGT::t_and) {
                const Lit l_lit = *left;
                const Lit r_lit = *right;

                // Create fresh variable for AND gate
                solver.new_var();
                const Lit and_out = Lit(solver.nVars() - 1, false);

                // Generate Tseitin clauses for AND gate
                // and_out represents (l_lit & r_lit)
                f.clauses.push_back(CL({~and_out, l_lit}));
                f.clauses.push_back(CL({~and_out, r_lit}));
                f.clauses.push_back(CL({~l_lit, ~r_lit, and_out}));

                // Apply negation if needed
                return neg ? ~and_out : and_out;
            }
            assert(false && "Unhandled AIG type in visitor");
            exit(EXIT_FAILURE);
        };

        // Recursively generate clauses for the AIG using the transform function
        map<aig_ptr, Lit> cache;
        Lit out_lit = AIG::transform<Lit>(aig, aig_to_cnf_visitor, cache);
        f.out = out_lit;
        f.aig = AIG::new_lit(v);
        assert(var_to_formula.count(v) == 0);
        var_to_formula[v] = f;
    }
}

// This adds (and re-numbers) the deep-copied AIGs to a fresh copy of the CNF, then checks if the CNF
// has any AIG cycles
bool Manthan::check_aig_dependency_cycles() const {
    // We need to copy these, so we don't accidentally update the original.
    // We deep copy them together in one go, to preserve e.g. cycles
    std::map<uint32_t, aig_ptr> aigs;
    for(const auto& y: to_define) {
        if (!var_to_formula.count(y)) continue;
        aigs[y] = var_to_formula.at(y).aig;
    }
    auto aigs_copy = AIG::deep_clone_map(aigs);

    SimplifiedCNF fcnf = cnf;
    fcnf.map_aigs_to_orig(aigs_copy, cnf.nVars());
    assert(fcnf.check_aig_cycles());
    return true;
}

void Manthan::print_y_order_occur() const {
    vector<uint32_t> occur_lit(cnf.nVars()*2, 0);
    for(const auto& cl: cnf.get_clauses()) {
        for(const auto& l: cl) occur_lit[l.toInt()]++;
    }
    for(const auto& y: y_order) {
        const uint32_t pos = occur_lit[Lit(y, false).toInt()];
        const uint32_t neg = occur_lit[Lit(y, true).toInt()];
        verb_print(2, "[y-order] var " << setw(4) << y+1
            << " BW: " << backward_defined.count(y)
            << "   pos occur " << setw(6) << pos
            << "   --  neg occur " << setw(6) << neg);
    }
}

void Manthan::print_cnf_debug_info(const sample& ctx) const {
    if (conf.verb >= 3) {
        for(const auto& y: to_define_full) {
            const auto y_hat = y_to_y_hat.at(y);
            if (ctx[y] == ctx[y_hat]) continue;
            verb_print(3, "for y " << setw(5) << y+1 << ": " << setw(4) << pr(ctx[y])
                    << " we got y_hat " << setw(5) << y_hat+1 << ":" << setw(4) << pr(ctx[y_hat]));
        }
        cout << "c o [DEBUG] CNF valuation: ";
        for(uint32_t i = 0; i < cnf.nVars(); i++)
            cout << "var " << setw(3) << i+1 << ": " << pr(ctx[i]) << " -- ";
        cout << endl;
    }
}

SimplifiedCNF Manthan::do_manthan(const SimplifiedCNF& input_cnf) {
    assert(input_cnf.get_need_aig() && input_cnf.defs_invariant());
    assert(mconf.simplify_every > 0 && "Can't give simplify_every=0");
    const double my_time = cpuTime();
    const auto ret = input_cnf.find_disconnected();
    verb_print(1, "[manthan] Found " << ret.size() << " disconnected components");

    uint32_t tot_repaired = 0;
    cout << "c o [DEBUG] About to assign cnf = input_cnf" << endl;
    cnf = input_cnf;
    if (!mconf.write_manthan_cnf.empty()) cnf.write_simpcnf(mconf.write_manthan_cnf);

    // CNF is divided into:
    // input vars -- original sampling vars
    // defined non-input vars -- vars defined via backward_round_synth
    // to_define vars -- vars that are not defined yet, and not input
    std::tie(input, to_define, backward_defined) = cnf.get_var_types(conf.verb);
    if (to_define.empty()) {
        verb_print(1, "[manthan] No variables to define, returning original CNF");
        return cnf;
    }
    to_define_full.clear();
    to_define_full.insert(to_define.begin(), to_define.end());
    to_define_full.insert(backward_defined.begin(), backward_defined.end());
    fill_dependency_mat_with_backward();
    get_incidence();

    // Fill repair solver with CNF
    repair_solver.new_vars(cnf.nVars());
    inject_cnf(repair_solver, false); // faster to add CNF later

    // Sampling
    verb_print(1, "[manthan] Getting " << mconf.num_samples << " samples...");
    vector<sample> samples = get_samples(mconf.num_samples);
    {
        vector<sample> samples2 = get_samples_ccnr(mconf.num_samples_ccnr);
        samples.insert(samples.end(), samples2.begin(), samples2.end());
    }


    // Training
    inject_cnf(solver);
    fh = std::make_unique<FHolder>(&solver);
    verb_print(2, "True lit in solver_train: " << fh->get_true_lit());
    verb_print(2, "[manthan] After fh creation: solver_train.nVars() = " << solver.nVars() << " cnf.nVars() = " << cnf.nVars());
    fix_order();
    print_y_order_occur();
    verb_print(1, "[manthan] Starting training. Manthan Config. "
        << "do_filter_samples=" << mconf.do_filter_samples
        << ", num_samples=" << mconf.num_samples
        << ", minimumLeafSize=" << mconf.minimumLeafSize
        << ", minGainSplit=" << mconf.minGainSplit
        << ", maximumDepth=" << mconf.maximumDepth);
        /* << ", train_error_threshold=" << mconf.train_error_threshold */
        /* << ", max_num_nodes=" << mconf.max_num_nodes */
        /* << ", num_epochs=" << mconf.num_epochs */
        /* << ", batch_size=" << mconf.batch_size */
        /* << ", learning_rate=" << mconf.learning_rate */
        /* << ", weight_decay=" << mconf.weight_decay */
        /* << ", step_size=" << mconf.step_size */
        /* << ", lr_decay_factor=" << mconf.lr_decay_factor */
        /* << ", use_sgdr=" << std::boolalpha << mconf.use_sgdr */ // stochastic gradient descent with restarts
    sort_all_samples(samples);
    const double train_start_time = cpuTime();
    for(const auto& v: y_order) {
        if (backward_defined.count(v)) continue;
        train(samples, v); // updates dependency_mat
    }
    verb_print(1, COLYEL "[manthan] training done. T: " << std::setprecision(2) << std::fixed << (cpuTime() - train_start_time) << " seconds");
    assert(check_map_dependency_cycles());

    const double repair_time = cpuTime();
    add_not_F_x_yhat();
    fill_var_to_formula_with_backward();
    fix_order();
    for(const auto& y: y_order) updated_y_funcs.push_back(y);

    // Counterexample-guided repair
    bool at_least_one_repaired = true;
    while(true) {
        if (num_loops_repair %  40 == 39) {
            verb_print(1, "[manthan] repaired so far: " << setw(6) << tot_repaired
                    << "   loops: "<< setw(4) << num_loops_repair
                    << "   avg repairs/loop: " << setprecision(1) << setw(4) << (double)tot_repaired/(num_loops_repair+0.0001)
                    << "   avg confl sz: " << setw(6) << fixed << setprecision(2) << (double)conflict_sizes_sum/(tot_repaired+0.0001)
                    << "   avg needs rep sz: " << setw(6) << fixed << setprecision(2) << (double)needs_repair_sum/(num_loops_repair+0.0001)
                    << "   T: " << setprecision(2) << fixed << setw(7) << cpuTime()-repair_time
                    << "   repair/s: " << setprecision(4) << (double)tot_repaired/(cpuTime()-repair_time+0.0001) << setprecision(2));
        }
        assert(at_least_one_repaired);
        at_least_one_repaired = false;
        num_loops_repair++;
        inject_formulas_into_solver();
        sample ctx;
        bool finished = get_counterexample(ctx);
        for(const auto& val: ctx) assert(val != l_Undef);
        if (finished) break;
        print_cnf_debug_info(ctx);

        uint32_t old_needs_repair_size;;
        vector<lbool> better_ctx;
        if (mconf.do_maxsat_better_ctx == -1) {
            better_ctx = ctx;
        } else if (mconf.do_maxsat_better_ctx == 1) {
          better_ctx = find_better_ctx_maxsat(ctx, old_needs_repair_size);
        } else {
          better_ctx = find_better_ctx_normal(ctx, old_needs_repair_size);
        }
        needs_repair_sum += needs_repair.size();

        verb_print(2, "[manthan] Finding better ctx DONE, needs_repair size before vs now: "
              << setw(3) << old_needs_repair_size << " -- " << setw(4) << needs_repair.size());
        for(const auto& y: to_define_full) if (!needs_repair.count(y)) {
            ctx[y] = better_ctx[y];
            if (conf.verb >= 3 && better_ctx[y] != ctx[y])
                verb_print(3, "Updated ctx on v: " << y+1 << " new val: " << better_ctx[y] << " old val: " << ctx[y]);
        }

        assert(!needs_repair.empty());
        uint32_t num_repaired = 0;
        while(!needs_repair.empty()) {
            const auto y_rep = find_next_repair_var(ctx); // updates ctx on backward-defined vars
            if (y_rep == std::numeric_limits<uint32_t>::max()) break;
            bool done = repair(y_rep, ctx); // this updates ctx on y
            if (done) {
                at_least_one_repaired = true;
                num_repaired++;
                tot_repaired++;
            }
            verb_print(3, "[manthan] finished repairing " << y_rep+1 << " : " << std::boolalpha << done);
        }
        verb_print(2, "[manthan] Num repaired: " << num_repaired << " tot repaired: " << tot_repaired << " num_loops_repair: " << num_loops_repair);
    }
    assert(check_map_dependency_cycles());
    verb_print(1, "[manthan] DONE");

    // Build final CNF
    map<uint32_t, aig_ptr> aigs;
    for(const auto& y: to_define) {
        assert(var_to_formula.count(y));
        verb_print(3, "Final formula for " << y+1 << ":" << endl << var_to_formula[y]);
        aigs[y] = var_to_formula[y].aig;
    }
    SimplifiedCNF fcnf = cnf;
    fcnf.map_aigs_to_orig(aigs, cnf.nVars());
    assert(verify_final_cnf(fcnf));
    verb_print(1, COLRED "[manthan] Total time in manthan: " << cpuTime()-my_time << " seconds");
    return fcnf;
}

bool Manthan::verify_final_cnf(const SimplifiedCNF& fcnf) const {
    assert(fcnf.check_aig_cycles());
    auto [input2, to_define2, backward_defined2] = fcnf.get_var_types(0);
    for(const auto& v: to_define2) {
        cout << "ERROR: var " << v+1 << " not defined in final CNF!" << endl;
        assert(false && "All to-define vars must be defined in final CNF");
    }
    assert(fcnf.get_need_aig() && fcnf.defs_invariant());
    return true;
}

uint32_t Manthan::find_next_repair_var(sample& ctx) {
    while(!needs_repair.empty()) {
        uint32_t y_rep = std::numeric_limits<uint32_t>::max();
        for(const auto& t: y_order) {
            if (needs_repair.count(t)) {
                y_rep = t;
                break;
            }
        }
        if (backward_defined.count(y_rep)) {
            verb_print(3, "[WARNING] trying to repair backward-defined var " << y_rep+1);
            ctx[y_to_y_hat[y_rep]] = ctx[y_rep]; // pretend to have fixed the ctx
            needs_repair.erase(y_rep);
            continue;
        }
        if (conf.verb >= 2) {
            cout << "c o needs repair: ";
            for(const auto& y: y_order) if (needs_repair.count(y)) {
                cout << y+1;
                if (backward_defined.count(y)) cout << "[BW]";
                cout << " ";
            }
            std::cout << endl;
        }
        assert(y_rep != std::numeric_limits<uint32_t>::max());
        needs_repair.erase(y_rep);
        verb_print(3, "-------------------");
        return y_rep;
    }
    return std::numeric_limits<uint32_t>::max();
}

bool Manthan::repair(const uint32_t y_rep, sample& ctx) {
    verb_print(2, "[DEBUG] Starting repair for var " << y_rep+1
            << (backward_defined.count(y_rep) ? "[BW]" : ""));
    assert(backward_defined.count(y_rep) == 0 && "Backward defined should need NO repair, ever");
    assert(to_define.count(y_rep) == 1 && "Only to-define vars should be repaired");
    assert(y_rep < cnf.nVars());
    assert(to_define.count(y_rep));

    if (num_loops_repair % mconf.simplify_every == (mconf.simplify_every-1)) {
        vector<Lit> assumps;
        assumps.reserve(input.size() + to_define_full.size());
        for(const auto& x: input) assumps.push_back(Lit(x, false));
        for(const auto& x: to_define_full) assumps.push_back(Lit(x, false));
        repair_solver.simplify(&assumps);
    }

    vector<Lit> conflict;
    bool ret = find_minim_conflict(y_rep, ctx, conflict);
    if (!ret) return false;
    perform_repair(y_rep, ctx, conflict);
    return true;
}

bool Manthan::find_minim_conflict(const uint32_t y_rep, sample& ctx, vector<Lit>& conflict) {
    // F(x,y) & x = ctx(x) && forall_y (y not dependent on v) (y = ctx(y)) & NOT (v = ctx(v))
    // Used to find UNSAT core that will help us repair the function
    vector<Lit> assumps;
    for(const auto& x: input) {
        const Lit l = Lit(x, ctx[x] == l_False);
        assumps.push_back({l});
        /* cout << "assumed input cl: " << std::vector<Lit>{l} << endl; */
    }

    // We go through the variables that y_rep does NOT depend on, and assume them to be correct
    for(const auto& y: y_order) {
        if (y == y_rep) break; // beyond this point we don't care
        assert(dependency_mat[y][y_rep] != 1 && "due to ordering, this should not happen. Otherwise y depends on y_rep, but we will repair y_rep potentially with y_rep");
        assert(ctx[y] == ctx[y_to_y_hat[y]]); // they are correct
        const Lit l = Lit(y, ctx[y] == l_False);
        verb_print(3, "assuming " << y+1 << " is " << ctx[y]);
        assumps.push_back({l});
        /* cout << "assumed cl: " << std::vector<Lit>{l} << endl; */
    }

    assert(ctx[y_rep] != ctx[y_to_y_hat[y_rep]] && "before repair, y and y_hat must be different");
    const Lit repairing = Lit(y_rep, ctx[y_to_y_hat[y_rep]] == l_True);
    assumps.push_back({~repairing});
    /* cout << "added repairing cl: " << std::vector<Lit>{~repairing} << endl; */

    verb_print(2, "assuming reverse for y_rep: " << ~repairing);
    auto ret = repair_solver.solve(&assumps);
    assert(ret != l_Undef);
    if (ret == l_True) {
        verb_print(2, "Repair cost is 0 for y: " << y_rep+1);
        for(uint32_t i = 0; i < cnf.nVars(); i++) {
            ctx[i] = repair_solver.get_model()[i];
        }
        /* ctx[y_rep] = ctx[y_rep] ^ true; */
        ctx[y_to_y_hat[y_rep]] = ctx[y_rep];
        // TODO: recompute y_hat values!!!
        bool reached = false;
        for(const auto&y: y_order) {
            if (y == y_rep) {reached = true; continue;}
            if (!reached) continue;
            if (repair_solver.get_model()[y] != ctx[y_to_y_hat[y]]) {
                needs_repair.insert(y);
            } else {
                needs_repair.erase(y);
            }
        }
        return false;
    } else {
        ctx[y_to_y_hat[y_rep]] = ctx[y_rep];
    }
    conflict = repair_solver.get_conflict();
    verb_print(2, "repair_maxsat conflict: " << conflict);
    if (conflict.empty()) {
        verb_print(1, "repairing " << y_rep+1 << " is not possible");
        return false;
    }
    uint32_t orig_size = conflict.size();
    if (conflict.size() > 1 && mconf.do_minimize_conflict)
        minimize_conflict(conflict, assumps, repairing);

    auto now_end = std::remove_if(conflict.begin(), conflict.end(),
                [&](const Lit l){ return l == repairing; });
    assert(now_end != conflict.end() && "repairing literal must be in conflict");
    conflict.erase(now_end, conflict.end());
    if (conflict.empty()) {
        verb_print(1, "repairing " << y_rep+1 << " is not possible after minimization");
        return false;
    }
    verb_print(2, "[manthan] minim. Removed: " << (orig_size - conflict.size())
            << " from conflict, now size: " << conflict.size());
    return true;
}

void Manthan::minimize_conflict(vector<Lit>& conflict, vector<Lit>& assumps, const Lit repairing) {
    bool removed_any = true;
    set<Lit> failed_removing;
    failed_removing.insert(repairing);
    while(removed_any) {
        std::shuffle(conflict.begin(), conflict.end(), mtrand);
        removed_any = false;
        for(const auto& try_rem: conflict) {
            if (failed_removing.count(try_rem)) continue;
            verb_print(3, "Trying to remove conflict literal: " << try_rem);
            assumps.clear();
            for(const auto& l: conflict) {
                if (l == try_rem) continue;
                assumps.push_back(~l);
            }
            release_assert(assumps.size() == conflict.size()-1);
            auto ret2 = repair_solver.solve(&assumps);
            if (ret2 == l_True) {
                failed_removing.insert(try_rem);
                continue;
            }
            conflict = repair_solver.get_conflict();
            removed_any = true;
            break;
        }
    }
}

void Manthan::perform_repair(const uint32_t y_rep, const sample& ctx, const vector<Lit>& conflict) {
    verb_print(2, "[manthan] Performing repair on " << setw(5) << y_rep+1
            << " with conflict size " << setw(3) << conflict.size());
    assert(backward_defined.count(y_rep) == 0 && "Backward defined should need NO repair, ever");
    conflict_sizes_sum += conflict.size();

    // not (conflict) -> v = ctx(v)
    FHolder::Formula f;

    // CNF part
    vector<Lit> cl;
    solver.new_var();
    auto fresh_l = Lit(solver.nVars()-1, false);
    cl.push_back(fresh_l);
    for(const auto& l: conflict) {
        cl.push_back(l);
        dependency_mat[y_rep][l.var()] = 1;
        // recursive update
        for(uint32_t i = 0; i < cnf.nVars(); i++) {
            if (input.count(i)) continue;
            dependency_mat[y_rep][i] |= dependency_mat[l.var()][i];
        }
        SLOW_DEBUG_DO(assert(check_map_dependency_cycles()));
    }
    f.clauses.push_back(cl);
    for(const auto& l: conflict) {
        cl.clear();
        cl.push_back(~fresh_l);
        cl.push_back(~l);
        f.clauses.push_back(cl);
    }
    f.out = fresh_l;

    // AIG part
    assert(!conflict.empty());
    auto b1 = AIG::new_lit(~conflict[0]);
    for(size_t i = 1; i < conflict.size(); i++) {
        auto lit_aig = AIG::new_lit(~conflict[i]);
        b1 = AIG::new_and(b1, lit_aig);
    }
    f.aig = b1;

    // when fresh_l is false, confl is satisfied
    verb_print(4, "Original formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    verb_print(4, "Branch formula. When this is true, H is wrong:" << endl << f);
    var_to_formula[y_rep] = fh->compose_ite(fh->constant_formula(ctx[y_rep] == l_True),
            var_to_formula[y_rep], f);
    updated_y_funcs.push_back(y_rep);
    verb_print(2, "repaired formula for " << y_rep+1 << " with " << conflict.size() << " vars");
    verb_print(4, "repaired formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    //We fixed the ctx on this variable
    assert(check_map_dependency_cycles());
}

// Will order 1st the variables that NOTHING depends on
// Will order LAST the variables that depends on EVERYTHING
void Manthan::fix_order() {
    double my_time = cpuTime();
    y_order.clear();
    verb_print(2, "[manthan] Fixing order...");
    vector<uint32_t> sorted(to_define_full.begin(), to_define_full.end());
    sort_unknown(sorted, incidence);
    /* std::reverse(sorted.begin(), sorted.end()); */

    set<uint32_t> already_fixed;
    while(already_fixed.size() != to_define_full.size()) {
        for(const auto& y: sorted) {
            if (already_fixed.count(y)) continue;
            verb_print(3, "Trying to add " << y+1 << " to order. to_define: " << to_define.count(y)
                 << " backward_defined: " << backward_defined.count(y));

            bool ok = true;
            for(const auto& y2: to_define_full) {
                if (y == y2) continue;
                if (dependency_mat[y][y2] == 0) continue;
                if (dependency_mat[y][y2] == 1 && already_fixed.count(y2)) continue;
                verb_print(3, "Bad due to y2: " << y2+1);
                ok = false;
                break;
            }
            if (!ok) continue;
            verb_print(2, "Fixed order of " << setw(5) << y+1 << " to: " << setw(5) << y_order.size()
                    << " BW: " << backward_defined.count(y));
            already_fixed.insert(y);
            y_order.push_back(y);
        }
    }
    verb_print(1, "[manthan] Fixed order. T: " << setprecision(2) << fixed << (cpuTime() - my_time)
            << " Final order size: " << y_order.size());
}

// Fills needs_repair with vars from y (i.e. output)
sample Manthan::find_better_ctx_maxsat(const sample& ctx, uint32_t& old_needs_repair_size) {
    needs_repair.clear();
    old_needs_repair_size = 0;
    verb_print(2, "Finding better ctx.");
    EvalMaxSAT s_ctx;
    for(uint32_t i = 0; i < cnf.nVars(); i++) s_ctx.newVar();

    // Fix input values
    for(const auto& x: input) {
        assert(ctx[x] != l_Undef && "Input variable must be defined in counterexample");
        const auto l = Lit(x, ctx[x] == l_False);
        s_ctx.addClause(lits_to_ints({l}));
    }

    // Fix to_define variables that are correct (y_hat is the learned one)
    for(const auto& y: to_define_full) {
        const auto y_hat = y_to_y_hat[y];
        if (ctx[y] != ctx[y_hat]) continue;
        verb_print(3, "[find-better-ctx] CTX is CORRECT on y=" << y+1 << " y_hat=" << y_hat+1
             << " -- ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat]));
        const Lit l = Lit(y, ctx[y_hat] == l_False);
        s_ctx.addClause(lits_to_ints({l}));
    }

    // Add all clauses
    for(const auto& c: cnf.get_clauses()) s_ctx.addClause(lits_to_ints(c));

    map<uint32_t, uint32_t> y_to_y_order_pos;
    for(size_t i = 0; i < y_order.size(); i++) {
        y_to_y_order_pos[y_order[i]] = y_order.size()-i;
    }

    // Fix to_define variables that are incorrect via assumptions
    set<Lit> assumps;
    for(const auto& y: y_order) {
        const auto y_hat = y_to_y_hat[y];
        if (ctx[y] == ctx[y_hat]) continue;
        const auto l = Lit(y, ctx[y_hat] == l_False);
        old_needs_repair_size++;
        verb_print(3, "[find-better-ctx] put into assumps y= " << l);
        assumps.insert(l);
        /* int w = 1; */
        int w = y_to_y_order_pos[y]*100;
        /* if (backward_defined.count(y)) w *= 2; */
        /* if (w == 0) w = 1; */
        s_ctx.addClause(lits_to_ints({l}), w); //want to flip valuation to ctx[y_hat], so when l is true, we flipped it (i.e. needs no repair)
    }

    /* verb_print(3, "[find-better-ctx] iteration " << i << " with " << ass.size() << " assumptions"); */
    auto ret = s_ctx.solve();
    assert(ret && "must be satisfiable");
    assert(s_ctx.getCost() > 0);
    for(const auto&l : assumps) {
        if (!s_ctx.getValue(lit_to_int(l))) {
            needs_repair.insert(l.var());
        }
    }
    verb_print(2, "optimum found: " << needs_repair.size() << " original assumps size: " << assumps.size());
    /* assert(needs_repair.size() == s_ctx.getCost()); */
    assert(!needs_repair.empty());

    sample better_ctx(cnf.nVars(), l_Undef);
    for(const auto& v: to_define_full) better_ctx[v] = s_ctx.getValue(v+1) ? l_True : l_False;
    return better_ctx;
}

// Fills needs_repair with vars from y (i.e. output) using normal SAT solver with assumptions
sample Manthan::find_better_ctx_normal(const sample& ctx, uint32_t& old_needs_repair_size) {
    SATSolver ctx_solver;
    ctx_solver.new_vars(cnf.nVars());

    needs_repair.clear();
    old_needs_repair_size = 0;
    verb_print(2, "Finding better ctx using normal SAT solver.");

    // Fix input values
    for(const auto& x: input) {
        assert(ctx[x] != l_Undef && "Input variable must be defined in counterexample");
        const auto l = Lit(x, ctx[x] == l_False);
        ctx_solver.add_clause({l});
    }

    map<uint32_t, uint32_t> y_to_y_order_pos;
    for(size_t i = 0; i < y_order.size(); i++) {
        y_to_y_order_pos[y_order[i]] = y_order.size()-i;
    }

    // For to_define variables, separate into correct and incorrect
    vector<std::pair<Lit, uint32_t>> incorrect_lits; // pair of literal and weight
    for(const auto& y: to_define_full) {
        const auto y_hat = y_to_y_hat[y];
        const Lit l = Lit(y, ctx[y_hat] == l_False); // literal that makes y match y_hat

        if (ctx[y] == ctx[y_hat]) {
            // Already correct, make this a fixed assumption
            verb_print(3, "[find-better-ctx-normal] CTX is CORRECT on y=" << y+1 << " y_hat=" << y_hat+1
                 << " -- ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat]));
            ctx_solver.add_clause({l});
        } else {
            // Incorrect, we want to try to fix this
            old_needs_repair_size++;
            uint32_t weight = y_to_y_order_pos[y];
            incorrect_lits.push_back({l, weight});
            verb_print(3, "[find-better-ctx-normal] CTX is INCORRECT on y=" << y+1
                 << " ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat])
                 << " weight=" << weight);
        }
    }
    inject_cnf(ctx_solver, false);

    // Sort incorrect lits by weight (higher weight = higher priority to fix)
    std::sort(incorrect_lits.begin(), incorrect_lits.end(),
              [](const auto& a, const auto& b) { return a.second > b.second; });

    // Iteratively find a minimal CTX
    set<uint32_t> cannot_fix; // variables we cannot fix
    vector<Lit> assumps;
    while (true) {
        assumps.clear();
        for(const auto& [lit, weight]: incorrect_lits) {
            if (cannot_fix.count(lit.var()) == 0) assumps.push_back(lit);
        }
        auto ret = ctx_solver.solve(&assumps);
        if (ret == l_True) {
            // Success! Extract the model
            verb_print(2, "[find-better-ctx-normal] Found satisfying assignment. "
                       << "Could not fix " << cannot_fix.size() << " variables.");
            sample better_ctx(cnf.nVars(), l_Undef);
            for(const auto& v: to_define_full) {
                better_ctx[v] = ctx_solver.get_model()[v];
                const auto y_hat = y_to_y_hat[v];
                if (better_ctx[v] != ctx[y_hat]) {
                    needs_repair.insert(v);
                }
            }
            verb_print(2, "Optimum found: " << needs_repair.size()
                       << " variables need repair (original: " << old_needs_repair_size << ")");
            assert(!needs_repair.empty() || cannot_fix.empty());
            return better_ctx;
        } else {
            auto conflict = ctx_solver.get_conflict();
            assert(!conflict.empty() && "Got UNSAT with empty conflict!");
            verb_print(3, "[find-better-ctx-normal] UNSAT, conflict size: " << conflict.size());

            // Find which soft assumptions are in the conflict
            set<Lit> conflict_set(conflict.begin(), conflict.end());
            for(const auto& [lit, weight]: incorrect_lits) {
                if (conflict_set.count(~lit) && !cannot_fix.count(lit.var())) {
                    verb_print(3, "[find-better-ctx-normal] Giving up on fixing var " << lit.var()+1);
                    cannot_fix.insert(lit.var());
                    break; // Remove one at a time
                }
            }
        }
    }
}

// Adds ~F(x, y_hat), fills y_to_y_hat and y_hat_to_y
void Manthan::add_not_F_x_yhat() {
    vector<Lit> tmp;
    // Create variables for y_hat
    for(const auto& y: to_define_full) {
        solver.new_var();
        const uint32_t y_hat = solver.nVars()-1;
        y_to_y_hat[y] = y_hat;
        y_hat_to_y[y_hat] = y;
        verb_print(3, "mapping -- y: " << y+1 << " y_hat: " << y_hat+1);
    }

    // Adds ~F(x, y_hat)
    vector<Lit> cl_indics; // if true, clause is satisfied, if false, clause is unsatisfied
    for(const auto& cl_orig: cnf.get_clauses()) {
        // Replace y with y_hat in the clause
        vector<Lit> cl;
        for(const auto& l: cl_orig) {
            if (to_define_full.count(l.var())) cl.push_back(Lit(y_to_y_hat[l.var()], l.sign()));
            else cl.push_back(l);
        }

        solver.new_var();
        uint32_t v = solver.nVars()-1;
        Lit cl_indic(v, false);
        tmp.clear();
        tmp.push_back(~cl_indic);
        for(const auto&l : cl) tmp.push_back(l);
        solver.add_clause(tmp);

        for(const auto&l : cl) {
            tmp.clear();
            tmp.push_back(cl_indic);
            tmp.push_back(~l);
            solver.add_clause(tmp);
        }
        cl_indics.push_back(cl_indic);
    }
    tmp.clear();
    for(const auto& l: cl_indics) tmp.push_back(~l); // at least one is unsatisfied
    solver.add_clause(tmp);
}

void Manthan::inject_formulas_into_solver() {
    // Replace y with y_hat
    for(auto& [var, form]: var_to_formula) {
        for(auto& cl: form.clauses) {
            if (cl.inserted) continue;
            vector<Lit> cl2;
            for(const auto& l: cl.lits) {
                auto v = l.var();
                if (to_define_full.count(v)) { cl2.push_back(Lit(y_to_y_hat[v], l.sign()));}
                else cl2.push_back(l);
            }
            solver.add_clause(cl2);
            cl.inserted = true;
        }
    }
}

bool Manthan::get_counterexample(sample& ctx) {
    if (num_loops_repair == 1)
        verb_print(1, "[manthan] Getting counterexample for the first time...");

    // Relation between y_hat and form_out
    // when y_hat_to_indic is TRUE, y_hat and form_out are EQUAL
    vector<Lit> tmp;
    for(const auto& y: updated_y_funcs) {
        solver.new_var();
        const uint32_t ind = solver.nVars()-1;

        assert(var_to_formula.count(y));
        const auto& form_out = var_to_formula[y].out;
        const auto& y_hat = y_to_y_hat[y];

        y_hat_to_indic[y_hat] = ind;
        indic_to_y_hat[ind] = y_hat;
        verb_print(3, "->CTX ind: " << ind+1 << " y_hat: " << y_hat+1  << " form_out: " << form_out);

        // when indic is TRUE, y_hat and form_out are EQUAL
        auto y_hat_l = Lit(y_hat, false);
        auto ind_l = Lit(ind, false);
        tmp.clear();
        tmp.push_back(~ind_l);
        tmp.push_back(y_hat_l);
        tmp.push_back(~form_out);
        solver.add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        solver.add_clause(tmp);

        tmp.clear();
        tmp.push_back(ind_l);
        tmp.push_back(~y_hat_l);
        tmp.push_back(~form_out);
        solver.add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        solver.add_clause(tmp);
    }
    updated_y_funcs.clear();

    vector<Lit> assumps;
    assumps.reserve(y_hat_to_indic.size());
    for(const auto& i: y_hat_to_indic) assumps.push_back(Lit(i.second, false));
    verb_print(4, "assumptions: " << assumps);
    if ((num_loops_repair % mconf.simplify_every) == (mconf.simplify_every-1)) solver.simplify(&assumps);

    /* solver.set_up_for_sample_counter(1000); */
    auto ret = solver.solve(&assumps);
    assert(ret != l_Undef);
    if (ret == l_True) {
        verb_print(2, COLYEL "[manthan] *** Counterexample found ***");
        ctx = solver.get_model();
        assert(ctx[fh->get_true_lit().var()] == l_True);
        for(const auto& y: y_order) {
            const auto y_hat = y_to_y_hat[y];
            if (ctx[y] == ctx[y_hat]) continue;
            needs_repair.insert(y);
        }
        return false;
    } else {
        assert(ret == l_False);
        verb_print(2, "Formula is good!");
        for(auto& f: var_to_formula) {
            if (!f.second.finished) {
                verb_print(2, "Marking Formula for " << f.first+1 << " as finished");
                f.second.finished = true;
            }
        }
        return true;
    }
}

FHolder::Formula Manthan::recur(DecisionTree<>* node, const uint32_t learned_v, const vector<uint32_t>& used_vars, uint32_t depth) {
    /* for(uint32_t i = 0; i < depth; i++) cout << " "; */
    if (node->NumChildren() == 0) {
        const bool val = node->ClassProbabilities()[1] > node->ClassProbabilities()[0];
        /* cout << "Leaf: "; */
        /* for(uint32_t i = 0; i < node->NumClasses(); i++) { */
        /*     cout << "class "<< i << " prob: " << node->ClassProbabilities()[i] << " --- "; */
        /* } */
        /* cout << endl; */
        return fh->constant_formula(val);
    } else {
        uint32_t v = node->SplitDimension();
        assert(v < used_vars.size());
        v = used_vars[v];
        /* cout << "(learning " << learned_v+1<< ") Node. v: " << v+1 << std::flush; */
        if (to_define_full.count(v)) {
            // v does not depend on learned_v!
            assert(dependency_mat[v][learned_v] == 0);
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                if (dependency_mat[v][i] == 1) {
                    if (input.count(i)) continue;
                    // nothing that v depends on can depend on learned_v
                    assert(dependency_mat[i][learned_v] == 0);
                }
            }
            // set that learned_v depends on v
            dependency_mat[learned_v][v] = 1;
            verb_print(3, learned_v+1 << " depends on " << v+1);

            // recursive update
            for(uint32_t i = 0 ; i < cnf.nVars(); i++) {
                if (input.count(i)) continue;
                dependency_mat[learned_v][i] |= dependency_mat[v][i];
            }
        } else
            verb_print(3, learned_v+1 << " depends on " << v+1 << " but NOT adding it, because it is not in to_define_full. input: " << (input.count(v) ? "yes" : "no"));

        /* cout << "  -- all-0 goes -> " << node->CalculateDirection(point_0); */
        /* cout << "  -- all-1 goes -> " << node->CalculateDirection(point_1) << endl; */
        assert(node->NumChildren() == 2);
        auto form_0 = recur(&node->Child(0), learned_v, used_vars, depth+1);
        auto form_1 = recur(&node->Child(1), learned_v, used_vars, depth+1);
        bool val_going_right = node->CalculateDirection(point_1);
        return fh->compose_ite(form_0, form_1, Lit(v, val_going_right));
    }
    assert(false);
}

// Checks if flipping variable v in sample s satisfies all clauses
vector<sample*> Manthan::filter_samples(const uint32_t v, const vector<sample>& samples) {
    auto check_satisfied_all_cls_with_flip = [](const sample& s, const uint32_t v2, const vector<vector<Lit>*>& clause_ptrs) -> bool {
        // Check all clauses
        for(const auto& cl: clause_ptrs) {
            bool satisfied = false;
            for(const auto& l: *cl) {
                uint32_t var = l.var();
                bool sign = l.sign();
                lbool val = s[l.var()];
                assert(val != l_Undef);
                if (var == v2) val = val ^ true;
                val = val ^ sign;
                if (val == l_True) {
                    satisfied = true;
                    break;
                }
            }
            if (!satisfied) return false;
        }
        // all clauses satisfied
        return true;
    };

    uint32_t num_removed = 0;
    vector<sample*> filtered_samples;
    vector<vector<Lit>*> clause_ptrs;
    for(const auto& cl: cnf.get_clauses()) {
        bool found = false;
        for(const auto& l: cl) {
            if (l.var() == v) {
                found = true;
                break;
            }
        }
        if (found) clause_ptrs.push_back(const_cast<vector<Lit>*>(&cl));
    }
    for(const auto& s: samples) {
        bool ret = check_satisfied_all_cls_with_flip(s, v, clause_ptrs);
        if (!ret) {
            // sample is good
            filtered_samples.push_back(const_cast<sample*>(&s));
        } else num_removed++;
    }
    verb_print(2, "[filter_samples] For variable " << setw(6) << v+1 << ", removed "
            << setw(6) << num_removed << " / " << setw(6) << samples.size()
            << " samples that had no effect on it.");

    return filtered_samples;
}

void Manthan::sort_all_samples(vector<sample>& samples) {
    if (samples.size() <= 1) return;
    std::sort(samples.begin(), samples.end(),
        [this](const sample& a, const sample& b) {
            for(const auto& v: input) {
                if (a[v] != b[v]) return a[v] == l_False;
            }
            return false; // equal
        });

    vector<sample> samples2;
    samples2.push_back(samples[0]);
    for(size_t i = 1; i < samples.size(); i++) {
        for(const auto& v: input) {
            if (samples[i][v] != samples2.back()[v]) {
                samples2.push_back(samples[i]);
                break;
            }
        }
    }
    verb_print(1, "[sort_all_samples] Reduced samples from " << samples.size()
            << " to " << samples2.size() << " by removing duplicates on input vars.");
    samples = samples2;
}

double Manthan::train(const vector<sample>& orig_samples, const uint32_t v) {
    verb_print(2, "training variable: " << v+1);
    /* assert(!orig_samples.empty()); */
    vector<sample*> samples;
    if (mconf.do_filter_samples) samples = filter_samples(v, orig_samples);
    else {
        for(const auto& s: orig_samples)
            samples.push_back(const_cast<sample*>(&s));
    }
    assert(v < cnf.nVars());
    point_0.resize(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) point_0[i] = 0;
    point_1.resize(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) point_1[i] = 1;

    Mat<uint8_t> dataset;
    Row<size_t> labels;

    vector<uint32_t> used_vars;
    verb_print(2, "Dataset size: " << dataset.n_rows << " x " << dataset.n_cols);

    set<uint32_t> added;
    for(const auto& dep_v: input) {
        used_vars.push_back(dep_v);
        added.insert(dep_v);
    }
    for(uint32_t dep_v = 0; dep_v < cnf.nVars(); dep_v++) {
        if (dependency_mat[dep_v][v] == 1 || dep_v == v || added.count(dep_v)) continue;
        used_vars.push_back(dep_v);
    }
    dataset.resize(used_vars.size(), samples.size());

    for(uint32_t i = 0; i < samples.size(); i++) {
        assert(samples[i]->size() == cnf.nVars());
        for(uint32_t k = 0; k < used_vars.size(); k++) {
            const uint32_t dep_v = used_vars[k];
            dataset(k, i) = lbool_to_bool((*samples[i])[dep_v]);
        }
    }
    labels.resize(samples.size());
    for(uint32_t i = 0; i < samples.size(); i++) labels[i] = lbool_to_bool((*samples[i])[v]);
    double train_error;
    if (samples.empty()) {
        var_to_formula[v] = fh->constant_formula(true);
        train_error = 0.0;
    } else {
        // Create the RandomForest object and train it on the training data.
        //
        //  All Available Parameters to Reduce Overfitting:
          /* 1. minimumLeafSize (default: 10) */
          /*   - Minimum number of points in each leaf node */
          /*   - Increase to reduce overfitting (e.g., 20, 50, 100) */
          /* 2. minimumGainSplit (default: 1e-7) */
          /*   - Minimum gain required for a node to split */
          /*   - Increase to reduce overfitting (e.g., 0.001, 0.01, 0.05) */
          /*   - Must be in range (0, 1) */
          /* 3. maximumDepth (default: 0 = unlimited) */
          /*   - Maximum depth of the tree */
          /*   - Set a limit to reduce overfitting (e.g., 5, 10, 15) */
          /* 4. dimensionSelector (optional) */
          /*   - Advanced: Controls which features to consider for splitting */
          /*   - Can use custom strategies (usually leave as default) */

        /* DecisionTree<> r(dataset, labels, 2); */
        // More conservative (less overfitting)
        /* DecisionTree<FitnessFunction, */
        /*              NumericSplitType, */
        /*              CategoricalSplitType, */
        /*              DimensionSelectionType, */
        /*              NoRecursion>::DecisionTree( */
        /*     MatType data, */
        /*     LabelsType labels, */
        /*     const size_t numClasses, */
        /*     const size_t minimumLeafSize, */
        /*     const double minimumGainSplit, */
        /*     const size_t maximumDepth, */
        /*     DimensionSelectionType dimensionSelector) */
        DecisionTree<> r(dataset, labels, 2,
                       mconf.minimumLeafSize,  // minimumLeafSize: require 20+ samples per leaf (default 10)
                       mconf.minGainSplit,     // minimumGainSplit: require k ratio gain to split
                       mconf.maximumDepth);    // maximumDepth: max k levels deep (0 = unlimited)

        // Compute and print the training error.
        Row<size_t> predictions;
        r.Classify(dataset, predictions);
        train_error = arma::accu(predictions != labels) * 100.0 / (double)labels.n_elem;
        verb_print(1, "Training error: " << setprecision(2) << setw(6) << train_error << "%." << " on v: "
                << setw(4) << v+1);
        /* r.serialize(cout, 1); */

        verb_print(2,"[DEBUG] About to call recur for v " << v+1 << " num children: " << r.NumChildren());
        assert(var_to_formula.count(v) == 0);
        var_to_formula[v] = recur(&r, v, used_vars);
    }

    // Forward dependency update
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        if (dependency_mat[i][v]) {
            for(uint32_t j = 0; j < cnf.nVars(); j++) {
                if (input.count(j)) continue;
                dependency_mat[i][j] |= dependency_mat[v][j];
            }
            SLOW_DEBUG_DO(assert(check_map_dependency_cycles()));
        }
    }
    verb_print(4, "Tentative, trained formula for y " << v+1 << ":" << endl << var_to_formula[v]);
    verb_print(2,"Done training variable: " << v+1);
    verb_print(2, "------------------------------");

    return train_error;
}

bool Manthan::has_dependency_cycle_dfs(const uint32_t node, vector<uint8_t>& color, vector<uint32_t>& path) const {
    color[node] = 1; // Mark as being processed (gray)
    path.push_back(node);

    for(uint32_t i = 0; i < dependency_mat[node].size(); i++) {
        if (dependency_mat[node][i] == 0) continue; // No dependency

        if (color[i] == 1) {
            // Found a back edge - cycle detected
            path.push_back(i);
            return true;
        } else if (color[i] == 0) {
            if (has_dependency_cycle_dfs(i, color, path)) {
                return true;
            }
        }
    }

    path.pop_back();
    color[node] = 2; // Mark as completely processed (black)
    return false;
}

bool Manthan::check_map_dependency_cycles() const {
    if (dependency_mat.empty()) return true;

    const uint32_t n = dependency_mat.size();
    vector<uint8_t> color(n, 0); // 0=white (unvisited), 1=gray (processing), 2=black (done)
    vector<uint32_t> cycle_path;

    for(uint32_t i = 0; i < n; i++) {
        if (color[i] == 0) {
            cycle_path.clear();
            if (has_dependency_cycle_dfs(i, color, cycle_path)) {
                // Found a cycle, print it
                cout << "c o [ERROR] Cycle detected in dependency_mat: ";
                for(const auto& v: cycle_path) {
                    cout << v+1 << " -> ";
                }
                cout << "(back to " << cycle_path[cycle_path.size()-1]+1 << ")" << endl;

                // Print detailed dependency information
                cout << "c o [ERROR] Cycle details:" << endl;
                for(size_t j = 0; j < cycle_path.size()-1; j++) {
                    uint32_t from = cycle_path[j];
                    uint32_t to = cycle_path[j+1];
                    cout << "c o   Variable " << from+1 << " depends on " << to+1 << endl;
                }
                return false;
            }
            assert(cycle_path.empty());
        }
    }
    return true;
}

void Manthan::get_incidence() {
    incidence.clear();
    incidence.resize(cnf.nVars(), 0);
    for(const auto& cl: cnf.get_clauses()) {
        for(const auto& l: cl) incidence[l.var()]++;
    }
}
