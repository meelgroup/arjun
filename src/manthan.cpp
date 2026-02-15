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
#include <memory>
#include <mlpack/methods/decision_tree/decision_tree.hpp>
#include <treedecomp/IFlowCutter.hpp>
#include <treedecomp/graph.hpp>
#include <vector>
#include <array>
#include <algorithm>
#include <ranges>
#include "constants.h"
#include "src/metasolver2.h"
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
using std::make_unique;

using namespace ArjunInt;
using namespace ArjunNS;
using namespace CMSat;

// good: benchmarks-qdimacs/small-bug1-fixpoint-10.qdimacs.cnf
// also good (some repair): benchmarks-qdimacs/amba2f9n.sat.qdimacs.cnf
// slow (actually, correct on 1st try at 4e7a4cea5b8a994044466578751ff229b514e747 with --bve 0 --ctxsolver 1 --samples 1000):
//     benchmarks-qdimacs/bobsmcodic_all_bit_differing_from_cycle.qdimacs.cnf
// many repairs, does finish: benchmarks-qdimacs/stmt32_329_378.qdimacs.cnf
// many-many repairs, does finish: benchmarks-qdimacs/sdlx-fixpoint-10.qdimacs.cnf
// no repair, learning/mbve does it: benchmarks-qdimacs/rankfunc57_unsigned_64.qdimacs.cnf
// interesting, does not finish, but fast: benchmarks-qdimacs/query48_exquery_1344n.qdimacs.cnf

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

template<typename S>
void Manthan::inject_cnf(S& s) const {
    s.new_vars(cnf.nVars());
    for(const auto& c: cnf.get_clauses()) s.add_clause(c);
    for(const auto& c: cnf.get_red_clauses()) s.add_red_clause(c);
}

vector<sample> Manthan::get_cmsgen_samples(const uint32_t num) {
    verb_print(1, "[manthan] Getting " << num << " CMSGen samples...");

    const double my_time = cpuTime();
    SATSolver solver_samp;
    solver_samp.set_seed(conf.seed);
    inject_cnf(solver_samp);
    solver_samp.set_up_for_sample_counter(mconf.sampler_fixed_conflicts);

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
            if (0.35 < p && p < 0.65 && 0.35 < q && q < 0.65) {
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
        auto ret = solver_samp.solve();
        assert(ret == l_True);
        assert(solver_samp.get_model().size() == cnf.nVars());
        samples.push_back(solver_samp.get_model());
    }
    verb_print(1, "[manthan] CMSGen got " << samples.size() << " samples. Biased: " << (bool)mconf.do_biased_sampling
            << " T: " << setprecision(2) << std::fixed << (cpuTime() - my_time));
    return samples;
}

vector<sample> Manthan::get_samples_ccnr(const uint32_t num) {
    const double my_time = cpuTime();
    verb_print(1, "[manthan] Getting " << num << " CCNR samples...");

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
        int res = ls_s.local_search(nullptr, mems, "c o", 50LL*1000);
        if (res) {
          s.clear();
          s.resize(cnf.nVars(), l_Undef);
          for(uint32_t i = 0; i < cnf.nVars(); i++) s[i] = ls_s._solution[i+1] ? l_True : l_False;
          samples.push_back(s);
        }
    }

    verb_print(1, "[manthan] CCNR got " << samples.size() << " / " << num << " samples. T: "
            << setprecision(2) << std::fixed << (cpuTime() - my_time));
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
            set_depends_on(d, v);
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
        FHolder<MetaSolver2>::Formula f;

        // Get the original variable number
        const auto orig = new_to_orig.at(v);
        const uint32_t v_orig = orig.var();
        const auto& aig = cnf.get_def(v_orig);
        assert(aig != nullptr);

        // Create a lambda to transform AIG to CNF using the transform function
        std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> aig_to_cnf_visitor =
          [&](AIGT type, const uint32_t var_orig, const bool neg, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                return neg ? ~fh->get_true_lit() : fh->get_true_lit();
            }

            if (type == AIGT::t_lit) {
                const Lit lit_new = cnf.orig_to_new_lit(Lit(var_orig, neg));
                const Lit result_lit = map_y_to_y_hat(lit_new);
                return result_lit;
            }

            if (type == AIGT::t_and) {
                const Lit l_lit = *left;
                const Lit r_lit = *right;

                // Create fresh variable for AND gate
                cex_solver.new_var();
                const Lit and_out = Lit(cex_solver.nVars() - 1, false);
                helpers.insert(and_out.var());

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
        const Lit out_lit = AIG::transform<Lit>(aig, aig_to_cnf_visitor, cache);
        f.out = out_lit ^ orig.sign();
        map<aig_ptr, aig_ptr> aig_cache;
        if (mconf.bve_deep_substitute) {
            f.aig = AIG::transform<aig_ptr>(aig,
              [&](AIGT type, const uint32_t var, const bool neg, const aig_ptr* left, const aig_ptr* right) -> aig_ptr {
                if (type == AIGT::t_const) {
                    return neg ? aig_mng.new_const(false) : aig_mng.new_const(true);
                }
                if (type == AIGT::t_lit) {
                    const auto l = cnf.orig_to_new_lit(Lit(var, neg));
                    return AIG::new_lit(l);
                }
                if (type == AIGT::t_and) {
                    return AIG::new_and(*left, *right, neg);
                }
                assert(false && "Unhandled AIG type in visitor");
                exit(EXIT_FAILURE);
              }, aig_cache);
        } else {
            f.aig = nullptr; // we won't need it.
        }
        assert(var_to_formula.count(v) == 0);
        var_to_formula[v] = f;
    }
    SLOW_DEBUG_DO(assert(check_functions_for_y_vars()));
}

// This adds (and re-numbers) the deep-copied AIGs to a fresh copy of the CNF, then checks if the CNF
// has any AIG cycles
bool Manthan::check_aig_dependency_cycles() const {
    // We need to copy these, so we don't accidentally update the original.
    // We deep copy them together in one go, to preserve e.g. cycles
    vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    for(const auto& y: to_define) {
        if (!var_to_formula.count(y)) continue;
        aigs[y] = var_to_formula.at(y).aig;
    }
    auto aigs_copy = AIG::deep_clone_vec(aigs);

    SimplifiedCNF fcnf = cnf;
    fcnf.map_aigs_to_orig(aigs_copy, cnf.nVars(), &y_hat_to_y);
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
        verb_print(1, "[manthan] y-order var " << setw(4) << y+1
            << " BW: " << backward_defined.count(y)
            << "   td_score " << setw(6) << fixed << setprecision(2) << td_score.at(y)
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

void Manthan::print_needs_repair_vars() const {
    if (conf.verb >= 2) {
        cout << "c o [manthan] needs repair vars: ";
        for(const auto& y: y_order) {
            if (needs_repair.count(y) == 0) continue;
            cout << y+1 << (backward_defined.count(y) ? "[BW]" : "") << " ";
        }
        cout << endl;
    }
}

uint32_t Manthan::calc_non_bw_needs_repair() const {
    uint32_t cnt = 0;
    for(const auto& y: needs_repair) {
        if (backward_defined.count(y) == 0) cnt++;
    }
    return cnt;
}

// debug
bool Manthan::ctx_is_sat(const sample& ctx) const {
    assert(ctx.size() > cnf.nVars());
    for(const auto& val: ctx) assert(val != l_Undef);

    SATSolver s;
    inject_cnf(s);
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        const auto val = ctx[i];
        s.add_clause({Lit(i, val == l_False)});
    }
    const auto ret = s.solve();
    assert(ret == l_True);
    verb_print(2,  "[DEBUG] ctx is sat");
    return ret == l_True;
}

// debug
bool Manthan::ctx_y_hat_correct(const sample& ctx) const {
    SATSolver s;
    while (s.nVars() < cex_solver.nVars()) s.new_var();

    // add true lit
    Lit l = fh->get_true_lit();
    s.add_clause({l});

    // Add input
    for(const auto& x: input) {
        const auto val = ctx[x];
        s.add_clause({Lit(x, val == l_False)});
    }


    // Add y_hat definitions
    vector<Lit> tmp;
    for(const auto& y: y_order) {
        const auto& f = var_to_formula.at(y);
        for(const auto& cl: f.clauses) {
            s.add_clause(cl.lits);
        }

        // make y_hat == f.out
        auto form_out = f.out;
        const auto& y_hat = y_to_y_hat.at(y);
        auto y_hat_l = Lit(y_hat, false);
        tmp.clear();
        tmp.push_back(y_hat_l);
        tmp.push_back(~form_out);
        s.add_clause(tmp);
        tmp[0] = ~tmp.at(0);
        tmp[1] = ~tmp.at(1);
        s.add_clause(tmp);
    }

    const auto ret = s.solve();
    assert(ret == l_True);
    const auto& model = s.get_model();
    vector<uint32_t> incorrect;
    for(const auto& y: y_order) {
        const uint32_t y_hat = y_to_y_hat.at(y);

        const auto ctx_y_hat = ctx[y_hat];
        const auto model_y_hat = model[y_hat];
        assert(ctx_y_hat != l_Undef);
        assert(model_y_hat != l_Undef);
        if (ctx_y_hat != model_y_hat) {
            incorrect.push_back(y);
            verb_print(0, "ERROR: ctx for y_hat " << setw(5) << y+1 << ": ctx has "
                << setw(4) << pr(ctx_y_hat) << " but computed y_hat has "
                << setw(4) << pr(model_y_hat));
        }
    }
    assert(incorrect.empty());
    verb_print(2,  "[DEBUG] y_hat ctx is right");
    return true;
}

bool Manthan::check_functions_for_y_vars() const {
    for(const auto& [v, f]  : var_to_formula) {
        for(const auto& cl: f.clauses) {
            for(const auto& l: cl.lits) {
                const uint32_t var = l.var();
                if (input.count(var)) continue;
                bool is_y_hat = y_hats.count(var) == 1;
                bool is_helper = helpers.count(var) == 1;
                bool is_true = var == fh->get_true_lit().var();
                assert(is_y_hat || is_helper || is_true);
            }
        }
    }
    return true;
}

aig_ptr Manthan::one_level_substitute(Lit l, const uint32_t v, map<uint32_t, aig_ptr>& transformed) {
    if (!transformed.count(l.var())) {
        assert(var_to_formula.count(l.var()) == 1);
        auto aig = var_to_formula.at(l.var()).aig;
        std::map<aig_ptr, aig_ptr> cache;
        auto aig2 = AIG::deep_clone(aig, cache);
        map<aig_ptr, aig_ptr> cache_aig;
        auto aig3 = AIG::transform<aig_ptr>(
          aig2,
          [&](AIGT type, const uint32_t var, const bool neg, const aig_ptr* left, const aig_ptr* right) -> aig_ptr {
            if (type == AIGT::t_const) {
                return neg ? aig_mng.new_const(false) : aig_mng.new_const(true);
            }
            if (type == AIGT::t_lit) {
                aig_ptr l_aig = nullptr;
                if (later_in_order(v, var)) {
                    l_aig = AIG::new_lit(Lit(var, neg));
                    set_depends_on(v, var);
                } else {
                    l_aig = aig_mng.new_const(true);
                }
                return l_aig;
            }
            if (type == AIGT::t_and) {
                return AIG::new_and(*left, *right, neg);
            }
            assert(false && "Unhandled AIG type in visitor");
            exit(EXIT_FAILURE);
          }, cache_aig);
        transformed[l.var()] = aig3;
    }
    auto aig = transformed.at(l.var());
    if (l.sign()) aig = AIG::new_not(aig);
    return aig;
}

// Prefer FALSE, i.e. it should be false unless we have evidence otherwise
// Hence, we only care about clauses where v appears positively
void Manthan::bve_and_substitute() {
    const double start_time = cpuTime();
    map<Lit, aig_ptr> lit_to_aig;

    auto get_aig = [&](const Lit l) {
      if (lit_to_aig.count(l)) return lit_to_aig.at(l);
      aig_ptr aig = AIG::new_lit(l);
      lit_to_aig[l] = aig;
      return aig;
    };
    vector<vector<uint32_t>> lit_to_cls(cnf.nVars()*2);
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        lit_to_cls[Lit(i, false).toInt()].clear();
        lit_to_cls[Lit(i, true).toInt()].clear();
    }
    for(uint32_t i = 0; i < cnf.get_clauses().size(); i++) {
        const auto& cl = cnf.get_clauses()[i];
        for(const auto& l: cl) {
            if (!to_define.count(l.var())) continue; // no need for these
            lit_to_cls[l.toInt()].push_back(i);
        }
    }

    uint32_t num_done = 0;
    for(const auto& y: y_order) {
        if (!to_define.count(y)) continue;
        assert(var_to_formula.count(y) == 0);

        FHolder<MetaSolver2>::Formula f;
        map<uint32_t, aig_ptr> transformed;

        // For optimizing which side of the BVE to take
        uint32_t num_pos = 0;
        uint32_t num_neg = 0;
        for(const auto& cl: cnf.get_clauses()) {
            for(const auto& l: cl) {
                if (l.var() == y) {
                    if (l.sign()) num_neg++;
                    else num_pos++;
                    break;
                }
            }
        }
        verb_print(2, "[manthan] bve var " << setw(5) << y+1
            << " pos occur: " << setw(6) << num_pos
            << " neg occur: " << setw(6) << num_neg);

        const bool sign = (num_pos >= num_neg);
        /* const bool sign = false; */
        aig_ptr overall = nullptr;
        for(const auto& at: lit_to_cls[Lit(y, sign).toInt()]) {
            const auto& cl = cnf.get_clauses()[at];
            bool todo = false;
            for(const auto& l: cl) {
                if (l.var() == y && l.sign() == sign) {
                    todo = true;
                    break;
                }
            }
            if (!todo) continue;
            aig_ptr current = nullptr; //aig_mng.new_const(true);
            for(const auto& l: cl) {
                if (l.var() == y) continue;
                aig_ptr aig = nullptr;
                if (later_in_order(y, l.var())) {
                    aig = get_aig(~l);
                    set_depends_on(y, l);
                    if (current == nullptr) current = aig;
                    else current = AIG::new_and(current, aig);
                } else if (y == l.var()) {
                    assert(false);
                } else {
                    if (mconf.bve_deep_substitute) {
                        assert(false && "not tested");
                        aig = one_level_substitute(l, y, transformed);
                        if (current == nullptr) current = aig;
                        else current = AIG::new_and(current, aig);
                    } else {
                        //keep current as-is, since we AND with TRUE
                    }
                }
            }
            if (current == nullptr) current = aig_mng.new_const(true);
            if (overall == nullptr) overall = current;
            else overall = AIG::new_or(overall, current);
        }
        if (overall == nullptr) overall = aig_mng.new_const(true);
        if (sign) overall = AIG::new_not(overall);

        f.aig = overall;
        var_to_formula[y] = f;
        num_done++;
        if (num_done % 50 == 49) {
            verb_print(1, "[manthan] done with BVE "
                << " funs: " << setw(6) << num_done
                << " funs/s: " << setw(6) << fixed << setprecision(2) << safe_div(num_done,(cpuTime()-start_time))
                << " T: " << setw(5) << (cpuTime()-start_time)
                << " mem: " << memUsedTotal()/(1024.0*1024.0) << " MB");
        }
    }

    for(const auto& v: y_order) {
        if (!to_define.count(v)) continue;
        FHolder<MetaSolver2>::Formula& f = var_to_formula.at(v);
        assert(f.out == lit_Error);
        assert(f.clauses.empty());

        // Transform AIG to CNF using the transform function
        std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> aig_to_cnf_visitor =
          [&](AIGT type, const uint32_t var, const bool neg, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                return neg ? ~fh->get_true_lit() : fh->get_true_lit();
            }

            if (type == AIGT::t_lit) {
                Lit l(var, neg);
                const Lit result_lit = map_y_to_y_hat(l);
                return result_lit;
            }

            if (type == AIGT::t_and) {
                const Lit l_lit = *left;
                const Lit r_lit = *right;

                // Create fresh variable for AND gate
                cex_solver.new_var();
                const Lit and_out = Lit(cex_solver.nVars() - 1, false);
                helpers.insert(and_out.var());

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
        const Lit out_lit = AIG::transform<Lit>(f.aig, aig_to_cnf_visitor, cache);
        f.out = out_lit;
    }

    assert(check_aig_dependency_cycles());
    verb_print(1, COLYEL "[manthan] BVE and substitute done."
        << " funs: " << setw(6) << to_define.size()
        << " funs/s: " << setw(6) << fixed << setprecision(2) << safe_div(num_done,(cpuTime()-start_time))
        << " T: " << setw(5) << (cpuTime()-start_time)
        << " mem: " << memUsedTotal()/(1024.0*1024.0) << " MB");
}

std::unique_ptr<TWD::Graph> Manthan::build_primal_graph() {
    auto primal = make_unique<TWD::Graph>(cnf.nVars());
    for(const auto& cl: cnf.get_clauses()) {
      for(uint32_t i = 0; i < cl.size(); i++) {
        for(uint32_t i2 = i+1; i2 < cl.size(); i2++) {
            assert(cl[i].var() != cl[i2].var() &&
                    "Tree decomposition cannot handle repeated variables in a clause");
          primal->addEdge(cl[i].var(), cl[i2].var());
        }
      }
    }

    verb_print(1, "[manthan] Primal graph nodes: " << primal->numNodes()
            << " edges: " << primal->numEdges());
    return primal;
}

void Manthan::full_train() {
    // Sampling
    verb_print(1, "[manthan] Starting training. Manthan Config. "
        << "do_filter_samples=" << mconf.do_filter_samples
        << ", num_samples=" << mconf.num_samples
        << ", minimumLeafSize=" << mconf.minimumLeafSize
        << ", minGainSplit=" << mconf.minGainSplit
        << ", maximumDepth=" << mconf.maximumDepth);
    double samp_start_time = cpuTime();
    vector<sample> samples = get_cmsgen_samples(mconf.num_samples);
    {
        vector<sample> samples2 = get_samples_ccnr(mconf.num_samples_ccnr);
        samples.insert(samples.end(), samples2.begin(), samples2.end());
    }
    sampl_time = cpuTime() - samp_start_time;
    verb_print(1, COLYEL "[manthan] Got " << setw(8) << samples.size() << " samples."
        << " samp/var: " << setw(8) << setprecision(2) << std::fixed << sampl_time/(double)to_define.size()
        << " T: " << setprecision(2) << std::fixed << sampl_time);
    sort_all_samples(samples);

    // Training
    const double train_start_time = cpuTime();
    for(const auto& v: y_order) {
        if (backward_defined.count(v)) continue;
        train(samples, v); // updates dependency_mat
    }
    train_time = cpuTime() - train_start_time;
    verb_print(1, COLYEL "[manthan] Training done."
            << " funs: " << setw(6) << to_define.size()
            << " fun/s: " << setw(6) << setprecision(2) << std::fixed << safe_div(to_define.size(), cpuTime() - train_start_time)
            << " T: " << setw(6) << setprecision(2) << std::fixed << train_time
            << " mem: " << memUsedTotal()/(1024.0*1024.0) << " MB");
    assert(check_map_dependency_cycles());
}

SimplifiedCNF Manthan::do_manthan(const uint32_t max_repairs) {
    assert(cnf.get_need_aig() && cnf.defs_invariant());
    assert(mconf.simplify_every > 0 && "Can't give simplify_every=0");
    const double my_time = cpuTime();
    const auto ret = cnf.find_disconnected();
    verb_print(1, "[manthan] Found " << ret.size() << " components");

    if (!mconf.write_manthan_cnf.empty()) cnf.write_simpcnf(mconf.write_manthan_cnf);

    // CNF is divided into:
    // input vars -- original sampling vars
    // defined non-input vars -- vars defined via backward_round_synth
    // to_define vars -- vars that are not defined yet, and not input
    std::tie(input, to_define, backward_defined) = cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_manthan");
    if (to_define.empty()) {
        verb_print(1, "[manthan] No variables to define, returning original CNF");
        return cnf;
    }
    to_define_full.clear();
    to_define_full.insert(to_define.begin(), to_define.end());
    to_define_full.insert(backward_defined.begin(), backward_defined.end());
    fill_dependency_mat_with_backward();
    get_incidence();

    inject_cnf(repair_solver);
    {
        cex_solver.new_vars(cnf.nVars());
        for(const auto& c: cnf.get_clauses()) cex_solver.add_clause(c, true);
        for(const auto& c: cnf.get_red_clauses()) cex_solver.add_red_clause(c, true);
    }
    fh = std::make_unique<FHolder<MetaSolver2>>(&cex_solver);
    create_vars_for_y_hats();
    add_not_f_x_yhat();
    verb_print(2, "True lit in solver_train: " << fh->get_true_lit());
    verb_print(2, "[manthan] After fh creation: solver_train.nVars() = " << cex_solver.nVars() << " cnf.nVars() = " << cnf.nVars());

    order_vars();
    fill_var_to_formula_with_backward();
    if (!mconf.manthan_bve) full_train();
    else bve_and_substitute();

    const double repair_start_time = cpuTime();
    for(const auto& v: to_define_full) {
        assert(var_to_formula.count(v) && "All must have a tentative definition");
        updated_y_funcs.push_back(v);
    }

    // Counterexample-guided repair
    bool at_least_one_repaired = true;
    SLOW_DEBUG_DO(assert(check_functions_for_y_vars()));

    while(true) {
        if (num_loops_repair %  40 == 39) {
            verb_print(1, "[manthan] rep: " << setw(6) << tot_repaired
                    << "   loops: "<< setw(6) << num_loops_repair
                    << "   avg rep/loop: " << setprecision(1) << setw(4) << (double)tot_repaired/(num_loops_repair+0.0001)
                    << "   avg conflsz: " << setw(6) << fixed << setprecision(2) << (double)conflict_sizes_sum/(tot_repaired+0.0001)
                    << "   avg need rep: " << setw(6) << fixed << setprecision(2) << (double)needs_repair_sum/(num_loops_repair+0.0001)
                    << "   cache-hit: " << setw(3) << fixed << setprecision(0) << repair_solver.get_cache_hit_rate()*100.0 << "%"
                    << "   T: " << setprecision(2) << fixed << setw(7) << cpuTime()-repair_start_time
                    << "   rep/s: " << setprecision(4) << safe_div(tot_repaired,cpuTime()-repair_start_time) << setprecision(2));
        }
        assert(at_least_one_repaired);
        at_least_one_repaired = false;
        num_loops_repair++;
        inject_formulas_into_solver();
        sample ctx;
        const bool finished = get_counterexample(ctx);
        if (finished) break;
        if (tot_repaired > max_repairs) {
            const double repair_time = cpuTime() - repair_start_time;
            verb_print(1, COLRED "[manthan] Reached max repairs without finishing "
                << "   loops: "<< setw(6) << num_loops_repair
                << "   avg rep/loop: " << setprecision(1) << setw(4) << (double)tot_repaired/(num_loops_repair+0.0001)
                << "   avg conflsz: " << setw(6) << fixed << setprecision(2) << (double)conflict_sizes_sum/(tot_repaired+0.0001)
                << "   avg need rep: " << setw(6) << fixed << setprecision(2) << (double)needs_repair_sum/(num_loops_repair+0.0001)
                << "   cache-hit: " << setw(3) << fixed << setprecision(0) << repair_solver.get_cache_hit_rate()*100.0 << "%"
                << "   T: " << setprecision(2) << fixed << setw(7) << repair_time
                << "   rep/s: " << setw(7) << setprecision(3) << (double)tot_repaired/(repair_time+0.0001) << setprecision(2));
                return cnf;
        }
        print_cnf_debug_info(ctx);
        print_needs_repair_vars();
        SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
        SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));

        const uint32_t old_needs_repair_size = needs_repair.size();
        if (mconf.do_maxsat_better_ctx == -1) {
          // Nothing to do
        } else if (mconf.do_maxsat_better_ctx == 1) {
          find_better_ctx_maxsat(ctx);
        } else {
          find_better_ctx_normal(ctx);
        }
        SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
        SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));
        compute_needs_repair(ctx);
        verb_print(2, "[manthan] finding better ctx done, needs_repair size before vs now: "
              << setw(3) << old_needs_repair_size << " -- " << setw(4) << needs_repair.size());
        print_needs_repair_vars();
        needs_repair_sum += needs_repair.size();

        assert(!needs_repair.empty());
        uint32_t num_repaired = 0;
        while(!needs_repair.empty()) {
            auto y_rep = find_next_repair_var(ctx);
            bool done = repair(y_rep, ctx); // this updates ctx
            if (done) {
                at_least_one_repaired = true;
                num_repaired++;
                tot_repaired++;
                if (mconf.one_repair_per_loop) break;
            } else {
                repair_failed++;
            }
            SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
            SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));
            verb_print(3, "[manthan] finished repairing " << y_rep+1 << " : " << std::boolalpha << done);
        }
        verb_print(2, "[manthan] Num repaired: " << num_repaired << " tot repaired: " << tot_repaired << " num_loops_repair: " << num_loops_repair);
    }

    const double repair_time = cpuTime() - repair_start_time;
    assert(check_map_dependency_cycles());
    verb_print(1, COLYEL "[manthan] rep: " << setw(6) << tot_repaired
        << "   loops: "<< setw(6) << num_loops_repair
        << "   avg rep/loop: " << setprecision(1) << setw(4) << (double)tot_repaired/(num_loops_repair+0.0001)
        << "   avg conflsz: " << setw(6) << fixed << setprecision(2) << (double)conflict_sizes_sum/(tot_repaired+0.0001)
        << "   avg need rep: " << setw(6) << fixed << setprecision(2) << (double)needs_repair_sum/(num_loops_repair+0.0001)
        << "   cache-hit: " << setw(3) << fixed << setprecision(0) << repair_solver.get_cache_hit_rate()*100.0 << "%"
        << "   T: " << setprecision(2) << fixed << setw(7) << repair_time
        << "   rep/s: " << setw(7) << setprecision(3) << (double)tot_repaired/(repair_time+0.0001) << setprecision(2)
        << " DONE");

    // Build final CNF
    vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    for(const auto& y: to_define) {
        assert(var_to_formula.count(y));
        verb_print(3, "Final formula for " << y+1 << ":" << endl << var_to_formula[y]);
        assert(var_to_formula[y].aig != nullptr);
        aigs[y] = var_to_formula[y].aig;
    }
    SimplifiedCNF fcnf = cnf;
    fcnf.map_aigs_to_orig(aigs, cnf.nVars(), &y_hat_to_y);
    assert(verify_final_cnf(fcnf));
    auto [input2, to_define2, backward_defined2] = fcnf.get_var_types(0 | verbose_debug_enabled, "end do_manthan");
    verb_print(1, COLRED "[manthan] Done. "
        << " sampl T: " << setprecision(2) << std::fixed << sampl_time
        << " train T: " << setprecision(2) << std::fixed << train_time
        << " repair T: " << setprecision(2) << std::fixed << repair_time
        << " repairs: " << tot_repaired << " repair failed: " << repair_failed
        << " defined: " << to_define.size() - to_define2.size()
        << " still to define: " << to_define2.size()
        << " T: " << cpuTime()-my_time);
    return fcnf;
}

bool Manthan::verify_final_cnf(const SimplifiedCNF& fcnf) const {
    assert(fcnf.check_aig_cycles());
    auto [input2, to_define2, backward_defined2] = fcnf.get_var_types(0 | verbose_debug_enabled, "verify_final_cnf");
    for(const auto& v: to_define2) {
        cout << "ERROR: var " << v+1 << " not defined in final CNF!" << endl;
        assert(false && "All to-define vars must be defined in final CNF");
    }
    assert(fcnf.get_need_aig() && fcnf.defs_invariant());
    return true;
}

uint32_t Manthan::find_next_repair_var(const sample& ctx) const {
    assert(!needs_repair.empty());
    uint32_t y_rep = std::numeric_limits<uint32_t>::max();
    for(const auto& y: y_order) {
        if (needs_repair.count(y)) {
            assert(ctx[y] != ctx[y_to_y_hat.at(y)]);
            y_rep = y;
            break;
        }
        assert(ctx[y] == ctx[y_to_y_hat.at(y)]);
    }
    assert(y_rep != std::numeric_limits<uint32_t>::max());
    assert(!backward_defined.count(y_rep) && "If all y_hat has been recomputed, the first wrong CANNOT be a BW var");
    return y_rep;
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
    bool ret = find_conflict(y_rep, ctx, conflict);
    if (ret) {
        perform_repair(y_rep, ctx, conflict);
        if (!mconf.one_repair_per_loop) {
            ctx[y_to_y_hat[y_rep]] = ctx[y_rep];
            inject_formulas_into_solver();
            recompute_all_y_hat_cnf(ctx, y_rep);
        }
    }
    compute_needs_repair(ctx);
    print_needs_repair_vars();
    return ret;
}

bool Manthan::find_conflict(const uint32_t y_rep, sample& ctx, vector<Lit>& conflict) {
    const double repair_solver_start_time = cpuTime();

    // F(x,y) & x = ctx(x) && forall_y (y not dependent on v) (y = ctx(y)) & NOT (v = ctx(v))
    // Used to find UNSAT core that will help us repair the function
    vector<Lit> assumps;
    for(const auto& x: input) {
        const Lit l = Lit(x, ctx[x] == l_False);
        assumps.push_back({l});
    }

    // We go through the variables that y_rep does NOT depend on, and assume them to be correct
    for(const auto& y: y_order) {
        if (y == y_rep) break; // beyond this point we don't care
        assert(dependency_mat[y][y_rep] != 1 && "due to ordering, this should not happen. Otherwise y depends on y_rep, but we will repair y_rep potentially with y_rep");
        assert(ctx[y] == ctx[y_to_y_hat[y]]); // they are correct
        const Lit l = Lit(y, ctx[y] == l_False);
        verb_print(3, "assuming " << y+1 << " is " << ctx[y]);
        assumps.push_back({l});
    }

    assert(ctx[y_rep] != ctx[y_to_y_hat[y_rep]] && "before repair, y and y_hat must be different");
    const Lit to_repair = Lit(y_rep, ctx[y_to_y_hat[y_rep]] == l_True);
    assumps.push_back({~to_repair});

    verb_print(2, "assuming reverse for y_rep: " << ~to_repair);
    auto ret = repair_solver.solve(&assumps);
    verb_print(2, "repair_solver finished "
            << " with result: " << (ret == l_True ? "SAT" : (ret == l_False ? "UNSAT" : "UNKNOWN"))
            << " in T: " << cpuTime()-repair_solver_start_time);
    assert(ret != l_Undef);
    if (ret == l_True) {
        verb_print(2, "Repair cost is 0 for y: " << y_rep+1);
        for(const auto& y: to_define_full) ctx[y] = repair_solver.get_model()[y];
        assert(ctx[y_rep] == ctx[y_to_y_hat[y_rep]]);
        return false;
    }
    conflict = repair_solver.get_conflict();
    assert(std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end() &&
        "to_repair literal must be in conflict");

    verb_print(2, "find_conflict conflict: " << conflict);
    if (conflict.size() == 1) {
        verb_print(2, "[manthan] conflict size 1, must flip value, always");
        conflict.clear();
        return true;
    }

    uint32_t orig_size = conflict.size();
    const double minimize_start_time = cpuTime();
    if (conflict.size() > 1 && mconf.do_minimize_conflict) {
        minimize_conflict(conflict, assumps, to_repair);
        assert(std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end() &&
            "to_repair literal must be in conflict");
    }
    if (conflict.size() == 1) {
        verb_print(2, "[manthan] conflict size 1, must flip value, always");
        conflict.clear();
        return true;
    }

    auto now_end = std::remove_if(conflict.begin(), conflict.end(),
                [&](const Lit l){ return l == to_repair; });
    conflict.erase(now_end, conflict.end());
    verb_print(2, "[manthan] minim. Removed: " << setw(3) << (orig_size - conflict.size())
            << " from conflict, now size: " << setw(3) << conflict.size()
            << " repair cache size: " << setw(8) << repair_solver.cache_size()/1000 << "K"
            << " repair cache hit rate: " << setw(5) << fixed << setprecision(0) << repair_solver.get_cache_hit_rate()*100.0 << "%"
            << " T: " << setw(5) << setprecision(2) << cpuTime()-minimize_start_time);
    return true;
}

void Manthan::minimize_conflict(vector<Lit>& conflict, vector<Lit>& assumps, const Lit to_repair) {
    bool removed_any = true;
    set<Lit> dont_remove;
    dont_remove.insert(to_repair);
    while(removed_any) {
        std::shuffle(conflict.begin(), conflict.end(), mtrand);
        removed_any = false;
        for(const auto& try_rem: conflict) {
            if (dont_remove.count(try_rem)) continue;
            verb_print(3, "Trying to remove conflict literal: " << try_rem);
            assumps.clear();
            for(const auto& l: conflict) {
                if (l == try_rem) continue;
                assumps.push_back(~l);
            }
            release_assert(assumps.size() == conflict.size()-1);
            auto ret2 = repair_solver.solve(&assumps);
            if (ret2 == l_True) {
                dont_remove.insert(try_rem);
                verb_print(3, "[manthan] conf minim. Cannot remove conflict literal: "
                        << setw(5) << try_rem << " -- it leads to SAT");
                continue;
            }
            const uint32_t sz_before = conflict.size();
            conflict = repair_solver.get_conflict();
            auto it = std::find(conflict.begin(), conflict.end(), to_repair);
            if (it == conflict.end()) {
                // leads to conflict without literal to repair
                dont_remove.insert(try_rem);
                continue;
            }
            removed_any = true;
            verb_print(3, "[manthan] conf minim. Removed conflict literal: " << setw(5) << try_rem
                << " sz ch: " << sz_before - conflict.size());
            break;
        }
    }
}

Lit Manthan::map_y_to_y_hat(const Lit& l) const {
    const uint32_t var = l.var();
    if (input.count(var)) return l;
    assert(to_define_full.count(var));
    const uint32_t y_hat = y_to_y_hat.at(var);
    return Lit(y_hat, l.sign());
}

// Update dependency matrix to say that a depends on b
void Manthan::set_depends_on(const uint32_t a, const uint32_t b) {
    if (dependency_mat[a][b]) return;

    verb_print(3, a+1 << " depends on " << b+1);
    dependency_mat[a][b] = 1;
#ifdef SLOW_DEBUG
    // recursive update
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        dependency_mat[a][i] |= dependency_mat[b][i];
    }
    assert(check_map_dependency_cycles());
#endif
}

void Manthan::perform_repair(const uint32_t y_rep, const sample& ctx, const vector<Lit>& conflict) {
    verb_print(2, "[manthan] Performing repair on " << setw(5) << y_rep+1
            << " with conflict size " << setw(3) << conflict.size());
    assert(backward_defined.count(y_rep) == 0 && "Backward defined should need NO repair, ever");
    conflict_sizes_sum += conflict.size();

    // not (conflict) -> v = ctx(v)
    FHolder<MetaSolver2>::Formula f;

    // CNF part
    vector<Lit> cl;
    cex_solver.new_var();
    auto fresh_l = Lit(cex_solver.nVars()-1, false);
    helpers.insert(fresh_l.var());
    cl.push_back(fresh_l);
    for(const auto& l: conflict) {
        cl.push_back(map_y_to_y_hat(l));
        set_depends_on(y_rep, l);
    }
    f.clauses.push_back(cl);
    for(const auto& l: conflict) {
        cl.clear();
        cl.push_back(~fresh_l);
        cl.push_back(~(map_y_to_y_hat(l)));
        f.clauses.push_back(cl);
    }
    f.out = fresh_l;

    // AIG part
    aig_ptr b1 = nullptr;
    for(const auto& l: conflict) assert(l.var() < cnf.nVars());
    if (conflict.empty()) b1 = aig_mng.new_const(true);
    else {
        b1 = AIG::new_lit(~conflict[0]);
        for(size_t i = 1; i < conflict.size(); i++) {
            auto lit_aig = AIG::new_lit(~conflict[i]);
            b1 = AIG::new_and(b1, lit_aig);
        }
    }
    f.aig = b1;

    // when fresh_l is false, confl is satisfied
    verb_print(4, "Original formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    verb_print(4, "Branch formula. When this is true, H is wrong:" << endl << f);
    var_to_formula[y_rep] = fh->compose_ite(fh->constant_formula(ctx[y_rep] == l_True),
            var_to_formula[y_rep], f, helpers);
    updated_y_funcs.push_back(y_rep);
    verb_print(2, "repaired formula for " << y_rep+1 << " with " << conflict.size() << " vars");
    verb_print(4, "repaired formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    //We fixed the ctx on this variable
    assert(check_map_dependency_cycles());
}

void Manthan::learn_order() {
    assert(y_order.empty());
    verb_print(2, "[manthan] Fixing LEARN order...");
    vector<uint32_t> sorted(to_define_full.begin(), to_define_full.end());
    vector<double> score(cnf.nVars(), 0.0);
    auto mysorter = [&](const uint32_t a, const uint32_t b) -> bool {
        if (td_score[a] != td_score[b]) return td_score[a] < td_score[b];
        if (incidence[a] != incidence[b]) return incidence[a] > incidence[b];
        return a < b;
    };
    std::sort(sorted.begin(), sorted.end(), mysorter);
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

    assert(y_order.size() == to_define_full.size());
}

bool Manthan::cluster_order() {
    assert(y_order.empty());
    verb_print(2, "[manthan] Fixing CLUSTER order...");

    auto primal = build_primal_graph();
    if (primal->numEdges() == 0) {
        verb_print(1, "[td] Primal graph has no edges, skipping TD");
        return false;
    }

    if (mconf.do_td_contract) {
      for(const auto& i: input) {
        primal->contract(i, mconf.td_max_edges*100);
        if (primal->numEdges() > mconf.td_max_edges*100 ) break;
      }
    }

    if (primal->numEdges() > mconf.td_max_edges) {
        verb_print(1, "[td] Too many edges, " << primal->numEdges() << " skipping TD");
        return false;
    }

    map<uint32_t, uint32_t> old_to_new;
    map<uint32_t, uint32_t> new_to_old;
    std::unique_ptr<TWD::Graph> primal_alt = nullptr;
    uint32_t nodes;
    if (mconf.do_td_contract) {
        primal_alt = make_unique<TWD::Graph>(to_define_full.size());
        nodes = to_define_full.size();
        uint32_t idx = 0;
        for(const auto& v: to_define_full) {
            old_to_new[v] = idx;
            new_to_old[idx] = v;
            idx++;
        }
        assert(idx == to_define_full.size());
        for(uint32_t v = 0; v < cnf.nVars(); v++) {
            const auto& adj = primal->get_adj_list()[v];
            if (!to_define_full.count(v)) {
                assert(adj.empty() && "Should have been contracted away");
                continue;
            }
            for(const auto& n: adj) {
                assert(to_define_full.count(n) && "Input vars should have been contracted away");
                primal_alt->addEdge(old_to_new[v], old_to_new[n]);
            }
        }
        primal.reset();
        verb_print(1, "[manthan] Contracted primal graph nodes: " << primal_alt->numNodes()
                << " edges: " << primal_alt->numEdges());
        if (primal_alt->numEdges() == 0) {
            verb_print(1, "[td] Contracted primal graph has no edges, skipping TD");
            return false;
        }
    } else {
        nodes = cnf.nVars();
        uint32_t idx = 0;
        for(uint32_t v = 0; v < cnf.nVars(); v++) {
            old_to_new[v] = idx;
            new_to_old[idx] = v;
            idx++;
        }
        primal_alt = std::move(primal);
    }

    // run FlowCutter
    verb_print(2, "[td-cmp] FlowCutter is running...");
    TWD::IFlowCutter fc(primal_alt->numNodes(), primal_alt->numEdges(), conf.verb);
    fc.importGraph(*primal_alt);

    // Notice that this graph returned is VERY different
    uint64_t td_steps = 1e5;
    int td_lookahead_iters = 900;
    auto tdec = TWD::TreeDecomposition(fc.constructTD(td_steps, td_lookahead_iters));
    tdec.centroid(primal_alt->numNodes(), conf.verb);
    const auto td_width = tdec.width()-1;
    verb_print(2, "[td] FlowCutter FINISHED, TD width: " << td_width);

    const auto& bags = tdec.Bags();
    if (td_width <= 0) {
      verb_print(1, "[td] TD width is 0, ignoring TD");
      return false;
    }

    verb_print(2, "[td] Calculated TD width: " << td_width-1);
    const auto& adj = tdec.get_adj_list();
    if (conf.verb >= 3) {
      for(uint32_t i = 0; i < bags.size(); i++) {
        const auto& b = bags[i];
        cout << "c o [td] bag id: " << setw(3) << i << " contains: ";
        for(const auto& bb: b) cout << setw(4) << bb << " ";
        cout << endl;
      }
      for(uint32_t i = 0; i < adj.size(); i++) {
        const auto& a = adj[i];
        cout << "c o [td] bag " << setw(3) << i << " is adjacent to bags: ";
        for(const auto& nn: a) cout << setw(3) << nn << " ";
        cout << endl;
      }
    }
    int max_dist = 0;
    std::vector<int> dists = tdec.distanceFromCentroid(tdec.numNodes());
    for(uint32_t i = 0; i < (uint32_t)tdec.numNodes(); i++)
        max_dist = std::max(max_dist, dists[i]);

    if (max_dist == 0) {
        verb_print(1, "All projected vars are the same distance, ignoring TD");
        return false;
    }
    assert(to_define_full.size() == (uint32_t)primal_alt->numNodes());
    compute_td_score_using_adj(nodes, bags, adj, new_to_old);
    return true;
}

void Manthan::compute_td_score_using_adj(const uint32_t nodes,
    const std::vector<std::vector<int>>& bags,
    const std::vector<std::vector<int>>& adj,
    const map<uint32_t, uint32_t>& new_to_old) {
  SLOW_DEBUG_DO(
    vector<int> check(nodes, 0);
    for(const auto& b:  bags) for(const auto&v: b) {
      assert(v < (int)nodes);
      check[v]++;
    }
    for(uint32_t i = 0; i < nodes; i++) {
      if (check[i] == 0) cout << "ERROR: vertex " << i << " is not in any bag!" << endl;
    }
    assert(std::all_of(check.begin(), check.end(), [](int i) { return i > 0; }));
  );

  sspp::TreeDecomposition dec(bags.size(), nodes);
  for(uint32_t i = 0; i < bags.size();i++) dec.setBag(i, bags[i]);
  for(uint32_t i = 0; i < adj.size(); i++)
    for(const auto& nn: adj[i]) dec.addEdge(i, nn);

  int centroid = -1;
  auto ord = dec.getOrd(centroid);
  verb_print(1, "[td] centroid bag id: " << centroid << " bag size: " << bags[centroid].size());
  if (!mconf.td_visualize_dot_file.empty()) {
    dec.visualizeTree(mconf.td_visualize_dot_file);
    cout << "c o [td] Wrote tree decomposition to file: " << mconf.td_visualize_dot_file << endl;
    cout << "c o [td] You can convert it to pdf using the command: dot -Tpdf " << mconf.td_visualize_dot_file << " -o td_tree.pdf" << endl;
  }

  assert(ord.size() == nodes);
  int max_ord = 0;
  int min_ord = std::numeric_limits<int>::max();
  for (uint32_t i = 0; i < nodes; i++) {
    max_ord = std::max(max_ord, ord[i]);
    min_ord = std::min(min_ord, ord[i]);
  }
  max_ord -= min_ord;
  assert(max_ord >= 1);

  // Calc td score
  for (uint32_t i = 0; i < nodes; i++) {
    double val = max_ord - (ord[i]-min_ord);
    val /= (double)max_ord;
    assert(val > -0.01 && val < 1.01);
    assert(i+1 < td_score.size());
    const uint32_t old_i = new_to_old.at(i);
    td_score[old_i] = val;
  }
}

// Will order 1st the variables that NOTHING depends on
// Will order LAST the variables that depends on EVERYTHING
void Manthan::order_vars() {
    assert(td_score.empty());
    td_score.resize(cnf.nVars(), 0.0);
    assert(order_val.empty());
    assert(y_order.empty());
    const double my_time = cpuTime();
    verb_print(2, "[manthan] Fixing order " << (mconf.manthan_bve ? "[BVE]" : "[LEARN]") << "...");

    switch(mconf.manthan_order) {
        case 0: learn_order(); break;
        case 1: cluster_order();
                learn_order();
                break;
        case 2: bve_order(); break;
        default: release_assert(false && "Invalid manthan_order");
    }

    // fill order_val
    order_val.resize(cnf.nVars(), -2);
    for(const auto& x: input) order_val[x] = -1;
    for(uint32_t i = 0; i < y_order.size(); i++) order_val[y_order[i]] = i;
    for(const auto& v: order_val) assert(v != -2);

    verb_print(1, "[manthan] Fixed order. T: " << setprecision(2) << fixed << (cpuTime() - my_time)
            << " Final order size: " << y_order.size());
    print_y_order_occur();
}

// Finds the order that minimizes dependencies that need to be broken by BVE system
void Manthan::bve_order() {
    const double my_time = cpuTime();
    assert(y_order.empty());
    auto depends_on = dependency_mat;

    for(const auto& v: to_define) {
        // For optimizing which side of the BVE to take
        uint32_t num_pos = 0;
        uint32_t num_neg = 0;
        for(const auto& cl: cnf.get_clauses()) {
            for(const auto& l: cl) {
                if (l.var()) {
                    if (l.sign()) num_neg++;
                    else num_pos++;
                }
            }
        }
        bool sign = (num_pos >= num_neg);
        /* bool sign = false; */
        for(const auto& cl: cnf.get_clauses()) {
            bool todo = false;
            for(const auto& l: cl) {
                if (l.var() == v && l.sign() == sign) {
                    todo = true;
                    break;
                }
            }
            if (!todo) continue;
            for(const auto& l: cl) {
                if (l.var() == v) continue;
                if (input.count(l.var())) continue;
                depends_on[v][l.var()] = 1;
            }
        }
    }

    uint32_t total_break = 0;
    set<uint32_t> already_fixed;
    while(y_order.size() != to_define_full.size()) {
        uint32_t smallest = std::numeric_limits<uint32_t>::max();
        uint32_t smallest_var = std::numeric_limits<uint32_t>::max();
        for(const auto& y: to_define_full) {
            if (already_fixed.count(y)) continue;

            uint32_t cnt = 0;
            for(uint32_t v = 0; v < cnf.nVars(); v++) {
                if (input.count(v)) continue;
                if (already_fixed.count(v)) continue;
                if (depends_on[y][v] == 1) cnt++;
            }
            if (backward_defined.count(y)) {
                if (cnt == 0) {
                    smallest = cnt;
                    smallest_var = y;
                }
            } else {
                if (cnt < smallest) {
                    smallest = cnt;
                    smallest_var = y;
                }
            }
        }
        assert(smallest_var != std::numeric_limits<uint32_t>::max());
        verb_print(1, "Fixed order of " << setw(5) << smallest_var+1 << " to: " << setw(5) << y_order.size() << " cnt: " << smallest
                << " BW: " << backward_defined.count(smallest_var));
        total_break += smallest;

        assert(!already_fixed.count(smallest_var));
        already_fixed.insert(smallest_var);
        y_order.push_back(smallest_var);
    }
    verb_print(2, "[manthan] BVE order total breaks: " << total_break << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
    assert(y_order.size() == to_define_full.size());
}

void Manthan::find_better_ctx_maxsat(sample& ctx) {
    verb_print(2, "Finding better ctx via maxsat.");
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
        if (!mconf.maxsat_order)
            y_to_y_order_pos[y_order[i]] = i+1;
        else
            y_to_y_order_pos[y_order[i]] = y_order.size()-i;
    }

    // Fix to_define variables that are incorrect via assumptions
    set<Lit> assumps;
    for(const auto& y: y_order) {
        const auto y_hat = y_to_y_hat[y];
        if (ctx[y] == ctx[y_hat]) continue;
        const auto l = Lit(y, ctx[y_hat] == l_False);
        verb_print(3, "[find-better-ctx] put into assumps y= " << l);
        assumps.insert(l);
        int w = y_to_y_order_pos[y];
        s_ctx.addClause(lits_to_ints({l}), w); // want to flip valuation to ctx[y_hat]
    }

    auto ret = s_ctx.solve();
    assert(ret && "must be satisfiable");
    assert(s_ctx.getCost() > 0);
    for(const auto& v: to_define_full) ctx[v] = s_ctx.getValue(v+1) ? l_True : l_False;
}

// Fills needs_repair with vars from y (i.e. output) using normal SAT solver with assumptions
void Manthan::find_better_ctx_normal(sample& ctx) {
    SATSolver s;
    s.new_vars(cnf.nVars());
    verb_print(2, "Finding better ctx via normal SAT solver.");

    // Fix input values
    for(const auto& x: input) {
        assert(ctx[x] != l_Undef && "Input variable must be defined in counterexample");
        const auto l = Lit(x, ctx[x] == l_False);
        s.add_clause({l});
    }

    map<uint32_t, uint32_t> y_to_y_order_pos;
    for(size_t i = 0; i < y_order.size(); i++) {
        if (mconf.maxsat_order)
            y_to_y_order_pos[y_order[i]] = i+1;
        else
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
            s.add_clause({l});
        } else {
            // Incorrect, we want to try to fix this
            uint32_t weight = y_to_y_order_pos[y];
            incorrect_lits.push_back({l, weight});
            verb_print(3, "[find-better-ctx-normal] CTX is INCORRECT on y=" << y+1
                 << " ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat])
                 << " weight=" << weight);
        }
    }
    assert(incorrect_lits.size() == needs_repair.size());
    for(const auto& c: cnf.get_clauses()) s.add_clause(c);

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
        auto ret = s.solve(&assumps);
        if (ret == l_True) {
            // Success! Extract the model
            verb_print(2, "[find-better-ctx-normal] Found satisfying assignment. "
                       << "Could not fix " << cannot_fix.size() << " variables.");
            for(const auto& v: to_define_full) {
                ctx[v] = s.get_model()[v];
            }
            return;
        } else {
            auto conflict = s.get_conflict();
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

void Manthan::create_vars_for_y_hats() {
    for(const auto& y: to_define_full) {
        cex_solver.new_var();
        const uint32_t y_hat = cex_solver.nVars()-1;
        y_to_y_hat[y] = y_hat;
        y_hat_to_y[y_hat] = y;
        y_hats.insert(y_hat);
        verb_print(3, "mapping -- y: " << y+1 << " y_hat: " << y_hat+1);
    }
}

// Adds ~F(x, y_hat), fills y_to_y_hat and y_hat_to_y
void Manthan::add_not_f_x_yhat() {
    vector<Lit> tmp;

    // Adds ~F(x, y_hat)
    vector<Lit> cl_indics; // if true, clause is satisfied, if false, clause is unsatisfied
    vector<Lit> cl;
    for(const auto& cl_orig: cnf.get_clauses()) {
        // Replace y with y_hat in the clause
        cl.clear();
        for(const auto& l: cl_orig) {
            if (to_define_full.count(l.var())) cl.push_back(Lit(y_to_y_hat.at(l.var()), l.sign()));
            else cl.push_back(l);
        }

        cex_solver.new_var();
        uint32_t cl_ind_v = cex_solver.nVars()-1;
        Lit cl_ind(cl_ind_v, false);
        tmp.clear();
        tmp.push_back(~cl_ind);
        for(const auto&l : cl) tmp.push_back(l);
        cex_solver.add_clause(tmp, true);

        for(const auto&l : cl) {
            tmp.clear();
            tmp.push_back(cl_ind);
            tmp.push_back(~l);
            cex_solver.add_clause(tmp, true);
        }
        cl_indics.push_back(cl_ind);
    }
    tmp.clear();
    for(const auto& l: cl_indics) tmp.push_back(~l); // at least one is unsatisfied
    cex_solver.add_clause(tmp, true);
}

void Manthan::inject_formulas_into_solver() {
    SLOW_DEBUG_DO(assert(check_functions_for_y_vars()));

    // Replace y with y_hat
    for(auto& k: updated_y_funcs) {
        auto& form = var_to_formula.at(k);
        for(auto& cl: form.clauses) {
            if (cl.inserted) continue;
            vector<Lit> cl2;
            for(const auto& l: cl.lits) {
                auto v = l.var();
                if (to_define_full.count(v)) { cl2.push_back(Lit(y_to_y_hat[v], l.sign()));}
                else cl2.push_back(l);
            }
            cex_solver.add_clause(cl2);
            cl.inserted = true;
        }
    }

    // Relation between y_hat and form_out
    // when y_hat_to_indic is TRUE, y_hat and form_out are EQUAL
    vector<Lit> tmp;
    for(const auto& y: updated_y_funcs) {
        cex_solver.new_var();
        const uint32_t ind = cex_solver.nVars()-1;

        assert(var_to_formula.count(y));
        for(const auto& cl: var_to_formula[y].clauses) assert(cl.inserted && "All clauses must have been inserted");
        const auto& form_out = var_to_formula[y].out;
        const auto& y_hat = y_to_y_hat[y];

        y_hat_to_indic[y_hat] = ind;
        indic_to_y_hat[ind] = y_hat;
        indic_to_y[ind] = y;
        verb_print(3, "->CTX ind: " << ind+1 << " y_hat: " << y_hat+1  << " form_out: " << form_out);

        // when indic is TRUE, y_hat and form_out are EQUAL
        auto y_hat_l = Lit(y_hat, false);
        auto ind_l = Lit(ind, false);
        tmp.clear();
        tmp.push_back(~ind_l);
        tmp.push_back(y_hat_l);
        tmp.push_back(~form_out);
        cex_solver.add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        cex_solver.add_clause(tmp);

        tmp.clear();
        tmp.push_back(ind_l);
        tmp.push_back(~y_hat_l);
        tmp.push_back(~form_out);
        cex_solver.add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        cex_solver.add_clause(tmp);

        if (backward_defined.count(y)) {
            verb_print(3, "backward defined y, forcing indic to TRUE, since it must be correct");
            cex_solver.add_clause({Lit(ind, false)});
        }
    }
    updated_y_funcs.clear();
}

bool Manthan::get_counterexample(sample& ctx) {
    const double my_time_start = cpuTime();
    needs_repair.clear();
    if (num_loops_repair == 1)
        verb_print(1, "[manthan] Getting counterexample for the first time...");

    vector<Lit> assumps;
    assumps.reserve(y_hat_to_indic.size());
    for(const auto& [y_hat, ind]: y_hat_to_indic) {
        uint32_t y = indic_to_y[ind];
        if (backward_defined.count(y)) continue; // already forced to true
        assumps.push_back(Lit(ind, false));
    }
    assert(assumps.size() == y_order.size() - backward_defined.size());
    verb_print(4, "assumptions: " << assumps);
    cex_solver.set_verbosity(conf.verb <= 0 ? 0 : conf.verb-1);
    if (num_loops_repair == 1 || (num_loops_repair % mconf.simplify_every) == (mconf.simplify_every-1))
        cex_solver.simplify(&assumps);

    /* solver.set_up_for_sample_counter(1000); */
    auto ret = cex_solver.solve(&assumps);
    if (num_loops_repair == 1)
        verb_print(1, "[manthan] First cex_solver ran in T: " << setprecision(2) << cpuTime() - my_time_start);
    else
        verb_print(2, "[manthan] cex_solver ran in T: " << setprecision(2) << cpuTime() - my_time_start);
    assert(ret != l_Undef);
    if (ret == l_True) {
        verb_print(2, COLYEL "[manthan] *** Counterexample found ***");
        ctx = cex_solver.get_model();
        compute_needs_repair(ctx);
        return false;
    } else {
        assert(ret == l_False);
        verb_print(2, "Formula is good!");
        return true;
    }
}

FHolder<MetaSolver2>::Formula Manthan::recur(DecisionTree<>* node, const uint32_t learned_v, const vector<uint32_t>& used_vars, uint32_t depth, uint32_t& max_depth) {
    max_depth = std::max(max_depth, depth);
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
            set_depends_on(learned_v, v);
            v = y_to_y_hat.at(v);
        } else {
            // it's input, so no need to update dependency matrix
            assert(input.count(v) && "If not to_define_full, must be input");
        }

        /* cout << "  -- all-0 goes -> " << node->CalculateDirection(point_0); */
        /* cout << "  -- all-1 goes -> " << node->CalculateDirection(point_1) << endl; */
        assert(node->NumChildren() == 2);
        auto form_0 = recur(&node->Child(0), learned_v, used_vars, depth+1, max_depth);
        auto form_1 = recur(&node->Child(1), learned_v, used_vars, depth+1, max_depth);
        bool val_going_right = node->CalculateDirection(point_1);
        return fh->compose_ite(form_0, form_1, Lit(v, val_going_right), helpers);
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

    if (mconf.do_unique_input_samples) {
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
    point_0.zeros(cnf.nVars());
    point_1.ones(cnf.nVars());

    Mat<uint8_t> dataset;
    Row<size_t> labels;

    vector<uint32_t> used_vars(input.begin(), input.end());
    if (mconf.do_use_all_variables_as_features) {
        for(const auto& y: y_order) {
            if (y == v) break;
            assert(dependency_mat[y][v] != 1);
            used_vars.push_back(y);
        }
    }
    dataset.resize(used_vars.size(), samples.size());
    verb_print(2, "Dataset size: " << dataset.n_rows << " x " << dataset.n_cols);

    for(uint32_t i = 0; i < samples.size(); i++) {
        assert(samples[i]->size() == cnf.nVars());
        for(uint32_t k = 0; k < used_vars.size(); k++) {
            const uint32_t dep_v = used_vars[k];
            dataset(k, i) = lbool_to_bool((*samples[i])[dep_v]);
        }
    }
    labels.resize(samples.size());
    for(uint32_t i = 0; i < samples.size(); i++) labels[i] = lbool_to_bool((*samples[i])[v]);
    const auto num_ones = arma::accu(labels);
    verb_print(2, "Labels distribution for v " << setw(5) <<  v+1 << ": " << setw(6) << num_ones << " ones and "
            << setw(6) << (samples.size() - num_ones) << " zeros");
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
        /* DecisionTree<FitnessFunction,  -- default is GiniGain */
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
        /* r.serialize(cout, 1); */

        verb_print(2,"[DEBUG] About to call recur for v " << v+1 << " num children: " << r.NumChildren());
        assert(var_to_formula.count(v) == 0);
        uint32_t max_depth = 0;
        var_to_formula[v] = recur(&r, v, used_vars, 0, max_depth);
        verb_print(1, "Training error: " << setprecision(2) << setw(6) << train_error << "%."
                << " depth: " << setw(6) << max_depth
                << " ones: " << setprecision(0) << fixed << setw(5) << (double)num_ones/samples.size()*100.0 << "%"
                << " on v: " << setprecision(2) << setw(4) << v+1);
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
    verb_print(2, "Trained formula for y " << v+1 << ":" << endl << var_to_formula[v]);
    verb_print(2, "Done training variable: " << v+1);
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

void Manthan::recompute_all_y_hat_cnf(sample& ctx, const uint32_t y_rep) {
    vector<Lit> assumps;
    assumps.reserve(input.size() + y_order.size() + y_hat_to_indic.size());
    for(const auto& x: input) {
        assumps.push_back(Lit(x, ctx[x] == l_False));
    }
    for(const auto& [y_hat, ind]: y_hat_to_indic) {
        uint32_t y = indic_to_y[ind];
        if (backward_defined.count(y)) continue; // already forced to true
        assumps.push_back(Lit(ind, false));
    }

    lbool ret = cex_solver.solve(&assumps, 1);
    assert(ret == l_True);
    const auto& m = cex_solver.get_model(1);
    for(const auto& y: y_order) {
        uint32_t y_hat = y_to_y_hat.at(y);
        ctx[y_hat] = m[y_hat];
    }
}

void Manthan::recompute_all_y_hat_aig(sample& ctx, const uint32_t y_rep) {
    vector<aig_ptr> defs(ctx.size(), nullptr);
    bool found = false;
    map<aig_ptr, lbool> cache;
    for (const auto& y : y_order) {
        // Only need to recompute after y_rep
        if (!found && y == y_rep) {
            found = true;
            continue;
        }
        assert(var_to_formula.count(y));
        const auto& aig = var_to_formula.at(y).aig;
        assert(aig != nullptr);
        lbool val = AIG::evaluate(ctx, aig, defs, cache);
        assert(val != l_Undef);
        ctx[y_to_y_hat.at(y)] = val;
    }
    verb_print(2, "Recomputed all y_hat values in ctx.");
}

void Manthan::compute_needs_repair(const sample& ctx) {
    assert(ctx[fh->get_true_lit().var()] == l_True);
    needs_repair.clear(); for(const auto& y: to_define_full)
        if (ctx[y] != ctx[y_to_y_hat[y]])
    needs_repair.insert(y);
}
