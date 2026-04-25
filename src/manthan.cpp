/*
 Arjun

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal
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
#include "aig_to_cnf.h"
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>
#include "arjun.h"
#include <cstddef>
#include <cstdlib>
#include <cstdint>
#include <iomanip>
#include <memory>
#include <treedecomp/IFlowCutter.hpp>
#include <treedecomp/graph.hpp>
#include <vector>
#include <array>
#include <algorithm>
#include <ranges>
#include "constants.h"
#include "metasolver2.h"
#include "time_mem.h"
#include "ccnr/ccnr.h"
#include <fstream>
#include <cstdio>
#include <filesystem>
#include "aig_rewrite.h"

#ifdef _WIN32
#  include <process.h>
#  define getpid _getpid
#  define popen  _popen
#  define pclose _pclose
#else
#  include <unistd.h>
#endif

#ifdef EXTRA_SYNTH
#include <armadillo>
#include <mlpack/methods/decision_tree/decision_tree.hpp>
#include "EvalMaxSAT.h"
#include "manthan_learn.h"
#endif

using std::min;
using std::sort;
using std::vector;
using std::array;
using std::set;
using std::unordered_set;
using std::map;
using std::unique_ptr;
using std::string;
using std::setprecision;
using std::fixed;
using std::make_unique;
using std::cout;
using std::endl;
using std::setw;

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

    if (mconf.biased_sampling && mconf.bias_samples > 0) {
        array<vector<double>,2> dist;
        dist[0].resize(cnf.nVars(), 0.0);
        dist[1].resize(cnf.nVars(), 0.0);

        // get biased samples in each direction
        const uint32_t bias_samples = mconf.bias_samples;
        for(int bias = 0; bias <= 1; bias++) {
            for(const auto& y: to_define) {
                double bias_w = bias ? mconf.bias_w_high : (1.0 - mconf.bias_w_high);
                solver_samp.set_lit_weight(Lit(y, false), bias_w);
                solver_samp.set_lit_weight(Lit(y, true), 1.0-bias_w);
            }
            vector<uint32_t> got_ones(cnf.nVars(), 0);
            for (uint32_t i = 0; i < bias_samples; i++) {
                solver_samp.solve();
                assert(solver_samp.get_model().size() == cnf.nVars());

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
            if (mconf.bias_p_low < p && p < mconf.bias_p_high && mconf.bias_p_low < q && q < mconf.bias_p_high) {
              bias = p;
            } else if (q <= mconf.bias_p_low) {
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
    verb_print(1, "[manthan] CMSGen got " << samples.size() << " samples. Biased: " << (bool)mconf.biased_sampling
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

    auto add_this_clause = [&](const vector<Lit>& cl) {
        yals_lits.clear();
        for(auto lit : cl) yals_lits.push_back(lit_to_pl(lit));
        for(auto& lit: yals_lits) {
            ls_s._clauses[cl_num].literals.emplace_back(lit, cl_num);
        }
        cl_num++;
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
    long long int mems = (long long int)(num * mconf.ccnr_mems_per_sample);
    for(uint32_t si = 0; si < num; si++) {
        int res = ls_s.local_search(nullptr, mems, "c o", (long long int)mconf.ccnr_per_call_limit);
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
    release_assert(false && "pr() called with l_Undef");
    return "?"; // unreachable, silences compiler warning
}

void Manthan::rebuild_var_bytemaps() {
    const uint32_t nv = cnf.nVars();
    is_input.assign(nv, 0);
    is_backward_defined.assign(nv, 0);
    is_to_define_full.assign(nv, 0);
    is_to_define.assign(nv, 0);
    is_helper_function.assign(nv, 0);
    for (const auto& v : input) is_input[v] = 1;
    for (const auto& v : backward_defined) is_backward_defined[v] = 1;
    for (const auto& v : to_define_full) is_to_define_full[v] = 1;
    for (const auto& v : to_define) is_to_define[v] = 1;
    for (const auto& v : helper_functions) is_helper_function[v] = 1;
}

void Manthan::fill_dependency_mat_with_backward() {
    dependency_mat.clear();
    dependency_mat.resize(cnf.nVars());
    for(auto& m: dependency_mat) m.resize(cnf.nVars(), 0);

    const auto deps = cnf.compute_dependencies(backward_defined);
    for(const auto& v: to_define_full) {
        assert(input.count(v) == 0);
        set<uint32_t> deps_for_var; // these vars depend on v
        for(const auto& [var, dep_set]: deps) {
            if (dep_set.count(v)) deps_for_var.insert(var);
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
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        for(uint32_t j = 0; j < cnf.nVars(); j++) {
            if (input.count(j)) continue;
            if (dependency_mat[i][j] == 0) continue;

            // i depends on j, so i should depend on everything j depends on
            for(uint32_t k = 0; k < cnf.nVars(); k++) {
                if (input.count(k)) continue;
                if (dependency_mat[j][k] == 1 && dependency_mat[i][k] == 0) {
                    verb_print(0, "ERROR: [fill-dep] transitive: " << i+1 << " depends on " << k+1
                        << " (via " << j+1 << ") -- but WE had to add it!!");
                    return false;
                }
            }
        }
    }
    return true;
}

void Manthan::fill_var_to_formula_with(set<uint32_t>& vars) {
    const auto new_to_orig = cnf.get_new_to_orig_var();

    // Routes AIGToCNF clauses into the per-formula clause list while allocating
    // helper vars in cex_solver (same pattern as the rebuild sink below).
    struct FormulaClauseSink {
        MetaSolver2& solver;
        std::vector<CL>& clauses;
        std::set<uint32_t>& helpers_set;
        void new_var() {
            solver.new_var();
            helpers_set.insert(solver.nVars() - 1);
        }
        [[nodiscard]] uint32_t nVars() const { return solver.nVars(); }
        void add_clause(const std::vector<Lit>& cl) {
            clauses.emplace_back(cl);
        }
    };

    for(const auto& v: vars) {
        FHolder<MetaSolver2>::Formula f;

        const auto orig = new_to_orig.at(v);
        const uint32_t v_orig = orig.var();
        const auto& aig = cnf.get_def(v_orig);
        assert(aig != nullptr);

        // Remap the AIG from original var space into y_hat space and bake in
        // orig.sign(). AIGToCNF consumes raw AIG lit vars, so the y_hat remap
        // must live in the AIG rather than a visit-time hook.
        map<aig_ptr, aig_ptr> aig_remap_cache;
        f.aig = AIG::transform<aig_ptr>(aig,
          [&](AIGT type, const uint32_t var_orig2, const bool neg2,
              const aig_ptr* left2, const aig_ptr* right2) -> aig_ptr {
            if (type == AIGT::t_const) return aig_mng.new_const(!neg2);
            if (type == AIGT::t_lit) {
                const Lit lit_new = cnf.orig_to_new_lit(Lit(var_orig2, neg2));
                const Lit result_lit = map_y_to_y_hat(lit_new);
                return AIG::new_lit(result_lit);
            }
            if (type == AIGT::t_and) return AIG::new_and(*left2, *right2, neg2);
            release_assert(false && "Unhandled AIG type");
          }, aig_remap_cache);
        if (orig.sign()) f.aig = AIG::new_not(f.aig);

        // Encode via the optimized AIGToCNF encoder (k-ary AND/OR fusion, ITE
        // pattern detection, De Morgan flattening, dedup/constant folding)
        // rather than naive pairwise Tseitin.
        FormulaClauseSink sink{cex_solver, f.clauses, helpers};
        ArjunNS::AIGToCNF<FormulaClauseSink> enc(sink);
        enc.set_true_lit(fh->get_true_lit());
        f.out = enc.encode(f.aig);

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
    fcnf.map_aigs_to_orig(aigs_copy, cnf.nVars(), y_hat_to_y);
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
        verb_print(2, "[manthan] y-order var " << setw(4) << y+1
            << " BW: " << backward_defined.count(y)
            << "   td_score " << setw(6) << fixed << setprecision(2) << td_score.at(y)
            << "   pos occur " << setw(6) << pos
            << "   --  neg occur " << setw(6) << neg);
    }
}

void Manthan::print_cnf_debug_info(const sample& ctx) const {
    if (conf.verb >= 3) {
        for(const auto& y: to_define_full) {
            const auto y_hat = y_to_y_hat_fast(y);
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
        const auto& y_hat = y_to_y_hat_fast(y);
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
        const uint32_t y_hat = y_to_y_hat_fast(y);

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
    verb_print(4, "[check] START nVars=" << cex_solver.nVars() << " helpers.size=" << helpers.size());
    for(const auto& [v, f]  : var_to_formula) {
        for(const auto& cl: f.clauses) {
            for(const auto& l: cl.lits) {
                const uint32_t var = l.var();
                if (input.count(var)) continue;
                bool is_y_hat = y_hats.count(var) == 1;
                bool is_helper = helpers.count(var) == 1;
                bool is_true = var == fh->get_true_lit().var();
                if (!(is_y_hat || is_helper || is_true)) {
                    std::cout << "c o [check_functions] BAD var in formula of v=" << (v+1)
                         << ": var=" << (var+1)
                         << " backward_defined=" << (backward_defined.count(var) ? 1 : 0)
                         << " to_define=" << (to_define.count(var) ? 1 : 0)
                         << " to_define_full=" << (to_define_full.count(var) ? 1 : 0)
                         << " helper_functions=" << (helper_functions.count(var) ? 1 : 0)
                         << " cnf.nVars=" << cnf.nVars()
                         << " y_hats.size=" << y_hats.size()
                         << " helpers.size=" << helpers.size()
                         << std::endl;
                    std::cout << "c o [check_functions] cex_solver.nVars=" << cex_solver.nVars() << std::endl;
                    std::cout << "c o [check_functions] true_lit=" << fh->get_true_lit().var()+1 << std::endl;
                }
                assert(is_y_hat || is_helper || is_true);
            }
        }
    }
    return true;
}

// SLOW_DEBUG: build a fresh SAT miter from var_to_formula[y].clauses + .out
// exactly as cex_solver would see them (no indicator gating), asks
// "does there exist an input + formula-consistent y_hat assignment that
// falsifies an orig clause?". UNSAT = synthesis correct. SAT = bug in the
// formula encoding — and since the miter uses the SAME clause set
// cex_solver does (minus the indicators and orig-CNF-over-y-vars), a SAT
// result here means cex_solver itself *should have* found this CEX.
bool Manthan::check_synth_via_clauses(const string& where) const {
    SATSolver s;
    while (s.nVars() < cex_solver.nVars()) s.new_var();
    s.add_clause({fh->get_true_lit()});

    // Orig CNF on x + y (0..cnf.nVars()-1) — same var namespace cex_solver uses.
    for (const auto& c : cnf.get_clauses()) s.add_clause(c);

    // Add every formula's clauses + couple its y_hat to its .out
    // unconditionally (no indicator).
    for (const auto& y : to_define_full) {
        auto it = var_to_formula.find(y);
        if (it == var_to_formula.end()) continue;
        const auto& f = it->second;
        for (const auto& cl : f.clauses) s.add_clause(cl.lits);
        uint32_t y_hat = y_to_y_hat_fast(y);
        s.add_clause({Lit(y_hat, false), ~f.out});
        s.add_clause({Lit(y_hat, true),  f.out});
    }

    // Miter: at least one orig clause, y→y_hat substituted, is FALSE.
    vector<Lit> cl_inds;
    cl_inds.reserve(cnf.get_clauses().size());
    for (const auto& cl_orig : cnf.get_clauses()) {
        vector<Lit> cl_sub;
        cl_sub.reserve(cl_orig.size());
        for (const auto& l : cl_orig) {
            if (to_define_full.count(l.var()))
                cl_sub.push_back(Lit(y_to_y_hat_fast(l.var()), l.sign()));
            else cl_sub.push_back(l);
        }
        s.new_var();
        Lit cl_ind(s.nVars() - 1, false);
        vector<Lit> def_cl{~cl_ind};
        for (auto l : cl_sub) def_cl.push_back(l);
        s.add_clause(def_cl);
        for (auto l : cl_sub) s.add_clause({cl_ind, ~l});
        cl_inds.push_back(cl_ind);
    }
    vector<Lit> at_least_one_unsat;
    at_least_one_unsat.reserve(cl_inds.size());
    for (auto l : cl_inds) at_least_one_unsat.push_back(~l);
    s.add_clause(at_least_one_unsat);

    auto ret = s.solve();
    if (ret == l_True) {
        cout << "c o [via_clauses] @ " << where
             << ": SYNTH WRONG (fresh SAT miter is SAT — cex_solver should have found this CEX)" << endl;
        const auto& m = s.get_model();
        cout << "c o [via_clauses]   inputs:";
        for (uint32_t x : input) cout << " x" << (x+1) << "=" << pr(m[x]);
        cout << endl;
        for (size_t i = 0; i < cl_inds.size() && i < cnf.get_clauses().size(); i++) {
            if (m[cl_inds[i].var()] == l_False) {
                cout << "c o [via_clauses]   first broken orig cl idx=" << i << ":";
                for (const auto& l : cnf.get_clauses()[i]) cout << " " << l;
                cout << endl;
                for (const auto& l : cnf.get_clauses()[i]) {
                    uint32_t v = l.var();
                    if (to_define_full.count(v)) {
                        uint32_t yh = y_to_y_hat_fast(v);
                        cout << "c o [via_clauses]     y=x" << (v+1)
                             << " y_hat_var=" << (yh+1)
                             << " y_hat_val=" << pr(m[yh])
                             << " lit_sign=" << l.sign() << endl;
                    } else {
                        cout << "c o [via_clauses]     free x=" << (v+1)
                             << " val=" << pr(m[v])
                             << " lit_sign=" << l.sign() << endl;
                    }
                }
                break;
            }
        }
        return false;
    }
    return true;
}

// SLOW_DEBUG: same miter, but the formula encoding comes from
// var_to_formula[y].aig (the AIG rep that will eventually become
// cnf.defs[y] after map_aigs_to_orig). If this passes but
// check_synth_via_clauses fails, the AIG and CNF reps of the same formula
// disagree; if this fails but _via_clauses passes, it's likely a leaf-
// substitution issue in the AIG.
bool Manthan::check_synth_via_aig(const string& where) const {
    SATSolver s;
    while (s.nVars() < cnf.nVars()) s.new_var();

    // Shadow y_hat vars (distinct from Manthan's to avoid any interference).
    map<uint32_t, Lit> shadow_y_hat;
    for (uint32_t y : to_define_full) {
        s.new_var();
        shadow_y_hat[y] = Lit(s.nVars() - 1, false);
    }

    // Local true_lit.
    s.new_var();
    Lit true_l(s.nVars() - 1, false);
    s.add_clause({true_l});

    // Orig CNF on x + y (for F(x, y) side).
    for (const auto& c : cnf.get_clauses()) s.add_clause(c);

    // Tseitin-encode each var_to_formula[y].aig onto shadow_y_hats.
    // Leaves: if var is to_define_full, use shadow_y_hat[v]; if it's a
    // (Manthan-internal) y_hat leaf from perform_repair, use the
    // corresponding shadow_y_hat via y_hat_to_y; otherwise treat as raw.
    std::unordered_map<const AIG*, Lit> cache;
    std::function<Lit(const aig_ptr&)> enc_edge = [&](const aig_ptr& n) -> Lit {
        assert(n != nullptr);
        if (n->type == AIGT::t_const) return n.neg ? ~true_l : true_l;
        if (n->type == AIGT::t_lit) {
            uint32_t v = n->var;
            Lit base;
            if (to_define_full.count(v)) {
                base = shadow_y_hat.at(v);
            } else if (y_hat_to_y.count(v)) {
                // AIG leaf is a Manthan y_hat (from perform_repair's
                // lit_to_aig for input/backward_defined vars). For inputs
                // map_y_to_y_hat returns the input var itself, so if we
                // reach here it's backward_defined. Use shadow.
                uint32_t y = y_hat_to_y.at(v).var();
                if (to_define_full.count(y)) base = shadow_y_hat.at(y);
                else base = Lit(v, false);
            } else {
                base = Lit(v, false);
            }
            return n.neg ? ~base : base;
        }
        assert(n->type == AIGT::t_and);
        auto it = cache.find(n.get());
        if (it != cache.end()) return n.neg ? ~it->second : it->second;
        Lit lc = enc_edge(n->l);
        Lit rc = enc_edge(n->r);
        s.new_var();
        Lit out(s.nVars() - 1, false);
        s.add_clause({~out, lc});
        s.add_clause({~out, rc});
        s.add_clause({out, ~lc, ~rc});
        cache[n.get()] = out;
        return n.neg ? ~out : out;
    };
    for (const auto& y : to_define_full) {
        auto it = var_to_formula.find(y);
        if (it == var_to_formula.end()) continue;
        const auto& f = it->second;
        if (f.aig == nullptr) continue;
        Lit out = enc_edge(f.aig);
        s.add_clause({~shadow_y_hat.at(y), out});
        s.add_clause({shadow_y_hat.at(y), ~out});
    }

    // Miter: at least one orig clause, y→shadow_y_hat substituted, is FALSE.
    vector<Lit> cl_inds;
    cl_inds.reserve(cnf.get_clauses().size());
    for (const auto& cl_orig : cnf.get_clauses()) {
        vector<Lit> cl_sub;
        cl_sub.reserve(cl_orig.size());
        for (const auto& l : cl_orig) {
            if (shadow_y_hat.count(l.var()))
                cl_sub.push_back(shadow_y_hat.at(l.var()) ^ l.sign());
            else cl_sub.push_back(l);
        }
        s.new_var();
        Lit cl_ind(s.nVars() - 1, false);
        vector<Lit> def_cl{~cl_ind};
        for (auto l : cl_sub) def_cl.push_back(l);
        s.add_clause(def_cl);
        for (auto l : cl_sub) s.add_clause({cl_ind, ~l});
        cl_inds.push_back(cl_ind);
    }
    vector<Lit> at_least_one_unsat;
    at_least_one_unsat.reserve(cl_inds.size());
    for (auto l : cl_inds) at_least_one_unsat.push_back(~l);
    s.add_clause(at_least_one_unsat);

    auto ret = s.solve();
    if (ret == l_True) {
        cout << "c o [via_aig] @ " << where
             << ": AIG-based synth check WRONG (CEX exists per .aig encoding)" << endl;
        const auto& m = s.get_model();
        cout << "c o [via_aig]   inputs:";
        for (uint32_t x : input) cout << " x" << (x+1) << "=" << pr(m[x]);
        cout << endl;
        for (size_t i = 0; i < cl_inds.size() && i < cnf.get_clauses().size(); i++) {
            if (m[cl_inds[i].var()] == l_False) {
                cout << "c o [via_aig]   first broken orig cl idx=" << i << ":";
                for (const auto& l : cnf.get_clauses()[i]) cout << " " << l;
                cout << endl;
                break;
            }
        }
        return false;
    }
    return true;
}

// SLOW_DEBUG: for each y in var_to_formula, prove that evaluating f.aig
// (in y-space, with its leaves remapped into y_hat-space via map_y_to_y_hat)
// yields the same value as f.out given the f.clauses constraints. Does a
// pairwise miter per formula, so when it fires we know exactly which y's
// AIG/CNF reps diverge.
bool Manthan::check_aig_matches_clauses_per_formula(const string& where) const {
    for (const auto& y : to_define_full) {
        auto it = var_to_formula.find(y);
        if (it == var_to_formula.end()) continue;
        const auto& f = it->second;
        if (f.aig == nullptr) continue;

        SATSolver s;
        while (s.nVars() < cex_solver.nVars()) s.new_var();
        s.add_clause({fh->get_true_lit()});
        // Add ALL formulas' clauses (not just this one) because
        // bve_and_substitute shares helper vars across formulas via the
        // persistent AIGToCNF encoder — a helper referenced in this f.out
        // may be defined in a different formula's .clauses.
        for (const auto& [yy, ff] : var_to_formula) {
            for (const auto& cl : ff.clauses) s.add_clause(cl.lits);
        }

        // Tseitin-encode f.aig on top of the SAME var namespace, mapping
        // leaves exactly as bve_and_substitute/perform_repair would (so we
        // get a lit that represents the AIG's value over y_hat vars).
        std::unordered_map<const AIG*, Lit> cache;
        std::function<Lit(const aig_ptr&)> enc_edge = [&](const aig_ptr& n) -> Lit {
            assert(n != nullptr);
            if (n->type == AIGT::t_const) {
                Lit t = fh->get_true_lit();
                return n.neg ? ~t : t;
            }
            if (n->type == AIGT::t_lit) {
                uint32_t v = n->var;
                Lit base;
                // For to_define_full: map to y_hat exactly like
                // bve_and_substitute's transform does.
                if (to_define_full.count(v)) base = Lit(y_to_y_hat_fast(v), false);
                else base = Lit(v, false);
                return n.neg ? ~base : base;
            }
            assert(n->type == AIGT::t_and);
            auto ci = cache.find(n.get());
            if (ci != cache.end()) return n.neg ? ~ci->second : ci->second;
            Lit lc = enc_edge(n->l);
            Lit rc = enc_edge(n->r);
            s.new_var();
            Lit out(s.nVars() - 1, false);
            s.add_clause({~out, lc});
            s.add_clause({~out, rc});
            s.add_clause({out, ~lc, ~rc});
            cache[n.get()] = out;
            return n.neg ? ~out : out;
        };
        Lit aig_val = enc_edge(f.aig);

        // Miter: aig_val XOR f.out — is there an assignment where they
        // differ? If yes, the two reps disagree.
        s.new_var();
        Lit diff(s.nVars() - 1, false);
        // diff ↔ (aig_val XOR f.out)
        s.add_clause({~diff, aig_val, f.out});
        s.add_clause({~diff, ~aig_val, ~f.out});
        s.add_clause({diff, aig_val, ~f.out});
        s.add_clause({diff, ~aig_val, f.out});
        s.add_clause({diff});  // force diff = true

        auto ret = s.solve();
        if (ret == l_True) {
            cout << "c o [aig_vs_clauses] @ " << where
                 << ": y=" << (y+1)
                 << " AIG and CNF reps DIVERGE (both representations disagree on some input)"
                 << endl;
            cout << "c o [aig_vs_clauses]   y_hat_var=" << (y_to_y_hat_fast(y)+1)
                 << " f.out=" << f.out
                 << " aig.type=" << (int)f.aig->type
                 << " aig.neg=" << f.aig.neg
                 << " bw_def=" << backward_defined.count(y)
                 << " to_define=" << to_define.count(y)
                 << " helper_func=" << helper_functions.count(y)
                 << " f.clauses.size=" << f.clauses.size()
                 << endl;
            const auto& m = s.get_model();
            cout << "c o [aig_vs_clauses]   inputs:";
            for (uint32_t x : input) cout << " x" << (x+1) << "=" << pr(m[x]);
            cout << endl;
            auto lit_val = [&](Lit l) -> lbool {
                lbool v = m[l.var()];
                if (v == l_Undef) return l_Undef;
                bool truthy = (v == l_True);
                if (l.sign()) truthy = !truthy;
                return truthy ? l_True : l_False;
            };
            cout << "c o [aig_vs_clauses]   aig_val_lit=" << aig_val
                 << " (rawvar_model=" << pr(m[aig_val.var()])
                 << " → lit_val=" << pr(lit_val(aig_val)) << ")"
                 << " f.out_lit=" << f.out
                 << " (rawvar_model=" << pr(m[f.out.var()])
                 << " → lit_val=" << pr(lit_val(f.out)) << ")"
                 << endl;
            // Also show f.aig fields for deeper inspection
            cout << "c o [aig_vs_clauses]   f.aig.node.nid=" << f.aig->nid
                 << " f.aig.node.var=" << f.aig->var
                 << " (AIGT: 0=and, 1=lit, 2=const)"
                 << endl;
            // Cross-check: evaluate f.aig directly under the SAT model.
            // For bve_and_substitute, f.aig leaves are y-space orig vars,
            // which under the miter map to y_hats. So read m[y_hat[v]] for
            // to_define_full leaves, m[v] for inputs.
            std::map<const AIG*, bool> eval_cache;
            std::function<bool(const aig_ptr&)> eval_aig = [&](const aig_ptr& n) -> bool {
                if (n->type == AIGT::t_const) return !n.neg;  // const TRUE is base, edge may flip
                if (n->type == AIGT::t_lit) {
                    uint32_t v = n->var;
                    bool val;
                    if (to_define_full.count(v)) {
                        uint32_t yh = y_to_y_hat_fast(v);
                        val = (m[yh] == l_True);
                    } else {
                        val = (m[v] == l_True);
                    }
                    return n.neg ? !val : val;
                }
                assert(n->type == AIGT::t_and);
                auto ci = eval_cache.find(n.get());
                if (ci != eval_cache.end()) return n.neg ? !ci->second : ci->second;
                bool lv = eval_aig(n->l);
                bool rv = eval_aig(n->r);
                bool pos = lv && rv;
                eval_cache[n.get()] = pos;
                return n.neg ? !pos : pos;
            };
            bool direct = eval_aig(f.aig);
            cout << "c o [aig_vs_clauses]   direct AIG eval under SAT model = " << (direct ? 1 : 0) << endl;
            // Full recursive AIG structure dump — gated under VERBOSE_DEBUG
            // so SLOW_DEBUG alone gets a concise diagnostic; verbose is
            // opt-in for deep triage.
            VERBOSE_DEBUG_DO({
                std::set<uint64_t> printed_nids;
                std::function<void(const aig_ptr&, int)> dump_aig = [&](const aig_ptr& n, int depth) {
                    std::string indent(depth * 2, ' ');
                    cout << "c o [aig_vs_clauses]   " << indent
                         << "nid=" << n->nid << " type=" << (int)n->type
                         << " neg=" << n.neg << " var=" << n->var;
                    if (printed_nids.count(n->nid)) { cout << " (seen)" << endl; return; }
                    printed_nids.insert(n->nid);
                    cout << endl;
                    if (n->type == AIGT::t_and && depth < 6) {
                        dump_aig(n->l, depth + 1);
                        dump_aig(n->r, depth + 1);
                    }
                };
                cout << "c o [aig_vs_clauses]   f.aig structure:" << endl;
                dump_aig(f.aig, 0);
            });
            return false;
        }
    }
    return true;
}

aig_ptr Manthan::one_level_substitute(Lit l, const uint32_t v, map<uint32_t, aig_ptr>& transformed) {
    if (!transformed.count(l.var())) {
        assert(var_to_formula.count(l.var()) == 1);
        auto aig = var_to_formula.at(l.var()).aig;
        std::unordered_map<const AIG*, aig_node_ptr> cache;
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
            release_assert(false && "Unhandled AIG type in visitor");
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
    for(uint32_t i = 0; i < cnf.get_clauses().size(); i++) {
        const auto& cl = cnf.get_clauses()[i];
        for(const auto& l: cl) {
            if (!to_define.count(l.var())) continue; // no need for these
            lit_to_cls[l.toInt()].push_back(i);
        }
    }

    uint32_t num_done = 0;
    vector<aig_ptr> aigs;
    for(const auto& y: y_order) {
        if (!to_define.count(y)) continue;
        assert(var_to_formula.count(y) == 0);

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
        aig_ptr overall = nullptr;

        // AIG
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
            aig_ptr current = nullptr;
            for(const auto& l: cl) {
                if (l.var() == y) continue;
                if (later_in_order(y, l.var())) {
                    aig_ptr aig = get_aig(~l);
                    set_depends_on(y, l);
                    if (current == nullptr) current = aig;
                    else current = AIG::new_and(current, aig);
                } else if (y == l.var()) {
                    assert(false);
                } else {
                    //keep current as-is, since we AND with TRUE
                }
            }
            if (current == nullptr) current = aig_mng.new_const(true);
            if (overall == nullptr) overall = current;
            else overall = AIG::new_or(overall, current);
        }
        if (overall == nullptr) overall = aig_mng.new_const(true);
        if (sign) overall = AIG::new_not(overall);
        overall = AIG::simplify_aig(overall);
        aigs.push_back(overall);
    }
    assert(aigs.size() == to_define.size());

    AIGRewriter rw;
    rw.set_sat_sweep(true);
    rw.rewrite_all(aigs, conf.verb);
    size_t prev = AIG::count_aig_nodes_fast(aigs);
    const uint32_t max_iters = 2;
    for (uint32_t i = 0; i < max_iters; i++) {
        rw.rewrite_all(aigs, conf.verb);
        rw.sat_sweep(aigs, conf.verb);
        const size_t now = AIG::count_aig_nodes_fast(aigs);
        if (now >= prev) break;
        prev = now;
    }

    // One AIGToCNF encoder per formula. An earlier version used a persistent
    // encoder across formulas, reasoning that the node-pointer-keyed cache
    // would dedup helpers for hash-consed sub-AIGs shared across formulas.
    // That turned out to be unsound: with sat_sweep + AIGRewriter massaging
    // the aigs vector, a cached Lit from one formula's encoding would be
    // reused for another formula's encode_edge cache hit, yielding a Lit
    // whose value disagreed with direct AIG evaluation (via an independent
    // fresh Tseitin miter). The failure surfaces as var_to_formula[y].aig
    // and var_to_formula[y].clauses+.out encoding different Boolean
    // functions — cex_solver is happy (it only sees .clauses+.out) but the
    // final exported AIGs (from .aig) are wrong. Reproducer: bug_real_big.cnf
    // under SLOW_DEBUG catches this via check_aig_matches_clauses_per_formula.
    struct FormulaClauseSink {
        MetaSolver2& solver;
        std::vector<CL>* clauses;
        std::set<uint32_t>& helpers_set;
        void new_var() {
            solver.new_var();
            helpers_set.insert(solver.nVars() - 1);
        }
        [[nodiscard]] uint32_t nVars() const { return solver.nVars(); }
        void add_clause(const std::vector<Lit>& cl) { clauses->emplace_back(cl); }
    };
    FormulaClauseSink sink{cex_solver, nullptr, helpers};

    uint32_t at = 0;
    for(const auto& y: y_order) {
        if (!to_define.count(y)) continue;
        FHolder<MetaSolver2>::Formula f;
        f.aig = aigs.at(at);

        // Fresh encoder per formula — see comment above FormulaClauseSink.
        ArjunNS::AIGToCNF<FormulaClauseSink> enc(sink);
        enc.set_true_lit(fh->get_true_lit());

        // Encode via AIGToCNF on a y_hat-space clone of f.aig: k-ary AND/OR
        // fusion, De Morgan flattening, ITE detection and dedup give a much
        // smaller CNF than the per-branch multi-input Tseitin we used before.
        map<aig_ptr, aig_ptr> aig_remap_cache;
        aig_ptr aig_yhat = AIG::transform<aig_ptr>(f.aig,
            [&](AIGT type, const uint32_t var2, const bool neg2,
                const aig_ptr* left2, const aig_ptr* right2) -> aig_ptr {
                if (type == AIGT::t_const) return aig_mng.new_const(!neg2);
                if (type == AIGT::t_lit) return AIG::new_lit(map_y_to_y_hat(Lit(var2, neg2)));
                if (type == AIGT::t_and) return AIG::new_and(*left2, *right2, neg2);
                release_assert(false && "Unhandled AIG type");
            }, aig_remap_cache);

        sink.clauses = &f.clauses;
        uint32_t nv_before = cex_solver.nVars();
        size_t h_before = helpers.size();
        f.out = enc.encode(aig_yhat);
        uint32_t nv_after = cex_solver.nVars();
        size_t h_after = helpers.size();
        verb_print(4, "[bve-sub] y=" << (y+1)
                  << " cex_solver.nVars " << nv_before << "->" << nv_after
                  << " helpers " << h_before << "->" << h_after);
        var_to_formula[y] = f;

        num_done++;
        if (num_done % 50 == 0 && num_done > 0) {
            verb_print(1, "[manthan] done with BVE "
                << " funs: " << setw(6) << num_done
                << " funs/s: " << setw(6) << fixed << setprecision(2) << safe_div(num_done,(cpuTime()-start_time))
                << " T: " << setw(5) << (cpuTime()-start_time)
                << " mem: " << memUsedTotal()/(1024.0*1024.0) << " MB");
        }
        at++;
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

void Manthan::print_repair_stats([[maybe_unused]] const string& txt, const string& color, [[maybe_unused]] const string& extra) const {
    vector<uint32_t> rep(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) rep[i] = i;
    sort(rep.begin(), rep.end(), [&] (const auto& a, const auto& b) {
        return repaired_vars_count[a] > repaired_vars_count[b];
    });

    for(size_t i = 0; i < min((size_t)10, (size_t)rep.size()); i++) {
        const auto& v = rep[i];
        if (repaired_vars_count[v] == 0) break;
        verb_print(1, color << "[manthan] repaired var " << setw(5) << v+1
            << " count: " << setw(6) << repaired_vars_count[v]);
    }
}

void Manthan::print_stats(const string& txt, const string& color, const string& extra) const {
    const double repair_time = cpuTime() - repair_start_time;
    verb_print(1, color << "[manthan]" << txt
            << " rep: " << setw(6) << tot_repaired
            << "   loops: "<< setw(6) << num_loops_repair
            << "   avg rep/loop: " << setprecision(1) << setw(4) << (double)tot_repaired/(num_loops_repair+0.0001)
            << "   avg conflsz: " << setw(6) << fixed << setprecision(2) << (double)conflict_sizes_sum/(tot_repaired+0.0001)
            << "   avg need rep: " << setw(6) << fixed << setprecision(2) << (double)needs_repair_sum/(num_loops_repair+0.0001)
            << "   cache-hit: " << setw(3) << fixed << setprecision(0) << repair_solver.get_cache_hit_rate()*100.0 << "%"
            << "   gen-ok: " << setw(4) << generalized_repair_ok << " gen-fb: " << generalized_repair_fallback
            << "   T: " << setprecision(2) << fixed << setw(7) << repair_time
            << "   rep/s: " << setprecision(4) << safe_div(tot_repaired,repair_time) << setprecision(2)
            << extra);
}

void Manthan::print_detailed_stats() const {
    const double repair_time = cpuTime() - repair_start_time;
    const double accounted = time_cex_finding + time_collect_extra_cex + time_find_better_ctx
        + time_find_conflict + time_perform_repair + time_inject_formulas + time_recompute_y_hat;
    verb_print(1, COLCYN "[manthan-stats] === DETAILED TIMING BREAKDOWN ===");
    verb_print(1, COLCYN "[manthan-stats] Total repair time:     " << fixed << setprecision(2) << repair_time << "s");
    verb_print(1, COLCYN "[manthan-stats]   cex_finding:         " << fixed << setprecision(2) << time_cex_finding << "s (" << setprecision(1) << safe_div(time_cex_finding, repair_time)*100.0 << "%)");
    verb_print(1, COLCYN "[manthan-stats]   collect_extra_cex:   " << fixed << setprecision(2) << time_collect_extra_cex << "s (" << setprecision(1) << safe_div(time_collect_extra_cex, repair_time)*100.0 << "%)");
    verb_print(1, COLCYN "[manthan-stats]   find_better_ctx:     " << fixed << setprecision(2) << time_find_better_ctx << "s (" << setprecision(1) << safe_div(time_find_better_ctx, repair_time)*100.0 << "%)");
    verb_print(1, COLCYN "[manthan-stats]   find_conflict:       " << fixed << setprecision(2) << time_find_conflict << "s (" << setprecision(1) << safe_div(time_find_conflict, repair_time)*100.0 << "%)");
    verb_print(1, COLCYN "[manthan-stats]   perform_repair:      " << fixed << setprecision(2) << time_perform_repair << "s (" << setprecision(1) << safe_div(time_perform_repair, repair_time)*100.0 << "%)");
    verb_print(1, COLCYN "[manthan-stats]   inject_formulas:     " << fixed << setprecision(2) << time_inject_formulas << "s (" << setprecision(1) << safe_div(time_inject_formulas, repair_time)*100.0 << "%)");
    verb_print(1, COLCYN "[manthan-stats]   recompute_y_hat:     " << fixed << setprecision(2) << time_recompute_y_hat << "s (" << setprecision(1) << safe_div(time_recompute_y_hat, repair_time)*100.0 << "%)");
    verb_print(1, COLCYN "[manthan-stats]   unaccounted:         " << fixed << setprecision(2) << (repair_time - accounted) << "s (" << setprecision(1) << safe_div(repair_time - accounted, repair_time)*100.0 << "%)");
    verb_print(1, COLCYN "[manthan-stats] === CONFLICT STATS ===");
    verb_print(1, COLCYN "[manthan-stats]   input-only conflicts: " << input_only_conflict_count
        << "  avg sz: " << fixed << setprecision(1) << safe_div(input_only_conflict_sizes_sum, input_only_conflict_count));
    verb_print(1, COLCYN "[manthan-stats]   full conflicts:       " << full_conflict_count
        << "  avg sz: " << fixed << setprecision(1) << safe_div(full_conflict_sizes_sum, full_conflict_count));
    verb_print(1, COLCYN "[manthan-stats]   cost-zero repairs:    " << cost_zero_repairs);
    verb_print(1, COLCYN "[manthan-stats]   repair_failed:        " << repair_failed);
    verb_print(1, COLCYN "[manthan-stats]   cex_solver calls:     " << cex_solver_calls);
    verb_print(1, COLCYN "[manthan-stats]   repair_solver calls:  " << repair_solver_calls);

    // Print top 20 most repaired vars with their AIG sizes
    vector<uint32_t> rep(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) rep[i] = i;
    sort(rep.begin(), rep.end(), [&] (const auto& a, const auto& b) {
        return repaired_vars_count[a] > repaired_vars_count[b];
    });
    verb_print(1, COLCYN "[manthan-stats] === TOP REPAIRED VARS ===");
    for(size_t i = 0; i < min((size_t)20, (size_t)rep.size()); i++) {
        const auto& v = rep[i];
        if (repaired_vars_count[v] == 0) break;
        size_t aig_sz = 0;
        size_t aig_depth = 0;
        if (var_to_formula.count(v) && var_to_formula.at(v).aig) {
            aig_sz = AIG::count_aig_nodes(var_to_formula.at(v).aig);
            // Compute depth
            std::function<size_t(const aig_ptr&, std::map<aig_ptr,size_t>&)> get_depth =
                [&](const aig_ptr& a, std::map<aig_ptr,size_t>& dc) -> size_t {
                    if (!a || a->type != AIGT::t_and) return 0;
                    auto it = dc.find(a);
                    if (it != dc.end()) return it->second;
                    size_t d = 1 + std::max(get_depth(a->l, dc), get_depth(a->r, dc));
                    dc[a] = d;
                    return d;
                };
            std::map<aig_ptr,size_t> dc;
            aig_depth = get_depth(var_to_formula.at(v).aig, dc);
        }
        verb_print(1, COLCYN "[manthan-stats]   var " << setw(5) << v+1
            << "  repairs: " << setw(6) << repaired_vars_count[v]
            << "  cnf_cl: " << setw(7) << (var_to_formula.count(v) ? var_to_formula.at(v).clauses.size() : 0)
            << "  aig_nodes: " << setw(7) << aig_sz
            << "  aig_depth: " << setw(5) << aig_depth
            << "  confl_freq: " << setw(5) << (v < var_conflict_freq.size() ? var_conflict_freq[v] : 0));
    }

    // Aggregate AIG stats
    uint64_t total_aig_nodes = 0, total_clauses = 0, max_aig_nodes = 0;
    {
        const uint64_t epoch = AIG::next_visit_epoch();
        size_t union_count = 0;
        for (const auto& [v, form] : var_to_formula) {
            total_clauses += form.clauses.size();
            if (form.aig) {
                size_t sz = AIG::count_aig_nodes(form.aig.get());
                AIG::count_aig_nodes_batch(form.aig.get(), epoch, union_count);
                max_aig_nodes = std::max(max_aig_nodes, (uint64_t)sz);
            }
        }
        total_aig_nodes = union_count;
    }
    verb_print(1, COLCYN "[manthan-stats] === AIG STATS ===");
    verb_print(1, COLCYN "[manthan-stats]   total unique AIG nodes: " << total_aig_nodes);
    verb_print(1, COLCYN "[manthan-stats]   max AIG nodes (single var): " << max_aig_nodes);
    verb_print(1, COLCYN "[manthan-stats]   total formula clauses: " << total_clauses);
    verb_print(1, COLCYN "[manthan-stats]   cex_solver nVars: " << cex_solver.nVars());
}

void Manthan::add_xor_var() {
    const auto& sampl_vars = cnf.get_sampl_vars();
    if (sampl_vars.empty()) return;

    // sampl_vars are in NEW space; AIGs stored in defs[] use ORIG space.
    // new_var() creates vars with orig == new (orig_to_new_var[v] = Lit(v,false)),
    // so intermediate XOR vars can use their index directly in AIGs.
    const auto new_to_orig = cnf.get_new_to_orig_var();

    // XOR(a, b) = OR(AND(a, NOT b), AND(NOT a, b))
    auto xor_of = [](const aig_ptr& a, const aig_ptr& b) -> aig_ptr {
        return AIG::new_or(
            AIG::new_and(a, AIG::new_not(b)),
            AIG::new_and(AIG::new_not(a), b));
    };

    // Start with the orig-space literal for the first sampling var
    Lit orig_lit = new_to_orig.at(sampl_vars[0]);
    aig_ptr prev = AIG::new_lit(orig_lit);

    for (size_t i = 1; i < sampl_vars.size(); i++) {
        orig_lit = new_to_orig.at(sampl_vars[i]);
        aig_ptr cur = AIG::new_lit(orig_lit);
        // new_var() gives orig == new for freshly created vars
        cnf.new_var();
        const uint32_t v = cnf.nVars() - 1;
        const Lit v_orig = cnf.get_new_to_orig_var().at(v);
        assert(v_orig.sign() == false);
        cnf.set_def(v_orig.var(), xor_of(prev, cur));
        helper_functions.insert(v);
        verb_print(2, "[manthan] Added XOR internal var: " << v+1 << " orig v: " << v_orig.var()+1);
        prev = AIG::new_lit(v_orig);
    }

    verb_print(1, "[manthan] Added " << sampl_vars.size() - 1 << " XOR vars as BVA input vars");
}

void Manthan::const_functions() {
    // Use multiple samples and majority voting to pick better constant values.
    // A single sample might be atypical; majority voting reduces the number of
    // counterexamples needed to reach the correct formula.
    const uint32_t num_samples = std::max(mconf.const_vote_samples, (uint32_t)1);
    vector<sample> samples = get_cmsgen_samples(num_samples);
    for(const auto& y: Manthan::y_order) {
        if (!to_define.count(y)) continue;

        vector<const sample*> filt_s = filter_samples(y, samples);
        assert(var_to_formula.count(y) == 0);
        bool val;
        if (filt_s.empty()) {
            val = true;
        } else {
            // Majority voting across filtered samples
            uint32_t true_count = 0;
            for (const auto* s : filt_s) {
                if ((*s)[y] == l_True) true_count++;
            }
            val = true_count * 2 >= filt_s.size(); // majority is TRUE
        }
        if (mconf.inv_learnt) val = !val;
        verb_print(3, "[manthan] const function for var " << y+1 << " is " << val);
        var_to_formula[y] = fh->constant_formula(val);
    }
}

SimplifiedCNF Manthan::do_manthan() {
    SLOW_DEBUG_DO(assert(cnf.get_need_aig() && cnf.defs_invariant()));
    const double my_time = cpuTime();
    const auto ret = cnf.find_disconnected();
    verb_print(1, "[manthan] Found " << ret.size() << " components");
    if (mconf.bva_xor_vars) add_xor_var();
    repaired_vars_count.resize(cnf.nVars(), 0);
    var_conflict_freq.resize(cnf.nVars(), 0);
    input_only_ok.resize(cnf.nVars(), 0);
    input_only_fail.resize(cnf.nVars(), 0);

    if (!mconf.write_manthan_cnf.empty()) cnf.write_simpcnf(mconf.write_manthan_cnf);

    // CNF is divided into:
    // input vars -- original sampling vars
    // defined non-input vars -- vars defined via backward_round_synth
    // to_define vars -- vars that are not defined yet, and not input
    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_manthan").unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[manthan] No variables to define, returning original CNF");
        return cnf;
    }
    for(const auto& v: helper_functions) {
        if (!input.count(v)) {
            cout << "ERROR: helper function var " << v+1 << " is not detected as an input var" << endl;
            release_assert(false);
        }
    }

    // Extend to_define_full to to_define + backward_defined
    to_define_full.clear();
    to_define_full.insert(to_define.begin(), to_define.end());
    to_define_full.insert(backward_defined.begin(), backward_defined.end());
    rebuild_var_bytemaps();
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

    // Order & train
    pre_order_vars();
    fill_var_to_formula_with(backward_defined);
    fill_var_to_formula_with(helper_functions);

    if (mconf.manthan_base == 0) {
#ifdef EXTRA_SYNTH
        ManthanLearn learn(*this, conf, mconf);
        learn.full_train();
#else
        cout << "ERROR: manthan_base is set to 0 but we are not in EXTRA_SYNTH mode!" << endl;
        exit(EXIT_FAILURE);
#endif
    } else if (mconf.manthan_base == 1) {
        const_functions();
    } else if (mconf.manthan_base == 2) {
        bve_and_substitute();
    }
    verb_print(4, "[trace] post bve_and_substitute nVars=" << cex_solver.nVars() << " helpers=" << helpers.size());
    post_order_vars();
    verb_print(4, "[trace] post post_order_vars nVars=" << cex_solver.nVars() << " helpers=" << helpers.size());

    // Counterexample-guided repair
    repair_start_time = cpuTime();
    for(const auto& v: to_define_full) {
        assert(var_to_formula.count(v) && "All must have a tentative definition");
        updated_y_funcs.push_back(v);
    }
    bool at_least_one_repaired = true;
    verb_print(4, "[trace] before check nVars=" << cex_solver.nVars() << " helpers=" << helpers.size());
    SLOW_DEBUG_DO(assert(check_functions_for_y_vars()));
    SLOW_DEBUG_DO({
        if (!check_aig_matches_clauses_per_formula("post-bve_and_substitute")) {
            assert(false && "bve_and_substitute produces diverging aig/clauses — bug before repair");
        }
    });

    while(true) {
        if (mconf.stats_every > 0 && num_loops_repair % mconf.stats_every == mconf.stats_every - 1) print_stats();
        if (mconf.detailed_stats_every > 0 && num_loops_repair % mconf.detailed_stats_every == mconf.detailed_stats_every - 1) print_detailed_stats();
        assert(at_least_one_repaired);
        at_least_one_repaired = false;
        num_loops_repair++;

        double t0 = cpuTime();
        inject_formulas_into_solver();
        time_inject_formulas += cpuTime() - t0;

        t0 = cpuTime();
        sample ctx;
        const bool finished = get_counterexample(ctx);
        time_cex_finding += cpuTime() - t0;
        cex_solver_calls++;
        if (finished) {
            // cex_solver claims no CEX. Triangulate:
            //   via_clauses  — fresh SAT miter using var_to_formula[y].clauses+.out
            //                  (same encoding cex_solver uses). If this fails,
            //                  cex_solver is wrong.
            //   via_aig      — fresh SAT miter using var_to_formula[y].aig
            //                  (what becomes cnf.defs). If this fails but
            //                  via_clauses passes, the AIG encoding diverges
            //                  from the CNF encoding per formula.
            //   aig_vs_clauses_per_formula — direct pairwise miter between
            //                  .aig and .clauses+.out. Pinpoints which y
            //                  has inconsistent reps.
            SLOW_DEBUG_DO({
                const std::string where = "finished-loop-exit iter=" + std::to_string(num_loops_repair);
                bool clauses_ok = check_synth_via_clauses(where);
                bool aig_ok = check_synth_via_aig(where);
                if (!clauses_ok) std::cout << "c o [BUG] cex_solver FINISHED but via_clauses miter is SAT" << std::endl;
                if (!aig_ok)     std::cout << "c o [BUG] cex_solver FINISHED but via_aig miter is SAT" << std::endl;
                if (clauses_ok && !aig_ok) {
                    std::cout << "c o [BUG] CNF rep correct but AIG rep wrong — pairwise check next" << std::endl;
                    bool per_formula_ok = check_aig_matches_clauses_per_formula(where);
                    (void)per_formula_ok;
                }
                assert(clauses_ok && "via_clauses check fails at loop exit");
                assert(aig_ok && "via_aig check fails at loop exit");
            });
            break;
        }
        if (tot_repaired >= mconf.max_repairs) {
            print_stats("", COLRED, " Reached max repairs");
            return cnf;
        }
        print_cnf_debug_info(ctx);
        print_needs_repair_vars();
        SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
        SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));

        // Collect additional counterexamples to identify free inputs and pick best cex.
        // When input-only conflicts dominate, reduce CEX collection since free input
        // detection is less critical (input-only conflicts are already general).
        // Also reduce when solver is slow (late in repair) to avoid expensive calls.
        t0 = cpuTime();
        const int saved_multi_cex_k = mconf.multi_cex_k;
        if (generalized_repair_ok > mconf.reduce_cex_gen_ok && generalized_repair_ok * mconf.reduce_cex_gen_ratio_den > tot_repaired * mconf.reduce_cex_gen_ratio_num) {
            const_cast<ArjunNS::Arjun::ManthanConf&>(mconf).multi_cex_k = min(mconf.multi_cex_k, 2);
        }
        // When deep into repair (solver slow), reduce extra CEXes to save time.
        // Also reduce when few vars need repair, as multiple CEXes provide less value.
        if (tot_repaired > mconf.reduce_cex_tot_rep) {
            const_cast<ArjunNS::Arjun::ManthanConf&>(mconf).multi_cex_k = min(mconf.multi_cex_k, 2);
        }
        compute_needs_repair(ctx);
        if (needs_repair.size() <= mconf.reduce_cex_need_rep) {
            const_cast<ArjunNS::Arjun::ManthanConf&>(mconf).multi_cex_k = 1;
        }
        // When cost-zero dominates, extra CEXes provide little value since
        // most repairs will be cost-zero regardless of which CEX we use
        if (cost_zero_repairs > tot_repaired * mconf.cz_high_ratio && tot_repaired > mconf.reduce_cex_cz_min_rep) {
            const_cast<ArjunNS::Arjun::ManthanConf&>(mconf).multi_cex_k =
                min(mconf.multi_cex_k, 2);
        }
        auto all_cexs = collect_extra_cex(ctx);
        const_cast<ArjunNS::Arjun::ManthanConf&>(mconf).multi_cex_k = saved_multi_cex_k;
        ctx = all_cexs[0]; // best CEX (lowest weighted repair cost)
        time_collect_extra_cex += cpuTime() - t0;
        compute_needs_repair(ctx);

        t0 = cpuTime();
        const uint32_t old_needs_repair_size = needs_repair.size();
        if (mconf.maxsat_better_ctx == 1) {
            #ifdef EXTRA_SYNTH
            find_better_ctx_maxsat(ctx);
            #else
            cout << "ERROR: maxsat_better_ctx is set to 1 but we are not in EXTRA_SYNTH mode!" << endl;
            exit(EXIT_FAILURE);
            #endif
        } else {
            find_better_ctx_normal(ctx);
        }
        time_find_better_ctx += cpuTime() - t0;
        SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
        SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));
        compute_needs_repair(ctx);
        verb_print(2, "[manthan] finding better ctx done, needs_repair size before vs now: "
              << setw(3) << old_needs_repair_size << " -- " << setw(4) << needs_repair.size());
        print_needs_repair_vars();
        needs_repair_sum += needs_repair.size();

        assert(!needs_repair.empty());
        uint32_t num_repaired = 0;
        uint32_t consecutive_cost_zero = 0;
        while(!needs_repair.empty()) {
            auto y_rep = find_next_repair_var(ctx);
            bool done = repair(y_rep, ctx); // this updates ctx
            if (done) {
                at_least_one_repaired = true;
                num_repaired++;
                tot_repaired++;
                consecutive_cost_zero = 0;
                if (tot_repaired >= mconf.max_repairs) {
                    print_stats("", COLRED, " Reached max repairs");
                    return cnf;
                }
                if (mconf.one_repair_per_loop) break;
            } else {
                repair_failed++;
                consecutive_cost_zero++;
                // After consecutive cost-zero repairs, break to get a fresh
                // counterexample. Adaptive threshold: break sooner when the
                // cost-zero rate is high (saving more solver calls).
                const uint32_t cz_threshold = (cost_zero_repairs > tot_repaired * mconf.cz_high_ratio) ? mconf.cz_threshold_high :
                    (cost_zero_repairs > tot_repaired * mconf.cz_low_ratio) ? mconf.cz_threshold_mid : mconf.cz_threshold_low;
                if (consecutive_cost_zero >= cz_threshold && num_repaired > 0) break;
            }
            SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
            SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));
            SLOW_DEBUG_DO({
                if (!check_aig_matches_clauses_per_formula(
                        "post-repair y=" + std::to_string(y_rep+1) +
                        " iter=" + std::to_string(num_loops_repair))) {
                    assert(false && "perform_repair introduced a diverging aig/clauses");
                }
            });
            verb_print(3, "[manthan] finished repairing " << y_rep+1 << " : " << std::boolalpha << done);
        }
        verb_print(2, "[manthan] Num repaired: " << num_repaired << " tot repaired: " << tot_repaired << " num_loops_repair: " << num_loops_repair);

        if (mconf.check_repair) check_repair_monotonic();
    }
    const double repair_time = cpuTime() - repair_start_time;
    assert(check_map_dependency_cycles());
    print_repair_stats();
    print_detailed_stats();
    print_stats("", COLYEL, " DONE");

    // Build final CNF
    vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    for(const auto& y: to_define) {
        assert(var_to_formula.count(y));
        verb_print(3, "Final formula for " << y+1 << ":" << endl << var_to_formula[y]);
        assert(var_to_formula[y].aig != nullptr);
        aigs[y] = var_to_formula[y].aig;
    }
    const uint32_t cnf_nvars = cnf.nVars();
    SimplifiedCNF fcnf = std::move(cnf);
    fcnf.map_aigs_to_orig(aigs, cnf_nvars, y_hat_to_y);
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
    SLOW_DEBUG_DO(assert(fcnf.get_need_aig() && fcnf.defs_invariant()));
    return true;
}

uint32_t Manthan::find_next_repair_var(const sample& ctx) const {
    assert(!needs_repair.empty());
    uint32_t y_rep = std::numeric_limits<uint32_t>::max();
    for(const auto& y: y_order) {
        if (needs_repair.count(y)) {
            assert(ctx[y] != ctx[y_to_y_hat_fast(y)]);
            y_rep = y;
            break;
        }
        assert(ctx[y] == ctx[y_to_y_hat_fast(y)]);
    }
    assert(y_rep != std::numeric_limits<uint32_t>::max());
    assert(!backward_defined.count(y_rep) && "If all y_hat has been recomputed, the first wrong CANNOT be a BW var");
    return y_rep;
}

bool Manthan::is_unsat(const vector<Lit>& conflict, uint32_t y_rep, const sample& ctx) const {
    SATSolver s;
    s.new_vars(cnf.nVars());
    for(const auto& c: cnf.get_clauses()) s.add_clause(c);
    for(const auto& l: conflict) s.add_clause({~l});
    const Lit to_repair = Lit(y_rep, ctx[y_to_y_hat_fast(y_rep)] == l_True);
    s.add_clause({~to_repair});
    const auto ret = s.solve();
    return ret == l_False;
}

bool Manthan::repair(const uint32_t y_rep, sample& ctx) {
    verb_print(2, "[DEBUG] Starting repair for var " << y_rep+1
            << (backward_defined.count(y_rep) ? "[BW]" : ""));
    assert(backward_defined.count(y_rep) == 0 && "Backward defined should need NO repair, ever");
    assert(to_define.count(y_rep) == 1 && "Only to-define vars should be repaired");
    assert(y_rep < cnf.nVars());

    if (mconf.simplify_every > 0 && (num_loops_repair % mconf.simplify_every == (mconf.simplify_every-1)
            || (mconf.simplify_repair_every > 0 && tot_repaired % mconf.simplify_repair_every == mconf.simplify_repair_every - 1))) {
        vector<Lit> assumps;
        assumps.reserve(input.size() + to_define_full.size());
        for(const auto& x: input) assumps.emplace_back(x, false);
        for(const auto& x: to_define_full) assumps.emplace_back(x, false);
        repair_solver.simplify(&assumps);
    }

    vector<Lit> conflict;
    repaired_vars_count[y_rep]++;

    double t0 = cpuTime();
    bool ret = find_conflict(y_rep, ctx, conflict);
    time_find_conflict += cpuTime() - t0;
    repair_solver_calls++;

    if (ret) {
        SLOW_DEBUG_DO(assert(is_unsat(conflict, y_rep, ctx)));

        // Add the repair conflict as a learned clause to the repair solver.
        // The conflict {l1, l2, ..., ln} (with to_repair already removed) means:
        // under the CNF, ~l1 AND ~l2 AND ... AND ~to_repair → FALSE.
        // So (l1 OR l2 OR ... OR to_repair) is a valid clause.
        // We add it as redundant to help the solver reason faster.
        if (!conflict.empty()) {
            const Lit to_repair = Lit(y_rep, ctx[y_to_y_hat_fast(y_rep)] == l_True);
            vector<Lit> learned_cl;
            learned_cl.reserve(conflict.size() + 1);
            for (const auto& l : conflict) learned_cl.push_back(l);
            learned_cl.push_back(to_repair);
            repair_solver.add_red_clause(learned_cl);
        }

        t0 = cpuTime();
        perform_repair(y_rep, ctx, conflict);
        time_perform_repair += cpuTime() - t0;

        if (!mconf.one_repair_per_loop) {
            ctx[y_to_y_hat_fast(y_rep)] = ctx[y_rep];

            t0 = cpuTime();
            inject_formulas_into_solver();
            time_inject_formulas += cpuTime() - t0;

            t0 = cpuTime();
            recompute_all_y_hat_cnf(ctx);
            time_recompute_y_hat += cpuTime() - t0;
        }

        // Track conflict type
        bool is_input_only = true;
        for (const auto& l : conflict) {
            if (!is_input[l.var()]) { is_input_only = false; break; }
        }
        if (is_input_only) {
            input_only_conflict_count++;
            input_only_conflict_sizes_sum += conflict.size();
        } else {
            full_conflict_count++;
            full_conflict_sizes_sum += conflict.size();
        }

    } else {
        cost_zero_repairs++;
        // Cost 0: find_conflict updated ctx[y] for y_rep and later vars only.
        // Formulas and inputs haven't changed, so y_hat values are still valid.
        // No recomputation needed.
    }
    compute_needs_repair(ctx);
    print_needs_repair_vars();
    return ret;
}

bool Manthan::find_conflict(const uint32_t y_rep, sample& ctx, vector<Lit>& conflict) {
    const double repair_solver_start_time = cpuTime();

    // Find which input variables the AIG for y_rep actually depends on.
    // Any input not in the AIG's dependency set is a don't-care and can be
    // excluded from assumptions, producing a more general (shorter) conflict.
    // Reset marks left by the previous call before reusing the scratch bitmap.
    for (const uint32_t prev_v : aig_dep_list) aig_dep_is_dep[prev_v] = 0;
    aig_dep_list.clear();
    aig_dep_stack.clear();
    if (mconf.minimize_conflict) {
        const auto& aig = var_to_formula.at(y_rep).aig;
        assert(aig != nullptr);
        const ArjunNS::AIG* aig_raw = aig.get();
        auto it = dep_cache.find(y_rep);
        if (it != dep_cache.end() && it->second.aig_ptr == aig_raw) {
            // Cache hit: reuse memoized dep_list, just repopulate the bitmap.
            const auto& cached = it->second.dep_list;
            for (const uint32_t dv : cached) {
                if (dv >= aig_dep_is_dep.size()) aig_dep_is_dep.resize(dv + 1, 0);
                aig_dep_is_dep[dv] = 1;
                aig_dep_list.push_back(dv);
            }
        } else {
            AIG::get_dependent_vars(aig, aig_dep_is_dep, aig_dep_list,
                                    aig_dep_stack, y_rep);
            if (it != dep_cache.end()) {
                it->second.aig_ptr = aig_raw;
                it->second.dep_list = aig_dep_list;
            } else {
                dep_cache.emplace(y_rep, DepCacheEntry{aig_raw, aig_dep_list});
            }
        }
    }
    const bool have_aig_deps = !aig_dep_list.empty();

    assert(ctx[y_rep] != ctx[y_to_y_hat_fast(y_rep)] && "before repair, y and y_hat must be different");
    const Lit to_repair = Lit(y_rep, ctx[y_to_y_hat_fast(y_rep)] == l_True);

    // Try input-only conflict first: assume only input vars + ~to_repair, without
    // fixing earlier y-variables. If UNSAT, the conflict is strictly more general:
    // it shows the formula is wrong for these inputs regardless of y-variable values.
    // Skip if this variable has consistently failed to produce input-only conflicts,
    // as the solver call is wasted effort (saves ~50% on query-type benchmarks).
    bool found_input_only = false;
    vector<Lit> assumps;
    // Skip input-only attempt when the GLOBAL success rate is very low,
    // indicating this benchmark structure rarely produces input-only conflicts.
    // This avoids wasting a solver call per repair on query-type benchmarks
    // where input-only conflicts are rare (<5% success rate).
    const bool skip_input_only = (tot_repaired > mconf.skip_input_only_min_rep &&
        generalized_repair_ok * mconf.skip_input_only_ratio < tot_repaired);
    if (!skip_input_only) {
        vector<Lit> input_assumps;
        input_assumps.reserve(input.size() + 1);
        for (const auto& x : input) {
            if (have_aig_deps && (x >= aig_dep_is_dep.size() || !aig_dep_is_dep[x])) continue;
            input_assumps.emplace_back(x, ctx[x] == l_False);
        }
        input_assumps.push_back({~to_repair});
        auto input_ret = repair_solver.solve(&input_assumps);
        if (input_ret == l_False) {
            conflict = repair_solver.get_conflict();
            if (std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end()) {
                verb_print(2, "[manthan] Found INPUT-ONLY conflict sz " << conflict.size()
                    << " for y_rep=" << y_rep+1);
                generalized_repair_ok++;
                found_input_only = true;
                assumps = std::move(input_assumps);
            }
        }
    }

    if (!found_input_only) {
    uint32_t skipped_inputs = 0;
    assumps.clear();
    assumps.reserve(input.size() + y_order.size() + 1);
    for(const auto& x: input) {
        // Skip inputs that the AIG for y_rep doesn't depend on
        if (have_aig_deps && (x >= aig_dep_is_dep.size() || !aig_dep_is_dep[x])) {
            skipped_inputs++;
            continue;
        }
        const Lit l = Lit(x, ctx[x] == l_False);
        assumps.push_back(l);
    }
    verb_print(2, "[manthan] skipped " << skipped_inputs << " / " << input.size()
            << " inputs for y_rep=" << y_rep+1);

    // We go through the variables that y_rep does NOT depend on, and assume them to be correct
    for(const auto& y: y_order) {
        // BW will be updated, as it can must depend on vars other than inputs
        if (!mconf.silent_var_update && backward_defined.count(y)) continue;
        if (y == y_rep) break; // beyond this point we don't care
        assert(dependency_mat[y][y_rep] != 1 && "due to ordering, this should not happen. Otherwise y depends on y_rep, but we will repair y_rep potentially with y_rep");
        assert(ctx[y] == ctx[y_to_y_hat_fast(y)]); // they are correct
        const Lit l = Lit(y, ctx[y] == l_False);
        verb_print(3, "assuming " << y+1 << " is " << ctx[y]);
        assumps.push_back(l);
    }

    assumps.push_back({~to_repair});

    verb_print(2, "assuming reverse for y_rep: " << ~to_repair);
    auto ret = repair_solver.solve(&assumps);
    verb_print(2, "repair_solver finished "
            << " with result: " << (ret == l_True ? "SAT" : (ret == l_False ? "UNSAT" : "UNKNOWN"))
            << " in T: " << cpuTime()-repair_solver_start_time);
    assert(ret != l_Undef);

    if (ret == l_True) {
        if (skipped_inputs > 0) {
            // SAT with reduced inputs - retry with all inputs to get proper cost-0 repair
            assumps.clear();
            for(const auto& x: input) assumps.push_back(Lit(x, ctx[x] == l_False));
            for(const auto& y: y_order) {
                if (!mconf.silent_var_update && backward_defined.count(y)) continue;
                if (y == y_rep) break;
                assumps.push_back(Lit(y, ctx[y] == l_False));
            }
            assumps.push_back({~to_repair});
            ret = repair_solver.solve(&assumps);
            assert(ret != l_Undef);
            if (ret == l_True) {
                verb_print(2, "Repair cost is 0 for y: " << y_rep+1);
                bool found_yrep = false;
                const auto& model = repair_solver.get_model();
                for(const auto& y: y_order) {
                    if (y == y_rep) found_yrep = true;
                    if (found_yrep) ctx[y] = model[y];
                }
                assert(ctx[y_rep] == ctx[y_to_y_hat_fast(y_rep)]);
                return false;
            }
            // UNSAT with all inputs - extract conflict normally
            conflict = repair_solver.get_conflict();
        } else {
            verb_print(2, "Repair cost is 0 for y: " << y_rep+1);
            bool found_yrep = false;
            const auto& model = repair_solver.get_model();
            for(const auto& y: y_order) {
                if (y == y_rep) found_yrep = true;
                if (found_yrep) ctx[y] = model[y];
            }
            assert(ctx[y_rep] == ctx[y_to_y_hat_fast(y_rep)]);
            return false;
        }
    } else {
        conflict = repair_solver.get_conflict();
    }
    } // end if (!found_input_only)
    assert(std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end() &&
        "to_repair literal must be in conflict");

    verb_print(2, "find_conflict sz: " << setw(5) << conflict.size() << " conflict: " << conflict);
    uint32_t orig_size = conflict.size();
    const double minimize_start_time = cpuTime();
    if (conflict.size() > 1 && mconf.minimize_conflict) {
        minimize_conflict(conflict, assumps, to_repair);
        assert(std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end() &&
            "to_repair literal must be in conflict");

        // After minimization, try dropping ALL y-variables from the conflict.
        // If the remaining input-only conflict is still UNSAT, the repair is
        // more general (independent of intermediate variable values).
        // Skip for very large conflicts (unlikely to succeed and expensive).
        if (conflict.size() <= mconf.conflict_drop_y_max) {
            bool has_y_vars = false;
            for (const auto& l : conflict) {
                if (l != to_repair && !is_input[l.var()]) { has_y_vars = true; break; }
            }
            if (has_y_vars) {
                assumps.clear();
                for (const auto& l : conflict) {
                    if (l == to_repair || is_input[l.var()]) assumps.push_back(~l);
                }
                if (!assumps.empty()) {
                    auto ret3 = repair_solver.solve(&assumps);
                    if (ret3 == l_False) {
                        auto conflict3 = repair_solver.get_conflict();
                        if (std::find(conflict3.begin(), conflict3.end(), to_repair) != conflict3.end()) {
                            verb_print(2, "[manthan] Dropped y-vars from conflict: "
                                << conflict.size() << " -> " << conflict3.size());
                            conflict = conflict3;
                            generalized_repair_ok++;
                        }
                    }
                }
            }
        }

        // For hot variables, do extra minimization passes with different orderings.
        // The greedy removal depends on iteration order; additional passes
        // with different shuffles can find additional removable literals.
        // Scale extra passes with hotness: 1 pass for moderate, 2 for very hot.
        if (repaired_vars_count[y_rep] >= mconf.extra_minim_hot && conflict.size() > 3) {
            int max_extra = (repaired_vars_count[y_rep] >= mconf.extra_minim_very_hot) ? 2 : 1;
            for (int extra = 0; extra < max_extra && conflict.size() > 2; extra++) {
                auto saved = conflict;
                minimize_conflict(conflict, assumps, to_repair);
                assert(std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end());
                if (conflict.size() >= saved.size()) {
                    conflict = saved;
                    break; // no progress, stop
                }
            }
        }

    }
    // Cap very large conflicts to prevent formula bloat. A conflict of 40+
    // literals creates 40+ clauses per repair, leading to 100K+ clause formulas.
    // Try keeping a subset and verify it's still UNSAT.
    if (conflict.size() > mconf.conflict_cap) {
        // Sort: to_repair first, then inputs (more general), then y-vars by freq
        std::sort(conflict.begin(), conflict.end(),
            [&](const Lit& a, const Lit& b) {
                if (a == to_repair) return true;
                if (b == to_repair) return false;
                bool a_inp = is_input[a.var()];
                bool b_inp = is_input[b.var()];
                if (a_inp != b_inp) return a_inp;
                return false;
            });
        assumps.clear();
        for (size_t i = 0; i < mconf.conflict_cap_keep && i < conflict.size(); i++) {
            assumps.push_back(~conflict[i]);
        }
        auto ret_cap = repair_solver.solve(&assumps);
        if (ret_cap == l_False) {
            auto capped = repair_solver.get_conflict();
            if (std::find(capped.begin(), capped.end(), to_repair) != capped.end()) {
                verb_print(2, "[manthan] Capped conflict: " << conflict.size() << " -> " << capped.size());
                conflict = capped;
            }
        }
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
    // Quick batch removal: try keeping only the to_repair literal and the
    // first/last halves of the conflict. If UNSAT, we dramatically reduce
    // the conflict in a single SAT call instead of O(n) individual calls.
    if (conflict.size() > mconf.batch_minim_min) {
        // Try keeping just the first half + to_repair
        for (size_t keep = conflict.size() / 2; keep >= 2; keep /= 2) {
            assumps.clear();
            uint32_t kept = 0;
            for (const auto& l : conflict) {
                if (l == to_repair || kept < keep) {
                    assumps.push_back(~l);
                    if (l != to_repair) kept++;
                }
            }
            auto ret = repair_solver.solve(&assumps);
            if (ret == l_False) {
                auto conflict2 = repair_solver.get_conflict();
                if (std::find(conflict2.begin(), conflict2.end(), to_repair) != conflict2.end()) {
                    verb_print(3, "[manthan] batch minim: " << conflict.size() << " -> " << conflict2.size());
                    conflict = conflict2;
                    break;
                }
            }
        }
    }

    bool removed_any = true;
    set<Lit> dont_remove;
    dont_remove.insert(to_repair);
    // Cap the total number of solver calls during greedy minimization.
    // For large conflicts, uncapped minimization causes O(n^2) solver calls.
    // Budget scales with conflict size but is bounded to prevent excessive work.
    // For large conflicts (>20 lits), cap the number of solver calls to prevent
    // O(n^2) minimization cost. Small conflicts are minimized without limit.
    const uint32_t minim_budget = (conflict.size() > mconf.minim_budget_threshold) ?
        min((uint32_t)(conflict.size() * mconf.minim_budget_mult), mconf.minim_budget_max) :
        std::numeric_limits<uint32_t>::max();
    uint32_t minim_calls = 0;
    while(removed_any) {
        // Sort to try removing the most beneficial literals first:
        // 1. y-variables before inputs (removing y-vars reduces dependencies)
        // 2. Within each category, least-frequent vars first (more likely removable)
        std::sort(conflict.begin(), conflict.end(),
            [this](const Lit& a, const Lit& b) {
                bool a_is_input = is_input[a.var()];
                bool b_is_input = is_input[b.var()];
                if (a_is_input != b_is_input) return !a_is_input; // y-vars first
                uint32_t fa = (a.var() < var_conflict_freq.size()) ? var_conflict_freq[a.var()] : 0;
                uint32_t fb = (b.var() < var_conflict_freq.size()) ? var_conflict_freq[b.var()] : 0;
                return fa < fb;
            });
        removed_any = false;
        for(const auto& try_rem: conflict) {
            if (minim_calls >= minim_budget) { removed_any = false; break; }
            if (dont_remove.count(try_rem)) continue;
            verb_print(3, "Trying to remove conflict literal: " << try_rem);
            assumps.clear();
            for(const auto& l: conflict) {
                if (l == try_rem) continue;
                assumps.push_back(~l);
            }
            release_assert(assumps.size() == conflict.size()-1);
            minim_calls++;
            auto ret2 = repair_solver.solve(&assumps);
            if (ret2 == l_True) {
                dont_remove.insert(try_rem);
                verb_print(3, "[manthan] conf minim. Cannot remove conflict literal (it leads to SAT): "
                        << try_rem
                        << " -- BW: " << backward_defined.count(try_rem.var())
                        << " -- input: " << input.count(try_rem.var()));
                continue;
            }

            // Check if returned conflict is sane
            const uint32_t sz_before = conflict.size();
            auto conflict2 = repair_solver.get_conflict();
            auto it = std::find(conflict2.begin(), conflict2.end(), to_repair);
            if (it == conflict2.end()) {
                // leads to conflict without literal to repair
                verb_print(3, "[manthan] conf minim. Cannot remove conflict literal (it leads to conflict without to_repair): "
                        << try_rem
                        << " -- BW: " << backward_defined.count(try_rem.var())
                        << " -- input: " << input.count(try_rem.var()));
                dont_remove.insert(try_rem);
                continue;
            }

            // OK, sane. Remove and restart
            removed_any = true;
            verb_print(3, "[manthan] conf minim. Removed conflict literal: " << setw(5) << try_rem
                << " sz ch: " << sz_before - conflict2.size());
            conflict = conflict2;
            break;
        }
    }
}

Lit Manthan::map_y_to_y_hat(const Lit& l) const {
    const uint32_t var = l.var();
    // Bytemap is_input is already maintained; the std::set::count was
    // O(log n) per call and this is on the hot perform_repair / lit_to_aig
    // path. y_to_y_hat_vec is the O(1) mirror of y_to_y_hat.
    if (var < is_input.size() && is_input[var]) return l;
    assert(to_define_full.count(var));
    return Lit(y_to_y_hat_fast(var), l.sign());
}

// Update dependency matrix to say that a depends on b
void Manthan::set_depends_on(const uint32_t a, const uint32_t b) {
    assert(!(a < is_input.size() && is_input[a]) && "we are not interested in what input vars depend on");
    if (b < is_input.size() && is_input[b]) {
       //We are not interested if a var depends on the input
       return;
    }
    if (dependency_mat[a][b]) return;

    verb_print(3, a+1 << " depends on " << b+1);
    dependency_mat[a][b] = 1;
    // The synthesis/repair setup is expected to keep dependencies loop-free by design,
    // so release builds only track direct edges.
#ifdef SLOW_DEBUG
    // In slow debug builds, keep transitive closure updated as an extra guard so
    // unexpected dependency loops can be detected more aggressively.
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        dependency_mat[a][i] |= dependency_mat[b][i];
    }
    assert(check_map_dependency_cycles());
#endif
}

void Manthan::perform_repair(const uint32_t y_rep, const sample& ctx, const vector<Lit>& conflict) {
    // Track conflict variable frequency for smarter minimization ordering
    for (const auto& l : conflict) {
        if (l.var() < var_conflict_freq.size()) var_conflict_freq[l.var()]++;
    }

    if (conflict.empty()) {
        verb_print(2, "[manthan] conflict empty for " << setw(5) << y_rep+1 << ", unconditionally fixing it to " << ctx[y_rep]);
        var_to_formula[y_rep] = fh->constant_formula(ctx[y_rep] == l_True);
        updated_y_funcs.push_back(y_rep);
        return;
    }
    verb_print(2, "[manthan] Performing repair on " << setw(5) << y_rep+1
            << " with conflict size " << setw(3) << conflict.size());
    assert(backward_defined.count(y_rep) == 0 && "Backward defined should need NO repair, ever");
    conflict_sizes_sum += conflict.size();

    // not (conflict) -> v = ctx(v)
    FHolder<MetaSolver2>::Formula f;

    auto lit_to_lit = [&] (const Lit l) {
        if (is_input[l.var()] || is_backward_defined[l.var()]) {
            return map_y_to_y_hat(l);
        }
        assert(var_to_formula.count(l.var()));
        auto f2 = var_to_formula.at(l.var());
        return l.sign() ? ~f2.out : f2.out;
    };

    auto lit_to_aig = [&] (const Lit l) {
        if (is_input[l.var()] || is_backward_defined[l.var()]) {
            return AIG::new_lit(map_y_to_y_hat(l));
        }
        assert(var_to_formula.count(l.var()));
        auto f2 = var_to_formula.at(l.var());
        return l.sign() ? AIG::new_not(f2.aig) : f2.aig;
    };

    // CNF part
    vector<Lit> cl;
    cex_solver.new_var();
    auto fresh_l = Lit(cex_solver.nVars()-1, false);
    helpers.insert(fresh_l.var());
    cl.push_back(fresh_l);
    for(const auto& l: conflict) {
        Lit l2;
        if (!mconf.silent_var_update) l2 = lit_to_lit(l);
        else l2 = map_y_to_y_hat(l);
        cl.push_back(l2);
        set_depends_on(y_rep, l);
    }
    f.clauses.emplace_back(cl);

    for(const auto& l: conflict) {
        Lit l2;
        if (!mconf.silent_var_update) l2 = lit_to_lit(l);
        else l2 = map_y_to_y_hat(l);
        cl.clear();
        cl.push_back(~fresh_l);
        cl.push_back(~l2);
        f.clauses.push_back(cl);
    }
    f.out = fresh_l;

    // AIG part
    aig_ptr b1 = nullptr;
    for(const auto& l: conflict) assert(l.var() < cnf.nVars());
    if (conflict.empty()) b1 = aig_mng.new_const(true);
    else {
        if (!mconf.silent_var_update) b1 = lit_to_aig(~conflict[0]);
        else b1 = AIG::new_lit(~conflict[0]);
        for(size_t i = 1; i < conflict.size(); i++) {
            aig_ptr lit_aig;
            if (!mconf.silent_var_update) lit_aig = lit_to_aig(~conflict[i]);
            else lit_aig = AIG::new_lit(~conflict[i]);
            b1 = AIG::new_and(b1, lit_aig);
        }
    }
    f.aig = b1;

    // when fresh_l is true, confl is satisfied → guard is active → use constant
    verb_print(4, "Original formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    verb_print(4, "Branch formula. When this is true, H is wrong:" << endl << f);

    // ITE(guard, TRUE, old) simplifies to OR(guard, old)
    // ITE(guard, FALSE, old) simplifies to AND(NOT(guard), old)
    // These create flatter AIGs with fewer nodes than the generic ITE encoding.
    if (ctx[y_rep] == l_True) {
        var_to_formula[y_rep] = fh->compose_or(f, var_to_formula[y_rep], helpers);
    } else {
        var_to_formula[y_rep] = fh->compose_and(fh->neg(f), var_to_formula[y_rep], helpers);
    }
    updated_y_funcs.push_back(y_rep);

    // For hot variables (repaired many times), periodically simplify the AIG
    // to prevent unbounded growth. Use the full rewriter for very hot variables,
    // and the simpler simplifier for moderately hot ones.
    if (mconf.aig_simplify_every > 0 && repaired_vars_count[y_rep] > 0 && repaired_vars_count[y_rep] % mconf.aig_simplify_every == 0) {
        var_to_formula[y_rep].aig = AIG::simplify_aig(var_to_formula[y_rep].aig);
        verb_print(2, "[manthan] Simplified AIG for hot var " << y_rep+1
            << " (repaired " << repaired_vars_count[y_rep] << " times)");
    }

    verb_print(2, "repaired formula for " << y_rep+1 << " with " << conflict.size() << " vars");
    verb_print(4, "repaired formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    //We fixed the ctx on this variable
    SLOW_DEBUG_DO(assert(check_map_dependency_cycles()));
}

void Manthan::learn_order() {
    assert(y_order.empty());
    verb_print(2, "[manthan] Fixing LEARN order...");
    vector<uint32_t> sorted(to_define_full.begin(), to_define_full.end());
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
    uint64_t td_steps = mconf.td_steps;
    int td_lookahead_iters = mconf.td_lookahead_iters;
    auto tdec = TWD::TreeDecomposition(fc.constructTD(td_steps, td_lookahead_iters));
    tdec.centroid(conf.verb);
    const auto td_width = tdec.width()-1;
    verb_print(2, "[td] FlowCutter FINISHED, TD width: " << td_width);

    const auto& bags = tdec.Bags();
    if (td_width <= 0) {
      verb_print(1, "[td] TD width is 0, ignoring TD");
      return false;
    }

    verb_print(2, "[td] Calculated TD width: " << td_width);
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
    std::vector<int> dists = tdec.distanceFromCentroid();
    for(uint32_t i = 0; i < (uint32_t)tdec.numNodes(); i++)
        max_dist = std::max(max_dist, dists[i]);

    if (max_dist == 0) {
        verb_print(1, "All projected vars are the same distance, ignoring TD");
        return false;
    }
    // When do_td_contract=1, primal_alt only contains to-define vars.
    // When do_td_contract=0, primal_alt contains all cnf vars (including inputs).
    if (mconf.do_td_contract) assert(to_define_full.size() == (uint32_t)primal_alt->numNodes());
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
    const uint32_t old_i = new_to_old.at(i);
    assert(old_i < td_score.size());
    td_score[old_i] = val;
  }
}

void Manthan::topological_sort_order() {
    y_order.clear();
    assert(y_order.empty());
    if (td_score.empty()) td_score.resize(cnf.nVars(), 0.0);
    vector<uint32_t> indeg(cnf.nVars(), 0);
    for(const auto& a: to_define_full) {
        for(const auto& b: to_define_full) {
            if (a == b) continue;
            if (dependency_mat[a][b] == 1) indeg[a]++;
        }
    }

    set<uint32_t> ready;
    for(const auto& v: to_define_full) {
        if (indeg[v] == 0) ready.insert(v);
    }

    while(!ready.empty()) {
        const uint32_t v = *ready.begin();
        ready.erase(ready.begin());
        y_order.push_back(v);

        for(const auto& dep: to_define_full) {
            if (dependency_mat[dep][v] == 0) continue;
            assert(indeg[dep] > 0);
            indeg[dep]--;
            if (indeg[dep] == 0) ready.insert(dep);
        }
    }

    release_assert(y_order.size() == to_define_full.size() && "Topological ordering failed, dependency cycle?");
    order_val.clear();
    order_val.resize(cnf.nVars(), -2);
    for(const auto& x: input) order_val[x] = -1;
    for(uint32_t i = 0; i < y_order.size(); i++) order_val[y_order[i]] = i;
    for(const auto& vv: order_val) assert(vv != -2);
    verb_print(1, "[manthan] Fixed order [TOPO] Final order size: " << y_order.size());
    print_y_order_occur();
}

void Manthan::post_order_vars() {
    if (mconf.manthan_on_the_fly_order)
        topological_sort_order();
}

// Will order 1st the variables that NOTHING depends on
// Will order LAST the variables that depends on EVERYTHING
void Manthan::pre_order_vars() {
    assert(td_score.empty());
    td_score.resize(cnf.nVars(), 0.0);
    assert(order_val.empty());
    assert(y_order.empty());
    const double my_time = cpuTime();
    verb_print(2, "[manthan] Fixing order " << (mconf.manthan_base == 0 ? "[LEARN]" : (mconf.manthan_base == 1 ? "[CONST]" : "[BVE]")) << "...");

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
                if (l.var() == v) {
                    if (l.sign()) num_neg++;
                    else num_pos++;
                    break;
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

#ifdef EXTRA_SYNTH
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
        const auto y_hat = y_to_y_hat_fast(y);
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
        if (mconf.maxsat_order)
            y_to_y_order_pos[y_order[i]] = i+1;
        else
            y_to_y_order_pos[y_order[i]] = y_order.size()-i;
    }

    // Fix to_define variables that are incorrect via assumptions
    for(const auto& y: y_order) {
        const auto y_hat = y_to_y_hat_fast(y);
        if (ctx[y] == ctx[y_hat]) continue;
        const auto l = Lit(y, ctx[y_hat] == l_False);
        verb_print(3, "[find-better-ctx] put into assumps y= " << l);
        int w = y_to_y_order_pos[y];
        s_ctx.addClause(lits_to_ints({l}), w); // want to flip valuation to ctx[y_hat]
    }

    auto ret = s_ctx.solve();
    assert(ret && "must be satisfiable");
    assert(s_ctx.getCost() > 0);
    for(const auto& v: to_define_full) ctx[v] = s_ctx.getValue(v+1) ? l_True : l_False;
}
#endif

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
        const auto y_hat = y_to_y_hat_fast(y);
        const Lit l = Lit(y, ctx[y_hat] == l_False); // literal that makes y match y_hat

        if (ctx[y] == ctx[y_hat]) {
            // Already correct, make this a fixed assumption
            verb_print(3, "[find-better-ctx-normal] CTX is CORRECT on y=" << y+1 << " y_hat=" << y_hat+1
                 << " -- ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat]));
            s.add_clause({l});
        } else {
            // Incorrect, we want to try to fix this
            uint32_t weight = y_to_y_order_pos[y];
            incorrect_lits.emplace_back(l, weight);
            verb_print(3, "[find-better-ctx-normal] CTX is INCORRECT on y=" << y+1
                 << " ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat])
                 << " weight=" << weight);
        }
    }
    assert(incorrect_lits.size() == needs_repair.size());
    for(const auto& c: cnf.get_clauses()) s.add_clause(c);

    // Sort incorrect lits by weight (higher weight = higher priority to fix).
    // Additionally boost weight for variables that were repaired in this session,
    // as they are known to be important for correctness.
    for (auto& [lit, weight] : incorrect_lits) {
        if (repaired_vars_count[lit.var()] > 0) {
            weight += repaired_vars_count[lit.var()];
        }
    }
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
        }
        auto conflict = s.get_conflict();
        assert(!conflict.empty() && "Got UNSAT with empty conflict!");
        verb_print(3, "[find-better-ctx-normal] UNSAT, conflict size: " << conflict.size());

        // Find which soft assumptions are in the conflict and remove them.
        // If the conflict is large (>5 conflicting vars), remove ALL at once
        // rather than one-at-a-time, since the one-at-a-time approach requires
        // many iterations for large conflicts.
        set<Lit> conflict_set(conflict.begin(), conflict.end());
        uint32_t num_conflicting = 0;
        for(const auto& [lit, weight]: incorrect_lits) {
            if (conflict_set.count(~lit) && !cannot_fix.count(lit.var()))
                num_conflicting++;
        }
        bool remove_all = (num_conflicting > mconf.better_ctx_remove_all);
        for(const auto& [lit, weight]: incorrect_lits) {
            if (conflict_set.count(~lit) && !cannot_fix.count(lit.var())) {
                verb_print(3, "[find-better-ctx-normal] Giving up on fixing var " << lit.var()+1);
                cannot_fix.insert(lit.var());
                if (!remove_all) break; // Remove one at a time for small conflicts
            }
        }
    }
}

void Manthan::create_vars_for_y_hats() {
    for(const auto& y: to_define_full) {
        cex_solver.new_var();
        const uint32_t y_hat = cex_solver.nVars()-1;
        y_to_y_hat[y] = y_hat;
        y_hat_to_y[y_hat] = Lit(y, false);
        y_hats.insert(y_hat);
        verb_print(3, "mapping -- y: " << y+1 << " y_hat: " << y_hat+1);
    }
    populate_y_to_y_hat_vec();
}

void Manthan::populate_y_to_y_hat_vec() {
    y_to_y_hat_vec.assign(cnf.nVars(), std::numeric_limits<uint32_t>::max());
    for (const auto& [y, y_hat] : y_to_y_hat) {
        if (y < y_to_y_hat_vec.size()) y_to_y_hat_vec[y] = y_hat;
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
            if (to_define_full.count(l.var())) cl.push_back(Lit(y_to_y_hat_fast(l.var()), l.sign()));
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

    // Replace y with y_hat. Each repair appends ~3-4 fresh clauses per
    // hot var; with several thousand repairs the per-literal hot loop
    // visits millions of literals — the std::set::count was the cost
    // here, the bytemap brings it to a single byte load.
    vector<Lit> cl2;
    for(auto& k: updated_y_funcs) {
        auto& form = var_to_formula.at(k);
        for(auto& cl: form.clauses) {
            if (cl.inserted) continue;
            cl2.clear();
            cl2.reserve(cl.lits.size());
            for(const auto& l: cl.lits) {
                const auto v = l.var();
                if (v < is_to_define_full.size() && is_to_define_full[v]) {
                    cl2.emplace_back(y_to_y_hat_fast(v), l.sign());
                } else cl2.push_back(l);
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
        helpers.insert(ind);

        assert(var_to_formula.count(y));
        for(const auto& cl: var_to_formula[y].clauses) assert(cl.inserted && "All clauses must have been inserted");
        const auto& form_out = var_to_formula[y].out;
        const auto& y_hat = y_to_y_hat_fast(y);

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

        if (mconf.force_bw_equal
            && y < is_backward_defined.size() && is_backward_defined[y]
            && !(y < is_helper_function.size() && is_helper_function[y])) {
            verb_print(3, "backward defined y (except helper function), forcing indic to TRUE, since it must be correct");
            cex_solver.add_clause({Lit(ind, false)});
        }
    }
    updated_y_funcs.clear();
}

vector<sample> Manthan::collect_extra_cex(const sample& ctx) {
    if (mconf.multi_cex_k <= 1) return {{ctx}};

    // Collect additional counterexamples by blocking previous ones
    vector<sample> all_cex = {ctx};
    vector<uint32_t> block_acts;
    for(int i = 0; i < mconf.multi_cex_k - 1; i++) {
        // Add activation-gated blocking clause: act OR (x1_flip OR x2_flip OR ...)
        // When act is not assumed, solver can set act=true -> clause trivially satisfied
        // When we assume ~act, blocking is active
        cex_solver.new_var();
        uint32_t act = cex_solver.nVars()-1;
        helpers.insert(act);
        block_acts.push_back(act);
        vector<Lit> block_cl;
        block_cl.reserve(1 + input.size());
        block_cl.push_back(Lit(act, false)); // positive act
        for(const auto& x: input) {
            block_cl.push_back(Lit(x, all_cex.back()[x] == l_True));
        }
        cex_solver.add_clause(block_cl);

        // Build assumptions: activate all blocking clauses + indicator assumptions
        vector<Lit> assumps;
        assumps.reserve(block_acts.size() + y_hat_to_indic.size());
        for(auto a: block_acts) assumps.push_back(Lit(a, true)); // ~act activates blocking
        for(const auto& [y_hat, ind]: y_hat_to_indic) {
            uint32_t y = indic_to_y[ind];
            if (mconf.force_bw_equal
                && y < is_backward_defined.size() && is_backward_defined[y]
                && !(y < is_helper_function.size() && is_helper_function[y]))
                continue;
            assumps.push_back(Lit(ind, false));
        }

        auto ret = cex_solver.solve(&assumps);
        if (ret != l_True) break;
        all_cex.push_back(cex_solver.get_model());
    }

    // Force activation vars to true, permanently satisfying (disabling) blocking clauses
    for(auto a: block_acts) cex_solver.add_clause({Lit(a, false)});

    if (all_cex.size() <= 1) return {ctx};

    // Pick the CEX with lowest weighted repair cost.
    // Variables early in y_order are repaired first, and their repairs
    // cascade to affect later variables. Give them much higher weight
    // so we prefer CEXes where early variables are correct.
    size_t best_idx = 0;
    uint64_t best_cost = std::numeric_limits<uint64_t>::max();
    for(size_t i = 0; i < all_cex.size(); i++) {
        uint64_t cost = 0;
        uint32_t rank = 0;
        for(const auto& y: y_order) {
            rank++;
            if (all_cex[i][y] != all_cex[i][y_to_y_hat_fast(y)]) {
                // Quadratic weight by order position: early vars matter much more.
                // Also boost by repair count for frequently-repaired vars.
                uint64_t pos_weight = (y_order.size() - rank + 1);
                cost += pos_weight * pos_weight + repaired_vars_count[y] * 10;
            }
        }
        verb_print(3, "[manthan] cex " << i << " has weighted repair cost " << cost);
        if (cost < best_cost) { best_cost = cost; best_idx = i; }
    }
    if (best_idx != 0) {
        verb_print(2, "[manthan] Switching to cex " << best_idx << " with cost " << best_cost);
        std::swap(all_cex[0], all_cex[best_idx]);
    }

    verb_print(2, "[manthan] Collected " << all_cex.size() << " counterexamples");
    return all_cex;
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
        if (mconf.force_bw_equal
            && y < is_backward_defined.size() && is_backward_defined[y]
            && !(y < is_helper_function.size() && is_helper_function[y]))
            continue; // already forced to true
        assumps.emplace_back(ind, false);
    }
    if (mconf.force_bw_equal) assert(assumps.size() == y_order.size() - backward_defined.size());
    else assert(assumps.size() == y_order.size());

    verb_print(4, "assumptions: " << assumps);
    cex_solver.set_verbosity(conf.verb <= 2 ? 0 : conf.verb-1);
    if (num_loops_repair == 1 || (
                mconf.simplify_every > 0 && (num_loops_repair % mconf.simplify_every) == (mconf.simplify_every-1)))
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
        assert(!needs_repair.empty() && "If we found a counterexample, there must be something to repair!");
        return false;
    }
    assert(ret == l_False);
    verb_print(2, "Formula is good!");
    return true;
}

// Checks if flipping variable v in sample s satisfies all clauses
vector<const sample*> Manthan::filter_samples(const uint32_t v, const vector<sample>& samples) {
    auto check_satisfied_all_cls_with_flip = [](const sample& s, const uint32_t v2, const vector<const vector<Lit>*>& clause_ptrs) -> bool {
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
    vector<const sample*> filtered_samples;
    vector<const vector<Lit>*> clause_ptrs;
    for(const auto& cl: cnf.get_clauses()) {
        bool found = false;
        for(const auto& l: cl) {
            if (l.var() == v) {
                found = true;
                break;
            }
        }
        if (found) clause_ptrs.push_back(&cl);
    }
    for(const auto& s: samples) {
        bool ret = check_satisfied_all_cls_with_flip(s, v, clause_ptrs);
        if (!ret) {
            // sample is good
            filtered_samples.push_back(&s);
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

bool Manthan::has_dependency_cycle_dfs(const uint32_t node, vector<uint8_t>& color, vector<uint32_t>& path) const {
    color[node] = 1; // Mark as being processed (gray)
    path.push_back(node);

    for(uint32_t i = 0; i < dependency_mat[node].size(); i++) {
        if (dependency_mat[node][i] == 0) continue; // No dependency

        if (color[i] == 1) {
            // Found a back edge - cycle detected
            path.push_back(i);
            return true;
        }
        if (color[i] == 0) {
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

void Manthan::recompute_all_y_hat_cnf(sample& ctx) {
    vector<Lit> assumps;
    assumps.reserve(input.size() + y_order.size() + y_hat_to_indic.size());
    for(const auto& x: input) {
        assumps.push_back(Lit(x, ctx[x] == l_False));
    }
    for(const auto& [y_hat, ind]: y_hat_to_indic) {
        uint32_t y = indic_to_y[ind];
        if (mconf.force_bw_equal && y < is_backward_defined.size() && is_backward_defined[y]) continue;
        assumps.push_back(Lit(ind, false));
    }

    lbool ret = cex_solver.solve(&assumps, 1);
    assert(ret == l_True);
    const auto& m = cex_solver.get_model(1);
    for(const auto& y: y_order) {
        uint32_t y_hat = y_to_y_hat_fast(y);
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
        if (!found) continue; // skip vars before y_rep
        if (!var_to_formula.count(y)) continue; // skip vars without formulas
        const auto& aig = var_to_formula.at(y).aig;
        assert(aig != nullptr && "All formulas should have AIGs for evaluation");
        lbool val = AIG::evaluate(ctx, aig, defs, cache);
        if (val == l_Undef) continue;
        ctx[y_to_y_hat_fast(y)] = val;
    }
    verb_print(2, "Recomputed all y_hat values in ctx.");
}

void Manthan::compute_needs_repair(const sample& ctx) {
    assert(ctx[fh->get_true_lit().var()] == l_True);
    needs_repair.clear();
    for(const auto& y: to_define_full) {
        if (ctx[y] != ctx[y_to_y_hat_fast(y)]) needs_repair.insert(y);
    }
}

void Manthan::check_repair_monotonic() {
    mpz_class cnt;
    if (!count_error_formula(cnt)) return;

    if (prev_error_count >= 0) {
        if (cnt >= prev_error_count) {
            cout << "c o ERROR [manthan-checkrepair] Error count did NOT strictly decrease: "
                 << prev_error_count << " -> " << cnt << endl;
        }
        assert(cnt < prev_error_count &&
            "Error formula count must strictly decrease after each repair iteration");
        verb_print(1, "[manthan-checkrepair] Error count decreased: "
            << prev_error_count << " -> " << cnt << " (good)");
    }
    prev_error_count = cnt;
}

Lit Manthan::tseitin_encode_aig(
    const aig_ptr& aig,
    const map<uint32_t, uint32_t>& count_y_to_y_hat,
    vector<vector<Lit>>& clauses,
    uint32_t& next_var,
    Lit true_lit,
    map<aig_ptr, Lit>& cache)
{
    auto it = cache.find(aig);
    if (it != cache.end()) return it->second;

    Lit result = lit_Error;
    if (aig->type == AIGT::t_const) {
        // const node is positive TRUE; edge sign flips it.
        result = aig.neg ? ~true_lit : true_lit;
    } else if (aig->type == AIGT::t_lit) {
        // Leaf: map to_define_full vars to y_hat, others stay as-is.
        // Sign lives on the referring edge.
        uint32_t v = aig->var;
        auto map_it = count_y_to_y_hat.find(v);
        if (map_it != count_y_to_y_hat.end()) v = map_it->second;
        result = Lit(v, aig.neg);
    } else {
        assert(aig->type == AIGT::t_and);
        // Children are signed edges (aig_lit); the recursive call returns
        // the CNF literal with the edge sign already applied.
        Lit left_lit = tseitin_encode_aig(aig->l, count_y_to_y_hat, clauses, next_var, true_lit, cache);
        Lit right_lit = tseitin_encode_aig(aig->r, count_y_to_y_hat, clauses, next_var, true_lit, cache);

        // Allocate gate variable for: gate = left AND right
        uint32_t gate_var = next_var++;
        Lit gate = Lit(gate_var, false);

        clauses.push_back({~gate, left_lit});
        clauses.push_back({~gate, right_lit});
        clauses.push_back({gate, ~left_lit, ~right_lit});

        // Outer edge sign flips the gate output.
        result = aig.neg ? ~gate : gate;
    }

    cache[aig] = result;
    return result;
}

bool Manthan::count_error_formula(mpz_class& out_count) {
    const double count_start = cpuTime();

    // Build variable mapping: y -> y_hat for counting formula
    map<uint32_t, uint32_t> count_y_to_y_hat;
    uint32_t next_var = cnf.nVars();
    for (const auto& y : to_define_full) {
        count_y_to_y_hat[y] = next_var++;
    }

    // Allocate a true literal
    uint32_t true_var = next_var++;
    Lit true_lit(true_var, false);

    vector<vector<Lit>> clauses;

    // Force true literal
    clauses.push_back({true_lit});

    // 1. Add F(x, y) - original CNF clauses
    for (const auto& cl : cnf.get_clauses()) clauses.push_back(cl);
    for (const auto& cl : cnf.get_red_clauses()) clauses.push_back(cl);

    // 2. Add ~F(x, y_hat) - negation of F with y -> y_hat substitution
    // For each clause, create indicator: ind_i <-> clause_i[y->y_hat] is satisfied
    // Then add: at least one clause is NOT satisfied
    vector<Lit> neg_clause;
    for (const auto& cl_orig : cnf.get_clauses()) {
        // Substitute y -> y_hat
        vector<Lit> cl_subst;
        for (const auto& l : cl_orig) {
            auto it = count_y_to_y_hat.find(l.var());
            if (it != count_y_to_y_hat.end())
                cl_subst.push_back(Lit(it->second, l.sign()));
            else
                cl_subst.push_back(l);
        }

        // Create clause indicator: cl_ind <-> OR(cl_subst)
        uint32_t cl_ind_var = next_var++;
        Lit cl_ind(cl_ind_var, false);

        // cl_ind -> OR(cl_subst): ~cl_ind OR l1 OR l2 OR ...
        vector<Lit> impl_cl = {~cl_ind};
        for (const auto& l : cl_subst) impl_cl.push_back(l);
        clauses.push_back(impl_cl);

        // OR(cl_subst) -> cl_ind: for each li, ~li -> cl_ind, i.e., cl_ind OR ~li
        for (const auto& l : cl_subst) {
            clauses.push_back({cl_ind, ~l});
        }

        // We want: at least one clause unsatisfied, i.e., at least one ~cl_ind
        neg_clause.push_back(~cl_ind);
    }
    clauses.push_back(neg_clause);

    // 3. Add synthesized function definitions: y_hat = f(x)
    // For each y, Tseitin-encode the AIG and equate to y_hat
    map<aig_ptr, Lit> tseitin_cache;
    for (const auto& y : to_define_full) {
        assert(var_to_formula.count(y));
        const auto& aig = var_to_formula.at(y).aig;
        assert(aig != nullptr);

        Lit func_out = tseitin_encode_aig(aig, count_y_to_y_hat, clauses, next_var, true_lit, tseitin_cache);
        uint32_t y_hat = count_y_to_y_hat.at(y);
        Lit y_hat_lit(y_hat, false);

        // y_hat <-> func_out
        // y_hat OR ~func_out
        clauses.push_back({y_hat_lit, ~func_out});
        // ~y_hat OR func_out
        clauses.push_back({~y_hat_lit, func_out});
    }

    // 4. Set up ganak and count
    // 4. Write DIMACS to temp file and invoke ganak subprocess
    auto tmp_path = std::filesystem::temp_directory_path() /
        ("arjun_checkrepair_" + std::to_string(getpid()) + ".cnf");
    string tmp_fname = tmp_path.string();
    {
        std::ofstream out(tmp_fname);
        out << "p cnf " << next_var << " " << clauses.size() << "\n";
        // Write independent support (input vars, 1-based)
        out << "c p show ";
        for (const auto& x : input) out << (x + 1) << " ";
        out << "0\n";
        // Write clauses
        for (const auto& cl : clauses) {
            for (const auto& l : cl) {
                out << (l.sign() ? -((int)l.var() + 1) : (int)l.var() + 1) << " ";
            }
            out << "0\n";
        }
    }

    verb_print(2, "[manthan-checkrepair] Wrote error formula: "
        << next_var << " vars, " << clauses.size() << " clauses to " << tmp_fname);

    // Run ganak with minimal verbosity
    string cmd = mconf.ganak_binary + " --verb 0 " + tmp_fname + " 2>&1";
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        cout << "c o ERROR [manthan-checkrepair] Failed to run ganak: " << cmd << endl;
        std::filesystem::remove(tmp_path);
        return false;
    }

    bool found_count = false;
    char buf[4096];
    while (fgets(buf, sizeof(buf), pipe)) {
        string line(buf);
        // Parse "c s exact arb int <count>" (count can be arbitrarily large)
        const string prefix = "c s exact arb int ";
        auto pos = line.find(prefix);
        if (pos != string::npos) {
            string count_str = line.substr(pos + prefix.size());
            // Trim whitespace/newline
            while (!count_str.empty() && (count_str.back() == '\n' || count_str.back() == '\r' || count_str.back() == ' '))
                count_str.pop_back();
            if (!count_str.empty()) {
                try {
                    out_count = mpz_class(count_str);
                    found_count = true;
                } catch (...) {
                    cout << "c o ERROR [manthan-checkrepair] Failed to parse count: '" << count_str << "'" << endl;
                }
            }
        }
    }
    int ret = pclose(pipe);
    std::filesystem::remove(tmp_path);

    if (ret != 0 || !found_count) {
        cout << "c o ERROR [manthan-checkrepair] ganak failed (ret=" << ret << ")" << endl;
        return false;
    }

    verb_print(1, "[manthan-checkrepair] Error formula count: " << out_count
        << "  vars: " << next_var << "  clauses: " << clauses.size()
        << "  T: " << fixed << setprecision(2) << (cpuTime() - count_start));

    return true;
}
