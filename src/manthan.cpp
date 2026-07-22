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
#include <vector>
#include <algorithm>
#include <ranges>
#include "constants.h"
#include "metasolver.h"
#include "time_mem.h"
#include <fstream>
#include <sstream>
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
#include <mlpack/methods/decision_tree/decision_tree.hpp>
#include <armadillo>
#include "EvalMaxSAT.h"
#include "manthan_learn.h"
#endif

using std::min;
using std::sort;
using std::vector;
using std::set;
using std::map;
using std::string;
using std::setprecision;
using std::fixed;
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

vector<sample> Manthan::get_cmsgen_samples(uint32_t num) {
    // Sampling costs one SAT solve each; halve it on large to-define sets.
    if (to_define.size() > 200) num = std::max<uint32_t>(1, num / 2);
    verb_print(1, "[manthan] Getting " << num << " CMSGen samples...");

    const double my_time = cpuTime();
    SATSolver solver_samp;
    solver_samp.set_seed(conf.seed);
    inject_cnf(solver_samp);
    solver_samp.set_up_for_sample_counter(mconf.sampler_fixed_conflicts);

    vector<sample> samples;
    for (uint32_t i = 0; i < num; i++) {
        auto ret = solver_samp.solve();
        assert(ret == l_True);
        assert(solver_samp.get_model().size() == cnf.nVars());
        samples.push_back(solver_samp.get_model());
    }
    verb_print(1, "[manthan] CMSGen got " << samples.size() << " samples."
            << " T: " << setprecision(2) << std::fixed << (cpuTime() - my_time));
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
    for (const auto& v : input) is_input[v] = 1;
    for (const auto& v : backward_defined) is_backward_defined[v] = 1;
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
    // If A depends on B and B depends on C, then A must already depend on C.
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
        MetaSolver& solver;
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
        FHolder<MetaSolver>::Formula f;

        const auto orig = new_to_orig.at(v);
        const uint32_t v_orig = orig.var();
        const auto& aig = cnf.get_def(v_orig);
        assert(aig != nullptr);

        // Remap AIG leaves from orig var space into y_hat space (baking in
        // orig.sign()) — AIGToCNF consumes raw lit vars, so the remap must
        // live in the AIG.
        f.aig = AIG::translate_leaves(
            aig,
            [&](uint32_t var_orig2) {
                return map_y_to_y_hat(cnf.orig_to_new_lit(Lit(var_orig2, false)));
            },
            orig.sign());

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
    // Deep-copy together in one go (preserves cycles, doesn't mutate originals).
    vector<aig_lit> aigs(cnf.nVars(), nullptr);
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


    // Shared helper defs first: the formulas' .out chains reference them.
    for(const auto& cl: shared_helper_cls) s.add_clause(cl);
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
    verb_print(4, "[check] START nVars=" << cex_solver.nVars() << " helpers.size=" << helpers.size());
    for(const auto& cl: shared_helper_cls) {
        for(const auto& l: cl) {
            const uint32_t var = l.var();
            if (input.count(var)) continue;
            assert((y_hats.count(var) || helpers.count(var)
                    || var == fh->get_true_lit().var())
                && "shared helper clause vars must be y_hat/helper/true/input");
        }
    }
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

// SLOW_DEBUG: fresh SAT miter from .clauses+.out (cex_solver's encoding minus
// indicator gating). UNSAT = correct; SAT = encoding bug cex_solver missed.
bool Manthan::check_synth_via_clauses(const string& where) const {
    SATSolver s;
    while (s.nVars() < cex_solver.nVars()) s.new_var();
    s.add_clause({fh->get_true_lit()});

    // Orig CNF on x + y (0..cnf.nVars()-1) — same var namespace cex_solver uses.
    for (const auto& c : cnf.get_clauses()) s.add_clause(c);

    // Shared helper defs from init_from_guess's batch encode.
    for (const auto& cl : shared_helper_cls) s.add_clause(cl);

    // Add every formula's clauses + couple its y_hat to its .out
    // unconditionally (no indicator).
    for (const auto& y : to_define_full) {
        auto it = var_to_formula.find(y);
        if (it == var_to_formula.end()) continue;
        const auto& f = it->second;
        for (const auto& cl : f.clauses) s.add_clause(cl.lits);
        uint32_t y_hat = y_to_y_hat.at(y);
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
                cl_sub.emplace_back(y_to_y_hat.at(l.var()), l.sign());
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
                        uint32_t yh = y_to_y_hat.at(v);
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

// SLOW_DEBUG: same miter as check_synth_via_clauses, but encoded from .aig
// (what becomes cnf.defs[y]). Disagreement with the .clauses check pinpoints
// an AIG-vs-CNF rep divergence; failure here alone suggests a leaf-sub issue.
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

    // Tseitin-encode each .aig onto shadow_y_hats. Leaves: to_define_full ->
    // shadow_y_hat[v]; Manthan-internal y_hat leaf -> shadow via y_hat_to_y;
    // else raw.
    std::unordered_map<const AIG*, Lit> cache;
    std::function<Lit(const aig_lit&)> enc_edge = [&](const aig_lit& n) -> Lit {
        assert(n != nullptr);
        if (n->type == AIGT::t_const) return n.neg ? ~true_l : true_l;
        if (n->type == AIGT::t_lit) {
            uint32_t v = n->var;
            Lit base;
            if (to_define_full.count(v)) {
                base = shadow_y_hat.at(v);
            } else if (y_hat_to_y.count(v)) {
                // Manthan y_hat leaf. Inputs map to themselves, so reaching
                // here means backward_defined -> use shadow.
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

// SLOW_DEBUG: per-y pairwise miter proving f.aig == f.out under f.clauses.
// Fires on the exact y whose AIG and CNF reps diverge.
bool Manthan::check_aig_matches_clauses_per_formula(const string& where) const {
    for (const auto& y : to_define_full) {
        auto it = var_to_formula.find(y);
        if (it == var_to_formula.end()) continue;
        const auto& f = it->second;
        if (f.aig == nullptr) continue;

        SATSolver s;
        while (s.nVars() < cex_solver.nVars()) s.new_var();
        s.add_clause({fh->get_true_lit()});
        // Add ALL formulas' clauses: helper vars are shared across formulas,
        // so a helper in this f.out may be defined in another's .clauses.
        for (const auto& [yy, ff] : var_to_formula) {
            for (const auto& cl : ff.clauses) s.add_clause(cl.lits);
        }
        // Shared helper defs from init_from_guess's batch encode.
        for (const auto& cl : shared_helper_cls) s.add_clause(cl);

        // Tseitin-encode f.aig in the SAME var namespace, mapping leaves
        // exactly as bve_and_substitute/perform_repair do (value over y_hat).
        std::unordered_map<const AIG*, Lit> cache;
        std::function<Lit(const aig_lit&)> enc_edge = [&](const aig_lit& n) -> Lit {
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
                if (to_define_full.count(v)) base = Lit(y_to_y_hat.at(v), false);
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
            cout << "c o [aig_vs_clauses]   y_hat_var=" << (y_to_y_hat.at(y)+1)
                 << " f.out=" << f.out
                 << " aig.type=" << (int)f.aig->type
                 << " aig.neg=" << f.aig.neg
                 << " bw_def=" << backward_defined.count(y)
                 << " to_define=" << to_define.count(y)
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
            // Leaves are y-space orig vars: read m[y_hat[v]] for to_define_full,
            // m[v] for inputs.
            std::map<const AIG*, bool> eval_cache;
            std::function<bool(const aig_lit&)> eval_aig = [&](const aig_lit& n) -> bool {
                if (n->type == AIGT::t_const) return !n.neg;  // const TRUE is base, edge may flip
                if (n->type == AIGT::t_lit) {
                    uint32_t v = n->var;
                    bool val;
                    if (to_define_full.count(v)) {
                        uint32_t yh = y_to_y_hat.at(v);
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
            // Full recursive AIG structure dump — VERBOSE_DEBUG only.
            VERBOSE_DEBUG_DO({
                std::set<uint64_t> printed_nids;
                std::function<void(const aig_lit&, int)> dump_aig = [&](const aig_lit& n, int depth) {
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

// Prefer FALSE, i.e. it should be false unless we have evidence otherwise
// Hence, we only care about clauses where v appears positively
void Manthan::bve_and_substitute() {
    const double start_time = cpuTime();
    map<Lit, aig_lit> lit_to_aig;

    auto get_aig = [&](const Lit l) {
      if (lit_to_aig.count(l)) return lit_to_aig.at(l);
      aig_lit aig = AIG::new_lit(l);
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

    vector<aig_lit> aigs;
    for(const auto& y: y_order) {
        if (!to_define.count(y)) continue;
        assert(var_to_formula.count(y) == 0);

        map<uint32_t, aig_lit> transformed;

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
        aig_lit overall = nullptr;

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
            aig_lit current = nullptr;
            for(const auto& l: cl) {
                if (l.var() == y) continue;
                if (later_in_order(y, l.var())) {
                    aig_lit aig = get_aig(~l);
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
    rw.rewrite_all(aigs, conf.verb);
    encode_aigs_to_formulas(aigs, start_time);

    verb_print(1, COLYEL "[manthan] BVE and substitute done."
        << " funs: " << setw(6) << to_define.size()
        << " funs/s: " << setw(6) << fixed << setprecision(2) << safe_div(to_define.size(),(cpuTime()-start_time))
        << " T: " << setw(5) << (cpuTime()-start_time)
        << " mem: " << memUsedTotal()/(1024.0*1024.0) << " MB");
}

// Encode per-y AIGs (one per to_define var, y_order sequence, orig var space)
// into var_to_formula.
void Manthan::encode_aigs_to_formulas(const vector<aig_lit>& aigs, const double start_time) {
    assert(aigs.size() == to_define.size());

    // One AIGToCNF encoder per formula. A shared encoder is unsound: cached
    // Lits get reused across formulas (AIGRewriter reshuffles aigs), so .aig
    // and .clauses+.out diverge — cex_solver stays happy but exported AIGs are
    // wrong. Caught by check_aig_matches_clauses_per_formula under SLOW_DEBUG.
    struct FormulaClauseSink {
        MetaSolver& solver;
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

    uint32_t num_done = 0;
    uint32_t at = 0;
    for(const auto& y: y_order) {
        if (!to_define.count(y)) continue;
        FHolder<MetaSolver>::Formula f;
        f.aig = aigs.at(at);

        // Fresh encoder per formula — see comment above FormulaClauseSink.
        ArjunNS::AIGToCNF<FormulaClauseSink> enc(sink);
        enc.set_true_lit(fh->get_true_lit());

        aig_lit aig_yhat = AIG::translate_leaves(
            f.aig,
            [&](uint32_t var2) { return map_y_to_y_hat(Lit(var2, false)); });

        sink.clauses = &f.clauses;
        uint32_t nv_before = cex_solver.nVars();
        size_t h_before = helpers.size();
        f.out = enc.encode(aig_yhat);
        uint32_t nv_after = cex_solver.nVars();
        size_t h_after = helpers.size();
        verb_print(4, "[aig-enc] y=" << (y+1)
                  << " cex_solver.nVars " << nv_before << "->" << nv_after
                  << " helpers " << h_before << "->" << h_after);
        var_to_formula[y] = f;

        num_done++;
        if (num_done % 50 == 0 && num_done > 0) {
            verb_print(1, "[manthan] done encoding AIGs"
                << " funs: " << setw(6) << num_done
                << " funs/s: " << setw(6) << fixed << setprecision(2) << safe_div(num_done,(cpuTime()-start_time))
                << " T: " << setw(5) << (cpuTime()-start_time)
                << " mem: " << memUsedTotal()/(1024.0*1024.0) << " MB");
        }
        at++;
    }

    assert(check_aig_dependency_cycles());
}

// Seed var_to_formula from the previous round's AIGs: compact, refill
// dependency_mat, re-Tseitin. Replaces the manthan_base init.
void Manthan::init_from_guess() {
    const double start_time = cpuTime();
    assert(!guess.empty());

    vector<aig_lit> aigs;
    aigs.reserve(to_define.size());
    for(const auto& y: y_order) {
        if (!to_define.count(y)) continue;
        assert(guess.count(y) && "guess must cover every to_define var");
        aigs.push_back(guess.at(y));
    }
    assert(aigs.size() == to_define.size());

    const size_t nodes_before = AIG::count_aig_nodes_fast(aigs);
    AIGRewriter rw;
    rw.rewrite_all(aigs, conf.verb);
    const size_t nodes_after = AIG::count_aig_nodes_fast(aigs);
    verb_print(1, COLYEL "[manthan-restart] guess AIGs compacted: "
        << nodes_before << " -> " << nodes_after << " nodes ("
        << fixed << setprecision(1)
        << (nodes_before ? 100.0 * ((double)nodes_before - (double)nodes_after) / (double)nodes_before : 0.0)
        << "% less) T: " << setprecision(2) << (cpuTime() - start_time));

    // Mirror each guess AIG's leaves into dependency_mat.
    uint32_t at = 0;
    set<uint32_t> deps;
    for(const auto& y: y_order) {
        if (!to_define.count(y)) continue;
        deps.clear();
        AIG::get_dependent_vars(aigs[at], deps, y);
        for(const auto& d: deps) {
            if (input.count(d)) continue;
            assert(later_in_order(y, d) &&
                "guess AIG must only depend on earlier vars in the (deterministic) order");
            set_depends_on(y, d);
        }
        at++;
    }

    install_shared_encoded_formulas(aigs);
    assert(check_aig_dependency_cycles());

    guess.clear();
    verb_print(1, COLYEL "[manthan-restart] guess encoded (shared)."
        << " funs: " << setw(6) << to_define.size()
        << " shared cls: " << shared_helper_cls.size()
        << " T: " << setw(5) << fixed << setprecision(2) << (cpuTime()-start_time)
        << " mem: " << memUsedTotal()/(1024.0*1024.0) << " MB");
}

// Encode all AIGs with one shared AIGToCNF batch so cross-formula nodes stay
// shared. Needs (1) one transform cache across all roots for the y->y_hat leaf
// translation; (2) helper defs in shared_helper_cls (inserted once), not in
// any formula's .clauses which a repair may drop.
void Manthan::install_shared_encoded_formulas(const vector<aig_lit>& aigs) {
    assert(aigs.size() == to_define.size());
    vector<aig_lit> aig_yhats;
    aig_yhats.reserve(aigs.size());
    {
        std::map<aig_lit, aig_lit> tcache;
        auto visit = [&](AIGT type, uint32_t var,
                         const aig_lit* l, const aig_lit* r) -> aig_lit {
            if (type == AIGT::t_const) return AIG::new_const(true);
            if (type == AIGT::t_lit)   return AIG::new_lit(map_y_to_y_hat(Lit(var, false)));
            return AIG::new_and(*l, *r);
        };
        for(const auto& a: aigs)
            aig_yhats.push_back(AIG::transform<aig_lit>(a, visit, tcache));
    }

    struct SharedClauseSink {
        MetaSolver& solver;
        std::vector<std::vector<Lit>>& cls;
        std::set<uint32_t>& helpers_set;
        void new_var() {
            solver.new_var();
            helpers_set.insert(solver.nVars() - 1);
        }
        [[nodiscard]] uint32_t nVars() const { return solver.nVars(); }
        void add_clause(const std::vector<Lit>& cl) { cls.push_back(cl); }
    };
    // Only the new suffix of shared_helper_cls is inserted below.
    const size_t cls_start = shared_helper_cls.size();
    SharedClauseSink sink{cex_solver, shared_helper_cls, helpers};
    ArjunNS::AIGToCNF<SharedClauseSink> enc(sink);
    enc.set_true_lit(fh->get_true_lit());
    const vector<Lit> outs = enc.encode_batch(aig_yhats);
    assert(outs.size() == aigs.size());

    uint32_t at = 0;
    for(const auto& y: y_order) {
        if (!to_define.count(y)) continue;
        FHolder<MetaSolver>::Formula f;
        f.aig = aigs.at(at);
        f.out = outs.at(at);
        var_to_formula[y] = f;
        at++;
    }
    // Shared clauses are already in y_hat/input/helper space; insert directly.
    for(size_t i = cls_start; i < shared_helper_cls.size(); i++)
        cex_solver.add_clause(shared_helper_cls[i]);
}

// AIG snapshot of every to_define formula (orig var space); feeds the next
// round's guess.
std::map<uint32_t, aig_lit> Manthan::export_formula_aigs() const {
    std::map<uint32_t, aig_lit> ret;
    for(const auto& y: to_define) {
        assert(var_to_formula.count(y));
        assert(var_to_formula.at(y).aig != nullptr);
        ret[y] = var_to_formula.at(y).aig;
    }
    return ret;
}

void ManthanStats::print_stats(const string& txt, const string& color, const string& extra) const {
    const double repair_time = cpuTime() - repair_start_time;
    col_print(color << "[manthan]" << txt
            << " rep: " << setw(6) << tot_repaired
            << "   loops: "<< setw(6) << num_loops_repair
            << "   avg rep/loop: " << setprecision(1) << setw(4) << (double)tot_repaired/(num_loops_repair+0.0001)
            << "   avg conflsz: " << setw(6) << fixed << setprecision(2) << (double)conflict_sizes_sum/(tot_repaired+0.0001)
            << "   avg need rep: " << setw(6) << fixed << setprecision(2) << (double)needs_repair_sum/(num_loops_repair+0.0001)
            << "   input-only: " << setw(4) << input_only_rep
            << "   T: " << setprecision(2) << fixed << setw(7) << repair_time
            << "   rep/s: " << setprecision(4) << safe_div(tot_repaired,repair_time) << setprecision(2)
            << extra);
}

void Manthan::print_detailed_stats(const ManthanStats& stats) const {
    verb_print(1, COLCYN "[manthan-stats] === CONFLICT STATS ===");
    verb_print(1, COLCYN "[manthan-stats]   input-only conflicts: " << stats.input_only_conflict_count
        << "  avg sz: " << fixed << setprecision(1) << safe_div(stats.input_only_conflict_sizes_sum, stats.input_only_conflict_count));
    verb_print(1, COLCYN "[manthan-stats]   full conflicts:       " << stats.full_conflict_count
        << "  avg sz: " << fixed << setprecision(1) << safe_div(stats.full_conflict_sizes_sum, stats.full_conflict_count));
    verb_print(1, COLCYN "[manthan-stats]   cost-zero repairs:    " << stats.cost_zero_repairs);
    verb_print(1, COLCYN "[manthan-stats]   repair_failed:        " << stats.repair_failed);
    verb_print(1, COLCYN "[manthan-stats]   cex_solver calls:     " << stats.cex_solver_calls);
    verb_print(1, COLCYN "[manthan-stats]   repair_solver calls:  " << stats.repair_solver_calls);
    // Repair recurrence: a single var repaired hundreds/thousands of
    // times means the repairs of that var are not generalising at all.
    {
        uint32_t max_rep = 0, max_rep_var = 0;
        uint64_t vars_over_100 = 0, vars_over_1000 = 0;
        for (uint32_t v = 0; v < repaired_vars_count.size(); v++) {
            const uint32_t r = repaired_vars_count[v];
            if (r > max_rep) { max_rep = r; max_rep_var = v; }
            if (r > 100) vars_over_100++;
            if (r > 1000) vars_over_1000++;
        }
        verb_print(1, COLCYN "[manthan-stats]   repair recurrence:    max "
            << max_rep << " on var " << max_rep_var+1
            << "  (vars >100x: " << vars_over_100
            << ", >1000x: " << vars_over_1000 << ")");
    }

    // Print top 20 most successfully repaired vars + AIG sizes. Order by
    // successful (non-cost-zero) repairs, ties broken by total attempts.
    auto n_succ_of = [&](uint32_t v) -> uint32_t {
        return (v < conflict_branch_repairs_per_var.size())
            ? conflict_branch_repairs_per_var[v] : 0;
    };
    vector<uint32_t> rep(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) rep[i] = i;
    sort(rep.begin(), rep.end(), [&] (const auto& a, const auto& b) {
        const uint32_t sa = n_succ_of(a), sb = n_succ_of(b);
        if (sa != sb) return sa > sb;
        return repaired_vars_count[a] > repaired_vars_count[b];
    });
    verb_print(1, COLCYN "[manthan-stats] === TOP SUCCESSFULLY REPAIRED VARS ===");
    for(size_t i = 0; i < min((size_t)20, (size_t)rep.size()); i++) {
        const auto& v = rep[i];
        if (n_succ_of(v) == 0) break;
        size_t aig_sz = 0;
        size_t aig_depth = 0;
        if (var_to_formula.count(v) && var_to_formula.at(v).aig) {
            aig_sz = AIG::count_aig_nodes_fast(var_to_formula.at(v).aig);
            std::function<size_t(const aig_lit&, std::map<aig_lit,size_t>&)> get_depth =
                [&](const aig_lit& a, std::map<aig_lit,size_t>& dc) -> size_t {
                    if (!a || a->type != AIGT::t_and) return 0;
                    auto it = dc.find(a);
                    if (it != dc.end()) return it->second;
                    size_t d = 1 + std::max(get_depth(a->l, dc), get_depth(a->r, dc));
                    dc[a] = d;
                    return d;
                };
            std::map<aig_lit,size_t> dc;
            aig_depth = get_depth(var_to_formula.at(v).aig, dc);
        }
        const uint32_t n_attempts = repaired_vars_count[v];
        const uint32_t n_succ = (v < conflict_branch_repairs_per_var.size())
            ? conflict_branch_repairs_per_var[v] : 0;
        const uint32_t n_cost_zero = (n_attempts >= n_succ) ? (n_attempts - n_succ) : 0;
        auto fmt_avg = [&](uint64_t sum, uint32_t cnt, int w) {
            std::ostringstream os;
            if (cnt == 0) os << setw(w) << "-";
            else os << setw(w) << fixed << setprecision(1) << ((double)sum / (double)cnt);
            return os.str();
        };
        verb_print(1, COLCYN "[m-stats] v" << setw(5) << v+1
            << " att:" << setw(5) << n_attempts
            << " c:" << setw(4) << n_succ
            << " z:" << setw(4) << n_cost_zero
            << " acl:" << fmt_avg(
                v < conflict_branch_lits_per_var.size() ? conflict_branch_lits_per_var[v] : 0,
                n_succ, 6)
            << " cl:" << setw(6) << (var_to_formula.count(v) ? var_to_formula.at(v).clauses.size() : 0)
            << " an:" << setw(6) << aig_sz
            << " ad:" << setw(3) << aig_depth
            << " cf:" << setw(5) << (v < var_conflict_freq.size() ? var_conflict_freq[v] : 0));
    }
    verb_print(1, COLCYN "[m-stats] --- legend ---");
    verb_print(1, COLCYN "[m-stats]   v   : var id (1-indexed)");
    verb_print(1, COLCYN "[m-stats]   att : total repair() calls for this var (successes + cost-zero failures); att = c + z");
    verb_print(1, COLCYN "[m-stats]   c   : # repairs that succeeded via the conflict-clause branch");
    verb_print(1, COLCYN "[m-stats]   z   : # cost-zero outcomes: solver found the bug is fixable by flipping later y-vars instead; y_rep needs no repair, so no repair is performed");
    verb_print(1, COLCYN "[m-stats]   acl : avg #literals in the conflict clause, over the 'c' successes only ('-' if c=0)");
    verb_print(1, COLCYN "[m-stats]   cl  : #clauses currently in this var's Manthan formula (var_to_formula[v].clauses)");
    verb_print(1, COLCYN "[m-stats]   an  : #AIG nodes in this var's current Manthan formula");
    verb_print(1, COLCYN "[m-stats]   ad  : longest AND-gate path from the formula's AIG root");
    verb_print(1, COLCYN "[m-stats]   cf  : total appearances of this var (any polarity) across all repair-conflict clauses ever seen (per literal, per clause)");

    // Aggregate AIG stats
    uint64_t total_aig_nodes = 0, total_clauses = 0, max_aig_nodes = 0;
    {
        const uint64_t epoch = AIG::next_visit_epoch();
        size_t union_count = 0;
        for (const auto& [v, form] : var_to_formula) {
            total_clauses += form.clauses.size();
            if (form.aig) {
                size_t sz = AIG::count_aig_nodes_fast(form.aig);
                AIG::count_aig_nodes_batch(form.aig.get(), epoch, union_count);
                max_aig_nodes = std::max(max_aig_nodes, (uint64_t)sz);
            }
        }
        total_aig_nodes = union_count;
    }
    verb_print(1, COLCYN "[manthan-stats] === AIG STATS ===");
    verb_print(1, COLCYN "[manthan-stats]   total unique AIG nodes: " << total_aig_nodes);
    verb_print(1, COLCYN "[manthan-stats]   max AIG nodes (single var): " << max_aig_nodes);
    verb_print(1, COLCYN "[manthan-stats]   total formula clauses: " << total_clauses
        << " (+ " << shared_helper_cls.size() << " shared helper cls)");
    verb_print(1, COLCYN "[manthan-stats]   cex_solver nVars: " << cex_solver.nVars());

    const double loop_t = cpuTime() - stats.repair_start_time;
    const double accounted = t_cex_solve + t_better_ctx + t_find_conflict
        + t_perform_repair + t_inject + recompute.t_total;
    verb_print(1, COLCYN "[manthan-stats] === TIME BREAKDOWN (cpu s) ===" << fixed << setprecision(2));
    verb_print(1, COLCYN "[manthan-stats]   cex_solver solve:     " << setw(8) << t_cex_solve
        << "  (" << setw(4) << setprecision(1) << safe_div(t_cex_solve*100.0, loop_t) << "%)" << setprecision(2));
    verb_print(1, COLCYN "[manthan-stats]   better_ctx:           " << setw(8) << t_better_ctx
        << "  (" << setw(4) << setprecision(1) << safe_div(t_better_ctx*100.0, loop_t) << "%)" << setprecision(2));
    verb_print(1, COLCYN "[manthan-stats]   find_conflict+minim:  " << setw(8) << t_find_conflict
        << "  (" << setw(4) << setprecision(1) << safe_div(t_find_conflict*100.0, loop_t) << "%)" << setprecision(2));
    verb_print(1, COLCYN "[manthan-stats]   perform_repair:       " << setw(8) << t_perform_repair
        << "  (" << setw(4) << setprecision(1) << safe_div(t_perform_repair*100.0, loop_t) << "%)" << setprecision(2));
    verb_print(1, COLCYN "[manthan-stats]   inject_formulas:      " << setw(8) << t_inject
        << "  (" << setw(4) << setprecision(1) << safe_div(t_inject*100.0, loop_t) << "%)" << setprecision(2));
    verb_print(1, COLCYN "[manthan-stats]   recompute_y_hat:      " << setw(8) << recompute.t_total
        << "  (" << setw(4) << setprecision(1) << safe_div(recompute.t_total*100.0, loop_t) << "%)" << setprecision(2));
    verb_print(1, COLCYN "[manthan-stats]   accounted/loop total: " << setw(8) << accounted
        << " / " << loop_t);
}

void Manthan::const_functions() {
    // Majority-vote the constant over several samples: a single sample can be
    // atypical, so voting cuts the counterexamples needed to converge.
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

void Manthan::print_cache_hit_rate() const {
    verb_print(1, "repair solver cache hit: " << setw(3) << fixed << setprecision(0) << repair_solver.get_cache_hit_rate()*100.0 << "%");
}

SimplifiedCNF Manthan::do_manthan() {
    SLOW_DEBUG_DO(assert(cnf.get_need_aig() && cnf.defs_invariant()));
    const double my_time = cpuTime();
    const auto ret = cnf.find_disconnected();
    verb_print(1, "[manthan] Found " << ret.size() << " components");
    repaired_vars_count.resize(cnf.nVars(), 0);
    var_conflict_freq.resize(cnf.nVars(), 0);
    needs_repair_window.assign(cnf.nVars(), 0);
    cz_window.assign(cnf.nVars(), 0);
    conflict_branch_lits_per_var.assign(cnf.nVars(), 0);
    conflict_branch_repairs_per_var.assign(cnf.nVars(), 0);

    if (!mconf.write_manthan_cnf.empty()) cnf.write_simpcnf(mconf.write_manthan_cnf);

    // CNF is divided into:
    // input vars -- original sampling vars
    // defined non-input vars -- vars defined via backward_round_synth
    // to_define vars -- vars that are not defined yet, and not input
    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_manthan").unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[manthan] No variables to-define, returning original CNF");
        return cnf;
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
        for(const auto& c: cnf.get_clauses()) cex_solver.add_clause(c);
        for(const auto& c: cnf.get_red_clauses()) cex_solver.add_red_clause(c);
    }
    fh = std::make_unique<FHolder<MetaSolver>>(&cex_solver);
    create_vars_for_y_hats();
    // Manthan only ever reads cex models up to the y_hats (created just
    // above); skip materializing the tens of thousands of helper vars.
    cex_solver.set_model_prefix(cex_solver.nVars());
    add_not_f_x_yhat();
    verb_print(2, "True lit in solver_train: " << fh->get_true_lit());
    verb_print(2, "[manthan] After fh creation: solver_train.nVars() = " << cex_solver.nVars() << " cnf.nVars() = " << cnf.nVars());

    // Order & train
    pre_order_vars();
    fill_var_to_formula_with(backward_defined);

    if (!guess.empty()) {
        // Restart round: seed from the previous round's AIGs.
        init_from_guess();
    } else if (mconf.manthan_base == 0) {
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

    // Counterexample-guided repair
    stats.repair_start_time = cpuTime();
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
        if (mconf.stats_every > 0 && stats.num_loops_repair % mconf.stats_every == mconf.stats_every - 1) {
            if (conf.verb >= 1) stats.print_stats();
        }
        if (mconf.detailed_stats_every > 0 && stats.num_loops_repair % mconf.detailed_stats_every == mconf.detailed_stats_every - 1) {
            print_detailed_stats(stats);
        }
        assert(at_least_one_repaired);
        at_least_one_repaired = false;
        stats.num_loops_repair++;

        maybe_reorder_vars();
        inject_formulas_into_solver();

        sample ctx;
        const double t_cex0 = cpuTime();
        const bool finished = get_counterexample(ctx);
        t_cex_solve += cpuTime() - t_cex0;
        stats.cex_solver_calls++;
        if (finished) {
            // cex_solver claims no CEX. Triangulate with three SLOW_DEBUG
            // miters: via_clauses, via_aig, and the per-formula pairwise check.
            SLOW_DEBUG_DO({
                const std::string where = "finished-loop-exit iter=" + std::to_string(stats.num_loops_repair);
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
        if (stats.tot_repaired >= mconf.max_repairs) {
            if (conf.verb >= 1) {
                stats.print_stats("", COLRED, " Reached max repairs: " + std::to_string(mconf.max_repairs));
                print_cache_hit_rate();
            }
            return cnf;
        }
        if (mconf.restart != 0 && stats.tot_repaired >= mconf.restart) {
            restart_needed = true;
            if (conf.verb >= 1) {
                stats.print_stats("", COLYEL, " Hit restart limit, exiting to compact AIGs + re-enter");
                print_cache_hit_rate();
            }
            return std::move(cnf);
        }
        print_cnf_debug_info(ctx);
        print_needs_repair_vars();
        SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
        SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));

        { // Find a better ctx if possible
            compute_needs_repair(ctx);
            const uint32_t old_needs_repair_size = needs_repair.size();
            const double t_bctx0 = cpuTime();
            if (mconf.maxsat_better_ctx == 1) find_better_ctx_maxsat(ctx);
            else find_better_ctx_normal(ctx);
            t_better_ctx += cpuTime() - t_bctx0;
            SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
            SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));
            compute_needs_repair(ctx);
            verb_print(2, "[manthan] finding better ctx done, needs_repair size before vs now: "
                  << setw(3) << old_needs_repair_size << " -- " << setw(4) << needs_repair.size());
            print_needs_repair_vars();
        }
        stats.needs_repair_sum += needs_repair.size();

        loops_since_reorder++;
        for(const auto& y: needs_repair) needs_repair_window[y]++;

        assert(!needs_repair.empty());
        uint32_t num_repaired = 0;
        uint32_t consecutive_cost_zero = 0;
        while(!needs_repair.empty()) {
            auto y_rep = find_next_repair_var(ctx);
            bool done = repair(y_rep, ctx); // this updates ctx
            if (done) {
                at_least_one_repaired = true;
                num_repaired++;
                stats.tot_repaired++;
                consecutive_cost_zero = 0;
                if (mconf.one_repair_per_loop) break;
            } else {
                stats.repair_failed++;
                consecutive_cost_zero++;
                // Break for a fresh counterexample after enough consecutive
                // cost-zero repairs; threshold drops as the cost-zero rate rises.
                const uint32_t cz_threshold = (stats.cost_zero_repairs > stats.tot_repaired * mconf.cz_high_ratio) ? mconf.cz_threshold_high :
                    (stats.cost_zero_repairs > stats.tot_repaired * mconf.cz_low_ratio) ? mconf.cz_threshold_mid : mconf.cz_threshold_low;
                if (consecutive_cost_zero >= cz_threshold && num_repaired > 0) {
                    verb_print(2, "[manthan] Breaking repair loop after " << consecutive_cost_zero
                        << " consecutive cost-zero repairs (threshold " << cz_threshold
                        << ", cost-zero repairs " << stats.cost_zero_repairs
                        << ", tot repaired " << stats.tot_repaired << ")");
                    break;
                }
            }
            SLOW_DEBUG_DO(assert(ctx_is_sat(ctx)));
            SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)));
            SLOW_DEBUG_DO({
                if (!check_aig_matches_clauses_per_formula(
                        "post-repair y=" + std::to_string(y_rep+1) +
                        " iter=" + std::to_string(stats.num_loops_repair))) {
                    assert(false && "perform_repair introduced a diverging aig/clauses");
                }
            });
            verb_print(3, "[manthan] finished repairing " << y_rep+1 << " : " << std::boolalpha << done);
        }
        verb_print(2, "[manthan] Num repaired: " << num_repaired << " tot repaired: " << stats.tot_repaired << " num_loops_repair: " << stats.num_loops_repair);

        if (mconf.check_repair) check_repair_monotonic();
    }
    const double repair_time = cpuTime() - stats.repair_start_time;
    assert(check_map_dependency_cycles());
    print_detailed_stats(stats);

    // Build final CNF
    vector<aig_lit> aigs(cnf.nVars(), nullptr);
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
    stats.print_stats("", COLYEL, " Round done");
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

// (l1 ∨..∨ ln ∨ to_repair) is valid under the CNF; add as redundant to speed
// up the repair solver.
void Manthan::add_repair_conflict_clause(const uint32_t y_rep, const sample& ctx,
        const vector<Lit>& conflict) {
    if (conflict.empty()) return;
    const Lit to_repair = Lit(y_rep, ctx[y_to_y_hat[y_rep]] == l_True);
    vector<Lit> learned_cl;
    learned_cl.reserve(conflict.size() + 1);
    for (const auto& l : conflict) learned_cl.push_back(l);
    learned_cl.push_back(to_repair);
    repair_solver.add_red_clause(learned_cl);
}

bool Manthan::is_unsat(const vector<Lit>& conflict, uint32_t y_rep, const sample& ctx) const {
    SATSolver s;
    s.new_vars(cnf.nVars());
    for(const auto& c: cnf.get_clauses()) s.add_clause(c);
    for(const auto& l: conflict) s.add_clause({~l});
    const Lit to_repair = Lit(y_rep, ctx[y_to_y_hat.at(y_rep)] == l_True);
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

    vector<Lit> conflict;
    repaired_vars_count[y_rep]++;

    const double t_fc0 = cpuTime();
    bool ret = find_conflict(y_rep, ctx, conflict);
    t_find_conflict += cpuTime() - t_fc0;
    stats.repair_solver_calls++;

    if (ret) {
        SLOW_DEBUG_DO(assert(is_unsat(conflict, y_rep, ctx)));

        add_repair_conflict_clause(y_rep, ctx, conflict);

        if (y_rep < conflict_branch_lits_per_var.size()) {
            conflict_branch_lits_per_var[y_rep] += conflict.size();
            conflict_branch_repairs_per_var[y_rep]++;
        }
        const double t_pr0 = cpuTime();
        perform_repair(y_rep, ctx, conflict);
        t_perform_repair += cpuTime() - t_pr0;

        if (!mconf.one_repair_per_loop) {
            ctx[y_to_y_hat[y_rep]] = ctx[y_rep];
            inject_formulas_into_solver();
            recompute.run(*this, ctx, y_rep);
        }

        // Track conflict type
        bool is_input_only = true;
        for (const auto& l : conflict) {
            if (!is_input[l.var()]) { is_input_only = false; break; }
        }
        if (is_input_only) {
            stats.input_only_conflict_count++;
            stats.input_only_conflict_sizes_sum += conflict.size();
        } else {
            stats.full_conflict_count++;
            stats.full_conflict_sizes_sum += conflict.size();
        }

    } else {
        stats.cost_zero_repairs++;
        cz_window[y_rep]++;
    }
    compute_needs_repair(ctx);
    print_needs_repair_vars();
    return ret;
}

// Memoized list of y's formula-AIG leaf vars (mixed orig/y_hat space), keyed
// by the AIG's raw pointer; a mismatch (formula rewritten) triggers recompute.
// Uses the aig_dep_* scratch internally — callers needing the scratch bitmap
// must repopulate it from the returned list afterwards.
const std::vector<uint32_t>& Manthan::formula_dep_list(const uint32_t y) {
    const auto& aig = var_to_formula.at(y).aig;
    assert(aig != nullptr);
    const ArjunNS::AIG* aig_raw = aig.get();
    auto it = dep_cache.find(y);
    if (it != dep_cache.end() && it->second.aig_lit == aig_raw)
        return it->second.dep_list;

    for (const uint32_t prev_v : aig_dep_list) is_aig_dep[prev_v] = 0;
    aig_dep_list.clear();
    aig_dep_stack.clear();
    AIG::get_dependent_vars(aig, is_aig_dep, aig_dep_list, aig_dep_stack, y);
    if (it != dep_cache.end()) {
        it->second.aig_lit = aig_raw;
        it->second.dep_list = aig_dep_list;
        return it->second.dep_list;
    }
    return dep_cache.emplace(y, DepCacheEntry{aig_raw, aig_dep_list}).first->second.dep_list;
}

bool Manthan::compute_aig_dep_set(const uint32_t y_rep) {
    if (!mconf.minimize_conflict) {
        // Reset marks left by the previous call before reusing the scratch.
        for (const uint32_t prev_v : aig_dep_list) is_aig_dep[prev_v] = 0;
        aig_dep_list.clear();
        return false;
    }
    const auto& deps = formula_dep_list(y_rep);
    for (const uint32_t prev_v : aig_dep_list) is_aig_dep[prev_v] = 0;
    aig_dep_list.clear();
    for (const uint32_t dv : deps) {
        if (dv >= is_aig_dep.size()) is_aig_dep.resize(dv + 1, 0);
        is_aig_dep[dv] = 1;
        aig_dep_list.push_back(dv);
    }
    return !aig_dep_list.empty();
}

bool Manthan::try_input_only_conflict(const uint32_t y_rep, const sample& ctx,
        const Lit to_repair, const bool have_aig_deps,
        vector<Lit>& conflict, vector<Lit>& assumps) {
    vector<Lit> input_assumps;
    input_assumps.reserve(input.size() + 1);
    for (const auto& x : input) {
        if (have_aig_deps && (x >= is_aig_dep.size() || !is_aig_dep[x])) continue;
        input_assumps.emplace_back(x, ctx[x] == l_False);
    }
    input_assumps.push_back({~to_repair});
    auto input_ret = repair_solver.solve(&input_assumps);
    if (input_ret == l_False) {
        conflict = repair_solver.get_conflict();
        if (std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end()) {
            verb_print(2, "[manthan] Found INPUT-ONLY conflict sz " << conflict.size()
                << " for y_rep=" << y_rep+1);
            stats.input_only_rep++;
            assumps = std::move(input_assumps);
            return true;
        }
    }
    return false;
}

// Cost-zero repair: y_rep is satisfiable without a formula change, so copy the
// repair_solver model into ctx for y_rep and all later y-vars.
void Manthan::apply_cost_zero_model(const uint32_t y_rep, sample& ctx) {
    bool found_yrep = false;
    const auto& model = repair_solver.get_model();
    for(const auto& y: y_order) {
        if (y == y_rep) found_yrep = true;
        if (found_yrep) ctx[y] = model[y];
    }
    assert(ctx[y_rep] == ctx[y_to_y_hat[y_rep]]);
}

// Solve over (dependent inputs + earlier y-vars + ~to_repair). Returns true
// with `conflict` on UNSAT; false on a cost-zero repair (SAT, ctx updated). If
// don't-care inputs were skipped and the reduced solve is SAT, retries with all.
bool Manthan::solve_full_assumption_conflict(const uint32_t y_rep, sample& ctx,
        const Lit to_repair, const bool have_aig_deps,
        vector<Lit>& conflict, vector<Lit>& assumps,
        const double repair_solver_start_time) {
    uint32_t skipped_inputs = 0;
    assumps.clear();
    assumps.reserve(input.size() + y_order.size() + 1);
    for(const auto& x: input) {
        // Skip inputs that the AIG for y_rep doesn't depend on
        if (have_aig_deps && (x >= is_aig_dep.size() || !is_aig_dep[x])) {
            skipped_inputs++;
            continue;
        }
        assumps.push_back(Lit(x, ctx[x] == l_False));
    }
    verb_print(2, "[manthan] skipped " << skipped_inputs << " / " << input.size()
            << " inputs for y_rep=" << y_rep+1);

    // Assume earlier (already-correct) y-variables; y_rep does not depend on them.
    for(const auto& y: y_order) {
        if (y == y_rep) break; // beyond this point we don't care
        assert(dependency_mat[y][y_rep] != 1 && "due to ordering, this should not happen. Otherwise y depends on y_rep, but we will repair y_rep potentially with y_rep");
        assert(ctx[y] == ctx[y_to_y_hat[y]]); // they are correct
        verb_print(3, "assuming " << y+1 << " is " << ctx[y]);
        assumps.push_back(Lit(y, ctx[y] == l_False));
    }
    assumps.push_back({~to_repair});

    verb_print(2, "assuming reverse for y_rep: " << ~to_repair);
    auto ret = repair_solver.solve(&assumps);
    verb_print(2, "repair_solver finished "
            << " with result: " << (ret == l_True ? "SAT" : (ret == l_False ? "UNSAT" : "UNKNOWN"))
            << " in T: " << cpuTime()-repair_solver_start_time);
    assert(ret != l_Undef);

    if (ret == l_False) {
        conflict = repair_solver.get_conflict();
        return true;
    }

    // SAT. With no skipped inputs this is directly a cost-zero repair.
    if (skipped_inputs == 0) {
        verb_print(2, "Repair cost is 0 for y: " << y_rep+1);
        apply_cost_zero_model(y_rep, ctx);
        return false;
    }

    // SAT with reduced inputs - retry with all inputs to get a proper conflict /
    // cost-zero repair.
    assumps.clear();
    for(const auto& x: input) assumps.push_back(Lit(x, ctx[x] == l_False));
    for(const auto& y: y_order) {
        if (y == y_rep) break;
        assumps.push_back(Lit(y, ctx[y] == l_False));
    }
    assumps.push_back({~to_repair});
    ret = repair_solver.solve(&assumps);
    assert(ret != l_Undef);
    if (ret == l_True) {
        verb_print(2, "Repair cost is 0 for y: " << y_rep+1);
        apply_cost_zero_model(y_rep, ctx);
        return false;
    }
    // UNSAT with all inputs - extract conflict normally
    conflict = repair_solver.get_conflict();
    return true;
}

// Drop ALL y-vars from the conflict; if the input-only remainder is still
// UNSAT the repair generalises (independent of intermediate values).
void Manthan::try_drop_y_vars(vector<Lit>& conflict, vector<Lit>& assumps,
        const Lit to_repair) {
    bool has_y_vars = false;
    for (const auto& l : conflict) {
        if (l != to_repair && !is_input[l.var()]) { has_y_vars = true; break; }
    }
    if (!has_y_vars) return;

    assumps.clear();
    for (const auto& l : conflict) {
        if (l == to_repair || is_input[l.var()]) assumps.push_back(~l);
    }
    if (assumps.empty()) return;

    auto ret3 = repair_solver.solve(&assumps);
    if (ret3 != l_False) return;
    auto conflict3 = repair_solver.get_conflict();
    if (std::find(conflict3.begin(), conflict3.end(), to_repair) == conflict3.end()) return;
    verb_print(2, "[manthan] Dropped y-vars from conflict: "
        << conflict.size() << " -> " << conflict3.size());
    conflict = conflict3;
    stats.input_only_rep++;
}

// Minimize the conflict, then generalise it (drop y-vars) and strip the
// to_repair literal so only the must-flip region's input/y literals remain.
void Manthan::minimize_and_generalize_conflict(vector<Lit>& conflict,
        vector<Lit>& assumps, const Lit to_repair) {
    verb_print(2, "find_conflict sz: " << setw(5) << conflict.size() << " conflict: " << conflict);
    const uint32_t orig_size = conflict.size();
    const double minimize_start_time = cpuTime();
    if (conflict.size() > 1 && mconf.minimize_conflict) {
        minimize_conflict(conflict, assumps, to_repair);
        assert(std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end() &&
            "to_repair literal must be in conflict");
        // Skip the y-drop for very large conflicts (unlikely to succeed, expensive).
        if (conflict.size() <= mconf.conflict_drop_y_max)
            try_drop_y_vars(conflict, assumps, to_repair);
    }

    auto now_end = std::remove_if(conflict.begin(), conflict.end(),
                [&](const Lit l){ return l == to_repair; });
    conflict.erase(now_end, conflict.end());
    verb_print(2, "[manthan] minim. Removed: " << setw(3) << (orig_size - conflict.size())
            << " from conflict, now size: " << setw(3) << conflict.size()
            << " repair cache size: " << setw(8) << repair_solver.cache_size()/1000 << "K"
            << " repair cache hit rate: " << setw(5) << fixed << setprecision(0) << repair_solver.get_cache_hit_rate()*100.0 << "%"
            << " T: " << setw(5) << setprecision(2) << cpuTime()-minimize_start_time);
}

bool Manthan::find_conflict(const uint32_t y_rep, sample& ctx,
        vector<Lit>& conflict) {
    const double repair_solver_start_time = cpuTime();
    const bool have_aig_deps = compute_aig_dep_set(y_rep);
    assert(ctx[y_rep] != ctx[y_to_y_hat[y_rep]] && "before repair, y and y_hat must be different");
    const Lit to_repair = Lit(y_rep, ctx[y_to_y_hat[y_rep]] == l_True);

    vector<Lit> assumps;
    const bool found_input_only = try_input_only_conflict(
            y_rep, ctx, to_repair, have_aig_deps, conflict, assumps);

    if (!found_input_only) {
        // Returns false on a cost-zero repair (ctx already updated); otherwise
        // `conflict` is the UNSAT core to minimise below.
        if (!solve_full_assumption_conflict(y_rep, ctx, to_repair, have_aig_deps,
                    conflict, assumps, repair_solver_start_time))
            return false;
    }
    assert(std::find(conflict.begin(), conflict.end(), to_repair) != conflict.end() &&
        "to_repair literal must be in conflict");

    minimize_and_generalize_conflict(conflict, assumps, to_repair);
    return true;
}

void Manthan::minimize_conflict(vector<Lit>& conflict, vector<Lit>& assumps, const Lit to_repair) {
    // Quick batch removal: keep to_repair + a shrinking prefix; if UNSAT we cut
    // the conflict in one SAT call instead of O(n) individual ones.
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
    // Cap solver calls during greedy minimization (uncapped it's O(n^2));
    // small conflicts below the threshold are minimized without limit.
    const uint32_t minim_budget = (conflict.size() > mconf.minim_budget_threshold) ?
        min((uint32_t)(conflict.size() * mconf.minim_budget_mult), mconf.minim_budget_max) :
        std::numeric_limits<uint32_t>::max();
    uint32_t minim_calls = 0;
    while(removed_any) {
        // Remove most-beneficial literals first: y-vars before inputs (fewer
        // deps), then least-frequent first (more likely removable).
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
    if (is_input[var]) return l;
    assert(to_define_full.count(var));
    return Lit(y_to_yhat_flat[var], l.sign());
}

// Update dependency matrix to say that a depends on b
void Manthan::set_depends_on(const uint32_t a, const uint32_t b) {
    assert(!input.count(a) && "we are not interested in what input vars depend on");
    if (input.count(b)) {
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

// A repair wraps the old formula: new = OR(guard, old) / AND(~guard, old)
// with the guard's leaves exactly the conflict vars, so the new dep set is
// old ∪ conflict — extend the cached list instead of invalidating it (which
// would force a full O(AIG-nodes) walk on the next formula_dep_list call).
// Any structurally different result (constant folds) falls back to erase.
void Manthan::update_dep_cache_after_repair(const uint32_t y_rep,
        const ArjunNS::AIG* old_root, const vector<Lit>& conflict) {
    const auto& new_aig = var_to_formula[y_rep].aig;
    if (new_aig.get() == old_root) return; // constant-folded to the old formula
    auto it = dep_cache.find(y_rep);
    if (it == dep_cache.end()) return; // no cached list to extend
    if (it->second.aig_lit != old_root
            || new_aig->type != AIGT::t_and
            || (new_aig->l.get() != old_root && new_aig->r.get() != old_root)) {
        dep_cache.erase(it);
        return;
    }
    auto& dep_list = it->second.dep_list;
    for (const auto& l : conflict) {
        const uint32_t v = l.var();
        if (std::find(dep_list.begin(), dep_list.end(), v) == dep_list.end())
            dep_list.push_back(v);
    }
    it->second.aig_lit = new_aig.get();
    SLOW_DEBUG_DO({
        // The incremental list must match a fresh full walk (as sets).
        std::set<uint32_t> full;
        AIG::get_dependent_vars(new_aig, full, y_rep);
        std::set<uint32_t> inc(dep_list.begin(), dep_list.end());
        assert(inc == full && "incremental dep list diverged from full walk");
    });
}

void Manthan::perform_repair(const uint32_t y_rep, const sample& ctx,
        const vector<Lit>& conflict) {
    for(const auto& l: conflict) assert(l.var() < cnf.nVars());

    // Track conflict variable frequency for smarter minimization ordering
    for (const auto& l : conflict) {
        if (l.var() < var_conflict_freq.size()) var_conflict_freq[l.var()]++;
    }

    if (conflict.empty()) {
        verb_print(2, "[manthan] conflict empty for " << setw(5) << y_rep+1 << ", unconditionally fixing it to " << ctx[y_rep]);
        var_to_formula[y_rep] = fh->constant_formula(ctx[y_rep] == l_True);
        dep_cache.erase(y_rep);
        updated_y_funcs.push_back(y_rep);
        return;
    }

    verb_print(2, "[manthan] Performing repair on " << setw(5) << y_rep+1
            << " with conflict size " << setw(3) << conflict.size());
    assert(backward_defined.count(y_rep) == 0 && "Backward defined should need NO repair, ever");
    stats.conflict_sizes_sum += conflict.size();

    // not (conflict) -> v = ctx(v)
    FHolder<MetaSolver>::Formula f;
    {
        vector<Lit> cl;
        cex_solver.new_var();
        auto fresh_l = Lit(cex_solver.nVars()-1, false);
        helpers.insert(fresh_l.var());
        cl.push_back(fresh_l);
        for(const auto& l: conflict) {
            cl.push_back(map_y_to_y_hat(l));
            set_depends_on(y_rep, l);
        }
        f.clauses.emplace_back(cl);

        for(const auto& l: conflict) {
            cl.clear();
            cl.push_back(~fresh_l);
            cl.push_back(~map_y_to_y_hat(l));
            f.clauses.emplace_back(cl);
        }
        f.out = fresh_l;

        // AIG part: the guard, TRUE exactly on the conflict cube.
        aig_lit guard = AIG::new_lit(~conflict[0]);
        for(size_t i = 1; i < conflict.size(); i++) {
            guard = AIG::new_and(guard, AIG::new_lit(~conflict[i]));
        }
        f.aig = guard;
    }

    // when fresh_l is true, confl is satisfied → guard is active → use constant
    verb_print(4, "Original formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    verb_print(4, "Branch formula. When this is true, H is wrong:" << endl << f);

    // ITE(guard,TRUE,old)=OR(guard,old); ITE(guard,FALSE,old)=AND(!guard,old)
    // — flatter AIGs than a generic ITE. std::move reuses the clause vector
    // (rvalue overload), keeping per-repair cost O(|f|) instead of O(N²).
    const AIG* old_root = var_to_formula[y_rep].aig.get();
    if (ctx[y_rep] == l_True) {
        var_to_formula[y_rep] = fh->compose_or(f, std::move(var_to_formula[y_rep]), helpers);
    } else {
        var_to_formula[y_rep] = fh->compose_and(fh->neg(f), std::move(var_to_formula[y_rep]), helpers);
    }
    update_dep_cache_after_repair(y_rep, old_root, conflict);
    updated_y_funcs.push_back(y_rep);

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

// Will order 1st the variables that NOTHING depends on
// Will order LAST the variables that depends on EVERYTHING
void Manthan::pre_order_vars() {
    assert(order_val.empty());
    assert(y_order.empty());
    const double my_time = cpuTime();
    verb_print(2, "[manthan] Fixing order " << (mconf.manthan_base == 0 ? "[LEARN]" : (mconf.manthan_base == 1 ? "[CONST]" : "[BVE]")) << "...");

    if (!order_hint.empty()) {
        // Mandatory: guess AIG deps only point earlier under the prev order.
        release_assert(order_hint.size() == to_define_full.size());
        SLOW_DEBUG_DO(for (const auto& y : order_hint) assert(to_define_full.count(y)));
        y_order = std::move(order_hint);
        order_hint.clear();
        verb_print(1, "[manthan] Inherited y_order from previous round");
    } else switch(mconf.manthan_order) {
        case 0: learn_order(); break;
        case 2: bve_order(); break;
        default: release_assert(false && "Invalid manthan_order");
    }

    rebuild_order_index();

    verb_print(1, "[manthan] Fixed order. T: " << setprecision(2) << fixed << (cpuTime() - my_time)
            << " Final order size: " << y_order.size());
    print_y_order_occur();
}

void Manthan::rebuild_order_index() {
    order_val.assign(cnf.nVars(), -2);
    for(const auto& x: input) order_val[x] = -1;
    for(uint32_t i = 0; i < y_order.size(); i++) order_val[y_order[i]] = i;
    for(const auto& v: order_val) assert(v != -2);

    // Per-y better-ctx weight: later in order = higher weight.
    y_order_weight.assign(cnf.nVars(), 0);
    for(size_t i = 0; i < y_order.size(); i++) {
        y_order_weight[y_order[i]] = i+1;
    }
}

// Ordering CEGAR: a var chronically in needs_repair (or chronically
// cost-zero) sits too early in y_order; demote it.
void Manthan::maybe_reorder_vars() {
    if (mconf.reorder_every == 0) return;
    if (loops_since_reorder < mconf.reorder_every) return;
    const uint32_t cutoff = (uint32_t)(mconf.reorder_hot_ratio * (double)loops_since_reorder);
    const uint32_t cz_cutoff = (uint32_t)(mconf.reorder_cz_ratio * (double)loops_since_reorder);
    vector<uint8_t> is_hot(cnf.nVars(), 0);
    uint32_t num_hot = 0;
    for (const auto& y : to_define) {
        const bool nr_hot = needs_repair_window[y] > cutoff;
        const bool cz_hot = mconf.reorder_cz_ratio > 0 && cz_window[y] > cz_cutoff;
        if (nr_hot || cz_hot) {
            is_hot[y] = 1;
            num_hot++;
            verb_print(2, "[manthan-reorder] hot var " << y+1
                << " needs_repair in " << needs_repair_window[y]
                << ", cost-zero in " << cz_window[y]
                << " of " << loops_since_reorder << " loops");
        }
    }
    loops_since_reorder = 0;
    std::fill(needs_repair_window.begin(), needs_repair_window.end(), 0);
    std::fill(cz_window.begin(), cz_window.end(), 0);
    if (num_hot == 0 || num_hot == to_define.size()) return;
    reorder_vars(is_hot);
}

// Kahn topo re-sort of y_order over dependency_mat. Hot vars are placed only
// when no cold var is placeable (maximal demotion); cold keep relative order.
void Manthan::reorder_vars(const vector<uint8_t>& is_hot) {
    const double my_time = cpuTime();
    const uint32_t n = y_order.size();

    // rem_deps[a] = # unplaced direct deps of a; dependents[b] = direct a's.
    std::vector<uint32_t> rem_deps(cnf.nVars(), 0);
    std::vector<std::vector<uint32_t>> dependents(cnf.nVars());
    for (const auto& a : y_order) {
        for (const auto& b : y_order) {
            if (dependency_mat[a][b]) {
                rem_deps[a]++;
                dependents[b].push_back(a);
            }
        }
    }

    // Ready sets hold current order positions -> deterministic picks.
    std::set<uint32_t> ready_cold, ready_hot;
    auto push_ready = [&](const uint32_t v) {
        (is_hot[v] ? ready_hot : ready_cold).insert((uint32_t)order_val[v]);
    };
    for (const auto& v : y_order) if (rem_deps[v] == 0) push_ready(v);

    vector<uint32_t> new_order;
    new_order.reserve(n);
    while (new_order.size() < n) {
        auto& ready = ready_cold.empty() ? ready_hot : ready_cold;
        assert(!ready.empty() && "dependency_mat must stay acyclic");
        const uint32_t v = y_order[*ready.begin()];
        ready.erase(ready.begin());
        new_order.push_back(v);
        for (const auto& a : dependents[v]) {
            assert(rem_deps[a] > 0);
            if (--rem_deps[a] == 0) push_ready(a);
        }
    }
    assert(new_order.size() == n);

    uint32_t num_moved = 0;
    for (uint32_t i = 0; i < n; i++) if (new_order[i] != y_order[i]) num_moved++;
    uint32_t num_hot = 0;
    for (const auto& v : y_order) if (is_hot[v]) num_hot++;
    y_order = std::move(new_order);
    rebuild_order_index();
    num_reorders++;
    verb_print((num_moved == 0 ? 2 : 1), COLYEL "[manthan-reorder] #" << num_reorders
        << " demoted " << num_hot << " hot vars, " << num_moved << " of " << n
        << " vars changed position. T: " << setprecision(2) << fixed << (cpuTime() - my_time));
    SLOW_DEBUG_DO({
        // Every direct dependency must still point at an earlier var.
        for (const auto& a : y_order)
            for (const auto& b : y_order)
                if (dependency_mat[a][b]) assert(later_in_order(a, b));
    });
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

void Manthan::find_better_ctx_maxsat(sample& ctx) {
#ifndef EXTRA_SYNTH
    cout << "ERROR: maxsat_better_ctx is set to 1 but we are not in EXTRA_SYNTH mode!" << endl;
    exit(EXIT_FAILURE);
#else
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

    // Fix to_define variables that are incorrect via assumptions
    for(const auto& y: y_order) {
        const auto y_hat = y_to_y_hat[y];
        if (ctx[y] == ctx[y_hat]) continue;
        const auto l = Lit(y, ctx[y_hat] == l_False);
        verb_print(3, "[find-better-ctx] put into assumps y= " << l);
        int w = y_order_weight[y];
        s_ctx.addClause(lits_to_ints({l}), w); // want to flip valuation to ctx[y_hat]
    }

    auto ret = s_ctx.solve();
    assert(ret && "must be satisfiable");
    assert(s_ctx.getCost() > 0);
    for(const auto& v: to_define_full) ctx[v] = s_ctx.getValue(v+1) ? l_True : l_False;
#endif
}

// Fills needs_repair with vars from y (i.e. output) using normal SAT solver with assumptions
void Manthan::find_better_ctx_normal(sample& ctx) {
    if (!better_ctx_solver) {
        // Persistent solver: the CNF never changes, so inject it once and fix
        // per-call values via assumptions
        better_ctx_solver = std::make_unique<SATSolver>();
        inject_cnf(*better_ctx_solver);
    }
    SATSolver& s = *better_ctx_solver;
    verb_print(2, "Finding better ctx via normal SAT solver.");

    // Fixed assumptions: input values + already-correct y values.
    vector<Lit> fixed;
    fixed.reserve(input.size() + to_define_full.size());
    for(const auto& x: input) {
        assert(ctx[x] != l_Undef && "Input variable must be defined in counterexample");
        fixed.emplace_back(x, ctx[x] == l_False);
    }

    // For to_define variables, separate into correct and incorrect
    vector<std::pair<Lit, uint32_t>> incorrect_lits; // pair of literal and weight
    for(const auto& y: to_define_full) {
        const auto y_hat = y_to_y_hat[y];
        const Lit l = Lit(y, ctx[y_hat] == l_False); // literal that makes y match y_hat

        if (ctx[y] == ctx[y_hat]) {
            // Already correct, keep it fixed
            verb_print(3, "[find-better-ctx-normal] CTX is CORRECT on y=" << y+1 << " y_hat=" << y_hat+1
                 << " -- ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat]));
            fixed.push_back(l);
        } else {
            // Incorrect, we want to try to fix this
            uint32_t weight = y_order_weight[y];
            incorrect_lits.emplace_back(l, weight);
            verb_print(3, "[find-better-ctx-normal] CTX is INCORRECT on y=" << y+1
                 << " ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat])
                 << " weight=" << weight);
        }
    }
    assert(incorrect_lits.size() == needs_repair.size());

    // Sort incorrect lits by weight (higher = fix first), boosting vars already
    // repaired this session since they matter for correctness.
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
        assumps = fixed;
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

        // Find the first soft assumption in the conflict and remove it. The
        // core must contain one: the fixed assumptions alone are satisfied
        // by ctx itself.
        set<Lit> conflict_set(conflict.begin(), conflict.end());
        bool found_soft = false;
        for(const auto& [lit, weight]: incorrect_lits) {
            if (conflict_set.count(~lit) && !cannot_fix.count(lit.var())) {
                verb_print(3, "[find-better-ctx-normal] Giving up on fixing var " << lit.var()+1);
                cannot_fix.insert(lit.var());
                found_soft = true;
                break;
            }
        }
        release_assert(found_soft && "UNSAT core must contain a soft assumption");
    }
}

void Manthan::create_vars_for_y_hats() {
    constexpr uint32_t none = std::numeric_limits<uint32_t>::max();
    y_to_yhat_flat.assign(cnf.nVars(), none);
    for(const auto& y: to_define_full) {
        cex_solver.new_var();
        const uint32_t y_hat = cex_solver.nVars()-1;
        y_to_y_hat[y] = y_hat;
        y_hat_to_y[y_hat] = Lit(y, false);
        y_hats.insert(y_hat);
        y_to_yhat_flat[y] = y_hat;
        if (y_hat >= yhat_to_y_flat.size()) yhat_to_y_flat.resize(y_hat + 1, none);
        yhat_to_y_flat[y_hat] = y;
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
            if (to_define_full.count(l.var())) cl.emplace_back(y_to_y_hat.at(l.var()), l.sign());
            else cl.push_back(l);
        }

        cex_solver.new_var();
        uint32_t cl_ind_v = cex_solver.nVars()-1;
        Lit cl_ind(cl_ind_v, false);
        tmp.clear();
        tmp.push_back(~cl_ind);
        for(const auto&l : cl) tmp.push_back(l);
        cex_solver.add_clause(tmp);

        for(const auto&l : cl) {
            tmp.clear();
            tmp.push_back(cl_ind);
            tmp.push_back(~l);
            cex_solver.add_clause(tmp);
        }
        cl_indics.push_back(cl_ind);
    }
    tmp.clear();
    for(const auto& l: cl_indics) tmp.push_back(~l); // at least one is unsatisfied
    cex_solver.add_clause(tmp);
}

void Manthan::inject_formulas_into_solver() {
    const double t_inj0 = cpuTime();
    SLOW_DEBUG_DO(assert(check_functions_for_y_vars()));

    // Replace y with y_hat. uninserted_start skips the already-inserted prefix;
    // cl.inserted stays the source of truth on degenerate paths.
    vector<Lit> cl2;
    for(auto& k: updated_y_funcs) {
        auto& form = var_to_formula.at(k);
        for (size_t i = form.uninserted_start; i < form.clauses.size(); i++) {
            auto& cl = form.clauses[i];
            if (cl.inserted) continue;
            cl2.clear();
            for(const auto& l: cl.lits) {
                const auto v = l.var();
                // Every non-input orig-CNF var is in to_define_full.
                if (v < cnf.nVars() && !is_input[v]) cl2.emplace_back(y_to_yhat_flat[v], l.sign());
                else cl2.push_back(l);
            }
            cex_solver.add_clause(cl2);
            cl.inserted = true;
        }
        form.uninserted_start = form.clauses.size();
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
        const auto& y_hat = y_to_y_hat.at(y);

        y_hat_to_indic[y_hat] = ind;
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

        if (mconf.force_bw_equal && backward_defined.count(y)) {
            verb_print(3, "backward defined y, forcing indic to TRUE, since it must be correct");
            cex_solver.add_clause({Lit(ind, false)});
        }
    }
    updated_y_funcs.clear();
    t_inject += cpuTime() - t_inj0;
}

bool Manthan::get_counterexample(sample& ctx) {
    const double my_time_start = cpuTime();
    needs_repair.clear();
    if (stats.num_loops_repair == 1)
        verb_print(1, "[manthan] Getting counterexample for the first time...");

    vector<Lit> assumps;
    assumps.reserve(y_hat_to_indic.size());
    for(const auto& [y_hat, ind]: y_hat_to_indic) {
        uint32_t y = indic_to_y[ind];
        if (mconf.force_bw_equal && backward_defined.count(y))
            continue; // already forced to true
        assumps.emplace_back(ind, false);
    }
    if (mconf.force_bw_equal) assert(assumps.size() == y_order.size() - backward_defined.size());
    else assert(assumps.size() == y_order.size());

    verb_print(4, "assumptions: " << assumps);
    cex_solver.set_verbosity(conf.verb <= 2 ? 0 : conf.verb-1);
    if (stats.num_loops_repair == 1) cex_solver.simplify(&assumps);

    /* solver.set_up_for_sample_counter(1000); */
    auto ret = cex_solver.solve(&assumps);
    if (stats.num_loops_repair == 1)
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

// Recompute every y_hat in ctx by evaluating each formula's AIG. The
// formulas force y_hat from the inputs.
// NOTE: Formula dependencies may cross y_order because backward defs under
// bve_order reference later-in-order vars. So we must evaluate along a
// topological order of the actual AIG dependencies.
void Manthan::RecomputeYHat::run(Manthan& m, sample& ctx, const uint32_t y_rep) {
    const double t_topo0 = cpuTime();
    // Topological DFS over the y-vars' formula dependency graph.
    // state: 0=unvisited, 1=being expanded (on stack), 2=done.
    state.assign(m.cnf.nVars(), 0);
    topo.clear();
    dfs.clear();
    for (const auto& y_root : m.y_order) {
        if (state[y_root]) continue;
        dfs.push_back(y_root);
        while (!dfs.empty()) {
            const uint32_t y = dfs.back();
            if (state[y] == 2) { dfs.pop_back(); continue; }
            if (state[y] == 1) {
                state[y] = 2;
                topo.push_back(y);
                dfs.pop_back();
                continue;
            }
            state[y] = 1;
            for (const uint32_t v : m.formula_dep_list(y)) {
                uint32_t d;
                if (v < m.cnf.nVars()) {
                    if (m.is_input[v]) continue;
                    d = v;
                } else {
                    if (v >= m.yhat_to_y_flat.size()) continue;
                    d = m.yhat_to_y_flat[v];
                    if (d == std::numeric_limits<uint32_t>::max()) continue;
                }
                assert(state[d] != 1 &&
                    "formula dependency cycle among y-vars");
                if (state[d] == 0) dfs.push_back(d);
            }
        }
    }
    assert(topo.size() == m.y_order.size());

    changed.assign(m.cnf.nVars(), 0);
    changed[y_rep] = 1; // caller already set ctx[y_hat[y_rep]]

    const uint64_t epoch = AIG::next_visit_epoch();
    for(const auto& y: topo) {
        if (y == y_rep) continue;
        bool dep_changed = false;
        for (const uint32_t v : m.formula_dep_list(y)) {
            uint32_t d;
            if (v < m.cnf.nVars()) {
                if (m.is_input[v]) continue;
                d = v;
            } else {
                if (v >= m.yhat_to_y_flat.size()) continue;
                d = m.yhat_to_y_flat[v];
                if (d == std::numeric_limits<uint32_t>::max()) continue;
            }
            if (changed[d]) { dep_changed = true; break; }
        }
        if (!dep_changed) continue;

        const bool val = AIG::evaluate_epoch(
            m.var_to_formula.at(y).aig, epoch, m.aig_dep_stack,
            [&](uint32_t v) -> uint8_t {
                // Leaves are mixed-space: orig-space y vars read their
                // (already recomputed, earlier-in-topo) y_hat; inputs and
                // y_hat-space leaves read ctx directly.
                if (v < m.cnf.nVars() && !m.is_input[v])
                    return ctx[m.y_to_yhat_flat[v]] == l_True;
                return ctx[v] == l_True;
            });
        const lbool lval = val ? l_True : l_False;
        const uint32_t y_hat = m.y_to_yhat_flat[y];
        if (ctx[y_hat] != lval) {
            ctx[y_hat] = lval;
            changed[y] = 1;
        }
    }
    t_total += cpuTime() - t_topo0;
}

void Manthan::compute_needs_repair(const sample& ctx) {
    assert(ctx[fh->get_true_lit().var()] == l_True);
    needs_repair.clear();
    for(const auto& y: to_define_full) {
        if (ctx[y] != ctx[y_to_yhat_flat[y]]) needs_repair.insert(y);
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
    const aig_lit& aig,
    const map<uint32_t, uint32_t>& count_y_to_y_hat,
    vector<vector<Lit>>& clauses,
    uint32_t& next_var,
    Lit true_lit,
    map<aig_lit, Lit>& cache)
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

    // 2. Add ~F(x, y_hat): per-clause indicator ind_i <-> clause_i[y->y_hat],
    // then assert at least one clause is unsatisfied.
    vector<Lit> neg_clause;
    for (const auto& cl_orig : cnf.get_clauses()) {
        // Substitute y -> y_hat
        vector<Lit> cl_subst;
        for (const auto& l : cl_orig) {
            auto it = count_y_to_y_hat.find(l.var());
            if (it != count_y_to_y_hat.end())
                cl_subst.emplace_back(it->second, l.sign());
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
    map<aig_lit, Lit> tseitin_cache;
    for (const auto& y : to_define_full) {
        assert(var_to_formula.count(y));
        const auto& aig = var_to_formula.at(y).aig;
        assert(aig != nullptr);

        Lit func_out = tseitin_encode_aig(aig, count_y_to_y_hat, clauses, next_var, true_lit, tseitin_cache);
        uint32_t y_hat = count_y_to_y_hat.at(y);
        Lit y_hat_lit(y_hat, false);

        // y_hat <-> func_out
        clauses.push_back({y_hat_lit, ~func_out});
        clauses.push_back({~y_hat_lit, func_out});
    }

    // 4. Write DIMACS to a temp file and invoke the ganak subprocess to count
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
