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
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>
#include "src/arjun.h"
#include <cstdlib>
#include <cstdint>
#include <ios>
#include <mlpack/methods/decision_tree/decision_tree.hpp>
#include <vector>
#include <ranges>
#include "constants.h"

// These ask mlpack to give more info & warnings
#define MLPACK_PRINT_INFO
#define MLPACK_PRINT_WARN
#include <mlpack.hpp>

#include "EvalMaxSAT.h"

using namespace arma;
using namespace mlpack;
using namespace mlpack::tree;

using std::vector;
using std::set;

using namespace ArjunInt;
using namespace ArjunNS;
using namespace CMSat;


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

void Manthan::inject_cnf(SATSolver& s) {
    s.new_vars(cnf.nVars());
    for(const auto& c: cnf.get_clauses()) s.add_clause(c);
    for(const auto& c: cnf.get_red_clauses()) s.add_red_clause(c);
}

vector<vector<lbool>> Manthan::get_samples(uint32_t num) {
    vector<vector<lbool>> solutions;
    SATSolver solver_samp;
    solver_samp.set_up_for_sample_counter(1000);
    inject_cnf(solver_samp);
    /* solver_samp.set_verbosity(1); */
    get_incidence();

    for (uint32_t i = 0; i < num; i++) {
        solver_samp.solve();
        assert(solver_samp.get_model().size() == cnf.nVars());
        /// TODO: old idea of CMS, make them zero if they are all the last decision and I can do it.
        solutions.push_back(solver_samp.get_model());
    }
    return solutions;
}

string Manthan::pr(const lbool val) const {
    if (val == l_True) return "1";
    if (val == l_False) return "0";
    if (val == l_Undef) assert(false);
    exit(EXIT_FAILURE);
};

SimplifiedCNF Manthan::do_manthan(const SimplifiedCNF& input_cnf) {
    assert(input_cnf.get_need_aig() && input_cnf.defs_invariant());
    uint32_t tot_repaired = 0;
    cout << "c o [DEBUG] About to assign cnf = input_cnf" << endl;
    cnf = input_cnf;
    // Grand master plan
    // 1. Get 10k samples
    // 2. Run ML to get a tree one-by-one and thereby generate an order
    // 3. Find counterexample
    // 4. Make counterexample as close to being good as possible. Originally maxsat, but we can try greedy
    // 5a -- we could fix solutions one-by-one but that's slow
    // 5b -- instead, get the conflict from the assumptions, which is a kind of poor "core",
    //       and do the "stupid" fix on that.
    //

    // CNF is divided into:
    // input vars -- original sampling vars
    // defined non-input vars -- vars defined via backward_round_synth
    // to_define vars -- vars that are not defined yet, and not input
    std::tie(input, to_define, backward_defined) = cnf.get_var_types(conf.verb);

    dependency_mat.resize(cnf.nVars());
    for(auto& m: dependency_mat) m.resize(cnf.nVars(), 0);
    auto backw_deps = cnf.compute_backw_dependencies();
    for(const auto& [backw_var, dep_set]: backw_deps) assert(backward_defined.count(backw_var) == 1);
    assert(backw_deps.size() == backward_defined.size());
    for(const auto& v: to_define) {
        assert(input.count(v) == 0);
        assert(backward_defined.count(v) == 0);
        set<uint32_t> deps_for_var;
        for(const auto& [backw_var, dep_set]: backw_deps) {
            if (dep_set.count(v)) deps_for_var.insert(backw_var);
        }
        for(const auto& d: deps_for_var) {
            assert(input.count(d) == 0);
            dependency_mat[d][v] = 1;
        }
    }

    // Sampling
    vector<vector<lbool>> solutions = get_samples(conf.num_samples);
    verb_print(1, "Got " << solutions.size() << " samples");

    // Training
    inject_cnf(solver);
    fh = std::make_unique<FHolder>(&solver);

    // TODO: what the HELL is this last_formula_var?
    /* assert(last_formula_var > solver_train.nVars()); */
    /* while(solver_train.nVars() < last_formula_var) solver_train.new_var(); */
    /* assert(solver_train.nVars() == last_formula_var); */

    verb_print(2, "True lit in solver_train: " << fh->get_true_lit());
    verb_print(2, "[do-manthan] After fh creation: solver_train.nVars() = " << solver.nVars() << " cnf.nVars() = " << cnf.nVars());
    vector<uint32_t> to_train;
    to_train.reserve(to_define.size());
    for(const auto& v: to_define) to_train.push_back(v);
    sort_unknown(to_train, incidence);
    for(const auto& v: to_train) train(solutions, v); // updates dependency_mat
    verb_print(2, "[do-manthan] After training: solver_train.nVars() = " << solver.nVars());

    add_not_F_x_yhat();
    fix_order();
    // Counterexample-guided repair
    while(true) {
        inject_formulas_into_solver();
        vector<lbool> ctx;
        bool finished = get_counterexample(ctx);
        for(const auto& val: ctx) assert(val != l_Undef);
        if (finished) break;
        for(const auto& y: to_define) {
            const auto y_hat = y_to_y_hat[y];
            if (ctx[y] == ctx[y_hat]) continue;
            verb_print(3, "for y " << setw(5) << y+1 << ": " << setw(4) << pr(ctx[y])
                    << " we got y_hat " << setw(5) << y_hat+1 << ":" << setw(4) << pr(ctx[y_hat]));
        }
        if (conf.verb >= 3) {
            cout << "c o [DEBUG] CNF valuation: ";
            for(uint32_t i = 0; i < cnf.nVars(); i++)
                cout << "var " << setw(3) << i+1 << ": " << pr(ctx[i]) << " -- ";
            cout << endl;
        }
        auto better_ctx = find_better_ctx(ctx);
        for(const auto& y: to_define) if (!needs_repair.count(y)) ctx[y] = better_ctx[y];

        cout << "c o [DEBUG] Needs repair vars: ";
        for(const auto& v: needs_repair) cout << v+1 << " ";
        cout << endl;
        if (conf.verb >= 3) {
            cout << "c o [DEBUG] after find_better_ctx, CNF valuation: ";
            for(uint32_t i = 0; i < cnf.nVars(); i++)
                cout << "var " << setw(3) << i+1 << ": " << pr(ctx[i]) << " -- ";
            cout << endl;
        }

        assert(!needs_repair.empty());
        uint32_t num_repaired = 0;
        while(!needs_repair.empty()) {
            uint32_t y = std::numeric_limits<uint32_t>::max();
            for(const auto& t: y_order) {
                if (needs_repair.count(t)) {
                    y = t;
                    break;
                }
            }
            assert(y != std::numeric_limits<uint32_t>::max());
            needs_repair.erase(y);
            verb_print(3, "-------------------");
            verb_print(1, "repairing: " << y+1);
            bool done = repair(y, ctx); // beware, this updates ctx on v
            if (done) {
                num_repaired++;
                tot_repaired++;
            }
            verb_print(3, "finished repairing " << y+1 << " : " << std::boolalpha << done);
        }
        verb_print(1, "Num repaired: " << num_repaired << " tot repaired: " << tot_repaired);
    }
    verb_print(1, "DONE");

    // Build final CNF
    map<uint32_t, aig_ptr> aigs;
    for(const auto& y: to_define) {
        assert(var_to_formula.count(y));
        verb_print(2, "Final formula for " << y+1 << ":" << endl << var_to_formula[y]);
        aigs[y] = var_to_formula[y].aig;
    }
    SimplifiedCNF fcnf = cnf;
    fcnf.map_aigs_to_orig(aigs, cnf.nVars());
    assert(fcnf.get_need_aig() && fcnf.defs_invariant());
    return fcnf;
}

vector<Lit> Manthan::further_minimize_conflict_via_maxsat(const vector<Lit>& conflict, const vector<Lit>& assumps, const Lit& repairing) {
    // Further minimize the conflict using MaxSAT
    EvalMaxSAT min_solver;
    for(uint32_t i = 0; i < cnf.nVars(); i++) min_solver.newVar();
    for(const auto& c: cnf.get_clauses()) min_solver.addClause(lits_to_ints(c));
    min_solver.addClause(lits_to_ints({~repairing})); // assume wrong value

    // Convert conflict to a set for fast lookup
    set<Lit> conflict_set(conflict.begin(), conflict.end());

    // Add soft clauses only for assumptions that are in the conflict
    for(const auto& l: assumps) {
        if (conflict_set.count(~l)) {
            min_solver.addClause(lits_to_ints({l}), 1); // soft clause
        } else {
            // Not in conflict, add as hard constraint
            /* min_solver.addClause(lits_to_ints({l})); */
        }
    }

    cout << "c o Running MaxSAT minimization with " << conflict_set.size() << " soft clauses" << endl;
    auto min_ret = min_solver.solve();
    cout << "c o cost of minimization: " << min_solver.getCost() << endl;
    assert(min_ret);

    // Extract minimized conflict
    vector<Lit> minimized_conflict;
    for(const auto& l: assumps) {
        if (conflict_set.count(~l) && min_solver.getValue(lit_to_int(l))) {
            minimized_conflict.push_back(~l);
        }
    }
    cout << "c o Orig assumps size: " << assumps.size()
         << " initial conflict size: " << conflict.size()
         << " minimized conflict size: " << minimized_conflict.size() << endl;
    return minimized_conflict;
}

bool Manthan::repair(const uint32_t y_rep, vector<lbool>& ctx) {
    // F(x,y) & x = ctx(x) && forall_y (y not dependent on v) (y = ctx(y)) & NOT (v = ctx(v))
    // Used to find UNSAT core that will help us repair the function
    SATSolver repair_solver;
    inject_cnf(repair_solver);

    vector<Lit> assumps; assumps.reserve(input.size());
    for(const auto& x: input) assumps.push_back(Lit(x, ctx[x] == l_False)); //correct value
    for(const auto& x: backward_defined) assumps.push_back(Lit(x, ctx[x] == l_False)); // TODO is this needed?
                                                                            //
    for(const auto& y: y_order) {
        if (y == y_rep) break;
        assert(dependency_mat[y][y_rep] != 1 && "due to ordering, this should not happen");
        assert(ctx[y] == ctx[y_to_y_hat[y]]);
        const Lit l = Lit(y, ctx[y] == l_False);
        verb_print(3, "assuming " << y+1 << " is " << ctx[y]);
        assumps.push_back({l});
    }

    const Lit repairing = Lit(y_rep, ctx[y_rep] == l_False);
    repair_solver.add_clause({~repairing}); //assume to wrong value
    ctx[y_to_y_hat[y_rep]] = ctx[y_rep];

    verb_print(2, "adding to solver: " << ~repairing);
    verb_print(2, "setting the to-be-repaired " << repairing << " to wrong.");
    verb_print(5, "solving with assumps: " << assumps);
    auto ret = repair_solver.solve(&assumps);
    assert(ret != l_Undef);
    if (ret == l_True) {
        const auto& model = repair_solver.get_model();
        if (conf.verb >= 3) {
            for(uint32_t i = 0; i < cnf.nVars(); i++)
                cout << "model i " << setw(5) << i+1 << " : " << model[i] << endl;
        }
        bool reached = false;
        for(const auto&y: y_order) {
            if (y == y_rep) {reached = true; continue;}
            if (!reached) continue;
            if (model[y] != ctx[y_to_y_hat[y]]) needs_repair.insert(y);
        }
        return false;
    }
    assert(ret == l_False);
    auto conflict = repair_solver.get_conflict();
    verb_print(2, "initial conflict: " << conflict);
    if (conflict.empty()) {
        verb_print(1, "repairing " << y_rep+1 << " is not possible");
        return false;
    }
    if (false) {
        conflict = further_minimize_conflict_via_maxsat(conflict, assumps, repairing);
        cout << "c o Minimized conflict: " << conflict << endl;
    }
    perform_repair(y_rep, ctx, conflict);
    return true;
}

// ctx contains both y, and y_hat
bool Manthan::repair_maxsat(const uint32_t y_rep, vector<lbool>& ctx) {
    // F(x,y) & x = ctx(x) && forall_y (y not dependent on v) (y = ctx(y)) & NOT (v = ctx(v))
    // Used to find UNSAT core that will help us repair the function
    EvalMaxSAT repair_solver;
    for(uint32_t i = 0; i < cnf.nVars(); i++) repair_solver.newVar();
    for(const auto& c: cnf.get_clauses()) repair_solver.addClause(lits_to_ints(c));

    vector<Lit> assumps; assumps.reserve(input.size());
    for(const auto& x: input) assumps.push_back(Lit(x, ctx[x] == l_False));
    for(const auto& x: backward_defined) assumps.push_back(Lit(x, ctx[x] == l_False)); // TODO is this needed?

    for(const auto& y: y_order) {
        if (y == y_rep) break;
        assert(dependency_mat[y][y_rep] != 1 && "due to ordering, this should not happen");
        assert(ctx[y] == ctx[y_to_y_hat[y]]);
        const Lit l = Lit(y, ctx[y] == l_False);
        verb_print(1, "assuming " << y+1 << " is " << ctx[y]);
        assumps.push_back({l});
    }

    const Lit repairing = Lit(y_rep, ctx[y_rep] == l_False);
    repair_solver.addClause(lits_to_ints({~repairing})); //assume to wrong value
    ctx[y_to_y_hat[y_rep]] = ctx[y_rep];

    verb_print(1, "adding to solver: " << ~repairing);
    verb_print(2, "setting the to-be-repaired " << repairing << " to wrong.");
    verb_print(5, "solving with assumps: " << assumps);

    for(const auto& l: assumps) repair_solver.addClause(lits_to_ints({l}), 1);
    cout << "c o Running MaxSAT repair for var " << y_rep+1 << " with " << assumps.size() << "soft clauses " << endl;
    auto ret = repair_solver.solve();
    if (!ret) {
        verb_print(1, "repairing " << y_rep+1 << " is not possible");
        return false;
    }
    assert(ret);
    if (repair_solver.getCost() == 0) {
        bool reached = false;
        for(const auto&y: y_order) {
            if (y == y_rep) {reached = true; continue;}
            if (!reached) continue;
            if (repair_solver.getValue(y+1) != (ctx[y_to_y_hat[y]] == l_True)) needs_repair.insert(y);
        }
        return false;
    }

    vector<Lit> conflict;
    for(const auto&l : assumps) {
        if (!repair_solver.getValue(lit_to_int(l))) conflict.push_back(~l);
    }
    assert(conflict.size() == repair_solver.getCost());
    verb_print(1, "repair conflict: " << conflict);
    cout << "c o Orig assumps size: " << assumps.size() << " conflict size: " << conflict.size() << endl;
    perform_repair(y_rep, ctx, conflict);
    return true;
}

void Manthan::perform_repair(const uint32_t y_rep, vector<lbool>& ctx, const vector<Lit>& conflict) {
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
        for(uint32_t i = 0; i < cnf.nVars(); i++)
            dependency_mat[y_rep][i] |= dependency_mat[l.var()][i];
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
    auto b1 = aig_mng.new_const(true);
    for(const auto& l: conflict) {
        auto lit_aig = AIG::new_lit(Lit(l.var(), !l.sign()));
        b1 = AIG::new_and(b1, lit_aig);
    }
    f.aig = b1;

    // when fresh_l is false, confl is satisfied
    verb_print(4, "Original formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    verb_print(4, "Branch formula. When this is true, H is wrong:" << endl << f);
    var_to_formula[y_rep] = fh->compose_ite(fh->constant_formula(ctx[y_rep] == l_True), var_to_formula[y_rep], f);
    verb_print(3, "repaired formula for " << y_rep+1 << " with " << conflict.size() << " vars");
    verb_print(4, "repaired formula for " << y_rep+1 << ":" << endl << var_to_formula[y_rep]);
    //We fixed the ctx on this variable
}

void Manthan::fix_order() {
    verb_print(1, "[manthan] Fixing order...");
    vector<uint32_t> sorted;
    sorted.reserve(to_define.size());
    for(const auto& v: to_define) sorted.push_back(v);
    sort_unknown(sorted, incidence);

    set<uint32_t> already_fixed;
    assert(y_order.empty());
    while(already_fixed.size() != to_define.size()) {
        for(const auto& y: sorted) {
            if (already_fixed.count(y)) continue;
            verb_print(2, "Trying to add " << y+1 << " to order...");

            bool ok = true;
            for(const auto& y2: to_define) {
                if (y == y2) continue;
                if (dependency_mat[y][y2] == 0) continue;
                if (dependency_mat[y][y2] == 1 && already_fixed.count(y2)) continue;
                verb_print(2, "Bad due to y2: " << y2+1);
                ok = false;
                break;
            }
            if (!ok) continue;
            verb_print(2, "Fixed order of " << y+1 << " to: " << y_order.size());
            already_fixed.insert(y);
            y_order.push_back(y);
        }
    }
}

// Fills needs_repair with vars from y (i.e. output)
vector<lbool> Manthan::find_better_ctx(const vector<lbool>& ctx) {
    needs_repair.clear();
    verb_print(2, "Finding better ctx.");
    EvalMaxSAT s_ctx;
    for(uint32_t i = 0; i < cnf.nVars(); i++) s_ctx.newVar();
    for(const auto& c: cnf.get_clauses()) s_ctx.addClause(lits_to_ints(c));

    // Fix input and backward_defined values
    for(const auto& x: input) {
        assert(ctx[x] != l_Undef && "Input variable must be defined in counterexample");
        const auto l = Lit(x, ctx[x] == l_False);
        s_ctx.addClause(lits_to_ints({l}));
    }

    // TODO not sure this is needed/should be here?
    for(const auto& x: backward_defined) {
        assert(ctx[x] != l_Undef && "Backward variable must be defined in counterexample");
        const auto l = Lit(x, ctx[x] == l_False);
        s_ctx.addClause(lits_to_ints({l}));
    }

    // Fix to_define variables that are correct (y_hat is the learned one)
    for(const auto& y: to_define) {
        const auto y_hat = y_to_y_hat[y];
        if (ctx[y] != ctx[y_hat]) continue;
        verb_print(3, "[find-better-ctx] CTX is CORRECT on y=" << y+1 << " y_hat=" << y_hat+1
             << " -- ctx[y]=" << pr(ctx[y]) << " ctx[y_hat]=" << pr(ctx[y_hat]));
        const Lit l = Lit(y, ctx[y_hat] == l_False);
        s_ctx.addClause(lits_to_ints({l}));
    }

    // Fix to_define variables that are incorrect via assumptions
    set<Lit> assumps;
    for(const auto& y: to_define) {
        const auto y_hat = y_to_y_hat[y];
        if (ctx[y] == ctx[y_hat]) continue;
        const auto l = Lit(y, ctx[y_hat] == l_False);
        verb_print(2, "[find-better-ctx] put into assumps y= " << l);
        assumps.insert(l);
        s_ctx.addClause(lits_to_ints({l}), 1); //want to flip this
    }

    /* verb_print(3, "[find-better-ctx] iteration " << i << " with " << ass.size() << " assumptions"); */
    auto ret = s_ctx.solve();
    assert(ret && "must be satisfiable");
    verb_print(1, "optimum found: " << s_ctx.getCost() << " original assumps size: " << assumps.size());
    assert(s_ctx.getCost() > 0);
    for(const auto&l : assumps) {
        if (s_ctx.getValue(l.var()+1) ^ !l.sign()) {
            verb_print(1, "had to erase y: " << ~l << " because it needs repair");
            needs_repair.insert(l.var());
        }
    }
    assert(needs_repair.size() == s_ctx.getCost());
    assert(!needs_repair.empty());

    verb_print(1, "Finding better ctx DONE, needs_repair size now: " << needs_repair.size());
    vector<lbool> better_ctx(cnf.nVars(), l_Undef);
    for(const auto& v: to_define) {
        better_ctx[v] = s_ctx.getValue(v+1) ? l_True : l_False;
    }
    return better_ctx;
}


// Adds ~F(x, y_hat), fills y_to_y_hat and y_hat_to_y
void Manthan::add_not_F_x_yhat() {
    vector<Lit> tmp;
    // Create variables for y_hat
    for(const auto& y: to_define) {
        solver.new_var();
        const uint32_t y_hat = solver.nVars()-1;
        y_to_y_hat[y] = y_hat;
        y_hat_to_y[y_hat] = y;
        verb_print(2, "mapping -- y: " << y+1 << " y_hat: " << y_hat+1);
        verb_print(4, "formula for y " << y+1 << ":" << endl << var_to_formula[y]);
    }

    // Adds ~F(x, y_hat)
    vector<Lit> cl_indics; // if true, clause is satisfied, if false, clause is unsatisfied
    for(const auto& cl_orig: cnf.get_clauses()) {
        // Replace y with y_hat in the clause
        vector<Lit> cl;
        for(const auto& l: cl_orig) {
            if (to_define.count(l.var())) cl.push_back(Lit(y_to_y_hat[l.var()], l.sign()));
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
        /* if (form.already_added_to_manthans_solver) continue; */
        for(auto& cl: form.clauses) {
            vector<Lit> cl2;
            for(const auto& l: cl) {
                auto v = l.var();
                if (to_define.count(v)) { cl2.push_back(Lit(y_to_y_hat[v], l.sign()));}
                else cl2.push_back(l);
            }
            solver.add_clause(cl2);
        }
        /* form.already_added_to_manthans_solver = true; */
    }
}

bool Manthan::get_counterexample(vector<lbool>& ctx) {
    // Relation between y_hat and form_out
    // when y_hat_to_indic is TRUE, y_hat and form_out are EQUAL
    vector<Lit> tmp;
    y_hat_to_indic.clear();
    indic_to_y_hat.clear();
    for(const auto& y: to_define) {
        solver.new_var();
        const uint32_t ind = solver.nVars()-1;

        assert(var_to_formula.count(y));
        const auto form_out = var_to_formula[y].out;
        const auto y_hat = y_to_y_hat[y];

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
    }

    vector<Lit> assumptions;
    assumptions.reserve(y_hat_to_indic.size());
    for(const auto& i: y_hat_to_indic) assumptions.push_back(Lit(i.second, false));
    verb_print(4, "assumptions: " << assumptions);


    /* solver_train.set_up_for_sample_counter(1000); */
    /* solver.simplify(); */
    auto ret = solver.solve(&assumptions);
    assert(ret != l_Undef);
    if (ret == l_True) {
        verb_print(1, "Counterexample found");
        ctx = solver.get_model();
        assert(ctx[fh->get_true_lit().var()] == l_True);
        return false;
    } else {
        assert(ret == l_False);
        verb_print(1, "Formula is good!");
        for(auto& f: var_to_formula) {
            if (!f.second.finished) {
                verb_print(1, "Marking Formula for " << f.first+1 << " as finished");
                f.second.finished = true;
            }
        }
        return true;
    }
}

FHolder::Formula Manthan::recur(DecisionTree<>* node, const uint32_t learned_v, uint32_t depth) {
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
        /* cout << "(learning " << learned_v+1<< ") Node. v: " << v+1 << std::flush; */
        if (to_define.count(v)) {
            // v does not depend on us!
            verb_print(2, "v: " << v+1 << " does not depend on us!");
            assert(dependency_mat[v][learned_v] == 0);
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                if (dependency_mat[v][i] == 1) {
                    // nothing that v depends on can depend on us
                    verb_print(2, "ERROR. i: " << i+1 << " does not depend on us, because " << v+1 << " depends on it");
                    assert(dependency_mat[i][learned_v] == 0);
                }
            }
            // we depend on v
            dependency_mat[learned_v][v] = 1;
            verb_print(2, learned_v+1 << " depends on " << v+1);

            // and everything that v depends on
            for(uint32_t i = 0 ; i < cnf.nVars(); i++) {
                dependency_mat[learned_v][i] |= dependency_mat[v][i];
                if (dependency_mat[v][i])
                    verb_print(2, "setting " << learned_v+1 << " depends on " << i+1);
            }
        }

        /* cout << "  -- all-0 goes -> " << node->CalculateDirection(point_0); */
        /* cout << "  -- all-1 goes -> " << node->CalculateDirection(point_1) << endl; */
        assert(node->NumChildren() == 2);
        auto form_0 = recur(&node->Child(0), learned_v, depth+1);
        auto form_1 = recur(&node->Child(1), learned_v, depth+1);
        bool val_going_right = node->CalculateDirection(point_1);
        return fh->compose_ite(form_0, form_1, Lit(v, val_going_right));
    }
    assert(false);
}

void Manthan::train(const vector<vector<lbool>>& samples, const uint32_t v) {
    verb_print(2, "training variable: " << v+1);
    assert(!samples.empty());
    assert(v < cnf.nVars());
    point_0.resize(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) point_0[i] = 0;
    point_1.resize(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) point_1[i] = 1;

    Mat<size_t> dataset;
    Row<size_t> labels;
    dataset.resize(cnf.nVars(), samples.size());
    verb_print(2, "Dataset size: " << dataset.n_rows << " x " << dataset.n_cols);
    // TODO: we fill 0 for the value of v, this MAY come back in the tree,but likely not

    for(uint32_t i = 0; i < samples.size(); i++) {
        assert(samples[i].size() == cnf.nVars());
        for(uint32_t j = 0; j < cnf.nVars(); j++) {
            // we are learning v.
            if (j == v) {dataset(j, i) = 0; continue;}
            if (dependency_mat[j][v] == 1) { dataset(j, i) = 0; continue;}
            dataset(j, i) = lbool_to_bool(samples[i][j]);
        }
    }
    labels.resize(samples.size());
    for(uint32_t i = 0; i < samples.size(); i++) labels[i] = lbool_to_bool(samples[i][v]);

    // Create the RandomForest object and train it on the training data.
    DecisionTree<> r(dataset, labels, 2);

    // Compute and print the training error.
    Row<size_t> predictions;
    r.Classify(dataset, predictions);
    const double train_error =
      arma::accu(predictions != labels) * 100.0 / (double)labels.n_elem;
    verb_print(1, "Training error: " << train_error << "%." << " on v: " << v+1);
    /* r.serialize(cout, 1); */

    cout << "c o [DEBUG] About to call recur for v " << v+1 << " num children: " << r.NumChildren() << endl;
    var_to_formula[v] = recur(&r, v, 0);
    cout << "c o [DEBUG] Formula for v " << v+1 << ":" << endl << var_to_formula[v] << endl;

    // Forward dependency update
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        if (dependency_mat[i][v]) {
            for(uint32_t j = 0; j < cnf.nVars(); j++) {
                if (input.count(j)) continue;
                dependency_mat[i][j] |= dependency_mat[v][j];
            }
        }
    }
    verb_print(4, "Tentative, trained formula for y " << v+1 << ":" << endl << var_to_formula[v]);
    verb_print(2,"Done training variable: " << v+1);
    verb_print(2, "------------------------------");
}

void Manthan::get_incidence() {
    incidence.clear();
    incidence.resize(cnf.nVars(), 0);
    for(const auto& cl: cnf.get_clauses()) {
        for(const auto& l: cl) incidence[l.var()]++;
    }
}
