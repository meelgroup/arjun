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
#include "cryptominisat5/cryptominisat.h"
#include "cryptominisat5/solvertypesmini.h"
#include "src/arjun.h"
#include <cstdint>
#include <ios>
#include <mlpack/methods/decision_tree/decision_tree.hpp>
#include <vector>
#include "constants.h"

#define MLPACK_PRINT_INFO
#define MLPACK_PRINT_WARN
#include <mlpack.hpp>

using namespace arma;
using namespace mlpack;
using namespace mlpack::tree;
using namespace std;

#define safe_xgb(call) {  \
  int err = (call); \
  if (err != 0) { \
    fprintf(stderr, "%s:%d: error in %s: %s\n", __FILE__, __LINE__, #call, XGBGetLastError());  \
    exit(1); \
  } \
}

using std::vector;
using std::set;

using namespace ArjunInt;
using namespace ArjunNS;
using namespace CMSat;

// good: qdimacs/small-bug1-fixpoint-10.qdimacs.cnf
// also good: simplify qdimacs/amba2f9n.sat.qdimacs.cnf then run manthan

void Manthan::inject_cnf(SATSolver& s) {
    s.new_vars(cnf.nVars());
    for(const auto& c: cnf.clauses) s.add_clause(c);
    for(const auto& c: cnf.red_clauses) s.add_red_clause(c);

}

void Manthan::inject_unit(SATSolver& s) {
    s.new_vars(1);
    my_true_lit = Lit(s.nVars()-1, false);
    s.add_clause({my_true_lit});
}

vector<vector<lbool>> Manthan::get_samples(uint32_t num) {
    vector<vector<lbool>> solutions;
    solver_samp.set_up_for_sample_counter(1000);
    inject_cnf(solver_samp);
    /* solver.set_verbosity(1); */
    get_incidence();

    for (uint32_t i = 0; i < num; i++) {
        solver_samp.solve();
        assert(solver_samp.get_model().size() == cnf.nVars());
        /// TODO: old idea of CMS, make them zero if they are all the last decision and I can do it.
        solutions.push_back(solver_samp.get_model());
    }
    return solutions;
}

SimplifiedCNF Manthan::do_manthan(const SimplifiedCNF& input_cnf) {
    uint32_t tot_repaired = 0;
    uint32_t tot_simple_repaired = 0;
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
    //
    for (const auto& v: cnf.opt_sampl_vars) input.insert(v);
    for (uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i) == 0) output.insert(i);
    }
    dependency_mat.resize(cnf.nVars());
    for(auto& m: dependency_mat) m.resize(cnf.nVars(), 0);

    // Sampling
    vector<vector<lbool>> solutions = get_samples(conf.num_samples);
    cout << "Got " << solutions.size() << " samples\n";

    // Training
    inject_cnf(solver_train);
    inject_unit(solver_train);
    fh.my_true_lit = my_true_lit;
    fh.solver = &solver_train;
    cout << "True lit: " << my_true_lit << endl;
    vector<uint32_t> to_train;
    to_train.reserve(output.size());
    for(const auto& v: output) to_train.push_back(v);
    sort_unknown(to_train, incidence);
    /* std::reverse(to_train.begin(), to_train.end()); */
    for(const auto& v: to_train) train(solutions, v);

    // Counterexample
    init_solver_train();
    fix_order();
    while(true) {
        vector<lbool> ctx;
        bool finished = get_counterexample(ctx);
        if (finished) break;
        auto pr = [=](lbool val) {
            if (val == l_True) return "1";
            if (val == l_False) return "0";
            if (val == l_Undef) assert(false);
            exit(-1);
        };
        for(const auto& y: output) {
            auto y_hat = y_to_y_hat[y];
            if (ctx[y] == ctx[y_hat]) continue;
            verb_print(1, "for y " << setw(5) << y+1 << ": " << setw(4) << pr(ctx[y])
                    << " we got y_hat " << setw(5) << y_hat+1 << ":" << setw(4) << pr(ctx[y_hat]));
        }
        if (conf.verb >= 3) {
            for(uint32_t i = 0; i < cnf.nVars(); i++) cout << "val " << setw(4) << i+1 << ": " << pr(ctx[i]) << " -- ";
            cout << endl;
        }
        needs_repair.clear();
        auto better_ctx = find_better_ctx(ctx);
        for(const auto& y: output) if (!needs_repair.count(y)) ctx[y] = better_ctx[y];
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
            verb_print(1, "-------------------");
            verb_print(1, "repairing: " << y+1);
            bool done = repair(y, ctx); // beware, this updates ctx on v
            if (done) {
                num_repaired++;
                tot_repaired++;
            }
            verb_print(2, "finished repairing " << y+1 << " : " << std::boolalpha << done);
        }
        /* if (num_repaired == 0) { */
        /*     // do simple repair */
        /*     verb_print(1, "doing simple repair"); */
        /*     auto y_rep = *needs_repair.begin(); */
        /*     vector<Lit> confl; */
        /*     for(const auto& i: input) confl.push_back(~Lit(i, ctx[i] == l_False)); */
        /*     perform_repair(y_rep, ctx, confl); */
        /*     tot_simple_repaired++; */
        /* } */
        verb_print(1, "Tot repaired: " << tot_repaired << " tot simple repaired: " << tot_simple_repaired);
    }
    verb_print(1, "DONE");
    exit(0);

    return cnf;
}

// ctx contains both y, and y_hat
bool Manthan::repair(const uint32_t y_rep, vector<lbool>& ctx) {
    // F(x,y) & x = ctx(x) && forall_y (y not dependent on v) (y = ctx(y)) & NOT (v = ctx(v))
    // Used to find UNSAT core that will help us repair the function
    SATSolver solver;
    inject_cnf(solver);


    vector<Lit> assumps;
    for(const auto& x: input) {
        assumps.push_back(Lit(x, ctx[x] == l_False)); //correct value
    }
    for(const auto& y: y_order) {
        if (y == y_rep) break;
        assert(dependency_mat[y][y_rep] != 1 && "due to ordering, this should not happen");
        assert(ctx[y] == ctx[y_to_y_hat[y]]);
        Lit l = Lit(y, ctx[y] == l_False);
        verb_print(2, "assuming " << y+1 << " is " << ctx[y]);
        assumps.push_back({l});
    }

    Lit repairing = Lit(y_rep, ctx[y_rep] == l_False);
    solver.add_clause({~repairing}); //assume to wrong value
    ctx[y_to_y_hat[y_rep]] = ctx[y_rep];

    verb_print(2, "adding to solver: " << ~repairing);
    verb_print(2, "setting the to-be-repaired " << repairing << " to wrong.");
    verb_print(2, "solving with assumps: " << assumps);
    auto ret = solver.solve(&assumps);
    assert(ret != l_Undef);
    if (ret == l_True) {
        auto model = solver.get_model();
        if (conf.verb >= 3) {
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                cout << "model i " << i+1 << " : " << model[i] << endl;
            }
        }
        bool reached = false;
        for(const auto&y: y_order) {
            if (y == y_rep) {reached = true; continue;}
            if (!reached) continue;
            if (model[y] != ctx[y_to_y_hat[y]]) {
                needs_repair.insert(y);
            }
        }
        return false;
    }
    assert(ret == l_False);
    auto conflict = solver.get_conflict();
    // TODO: further minimize this conflict, if possible
    verb_print(2, "conflict: " << conflict);
    if (conflict.empty()) {
        verb_print(1, "repairing " << y_rep+1 << " is not possible");
        return false;
    }
    if (conflict.empty()) {
        verb_print(1, "repairing " << y_rep+1 << " is not possible");
        return false;
    }
    perform_repair(y_rep, ctx, conflict);
    return true;
}

void Manthan::perform_repair(const uint32_t y_rep, vector<lbool>& ctx, const vector<Lit>& conflict) {
    // not (conflict) -> v = ctx(v)
    FHolder::Formula f;
    vector<Lit> cl;
    solver_train.new_var();
    auto fresh_l = Lit(solver_train.nVars()-1, false);
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
    // when fresh_l is false, confl is satisfied
    verb_print(3, "Original formula for " << y_rep+1 << ":" << endl << funcs[y_rep]);
    verb_print(2, "Branch formula. When this is true, H is wrong:" << endl << f);
    funcs[y_rep] = fh.compose_ite(fh.constant_formula(ctx[y_rep] == l_True), funcs[y_rep], f);
    verb_print(3, "repaired formula for " << y_rep+1 << ":" << endl << funcs[y_rep]);
    verb_print(1, "repaired formula for " << y_rep+1 << " with " << conflict.size() << " vars");
    //We fixed the ctx on this variable
}

void Manthan::fix_order() {
    vector<uint32_t> sorted;
    sorted.reserve(output.size());
    for(const auto& v: output) sorted.push_back(v);
    sort_unknown(sorted, incidence);
    /* std::reverse(sorted.begin(), sorted.end()); */

    set<uint32_t> already_fixed;
    assert(y_order.empty());
    while(already_fixed.size() != output.size()) {
        for(const auto& y: sorted) {
            verb_print(2, "Checking y: " << y+1);
            if (already_fixed.count(y)) continue;
            bool ok = true;
            for(const auto& y2: output) {
                if (y == y2) continue;
                if (dependency_mat[y][y2] == 0) continue;
                if (dependency_mat[y][y2] == 1 && already_fixed.count(y2)) continue;
                verb_print(2, "Bad due to y2: " << y2+1);
                ok = false;
                break;
            }
            if (!ok) continue;
            verb_print(2, "fixed order of " << y+1 << " to: " << y_order.size());
            already_fixed.insert(y);
            y_order.push_back(y);
        }
    }
}

// Fills needs_repair with vars from y (i.e. output)
// TODO: use MaxSAT solver
vector<lbool> Manthan::find_better_ctx(const vector<lbool>& ctx) {
    needs_repair.clear();
    SATSolver s_ctx;
    s_ctx.set_up_for_sample_counter(10000);
    inject_cnf(s_ctx);
    for(const auto& x: input) {
        auto l =Lit(x, ctx[x] == l_False);
        s_ctx.add_clause({l});
    }

    for(const auto& y: output) {
        auto y_hat = y_to_y_hat[y];
        if (ctx[y] != ctx[y_hat]) continue;
        Lit l = Lit(y, ctx[y_hat] == l_False);
        s_ctx.add_clause({l});
    }

    set<Lit> assumps;
    for(const auto& y: output) {
        auto y_hat = y_to_y_hat[y];
        if (ctx[y] == ctx[y_hat]) continue;
        auto l = Lit(y, ctx[y_hat] == l_False);
        verb_print(2, "put into ass: " << l);
        assumps.insert(l);
    }

    for(;;) {
        vector<Lit> ass(assumps.begin(), assumps.end());
        lbool ret = s_ctx.solve(&ass);
        assert(ret != l_Undef);
        if (ret == l_True) {
            verb_print(2, "Improved counterexample, now potentially shorter");
            break;
        }
        auto confl = s_ctx.get_conflict();
        verb_print(2, "confl sz: " << confl.size());
        assert(!confl.empty());
        /* for(const auto&l : confl) cout << "conf: " << l << endl; */
        for(const auto&l : confl) {
            assert(assumps.count(~l));
            assumps.erase(~l);
            verb_print(2, "had to erase y: " << ~l << " because it needs repair");
            needs_repair.insert(l.var());
        }
    }
    return s_ctx.get_model();
}

void Manthan::init_solver_train() {
    vector<Lit> tmp;
    // Create variables for y_hat
    for(const auto& y: output) {
        solver_train.new_var();
        uint32_t y_hat = solver_train.nVars()-1;
        y_to_y_hat[y] = y_hat;
        y_hat_to_y[y_hat] = y;
        verb_print(2, "mapping -- y: " << y+1 << " y_hat: " << y_hat+1);
    }

    // Adds ~F(x, y_hat)
    vector<Lit> cl_indics; // if true, clause is satisfied, if false, clause is unsatisfied
    for(const auto& cl_orig: cnf.clauses) {
        // Replace y with y_hat in the clause
        vector<Lit> cl;
        for(const auto& l: cl_orig) {
            if (output.count(l.var())) {
                cl.push_back(Lit(y_to_y_hat[l.var()], l.sign()));
            } else cl.push_back(l);
        }

        solver_train.new_var();
        uint32_t v = solver_train.nVars()-1;
        Lit cl_indic(v, false);
        tmp.clear();
        tmp.push_back(~cl_indic);
        for(const auto&l : cl) tmp.push_back(l);
        solver_train.add_clause(tmp);

        for(const auto&l : cl) {
            tmp.clear();
            tmp.push_back(cl_indic);
            tmp.push_back(~l);
            solver_train.add_clause(tmp);
        }
        cl_indics.push_back(cl_indic);
    }
    tmp.clear();
    for(const auto& l: cl_indics) tmp.push_back(~l); // at least one is unsatisfied
    solver_train.add_clause(tmp);
}

bool Manthan::get_counterexample(vector<lbool>& ctx) {
    // Inject the formulas into the solver
    // Replace y with y_hat
    // TODO: have flag of what clause has already been added
    for(const auto& f: funcs) {
        const auto& form = f.second;
        for(const auto& cl: form.clauses) {
            vector<Lit> cl2;
            for(const auto& l: cl) {
                auto v = l.var();
                if (output.count(v)) {
                    cl2.push_back(Lit(y_to_y_hat[v], l.sign()));
                } else cl2.push_back(l);
            }
            solver_train.add_clause(cl2);
        }
    }

    // Relation between y_hat and func_out
    // when y_hat_to_indic is TRUE, y_hat and func_out are EQUAL
    vector<Lit> tmp;
    y_hat_to_indic.clear();
    indic_to_y_hat.clear();
    for(const auto& y: output) {
        solver_train.new_var();
        uint32_t ind = solver_train.nVars()-1;

        assert(funcs.count(y));
        auto func_out = funcs[y].out;
        auto y_hat = y_to_y_hat[y];

        y_hat_to_indic[y_hat] = ind;
        indic_to_y_hat[ind] = y_hat;
        verb_print(2, "->CTX ind: " << ind+1 << " y_hat: " << y_hat+1  << " func_out: " << func_out);

        // when indic is TRUE, y_hat and func_out are EQUAL
        auto y_hat_l = Lit(y_hat, false);
        auto ind_l = Lit(ind, false);
        tmp.clear();
        tmp.push_back(~ind_l);
        tmp.push_back(y_hat_l);
        tmp.push_back(~func_out);
        solver_train.add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        solver_train.add_clause(tmp);
    }

    vector<Lit> assumptions;
    assumptions.reserve(y_hat_to_indic.size());
    for(const auto& i: y_hat_to_indic) assumptions.push_back(Lit(i.second, false));
    verb_print(2, "assumptions: " << assumptions);


    /* solver_train.set_up_for_sample_counter(1000); */
    solver_train.simplify();
    auto ret = solver_train.solve(&assumptions);
    assert(ret != l_Undef);
    if (ret == l_True) {
        verb_print(1, "Counterexample found");
        ctx = solver_train.get_model();
        return false;
    } else {
        assert(ret == l_False);
        /* vector<Lit> conflict = solver_train.get_conflict(); */
        cout << "Function is good!" << endl;
        return true;
    }
}

FHolder::Formula Manthan::recur(DecisionTree<>* node, const uint32_t learned_v, uint32_t depth) {
    FHolder::Formula ret;
    /* for(uint32_t i = 0; i < depth; i++) cout << " "; */
    if (node->NumChildren() == 0) {
        uint32_t val = node->ClassProbabilities()[1] > node->ClassProbabilities()[0];
        /* cout << "Leaf: "; */
        /* for(uint32_t i = 0; i < node->NumClasses(); i++) { */
        /*     cout << "class "<< i << " prob: " << node->ClassProbabilities()[i] << " --- "; */
        /* } */
        /* cout << endl; */
        return fh.constant_formula(val);
    } else {
        uint32_t v = node->SplitDimension();
        /* cout << "(learning " << learned_v+1<< ") Node. v: " << v+1 << std::flush; */
        if (output.count(v)) {
            // v does not depend on us!
            verb_print(2, "v: " << v+1 << " does not depend on us!");
            assert(dependency_mat[v][learned_v] == 0);
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                if (dependency_mat[v][i] == 1) {
                    // nothing that v depends on can depend on us
                    verb_print(2, "i: " << i+1 << " does not depend on us, because " << v+1 << " depends on it");
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
        return fh.compose_ite(form_0, form_1, Lit(v, val_going_right));
    }
    assert(false);
}

void Manthan::train(const vector<vector<lbool>>& samples, uint32_t v) {
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
            dataset(j, i) = samples[i][j] == l_True ? 1 : 0;
        }
    }
    labels.resize(samples.size());
    for(uint32_t i = 0; i < samples.size(); i++) {
        labels[i] = samples[i][v] == l_True ? 1 : 0;
    }

/* //! Construct and train. */
/* template<typename FitnessFunction, */
/*          template<typename> class NumericSplitType, */
/*          template<typename> class CategoricalSplitType, */
/*          typename DimensionSelectionType, */
/*          bool NoRecursion> */
/* template<typename MatType, typename LabelsType> */
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


    // Create the RandomForest object and train it on the training data.
    DecisionTree<> r(dataset, labels, 2);

    // Compute and print the training error.
    Row<size_t> predictions;
    r.Classify(dataset, predictions);
    const double train_error =
      arma::accu(predictions != labels) * 100.0 / (double)labels.n_elem;
    verb_print(1, "Training error: " << train_error << "%." << " on v: " << v+1);
    /* r.serialize(cout, 1); */

    funcs[v] = recur(&r, v, 0);
    // Forward dependency update
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (dependency_mat[i][v]) {
            for(uint32_t j = 0; j < cnf.nVars(); j++) {
                dependency_mat[i][j] |= dependency_mat[v][j];
            }
        }
    }
    verb_print(3, "Formula for " << v+1 << ":" << endl << funcs[v]);
    verb_print(2,"Done training variable: " << v+1);
    verb_print(2, "------------------------------");
}


void Manthan::get_incidence() {
    incidence.clear();
    incidence.resize(cnf.nVars(), 0);
    for(const auto& cl: cnf.clauses) {
        for(const auto& l: cl) {
            incidence[l.var()]++;
        }
    }
}
