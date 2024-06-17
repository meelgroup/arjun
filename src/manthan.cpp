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
#include <mlpack/methods/decision_tree/decision_tree.hpp>
#include <vector>
#include <iterator>
#include <algorithm>
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
    solver_samp.set_up_for_sample_counter(100);
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
    /* uint32_t num_samples = 5*1e2; */
    uint32_t num_samples = 2;
    vector<vector<lbool>> solutions = get_samples(num_samples);
    cout << "Got " << solutions.size() << " samples\n";
    cout << "True lit: " << my_true_lit << endl;

    // Training
    inject_cnf(solver_train);
    inject_unit(solver_train);
    vector<uint32_t> to_train;
    to_train.reserve(output.size());
    for(const auto& v: output) to_train.push_back(v);
    sort_unknown(to_train, incidence);
    std::reverse(to_train.begin(), to_train.end());
    for(const auto& v: to_train) train(solutions, v);

    // Counterexample
    vector<lbool> ctx;
    bool finished = get_counterexample(ctx);
    if (finished) return cnf;
    auto pr = [=](lbool val) {
        if (val == l_True) return "1";
        if (val == l_False) return "0";
        if (val == l_Undef) assert(false);
        exit(-1);
    };
    for(const auto& y: output) {
        auto y_hat = y_to_y_hat[y];
        if (ctx[y] == ctx[y_hat]) continue;
        cout << "for y " << setw(5) << y+1 << ": " << setw(4) << pr(ctx[y])
            << " we got y_hat " << setw(5) << y_hat+1 << ":" << setw(4) << pr(ctx[y_hat]) << endl;
        for(const auto& i: input) {
            cout << "val " << setw(4) << i+1 << ": " << pr(ctx[i]) << " -- ";
        }
        cout << endl;
    }
    vector<uint32_t> needs_repair;
    auto better_ctx = find_better_ctx(ctx, needs_repair);
    /* fix_order(); */
    for(const auto& v: needs_repair) {
        cout << "repairing: " << v+1 << endl;
        repair(v, ctx);

    }

    // repair. We need to find the largest set of solutions for which the valuation needs to be flipped
    exit(0);

    return cnf;
}

void Manthan::repair(uint32_t v, const vector<lbool>& ctx) {
    // F(x,y) & x = ctx(x) && forall_y (y not dependent on v) (y = ctx(y)) & NOT (v = ctx(v))
    SATSolver solver;
    inject_cnf(solver);

    vector<Lit> cl;
    cl.push_back(Lit(v, ctx[v] == l_True));
    solver.add_clause(cl);

    vector<Lit> assumps;
    for(const auto& x: input) {
        assumps.push_back(Lit(x, ctx[x] == l_False));
    }
    for(const auto& y: output) {
        if (dependency_mat[y][v] == 1) continue;
        assumps.push_back(Lit(y, ctx[y] == l_False));
    }
    auto ret = solver.solve(&assumps);
    assert(ret != l_Undef);
    if (ret == l_True) {
        cout << "repairing " << v+1 << " is not possible\n";
        return;
    }
    assert(ret == l_False);
    auto conflict = solver.get_conflict();
    cout << "conflict: " << conflict << endl;

    // not (conflict) -> v = ctx(v)
    Formula f;
    cl.clear();
    solver_train.new_var();
    auto fresh_l = Lit(solver_train.nVars()-1, false);
    cl.push_back(fresh_l);
    for(const auto& l: conflict) cl.push_back(l);
    f.clauses.push_back(cl);
    for(const auto& l: conflict) {
        cl.clear();
        cl.push_back(~fresh_l);
        cl.push_back(~l);
        f.clauses.push_back(cl);
    }
    f.out = fresh_l;
    // when fresh_l is false, confl is satisfied
    cout << "Original formula for " << v+1 << ":" << endl
        << funcs[v] << endl;
    cout << "Branch formula. When this is true, H is wrong:" << endl
        << f << endl;
    funcs[v] = compose_ite(constant_formula(ctx[v] == l_True), funcs[v], f);
    cout << "repaired formula for " << v+1 << ":" << endl
        << funcs[v] << endl;
    exit(0);
}

void Manthan::fix_order() {
    set<uint32_t> already_fixed;
    while(already_fixed.size() != output.size()) {
        for(const auto& y: output) {
            if (already_fixed.count(y)) continue;
            bool ok = true;
            for(const auto& y2: output) {
                if (y == y2) continue;
                if (dependency_mat[y][y2] == 0) continue;
                if (dependency_mat[y][y2] == 1 && already_fixed.count(y)) continue;
                ok = false;
                break;
            }
            if (!ok) continue;
            already_fixed.insert(y);
            /* y_order.push_back(y); */
        }
    }
}

vector<lbool> Manthan::find_better_ctx(const vector<lbool>& ctx, vector<uint32_t>& needs_repair) {
    needs_repair.clear();
    inject_cnf(solver_rep);
    vector<Lit> cl;
    for(const auto& x: input) {
        cl.clear();
        cl.push_back(Lit(x, ctx[x] == l_False));
        solver_rep.add_clause(cl);
    }
    set<Lit> assumps;
    for(const auto& y: output) {
        auto y_hat = y_to_y_hat[y];
        /* if (ctx[y] == ctx[y_hat]) continue; */
        auto l = Lit(y, ctx[y_hat] == l_False);
        /* cout << "put into ass: " << l << endl; */
        assumps.insert(l);
    }

    for(;;) {
        vector<Lit> ass(assumps.begin(), assumps.end());
        lbool ret = solver_rep.solve(&ass);
        assert(ret != l_Undef);
        if (ret == l_True) break;
        auto confl = solver_rep.get_conflict();
        for(const auto&l : confl) {
            cout << "conf: " << l << endl;
        }
        for(const auto&l : confl) {
            assert(assumps.count(~l));
            assumps.erase(~l);
            cout << "had to erase y: " << ~l << " because it needs repair" << endl;
            needs_repair.push_back(l.var());
        }
    }
    return solver_rep.get_model();
}

bool Manthan::get_counterexample(vector<lbool>& ctx) {
    // Inject the formulas into the solver
    for(const auto& f: funcs) {
        const auto& form = f.second;
        for(const auto& cl: form.clauses) solver_train.add_clause(cl);
    }
    // Create variables for y_hat
    for(const auto& y: output) {
        solver_train.new_var();
        uint32_t y_hat = solver_train.nVars()-1;
        y_to_y_hat[y] = y_hat;
        y_hat_to_y[y_hat] = y;
        cout << "mapping -- y: " << y+1 << " y_hat: " << y_hat+1 << endl;
    }

    // Relation between y_hat and func_out
    // when y_hat_to_indic is TRUE, y_hat and func_out are EQUAL
    vector<Lit> tmp;
    for(const auto& y: output) {
        solver_train.new_var();
        uint32_t ind = solver_train.nVars()-1;

        assert(funcs.count(y));
        auto func_out = funcs[y].out;
        auto y_hat = y_to_y_hat[y];

        y_hat_to_indic[y_hat] = ind;
        indic_to_y_hat[ind] = y_hat;
        cout << "-> ind: " << ind+1 << " y_hat: " << y_hat+1  << " func_out: " << func_out << endl;

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

    vector<Lit> assumptions;
    assumptions.reserve(y_hat_to_indic.size());
    for(const auto& i: y_hat_to_indic) assumptions.push_back(Lit(i.second, false));
    cout << "assumptions: " << assumptions << endl;


    auto ret = solver_train.solve(&assumptions);
    assert(ret != l_Undef);
    if (ret == l_True) {
        cout << "Counterexample found\n";
        ctx = solver_train.get_model();
        return false;
    } else {
        assert(ret == l_False);
        /* vector<Lit> conflict = solver_train.get_conflict(); */
        cout << "Function is good!" << endl;
        return true;
    }
}

Formula Manthan::recur(DecisionTree<>* node, const uint32_t learned_v, uint32_t depth) {
    Formula ret;
    for(uint32_t i = 0; i < depth; i++) cout << " ";
    if (node->NumChildren() == 0) {
        uint32_t val = node->ClassProbabilities()[1] > node->ClassProbabilities()[0];
        cout << "Leaf: ";
        for(uint32_t i = 0; i < node->NumClasses(); i++) {
            cout << "class "<< i << " prob: " << node->ClassProbabilities()[i] << " --- ";
        }
        cout << endl;
        return constant_formula(val);
    } else {
        uint32_t v = node->SplitDimension();
        cout << "(learning " << learned_v+1<< ") Node. v: " << v+1 << std::flush;
        if (output.count(v)) {
            // v does not depend on us!
            assert(dependency_mat[v][learned_v] == 0);
            // we depend on v
            dependency_mat[learned_v][v] = 1;
            // and everything that v depends on
            for(uint32_t i = 0 ; i < cnf.nVars(); i++) dependency_mat[learned_v][i] |= dependency_mat[v][i];
        }

        cout << "  -- all-0 goes -> " << node->CalculateDirection(point_0);
        cout << "  -- all-1 goes -> " << node->CalculateDirection(point_1) << endl;
        assert(node->NumChildren() == 2);
        auto form_0 = recur(&node->Child(0), learned_v, depth+1);
        auto form_1 = recur(&node->Child(1), learned_v, depth+1);
        bool val_going_right = node->CalculateDirection(point_1);
        return compose_ite(form_0, form_1, Lit(v, val_going_right));
    }
    assert(false);
}

void Manthan::train(const vector<vector<lbool>>& samples, uint32_t v) {
    cout << "variable: " << v+1 << endl;
    assert(!samples.empty());
    assert(v < cnf.nVars());
    point_0.resize(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) point_0[i] = 0;
    point_1.resize(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) point_1[i] = 1;

    Mat<size_t> dataset;
    Row<size_t> labels;
    dataset.resize(cnf.nVars(), samples.size());
    cout << "Dataset size: " << dataset.n_rows << " x " << dataset.n_cols << endl;
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
    cout << "Training error: " << train_error << "%." << endl;
    /* r.serialize(cout, 1); */

    funcs[v] = recur(&r, v, 0);
    cout << "Formula for " << v+1 << ":" << endl
        << funcs[v] << endl;
    cout << "------------------------------" << endl;
    cout << "Done\n";
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

Formula Manthan::constant_formula(int value) {
    Formula ret;
    ret.out = value ? my_true_lit : ~my_true_lit;
    ret.inter_vs.insert(my_true_lit.var());
    return ret;
}


Formula Manthan::compose_ite(const Formula& fleft, const Formula& fright, const Formula& branch) {
    Formula ret = compose_ite(fleft, fright, branch.out);
    ret.inter_vs.insert(branch.inter_vs.begin(), branch.inter_vs.end());
    ret.inter_vs.insert(branch.out.var());
    ret.clauses.insert(ret.clauses.end(), branch.clauses.begin(), branch.clauses.end());
    return ret;
}

Formula Manthan::compose_ite(const Formula& fleft, const Formula& fright, Lit branch) {
    Formula ret;
    ret.inter_vs = fleft.inter_vs;
    for(const auto& v: fright.inter_vs) ret.inter_vs.insert(v);
    ret.clauses = fleft.clauses;
    for(const auto& cl: fright.clauses) ret.clauses.push_back(cl);
    solver_train.new_var();
    uint32_t fresh_v = solver_train.nVars()-1;
    //  branch -> return left
    // !branch -> return right
    //
    //  b -> fresh = left
    // !b -> fresh = right
    //
    // !b V    f V -left
    // -b V   -f V  left
    //  b V    f V -right
    //  b V   -f V  right
    //
    Lit b = branch;
    Lit l = fleft.out;
    Lit r = fright.out;
    Lit fresh = Lit(fresh_v, false);
    ret.inter_vs.insert(fresh_v);
    ret.clauses.push_back({~b, fresh, ~l});
    ret.clauses.push_back({~b, ~fresh, l});
    ret.clauses.push_back({b, fresh, ~r});
    ret.clauses.push_back({b, ~fresh, r});
    ret.out = Lit(fresh_v, false);

    return ret;
}
