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

vector<vector<lbool>> Manthan::get_samples(uint32_t num) {
    vector<vector<lbool>> solutions;
    solver.set_up_for_sample_counter(100);
    solver.new_vars(cnf.nVars());
    for(const auto& c: cnf.clauses) solver.add_clause(c);
    for(const auto& c: cnf.red_clauses) solver.add_red_clause(c);
    get_incidence();

    for (uint32_t i = 0; i < num; i++) {
        solver.solve();
        assert(solver.get_model().size() == cnf.nVars());
        /// TODO: old idea of CMS, make them zero if they are all the last decision and I can do it.
        solutions.push_back(solver.get_model());
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
    uint32_t num_samples = 5*1e2;
    vector<vector<lbool>> solutions = get_samples(num_samples);
    cout << "Got " << solutions.size() << " samples\n";
    solver.new_vars(1);
    my_true_lit = Lit(solver.nVars()-1, false);
    solver.add_clause({my_true_lit});

    // Training
    vector<uint32_t> to_train;
    to_train.reserve(output.size());
    for(const auto& v: output) to_train.push_back(v);
    sort_unknown(to_train, incidence);
    std::reverse(to_train.begin(), to_train.end());
    for(const auto& v: to_train) train(solutions, v);

    // Counterexample
    get_counterexample();

    return cnf;
}

void Manthan::get_counterexample() {
    // Inject the formulas into the solver
    for(const auto& f: funcs) {
        const auto& form = f.second;
        for(const auto& cl: form.clauses) {
            solver.add_clause(cl);
        }
    }
    // add indicator variables for each output == expected output
    vector<Lit> cl;
    for(const auto& o: output) {
        solver.new_var();
        Lit ind = Lit(solver.nVars()-1, false);
        Lit out = Lit(o, false);
        out_to_indic[o] = ind.var();
        indic_to_out[ind.var()] = o;
        // when indic is FALSE, they are NOT EQUIVALENT
        cl.clear();
        cl.push_back(ind);
        cl.push_back(out);
        assert(funcs.count(o));
        cl.push_back(funcs[o].out);
        solver.add_clause(cl);
        cl[1] = ~cl[1];
        cl[2] = ~cl[2];
        solver.add_clause(cl);
    }
    vector<Lit> assumptions;
    assumptions.reserve(out_to_indic.size());
    for(const auto& i: out_to_indic) {
        assumptions.push_back(Lit(i.second, true));
    }
    auto ret = solver.solve(&assumptions);
    assert(ret != l_Undef);
    if (ret == l_True) {
        cout << "No counterexample found\n";
        return;
    }
    vector<Lit> conflict = solver.get_conflict();
    cout << "Conflict sz: " << conflict.size() << endl;
    for(const auto& l: conflict)  {
        cout << l << " -- ";
        if (indic_to_out.count(l.var())) cout << " output lit: " << indic_to_out[l.var()];
        cout << endl;
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

Formula Manthan::compose_ite(const Formula& fleft, const Formula& fright, Lit branch) {
    Formula ret;
    ret.inter_vs = fleft.inter_vs;
    for(const auto& v: fright.inter_vs) ret.inter_vs.insert(v);
    ret.clauses = fleft.clauses;
    for(const auto& cl: fright.clauses) ret.clauses.push_back(cl);
    solver.new_var();
    uint32_t fresh_v = solver.nVars()-1;
    // branch -> return left
    // branch -> return right
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
