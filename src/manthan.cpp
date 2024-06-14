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
#include "src/arjun.h"
#include <cstdint>
#include <mlpack/methods/decision_tree/decision_tree.hpp>
#include <vector>

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
    sample_solver.set_up_for_sample_counter(100);
    sample_solver.new_vars(cnf.nVars());
    for(const auto& c: cnf.clauses) sample_solver.add_clause(c);
    for(const auto& c: cnf.red_clauses) sample_solver.add_red_clause(c);

    for (uint32_t i = 0; i < num; i++) {
        sample_solver.solve();
        assert(sample_solver.get_model().size() == cnf.nVars());
        solutions.push_back(sample_solver.get_model());
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

    uint32_t num_samples = 5*1e2;
    vector<vector<lbool>> solutions = get_samples(num_samples);
    cout << "Got " << solutions.size() << " samples\n";
    for(const auto& v: output) train(solutions, v);

    return cnf;
}

void Manthan::recur(DecisionTree<>* node, const vec& point_0, const vec& point_1, uint32_t depth) {
   for(uint32_t i = 0; i < depth; i++) cout << " ";
   if (node->NumChildren() == 0) {
       cout << "Leaf: ";
       for(uint32_t i = 0; i < node->NumClasses(); i++) {
           cout << "class "<< i << " prob: " << node->ClassProbabilities()[i] << " --- ";
       }
       cout << endl;
   } else {
       cout << "Node. v: " << node->SplitDimension();
       cout << "  -- all-0 goes -> " << node->CalculateDirection(point_0);
       cout << "  -- all-1 goes -> " << node->CalculateDirection(point_1) << endl;
       for(uint32_t i = 0; i < node->NumChildren(); i++) {
           recur(&node->Child(i), point_0, point_1, depth+1);
       }
   }
}

void Manthan::train(const vector<vector<lbool>>& samples, uint32_t v) {
    cout << "variable: " << v << endl;
    assert(!samples.empty());
    assert(v < cnf.nVars());
    vec point_0 = vec(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) point_0[i] = 0;
    vec point_1 = vec(cnf.nVars());
    for(uint32_t i = 0; i < cnf.nVars(); i++) point_1[i] = 1;

    Mat<size_t> dataset;
    Row<size_t> labels;
    dataset.resize(cnf.nVars(), samples.size());
    cout << "Dataset size: " << dataset.n_rows << " x " << dataset.n_cols << endl;
    // TODO: we fill 0 for the value of v, this MAY come back in the tree,but likely not

    for(uint32_t i = 0; i < samples.size(); i++) {
        assert(samples[i].size() == cnf.nVars());
        for(uint32_t j = 0; j < cnf.nVars(); j++) {
            if (j == v) dataset(j, i) = 0;
            else dataset(j, i) = samples[i][j] == l_True ? 1 : 0;
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

   /* DecisionTree* node = r.children[0]; */
   /* while (node->NumChildren() != 0) */
   /*  node = &node->Child(0); */
   /*  r.serialize(cout); */
    recur(&r, point_0, point_1, 0);
    cout << "Done\n";
    /* exit(0); */
}


