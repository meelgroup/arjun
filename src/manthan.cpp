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
#include <vector>
#include <xgboost/c_api.h>

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

vector<vector<lbool>> Manthan::get_samples(const SimplifiedCNF& cnf, uint32_t num) {
    vector<vector<lbool>> solutions;
    sample_solver.set_up_for_sample_counter(100);
    for(const auto& c: cnf.clauses) sample_solver.add_clause(c);
    for(const auto& c: cnf.red_clauses) sample_solver.add_red_clause(c);

    for (uint32_t i = 0; i < num; i++) {
        sample_solver.solve();
        solutions.push_back(sample_solver.get_model());
    }
    return solutions;
}

void Manthan::do_manthan(SimplifiedCNF& cnf) {
    // Grand master plan
    // 1. Get 10k samples
    // 2. Run boost to get a tree one-by-one and thereby generate an order
    // 3. Find counterexample
    // 4. Make counterexample as close to being good as possible. Originally maxsat, but we can try greedy
    // 5a -- we could fix solutions one-by-one but that's slow
    // 5b -- instead, get the conflict from the assumptions, which is a kind of poor "core",
    //       and do the "stupid" fix on that.
    //

    vector<vector<lbool>> solutions = get_samples(cnf, 10e3);
    BoosterHandle booster = nullptr;
    safe_xgb(XGBoosterSetParam(booster, "nthread", "1"))
    DMatrixHandle data;
    const int data1[] = { 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 };
    int eval_dmats_size = 10;

    // We assume that training and test data have been loaded into 'train' and 'test'
    DMatrixHandle eval_dmats[eval_dmats_size] = {train, test};
    /* safe_xgboost(XGBoosterCreate(eval_dmats, eval_dmats_size, &booster)); */
    float* ret_data;
    safe_xgboost(XGDMatrixCreateFromMat(ret_data, num_rows, num_cols, missing_val, &dmat));
    free(ret_data);

    int num_of_iterations = 20;
    const char* eval_names[eval_dmats_size] = {"train", "test"};
    const char* eval_result = NULL;


    for (int i = 0; i < num_of_iterations; ++i) {
      // Update the model performance for each iteration
      safe_xgboost(XGBoosterUpdateOneIter(booster, i, train));
    }


  // Give the statistics for the learner for training & testing dataset
  // in terms of error after each iteration
  safe_xgboost(XGBoosterEvalOneIter(booster, i, eval_dmats, eval_names, eval_dmats_size, &eval_result));

  /* printf("%s\n", eval_result); */


    XGBoosterFree(booster);

}
