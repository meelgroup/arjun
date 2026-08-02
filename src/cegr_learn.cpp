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

#include "cegr_learn.h"
#include "constants.h"
#include <iomanip>
#include <algorithm>
#include "time_mem.h"

using std::setprecision;
using std::fixed;
using std::setw;
using std::vector;
using std::string;
using std::endl;
using namespace ArjunInt;
using namespace ArjunNS;
using namespace CMSat;

void CegrLearn::full_train() {
    // Sampling
    verb_print(1, "[cegr] Starting training. Cegr Config. "
        << "do_filter_samples=" << mconf.filter_samples
        << ", samples=" << mconf.samples
        << ", minimumLeafSize=" << mconf.min_leaf_size
        << ", minGainSplit=" << setprecision(6) << mconf.min_gain_split << setprecision(2)
        << ", maximumDepth=" << mconf.max_depth
        << ", learn_input_only=" << mconf.learn_input_only);
    double samp_start_time = cpuTime();
    vector<sample> samples = get_cmsgen_samples(mconf.samples);
    m.stats.sampl_time = cpuTime() - samp_start_time;
    verb_print(1, COLYEL "[cegr] Got " << setw(8) << samples.size() << " samples."
        << " samp/var: " << setw(8) << setprecision(2) << std::fixed << m.stats.sampl_time/(double)m.to_define.size()
        << " T: " << setprecision(2) << std::fixed << m.stats.sampl_time);
    m.sort_all_samples(samples);

    // Training -- updates depenndency_mat
    const double train_start_time = cpuTime();
    for(const auto& v: m.y_order) {
        if (m.backward_defined.count(v)) continue;
        train(samples, v);
    }
    m.stats.train_time = cpuTime() - train_start_time;
    verb_print(1, COLYEL "[cegr] Training done."
            << " funs: " << setw(6) << m.to_define.size()
            << " fun/s: " << setw(6) << setprecision(2) << std::fixed << safe_div(m.to_define.size(), cpuTime() - train_start_time)
            << " T: " << setw(6) << setprecision(2) << std::fixed << m.stats.train_time
            << " mem: " << memUsedTotal()/(1024.0*1024.0) << " MB");
    assert(m.check_map_dependency_cycles());
}

double CegrLearn::train(const vector<sample>& orig_samples, const uint32_t v) {
    verb_print(2, "training variable: " << v+1);

    vector<uint32_t> used_vars(m.input.begin(), m.input.end());
    if (!mconf.learn_input_only) {
        for(const auto& y: m.y_order) {
            if (y == v) break;
            assert(m.dependency_mat[y][v] != 1);
            used_vars.push_back(y);
        }
    }
    /* assert(!orig_samples.empty()); */
    vector<const sample*> samples;
    if (mconf.filter_samples) samples = m.filter_samples(v, orig_samples);
    else {
        for(const auto& s: orig_samples)
            samples.push_back(&s);
    }
    assert(v < m.cnf.nVars());
    arma::Mat<uint8_t> dataset;
    arma::Row<size_t> labels;

    dataset.resize(used_vars.size(), samples.size());
    verb_print(2, "Dataset size: " << dataset.n_rows << " x " << dataset.n_cols);

    for(uint32_t i = 0; i < samples.size(); i++) {
        assert(samples[i]->size() == m.cnf.nVars());
        for(uint32_t k = 0; k < used_vars.size(); k++) {
            const uint32_t dep_v = used_vars[k];
            dataset(k, i) = m.lbool_to_bool((*samples[i])[dep_v]);
        }
    }
    labels.resize(samples.size());
    for(uint32_t i = 0; i < samples.size(); i++) labels[i] = m.lbool_to_bool((*samples[i])[v]);
    const auto num_ones = arma::accu(labels);
    verb_print(2, "Labels distribution for v " << setw(5) <<  v+1 << ": " << setw(6) << num_ones << " ones and "
            << setw(6) << (samples.size() - num_ones) << " zeros");
    double train_error;
    if (samples.empty()) {
        m.var_to_formula[v] = m.fh->constant_formula(!mconf.inv_guess);
        train_error = 0.0;
    } else {
        // Create the RandomForest object and train it on the training data.
        mlpack::DecisionTree<> r(dataset, labels, 2,
            mconf.min_leaf_size,  // minimumLeafSize: require 20+ samples per leaf (default 10)
            mconf.min_gain_split,     // minimumGainSplit: require k ratio gain to split
            mconf.max_depth);    // maximumDepth: max k levels deep (0 = unlimited)

        // Compute and print the training error.
        arma::Row<size_t> predictions;
        r.Classify(dataset, predictions);
        train_error = arma::accu(predictions != labels) * 100.0 / (double)labels.n_elem;
        /* r.serialize(cout, 1); */

        verb_print(2,"[DEBUG] About to call recur for v " << v+1 << " num children: " << r.NumChildren());
        assert(m.var_to_formula.count(v) == 0);
        uint32_t max_depth = 0;
        m.var_to_formula[v] = recur(&r, v, used_vars, 0, max_depth);
        SLOW_DEBUG_DO(verify_aig_matches_tree(&r, samples, v, used_vars, train_error));
        if (mconf.inv_guess)
            m.var_to_formula[v] = m.fh->neg(m.var_to_formula[v]);
        verb_print(1, "Training error: " << setprecision(2) << setw(6) << train_error << "%."
                << " depth: " << setw(6) << max_depth
                << " ones: " << setprecision(0) << fixed << setw(5) << (double)num_ones/samples.size()*100.0 << "%"
                << " on v: " << setprecision(2) << setw(4) << v+1);
    }

    // Forward dependency update
    for(uint32_t i = 0; i < m.cnf.nVars(); i++) {
        if (m.input.count(i)) continue;
        if (m.dependency_mat[i][v]) {
            for(uint32_t j = 0; j < m.cnf.nVars(); j++) {
                if (m.input.count(j)) continue;
                m.dependency_mat[i][j] |= m.dependency_mat[v][j];
            }
            SLOW_DEBUG_DO(assert(m.check_map_dependency_cycles()));
        }
    }
    verb_print(2, "Trained formula for y " << v+1 << ":" << endl << m.var_to_formula[v]);
    verb_print(2, "Done training variable: " << v+1);
    verb_print(2, "------------------------------");

    return train_error;
}

#ifdef SLOW_DEBUG
// Point-for-point equivalence of the AIG built by recur() against mlpack's own
// Classify(). Aggregate error rates can coincide while the two functions differ
// on individual points, so this compares every point instead. Checks the
// training points, then -- when the feature space is small enough -- every
// assignment in it, which covers tree regions no sample ever reaches.
void CegrLearn::verify_aig_matches_tree(mlpack::tree::DecisionTree<>* r,
        const vector<const sample*>& samples, const uint32_t v,
        const vector<uint32_t>& used_vars, const double train_error) {
    const auto& aig = m.var_to_formula.at(v).aig;
    const uint32_t n = used_vars.size();

    uint32_t max_var = m.cnf.nVars();
    for (const auto& [y, y_hat] : m.y_to_y_hat) max_var = std::max(max_var, y_hat + 1);
    const vector<aig_lit> defs(max_var, nullptr);

    // The AIG reads inputs by their own var, and to_define vars via y_hat, so
    // seed both slots from the same bit.
    vector<CMSat::lbool> vals(max_var, CMSat::l_Undef);
    arma::vec point(n);
    auto eval_both = [&](uint32_t& mismatches) {
        std::map<aig_lit, CMSat::lbool> cache;
        const CMSat::lbool got = ArjunNS::AIG::evaluate(vals, aig, defs, cache);
        assert(got != CMSat::l_Undef && "AIG leaf outside the feature set");
        const bool want = r->Classify(point) == 1;
        if (m.lbool_to_bool(got) != want) mismatches++;
    };
    auto set_bit = [&](const uint32_t k, const bool bit) {
        point[k] = bit ? 1.0 : 0.0;
        const uint32_t var = used_vars[k];
        vals[var] = bit ? CMSat::l_True : CMSat::l_False;
        if (m.to_define_full.count(var)) vals[m.y_to_y_hat.at(var)] = vals[var];
    };

    uint32_t mismatches = 0;
    uint32_t wrong = 0;
    for (const auto* s : samples) {
        for (uint32_t k = 0; k < n; k++) set_bit(k, m.lbool_to_bool((*s)[used_vars[k]]));
        eval_both(mismatches);

        std::map<aig_lit, CMSat::lbool> cache;
        if (ArjunNS::AIG::evaluate(vals, aig, defs, cache) != (*s)[v]) wrong++;
    }
    if (mismatches != 0) {
        std::cout << "ERROR: AIG disagrees with the decision tree on " << mismatches
            << " / " << samples.size() << " training points, v: " << v+1 << endl;
        assert(false && "recur() built an AIG that is not the trained tree");
    }

    // 2^n over the whole feature space; 20 keeps the worst case ~1M evals.
    if (n <= 20) {
        const uint64_t total = 1ULL << n;
        for (uint64_t mask = 0; mask < total; mask++) {
            for (uint32_t k = 0; k < n; k++) set_bit(k, (mask >> k) & 1ULL);
            eval_both(mismatches);
        }
        if (mismatches != 0) {
            std::cout << "ERROR: AIG disagrees with the decision tree on " << mismatches
                << " / " << total << " exhaustive points, v: " << v+1 << endl;
            assert(false && "recur() built an AIG that is not the trained tree");
        }
    }

    const double aig_error = wrong * 100.0 / (double)samples.size();
    verb_print(1, "[verify] AIG matches tree exactly."
            << " AIG err: " << setprecision(4) << aig_error
            << "% ML err: " << train_error << "% on v: " << v+1);
    assert(std::abs(aig_error - train_error) <= 0.01);
}
#endif

FHolder<MetaSolver>::Formula CegrLearn::recur(mlpack::tree::DecisionTree<>* node,
        const uint32_t learned_v, const vector<uint32_t>& used_vars, uint32_t depth, uint32_t& max_depth) {
    max_depth = std::max(max_depth, depth);
    /* for(uint32_t i = 0; i < depth; i++) cout << " "; */
    if (node->NumChildren() == 0) {
        const bool val = node->ClassProbabilities()[1] > node->ClassProbabilities()[0];
        /* cout << "Leaf: "; */
        /* for(uint32_t i = 0; i < node->NumClasses(); i++) { */
        /*     cout << "class "<< i << " prob: " << node->ClassProbabilities()[i] << " --- "; */
        /* } */
        /* cout << endl; */
        return m.fh->constant_formula(val);
    } else {
        uint32_t v = node->SplitDimension();
        assert(v < used_vars.size());
        v = used_vars[v];
        /* cout << "(learning " << learned_v+1<< ") Node. v: " << v+1 << std::flush; */
        if (m.to_define_full.count(v)) {
            // v does not depend on learned_v!
            assert(m.dependency_mat[v][learned_v] == 0);
            for(uint32_t i = 0; i < m.cnf.nVars(); i++) {
                if (m.dependency_mat[v][i] == 1) {
                    if (m.input.count(i)) continue;
                    // nothing that v depends on can depend on learned_v
                    assert(m.dependency_mat[i][learned_v] == 0);
                }
            }
            m.set_depends_on(learned_v, v);
            v = m.y_to_y_hat.at(v);
        } else {
            // it's input, so no need to update dependency matrix
            assert(m.input.count(v) && "If not to_define_full, must be input");
        }

        /* cout << "  -- all-0 goes -> " << node->CalculateDirection(point_0); */
        /* cout << "  -- all-1 goes -> " << node->CalculateDirection(point_1) << endl; */
        assert(node->NumChildren() == 2);
        auto form_0 = recur(&node->Child(0), learned_v, used_vars, depth+1, max_depth);
        auto form_1 = recur(&node->Child(1), learned_v, used_vars, depth+1, max_depth);
        bool val_going_right = node->CalculateDirection(point_1);
        return m.fh->compose_ite(form_0, form_1, Lit(v, val_going_right), m.helpers);
    }
    assert(false);
}

vector<sample> CegrLearn::get_cmsgen_samples(uint32_t num) {
    // Sampling costs one SAT solve each; halve it on large to-define sets.
    verb_print(1, "[cegr] Getting " << num << " CMSGen samples...");

    const double my_time = cpuTime();
    SATSolver solver_samp;
    solver_samp.set_seed(m.eff_seed());
    m.inject_cnf(solver_samp);
    solver_samp.set_up_for_sample_counter(mconf.sampler_fixed_conflicts);

    vector<sample> samples;
    for (uint32_t i = 0; i < num; i++) {
        auto ret = solver_samp.solve();
        assert(ret == l_True);
        assert(solver_samp.get_model().size() == m.cnf.nVars());
        samples.push_back(solver_samp.get_model());
    }
    verb_print(1, "[cegr] CMSGen got " << samples.size() << " samples."
            << " T: " << setprecision(2) << std::fixed << (cpuTime() - my_time));
    return samples;
}

