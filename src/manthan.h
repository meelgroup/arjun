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

#include "arjun.h"
#include "config.h"
#include "cryptominisat5/solvertypesmini.h"

#include <cstdint>
#include <vector>
#include <set>



#define MLPACK_PRINT_INFO
#define MLPACK_PRINT_WARN
#include <mlpack.hpp>

using namespace arma;
using namespace mlpack;
using namespace mlpack::tree;
using namespace CMSat;

using std::vector;
using std::set;
using std::map;

using namespace ArjunInt;
using namespace ArjunNS;

struct Formula {
    vector<vector<Lit>> clauses;
    set<uint32_t> inter_vs;
    Lit out = lit_Error; // member of inter_vs
};

inline std::ostream& operator<<(std::ostream& os, const Formula& f) {
    os << " ==== Formula: " << f.out << " ==== " << endl;
    for (const auto& cl : f.clauses) {
        for (const auto& l : cl) {
            os << std::setw(6) << l;
        }
        cout << " 0" << endl;
    }
    os << "Intermediates: ";
    for (const auto& v : f.inter_vs) {
        os << v+1 << " ";
    }
    os << endl;
    os << "Output: " << f.out << endl;
    return os;
}

class Manthan {
    public:
        Manthan(Config& _conf) : conf(_conf) {}
        SimplifiedCNF do_manthan(const SimplifiedCNF& cnf);
        SimplifiedCNF cnf;

    private:
        vec point_0;
        vec point_1;
        Lit my_true_lit;


        map<uint32_t, Formula> funcs; // output -> formula
        // when indic is TRUE, they are EQUIVALENT
        // when indic is FALSE, they are NOT EQUIVALENT <<-- only this injected
        map<uint32_t, uint32_t> out_to_indic;
        map<uint32_t, uint32_t> indic_to_out;

        const Config& conf;
        SATSolver solver;
        set<uint32_t> input;
        set<uint32_t> output;
        Formula recur(DecisionTree<>* node, const uint32_t learned_v, uint32_t depth = 0);
        vector<uint32_t> incidence;
        void get_incidence();
        Formula compose_ite(const Formula& a, const Formula& b, Lit branch);
        Formula constant_formula(int val);
        void get_counterexample();

        void add_sample_clauses(SimplifiedCNF& cnf);
        vector<vector<lbool>> get_samples(uint32_t num_samples);
        void train(const vector<vector<lbool>>& samples, uint32_t v);
        vector<vector<char>> dependency_mat;
};
