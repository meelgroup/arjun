/******************************************
Copyright (c) 2019, Shaowei Cai

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
***********************************************/

#pragma once

#include <cstdint>
#include <cstdlib>
#include <ostream>
#include <vector>
#include "ccnr_mersenne.hpp"

using std::vector;
using std::abs;

namespace CCNR {

struct lit {
    int var_num;             //variable num, begin with 1
    uint32_t cl_num : 31;         //clause ID it belongs to, begin with 0
    uint32_t sense : 1;           //is 1 for true literals, 0 for false literals.
    lit(int the_lit, int the_clause) {
        var_num = std::abs(the_lit);
        cl_num = the_clause;
        sense = the_lit > 0 ? 1 : 0;
    }

    /* struct lit &operator^=(const struct lit &l) { */
    /*     sense ^= l.sense; */
    /*     cl_num ^= l.cl_num; */
    /*     var_num ^= l.var_num; */
    /*     return *this; */
    /* } */

    void reset(void) {
        sense = 0;
        cl_num = 0;
        var_num = 0;
    }

    bool operator==(const struct lit &l) const {
        return sense == l.sense && cl_num == l.cl_num && var_num == l.var_num;
    }

    bool operator!=(const struct lit &l) const {
        return !(*this == l);
    }
};

struct variable {
    vector<lit> lits;
    vector<int> neighbor_vars;
    long long score;
    long long last_flip_step;
    int unsat_appear; //how many unsat clauses it appears in
};

struct clause {
    vector<lit> lits;
    int sat_count; //no. of satisfied literals
    int touched_cnt; // no. of literals that are touched but not satisfied
    int sat_var; // the variable that makes the clause satisfied
    long long weight;
};

inline std::ostream& operator<<(std::ostream &os, const lit &l) {
    os << (l.sense ? "" : "-") << l.var_num;
    return os;
}

inline std::ostream& operator<<(std::ostream &os, const clause &cl) {
  for(const auto &l: cl.lits) {
    os << l << " ";
  }
  os << "0";
  return os;
}

class LSSolver {
 public:
    LSSolver();
    bool local_search(
        long long int _mems_limit = 100*1000*1000
        , const char* prefix = "c "
    );
    void print_solution(bool need_verify = 0);
    void set_verbosity(uint32_t _verb) { verb = _verb; }

    //formula
    vector<variable> vars;
    vector<clause> cls;
    int num_vars;
    int num_cls;

    //data structure used
    vector<int> unsat_cls; // list of unsatisfied clauses
    vector<int> idx_in_unsat_cls; // idx_in_unsat_cls[cl_id] tells where cl_id is in unsat_vars
                                  //
    vector<int> touched_cls; // cls that have been touched but not satisfied
    vector<int> idx_in_touched_cls; // idx_in_touched_cls[cl_id] tells where cl_id is in touched_cls
                             //
    vector<int> unsat_vars; // clauses are UNSAT due to these vars
    vector<int> idx_in_unsat_vars;
    vector<int> indep_map; // always num_vars+1 size, contains 0/1 if it's indep or not
    vector<uint8_t> sol; //solution information. 0 = false, 1 = true, 3 = unset

    //functions for building data structure
    bool make_space();
    void build_neighborhood();
    int get_cost() { return unsat_cls.size(); }

  private:
    void check_invariants() const;
    void check_unsat_cls() const;
    Mersenne random_gen;

    // Config
    long long max_steps;
    int64_t max_tries;
    uint32_t verb = 0;
    float swt_p = 0.3;
    float swt_q = 0.7;
    int swt_thresh = 50;

    // internal stats
    int64_t step;
    int64_t mems = 0;
    int avg_cl_weight;
    long long delta_tot_cl_weight;

    //main functions
    void initialize();
    void initialize_variable_datas();
    int pick_var();
    int unset_a_clause();
    void flip(int flipv);
    void unset(int v);
    void update_clause_weights();
    void smooth_clause_weights();

    //funcitons for basic operations
    void sat_a_clause(int the_clause);
    void unsat_a_clause(int the_clause);
    void untouch_a_clause(int cl_id);
    void touch_a_clause(int cl_id);

    // debug
    void print_cl(int cl_id) const;
    void check_clause(int cid) const;
};

} // namespace CCNR
