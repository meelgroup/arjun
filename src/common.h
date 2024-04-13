/*
 Arjun

 Copyright (c) 2019, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#pragma once

// verb_print
#define COLRED "\033[31m"
#define COLYEL2 "\033[35m"
#define COLYEL "\033[33m"
#define COLCYN "\033[36m"
#define COLWHT "\033[97m"
#define COLORG "\033[43m"
#define COLBLBACK  "\033[44m"
#define COLORGBG "\033[100m"
#define COLREDBG "\033[41m"
//default
#define COLDEF "\033[0m"

#define verb_print(a, x) \
    do { \
        if (conf.verb >= a) {std::cout << COLDEF << "c " << x << COLDEF << std::endl;}\
    } while (0)

#if defined(_MSC_VER)
#include "cms_windows_includes.h"
#define release_assert(a) \
    do { \
    __pragma(warning(push)) \
    __pragma(warning(disable:4127)) \
        if (!(a)) {\
    __pragma(warning(pop)) \
            fprintf(stderr, "*** ASSERTION FAILURE in %s() [%s:%d]: %s\n", \
            __FUNCTION__, __FILE__, __LINE__, #a); \
            abort(); \
        } \
    } while (0)
#else
#define release_assert(a) \
    do { \
        if (!(a)) {\
            fprintf(stderr, "*** ASSERTION FAILURE in %s() [%s:%d]: %s\n", \
            __FUNCTION__, __FILE__, __LINE__, #a); \
            abort(); \
        } \
    } while (0)
#endif

#include "arjun.h"
#include <vector>
#include <iostream>
#include <iomanip>
#include <random>
#include <algorithm>
#include <map>
#include <set>
#include <vector>
#include <sstream>
#include <string>
#ifdef CMS_LOCAL_BUILD
#include "cryptominisat.h"
#else
#include <cryptominisat5/cryptominisat.h>
#endif

#include "time_mem.h"
#include "config.h"

using namespace CMSat;
using std::cout;
using std::endl;
using std::map;
using std::set;
using std::string;
using std::vector;

namespace ArjunInt {

struct Common
{
    Common() {
        set_up_solver();
    }
    ~Common() { delete solver; }

    Config conf;
    CMSat::SATSolver* solver = nullptr;
    bool already_duplicated = false;
    vector<uint32_t> sampling_set;
    vector<uint32_t> orig_sampling_vars;
    vector<uint32_t> empty_sampling_vars;
    vector<uint32_t> set_sampling_vars;

    vector<char> seen;
    uint32_t orig_num_vars = std::numeric_limits<uint32_t>::max();
    bool definitely_satisfiable = false;
    enum ModeType {one_mode, many_mode};

    //assert indic[var] to TRUE to force var==var+orig_num_vars
    vector<uint32_t> var_to_indic; //maps an ORIG VAR to an INDICATOR VAR
    vector<uint32_t> indic_to_var; //maps an INDICATOR VAR to ORIG VAR

    //Incidence as counted by clauses it's appeared together with other variables
    vector<uint32_t> incidence;
    //Incidence as counted by probing
    vector<uint32_t> incidence_probing;

    vector<Lit> dont_elim;

    // cnf as we parsed it in (no simplification whatsoever)
    ArjunNS::SimplifiedCNF orig_cnf;

    void init();
    void update_sampling_set(
        const vector<uint32_t>& unknown,
        const vector<char>& unknown_set,
        const vector<uint32_t>& indep
    );
    bool preproc_and_duplicate();
    void add_fixed_clauses();
    void add_all_indics();
    void print_orig_sampling_set();
    void start_with_clean_sampling_set();
    void duplicate_problem();
    void get_incidence();
    void set_up_solver();
    ArjunNS::SimplifiedCNF get_init_cnf();
    std::mt19937 random_source = std::mt19937(0);

    //simp
    vector<uint32_t> toClear;
    bool simplify();
    bool remove_definable_by_gates();
    void remove_definable_by_irreg_gates();
    void remove_zero_assigned_literals(bool print = true);
    void remove_eq_literals(bool print = true);
    void get_empty_occs();
    bool probe_all();
    void empty_out_indep_set_if_unsat();
    bool simplify_bve_only();
    bool run_gauss_jordan();
    void check_no_duplicate_in_sampling_set();
    void order_sampl_set_for_simp();

    //backward
    void fill_assumptions_backward(
        vector<Lit>& assumptions,
        vector<uint32_t>& unknown,
        const vector<char>& unknown_set,
        const vector<uint32_t>& indep);
    void backward_round();
    void order_by_file(const string& fname, vector<uint32_t>& unknown);
    void print_sorted_unknown(const vector<uint32_t>& unknown) const;

    // extend
    template<class T>
    void fill_assumptions_extend(
        vector<Lit>& assumptions,
        const T& indep);
    void extend_round();

    // Unsat define
    void unsat_define(const vector<uint32_t>& orig_sampl_vars);
    void generate_picosat(const vector<Lit>& assumptions , uint32_t test_var);

    //Sorting
    template<class T> void sort_unknown(T& unknown);

};

inline string print_value_kilo_mega(const int64_t value, bool setw = true)
{
    std::stringstream ss;
    if (value > 20*1000LL*1000LL) {
        if (setw) {
            ss << std::setw(4);
        }
        ss << value/(1000LL*1000LL) << "M";
    } else if (value > 20LL*1000LL) {
        if (setw) {
            ss << std::setw(4);
        }
        ss << value/1000LL << "K";
    } else {
        if (setw) {
            ss << std::setw(5);
        }
        ss << value;
    }

    return ss.str();
}

inline double stats_line_percent(double num, double total)
{
    if (total == 0) {
        return 0;
    } else {
        return num/total*100.0;
    }
}

template<class T>
struct IncidenceSorter ///DESCENDING ORDER (i.e. most likely independent at the top)
{
    IncidenceSorter(const vector<T>& _inc) : inc(_inc) {}
    bool operator()(const T a, const T b) {
        if (inc[a] != inc[b]) {
            return inc[a] > inc[b];
        }
        return a < b;
    }

    const vector<T>& inc;
};

template<class T>
struct IncidenceSorter2
{
    IncidenceSorter2(const vector<T>& _inc, const vector<T>& _inc2) : inc(_inc), inc2(_inc2) {}
    bool operator()(const T a, const T b) {
        if (inc[a] != inc[b]) {
            return inc[a] > inc[b];
        }
        if (inc2[a] != inc2[b]) {
            return inc2[a] > inc2[b];
        }
        return a < b;
    }

    const vector<T>& inc;
    const vector<T>& inc2;
};

template<class T> void Common::sort_unknown(T& unknown)
{
    if (conf.unknown_sort == 1) {
        std::sort(unknown.begin(), unknown.end(), IncidenceSorter<uint32_t>(incidence));
    } else if (conf.unknown_sort == 2) {
        std::sort(unknown.begin(), unknown.end(), IncidenceSorter2<uint32_t>(incidence, incidence_probing));
    } else if (conf.unknown_sort == 3) {
        std::sort(unknown.begin(), unknown.end(), IncidenceSorter<uint32_t>(incidence_probing));
    } else if (conf.unknown_sort == 6) {
        std::shuffle(unknown.begin(), unknown.end(), random_source);
    } else {
        cout << "ERROR: wrong sorting mechanism given" << endl;
        exit(-1);
    }
}

}
