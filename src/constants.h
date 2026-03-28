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

#pragma once

#include <cryptominisat5/solvertypesmini.h>
#include <iostream>
#include <set>
#include <string>
#include <vector>
#include <algorithm>
#include <cstdint>
#include <iomanip>
#include <sstream>
#include <fstream>

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

/* #define SLOW_DEBUG */
/* #define VERBOSE_DEBUG */

#ifdef VERBOSE_DEBUG
constexpr int verbose_debug_enabled = 10;
#else
constexpr int verbose_debug_enabled = 0;
#endif

#ifdef SLOW_DEBUG
#define SLOW_DEBUG_DO(x) do { x; } while (0)
constexpr int slow_debug_enabled = 1;
#else
#define SLOW_DEBUG_DO(x) do { } while (0)
constexpr int slow_debug_enabled = 0;
#endif

template<typename LIT, typename T, typename T2>
inline void dump_cnf(T2& s, const std::string& name, const T& sampl_set) {
    std::vector<std::vector<LIT>> cls;
    std::vector<LIT> cl;
    s.start_getting_constraints(false);
    bool is_xor, rhs;
    while(s.get_next_constraint(cl, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        cls.push_back(cl);
    }
    s.end_getting_constraints();

    std::ofstream f(name);
    f << "p cnf " << s.nVars() << " " << cls.size() << std::endl;

    f << "c p show ";
    for(const auto& l: sampl_set) f << l << " ";
    f << " 0" << std::endl;

    for(const auto& c: cls) f << c << " 0" << std::endl;
    f.close();
    std::cout << "c o DEBUG dumped CNF to " << name << " with " << cls.size() << " clauses and "
        << s.nVars() << " vars" << std::endl;
}

inline double safe_div(double a, double b) noexcept {
    if (b == 0) {
        return 0;
    } else {
        return a/b;
    }
}

// lit to picolit
[[nodiscard]] inline int lit_to_pl(const CMSat::Lit l) noexcept {
    int picolit = (l.var()+1) * (l.sign() ? -1 : 1);
    return picolit;
}

[[nodiscard]] inline CMSat::Lit pl_to_lit(const int l) noexcept {
    uint32_t v = abs(l)-1;
    return CMSat::Lit(v, l < 0);
}

[[nodiscard]] inline std::vector<CMSat::Lit> pl_to_lit_cl(const std::vector<int>& cl) {
    std::vector<CMSat::Lit> ret;
    ret.reserve(cl.size());
    for(const auto& l: cl) ret.push_back(pl_to_lit(l));
    return ret;
}

#define verb_print(a, x) \
    do { \
        if (conf.verb >= a) {\
            std::cout << "c o " << COLDEF << x << COLDEF << std::endl;}\
    } while (0)


#define verb_print2(a, x) \
    do { \
        if (arjdata->conf.verb >= a) {\
            std::cout << "c o " << COLDEF << x << COLDEF << std::endl;}\
    } while (0)

#ifdef VERBOSE_DEBUG
#define VERBOSE_DEBUG_DO(x) do { x; } while (0)
#else
#define VERBOSE_DEBUG_DO(x) do { } while (0)
#endif

#ifdef VERBOSE_DEBUG
#define debug_print(x) std::cout << COLDEF << x << COLDEF << std::endl
#define debug_print_noendl(x) std::cout << x
#else
#define debug_print(x) do {} while(0)
#define debug_print_noendl(x) do {} while (0)
#endif
#define debug_print_tmp(x) std::cout << COLDEF << x << COLDEF << std::endl

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

template<class T>
struct IncidenceSorter ///DESCENDING ORDER (i.e. most likely independent at the top)
{
    IncidenceSorter(const std::vector<T>& _inc) : inc(_inc) {}
    bool operator()(const T a, const T b) const noexcept {
        if (inc[a] != inc[b]) {
            return inc[a] > inc[b];
        }
        return a < b;
    }

    const std::vector<T>& inc;
};

template<typename T, typename  T2> void sort_unknown(T& unknown, std::vector<T2>& incidence)
{
    assert(!incidence.empty() && "Incidence is filled at fill_solver time");
    std::sort(unknown.begin(), unknown.end(), IncidenceSorter<uint32_t>(incidence));
}

[[nodiscard]] inline std::string print_value_kilo_mega(const int64_t value, bool setw = true)
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

[[nodiscard]] inline double stats_line_percent(double num, double total) noexcept
{
    if (total == 0) {
        return 0;
    } else {
        return num/total*100.0;
    }
}

// Create indicator variables encoding "var == var+orig_num_vars" when the
// indicator is TRUE, for every variable NOT in `except`.  Used by both
// Minimize and Extend to set up the duplicated-formula reasoning.
template<typename Solver>
inline void add_all_indics_except(
    Solver& solver,
    uint32_t orig_num_vars,
    const std::set<uint32_t>& except,
    std::vector<uint32_t>& var_to_indic,
    std::vector<uint32_t>& indic_to_var,
    std::vector<CMSat::Lit>& dont_elim,
    std::vector<char>& seen,
    [[maybe_unused]] int verb)
{
    assert(dont_elim.empty());
    assert(var_to_indic.empty());
    assert(indic_to_var.empty());

    var_to_indic.resize(orig_num_vars*2, CMSat::var_Undef);

    std::vector<CMSat::Lit> tmp;
    for(uint32_t var = 0; var < orig_num_vars; var++) {
        if (except.count(var)) continue;

        solver.new_var();
        uint32_t this_indic = solver.nVars()-1;
        var_to_indic[var] = this_indic;
        var_to_indic[var+orig_num_vars] = this_indic;
        dont_elim.push_back(CMSat::Lit(this_indic, false));
        indic_to_var.resize(this_indic+1, CMSat::var_Undef);
        indic_to_var[this_indic] = var;

        // var == (var+orig) when indic is TRUE
        tmp.clear();
        tmp.push_back(CMSat::Lit(var,               false));
        tmp.push_back(CMSat::Lit(var+orig_num_vars, true));
        tmp.push_back(CMSat::Lit(this_indic,        true));
        solver.add_clause(tmp);

        tmp.clear();
        tmp.push_back(CMSat::Lit(var,               true));
        tmp.push_back(CMSat::Lit(var+orig_num_vars, false));
        tmp.push_back(CMSat::Lit(this_indic,        true));
        solver.add_clause(tmp);
    }
    seen.clear();
    seen.resize(indic_to_var.size()*2, 0);
}
