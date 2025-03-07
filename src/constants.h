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
#include <cmath>
#include <iostream>
#include <string>
#include <vector>
#include <algorithm>
#include <cstdint>
#include <iomanip>
#include <sstream>
using std::cout;
using std::endl;
using std::cerr;
using std::string;
using std::vector;
using std::setw;

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

#ifdef SLOW_DEBUG
#define SLOW_DEBUG_DO(x) do { x; } while (0)
#else
#define SLOW_DEBUG_DO(x) do { } while (0)
#endif

// lit to picolit
inline int lit_to_pl(const CMSat::Lit l) {
    int picolit = (l.var()+1) * (l.sign() ? -1 : 1);
    return picolit;
}
inline CMSat::Lit pl_to_lit(const int l) {
    uint32_t v = abs(l)-1;
    return CMSat::Lit(v, l < 0);
}
inline vector<CMSat::Lit> pl_to_lit_cl(const vector<int>& cl) {
    vector<CMSat::Lit> ret;
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
    IncidenceSorter(const vector<T>& _inc) : inc(_inc) {}
    bool operator()(const T a, const T b) {
        if (inc[a] != inc[b]) {
            return inc[a] > inc[b];
        }
        return a < b;
    }

    const vector<T>& inc;
};

template<class T> void sort_unknown(T& unknown, vector<uint32_t>& incidence)
{
    std::sort(unknown.begin(), unknown.end(), IncidenceSorter<uint32_t>(incidence));
}

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
