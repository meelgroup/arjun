/*
 Arjun

 Copyright (c) 2019-2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#include <cstdint>
#include <iostream>
#include <vector>
#include <fstream>
#include <string>
#include <cryptominisat5/dimacsparser.h>
#include <cryptominisat5/solvertypesmini.h>
#ifdef USE_ZLIB
#include <zlib.h>
#endif

#include "arjun.h"

using std::vector;
using namespace ArjunNS;
using namespace CMSat;
using std::cerr;
using std::cout;
using std::endl;

inline double stats_line_percent(double num, double total)
{
    if (total == 0) {
        return 0;
    } else {
        return num/total*100.0;
    }
}

inline void write_simpcnf(const ArjunNS::SimplifiedCNF& simpcnf,
        const std::string& fname, bool red = true)
{
    uint32_t num_cls = simpcnf.cnf.size();
    std::ofstream outf;
    outf.open(fname.c_str(), std::ios::out);
    outf << "p cnf " << simpcnf.nvars << " " << num_cls << endl;

    //Add projection
    outf << "c p show ";
    auto sampl = simpcnf.sampl_vars;
    std::sort(sampl.begin(), sampl.end());
    for(const auto& v: sampl) {
        assert(v < simpcnf.nvars);
        outf << v+1  << " ";
    }
    outf << "0\n";
    outf << "c p optshow ";
    sampl = simpcnf.opt_sampl_vars;
    std::sort(sampl.begin(), sampl.end());
    for(const auto& v: sampl) {
        assert(v < simpcnf.nvars);
        outf << v+1  << " ";
    }
    outf << "0\n";

    for(const auto& cl: simpcnf.cnf) outf << cl << " 0\n";
    if (red) for(const auto& cl: simpcnf.red_cnf) outf << "c red " << cl << " 0\n";

#ifdef WEIGHTED
    if (simpcnf.weighted) {
        for(const auto& it: simpcnf.weights) {
            outf << "c p weight " << it.first << " " << it.second << endl;
        }
    }
#endif
    mpz_class w = simpcnf.multiplier_weight;
    outf << "c MUST MULTIPLY BY " << w << endl;
}

inline void read_in_a_file(const std::string& filename,
        Arjun* arjun,
        const bool recompute_sampling_set,
        bool& indep_support_given)
{
    #ifndef USE_ZLIB
    FILE * in = fopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<FILE*, FN>, ArjunNS::Arjun> parser(arjun, nullptr, 0);
    #else
    gzFile in = gzopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<gzFile, GZ>, ArjunNS::Arjun> parser(arjun, nullptr, 0);
    #endif

    if (in == nullptr) {
        std::cerr
        << "ERROR! Could not open file '"
        << filename
        << "' for reading: " << strerror(errno) << endl;

        std::exit(-1);
    }

    if (!parser.parse_DIMACS(in, true)) exit(-1);
    if (!arjun->get_sampl_vars_set() || recompute_sampling_set) {
        arjun->start_with_clean_sampling_set();
        indep_support_given = false;
    } else {
        indep_support_given = true;
    }
    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}
