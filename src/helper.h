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
#include <set>
#include <fstream>
#include <string>
#include <cryptominisat5/dimacsparser.h>
#include <cryptominisat5/solvertypesmini.h>
#ifdef USE_ZLIB
#include <zlib.h>
#endif

#include "arjun.h"

using std::vector;
using std::set;
using namespace ArjunNS;
using namespace CMSat;
using std::cerr;
using std::cout;
using std::endl;

inline double stats_line_percent(double num, double total) {
    if (total == 0) return 0;
    else return num/total*100.0;
}

inline void write_synth(const ArjunNS::SimplifiedCNF& simpcnf, const std::string& fname) {
    uint32_t num_cls = simpcnf.clauses.size()+simpcnf.red_clauses.size();
    std::ofstream outf;
    outf.open(fname.c_str(), std::ios::out);
    outf << "p cnf " << simpcnf.nvars << " " << num_cls << endl;

    //Add projection
    /* outf << "a "; */
    outf << "c p show ";
    auto sampl = simpcnf.sampl_vars;
    std::sort(sampl.begin(), sampl.end());
    for(const auto& v: sampl) {
        assert(v < simpcnf.nvars);
        outf << v+1  << " ";
    }
    outf << "0\n";
    cout << "c o forall vars: " << simpcnf.sampl_vars.size() << endl;
    set<uint32_t> e;
    for(uint32_t i = 0; i < simpcnf.nvars; i++) e.insert(i);
    for(auto v: simpcnf.sampl_vars) e.erase(v);
    /* outf << "e "; */
    outf << "c e ";
    for(const auto& v: e) outf << v+1  << " ";
    outf << "0\n";
    cout << "c o exist vars: " << e.size() << endl;

    for(const auto& cl: simpcnf.clauses) outf << cl << " 0\n";
    for(const auto& cl: simpcnf.red_clauses) outf << cl << " 0\n";
}

template<typename T> void read_in_a_file(const std::string& filename,
        T* holder, bool& all_indep, unique_ptr<CMSat::FieldGen>& fg) {
    #ifndef USE_ZLIB
    FILE * in = fopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<FILE*, FN>, T> parser(holder, nullptr, 0, fg);
    #else
    gzFile in = gzopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<gzFile, GZ>, T> parser(holder, nullptr, 0, fg);
    #endif

    if (in == nullptr) {
        std::cerr << "ERROR! Could not open file '" << filename
            << "' for reading: " << strerror(errno) << endl;
        std::exit(-1);
    }

    if (!parser.parse_DIMACS(in, true)) exit(-1);
    if (!holder->get_sampl_vars_set()) {
        holder->start_with_clean_sampl_vars();
        all_indep = true;
    }
    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}
