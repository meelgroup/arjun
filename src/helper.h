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

inline void write_origcnf(Arjun* arjun, vector<uint32_t>& indep_vars,
        const std::string& elimtofile, const uint32_t orig_cnf_must_mult_exp2)
{
    uint32_t num_cls = 0;
    const auto& cnf = arjun->get_orig_cnf();
    for(const auto& l: cnf) if (l == lit_Undef) num_cls++;
    std::ofstream outf;
    outf.open(elimtofile.c_str(), std::ios::out);
    outf << "p cnf " << arjun->get_orig_num_vars() << " " << num_cls << endl;

    //Add projection
    outf << "c p show ";
    std::sort(indep_vars.begin(), indep_vars.end());
    for(const auto& v: indep_vars) {
        assert(v < arjun->get_orig_num_vars());
        outf << v+1  << " ";
    }
    outf << "0\n";

    for(const auto& l: cnf) {
        if (l == lit_Undef) outf << "0\n";
        else outf << l << " ";
    }
    outf << "c MUST MULTIPLY BY 2**" << orig_cnf_must_mult_exp2 << endl;
}

inline void write_simpcnf(const ArjunNS::SimplifiedCNF& simpcnf,
        const std::string& fname, const uint32_t orig_cnf_must_mult_exp2,
        bool red = true)
{
    uint32_t num_cls = simpcnf.cnf.size();
    std::ofstream outf;
    outf.open(fname.c_str(), std::ios::out);
    outf << "p cnf " << simpcnf.nvars << " " << num_cls << endl;

    //Add projection
    outf << "c p show ";
    auto sampl = simpcnf.sampling_vars;
    std::sort(sampl.begin(), sampl.end());
    for(const auto& v: sampl) {
        assert(v < simpcnf.nvars);
        outf << v+1  << " ";
    }
    outf << "0\n";

    for(const auto& cl: simpcnf.cnf) outf << cl << " 0\n";
    if (red) for(const auto& cl: simpcnf.red_cnf) outf << "c red " << cl << " 0\n";
    outf << "c MUST MULTIPLY BY 2**" << simpcnf.empty_occs+orig_cnf_must_mult_exp2 << endl;
}

inline void readInAFile(const std::string& filename,
        Arjun* arjun,
        uint32_t& orig_sampling_set_size,
        uint32_t& orig_cnf_must_mult_exp2,
        const bool recompute_sampling_set)
{
    assert(orig_cnf_must_mult_exp2 == 0);
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

    if (!parser.parse_DIMACS(in, true)) {
        exit(-1);
    }

    if (!parser.sampling_vars_found || recompute_sampling_set) {
        orig_sampling_set_size = arjun->start_with_clean_sampling_set();
    } else {
        orig_sampling_set_size = arjun->set_starting_sampling_set(parser.sampling_vars);
    }
    orig_cnf_must_mult_exp2 = parser.must_mult_exp2;

    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}
