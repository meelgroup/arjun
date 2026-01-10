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

#include <iostream>
#include <vector>
#include <set>
#include <string>
#include <cryptominisat5/dimacsparser.h>
#include <cryptominisat5/solvertypesmini.h>
#ifdef USE_ZLIB
#include <zlib.h>
#endif

using std::vector;
using std::set;
using namespace CMSat;
using std::cerr;
using std::cout;
using std::endl;

inline double stats_line_percent(double num, double total) {
    if (total == 0) return 0;
    else return num/total*100.0;
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
        std::exit(EXIT_FAILURE);
    }

    if (!parser.parse_DIMACS(in, true)) exit(EXIT_FAILURE);
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
