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

#include <boost/program_options.hpp>

#if defined(__GNUC__) && defined(__linux__)
#include <fenv.h>
#endif

#include <iostream>
#include <iomanip>
#include <vector>
#include <atomic>
#include <fstream>
#include <sstream>
#include <string>
#include <signal.h>
#ifdef USE_ZLIB
#include <zlib.h>
#endif


#include "time_mem.h"
#include "arjun.h"
#include "config.h"
#include "helper.h"
#include <cryptominisat5/dimacsparser.h>

using std::cout;
using std::endl;
using std::string;
using std::vector;
using namespace CMSat;

po::options_description dontcare_options = po::options_description("dontcare options");
po::options_description help_options;
po::variables_map vm;
po::positional_options_description p;
double startTime;
ArjunInt::Config conf;
ArjunNS::Arjun* arjun = NULL;
string elimtofile;

uint32_t orig_cnf_must_mult_exp2;
uint32_t orig_sampling_set_size = 0;
vector<uint32_t> orig_sampling_set;

void add_dontcare_options()
{
    conf.verb = 1;

    dontcare_options.add_options()
    ("help,h", "Prints help")
    ("version", "Print version info")
    ("input", po::value<std::vector<string>>(), "file to read/write")
    ("verb,v", po::value(&conf.verb)->default_value(conf.verb), "verbosity")
    ("seed,s", po::value(&conf.seed)->default_value(conf.seed), "Seed")
    ;

    help_options.add(dontcare_options);
}

void only_conditional_dontcare(const vector<uint32_t>& sampl_vars)
{
    cout << "c [arjun] dumping simplified problem to '" << elimtofile << "'" << endl;
    auto simp_cnf = arjun->only_conditional_dontcare(sampl_vars);
    cout << " simp cnf size: " << simp_cnf.cnf.size() << endl;

    write_simpcnf(simp_cnf, elimtofile, orig_cnf_must_mult_exp2);
}

void set_config(ArjunNS::Arjun* arj) {
    /* cout << "c [arjun] using seed: " << conf.seed << endl; */
    arj->set_verbosity(conf.verb);
    arj->set_seed(conf.seed);
}

int main(int argc, char** argv)
{
    arjun = new ArjunNS::Arjun;
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
                  );
    #endif

    //Reconstruct the command line so we can emit it later if needed
    string command_line;
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) command_line += " ";
    }

    add_dontcare_options();
    add_supported_options(argc, argv, p, help_options, vm, arjun);

    /* cout << "c Arjun Version: " */
    /* << arjun->get_version_info() << endl; */
    /* cout << arjun->get_solver_version_info(); */

    /* cout */
    /* << "c executed with command line: " */
    /* << command_line */
    /* << endl; */

    set_config(arjun);

    //parsing the input
    if (vm.count("input") == 0
            || vm["input"].as<vector<string>>().size() == 0
            || vm["input"].as<vector<string>>().size() > 3) {
        cout << "ERROR: you must pass an INPUT, optionally an OUTPUT, and optionally a RECOVER files as parameters" << endl;
        exit(-1);
    }

    const string inp = vm["input"].as<vector<string>>()[0];
    if (vm["input"].as<vector<string>>().size() >= 2) {
        elimtofile = vm["input"].as<vector<string>>()[1];
    }
    if (vm["input"].as<vector<string>>().size() >= 3) {
        assert(false);
    }
    readInAFile(inp, arjun, orig_sampling_set_size, orig_cnf_must_mult_exp2, false);
    cout << "c [arjun] original sampling set size: " << orig_sampling_set_size << endl;

    if (elimtofile.empty()) {
        cout << "Must give output file" << endl;
        exit(-1);
    }
    only_conditional_dontcare(orig_sampling_set);

    delete arjun;
    return 0;
}
