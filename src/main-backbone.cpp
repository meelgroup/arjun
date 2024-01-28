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


#include "argparse.hpp"
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

argparse::ArgumentParser program = argparse::ArgumentParser("dontcare");
double startTime;
ArjunInt::Config conf;
ArjunNS::Arjun* arjun = nullptr;
string elimtofile;

uint32_t orig_cnf_must_mult_exp2;
uint32_t orig_sampling_set_size = 0;
vector<uint32_t> orig_sampling_set;

void add_backbone_options() {
    conf.verb = 1;
    program.add_argument("-h", "--help")
        .help("Prints help");
    program.add_argument("-v", "--version")
        .help("Print version info")
        .flag();
    program.add_argument("--verb,v")
        .action([&](const auto& a) {conf.verb = std::atoi(a.c_str());})
        .default_value(conf.verb)
        .help("verbosity");
    program.add_argument("--seed,s")
        .action([&](const auto& a) {conf.seed = std::atoi(a.c_str());})
        .default_value(conf.seed)
        .help("Seed");
    program.add_argument("files").remaining().help("input file and output file");
    conf.verb = 1;
}

void only_synthesis_unate(const vector<uint32_t>& sampl_vars)
{
    cout << "c [backbone] dumping simplified problem to '" << elimtofile << "'" << endl;
    auto ret = arjun->only_synthesis_unate(sampl_vars);

    write_simpcnf(ret, elimtofile, orig_cnf_must_mult_exp2);
}

void set_config(ArjunNS::Arjun* arj) {
    cout << "c [backbone] using seed: " << conf.seed << endl;
    arj->set_verbosity(conf.verb);
    arj->set_seed(conf.seed);
}

int main(int argc, char** argv)
{
    arjun = new ArjunNS::Arjun;
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   | FE_DIVBYZERO | FE_OVERFLOW);
    #endif

    //Reconstruct the command line so we can emit it later if needed
    string command_line;
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) command_line += " ";
    }

    add_backbone_options();
    cout << "c backbone Arjun Version: " << arjun->get_version_info() << endl;
    cout << arjun->get_solver_version_info();
    cout << "c executed with command line: " << command_line << endl;

    set_config(arjun);
    //parsing the input
    vector<std::string> files;
    try {
        files = program.get<std::vector<std::string>>("files");
        if (files.size() != 2) {
            cout << "ERROR: you must give an input an output file" << endl;
            exit(-1);
        }
    } catch (std::logic_error& e) {
        cout << "ERROR: you must give at least an input file" << endl;
        exit(-1);
    }
    const string inp = files[0];
    elimtofile = files[1];

    readInAFile(inp, arjun, orig_sampling_set_size, orig_cnf_must_mult_exp2, false);
    cout << "c [backbone] original sampling set size: " << orig_sampling_set_size << endl;
    vector<uint32_t> sampling_set = arjun->get_current_indep_set();
    auto simp_cnf = arjun->only_backbone(sampling_set);
    write_simpcnf(simp_cnf, elimtofile, orig_cnf_must_mult_exp2);

    delete arjun;
    return 0;
}
