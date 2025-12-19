/*
 test-synth

 Copyright (c) 2024. All rights reserved.

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

#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include "argparse.hpp"
#include "arjun.h"

#define myopt(name, var, fun, hhelp) \
    program.add_argument(name) \
        .action([&](const auto& a) {var = std::fun(a.c_str());}) \
        .default_value(var) \
        .help(hhelp)
#define myopt2(name1, name2, var, fun, hhelp) \
    program.add_argument(name1, name2) \
        .action([&](const auto& a) {var = std::fun(a.c_str());}) \
        .default_value(var) \
        .help(hhelp)

using std::cout;
using std::endl;
using std::string;
using std::vector;
using std::unique_ptr;
using namespace ArjunNS;

int verb = 1;
int mode = 0;

int main(int argc, char** argv) {
    argparse::ArgumentParser program = argparse::ArgumentParser("test-synth", "1.0",
            argparse::default_arguments::help);

    // Add options
    myopt2("-v", "--verb", verb, atoi, "Verbosity");
    myopt2("-m", "--mode", mode, atoi, "Field mode (0=FGenMpz, 1=FGenMpq)");

    // Add positional argument for input file
    program.add_argument("files").remaining().help("input AIG file");

    try {
        program.parse_args(argc, argv);
    } catch (const std::exception& err) {
        std::cerr << err.what() << std::endl;
        std::cerr << program;
        return EXIT_FAILURE;
    }

    // Get input file
    vector<string> files;
    try {
        files = program.get<std::vector<std::string>>("files");
        if (files.empty()) {
            cout << "ERROR: you must provide an input file" << endl;
            return EXIT_FAILURE;
        }
        if (files.size() > 1) {
            cout << "ERROR: you can only pass one input file" << endl;
            return EXIT_FAILURE;
        }
    } catch (std::logic_error& e) {
        cout << "ERROR: you must give an input file" << endl;
        return EXIT_FAILURE;
    }

    string input_file = files[0];

    // Create field generator
    unique_ptr<CMSat::FieldGen> fg;
    switch (mode) {
        case 0:
            fg = std::make_unique<FGenMpz>();
            break;
        case 1:
            fg = std::make_unique<FGenMpq>();
            break;
        default:
            cout << "ERROR: Unknown mode " << mode << endl;
            return EXIT_FAILURE;
    }

    // Create SimplifiedCNF and read the AIG file
    SimplifiedCNF cnf(fg);

    if (verb) {
        cout << "c [test-synth] Reading AIG file: " << input_file << endl;
    }

    cnf.read_aig_defs_from_file(input_file);

    // Print statistics
    if (verb) {
        cout << "c [test-synth] Successfully read AIG file" << endl;
        cout << "c [test-synth] Number of variables: " << cnf.nvars << endl;
        cout << "c [test-synth] Number of clauses: " << cnf.clauses.size() << endl;
        cout << "c [test-synth] Number of red clauses: " << cnf.red_clauses.size() << endl;
        cout << "c [test-synth] Number of sampl_vars: " << cnf.sampl_vars.size() << endl;
        cout << "c [test-synth] Number of opt_sampl_vars: " << cnf.opt_sampl_vars.size() << endl;
        cout << "c [test-synth] Number of AIG defs: " << cnf.defs.size() << endl;
        cout << "c [test-synth] need_aig: " << cnf.need_aig << endl;
        cout << "c [test-synth] proj: " << cnf.proj << endl;
        cout << "c [test-synth] backbone_done: " << cnf.backbone_done << endl;
    }

    cout << "c [test-synth] All done." << endl;
    return 0;
}
