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

#include "src/arjun.h"

#if defined(__GNUC__) && defined(__linux__)
#include <cfenv>
#endif

#include <iostream>
#include <iomanip>
#include <vector>
#include <atomic>
#include <fstream>
#include <sstream>
#include <string>
#include <csignal>
#ifdef USE_ZLIB
#include <zlib.h>
#endif
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/streambuffer.h>

#include "argparse.hpp"
#include "time_mem.h"

using std::cout;
using std::endl;
using std::string;
using std::vector;
using namespace CMSat;

argparse::ArgumentParser program = argparse::ArgumentParser("dontcare");
double start_time;
int verb;
int seed;
vector<lbool> simp_sol;
bool satisfiable;

void add_options()
{
    verb = 1;
    program.add_argument("--verb,v")
        .action([&](const auto& a) {verb = std::atoi(a.c_str());})
        .default_value(verb)
        .help("verbosity");
    program.add_argument("--seed,s")
        .action([&](const auto& a) {seed = std::atoi(a.c_str());})
        .default_value(seed)
        .help("Seed");
    program.add_argument("files").remaining().help("input file and output file");
}

void parse_v_line(StreamBuffer<FILE*, FN>& in, const uint32_t line_num)
{
    int32_t parsed_lit;
    uint32_t var;
    for (;;) {
        if (!in.parseInt(parsed_lit, line_num, true)) {
            exit(-1);
        }
        if (parsed_lit == std::numeric_limits<int32_t>::max()) {
            break;
        }
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        if (simp_sol.size() <= var)
            simp_sol.insert(simp_sol.end(), var-simp_sol.size()+1, l_Undef);

        if (simp_sol[var] != l_Undef) {
            cout << "ERROR: Variable " << var+1 << " is in the solution TWICE! That's wrong." << endl;
            exit(-1);
        }
        simp_sol[var] = parsed_lit < 0 ? l_False : l_True;
    }
}

void parse_solution(StreamBuffer<FILE*, FN>& in)
{
    std::string str;
    uint32_t line_num = 0;
    bool s_line_found = false;

    for (;;) {
        in.skipWhitespace();
        switch (*in) {
        case EOF:
            if (!s_line_found) {
                cout << "ERROR: could not find line starting with 's SATISFIABLE' in solution" << endl;
                exit(-1);
            }
            return;
        case 's': {
            ++in;
            if (s_line_found) {
                cout << "ERROR: solution contains TWO lines starting with 's'. That's wrong." << endl;
                exit(-1);
            }
            in.skipWhitespace();
            in.parseString(str);
            if (str == string("SATISFIABLE")) {
                satisfiable = true;
            } else if (str == string("UNSATISFIABLE")) {
                satisfiable = false;
            } else {
                cout << "ERROR: line starting with 's' is not followed by either SATISFIABLE or UNSATISFIABLE" << endl;
                exit(-1);
            }
            s_line_found = true;
            in.skipLine();
            line_num++;
            break;
        }
        case 'v':
            ++in;
            parse_v_line(in, line_num);
            in.skipLine();
            line_num++;
            break;
        default:
            ++in;
            in.skipLine();
            line_num++;
            break;
        }
    }
}

uint32_t print_model(const vector<lbool>& model, std::ostream* os)
{
    *os << "v ";
    size_t line_size = 2;
    size_t num_undef = 0;

    auto fun = [&](uint32_t var) {
        if (model[var] != CMSat::l_Undef) {
            const bool value_is_positive = (model[var] == CMSat::l_True);
            const size_t this_var_size = std::ceil(std::log10(var+1)) + 1 + !value_is_positive;
            line_size += this_var_size;
            if (line_size > 80) {
                *os << std::endl << "v ";
                line_size = 2 + this_var_size;
            }
            *os << (value_is_positive? "" : "-") << var+1 << " ";
        } else {
            num_undef++;
        }
    };

    for (uint32_t var = 0; var < model.size(); var++) fun(var);
    *os << "0" << std::endl;
    return num_undef;
}

int main(int argc, char** argv)
{
    //Reconstruct the command line so we can emit it later if needed
    string command_line;
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) command_line += " ";
    }

    if (verb) {
        cout << "c solextend Version: " << ArjunNS::Arjun::get_version_info() << endl;
        cout << ArjunNS::Arjun::get_solver_version_info();
        cout << "c executed with command line: " << command_line << endl;
    }

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
    const string recover_file = files[0];
    const string sol_file = files[1];

    // get solution from file
    FILE * in = fopen(sol_file.c_str(), "rb");
    StreamBuffer<FILE*, FN> sb(in);
    parse_solution(sb);
    fclose(in);
    if (verb >= 2) {
        cout << "c orig solution is: ";
        if (satisfiable) {
            cout << "SAT" << endl;
            for(uint32_t i = 0; i < simp_sol.size(); i++) {
                cout << "var " << std::setw(7) << i+1 << " : " << simp_sol[i]  << " " << endl;
            }
        } else {
            cout << "UNSAT" << endl;
        }
    }

    if (!satisfiable) {
        cout << "s UNSATISFIABLE" << endl;
        return 20;
    }

    // get recovery system from file
    std::ifstream ifs(recover_file, std::ios::in | std::ios::binary);
    string rec_data(
            (std::istreambuf_iterator<char>(ifs)),
            (std::istreambuf_iterator<char>()));
    ifs.close();
    void* solver = SATSolver::create_extend_solution_setup(rec_data);

    // Extend solutions
    const auto sol = SATSolver::extend_solution(solver, simp_sol);
    if (verb) cout << "c solution mapped back" << endl;
    assert(sol.first != l_Undef);
    if (sol.first == l_False) {
        cout << "s UNSATISFIABLE" << endl;
        return 20;
    }
    cout << "s SATISFIABLE" << endl;
    print_model(sol.second, &std::cout);

    return 10;
}
