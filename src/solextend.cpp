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
#include <boost/program_options.hpp>
namespace po = boost::program_options;

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
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/streambuffer.h>
#include "time_mem.h"

using std::cout;
using std::cerr;
using std::endl;
using std::string;
using std::vector;
using namespace CMSat;

po::options_description options = po::options_description("Solution Extender options");
po::options_description help_options;
po::variables_map vm;
po::positional_options_description p;
double startTime;
int verb;
int seed;
vector<lbool> simp_sol;

void add_options()
{

    options.add_options()
    ("help,h", "Prints help")
    ("version", "Print version info")
    ("input", po::value<std::vector<string>>(), "file to read/write")
    ("verb,v", po::value(&verb)->default_value(verb), "verbosity")
    ("seed,s", po::value(&seed)->default_value(seed), "Seed")
    ;

    help_options.add(options);
}

void add_supported_options(int argc, char** argv)
{
    add_options();
    p.add("input", -1);

    try {
        po::store(po::command_line_parser(argc, argv).options(help_options).positional(p).run(), vm);
        if (vm.count("help"))
        {
            cout
            << "Solution extender for Arjun." << endl << endl
            << "arjun-extend [options] recover.dat solutionfile" << endl;

            cout << help_options << endl;
            std::exit(0);
        }

        if (vm.count("version")) {
            cout << "c [arjun] SHA revision: " << ArjunNS::Arjun::get_version_info() << endl;
            cout << "c [arjun] Compilation environment: " << ArjunNS::Arjun::get_compilation_env() << endl;
            cout << "c [arjun] CMS version: " << ArjunNS::Arjun::get_solver_version_info();
            std::exit(0);
        }

        po::notify(vm);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::unknown_option> >& c
    ) {
        cerr
        << "ERROR: Some option you gave was wrong. Please give '--help' to get help" << endl
        << "       Unkown option: " << c.what() << endl;
        std::exit(-1);
    } catch (boost::bad_any_cast &e) {
        std::cerr
        << "ERROR! You probably gave a wrong argument type" << endl
        << "       Bad cast: " << e.what()
        << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::invalid_option_value> >& what
    ) {
        cerr
        << "ERROR: Invalid value '" << what.what() << "'" << endl
        << "       given to option '" << what.get_option_name() << "'"
        << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::multiple_occurrences> >& what
    ) {
        cerr
        << "ERROR: " << what.what() << " of option '"
        << what.get_option_name() << "'"
        << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::required_option> >& what
    ) {
        cerr
        << "ERROR: You forgot to give a required option '"
        << what.get_option_name() << "'"
        << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::too_many_positional_options_error> >& what
    ) {
        cerr
        << "ERROR: You gave too many positional arguments. Only the input CNF can be given as a positional option." << endl;
        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::ambiguous_option> >& what
    ) {
        cerr
        << "ERROR: The option you gave was not fully written and matches" << endl
        << "       more than one option. Please give the full option name." << endl
        << "       The option you gave: '" << what.get_option_name() << "'" <<endl
        << "       The alternatives are: ";
        for(size_t i = 0; i < what.alternatives().size(); i++) {
            cout << what.alternatives()[i];
            if (i+1 < what.alternatives().size()) {
                cout << ", ";
            }
        }
        cout << endl;

        std::exit(-1);
    } catch (boost::exception_detail::clone_impl<
        boost::exception_detail::error_info_injector<po::invalid_command_line_syntax> >& what
    ) {
        cerr
        << "ERROR: The option you gave is missing the argument or the" << endl
        << "       argument is given with space between the equal sign." << endl
        << "       detailed error message: " << what.what() << endl
        ;
        std::exit(-1);
    }
}

void parse_v_line(StreamBuffer<FILE*, FN>& in, const uint32_t lineNum)
{
    int32_t parsed_lit;
    uint32_t var;
    for (;;) {
        if (!in.parseInt(parsed_lit, lineNum, true)) {
            exit(-1);
        }
        if (parsed_lit == std::numeric_limits<int32_t>::max()) {
            break;
        }
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        if (simp_sol.size() <= var)
            simp_sol.insert(simp_sol.end(), var-simp_sol.size()+1, l_Undef);

        simp_sol[var] = parsed_lit < 0 ? l_False : l_True;
    }
}

void parse_solution(StreamBuffer<FILE*, FN>& in)
{
    std::string str;
    uint32_t lineNum = 0;
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
            in.skipWhitespace();
            std::string s;
            in.parseString(str);
            if (str != string("SATISFIABLE")) {
                cout << "ERROR: solution doesn't contain 's SATISFIABLE'" << endl;
                exit(-1);
            }
            lineNum++;
            break;
        }
        case 'v':
            ++in;
            parse_v_line(in, lineNum);
            lineNum++;
            break;
        default:
            in.skipLine();
            lineNum++;
            break;
        }
    }
}


int main(int argc, char** argv)
{
    //Reconstruct the command line so we can emit it later if needed
    string command_line;
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) command_line += " ";
    }

    add_supported_options(argc, argv);

    cout << "c Arjun Version: "
    << ArjunNS::Arjun::get_version_info() << endl;
    cout << ArjunNS::Arjun::get_solver_version_info();

    cout
    << "c executed with command line: "
    << command_line
    << endl;

    //parsing the input
    if (vm.count("input") != 2) {
        cout << "ERROR: you must pass an INPUT, optionally an OUTPUT, and optionally a RECOVER files as parameters" << endl;
        exit(-1);
    }

    const string sol_file = vm["input"].as<vector<string>>()[0];
    const string recover_file = vm["input"].as<vector<string>>()[2];

    // get solution from file
    FILE * in = fopen(sol_file.c_str(), "rb");
    StreamBuffer<FILE*, FN> sb(in);
    parse_solution(sb);
    fclose(in);
    if (verb) {
        cout << "c orig solution is: ";
        for(const auto& l: simp_sol)
            cout << l << " ";
        cout << "0" << endl;
    }
    return 0;

    // get recovery system from file
    std::ifstream indat(recover_file, std::ios::in);
    string rec_data;
    indat >> rec_data;
    indat.close();
    void* solver = SATSolver::create_extend_solution_setup(rec_data);

    // Extend solutions
    const auto sol = SATSolver::extend_solution(solver, simp_sol);



    return 0;
}

