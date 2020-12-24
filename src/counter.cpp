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
using boost::lexical_cast;
namespace po = boost::program_options;

#include <boost/multiprecision/cpp_bin_float.hpp>
namespace bmp = boost::multiprecision;
typedef bmp::number<bmp::cpp_bin_float<100> > cpp_bin_float_100;

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

#include "time_mem.h"
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>
#include <cryptominisat5/dimacsparser.h>


using std::cout;
using std::cerr;
using std::endl;
using std::map;
using std::set;
using std::string;
using std::vector;
using namespace CMSat;

po::options_description arjun_options = po::options_description("Arjun options");
po::options_description help_options;
po::variables_map vm;
po::positional_options_description p;


double startTime;
CMSat::SATSolver* solver;
vector<uint32_t> sampling_set;
int verb = 1;
int seed = 0;
int simp = 1;
uint32_t precision = 100;

void add_arjun_options()
{


    arjun_options.add_options()
    ("help,h", "Prints help")
    ("version", "Print version info")
    ("verb,v", po::value(&verb)->default_value(verb), "verbosity")
    ("simp,s", po::value(&simp)->default_value(simp), "simplify")
//     ("seed,s", po::value(&seed)->default_value(seed), "Seed")
    ("precision,p", po::value(&precision)->default_value(precision), "The precision to do")
    ("input", po::value<string>(), "file to read")
    ;

    help_options.add(arjun_options);
}


void add_supported_options(int argc, char** argv)
{
    add_arjun_options();
    p.add("input", 1);

    try {
        po::store(po::command_line_parser(argc, argv).options(help_options).positional(p).run(), vm);
        if (vm.count("help"))
        {
            cout
            << "Minimal projection set finder" << endl;

            cout
            << "counter [options] inputfile" << endl << endl;

            cout << help_options << endl;
            std::exit(0);
        }

        if (vm.count("version")) {
            //TODO //cout << "c [counter] Version: " << arjun->get_version_info() << endl;
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

void readInAFile(const string& filename)
{
    #ifndef USE_ZLIB
    FILE * in = fopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<FILE*, FN>, CMSat::SATSolver> parser(solver, NULL, 0);
    #else
    gzFile in = gzopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<gzFile, GZ>, CMSat::SATSolver> parser(solver, NULL, 0);
    #endif

    if (in == NULL) {
        std::cerr
        << "ERROR! Could not open file '"
        << filename
        << "' for reading: " << strerror(errno) << endl;

        std::exit(-1);
    }

    if (!parser.parse_DIMACS(in, false)) {
        exit(-1);
    }

    if (parser.sampling_vars.empty()) {
        cout << "ERROR: Must give sampling set!!" << endl;
        exit(-1);
    }

    sampling_set = parser.sampling_vars;

    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}


int main(int argc, char** argv)
{
    solver = new CMSat::SATSolver;
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
                  );
    #endif
    double start_time = cpuTime();

    //Reconstruct the command line so we can emit it later if needed
    string command_line;
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) {
            command_line += " ";
        }
    }

    add_supported_options(argc, argv);

    cout
    << "c executed with command line: "
    << command_line
    << endl;


    //parsing the input
    if (vm.count("input") == 0) {
        cout << "ERROR: you must pass a file" << endl;
        exit(-1);
    }
    const string inp = vm["input"].as<string>();
    readInAFile(inp);


    //Get initial solution
    if (sampling_set.size() == 0) {
        cout << "WARNING: sampling set is empty!" << endl;
        cout << "Num sols: 0" << endl;
        return 0;

    }

    double simp_time = cpuTime();
    cout << "Simplifying..." << endl;
    solver->set_sampling_vars(&sampling_set);

    if (simp) {
        vector<Lit> dont_elim;
        for(const auto& x: sampling_set) {
            dont_elim.push_back(Lit(x, false));
        }
        solver->simplify(&dont_elim);
        cout << "Simplify done. T: "
        << std::fixed
        << std::setprecision(2) << std::setw(6)
        << (cpuTime() - simp_time) << endl;
    }


    lbool ret = solver->solve(NULL, true);
    if (ret == l_False) {
        cout << "Num sols: 0" << endl;
        return 0;
    }

    //Now we sample
    solver->set_up_for_sample_counter();
    vector<lbool> solution;
    for(const auto& v: sampling_set) {
        solution.push_back(solver->get_model()[v]);
    }
    vector<Lit> assumps;
    for(uint32_t i = 0 ; i < sampling_set.size(); i++) {
        uint32_t var = sampling_set[i];
        lbool val = solution[i];
        assert(val != l_Undef);
        assumps.push_back(Lit(var, val==l_False));
    }

    double sampling_time = cpuTime();
    vector<cpp_bin_float_100> values;
    values.push_back(1.0);
    uint32_t at = 0;
    solver->set_verbosity(verb-1);
    for(int i = sampling_set.size()-1; i >=0; i--, at++) {
        cout << "Doing round " << i << " ..." << endl;
        double one_round_t = cpuTime();
        const uint32_t var = sampling_set[i];
        const lbool val = solution[i];

        assumps.resize(i);
        if (at % 20 == 19 && simp) {
            cout << "New simplify..." << endl;
            double in_simp_time = cpuTime();
            solver->simplify(&assumps);
            cout << "New simp finished. T: " << (cpuTime() - in_simp_time) << endl;
        }

        uint32_t set_right = 0;
        for(uint32_t i2 = 0; i2 < precision; i2++) {
            solver->solve(&assumps, true);
            assert(solver->get_model()[var] != l_Undef);
            if (solver->get_model()[var] == val) {
                set_right++;
            }
        }
        cpp_bin_float_100 distrib = set_right;
        distrib /= precision;

        values.push_back(distrib);
        cout << "Round " << i << " time: "
        << std::setprecision(4) << std::setw(6)
        << (cpuTime() - one_round_t)
        << std::setprecision(4) << std::setw(6)
        << " distrib: " << distrib
        << endl;
    }
    cout << "All round time: "
    << std::setprecision(4) << std::setw(6)
    << (cpuTime() - sampling_time) << endl;

    cout << "Total time: "
    << std::setprecision(2) << std::setw(2)
    << (cpuTime() - start_time) << endl;

    cpp_bin_float_100 count = 1.0;
    for(const auto& x: values) {
        count /= x;
    }
    cout << "Num sols: "
    << std::fixed
    << (count) << endl;

    delete solver;
}
