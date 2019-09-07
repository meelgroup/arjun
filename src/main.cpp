/*
 MIS

 Copyright (c) 2009-2018, Mate Soos. All rights reserved.

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
using std::string;
using std::vector;

#if defined(__GNUC__) && defined(__linux__)
#include <fenv.h>
#endif

#include <iostream>
#include "time_mem.h"
#include "GitSHA1.h"
#include <cryptominisat5/cryptominisat.h>
#include "cryptominisat5/dimacsparser.h"
#include "cryptominisat5/streambuffer.h"

using namespace CMSat;
using std::cout;
using std::cerr;
using std::endl;

po::options_description mis_options = po::options_description("MIS options");
po::options_description help_options;
po::variables_map vm;
po::positional_options_description p;
CMSat::SATSolver* solver = NULL;
double startTime;

struct Config {
    int verb = 0;
    int seed = 0;
    vector<uint32_t> sampling_set;
};

Config conf;

void add_mis_options()
{
    std::ostringstream my_epsilon;
    std::ostringstream my_delta;
    std::ostringstream my_kappa;

    mis_options.add_options()
    ("help,h", "Prints help")
    ("version", "Print version info")
    ("input", po::value<string>(), "file to read")
    ("verb,v", po::value(&conf.verb)->default_value(conf.verb), "verbosity")
    ("seed,s", po::value(&conf.seed)->default_value(conf.seed), "Seed")
    ;

    help_options.add(mis_options);
}

void add_supported_options(int argc, char** argv)
{
    add_mis_options();
    p.add("input", 1);

    try {
        po::store(po::command_line_parser(argc, argv).options(help_options).positional(p).run(), vm);
        if (vm.count("help"))
        {
            cout
            << "Probably Approximate counter" << endl;

            cout
            << "approxmc [options] inputfile" << endl << endl;

            cout << help_options << endl;
            std::exit(0);
        }

        if (vm.count("version")) {
            cout << "[mis] Version: " << get_version_sha1() << endl;
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
    solver->add_sql_tag("filename", filename);
    #ifndef USE_ZLIB
    FILE * in = fopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<FILE*, FN> > parser(solver, NULL, 2);
    #else
    gzFile in = gzopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<gzFile, GZ> > parser(solver, NULL, 2);
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

    conf.sampling_set.swap(parser.sampling_vars);

    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}

void readInStandardInput()
{
    cout
    << "c Reading from standard input... Use '-h' or '--help' for help."
    << endl;

    #ifndef USE_ZLIB
    FILE * in = stdin;
    #else
    gzFile in = gzdopen(0, "rb"); //opens stdin, which is 0
    #endif

    if (in == NULL) {
        std::cerr << "ERROR! Could not open standard input for reading" << endl;
        std::exit(1);
    }

    #ifndef USE_ZLIB
    DimacsParser<StreamBuffer<FILE*, FN> > parser(solver, NULL, 2);
    #else
    DimacsParser<StreamBuffer<gzFile, GZ> > parser(solver, NULL, 2);
    #endif

    if (!parser.parse_DIMACS(in, false)) {
        exit(-1);
    }

    conf.sampling_set.swap(parser.sampling_vars);

    #ifdef USE_ZLIB
        gzclose(in);
    #endif
}

void set_sampling_vars()
{
    if (conf.sampling_set.empty()) {
        cout
        << "[mis] No sample set given, starting with full" << endl;
        for (size_t i = 0; i < solver->nVars(); i++) {
            conf.sampling_set.push_back(i);
        }
    }
    cout << "[mis] Sampling set size: " << conf.sampling_set.size() << endl;
    if (conf.sampling_set.size() > 100) {
        cout
        << "[mis] Sampling var set contains over 100 variables, not displaying"
        << endl;
    } else {
        cout << "[mis] Sampling set: ";
        for (auto v: conf.sampling_set) {
            cout << v+1 << ", ";
        }
        cout << endl;
    }
    solver->set_sampling_vars(&conf.sampling_set);
}

int main(int argc, char** argv)
{
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
                  );
    #endif

    add_supported_options(argc, argv);
    cout << "[mis] Version: " << get_version_sha1() << endl;

    cout << "[mis] using seed: " << conf.seed << endl;

    startTime = cpuTimeTotal();
    solver = new SATSolver();
    if (conf.verb > 2) {
        solver->set_verbosity(conf.verb-2);
    }

    //parsing the input
    if (vm.count("input") != 0) {
        string inp = vm["input"].as<string>();
        if (inp.size() > 1) {
            cout << "[mis] ERROR: can only parse in one file" << endl;
        }
        readInAFile(inp.c_str());
    } else {
        readInStandardInput();
    }
    set_sampling_vars();

    return 0;
}

