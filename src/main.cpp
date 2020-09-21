/*
 Arjun

 Copyright (c) 2019, Mate Soos and Kuldeep S. Meel. All rights reserved.

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
#include <iomanip>
#include <random>
#include <algorithm>
#include <map>
#include <set>
#include <vector>
#include <atomic>
#include <signal.h>

#include "time_mem.h"
#include "GitSHA1.h"
#include "MersenneTwister.h"

#include <cryptominisat5/cryptominisat.h>
#include "cryptominisat5/dimacsparser.h"
#include "cryptominisat5/streambuffer.h"
#include "arjun_config.h"
#include "common.h"

using namespace CMSat;
using std::cout;
using std::cerr;
using std::endl;
using std::map;
using std::set;

po::options_description mis_options = po::options_description("MIS options");
po::options_description help_options;
po::variables_map vm;
po::positional_options_description p;
string command_line;
double startTime;

Common common;
MTRand mtrand;

static void signal_handler(int) {
    cout << endl << "*** INTERRUPTED ***" << endl << std::flush;
    common.print_indep_set();
    cout << endl << "*** INTERRUPTED ***" << endl << std::flush;
    exit(1);
}

void add_mis_options()
{
    std::ostringstream my_epsilon;
    std::ostringstream my_delta;
    std::ostringstream my_kappa;

    mis_options.add_options()
    ("help,h", "Prints help")
    ("version", "Print version info")
    ("input", po::value<string>(), "file to read")
    ("verb,v", po::value(&common.conf.verb)->default_value(common.conf.verb), "verbosity")
    ("seed,s", po::value(&common.conf.seed)->default_value(common.conf.seed), "Seed")
    ("bve", po::value(&common.conf.bve)->default_value(common.conf.bve), "bve")
    ("distill", po::value(&common.conf.distill)->default_value(common.conf.distill), "distill")
    ("backbone", po::value(&common.conf.backbone)->default_value(common.conf.backbone), "backbone")
    ("guess", po::value(&common.conf.guess)->default_value(common.conf.guess), "Guess small set")
    ("one", po::value(&common.conf.always_one_by_one)->default_value(common.conf.always_one_by_one),
     "always one-by-one mode")
    ("simp", po::value(&common.conf.simp)->default_value(common.conf.simp),
     "simplify")
    ("recomp", po::value(&common.conf.recompute_sampling_set)->default_value(common.conf.recompute_sampling_set),
     "Recompute sampling set even if it's part of the CNF")
    ("byforce", po::value(&common.conf.force_by_one)->default_value(common.conf.force_by_one),
     "Force 1-by-1 query")
    ("setfwd", po::value(&common.conf.set_val_forward)->default_value(common.conf.set_val_forward),
     "When doing forward, set the value instead of using assumptions")
    ("backwardonly", po::value(&common.conf.backward_only)->default_value(common.conf.backward_only),
     "Only do backwards query")
    ("gates", po::value(&common.conf.gate_based)->default_value(common.conf.gate_based),
     "Use 3-long gate detection in SAT solver")
    ("bmaxc", po::value(&common.conf.backw_max_confl)->default_value(common.conf.backw_max_confl),
     "Maximum conflicts per variable in backward mode")


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
            cout << "c [mis] Version: " << get_version_sha1() << endl;
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


int main(int argc, char** argv)
{
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
                  );
    #endif

    //Reconstruct the command line so we can emit it later if needed
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) {
            command_line += " ";
        }
    }

    add_supported_options(argc, argv);
    cout << "c [mis] Arjun Version: " << get_version_sha1() << endl;
    cout
    << "c executed with command line: "
    << command_line
    << endl;
    cout << "c [mis] using seed: " << common.conf.seed << endl;

    double starTime = cpuTime();
    mtrand.seed(common.conf.seed);

        //parsing the input
    if (vm.count("input") == 0) {
        cout << "ERROR: you must pass a file" << endl;
    }
    const string inp = vm["input"].as<string>();

    common.init_solver_setup(true, inp);
    cout << common.solver->get_text_version_info();
    signal(SIGALRM,signal_handler);
    //signal(SIGINT,signal_handler);

    uint32_t prev_size = common.sampling_set->size()*100;
    uint32_t num;
    uint32_t round_num = 0;

    bool cont = true;
    bool forward = true;
    if (common.conf.backward_only) {
        forward = false;
    }
    while(cont) {
        if (common.sampling_set->size() > 60 && round_num < 1) {
            common.simp();
        }
        if (common.conf.guess && round_num > 1) {
            common.run_guess();
        }

        num = 1;
        prev_size = common.sampling_set->size();

        cout << "c [mis] ===--> Doing a run for " << num << endl;
        if (forward) {
            cout << "c [mis] FORWARD " << endl;
            uint32_t guess_indep = std::max<uint32_t>(common.sampling_set->size()/100, 10);
            common.forward_round(50000, guess_indep, false, false, 0);
            cont = true;
        } else {
            cout << "c [mis] BACKWARD " << endl;
            num = 50000;
            if (common.conf.backward_only) {
                num = std::numeric_limits<uint32_t>::max();
            }
            cont = !common.backward_round(num);
        }
        round_num++;
        if (round_num > 0) {
            //forward = !forward;
            forward = 0;
        }
    }

    common.print_indep_set();
    cout << "c [mis] "
    << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - starTime)
    << endl;

    return 0;
}
