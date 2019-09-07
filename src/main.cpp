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
#include <random>
#include <algorithm>
#include <map>
#include <set>
#include <vector>
#include "time_mem.h"
#include "GitSHA1.h"
#include <cryptominisat5/cryptominisat.h>
#include "cryptominisat5/dimacsparser.h"
#include "cryptominisat5/streambuffer.h"

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
CMSat::SATSolver* solver = NULL;
double startTime;
vector<uint32_t> sampling_set;

struct Config {
    int verb = 0;
    int seed = 0;
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

void readInAFile(const string& filename, uint32_t var_offset, bool get_sampling_set)
{
    #ifndef USE_ZLIB
    FILE * in = fopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<FILE*, FN> > parser(solver, NULL, 0);
    #else
    gzFile in = gzopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<gzFile, GZ> > parser(solver, NULL, 0);
    #endif

    if (in == NULL) {
        std::cerr
        << "ERROR! Could not open file '"
        << filename
        << "' for reading: " << strerror(errno) << endl;

        std::exit(-1);
    }

    if (!parser.parse_DIMACS(in, false, var_offset)) {
        exit(-1);
    }
    if (get_sampling_set) {
        sampling_set = parser.sampling_vars;
    }

    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}

void update_and_print_sampling_vars()
{
    if (sampling_set.empty()) {
        cout
        << "[mis] No sample set given, starting with full" << endl;
        for (size_t i = 0; i < solver->nVars(); i++) {
            sampling_set.push_back(i);
        }
    }
    cout << "[mis] Sampling set size: " << sampling_set.size() << endl;
    if (sampling_set.size() > 100) {
        cout
        << "[mis] Sampling var set contains over 100 variables, not displaying"
        << endl;
    } else {
        cout << "[mis] Sampling set: ";
        for (auto v: sampling_set) {
            cout << v+1 << ", ";
        }
        cout << endl;
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

    add_supported_options(argc, argv);
    cout << "[mis] Version: " << get_version_sha1() << endl;

    cout << "[mis] using seed: " << conf.seed << endl;

    startTime = cpuTimeTotal();
    solver = new SATSolver();
    if (conf.verb > 2) {
        solver->set_verbosity(conf.verb-2);
    }

    //parsing the input
    if (vm.count("input") == 0) {
        cout << "ERROR: you must pass a file" << endl;
    }
    const string inp = vm["input"].as<string>();

    //Read in file and set sampling set
    readInAFile(inp.c_str(), 0, true);
    update_and_print_sampling_vars();

    //Read in file again, with offset
    const uint32_t orig_num_vars = solver->nVars();
    readInAFile(inp.c_str(), orig_num_vars, false);

    //Set up solver
    vector<Lit> torem_orig;
    solver->set_no_bve();
    solver->set_no_bva();
    solver->set_up_for_scalmc();
    //solver->set_verbosity(2);

    //Print stats
    cout << "Orig number of variables: " << orig_num_vars << endl;
    cout << "Cur number of variables : " << solver->nVars() << endl;

    vector<uint32_t> indic;

    vector<Lit> tmp;
    //Indicator variable is TRUE when they are NOT equal
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        //(a=b) = !f
        //a  V -b V  f
        //-a V  b V  f
        //a  V  b V -f
        //-a V -b V -f
        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        torem_orig.push_back(Lit(this_indic, false));
        indic.push_back(this_indic);

        tmp.clear();
        tmp.push_back(Lit(i,               false));
        tmp.push_back(Lit(i+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,      false));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(i,               true));
        tmp.push_back(Lit(i+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,      false));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(i,               false));
        tmp.push_back(Lit(i+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,      true));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(i,               true));
        tmp.push_back(Lit(i+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,      true));
        solver->add_clause(tmp);
    }

    //OR together the indicators: one of them must NOT be equal
    //indicator tells us when they are NOT equal. One among them MUST be NOT equal
    //hence at least one indicator variable must be TRUE
    assert(indic.size() == orig_num_vars);
    tmp.clear();
    for(uint32_t var: indic) {
        tmp.push_back(Lit(var, false));
    }
    solver->add_clause(tmp);

    //Initially, all of independent set is unknown
    set<uint32_t> unknown;
    unknown.insert(sampling_set.begin(), sampling_set.end());

    //start with empty independent set
    vector<uint32_t> indep;

    //testvar_to_assump:
    //FIRST is variable we want to test for
    //SECOND is what we have to assumoe (in negative)
    map<uint32_t, uint32_t> testvar_to_assump;
    map<uint32_t, uint32_t> assump_to_testvar;


    for(const auto& var: unknown) {
        solver->new_var();
        uint32_t ass = solver->nVars()-1;

        tmp.clear();
        tmp.push_back(Lit(ass, false));
        tmp.push_back(Lit(var, false));
        tmp.push_back(Lit(var+orig_num_vars, true));
        solver->add_clause(tmp);

        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        solver->add_clause(tmp);
        testvar_to_assump[var] = ass;
        assump_to_testvar[ass] = var;
    }
    cout << "[mis] Start unknown size: " << unknown.size() << endl;

    double start_iter_time = cpuTime();
    uint32_t not_indep = 0;
    vector<Lit> assumptions;
    vector<char> seen;
    seen.resize(solver->nVars(), 0);
    uint32_t iter = 0;
    bool slow_mode = false;
    uint32_t num_fast = 0;
    while(!unknown.empty()) {
        if (!slow_mode) {
            if (iter % 100 == 0 ||  iter < 1) {
                num_fast ++;
            } else {
                slow_mode = true;
            }
        }
        bool old_mode = slow_mode;
        assumptions.clear();

        uint32_t test_var = var_Undef;
        if (slow_mode) {
            test_var = *unknown.begin();
            unknown.erase(test_var);
        }

        //Add unknown as assumptions
        vector<Lit> torem(torem_orig);
        for(const auto& var: unknown) {
            //torem.push_back(Lit(var, false));
            uint32_t ass = testvar_to_assump[var];
            assumptions.push_back(Lit(ass, true));
            torem.push_back(Lit(ass, false));
        }

        //Add known independent as assumptions
        for(const auto& var: indep) {
            //torem.push_back(Lit(var, false));
            uint32_t ass = testvar_to_assump[var];
            assumptions.push_back(Lit(ass, true));
            torem.push_back(Lit(ass, false));
        }

        double myTime = cpuTime();
        std::random_shuffle(assumptions.begin(), assumptions.end());
        /*cout << "ass: ";
        for(uint32_t i = 0; i < assumptions.size(); i ++) {
            cout << assumptions[i] << " ";
        }
        cout << "0" << endl;*/
        if (!slow_mode) {
            //solver->simplify(&assumptions);
            //solver->forget_long_cls(0, torem);
        }
        if (iter ==0) {
            solver->simplify(&assumptions);
        }
        lbool ret = solver->solve(&assumptions);
        assert(ret != l_Undef);
        //anything that's NOT in the reason is dependent.

        uint32_t num_removed = 0;
        if (ret == l_True) {
            assert(slow_mode);
            indep.push_back(test_var);
            num_removed++;
            slow_mode = false;
        } else {
            if (slow_mode) {
                //not independent
                uint32_t var = test_var;
                tmp.clear();
                tmp.push_back(Lit(testvar_to_assump[var], false));
                solver->add_clause(tmp);
                not_indep++;
                num_removed++;
                slow_mode = false;
            } else {
                vector<Lit> reason = solver->get_conflict();
                //cout << "reason size: " << reason.size() << endl;
                for(Lit l: reason) {
                    seen[l.var()] = true;
                }
                vector<uint32_t> not_in_reason;
                for(Lit l: assumptions) {
                    if (!seen[l.var()]) {
                        not_in_reason.push_back(l.var());
                    }
                }
                for(Lit l: reason) {
                    seen[l.var()] = false;
                }
                //cout << "not in reason: " << not_in_reason.size() << endl;

                //not independent.
                for(uint32_t ass: not_in_reason) {
                    uint32_t var = assump_to_testvar[ass];
                    tmp.clear();
                    assert(testvar_to_assump[var] == ass);
                    tmp.push_back(Lit(testvar_to_assump[var], false));
                    solver->add_clause(tmp);
                    not_indep++;
                    num_removed++;
                    unknown.erase(var);
                }
                if (num_removed < 2) {
                    slow_mode = true;
                }
            }
        }

        cout
        << "[mis] iter: " << std::setw(8) << iter
        << " mode: " << (old_mode ? "slow" : "fast")
        << " ret: " << std::setw(8) << ret
        << " U: " << std::setw(7) << unknown.size()
        << " I: " << std::setw(7) << indep.size()
        << " N: " << std::setw(7) << not_indep
        << " Rem : " << std::setw(7) << num_removed
        << " T: "
        << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
        << endl;
        iter++;
    }
    cout
    << "[mis] Final indep: " << std::setw(7) << unknown.size()+indep.size()
    << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_iter_time)
    << endl;

    cout << "c ind ";
    for(const auto& var: unknown) {
        cout << var+1 << " ";
    }
    for(const auto& var: indep) {
        cout << var+1 << " ";
    }
    cout << "0" << endl;

    return 0;
}

