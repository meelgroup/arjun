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
#include <random>
#include <algorithm>
#include <map>
#include <set>
#include <vector>
#include "time_mem.h"
#include "GitSHA1.h"
#include "MersenneTwister.h"
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
string command_line;
CMSat::SATSolver* solver = NULL;
double startTime;
vector<uint32_t> sampling_set;
vector<Lit> tmp;
vector<char> seen;
uint32_t orig_num_vars;
uint32_t total_eq_removed = 0;
uint32_t total_set_removed = 0;
enum ModeType {one_mode, many_mode, inverse_mode};

struct Config {
    int verb = 0;
    int seed = 0;
    int bva = 1;
    int bve = 1;
    int simp_at_start = 1;
    int always_one_by_one = 0;
    int recompute_sampling_set = 0;
};

Config conf;
MTRand mtrand;

void remove_eq_literals(set<uint32_t>* unknown = NULL);
void remove_zero_assigned_literals(set<uint32_t>* unknown = NULL);
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
    ("bva", po::value(&conf.bva)->default_value(conf.bva), "bva")
    ("bve", po::value(&conf.bve)->default_value(conf.bve), "bve")
    ("one", po::value(&conf.always_one_by_one)->default_value(conf.always_one_by_one), "always one-by-one mode")
    ("simp", po::value(&conf.simp_at_start)->default_value(conf.simp_at_start), "simp at iter 0")
    ("recomp", po::value(&conf.recompute_sampling_set)->default_value(conf.recompute_sampling_set), "Recompute sampling set even if it's part of the CNF")
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

void update_and_print_sampling_vars(bool recompute)
{
    if (sampling_set.empty() || recompute) {
        if (recompute && !sampling_set.empty()) {
            cout << "[mis] WARNING: recomputing independent set even though" << endl;
            cout << "[mis]          a sampling/independent set was part of the CNF" << endl;
            cout << "[mis]          orig sampling set size: " << sampling_set.size() << endl;
        }

        if (sampling_set.empty()) {
            cout << "[mis] No sample set given, starting with full" << endl;
        }
        sampling_set.clear();
        for (size_t i = 0; i < solver->nVars(); i++) {
            sampling_set.push_back(i);
        }
    }

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
    cout << "[mis] Orig size         : " << sampling_set.size() << endl;
}

void add_fixed_clauses()
{
    vector<uint32_t> indic;

    //Indicator variable is TRUE when they are NOT equal
    for(uint32_t i: sampling_set) {
        //(a=b) = !f
        //a  V -b V  f
        //-a V  b V  f
        //a  V  b V -f
        //-a V -b V -f
        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        //torem_orig.push_back(Lit(this_indic, false));
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
    assert(indic.size() == sampling_set.size());
    tmp.clear();
    for(uint32_t var: indic) {
        tmp.push_back(Lit(var, false));
    }
    solver->add_clause(tmp);
}

void fill_assumptions(
    vector<Lit>& assumptions,
    const set<uint32_t>& unknown,
    const vector<uint32_t>& indep,
    map<uint32_t, uint32_t>& testvar_to_assump
)
{
    assumptions.clear();

    //Add unknown as assumptions
    for(const auto& var: unknown) {
        uint32_t ass = testvar_to_assump[var];
        if (!seen[ass]) {
            seen[ass] = 1;
            assumptions.push_back(Lit(ass, true));
        }
    }

    //Add known independent as assumptions
    for(const auto& var: indep) {
        uint32_t ass = testvar_to_assump[var];
        if (!seen[ass]) {
            seen[ass] = 1;
            assumptions.push_back(Lit(ass, true));
        }
    }

    //clear seen
    for(const auto& x: assumptions) {
        seen[x.var()] = 0;
    }
}

uint32_t fill_assumptions2(
    vector<Lit>& assumptions,
    const vector<uint32_t>& indep,
    map<uint32_t, uint32_t>& testvar_to_assump,
    map<uint32_t, vector<uint32_t>>& assump_to_testvars,
    uint32_t index
)
{
    assumptions.clear();

    //Add unknown as assumptions

    vector<uint32_t> ass_select;
    for(const auto& x: assump_to_testvars) {
        ass_select.push_back(x.first);
    }
    std::sort(ass_select.begin(), ass_select.end());
    uint32_t ass = ass_select.at(index);
    seen[ass] = 1;
    assumptions.push_back(Lit(ass, true));

    //Add known independent as assumptions
    for(const auto& var: indep) {
        uint32_t ass_indep = testvar_to_assump[var];
        if (!seen[ass_indep]) {
            seen[ass_indep] = 1;
            assumptions.push_back(Lit(ass_indep, true));
        }
    }

    //clear seen
    for(const auto& x: assumptions) {
        seen[x.var()] = 0;
    }

    return ass;
}

vector<uint32_t> one_round(uint32_t by, bool only_inverse)
{
    double start_round_time = cpuTimeTotal();
    //start with empty independent set
    vector<uint32_t> indep;

    //testvar_to_assump:
    //FIRST is variable we want to test for
    //SECOND is what we have to assumoe (in negative)
    map<uint32_t, uint32_t> testvar_to_assump;
    map<uint32_t, vector<uint32_t>> assump_to_testvars;
    vector<Lit> all_assumption_lits;
    for(uint32_t i = 0; i < sampling_set.size();) {
        solver->new_var();
        const uint32_t ass = solver->nVars()-1;
        all_assumption_lits.push_back(Lit(ass, false));

        vector<uint32_t> vars;
        for(uint32_t i2 = 0; i2 < by && i < sampling_set.size(); i2++, i++) {
            uint32_t var = sampling_set[i];

            tmp.clear();
            tmp.push_back(Lit(ass, false));
            tmp.push_back(Lit(var, false));
            tmp.push_back(Lit(var+orig_num_vars, true));
            solver->add_clause(tmp);

            tmp[1] = ~tmp[1];
            tmp[2] = ~tmp[2];
            solver->add_clause(tmp);
            testvar_to_assump[var] = ass;
            vars.push_back(var);
        }
        assump_to_testvars[ass] = vars;
    }
    assert(testvar_to_assump.size() == sampling_set.size());

    //Initially, all of samping_set is unknown
    set<uint32_t> unknown;
    unknown.insert(sampling_set.begin(), sampling_set.end());
    cout << "[mis] Start unknown size: " << unknown.size() << endl;

    seen.clear();
    seen.resize(solver->nVars(), 0);
    vector<Lit> assumptions;

    uint32_t iter = 0;
    ModeType one_by_one_mode = conf.always_one_by_one ? one_mode : many_mode;
    if (only_inverse) {
        one_by_one_mode = inverse_mode;
    }
    uint32_t num_fast = 0;
    uint32_t not_indep = 0;
    bool inverse_won = false;
    while(
        (!only_inverse && !unknown.empty())
        || (only_inverse && iter < assump_to_testvars.size())
    ) {
        if (one_by_one_mode == many_mode) {
            if (iter % 100 == 0 ||  iter < 1) {
                num_fast ++;
            } else {
                one_by_one_mode = one_mode;
            }
        }
        if (conf.always_one_by_one) {
            one_by_one_mode = one_mode;
        }
        if (only_inverse) {
            one_by_one_mode = inverse_mode;
        }

        auto old_one_by_one_mode = one_by_one_mode;

        uint32_t test_var = var_Undef;
        if (one_by_one_mode == one_mode) {
            //TODO improve
            vector<uint32_t> pick;
            for(const auto& unk_v: unknown) {
                pick.push_back(unk_v);
            }
            test_var = pick[mtrand.randInt(pick.size()-1)];
            test_var = pick[pick.size()-1];

            assert(testvar_to_assump.find(test_var) != testvar_to_assump.end());
            uint32_t ass = testvar_to_assump[test_var];
            assert(assump_to_testvars.find(ass) != assump_to_testvars.end());
            const auto& vars = assump_to_testvars[ass];
            for(uint32_t var: vars) {
                unknown.erase(var);
            }
        }

        uint32_t inverse_ass = var_Undef;
        if (one_by_one_mode == inverse_mode) {
            inverse_ass = fill_assumptions2(assumptions, indep, testvar_to_assump, assump_to_testvars, iter);
        } else {
            fill_assumptions(assumptions, unknown, indep, testvar_to_assump);
        }

        double myTime = cpuTime();
        //std::random_shuffle(assumptions.begin(), assumptions.end());
        /*cout << "ass: ";
        for(uint32_t i = 0; i < assumptions.size(); i ++) {
            cout << assumptions[i] << " ";
        }
        cout << "0" << endl;*/
        if (one_by_one_mode == inverse_mode) {
            //solver->set_max_confl(10000);
        }
        lbool ret = solver->solve(&assumptions);
        if (ret == l_Undef) {
            assert(one_by_one_mode == inverse_mode);
        }

        if (ret == l_True) {
            //Independent
            assert(one_by_one_mode == one_mode || one_by_one_mode == inverse_mode);
            if (one_by_one_mode == one_mode) {
                uint32_t ass = testvar_to_assump[test_var];
                const auto& vars = assump_to_testvars[ass];
                for(uint32_t var: vars) {
                    indep.push_back(var);
                }
            }
        } else if (ret == l_False) {
            if (one_by_one_mode == one_mode) {
                //not independent
                uint32_t var = test_var;
                uint32_t ass = testvar_to_assump[var];
                tmp.clear();
                tmp.push_back(Lit(ass, false));
                solver->add_clause(tmp);
                not_indep += assump_to_testvars[ass].size();
            } else if (one_by_one_mode == many_mode) {
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
                //cout << "not in reason size: " << not_in_reason.size() << endl;

                //not independent.
                for(uint32_t ass: not_in_reason) {
                    assert(assump_to_testvars.find(ass) != assump_to_testvars.end());
                    const auto& vars = assump_to_testvars[ass];

                    //Remove from unknown
                    for(uint32_t var: vars) {
                        not_indep++;
                        unknown.erase(var);
                    }

                    //Remove from solver
                    tmp.clear();
                    assert(testvar_to_assump[vars[0]] == ass);
                    tmp.push_back(Lit(testvar_to_assump[vars[0]], false));
                    solver->add_clause(tmp);
                }
                //cout << "fin unknown size: " << unknown.size() << endl;
            } else {
                assert(one_by_one_mode == inverse_mode);
                cout << "WINNER" << endl;
                inverse_won = true;
                assert(assump_to_testvars.find(inverse_ass) != assump_to_testvars.end());
                const auto& vars = assump_to_testvars[inverse_ass];
                uint32_t old_size = unknown.size();
                unknown.clear();
                unknown.insert(vars.begin(), vars.end());
                cout << "After unknown size: " << unknown.size() << endl;
                not_indep += old_size - unknown.size();
                break;
            }
        }

        cout
        << "[mis] iter: " << std::setw(8) << iter
        << " mode: "
        << (old_one_by_one_mode==one_mode ? "one " :
        ((old_one_by_one_mode==many_mode) ? "many" : "inv " ))
        << " ret: " << std::setw(8) << ret
        << " U: " << std::setw(7) << unknown.size()
        << " I: " << std::setw(7) << indep.size()
        << " N: " << std::setw(7) << not_indep
        << " T: "
        << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
        << endl;
        iter++;
    }
    cout << "[mis] one_round finished T: "
    << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
    << endl;

    //clear clauses to do with assumptions
    for(const auto& lit: all_assumption_lits) {
        tmp.clear();
        tmp.push_back(lit);
        solver->add_clause(tmp);
    }

    vector<uint32_t> final_indep;
    for(const auto& var: unknown) {
        final_indep.push_back(var);
    }
    for(const auto& var: indep) {
        final_indep.push_back(var);
    }
    return final_indep;
}

void simp()
{
    if (conf.simp_at_start) {
        double simp_time = cpuTime();
        cout << "[mis] Simplifying..." << endl;
        solver->simplify();
        remove_eq_literals(NULL);
        remove_zero_assigned_literals(NULL);
        cout << "[mis] Simplify finished. T: " << (cpuTime() - simp_time) << endl;
    }
}

void remove_zero_assigned_literals(set<uint32_t>* unknown)
{
    //Remove zero-assigned literals
    seen.clear();
    seen.resize(solver->nVars(), 0);
    uint32_t orig_sampling_set_size = sampling_set.size();
    for(auto x: sampling_set) {
        seen[x] = 1;
    }
    const auto zero_ass = solver->get_zero_assigned_lits();
    for(Lit l: zero_ass) {
        seen[l.var()] = 0;
    }
    sampling_set.clear();
    for(uint32_t i = 0; i < seen.size(); i++) {
        if (seen[i]) {
            sampling_set.push_back(i);
            seen[i] = 0;
        } else {
            if (unknown) {
                unknown->erase(i);
            }
        }
    }
    if (orig_sampling_set_size - sampling_set.size() > 0) {
        total_set_removed += orig_sampling_set_size - sampling_set.size();
        cout << "[mis] Removed set       : "
        << (orig_sampling_set_size - sampling_set.size()) << endl;
    }
}

void remove_eq_literals(set<uint32_t>* unknown)
{
    seen.clear();
    seen.resize(solver->nVars(), 0);
    uint32_t orig_sampling_set_size = sampling_set.size();
    for(auto x: sampling_set) {
        seen[x] = 1;
    }
    const auto zero_ass = solver->get_all_binary_xors();
    for(auto mypair: zero_ass) {
        //Only remove if both are sampling vars
        if (seen[mypair.second.var()] == 1 && seen[mypair.first.var()] == 1) {
            //Doesn't matter which one to remove
            seen[mypair.second.var()] = 0;
        }
    }
    sampling_set.clear();
    for(uint32_t i = 0; i < seen.size(); i++) {
        if (seen[i]) {
            sampling_set.push_back(i);
            seen[i] = 0;
        } else {
            if (unknown) unknown->erase(i);
        }
    }

    total_eq_removed += orig_sampling_set_size - sampling_set.size();
    if (orig_sampling_set_size - sampling_set.size() > 0) {
        cout << "[mis] Removed equivalent: "
        << (orig_sampling_set_size - sampling_set.size())
        << endl;
    }

}

void init_solver_setup()
{
    double myTime = cpuTime();
    solver = new SATSolver();
    if (conf.verb > 2) {
        solver->set_verbosity(conf.verb-2);
    }

    //parsing the input
    if (vm.count("input") == 0) {
        cout << "ERROR: you must pass a file" << endl;
    }
    const string inp = vm["input"].as<string>();

    //Read in file and set sampling_set in case we are starting with empty
    readInAFile(inp.c_str(), 0, sampling_set.empty());
    update_and_print_sampling_vars(conf.recompute_sampling_set);
    remove_zero_assigned_literals();


    //Read in file again, with offset
    orig_num_vars = solver->nVars();
    readInAFile(inp.c_str(), orig_num_vars, false);

    //Set up solver
    if (!conf.bva) {
        solver->set_no_bve();
    }
    if (!conf.bve) {
        solver->set_no_bva();
    }
    solver->set_up_for_scalmc();
    //solver->set_verbosity(2);

    //Print stats
    add_fixed_clauses();
    cout << "[mis] Setup time: " << (cpuTime()-myTime) << endl;
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
    cout << "[mis] Version: " << get_version_sha1() << endl;
    cout
    << "c executed with command line: "
    << command_line
    << endl;
    cout << "[mis] using seed: " << conf.seed << endl;

    double starTime = cpuTime();
    mtrand.seed(conf.seed);
    init_solver_setup();

    if (false) {
        uint32_t guess_indep = std::max<uint32_t>(sampling_set.size()/20, 50);
        simp();
        sampling_set = one_round(guess_indep, true);
    }

    uint32_t prev_size = sampling_set.size()*100;
    uint32_t num;
    while(true) {
        simp();
        if (sampling_set.size() < prev_size/2) {
            num = sampling_set.size()/10;
        } else {
            num = num/5;
        }
        if (num < 5) {
            num = 1;
        }
        prev_size = sampling_set.size();

        cout << "[mis] ===--> Doing a run for " << num << endl;
        sampling_set = one_round(num, false);
        if (num == 1) {
            break;
        }
    }

    cout
    << "[mis] Final indep: " << std::setw(7) << sampling_set.size()
    << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - starTime)
    << endl;

    cout << "c ind ";
    for(const auto& var: sampling_set) {
        cout << var+1 << " ";
    }
    cout << "0" << endl;

    delete solver;
    return 0;
}
