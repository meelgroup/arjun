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
vector<Lit> tmp;
vector<char> seen;
uint32_t orig_num_vars;
uint32_t total_eq_removed = 0;
uint32_t total_set_removed = 0;
uint32_t mult_or_invers_var;
enum ModeType {one_mode, many_mode};

//assert indic[var] to FASLE to force var==var+orig_num_vars
vector<uint32_t> var_to_indic; //maps an ORIG VAR to an INDICATOR VAR
vector<uint32_t> indic_to_var; //maps an INDICATOR VAR to ORIG VAR

vector<uint32_t> sampling_set_tmp1;
vector<uint32_t> sampling_set_tmp2;
vector<uint32_t> guess_set_tmp;
vector<uint32_t>* sampling_set = NULL;
vector<uint32_t>* guess_assumption_set = NULL;
vector<uint32_t>* other_sampling_set = NULL;
map<uint32_t, vector<uint32_t>> global_assump_to_testvars;
vector<uint32_t> incidence;
vector<double> vsids_scores;
vector<Lit> dont_elim;
vector<uint32_t> this_indic2;
void run_guess();
void init_solver_setup(bool init_sampling);

struct Config {
    int verb = 0;
    int seed = 0;
    int bva = 0;
    int bve = 1;
    int guess = 1;
    int force_by_one = 1;
    int simp_at_start = 1;
    int always_one_by_one = 1;
    int recompute_sampling_set = 0;
    int backward_only = 0;
};

struct IncidenceSorter
{
    IncidenceSorter(const vector<uint32_t>& _inc) :
        inc(_inc)
    {}

    bool operator()(const uint32_t a, const uint32_t b) {
        return inc[a] > inc[b];
    }

    const vector<uint32_t>& inc;
};

struct VSIDSSorter
{
    VSIDSSorter(const vector<uint32_t>& _inc, const vector<double>& _vsids) :
        vsids(_vsids),
        inc(_inc)
    {}

    bool operator()(const uint32_t a, const uint32_t b) {
        if (inc[a] != inc[b]) {
            return inc[a] > inc[b];
        }
        return vsids[a] > vsids[b];
    }

    const vector<double>& vsids;
    const vector<uint32_t>& inc;
};

Config conf;
MTRand mtrand;

void print_indep_set()
{
    cout << "c ind ";
    for(const uint32_t s: *sampling_set) {
        cout << s+1 << " ";
    }
    cout << "0" << endl;

//     cout << "c inc ";
//     for(const uint32_t s: *sampling_set) {
//         cout << incidence[s] << " ";
//     }
//     cout << "0" << endl;

    cout << "c set size: " << std::setw(8)
    << sampling_set->size()
    << " fraction of original: "
    <<  std::setw(6) << std::setprecision(4)
    << (double)sampling_set->size()/(double)orig_num_vars
    << endl << std::flush;
}

static void signal_handler(int) {
    cout << endl << "*** INTERRUPTED ***" << endl << std::flush;
    print_indep_set();
    cout << endl << "*** INTERRUPTED ***" << endl << std::flush;
    exit(1);
}

void simp(vector<char>* unknown_set = NULL);
void remove_eq_literals(vector<char>* unknown_set = NULL);
void remove_zero_assigned_literals(vector<char>* unknown_set = NULL);
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
    ("guess", po::value(&conf.guess)->default_value(conf.guess), "Guess small set")
    ("one", po::value(&conf.always_one_by_one)->default_value(conf.always_one_by_one), "always one-by-one mode")
    ("simpstart", po::value(&conf.simp_at_start)->default_value(conf.simp_at_start), "simp at startup")
    ("recomp", po::value(&conf.recompute_sampling_set)->default_value(conf.recompute_sampling_set), "Recompute sampling set even if it's part of the CNF")
    ("byforce", po::value(&conf.force_by_one)->default_value(conf.force_by_one), "Force 1-by-1 query")
    ("backwardonly", po::value(&conf.backward_only)->default_value(conf.backward_only), "Only do backwards query")

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
        *sampling_set = parser.sampling_vars;
    }

    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}

void init_samping_set(bool recompute)
{
    if (sampling_set->empty() || recompute) {
        if (recompute && !sampling_set->empty()) {
            cout << "[mis] WARNING: recomputing independent set even though" << endl;
            cout << "[mis]          a sampling/independent set was part of the CNF" << endl;
            cout << "[mis]          orig sampling set size: " << sampling_set->size() << endl;
        }

        if (sampling_set->empty()) {
            cout << "[mis] No sample set given, starting with full" << endl;
        }
        sampling_set->clear();
        for (size_t i = 0; i < solver->nVars(); i++) {
            sampling_set->push_back(i);
        }
    }

    if (sampling_set->size() > 100) {
        cout
        << "[mis] Sampling var set contains over 100 variables, not displaying"
        << endl;
    } else {
        cout << "[mis] Sampling set: ";
        for (auto v: *sampling_set) {
            cout << v+1 << ", ";
        }
        cout << endl;
    }
    cout << "[mis] Orig size         : " << sampling_set->size() << endl;
}

void add_fixed_clauses()
{
    dont_elim.clear();
    var_to_indic.clear();
    var_to_indic.resize(orig_num_vars, var_Undef);
    indic_to_var.clear();
    indic_to_var.resize(solver->nVars(), var_Undef);

    //Indicator variable is TRUE when they are NOT equal
    for(uint32_t var: *sampling_set) {
        //(a=b) = !f
        //a  V -b V  f
        //-a V  b V  f
        //a  V  b V -f
        //-a V -b V -f
        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        //torem_orig.push_back(Lit(this_indic, false));
        var_to_indic[var] = this_indic;
        dont_elim.push_back(Lit(this_indic, false));
        indic_to_var.resize(this_indic+1, var_Undef);
        indic_to_var[this_indic] = var;

        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,      false));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,      false));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,      true));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,      true));
        solver->add_clause(tmp);
    }

    //OR together the indicators: one of them must NOT be equal
    //indicator tells us when they are NOT equal. One among them MUST be NOT equal
    //hence at least one indicator variable must be TRUE
    tmp.clear();
    solver->new_var();
    mult_or_invers_var = solver->nVars()-1;
    dont_elim.push_back(Lit(mult_or_invers_var, false));
    tmp.push_back(Lit(mult_or_invers_var, false));
    for(uint32_t var = 0; var < var_to_indic.size(); var++) {
        uint32_t indic = var_to_indic[var];
        if (indic == var_Undef)
            continue;

        tmp.push_back(Lit(indic, false));
    }
    solver->add_clause(tmp);



    this_indic2.clear();
    this_indic2.resize(orig_num_vars, var_Undef);
    vector<Lit> tmp_one;
    for(uint32_t var: *sampling_set) {
        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        dont_elim.push_back(Lit(this_indic, false));

        tmp.clear();
        tmp.push_back(Lit(var, false));
        tmp.push_back(Lit(this_indic, true));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic, true));
        solver->add_clause(tmp);

        this_indic2[var] = this_indic;
        tmp_one.push_back(Lit(this_indic, false));
    }
    solver->add_clause(tmp_one);

    for(uint32_t i = 0; i < orig_num_vars; i ++) {
        dont_elim.push_back(Lit(i, false));
        dont_elim.push_back(Lit(i+orig_num_vars, false));
    }
}

void fill_assumptions_backward(
    vector<Lit>& assumptions,
    vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const vector<uint32_t>& indep
)
{
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);

        uint32_t ass_var = var_to_indic[var];
        assert(ass_var != var_Undef);
        assumptions.push_back(Lit(ass_var, true));
    }
    //Add unknown as assumptions, clean "unknown"
    uint32_t j = 0;
    std::sort(unknown.begin(), unknown.end(), IncidenceSorter(incidence));
    for(uint32_t i = 0; i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        if (unknown_set[var] == 0) {
            continue;
        } else {
            unknown[j++] = var;
        }

        assert(var < orig_num_vars);
        uint32_t ass_var = var_to_indic[var];
        assert(ass_var != var_Undef);
        assumptions.push_back(Lit(ass_var, true));
    }
    unknown.resize(j);
}

void fill_assumptions_inv(
    vector<Lit>& assumptions,
    const vector<uint32_t>& indep,
    const vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    uint32_t group,
    uint32_t offs,
    uint32_t index,
    vector<char>& dontremove_vars
)
{
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        //assumptions.push_back(Lit(this_indic2[var], true)); //Shouldn't this be false?
        uint32_t ass = var_to_indic[var];
        if (!seen[ass]) {
            seen[ass] = 1;
            assumptions.push_back(Lit(ass, true));
            dontremove_vars[var] = 1;
        }
    }

    for(uint32_t i = group*offs; i < group*(offs+index+1) && i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        assert(var < orig_num_vars);
        if (unknown_set[var]) {
            uint32_t ass = var_to_indic[var];
            if (!seen[ass]) {
                seen[ass] = 1;
                assumptions.push_back(Lit(ass, true));
                dontremove_vars[var] = 1;
            }
        }
    }

    //clear seen
    for(const auto& x: assumptions) {
        seen[x.var()] = 0;
    }
}

void fill_assumptions_forward(
    vector<Lit>& assumptions,
    const vector<uint32_t>& indep,
    vector<uint32_t>& unknown,
    uint32_t group,
    uint32_t offs,
    vector<char>& guess_set
)
{
    assumptions.clear();
    for(auto& x: seen) {
        assert(x == 0);
    }

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);
        uint32_t ass = var_to_indic[var];
        assert(ass != var_Undef);
        if (!seen[ass]) {
            seen[ass] = 1;
            assumptions.push_back(Lit(ass, true));
        }
    }

    for(uint32_t i = group*offs; i < group*(offs+1) && i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        assert(var < orig_num_vars);
        if (guess_set[var]) {
            uint32_t ass = var_to_indic[var];
            if (!seen[ass]) {
                seen[ass] = 1;
                assumptions.push_back(Lit(ass, true));
            }
        }
    }

    //clear seen
    for(const auto& var: unknown) {
        uint32_t ass = var_to_indic[var];
        seen[ass] = 0;
    }

    for(const auto& var: indep) {
        uint32_t ass = var_to_indic[var];
        seen[ass] = 0;
    }
}

void set_guess_forward_round(
    const vector<uint32_t>& indep,
    vector<uint32_t>& unknown,
    vector<char>& unknown_set,
    uint32_t group,
    uint32_t offs,
    vector<char>& guess_set
)
{
    for(auto& x: seen) {
        x = 0;
    }

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);
        uint32_t ass = var_to_indic[var];
        assert(ass != var_Undef);
        if (!seen[ass]) {
            seen[ass] = 1;
        }
    }

    for(uint32_t i = group*offs; i < group*(offs+1) && i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        assert(var < orig_num_vars);
        if (unknown_set[var]) {
            unknown_set[var] = 0;
            uint32_t ass = var_to_indic[var];
            if (!seen[ass]) {
                seen[ass] = 1;
                guess_set[var] = 1;
            }
        }
    }

    //clear seen
    for(auto& x: seen) {
        x = 0;
    }
}

void update_sampling_set(
    const vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const vector<uint32_t>& indep
)
{
    other_sampling_set->clear();
    for(const auto& var: unknown) {
        if (unknown_set[var]) {
            other_sampling_set->push_back(var);
        }
    }
    for(const auto& var: indep) {
        other_sampling_set->push_back(var);
    }
    //TODO: atomic swap
    std::swap(sampling_set, other_sampling_set);
}

void re_sort(vector<uint32_t>* pick_possibilities = NULL)
{
    assert(false);
    incidence = solver->get_var_incidence();
    vsids_scores = solver->get_vsids_scores();
    if (pick_possibilities) {
        std::sort(pick_possibilities->begin(),
                  pick_possibilities->end(),
                  VSIDSSorter(incidence, vsids_scores));

//         std::sort(pick_possibilities->begin(),
//                   pick_possibilities->end(),
//                   IncidenceSorter(incidence));
    }
    cout << "Re-sorted" << endl;
}

bool backward_round(uint32_t max_iters = std::numeric_limits<uint32_t>::max())
{
    for(const auto& x: seen) {
        assert(x == 0);
    }

    double start_round_time = cpuTimeTotal();
    //start with empty independent set
    vector<uint32_t> indep;

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    vector<char> unknown_set;
    unknown_set.resize(orig_num_vars, 0);
    for(const auto& x: *sampling_set) {
        unknown.push_back(x);
        unknown_set[x] = 1;
    }
    cout << "[mis] Start unknown size: " << unknown.size() << endl;

    vector<Lit> assumptions;
    uint32_t iter = 0;
    ModeType mode_type = conf.always_one_by_one ? one_mode : many_mode;
    uint32_t not_indep = 0;

    double myTime = cpuTime();
    vector<char> tried_var_already;
    tried_var_already.resize(orig_num_vars, 0);

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_set->size()) > 20 ) {
        uint32_t will_do_iters = sampling_set->size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }

    vector<uint32_t> pick_possibilities;
    pick_possibilities.reserve(unknown.size());
    for(const auto& unk_v: unknown) {
        pick_possibilities.push_back(unk_v);
    }
    std::sort(pick_possibilities.begin(), pick_possibilities.end(), IncidenceSorter(incidence));

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    bool quick_pop_ok = false;
    while(iter < max_iters) {
        if (iter % 500 == 0) {
            mode_type = many_mode;
        } else {
            mode_type = one_mode;
        }
        //quick_pop_ok = false;

        if (conf.always_one_by_one) {
            mode_type = one_mode;
        }

        auto old_mode_type = mode_type;

        uint32_t test_var = var_Undef;
        if (mode_type == one_mode) {
            if (quick_pop_ok) {
                //Remove 2 last
                assumptions.pop_back();
                assumptions.pop_back();

                //No more left, try again with full
                if (assumptions.empty()) {
                    quick_pop_ok = false;
                    continue;
                }

                uint32_t ass_var = assumptions[assumptions.size()-1].var();
                assumptions.pop_back();
                assert(ass_var < indic_to_var.size());
                test_var = indic_to_var[ass_var];
                assert(test_var != var_Undef);
                assert(test_var < orig_num_vars);

                //Something is odd, try again with full
                if (!unknown_set[test_var]) {
                    test_var = var_Undef;
                    quick_pop_ok = false;
                    continue;
                }
                uint32_t last_unkn = unknown[unknown.size()-1];
                assert(last_unkn == test_var);
                unknown.pop_back();
            } else {
                for(int i = pick_possibilities.size()-1; i>= 0; i--) {
                    uint32_t var = pick_possibilities[i];
                    if (!tried_var_already[var] && unknown_set[var]) {
                        test_var = pick_possibilities[i];
                        break;
                    } else {
                        pick_possibilities.pop_back();
                    }
                }
                if (test_var == var_Undef) {
                    break;
                }
            }
            assert(test_var < orig_num_vars);
            assert(unknown_set[test_var] == 1);
            unknown_set[test_var] = 0;
            tried_var_already[test_var] = 1;
        }

        //Assumption filling
        if (mode_type == many_mode) {
            fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
            assumptions.push_back(Lit(mult_or_invers_var, true));
        }
        else if (mode_type == one_mode) {
            assert(test_var != var_Undef);
            if (!quick_pop_ok) {
                fill_assumptions_backward(assumptions, unknown, unknown_set, indep);
                assumptions.push_back(Lit(test_var, false));
                assumptions.push_back(Lit(test_var + orig_num_vars, true));
            } else {
                assumptions.push_back(Lit(test_var, false));
                assumptions.push_back(Lit(test_var + orig_num_vars, true));
            }
        }
        quick_pop_ok = false;

        solver->set_max_confl(500);
        if (mode_type == one_mode) {
            solver->set_no_confl_needed();
        }

        lbool ret = l_Undef;
        ret = solver->solve(&assumptions);
        if (ret == l_False) {
            ret_false++;
        } else if (ret == l_True) {
            ret_true++;
        } else if (ret == l_Undef) {
            ret_undef++;
        }

        if (ret == l_Undef) {
            if (mode_type == one_mode) {
                assert(test_var < orig_num_vars);
                assert(unknown_set[test_var] == 0);
                unknown_set[test_var] = 1;
                unknown.push_back(test_var);
            }
        } else if (ret == l_True) {
            //Independent
            assert(mode_type == one_mode);
            if (mode_type == one_mode) {
                indep.push_back(test_var);
            }
        } else if (ret == l_False) {
            if (mode_type == one_mode) {
                //not independent
                not_indep++;
                quick_pop_ok = true;
            } else if (mode_type == many_mode) {
                vector<Lit> reason = solver->get_conflict();
                for(Lit l: reason) {
                    seen[l.var()] = 1;
                }
                vector<uint32_t> not_in_reason;
                for(Lit l: assumptions) {
                    if (!seen[l.var()]) {
                        not_in_reason.push_back(l.var());
                    }
                }
                for(Lit l: reason) {
                    seen[l.var()] = 0;
                }

                //not independent.
                for(uint32_t ass: not_in_reason) {
                    if (ass >= indic_to_var.size()
                        || indic_to_var[ass] == var_Undef
                    ) {
                        continue;
                    }
                    uint32_t var = indic_to_var[ass];
                    not_indep++;
                    unknown_set[var] = 0;

                    //Remove from solver
                    tmp.clear();
                    tmp.push_back(Lit(ass, false));
                    solver->add_clause(tmp);
                }
            }
        }

        if (iter % mod == (mod-1)) {
            cout
            << "[mis] iter: " << std::setw(5) << iter;
            if (mod == 1) {
                cout << " mode: "
                << (old_mode_type==one_mode ? "one " :
                ((old_mode_type==many_mode) ? "many" : "inv " ))
                << " ret: " << std::setw(8) << ret;
            } else {
                cout
                << " T/F/U: ";
                std::stringstream ss;
                ss << ret_true << "/" << ret_false << "/" << ret_undef;
                cout << std::setw(10) << std::left << ss.str() << std::right;
                ret_true = 0;
                ret_false = 0;
                ret_undef = 0;
            }
            cout
            << " by: " << std::setw(3) << 1
            << " U: " << std::setw(7) << unknown.size()
            << " I: " << std::setw(7) << indep.size()
            << " N: " << std::setw(7) << not_indep
            << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
            << endl;
            myTime = cpuTime();

        }
        iter++;

        if (iter % 500 == 499) {
            update_sampling_set(unknown, unknown_set, indep);
        }
    }
    update_sampling_set(unknown, unknown_set, indep);
    cout << "[mis] backward_round finished T: "
    << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
    << endl;

    return iter < max_iters;
}


uint32_t guess_remove_and_update_ass(
    vector<Lit>& assumptions,
    vector<char>& unknown_set,
    vector<char>& dontremove_vars)
{
    uint32_t removed = 0;
    seen.resize(solver->nVars(), 0);

    vector<Lit> prop = solver->propagated_by(assumptions);

    //Anything that's remaining, remove
    for(const Lit p: prop) {
        uint32_t ind = p.var();
        if (p.sign() == false ||
            ind >= indic_to_var.size() ||
            indic_to_var[ind] == var_Undef)
        {
            continue;
        }
        uint32_t var = indic_to_var[ind];

        //Setting them to be dependent
        if (!dontremove_vars[var] && unknown_set[var]) {
            unknown_set[var] = 0;
            assumptions.push_back(Lit(ind, true));
            dontremove_vars[var] = 1;
            removed++;
        }
    }

    return removed;
}

void guess_round(
    uint32_t group,
    bool reverse = false,
    bool shuffle = false,
    int offset = 0)
{
    for(const auto& x: seen) {
        assert(x == 0);
    }

    if (offset >= sampling_set->size()/group) {
        return;
    }

    double start_round_time = cpuTimeTotal();
    //start with empty independent set
    vector<uint32_t> indep;

    seen.resize(solver->nVars(), 0);

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    vector<char> unknown_set;
    unknown_set.resize(orig_num_vars, 0);
    for(const auto& x: *sampling_set) {
        unknown.push_back(x);
        unknown_set[x] = 1;
    }
    cout << "[mis] Start unknown size: " << unknown.size() << endl;

    vector<Lit> assumptions;

    uint32_t iter = 0;
    uint32_t removed = 0;
    double myTime = cpuTime();
    vector<char> tried_var_already;
    tried_var_already.resize(orig_num_vars, 0);

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_set->size()/group) > 20 ) {
        uint32_t will_do_iters = (sampling_set->size()/group);
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }
    vector<char> dontremove_vars(orig_num_vars, 0);

    std::sort(unknown.begin(), unknown.end(), IncidenceSorter(incidence));
    if (reverse) {
        std::reverse(unknown.begin(), unknown.end());
    }
    if (shuffle) {
        std::random_shuffle(unknown.begin(), unknown.end());
    }

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    bool should_continue_guess = true;
    uint32_t tot_removed = 0;
    while(iter < 5) {
        should_continue_guess = false;

        //Assumption filling
        if (iter < 5) {
            fill_assumptions_inv(
                assumptions,
                indep,
                unknown,
                unknown_set,
                group,
                offset,
                iter,
                dontremove_vars
            );
            assumptions.push_back(Lit(mult_or_invers_var, true));
        }

        solver->set_max_confl(100);
        removed = guess_remove_and_update_ass(
            assumptions, unknown_set, dontremove_vars);

        tot_removed += removed;

        if (iter % mod == (mod-1)) {
            cout
            << "[mis] iter: " << std::setw(5) << iter;
            cout << " mode: guess ";
            cout
            << " Test: " << std::setw(7) << assumptions.size()
            << " Rem: " << std::setw(7) << tot_removed
            << " U: " << std::setw(7) << unknown.size()
            << " I: " << std::setw(7) << indep.size()
            << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
            << endl;
            myTime = cpuTime();
            tot_removed = 0;
        }
        iter++;
    }
    update_sampling_set(unknown, unknown_set, indep);
    cout << "[mis] backward_round finished T: "
    << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
    << endl;
}

bool forward_round(
    uint32_t max_iters = std::numeric_limits<uint32_t>::max(),
    uint32_t group = 1,
    bool reverse = false,
    bool shuffle = false,
    int offset = 0)
{
    for(const auto& x: seen) {
        assert(x == 0);
    }

    double start_round_time = cpuTimeTotal();
    //start with empty independent set
    vector<uint32_t> indep;
    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    vector<char> unknown_set;
    unknown_set.resize(orig_num_vars, 0);
    for(const auto& x: *sampling_set) {
        unknown.push_back(x);
        unknown_set[x] = 1;
    }

    vector<Lit> assumptions;
    uint32_t iter = 0;
    uint32_t not_indep = 0;

    double myTime = cpuTime();
    vector<char> tried_var_already;
    tried_var_already.resize(orig_num_vars, 0);

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_set->size()) > 20 ) {
        uint32_t will_do_iters = sampling_set->size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }
    std::sort(unknown.begin(), unknown.end(), IncidenceSorter(incidence));
    if (reverse) {
        std::reverse(unknown.begin(), unknown.end());
    }
    if (shuffle) {
        std::random_shuffle(unknown.begin(), unknown.end());
    }
    vector<char> guess_set(orig_num_vars, 0);

    vector<uint32_t> pick_possibilities;
    for(const auto& unk_v: unknown) {
        if (unknown_set[unk_v]){
            pick_possibilities.push_back(unk_v);
        }
    }
    std::sort(pick_possibilities.begin(), pick_possibilities.end(), IncidenceSorter(incidence));
    cout << "[mis] Start unknown size: " << pick_possibilities.size() << endl;

    set_guess_forward_round(
        indep,
        unknown,
        unknown_set,
        group,
        offset,
        guess_set
    );

    fill_assumptions_forward(
        assumptions,
        indep,
        unknown,
        group,
        offset,
        guess_set
    );
//     for(const auto& a: assumptions) {
//         tmp.clear();
//         tmp.push_back(a);
//         solver->add_clause(tmp);
//     }
//     assumptions.clear();

    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    uint32_t prev_test_var = var_Undef;
    while(iter < max_iters) {
        //Select var
        uint32_t test_var = var_Undef;
        for(int i = pick_possibilities.size()-1; i>= 0; i--) {
            uint32_t var = pick_possibilities[i];
            if (!tried_var_already[var] && unknown_set[var] && !guess_set[var]) {
                test_var = pick_possibilities[i];
                break;
            } else {
                pick_possibilities.pop_back();
            }
        }
        if (test_var == var_Undef) {
            break;
        }
        assert(test_var < orig_num_vars);
        assert(unknown_set[test_var] == 1);
        unknown_set[test_var] = 0;
        assert(guess_set[test_var] == 0);
        tried_var_already[test_var] = 1;

        //Assumption filling: with guess_set that is in range + indep
        assert(test_var != var_Undef);

        //Remove old
        if (iter != 0) {
            assumptions.pop_back();
            assumptions.pop_back();

            //in case of DEP: This is just an optimization, to add the dependent var
            //in case of INDEP: This is needed.
            uint32_t ass = var_to_indic[prev_test_var];
            assert(ass != var_Undef);
            assert(!seen[ass]);
//             tmp.clear();
//             tmp.push_back(Lit(ass, true));
//             solver->add_clause(tmp);
            assumptions.push_back(Lit(ass, true));
        }

        //Add new one
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_max_confl(50);
        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        ret = solver->solve(&assumptions);
        if (ret == l_False) {
            ret_false++;
        } else if (ret == l_True) {
            ret_true++;
        } else if (ret == l_Undef) {
            ret_undef++;
        }

        if (ret == l_Undef || ret == l_True) {
            assert(test_var < orig_num_vars);
            assert(unknown_set[test_var] == 0);
            indep.push_back(test_var);
        } else if (ret == l_False) {
            //not independent
            not_indep++;
            //TODO: In the forward pass, even when the variable is not independent, we can still add it to the assumptions
        }

        if (iter % mod == (mod-1)) {
            cout
            << "[mis] iter: " << std::setw(5) << iter;
            if (mod == 1) {
                cout << " mode: "
                << " guess one "
                << " ret: " << std::setw(8) << ret;
            } else {
                cout
                << " T/F/U: ";
                std::stringstream ss;
                ss << ret_true << "/" << ret_false << "/" << ret_undef;
                cout << std::setw(10) << std::left << ss.str() << std::right;
                ret_true = 0;
                ret_false = 0;
                ret_undef = 0;
            }
            cout
            << " by: " << std::setw(3) << 1
            << " U: " << std::setw(7) << unknown.size()
            << " I: " << std::setw(7) << indep.size()
            << " N: " << std::setw(7) << not_indep
            << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
            << endl;
            myTime = cpuTime();

        }
        iter++;
        prev_test_var = test_var;
    }

    for (uint32_t var =0; var < orig_num_vars; var++){
        if (guess_set[var]) {
            unknown_set[var] = 1;
            unknown.push_back(var);
        }
    }
    for (auto var: indep) {
        if (!unknown_set[var]) {
            unknown.push_back(var);
            unknown_set[var] = 1;
        }
    }
    indep.clear();

    update_sampling_set(unknown, unknown_set, indep);
    cout << "[mis] backward_round finished T: "
    << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
    << endl;

    //we messed up the solver, re-init please
    //init_solver_setup(false);
    return iter < max_iters;
}
void simp(vector<char>* unknown_set)
{
    if (conf.simp_at_start) {
        double simp_time = cpuTime();
        cout << "[mis] Simplifying..." << endl;
        solver->simplify(&dont_elim);
        remove_eq_literals(unknown_set);
        remove_zero_assigned_literals(unknown_set);
        cout << "[mis] Simplify finished. T: " << (cpuTime() - simp_time) << endl;
        //incidence = solver->get_var_incidence();
    }
}

void remove_zero_assigned_literals(vector<char>* unknown_set)
{
    //Remove zero-assigned literals
    seen.clear();
    seen.resize(solver->nVars(), 0);

    *other_sampling_set = *sampling_set;
    uint32_t orig_sampling_set_size = other_sampling_set->size();
    for(auto x: *other_sampling_set) {
        //cout << "x:" << x << " orig_num_vars: " << orig_num_vars << endl;
        seen[x] = 1;
    }
    const auto zero_ass = solver->get_zero_assigned_lits();
    for(Lit l: zero_ass) {
        seen[l.var()] = 0;
        if (unknown_set && l.var() < orig_num_vars) {
            (*unknown_set)[l.var()] = 0;
        }
    }

    other_sampling_set->clear();
    for(uint32_t i = 0; i < seen.size() && i < orig_num_vars; i++) {
        if (seen[i]) {
            other_sampling_set->push_back(i);
        }
        seen[i] = 0;
    }
    //TODO atomic swap
    std::swap(sampling_set, other_sampling_set);

    total_set_removed += orig_sampling_set_size - sampling_set->size();
    cout << "[mis] Removed set       : "
    << (orig_sampling_set_size - sampling_set->size())
    << " new size: " << sampling_set->size()
    << endl;
}

void remove_eq_literals(vector<char>* unknown_set)
{
    seen.clear();
    seen.resize(solver->nVars(), 0);
    *other_sampling_set = *sampling_set;

    uint32_t orig_sampling_set_size = other_sampling_set->size();
    for(auto x: *other_sampling_set) {
        seen[x] = 1;
    }
    const auto zero_ass = solver->get_all_binary_xors();
    for(auto mypair: zero_ass) {
        //Only remove if both are sampling vars
        if (seen[mypair.second.var()] == 1 && seen[mypair.first.var()] == 1) {
            //Doesn't matter which one to remove
            seen[mypair.second.var()] = 0;
            if (unknown_set && mypair.second.var() < orig_num_vars) {
                (*unknown_set)[mypair.second.var()] = 0;
            }
        }
    }

    other_sampling_set->clear();
    for(uint32_t i = 0; i < seen.size() && i < orig_num_vars; i++) {
        if (seen[i]) {
            other_sampling_set->push_back(i);
        }
        seen[i] = 0;
    }
    //TODO atomic swap
    std::swap(sampling_set, other_sampling_set);

    total_eq_removed += orig_sampling_set_size - sampling_set->size();

    cout << "[mis] Removed equivalent: "
    << (orig_sampling_set_size - sampling_set->size())
    << " new size: " << sampling_set->size()
    << endl;

}

void init_solver_setup(bool init_sampling)
{
    delete solver;
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
    readInAFile(inp.c_str(), 0, true);
    if (init_sampling) {
        init_samping_set(conf.recompute_sampling_set);
    }
    orig_num_vars = solver->nVars();
    remove_zero_assigned_literals();

    //Read in file again, with offset
    readInAFile(inp.c_str(), orig_num_vars, false);

    //Set up solver
    solver->set_up_for_scalmc();
    if (!conf.bva) {
        solver->set_no_bva();
    }
    if (!conf.bve) {
        solver->set_no_bve();
    }
    solver->set_intree_probe(0);
    //solver->set_verbosity(2);

    //Print stats
    add_fixed_clauses();
    incidence = solver->get_var_incidence();
    cout << "[mis] CNF read-in time: " << (cpuTime()-myTime) << endl;
}

void run_guess()
{
    double myTime = cpuTime();
    uint32_t start_sampl = sampling_set->size();

    uint32_t div = 5;
    uint32_t guess_indep = std::max<uint32_t>(sampling_set->size()/div, 20);

    //NORM
    uint32_t cur_sampl_size = sampling_set->size();
    if (true) {
        cout << " ============ INV ==============" << endl;
        for (uint32_t i = 0; i < div/2; i++){
            guess_round(guess_indep, true, false, i);
        }
    }
    uint32_t inv_removed = cur_sampl_size - sampling_set->size();

    cur_sampl_size = sampling_set->size();
    if (true) {
        cout << " ============ NORM ==============" << endl;
        for (uint32_t i = 0; i < div/2; i++) {
            guess_round(guess_indep, false, false, i);
        }
    }
    uint32_t norm_removed = cur_sampl_size - sampling_set->size();

    cur_sampl_size = sampling_set->size();
    if (true) {
        cout << " ============ RND ==============" << endl;
        for (uint32_t i = 0; i < div/2; i++) {
            guess_round(guess_indep, false, true, 0);
        }
    }
    uint32_t rnd_removed = cur_sampl_size - sampling_set->size();

    cout
    << "[mis] GUESS"
    << " rem: " << std::setw(7) << (start_sampl - sampling_set->size())
    << " rem-inv: " << inv_removed
    << " rem-norm: " << norm_removed
    << " rem-rnd: " << rnd_removed
    << " T: " << (cpuTime() - myTime) << endl;
}

int main(int argc, char** argv)
{
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
                  );
    #endif

    sampling_set = &sampling_set_tmp1;
    other_sampling_set = &sampling_set_tmp2;
    guess_assumption_set = &guess_set_tmp;
    guess_assumption_set->clear();
    //Reconstruct the command line so we can emit it later if needed
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) {
            command_line += " ";
        }
    }

    add_supported_options(argc, argv);
    cout << "[mis] Arjun Version: " << get_version_sha1() << endl;
    cout
    << "c executed with command line: "
    << command_line
    << endl;
    cout << "[mis] using seed: " << conf.seed << endl;

    double starTime = cpuTime();
    mtrand.seed(conf.seed);
    init_solver_setup(true);
    cout << solver->get_text_version_info();
    signal(SIGALRM,signal_handler);
    //signal(SIGINT,signal_handler);

    seen.clear();
    seen.resize(solver->nVars(), 0);

    uint32_t prev_size = sampling_set->size()*100;
    uint32_t num;
    uint32_t round_num = 0;

    bool cont = true;
    bool forward = true;
    if (conf.backward_only) {
        forward = false;
    }
    while(cont) {
        if (sampling_set->size() > 60) {
            simp();
        }
        if (conf.guess && round_num > 0) {
            run_guess();
        }

        num = 1;
        prev_size = sampling_set->size();

        cout << "[mis] ===--> Doing a run for " << num << endl;
        if (forward) {
            cout << " FORWARD " << endl;
            uint32_t guess_indep = std::max<uint32_t>(sampling_set->size()/10, 10);

            forward_round(50000, guess_indep, false, false, 0);
            cont = true;
        } else {
            cout << " BACKWARD " << endl;
            uint32_t num = 50000;
            if (conf.backward_only) {
                num = std::numeric_limits<uint32_t>::max();
            }
            cont = !backward_round(num);
        }
        if (round_num > 1) {
            forward = !forward;
        }
        round_num++;
    }

    print_indep_set();
    cout
    << "[mis] "
    << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - starTime)
    << endl;

    delete solver;
    return 0;
}
