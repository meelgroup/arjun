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
enum ModeType {one_mode, many_mode, inverse_mode};

//assert indic[var] to FASLE to force var==var+orig_num_vars
map<uint32_t, uint32_t> indic;

vector<uint32_t> sampling_set_tmp1;
vector<uint32_t> sampling_set_tmp2;
vector<uint32_t> guess_set_tmp;
vector<uint32_t>* sampling_set = NULL;
vector<uint32_t>* guess_assumption_set = NULL;
vector<uint32_t>* other_sampling_set = NULL;
map<uint32_t, vector<uint32_t>> global_assump_to_testvars;
vector<uint32_t> incidence;
vector<double> vsids_scores;
vector<uint32_t> this_indic2;
void run_guess();

struct Config {
    int verb = 0;
    int seed = 0;
    int bva = 0;
    int bve = 0;
    int guess = 1;
    int force_by_one = 0;
    int simp_at_start = 1;
    int always_one_by_one = 1;
    int recompute_sampling_set = 0;
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
        indic[var] = this_indic;

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
    assert(indic.size() == sampling_set->size());
    tmp.clear();
    solver->new_var();
    mult_or_invers_var = solver->nVars()-1;
    tmp.push_back(Lit(mult_or_invers_var, false));
    for(const auto& var: indic) {
        tmp.push_back(Lit(var.second, false));
    }
    solver->add_clause(tmp);



    assert(this_indic2.empty());
    this_indic2.resize(orig_num_vars, var_Undef);
    vector<Lit> tmp_one;
    for(uint32_t var: *sampling_set) {
        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;

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
}

void fill_assumptions(
    vector<Lit>& assumptions,
    vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const vector<uint32_t>& indep,
    const vector<uint32_t>& testvar_to_assump,
    bool trick = false
)
{
    assumptions.clear();

    //Add unknown as assumptions
    uint32_t j = 0;
    for(uint32_t i = 0; i < unknown.size(); i++) {
        uint32_t var = unknown[i];
        if (unknown_set[var] == 0) {
            continue;
        } else {
            unknown[j++] = var;
        }

        assert(testvar_to_assump.size() > var);
        uint32_t ass = testvar_to_assump[var];
        if (!seen[ass]) {
            seen[ass] = 1;
            assumptions.push_back(Lit(ass, true));
            if (!trick) {
                assumptions.push_back(Lit(this_indic2[var], true));
            }
        }
    }
    unknown.resize(j);

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(testvar_to_assump.size() > var);
        uint32_t ass = testvar_to_assump[var];
        if (!seen[ass]) {
            seen[ass] = 1;
            assumptions.push_back(Lit(ass, true));
            if (!trick) {
                assumptions.push_back(Lit(this_indic2[var], true));
            }
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
    const vector<uint32_t> testvar_to_assump,
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
    cout<<"index "<<index<<" ass select size"<<ass_select.size()<< endl;
    std::sort(ass_select.begin(), ass_select.end());
    uint32_t ass = ass_select.at(index);

    seen[ass] = 1;
    assumptions.push_back(Lit(ass, true));

    /*for(const auto& v: assump_to_testvars[ass]) {
        //cout << "v: " << v+1 << " inc: " << incidence[v] << endl;
        assumptions.push_back(Lit(this_indic2[v], true));
    }*/

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assumptions.push_back(Lit(this_indic2[var], true)); //Shouldn't this be false?
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
    incidence = solver->get_var_incidence_also_red();
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

uint32_t inverse_remove(vector<Lit>& assumptions,
                    vector<char>& unknown_set,

                    const vector<uint32_t>& dontremove)
{
    uint32_t removed = 0;
    cout << "assumptions size: " << assumptions.size() << endl;
    seen.resize(solver->nVars(), 0);

    vector<Lit> prop = solver->propagated_by(assumptions);
    cout << "prop len: " << prop.size() << endl;

    for(Lit l: prop) {
        if (l.sign() == true) {
            seen[l.var()] = 1;
            }
    }
    for(auto var: dontremove) {
        assert(indic.find(var) != indic.end());
        seen[indic[var]] = 0;
    }
    for(auto& x: indic) {
        if (seen[x.second]) {
            assert(x.first < orig_num_vars);
            auto var = x.first;
            if (unknown_set[var]) {
                unknown_set[var] = 0;
                assumptions.push_back(Lit(x.second,true));
                removed++;
            }
        }
    }
    for(Lit l: prop) {
        seen[l.var()] = 0;
    }

    cout << "removed: " << removed << endl;
    return removed;
}

void one_round(uint32_t by, bool only_inverse, bool reverse = false, bool shuffle = false, int inv_at = 0, int offset_guess = 0)
{
    for(const auto& x: seen) {
        assert(x == 0);
    }

    if (offset_guess >= sampling_set->size()){
        return;
    }
    double start_round_time = cpuTimeTotal();
    //start with empty independent set
    vector<uint32_t> indep;
    uint32_t total_by = by;
    //testvar_to_assump:
    //FIRST is variable we want to test for
    //SECOND is what we have to assumoe (in negative)
    vector<uint32_t> testvar_to_assump;
    testvar_to_assump.resize(orig_num_vars, var_Undef);

    map<uint32_t, vector<uint32_t>> assump_to_testvars;
    vector<uint32_t> assump_to_testvar;

    vector<Lit> all_assumption_lits;
    std::sort(sampling_set->begin(), sampling_set->end(), IncidenceSorter(incidence));
    if (reverse) {
        std::reverse(sampling_set->begin(), sampling_set->end());
    }
    if (shuffle) {
        std::random_shuffle(sampling_set->begin(), sampling_set->end());
    }

    for(uint32_t i = offset_guess; i < sampling_set->size();) {
        solver->new_var();
        const uint32_t ass = solver->nVars()-1;
        all_assumption_lits.push_back(Lit(ass, false));

        vector<uint32_t> vars;
        for(uint32_t i2 = 0; i2 < by && i < sampling_set->size(); i2++, i++) {
            uint32_t var = (*sampling_set)[i];

            tmp.clear();
            tmp.push_back(Lit(ass, false));
            assert(indic.find(var) != indic.end());
            tmp.push_back(Lit(indic[var], true));
            solver->add_clause(tmp);

            assert(var < orig_num_vars);
            testvar_to_assump[var] = ass;
            vars.push_back(var);
        }

       global_assump_to_testvars[ass] = vars;
        assump_to_testvars[ass] = vars;
        if (assump_to_testvar.size() <= ass) {
            assump_to_testvar.resize(ass+1, var_Undef);
        }
       assump_to_testvar[ass] = vars[0];
    }
    seen.resize(solver->nVars(), 0);

    vector<uint32_t> ass_select;
    for(const auto& x: assump_to_testvars) {
        ass_select.push_back(x.first);
    }
    std::sort(ass_select.begin(), ass_select.end());
    uint32_t ass = ass_select.at(inv_at);
     if (false && only_inverse){
            cout<<" Guess set size: "<<guess_assumption_set->size()<<endl;
            for(uint32_t i2 = 0; i2 < guess_assumption_set->size();i2++) {
                uint32_t guess_ass = (*guess_assumption_set)[i2];
      //          cout<<"Size "<<global_assump_to_testvars[guess_ass].size()<<endl;
                for (uint32_t i3 = 0; i3 < global_assump_to_testvars[guess_ass].size(); i3++) {
                    uint32_t var = global_assump_to_testvars[guess_ass][i3];
                        assert(var < orig_num_vars);
                        assert(indic.find(var) != indic.end());
                        assump_to_testvars[ass].push_back(var);

                        total_by++;
                }
            }

        }

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
    ModeType one_by_one_mode = conf.always_one_by_one ? one_mode : many_mode;
    if (only_inverse) {
        one_by_one_mode = inverse_mode;
    }
    uint32_t num_fast = 0;
    uint32_t not_indep = 0;
    uint32_t removed = 0;
    bool inverse_won = false;
    double myTime = cpuTime();
    vector<char> tried_var_already;
    tried_var_already.resize(orig_num_vars, 0);

    //Calc mod:
    uint32_t mod = 1;
    if ((sampling_set->size()/by) > 20 ) {
        uint32_t will_do_iters = (sampling_set->size()/by);
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }
    vector<uint32_t> dontremove;
    vector<uint32_t> pick_possibilities;
    for(const auto& unk_v: unknown) {
        pick_possibilities.push_back(unk_v);
    }
    std::sort(pick_possibilities.begin(), pick_possibilities.end(), IncidenceSorter(incidence));
    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    uint32_t inverse_ass = var_Undef;
    bool should_continue_inverse = true;
    while(
        (!only_inverse && true)
        || (only_inverse && should_continue_inverse && iter < 5)
    ) {
        if (one_by_one_mode == many_mode) {
            num_fast ++;
        }
        if (iter % 500 == 0) {
            one_by_one_mode = many_mode;
        } else {
            one_by_one_mode = one_mode;
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
            test_var = var_Undef;
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
            assert(test_var < orig_num_vars);
            assert(testvar_to_assump.size() > test_var);
            uint32_t ass = testvar_to_assump[test_var];
            assert(ass != var_Undef);

            if (by > 1) {
                assert(assump_to_testvars.find(ass) != assump_to_testvars.end());
                const auto& vars = assump_to_testvars[ass];
                for(uint32_t var: vars) {
                    unknown_set[var] = 0;
                    tried_var_already[var] = 1;
                }
            } else {
                const auto& var = assump_to_testvar[ass];
                unknown_set[var] = 0;
                tried_var_already[var] = 1;
            }
        }


        //Assumption filling

        if (one_by_one_mode == inverse_mode && iter < 1) {

            inverse_ass = fill_assumptions2(
                assumptions, indep, testvar_to_assump, assump_to_testvars,
                iter);
            for (auto var: assump_to_testvars[inverse_ass]){
                dontremove.push_back(var);
            }
            assumptions.push_back(Lit(mult_or_invers_var, true));
/*           for(uint32_t i2 = 0; i2 < guess_assumption_set->size();i2++) {
                uint32_t guess_ass = (*guess_assumption_set)[i2];
                assumptions.push_back(Lit(guess_ass, false));
            }
*/
        }
        else if (one_by_one_mode == many_mode) {
            fill_assumptions(assumptions, unknown, unknown_set, indep, testvar_to_assump, true);
            assumptions.push_back(Lit(mult_or_invers_var, true));
        }
        else if (one_by_one_mode == one_mode) {
            if (by > 1) {
                fill_assumptions(assumptions, unknown, unknown_set, indep, testvar_to_assump, false);
            } else {
                fill_assumptions(assumptions, unknown, unknown_set, indep, testvar_to_assump, true);

                assert(testvar_to_assump.size() > test_var);
                uint32_t ass = testvar_to_assump[test_var];
                assert(ass != var_Undef);
                const auto& var = assump_to_testvar[ass];
                assumptions.push_back(Lit(var, false));
                assumptions.push_back(Lit(var + orig_num_vars, true));
            }
        }

        if (by > 100) {
            solver->set_max_confl(1500);
        } else {
            solver->set_max_confl(500);
        }
        if (one_by_one_mode == one_mode) {
            //solver->set_no_confl_needed();
        }

        lbool ret = l_Undef;
        if (true || !only_inverse) {
            ret = solver->solve(&assumptions);
        }
        if (ret == l_False) {
            ret_false++;
        } else if (ret == l_True) {
            ret_true++;
        } else if (ret == l_Undef) {
            ret_undef++;
        }

        if (ret == l_Undef) {
            if (one_by_one_mode == one_mode) {
                assert(test_var < orig_num_vars);
                uint32_t ass = testvar_to_assump[test_var];
                const auto& vars = assump_to_testvars[ass];
                for(uint32_t var: vars) {
                    assert(unknown_set[var] == 0);
                    unknown_set[var] = 1;
                    unknown.push_back(var);
                }
            } else if (ret == l_Undef) {
               removed = inverse_remove(assumptions, unknown_set ,  assump_to_testvars[inverse_ass]);
               if (removed == 0){
                    should_continue_inverse = false;
                }
               if (removed >= 10){
                    guess_assumption_set->push_back(inverse_ass);
                }

            }
        } else if (ret == l_True) {
            //Independent
            assert(one_by_one_mode == one_mode || one_by_one_mode == inverse_mode);
            if (one_by_one_mode == inverse_mode) {
                removed = inverse_remove(assumptions, unknown_set ,  assump_to_testvars[inverse_ass]);
                if (removed >= 10 ){
                    guess_assumption_set->push_back(inverse_ass);
                }

            const vector<lbool> model = solver->get_model();
            cout << "dontremove size: " << dontremove.size() << endl;
            cout << "indic size: " << indic.size() << endl;
            should_continue_inverse = false;
            seen.resize(solver->nVars(), 0);
            for (uint32_t var = 0; var <solver->nVars();var++){
                seen[var] = 1;
            }
            for(auto var: dontremove) {
                seen[var] = 0;
            }
            for(auto& x: indic) {
                auto var = x.first;
                auto indic_var = x.second;

                if (seen[var]) {
                    if (solver->get_model()[indic_var] == l_True){
                        assumptions.push_back(Lit(indic_var, true));
                        if (unknown_set[var]){
                            dontremove.push_back(var);
                        }
                        should_continue_inverse = true;
                    }
                }
            }
            for (uint32_t var = 0; var <solver->nVars();var++){
              seen[var] = 0;
            }
            cout << "dontremove size: " << dontremove.size() << endl;

                if (removed > 50){
                 //simp();

                }


            }
            if (one_by_one_mode == one_mode) {
                uint32_t ass = testvar_to_assump[test_var];

                if (by > 1) {
                    const auto& vars = assump_to_testvars[ass];
                    for(uint32_t var: vars) {
                        indep.push_back(var);
                    }
                } else {
                    const auto& var = assump_to_testvar[ass];
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
                    if (assump_to_testvars.find(ass) == assump_to_testvars.end()) {
                        continue;
                    }
                    const auto& vars = assump_to_testvars[ass];

                    //Remove from unknown
                    for(uint32_t var: vars) {
                        not_indep++;
                        unknown_set[var] = 0;
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
                //const auto& vars = assump_to_testvars[inverse_ass];

                const auto& vars = dontremove;

                for(auto&x: unknown) {
                    unknown_set[x] = 0;
                }
                unknown.clear();
                for(auto&x: vars) {
                    unknown.push_back(x);
                    unknown_set[x] = 1;
                }

                cout << "After unknown size: " << unknown.size() << endl;
                not_indep = orig_num_vars - unknown.size();
                cout << "not_indep:"<< not_indep <<endl;


                break;
            }
        }

        if (iter % mod == (mod-1)) {
            cout
            << "[mis] iter: " << std::setw(5) << iter;
            if (mod == 1) {
                cout << " mode: "
                << (old_one_by_one_mode==one_mode ? "one " :
                ((old_one_by_one_mode==many_mode) ? "many" : "inv " ))
                << " ret: " << std::setw(8) << ret;
            } else {
                cout
                << " T/F/U: ";
                std::stringstream ss;
                ss << ret_true << "/" << ret_false << "/" << ret_undef;
                cout << std::setw(8) << std::left << ss.str() << std::right;
                ret_true = 0;
                ret_false = 0;
                ret_undef = 0;
            }
            cout
            << " by: " << std::setw(3) << total_by
            << " U: " << std::setw(7) << unknown.size()
            << " I: " << std::setw(7) << indep.size()
            << " N: " << std::setw(7) << not_indep
            << " T: "
            << std::setprecision(2) << std::fixed << (cpuTime() - myTime)
            << endl;
            myTime = cpuTime();

        }
        iter++;
        if (iter %1000 == 0){
            run_guess();

        }


        if (by > 10 || iter % 10 == 0) {
            update_sampling_set(unknown, unknown_set, indep);
        }

    }
    if (!only_inverse && by != 1) {
        simp();
        re_sort();
    }
    update_sampling_set(unknown, unknown_set, indep);
    cout << "[mis] one_round finished T: "
    << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time)
    << endl;

    //clear clauses to do with assumptions
    for(const auto& lit: all_assumption_lits) {
        tmp.clear();
        tmp.push_back(lit);
        solver->add_clause(tmp);
    }
}

void simp(vector<char>* unknown_set)
{
    if (conf.simp_at_start) {
        double simp_time = cpuTime();
        cout << "[mis] Simplifying..." << endl;
        solver->simplify();
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
    readInAFile(inp.c_str(), 0, sampling_set->empty());
    init_samping_set(conf.recompute_sampling_set);
    orig_num_vars = solver->nVars();
    remove_zero_assigned_literals();

    //Read in file again, with offset
    readInAFile(inp.c_str(), orig_num_vars, false);

    //Set up solver
    solver->set_up_for_scalmc();
    if (!conf.bva) {
        solver->set_no_bve();
    }
    if (!conf.bve) {
        solver->set_no_bva();
    }
    solver->set_no_intree_probe();
    //solver->set_verbosity(2);

    //Print stats
    add_fixed_clauses();
    incidence = solver->get_var_incidence();
    cout << "[mis] Setup time: " << (cpuTime()-myTime) << endl;
}

void run_guess()
{

    double myTime = cpuTime();
    guess_assumption_set->clear();
    bool flip = true;
    uint32_t div = 10;

     uint32_t guess_indep = std::max<uint32_t>(sampling_set->size()/div, 20);
      guess_assumption_set->clear();
    for (uint32_t i = 1; i < 5; i++){
         cout<<"Guess set size:"<<guess_assumption_set->size()<<endl;
         one_round(guess_indep, true, flip, false, 0, i*guess_indep);
        // flip = !flip;
    }

    guess_assumption_set->clear();
    one_round(guess_indep, true, true, false, 0, 0);
    for (uint32_t i = 1; i < 5; i++){
        guess_assumption_set->clear();
        cout<<"Guess set size:"<<guess_assumption_set->size()<<endl;
        one_round(guess_indep, true, false, false, 0, i*guess_indep);

    }
    return;

    cout << "final :" << sampling_set->size() << " T: " << (myTime - cpuTime()) << endl;

    uint32_t last_sampl_size = sampling_set->size();
    uint32_t last_gain = 100000000;
    for(int div = 4; div < 6; div+=2) {
        cout << "rem Norm NOW..." << endl;
        last_gain = 1000000;
        for(int i = 0; i < div; i++) {
            uint32_t guess_indep = std::max<uint32_t>(sampling_set->size()/div, 50);
            cout << "Guessing: " << guess_indep << endl;
            one_round(guess_indep, true, false, false, i);

            assert(last_sampl_size >= sampling_set->size());
            last_gain = last_sampl_size - sampling_set->size();
            last_sampl_size = sampling_set->size();
        }

        cout << "rem shuffling NOW..." << endl;
        for(int i = 0; i < div; i++) {
            uint32_t guess_indep = std::max<uint32_t>(sampling_set->size()/div, 50);
            cout << "Guessing: " << guess_indep << endl;
            one_round(guess_indep, true, false, true, i);

            assert(last_sampl_size >= sampling_set->size());
            last_gain = last_sampl_size - sampling_set->size();
            last_sampl_size = sampling_set->size();
        }

        cout << "rem REVERSING NOW..." << endl;
        last_gain = 1000000;
        for(int i = 0; i < div; i++) {
            uint32_t guess_indep = std::max<uint32_t>(sampling_set->size()/div, 50);
            cout << "Guessing: " << guess_indep << endl;
            one_round(guess_indep, true, true, false, i);

            assert(last_sampl_size >= sampling_set->size());
            last_gain = last_sampl_size - sampling_set->size();
            last_sampl_size = sampling_set->size();
        }
    }
    cout << "1====final :" << sampling_set->size() << " T: " << (myTime - cpuTime()) << endl;
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
    init_solver_setup();
    cout << solver->get_text_version_info();
    signal(SIGALRM,signal_handler);
    //signal(SIGINT,signal_handler);

    seen.clear();
    seen.resize(solver->nVars(), 0);

    if (conf.guess && sampling_set->size() > 60) {
        uint32_t guess_indep = std::max<uint32_t>(sampling_set->size()/10, 100);
        //guess_indep = 1000;
       // guess_indep = 100;
        simp();
        one_round(guess_indep, true);
    }

    uint32_t prev_size = sampling_set->size()*100;
    uint32_t num;
    uint32_t round_num = 0;

    while(true) {
        if (conf.simp_at_start && round_num ==0) {
            simp();
        }
        if (conf.guess) {
            run_guess();

        }

        if (sampling_set->size() < prev_size/5) {
            num = sampling_set->size()/10;
        } else {
            num = num/10;
        }
        if (num < 100) {
            num = 1;
        }
        if (conf.force_by_one) {
            num = 1;
        }
        prev_size = sampling_set->size();

        cout << "[mis] ===--> Doing a run for " << num << endl;
        one_round(num, false);
        if (num == 1) {
            break;
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
