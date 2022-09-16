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

#include "arjun.h"
#include "config.h"
#include <cryptominisat5/dimacsparser.h>


using std::cout;
using std::cerr;
using std::endl;
using std::map;
using std::set;
using std::string;
using std::vector;

po::options_description arjun_options = po::options_description("Arjun options");
po::options_description help_options;
po::variables_map vm;
po::positional_options_description p;
double startTime;
Config conf;
ArjunNS::Arjun* arjun = NULL;
string elimtofile;

int recompute_sampling_set = 0;
uint32_t orig_sampling_set_size = 0;
uint32_t polar_mode = 0;

// static void signal_handler(int) {
//     cout << endl << "c [arjun] INTERRUPTING ***" << endl << std::flush;
//     common.interrupt_asap = true;
// }

void add_arjun_options()
{
    conf.verb = 1;

    arjun_options.add_options()
    ("help,h", "Prints help")
    ("version", "Print version info")
    ("input", po::value<std::vector<string>>(), "file to read/write")
    ("verb,v", po::value(&conf.verb)->default_value(conf.verb), "verbosity")
    ("seed,s", po::value(&conf.seed)->default_value(conf.seed), "Seed")
//     ("bve", po::value(&conf.bve)->default_value(conf.bve), "bve")
    ("intree", po::value(&conf.intree)->default_value(conf.intree), "intree")
    ("distill", po::value(&conf.distill)->default_value(conf.distill), "distill")
    ("fastbackw", po::value(&conf.fast_backw)->default_value(conf.fast_backw), "fast_backw")
    ("guess", po::value(&conf.guess)->default_value(conf.guess), "Guess small set")
    ("simp", po::value(&conf.simp)->default_value(conf.simp), "Do ANY sort of simplification")
    ("sort", po::value(&conf.incidence_sort)->default_value(conf.incidence_sort),
     "Which sorting mechanism.")
    ("presimp", po::value(&conf.pre_simplify)->default_value(conf.pre_simplify),
     "simplify")
    ("regsimp", po::value(&conf.regularly_simplify)->default_value(conf.regularly_simplify),
     "Regularly simplify")
    ("recomp", po::value(&recompute_sampling_set)->default_value(recompute_sampling_set),
     "Recompute sampling set even if it's part of the CNF")
    ("fwdset", po::value(&conf.assign_fwd_val)->default_value(conf.assign_fwd_val),
     "When doing forward, set the value instead of using assumptions")
    ("backward", po::value(&conf.backward)->default_value(conf.backward),
     "Do backwards query")
    ("forward", po::value(&conf.forward)->default_value(conf.forward),
     "Do forward query")
    ("fwdgroup", po::value(&conf.forward_group)->default_value(conf.forward_group),
     "Group variables by this bunches when doing forward query")
    ("orgate", po::value(&conf.or_gate_based)->default_value(conf.or_gate_based),
     "Use 3-long gate detection in SAT solver to define some variables")
    ("irreggate", po::value(&conf.irreg_gate_based)->default_value(conf.irreg_gate_based),
     "Use irregular gate based removal of variables from sampling set")
    ("itegate", po::value(&conf.ite_gate_based)->default_value(conf.ite_gate_based),
     "Use ITE gate detection in SAT solver to define some variables")
    ("probe", po::value(&conf.probe_based)->default_value(conf.probe_based),
     "Use simple probing to set (and define) some variables")
    ("backbone", po::value(&conf.backbone_simpl)->default_value(conf.backbone_simpl),
     "Use backbone simplification")
    ("backbonemaxconfl", po::value(&conf.backbone_simpl_max_confl)->default_value(conf.backbone_simpl_max_confl),
     "Backbone simplification max conflicts")
    ("xorgate", po::value(&conf.xor_gates_based)->default_value(conf.xor_gates_based),
     "Use XOR detection in SAT solver to define some variables")
    ("maxc", po::value(&conf.backw_max_confl)->default_value(conf.backw_max_confl),
     "Maximum conflicts per variable in backward mode")
    ("gaussj", po::value(&conf.gauss_jordan)->default_value(conf.gauss_jordan),
     "Use XOR finding and Gauss-Jordan elimination")
    ("empty", po::value(&conf.empty_occs_based)->default_value(conf.empty_occs_based),
     "Use empty occurrence improvement")
    ("mirrorempty", po::value(&conf.mirror_empty)->default_value(conf.mirror_empty),
     "Allow mirror F|v=true === F|v=false empty")
    ;

    help_options.add(arjun_options);
}

void add_supported_options(int argc, char** argv)
{
    add_arjun_options();
    p.add("input", -1);

    try {
        po::store(po::command_line_parser(argc, argv).options(help_options).positional(p).run(), vm);
        if (vm.count("help"))
        {
            cout
            << "Minimal projection set finder" << endl;

            cout
            << "arjun [options] inputfile" << endl << endl;

            cout << help_options << endl;
            std::exit(0);
        }

        if (vm.count("version")) {
            cout << "c [arjun] SHA revision: " << arjun->get_version_info() << endl;
            cout << "c [arjun] Compilation environment: " << arjun->get_compilation_env() << endl;
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

inline double stats_line_percent(double num, double total)
{
    if (total == 0) {
        return 0;
    } else {
        return num/total*100.0;
    }
}

void print_final_indep_set(const vector<uint32_t>& indep_set, const vector<uint32_t>& empty_occs)
{
    cout << "c ind ";
    for(const uint32_t s: indep_set) cout << s+1 << " ";
    cout << "0" << endl;

    cout
    << "c [arjun] final set size:      " << std::setw(7) << indep_set.size()
    << " percent of original: "
    <<  std::setw(6) << std::setprecision(4)
    << stats_line_percent(indep_set.size(), orig_sampling_set_size)
    << " %" << endl
    << "c [arjun] of which empty occs: " << std::setw(7) << empty_occs.size()
    << " percent of original: "
    <<  std::setw(6) << std::setprecision(4)
    << stats_line_percent(empty_occs.size(), orig_sampling_set_size)
    << " %" << endl;
}

void readInAFile(const string& filename)
{
    #ifndef USE_ZLIB
    FILE * in = fopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<FILE*, FN>, ArjunNS::Arjun> parser(arjun, NULL, 0);
    #else
    gzFile in = gzopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<gzFile, GZ>, ArjunNS::Arjun> parser(arjun, NULL, 0);
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

    if (!parser.sampling_vars_found || recompute_sampling_set) {
        orig_sampling_set_size = arjun->start_with_clean_sampling_set();
    } else {
        orig_sampling_set_size = arjun->set_starting_sampling_set(parser.sampling_vars);
    }

    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}

void dump_cnf(const std::pair<vector<vector<Lit>>, uint32_t>& cnf, const vector<uint32_t>& sampl_set, const uint32_t multiply = 0)
{
    uint32_t num_cls = cnf.first.size();
    uint32_t max_var = cnf.second;
    std::ofstream outf;
    outf.open(elimtofile.c_str(), std::ios::out);
    outf << "p cnf " << max_var << " " << num_cls << endl;

    //Add projection
    outf << "c ind ";
    for(const auto& v: sampl_set) {
        outf << v+1  << " ";
    }
    outf << "0\n";

    for(const auto& cl: cnf.first) {
        outf << cl << " 0\n";
    }
    outf << "c MUST MUTIPLY BY 2**" << multiply << endl;
}

void elim_to_file(
    const vector<uint32_t>& sampl_set,
    const vector<uint32_t>& empty_occs,
    uint32_t orig_num_vars)
{
    double dump_start_time = cpuTime();
    cout << "c [arjun] dumping simplified problem to '" << elimtofile << "'" << endl;
    auto ret = arjun->get_fully_simplified_renumbered_cnf(sampl_set, empty_occs, orig_num_vars);
    dump_cnf(std::get<0>(ret), std::get<1>(ret), std::get<2>(ret));
    cout << "c [arjun] Done dumping. T: " << (cpuTime() - dump_start_time) << endl;
}

int main(int argc, char** argv)
{
    arjun = new ArjunNS::Arjun;
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
                  );
    #endif

    //Reconstruct the command line so we can emit it later if needed
    string command_line;
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) {
            command_line += " ";
        }
    }

    add_supported_options(argc, argv);

    cout << "c Arjun Version: "
    << arjun->get_version_info() << endl;
    cout << arjun->get_solver_version_info();

    cout
    << "c executed with command line: "
    << command_line
    << endl;

    double starTime = cpuTime();
    cout << "c [arjun] using seed: " << conf.seed << endl;
    arjun->set_verbosity(conf.verb);
    arjun->set_seed(conf.seed);
    arjun->set_fast_backw(conf.fast_backw);
    arjun->set_distill(conf.distill);
    arjun->set_regularly_simplify(conf.regularly_simplify);
    arjun->set_intree(conf.intree);
    arjun->set_guess(conf.guess);
    arjun->set_pre_simplify(conf.pre_simplify);
    arjun->set_incidence_sort(conf.incidence_sort);
    arjun->set_or_gate_based(conf.or_gate_based);
    arjun->set_ite_gate_based(conf.ite_gate_based);
    arjun->set_xor_gates_based(conf.xor_gates_based);
    arjun->set_probe_based(conf.probe_based);
    arjun->set_forward(conf.forward);
    arjun->set_backward(conf.backward);
    arjun->set_assign_fwd_val(conf.assign_fwd_val);
    arjun->set_backw_max_confl(conf.backw_max_confl);
    arjun->set_gauss_jordan(conf.gauss_jordan);
    arjun->set_fwd_group(conf.forward_group);
    arjun->set_backbone_simpl(conf.backbone_simpl);
    arjun->set_irreg_gate_based(conf.irreg_gate_based);
    arjun->set_backbone_simpl_max_confl(conf.backbone_simpl_max_confl);
    arjun->set_simp(conf.simp);
    arjun->set_empty_occs_based(conf.empty_occs_based);
    arjun->set_mirror_empty(conf.mirror_empty);
//     if (polar_mode == 1) {
//         arjun->set_polar_mode(CMSat::PolarityMode::polarmode_neg);
//     }


    //signal(SIGINT,signal_handler);

    //parsing the input
    if (vm.count("input") == 0 || vm["input"].as<vector<string>>().size() == 0 || vm["input"].as<vector<string>>().size() > 2) {
        cout << "ERROR: you must pass an INPUT and optionally an OUTPUT file as parameters" << endl;
        exit(-1);
    }

    const string inp = vm["input"].as<vector<string>>()[0];
    if (vm["input"].as<vector<string>>().size() >= 2) {
        elimtofile = vm["input"].as<vector<string>>()[1];
    }
    readInAFile(inp);
    cout << "c [arjun] original sampling set size: " << orig_sampling_set_size << endl;

    uint32_t orig_num_vars = arjun->nVars();
    vector<uint32_t> sampl_set = arjun->get_indep_set();
    print_final_indep_set(sampl_set, arjun->get_empty_occ_sampl_vars());
    cout << "c [arjun] finished "
    << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - starTime)
    << endl;

    if (!elimtofile.empty()) {
        elim_to_file(sampl_set, arjun->get_empty_occ_sampl_vars(), orig_num_vars);
    }

    delete arjun;
    return 0;
}
