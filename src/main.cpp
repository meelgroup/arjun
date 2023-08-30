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


#include "time_mem.h"
#include "arjun.h"
#include "config.h"
#include "helper.h"
#include <cryptominisat5/dimacsparser.h>

using std::cout;
using std::endl;
using std::string;
using std::vector;
using namespace CMSat;

po::options_description arjun_options = po::options_description("Arjun options");
po::options_description help_options;
po::variables_map vm;
po::positional_options_description p;
double startTime;
ArjunInt::Config conf;
ArjunNS::Arjun* arjun = NULL;
string elimtofile;
string recover_file;
int recompute_sampling_set = 0;

uint32_t orig_cnf_must_mult_exp2 = 0;
uint32_t orig_sampling_set_size = 0;
uint32_t polar_mode = 0;
int oracle_sparsify = true;
int oracle_vivif = true;
int oracle_vivif_get_learnts = false;
int sampo_iters1 = 2;
int sampo_iters2 = 2;
int renumber = true;
bool gates = true;
int extend_indep = false;
int redundant_cls = true;

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
    ("sort", po::value(&conf.unknown_sort)->default_value(conf.unknown_sort),
     "Which sorting mechanism.")
    ("recomp", po::value(&recompute_sampling_set)->default_value(recompute_sampling_set),
     "Recompute sampling set even if it's part of the CNF")
    ("backward", po::value(&conf.backward)->default_value(conf.backward),
     "Do backwards query")
    ("empty", po::value(&conf.empty_occs_based)->default_value(conf.empty_occs_based),
     "Use empty occurrence improvement")
    ("maxc", po::value(&conf.backw_max_confl)->default_value(conf.backw_max_confl),
     "Maximum conflicts per variable in backward mode")
    ("extend", po::value(&extend_indep)->default_value(extend_indep),
     "Extend independent set just before CNF dumping")
    ;

    po::options_description simp_options("Simplification before indep detection");
    simp_options.add_options()
    ("bvepresimp", po::value(&conf.bve_pre_simplify)->default_value(conf.bve_pre_simplify),
     "simplify")
    ("simp", po::value(&conf.simp)->default_value(conf.simp), "Do ANY sort of simplification")
    ("probe", po::value(&conf.probe_based)->default_value(conf.probe_based),
     "Use simple probing to set (and define) some variables")
    ("intree", po::value(&conf.intree)->default_value(conf.intree), "intree")
    ;


    po::options_description gate_options("Gate options");
    gate_options.add_options()
    ("gates", po::value<bool>(&gates),
     "Turn on/off all gate-based definability")
    ("nogatebelow", po::value<double>(&conf.no_gates_below)->default_value(conf.no_gates_below)
     , "Don't use gates below this incidence relative position (1.0-0.0) to minimize the independent set. Gates are not very accurate, but can save a LOT of time. We use them to get rid of most of the uppert part of the sampling set only. Default is 99% is free-for-all, the last 1% we test. At 1.0 we test everything, at 0.0 we try using gates for everything.")
    ("orgate", po::value(&conf.or_gate_based)->default_value(conf.or_gate_based),
     "Use 3-long gate detection in SAT solver to define some variables")
    ("irreggate", po::value(&conf.irreg_gate_based)->default_value(conf.irreg_gate_based),
     "Use irregular gate based removal of variables from sampling set")
    ("itegate", po::value(&conf.ite_gate_based)->default_value(conf.ite_gate_based),
     "Use ITE gate detection in SAT solver to define some variables")
    ("xorgate", po::value(&conf.xor_gates_based)->default_value(conf.xor_gates_based),
     "Use XOR detection in SAT solver to define some variables")
    ;

    po::options_description debug_options("Debug options");
    debug_options.add_options()
    ("fastbackw", po::value(&conf.fast_backw)->default_value(conf.fast_backw), "fast_backw")
    ("gaussj", po::value(&conf.gauss_jordan)->default_value(conf.gauss_jordan),
     "Use XOR finding and Gauss-Jordan elimination")
    ("sampoiters1", po::value(&sampo_iters1)->default_value(sampo_iters1),
     "Sampo iters before oracle")
    ("sampoiters2", po::value(&sampo_iters2)->default_value(sampo_iters2),
     "Sampo iters after oracle")
    ("oraclesparsify", po::value(&oracle_sparsify)->default_value(oracle_sparsify),
     "Use Oracle to sparsify")
    ("oraclevivif", po::value(&oracle_vivif)->default_value(oracle_vivif),
     "Use oracle to vivify")
    ("oraclevivifgetl", po::value(&oracle_vivif_get_learnts)->default_value(oracle_vivif_get_learnts),
     "Use oracle to vivify get learnts")
    ("renumber", po::value(&renumber)->default_value(renumber),
     "Renumber variables to start from 1...N in CNF. Setting this to 0 is EXPERIMENTAL!!")
    ("distill", po::value(&conf.distill)->default_value(conf.distill), "distill")
    ("bve", po::value(&conf.bve_during_elimtofile)->default_value(conf.bve_during_elimtofile),
     "Use BVE during simplificaiton of the formula")
    ("bce", po::value(&conf.bce)->default_value(conf.bce),
     "Use blocked clause elimination (BCE). VERY experimental!!")
    ("red", po::value(&redundant_cls)->default_value(redundant_cls),
     "Also dump redundant clauses")
    ("specifiedorder", po::value(&conf.specified_order_fname)
     , "Try to remove variables from the independent set in this order. File must contain a variable on each line. Variables start at ZERO. Variable from the BOTTOM will be removed FIRST. This is for DEBUG ONLY")
    ;

    help_options.add(arjun_options);
    help_options.add(simp_options);
    help_options.add(gate_options);
    help_options.add(debug_options);
}

void print_final_indep_set(const vector<uint32_t>& indep_set, const vector<uint32_t>& empty_occs, bool force)
{
    if (indep_set.size() < 100 || force) {
        cout << "c p show ";
        for(const uint32_t s: indep_set) cout << s+1 << " ";
        cout << "0" << endl;
    } else {
        cout << "c not printing indep set, it's more than 100 elements" << endl;
    }

    if (empty_occs.size() < 100 || force) {
        cout << "c empties ";
        for(const uint32_t s: empty_occs) cout << s+1 << " ";
        cout << "0" << endl;
    } else {
        cout << "c not printing empty set, it's more than 100 elements" << endl;
    }

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

void elim_to_file(const vector<uint32_t>& sampl_vars)
{
    double dump_start_time = cpuTime();
    auto ret = arjun->get_fully_simplified_renumbered_cnf(
        sampl_vars, oracle_vivif, oracle_vivif_get_learnts, oracle_sparsify,
        sampo_iters1, sampo_iters2, renumber, !recover_file.empty());

    delete arjun;
    arjun = NULL;
    if (extend_indep) {
        Arjun arj2;
        arj2.new_vars(ret.nvars);
        arj2.set_verbosity(conf.verb);
        for(const auto& cl: ret.cnf) arj2.add_clause(cl);
        arj2.set_starting_sampling_set(ret.sampling_vars);
        ret.sampling_vars = arj2.extend_indep_set();
    }

    // TODO fix recover file based on SCNF renumbering
    if (!recover_file.empty()) {
        std::ofstream f(recover_file, std::ios::out | std::ios::binary);
        f.write(&ret.sol_ext_data[0], ret.sol_ext_data.size());
        f.close();
    }

    if (renumber) ret.renumber_sampling_for_ganak();
    cout << "c [arjun] dumping simplified problem to '" << elimtofile << "'" << endl;
    write_simpcnf(ret, elimtofile, orig_cnf_must_mult_exp2, redundant_cls);
    cout << "c [arjun] Dumping took: "
        << std::setprecision(2) << (cpuTime() - dump_start_time) << endl;

    cout << "c [arjun] All done. T: "
        << std::setprecision(2) << (cpuTime() - startTime) << endl;
}

void set_config(ArjunNS::Arjun* arj) {
    cout << "c [arjun] using seed: " << conf.seed << endl;
    arj->set_verbosity(conf.verb);
    arj->set_seed(conf.seed);
    arj->set_fast_backw(conf.fast_backw);
    arj->set_distill(conf.distill);
    arj->set_specified_order_fname(conf.specified_order_fname);
    arj->set_intree(conf.intree);
    arj->set_bve_pre_simplify(conf.bve_pre_simplify);
    arj->set_unknown_sort(conf.unknown_sort);
    if (gates) {
      arj->set_or_gate_based(conf.or_gate_based);
      arj->set_ite_gate_based(conf.ite_gate_based);
      arj->set_xor_gates_based(conf.xor_gates_based);
      arj->set_irreg_gate_based(conf.irreg_gate_based);
    } else {
      cout << "c NOTE: all gates are turned off due to `--gates 0`" << endl;
      arj->set_or_gate_based   (0);
      arj->set_ite_gate_based  (0);
      arj->set_xor_gates_based (0);
      arj->set_irreg_gate_based(0);
    }
    arj->set_no_gates_below(conf.no_gates_below);
    arj->set_probe_based(conf.probe_based);
    arj->set_backward(conf.backward);
    arj->set_backw_max_confl(conf.backw_max_confl);
    arj->set_gauss_jordan(conf.gauss_jordan);
    arj->set_simp(conf.simp);
    arj->set_empty_occs_based(conf.empty_occs_based);
    arj->set_bve_during_elimtofile(conf.bve_during_elimtofile);
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
        if (i+1 < argc) command_line += " ";
    }

    add_arjun_options();
    add_supported_options(argc, argv, p, help_options, vm, arjun);

    cout << "c Arjun Version: "
    << arjun->get_version_info() << endl;
    cout << arjun->get_solver_version_info();

    cout
    << "c executed with command line: "
    << command_line
    << endl;

    startTime = cpuTime();
    set_config(arjun);

    //parsing the input
    if (vm.count("input") == 0
            || vm["input"].as<vector<string>>().size() == 0
            || vm["input"].as<vector<string>>().size() > 3) {
        cout << "ERROR: you must pass an INPUT, optionally an OUTPUT, and optionally a RECOVER files as parameters" << endl;
        exit(-1);
    }

    const string inp = vm["input"].as<vector<string>>()[0];
    if (vm["input"].as<vector<string>>().size() >= 2) {
        elimtofile = vm["input"].as<vector<string>>()[1];
    }
    if (vm["input"].as<vector<string>>().size() >= 3) {
        recover_file = vm["input"].as<vector<string>>()[2];
    }
    readInAFile(inp, arjun, orig_sampling_set_size, orig_cnf_must_mult_exp2,
            recompute_sampling_set);
    cout << "c [arjun] original sampling set size: " << orig_sampling_set_size << endl;

    vector<uint32_t> indep_vars = arjun->get_indep_set();
    print_final_indep_set(indep_vars, arjun->get_empty_occ_sampl_vars(), elimtofile.empty());
    cout << "c [arjun] finished "
        << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - startTime)
        << endl;

    if (!elimtofile.empty()) {
        if (conf.simp) elim_to_file(indep_vars);
        else {
            if (extend_indep) {
                cout << "ERROR, '--extend 1' option makes no sense if not simplifying. The tool would shrink then extend the projection set. Why do that?" << endl;
                exit(-1);
            }
            write_origcnf(arjun, indep_vars, elimtofile, orig_cnf_must_mult_exp2);
        }
    }

    delete arjun;
    return 0;
}
