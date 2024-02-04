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

#if defined(__GNUC__) && defined(__linux__)
#include <cfenv>
#endif

#include <iostream>
#include <iomanip>
#include <vector>
#include <atomic>
#include <fstream>
#include <sstream>
#include <string>
#include <csignal>
#ifdef USE_ZLIB
#include <zlib.h>
#endif
#include "argparse.hpp"

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

argparse::ArgumentParser program = argparse::ArgumentParser("arjun");
double start_time;
ArjunInt::Config conf;
ArjunNS::Arjun* arjun = nullptr;
string elimtofile;
string recover_file;
int recompute_sampling_set = 0;

uint32_t orig_cnf_must_mult_exp2 = 0;
uint32_t orig_sampling_set_size = 0;
uint32_t polar_mode = 0;
SimpConf simp_conf;
int renumber = true;
bool gates = true;
int extend_indep = false;
int synthesis_define = false;
int redundant_cls = true;
int compute_indep = true;
int unate = false;
int simptofile = true;

// static void signal_handler(int) {
//     cout << endl << "c [arjun] INTERRUPTING ***" << endl << std::flush;
//     common.interrupt_asap = true;
// }

void add_arjun_options()
{
    conf.verb = 1;
    program.add_argument("-h", "--help")
        .help("Prints help")
        .default_value(false);
    program.add_argument("-v", "--version")
        .help("Print version info")
        .flag();
    program.add_argument("-v", "--verb")
        .action([&](const auto& a) {conf.verb = std::atoi(a.c_str());})
        .default_value(conf.verb)
        .help("verbosity");
    program.add_argument("--s", "--seed")
        .action([&](const auto& a) {conf.seed = std::atoi(a.c_str());})
        .default_value(conf.seed)
        .help("Seed");
    program.add_argument("--sort")
        .action([&](const auto& a) {conf.unknown_sort = std::atoi(a.c_str());})
        .default_value(conf.unknown_sort)
        .help("Which sorting mechanism.");
    program.add_argument("--recomp")
        .action([&](const auto& a) {recompute_sampling_set = std::atoi(a.c_str());})
        .default_value(recompute_sampling_set)
        .help("Recompute sampling set even if it's part of the CNF");
    program.add_argument("--backward")
        .action([&](const auto& a) {conf.backward = std::atoi(a.c_str());})
        .default_value(conf.backward)
        .help("Do backwards query");
    program.add_argument("--empty")
        .action([&](const auto& a) {conf.empty_occs_based = std::atoi(a.c_str());})
        .default_value(conf.empty_occs_based)
        .help("Use empty occurrence improvement");
    program.add_argument("--maxc")
        .action([&](const auto& a) {conf.backw_max_confl = std::atoi(a.c_str());})
        .default_value(conf.backw_max_confl)
        .help("Maximum conflicts per variable in backward mode");
    program.add_argument("--extend")
        .action([&](const auto& a) {extend_indep = std::atoi(a.c_str());})
        .default_value(extend_indep)
        .help("Extend independent set just before CNF dumping");
    program.add_argument("--synthdefine")
        .action([&](const auto& a) {synthesis_define = std::atoi(a.c_str());})
        .default_value(synthesis_define)
        .help("Define for synthesis");
    program.add_argument("--compindep")
        .action([&](const auto& a) {compute_indep = std::atoi(a.c_str());})
        .default_value(compute_indep)
        .help("compute indep support");
    program.add_argument("--unate")
        .action([&](const auto& a) {conf.do_unate = std::atoi(a.c_str());})
        .default_value(conf.do_unate)
        .help("Perform unate analysis");

    /* po::options_description simp_options("Simplification before indep detection"); */
    /* simp_options.add_options() */
    program.add_argument("--bvepresimp")
        .action([&](const auto& a) {conf.bve_pre_simplify = std::atoi(a.c_str());})
        .default_value(conf.bve_pre_simplify)
        .help("simplify");
    program.add_argument("--simp")
        .action([&](const auto& a) {conf.simp = std::atoi(a.c_str());})
        .default_value(conf.simp)
        .help("Do ANY sort of simplification");
    program.add_argument("--simptofile")
        .action([&](const auto& a) {simptofile = std::atoi(a.c_str());})
        .default_value(simptofile)
        .help("Write SIMPLIFIED file");
    program.add_argument("--probe")
        .action([&](const auto& a) {conf.probe_based = std::atoi(a.c_str());})
        .default_value(conf.probe_based)
        .help("Use simple probing to set (and define) some variables");
    program.add_argument("--intree")
        .action([&](const auto& a) {conf.intree = std::atoi(a.c_str());})
        .default_value(conf.intree)
        .help("intree");

    /* po::options_description gate_options("Gate options"); */
    /* gate_options.add_options() */
    program.add_argument("--gates")
        .action([&](const auto& a) {gates = std::atoi(a.c_str());})
        .default_value(1)
        .help("Turn on/off all gate-based definability");
    program.add_argument("--nogatebelow")
        .action([&](const auto& a) {conf.no_gates_below = std::atof(a.c_str());})
        .default_value(conf.no_gates_below)
        .help("Don't use gates below this incidence relative position (1.0-0.0) to minimize the independent set. Gates are not very accurate, but can save a LOT of time. We use them to get rid of most of the uppert part of the sampling set only. Default is 99% is free-for-all, the last 1% we test. At 1.0 we test everything, at 0.0 we try using gates for everything.");
    program.add_argument("--orgate")
        .action([&](const auto& a) {conf.or_gate_based = std::atoi(a.c_str());})
        .default_value(conf.or_gate_based)
        .help("Use 3-long gate detection in SAT solver to define some variables");
    program.add_argument("--irreggate")
        .action([&](const auto& a) {conf.irreg_gate_based = std::atoi(a.c_str());})
        .default_value(conf.irreg_gate_based)
        .help("Use irregular gate based removal of variables from sampling set");
    program.add_argument("--itegate")
        .action([&](const auto& a) {conf.ite_gate_based = std::atoi(a.c_str());})
        .default_value(conf.ite_gate_based)
        .help("Use ITE gate detection in SAT solver to define some variables");
    program.add_argument("--xorgate")
        .action([&](const auto& a) {conf.xor_gates_based = std::atoi(a.c_str());})
        .default_value(conf.xor_gates_based)
        .help("Use XOR detection in SAT solver to define some variables");

    /* po::options_description debug_options("Debug options"); */
    /* debug_options.add_options() */
    program.add_argument("--fastbackw")
        .action([&](const auto& a) {conf.fast_backw = std::atoi(a.c_str());})
        .default_value(conf.fast_backw)
        .help("fast_backw");
    program.add_argument("--gaussj")
        .action([&](const auto& a) {conf.gauss_jordan = std::atoi(a.c_str());})
        .default_value(conf.gauss_jordan)
        .help("Use XOR finding and Gauss-Jordan elimination");
    program.add_argument("--iter1")
        .action([&](const auto& a) {simp_conf.iter1 = std::atoi(a.c_str());})
        .default_value(simp_conf.iter1)
        .help("Puura iterations before oracle");
    program.add_argument("--iter1grow")
        .action([&](const auto& a) {simp_conf.bve_grow_iter1 = std::atoi(a.c_str());})
        .default_value(simp_conf.bve_grow_iter1)
        .help("Puura BVE grow rate allowed before Oracle");
    program.add_argument("--iter2")
        .action([&](const auto& a) {simp_conf.iter2 = std::atoi(a.c_str());})
        .default_value(simp_conf.iter2)
        .help("Puura iterations after oracle");
    program.add_argument("--iter2grow")
        .action([&](const auto& a) {simp_conf.bve_grow_iter2 = std::atoi(a.c_str());})
        .default_value(simp_conf.bve_grow_iter2)
        .help("Puura BVE grow rate allowed after Oracle");
    program.add_argument("--oraclesparsify")
        .action([&](const auto& a) {simp_conf.oracle_sparsify = std::atoi(a.c_str());})
        .default_value(simp_conf.oracle_sparsify)
        .help("Use Oracle to sparsify");
    program.add_argument("--oraclevivif")
        .action([&](const auto& a) {simp_conf.oracle_vivify = std::atoi(a.c_str());})
        .default_value(simp_conf.oracle_vivify)
        .help("Use oracle to vivify");
    program.add_argument("--oraclevivifgetl")
        .action([&](const auto& a) {simp_conf.oracle_vivify_get_learnts = std::atoi(a.c_str());})
        .default_value(simp_conf.oracle_vivify_get_learnts)
        .help("Use oracle to vivify get learnts");
    program.add_argument("--renumber")
        .action([&](const auto& a) {renumber = std::atoi(a.c_str());})
        .default_value(renumber)
        .help("Renumber variables to start from 1...N in CNF. Setting this to 0 is EXPERIMENTAL!!");
    program.add_argument("--distill")
        .action([&](const auto& a) {conf.distill = std::atoi(a.c_str());})
        .default_value(conf.distill);
    program.add_argument("--bve")
        .action([&](const auto& a) {conf.bve_during_elimtofile = std::atoi(a.c_str());})
        .default_value(conf.bve_during_elimtofile)
        .help("Use BVE during simplificaiton of the formula");
    program.add_argument("--bce")
        .action([&](const auto& a) {conf.bce = std::atoi(a.c_str());})
        .default_value(conf.bce)
        .help("Use blocked clause elimination (BCE). VERY experimental!!");
    program.add_argument("--red")
        .action([&](const auto& a) {redundant_cls = std::atoi(a.c_str());})
        .default_value(redundant_cls)
        .help("Also dump redundant clauses");
    program.add_argument("--specifiedorder")
        .action([&](const auto& a) {conf.specified_order_fname = a;})
        .default_value(conf.specified_order_fname)
        .help("Try to remove variables from the independent set in this order. File must contain a variable on each line. Variables start at ZERO. Variable from the BOTTOM will be removed FIRST. This is for DEBUG ONLY");

    program.add_argument("files").remaining().help("input file and output file");
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
        sampl_vars, simp_conf, renumber, !recover_file.empty());

    delete arjun; arjun = nullptr;
    if (extend_indep && synthesis_define) {
        cout << "ERROR: can't have both --extend and --synthdefine" << endl;
        exit(-1);
    }
    if (extend_indep) {
        Arjun arj2;
        arj2.new_vars(ret.nvars);
        arj2.set_verbosity(conf.verb);
        for(const auto& cl: ret.cnf) arj2.add_clause(cl);
        arj2.set_starting_sampling_set(ret.sampling_vars);
        ret.sampling_vars = arj2.extend_indep_set();
    }

    if (synthesis_define) {
        Arjun arj2;
        arj2.new_vars(ret.nvars);
        arj2.set_verbosity(conf.verb);
        for(const auto& cl: ret.cnf) arj2.add_clause(cl);
        arj2.set_starting_sampling_set(ret.sampling_vars);
        ret.sampling_vars = arj2.synthesis_define();
    }

    // TODO fix recover file based on SCNF renumbering
    if (!recover_file.empty()) {
        std::ofstream f(recover_file, std::ios::out | std::ios::binary);
        f.write(&ret.sol_ext_data[0], ret.sol_ext_data.size());
        f.close();
    }

    if (renumber) ret.renumber_sampling_vars_for_ganak();
    cout << "c [arjun] dumping simplified problem to '" << elimtofile << "'" << endl;
    write_simpcnf(ret, elimtofile, orig_cnf_must_mult_exp2, redundant_cls);
    cout << "c [arjun] Dumping took: " << std::setprecision(2) << (cpuTime() - dump_start_time) << endl;
    cout << "c [arjun] All done. T: " << std::setprecision(2) << (cpuTime() - start_time) << endl;
}

void set_config(ArjunNS::Arjun* arj) {
    if (!compute_indep) {
        gates = 0;
        conf.backward = 0;
        conf.empty_occs_based = 0;
    }

    cout << "c [arjun] using seed: " << conf.seed << endl;
    arj->set_verbosity(conf.verb);
    arj->set_seed(conf.seed);
    arj->set_fast_backw(conf.fast_backw);
    arj->set_distill(conf.distill);
    arj->set_specified_order_fname(conf.specified_order_fname);
    arj->set_intree(conf.intree);
    arj->set_bve_pre_simplify(conf.bve_pre_simplify);
    arj->set_unknown_sort(conf.unknown_sort);
    arj->set_do_unate(conf.do_unate);
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
    feenableexcept(FE_INVALID   | FE_DIVBYZERO | FE_OVERFLOW);
    #endif

    //Reconstruct the command line so we can emit it later if needed
    string command_line;
    for(int i = 0; i < argc; i++) {
        command_line += string(argv[i]);
        if (i+1 < argc) command_line += " ";
    }

    add_arjun_options();
    try {
        program.parse_args(argc, argv);
        if (program.is_used("--help")) {
            cout
            << "Minimal projection set finder and simplifier." << endl << endl
            << "arjun [options] inputfile [outputfile]" << endl;
            cout << program << endl;
            std::exit(0);
        }
    }
    catch (const std::exception& err) {
        std::cerr << err.what() << std::endl;
        std::cerr << program;
        exit(-1);
    }

    if (program["version"] == true) {
        cout << "c [arjun] SHA revision: " << arjun->get_version_info() << endl;
        cout << "c [arjun] Compilation environment: " << arjun->get_compilation_env() << endl;
        std::exit(0);
    }

    cout << "c Arjun Version: " << arjun->get_version_info() << endl;
    cout << arjun->get_solver_version_info();
    cout << "c executed with command line: " << command_line << endl;

    start_time = cpuTime();
    set_config(arjun);

    //parsing the input
    vector<std::string> files;
    try {
        files = program.get<std::vector<std::string>>("files");
        if (files.size() > 3) {
            cout << "ERROR: you can only pass at most 3 positional parameters: an INPUT file"
                ", optionally an OUTPUT file, and optionally a RECOVER file" << endl;
            exit(-1);
        }
    } catch (std::logic_error& e) {
        cout << "ERROR: you must give at least an input file" << endl;
        exit(-1);
    }

    const string inp = files[0];
    if (files.size() >= 2) elimtofile = files[1];
    if (files.size() >= 3) recover_file = files[2];
    readInAFile(inp, arjun, orig_sampling_set_size, orig_cnf_must_mult_exp2, recompute_sampling_set);
    cout << "c [arjun] original sampling set size: " << orig_sampling_set_size << endl;

    vector<uint32_t> indep_vars = arjun->get_indep_set();
    print_final_indep_set(indep_vars, arjun->get_empty_occ_sampl_vars(), elimtofile.empty());
    cout << "c [arjun] finished "
        << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_time) << endl;

    if (!elimtofile.empty()) {
        if (simptofile) elim_to_file(indep_vars);
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
