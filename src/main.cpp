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
#include <string>
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
string input_file;
string elimtofile;

SimpConf simp_conf;
int renumber = true;
bool gates = true;
int do_extend_indep = true;
int redundant_cls = true;
int compute_indep = true;
int simptofile = true;
int sampl_start_at_zero = false;
int64_t sbva_steps = 1000;
int sbva_cls_cutoff = 4;
int sbva_lits_cutoff = 5;
int sbva_tiebreak = 1;
int do_bce = true;
int debug_synt = false;

int synthesis = false;
int do_unate = false;
int do_revbce = false;
int do_minim_indep = true;
bool all_indep = false;
string debug_minim;
int do_pre_manthan = false;

void add_arjun_options()
{
    conf.verb = 1;
    program.add_argument("-v", "--verb")
        .action([&](const auto& a) {conf.verb = std::atoi(a.c_str());})
        .default_value(conf.verb)
        .help("verbosity");
    program.add_argument("--allindep")
        .action([&](const auto& a) {all_indep = std::atoi(a.c_str());})
        .default_value(all_indep)
        .help("All variables are in the independent set. The indep set is given only to help Arjun");
    program.add_argument("--premanthan")
        .action([&](const auto& a) {do_pre_manthan = std::atoi(a.c_str());})
        .default_value(do_pre_manthan)
        .help("All variables are in the independent set. The indep set is given only to help Arjun");
    program.add_argument("--maxc")
        .action([&](const auto& a) {conf.backw_max_confl = std::atoi(a.c_str());})
        .default_value(conf.backw_max_confl)
        .help("Maximum conflicts per variable in backward mode");
    program.add_argument("--extend")
        .action([&](const auto& a) {do_extend_indep = std::atoi(a.c_str());})
        .default_value(do_extend_indep)
        .help("Extend independent set just before CNF dumping");
    program.add_argument("--synth")
        .action([&](const auto&) {synthesis = 1;})
        .default_value(synthesis)
        .flag()
        .help("Define for synthesis");
    program.add_argument("--unate")
        .action([&](const auto& a) {do_unate = std::atoi(a.c_str());})
        .default_value(do_unate)
        .help("Perform unate analysis");
    program.add_argument("--revbce")
        .action([&](const auto& a) {do_revbce = std::atoi(a.c_str());})
        .default_value(do_revbce)
        .help("Perform reverse BCE");
    program.add_argument("--sbva")
        .action([&](const auto& a) {sbva_steps = std::atoi(a.c_str());})
        .default_value(sbva_steps)
        .help("SBVA timeout. 0 = no sbva");
    program.add_argument("--debugsynt")
        .action([&](const auto&) {debug_synt = true;})
        .flag()
        .help("Debug synthesis");
    program.add_argument("--sbvaclcut")
        .action([&](const auto& a) {sbva_cls_cutoff = std::atoi(a.c_str());})
        .default_value(sbva_cls_cutoff)
        .help("SBVA heuristic cutoff. The higher, the more it needs to improve to be applied");
    program.add_argument("--sbvalitcut")
        .action([&](const auto& a) {sbva_lits_cutoff = std::atoi(a.c_str());})
        .default_value(sbva_lits_cutoff)
        .help("SBVA heuristic cutoff. The higher, the more it needs to improve to be applied");
    program.add_argument("--sbvabreak")
        .action([&](const auto& a) {
                sbva_tiebreak = std::atoi(a.c_str());
                if (sbva_tiebreak != 0 && sbva_tiebreak != 1 ) {
                    cout << "Unrecognized tie break: sbva/bva allowed." << endl;
                    exit(-1);}
                })
        .default_value(1)
        .help("SBVA tie break: sbva or bva");

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
    program.add_argument("--minimize")
        .action([&](const auto& a) {do_minim_indep = std::atoi(a.c_str());})
        .default_value(do_minim_indep)
        .help("Minimize indep set");
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
    program.add_argument("--bveresolvmaxsz")
        .action([&](const auto& a) {simp_conf.bve_too_large_resolvent = std::atoi(a.c_str());})
        .default_value(simp_conf.bve_too_large_resolvent)
        .help("Puura BVE max resolvent size in literals. -1 == no limit");
    program.add_argument("--oraclesparsify")
        .action([&](const auto& a) {simp_conf.oracle_sparsify = std::atoi(a.c_str());})
        .default_value(simp_conf.oracle_sparsify)
        .help("Use Oracle to sparsify");
    program.add_argument("--appmc")
        .action([&](const auto&) {
                simp_conf.appmc = true;
                simp_conf.oracle_vivify = true;
                simp_conf.oracle_sparsify = false;
                simp_conf.oracle_vivify_get_learnts = 1;
                simp_conf.iter1 = 2;
                simp_conf.iter2 = 0;
                })
        .flag()
        .help("Set CNF options for appmc");
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
    program.add_argument("--bce")
        .action([&](const auto& a) {do_bce = std::atoi(a.c_str());})
        .default_value(do_bce)
        .help("Use blocked clause elimination (BCE). VERY experimental!!");
    program.add_argument("--red")
        .action([&](const auto& a) {redundant_cls = std::atoi(a.c_str());})
        .default_value(redundant_cls)
        .help("Also dump redundant clauses");
    program.add_argument("--specifiedorder")
        .action([&](const auto& a) {conf.specified_order_fname = a;})
        .default_value(conf.specified_order_fname)
        .help("Try to remove variables from the independent set in this order. "
                "File must contain a variable on each line. "
                "Variables start at ZERO. Variable from the BOTTOM will be removed FIRST. This is for DEBUG ONLY");
    program.add_argument("--debugminim")
        .action([&](const auto& a) {debug_minim = a;})
        .help("Create this file that is the CNF after indep set minimization");

    program.add_argument("files").remaining().help("input file and output file");
}

void print_final_sampl_set(SimplifiedCNF& cnf, const vector<uint32_t>& orig_sampl_vars) {
    cout
    << "c o [arjun] final set size: " << std::setw(7) << cnf.sampl_vars.size()
    << " percent of original: " << std::setw(6) << std::setprecision(3)
    << std::fixed
    << stats_line_percent(cnf.sampl_vars.size(), orig_sampl_vars.size()) << " %" << endl;

    cout << "c p show ";
    for(const uint32_t s: cnf.sampl_vars) cout << s+1 << " ";
    cout << "0" << endl;
    cout << "c p optshow ";
    for(const uint32_t s: cnf.opt_sampl_vars) cout << s+1 << " ";
    cout << "0" << endl;
    cout << "c MUST MULTIPLY BY " << cnf.multiplier_weight << std::endl;
}

void set_config(ArjunNS::Arjun* arj) {
    arj->set_verb(conf.verb);
    arj->set_distill(conf.distill);
    arj->set_specified_order_fname(conf.specified_order_fname);
    arj->set_intree(conf.intree);
    arj->set_bve_pre_simplify(conf.bve_pre_simplify);
    if (gates) {
      arj->set_or_gate_based(conf.or_gate_based);
      arj->set_ite_gate_based(conf.ite_gate_based);
      arj->set_xor_gates_based(conf.xor_gates_based);
      arj->set_irreg_gate_based(conf.irreg_gate_based);
    } else {
      cout << "c o NOTE: all gates are turned off due to `--gates 0`" << endl;
      arj->set_or_gate_based   (0);
      arj->set_ite_gate_based  (0);
      arj->set_xor_gates_based (0);
      arj->set_irreg_gate_based(0);
    }
    arj->set_no_gates_below(conf.no_gates_below);
    arj->set_probe_based(conf.probe_based);
    arj->set_backw_max_confl(conf.backw_max_confl);
    arj->set_gauss_jordan(conf.gauss_jordan);
    arj->set_simp(conf.simp);
}

void do_synthesis() {
    assert(!elimtofile.empty());
    SimplifiedCNF cnf;
    read_in_a_file(input_file, &cnf, all_indep);
    arjun->only_backbone(cnf);
    if (do_unate) arjun->only_unate(cnf);


    if (do_pre_manthan) {
        // First we extend
        arjun->only_unsat_define(cnf);

        // Then we BVE
        simp_conf.bve_too_large_resolvent = -1;
        cnf = arjun->only_get_simplified_cnf(cnf, simp_conf);
        if (do_revbce) arjun->only_reverse_bce(cnf);
        if (false && do_minim_indep) arjun->only_run_minimize_indep_synth(cnf);
        write_synth(cnf, elimtofile, false);
    }
    if (cnf.opt_sampl_vars.size() == cnf.nVars()) {
        cout << "c o [arjun] No variables to synthesize" << endl;
        return;
    }
    arjun->only_manthan(cnf);
}

void do_minimize() {
    SimplifiedCNF cnf;
    read_in_a_file(input_file, &cnf, all_indep);
    arjun->only_backbone(cnf);
    const auto orig_sampl_vars = cnf.sampl_vars;
    if (do_minim_indep) {
        arjun->only_run_minimize_indep(cnf);
    }
    if (!debug_minim.empty()) {
        cnf.write_simpcnf(debug_minim, false, true);
        auto cnf2 = cnf;
        cnf2.renumber_sampling_vars_for_ganak();
        cnf2.write_simpcnf(debug_minim+"-renum", false, true);
    }

    if (!elimtofile.empty()) {
        arjun->elim_to_file(cnf, all_indep,
            do_extend_indep, do_bce,
            do_unate, simp_conf,
            sbva_steps, sbva_cls_cutoff, sbva_lits_cutoff, sbva_tiebreak);

        cnf.write_simpcnf(elimtofile, redundant_cls, true);
        cout << "c o [arjun] dumped simplified problem to '" << elimtofile << "'" << endl;
    } else {
        print_final_sampl_set(cnf, orig_sampl_vars);
    }
}

int main(int argc, char** argv) {
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

    if (conf.verb || program["version"] == true) {
        cout << "c o Arjun Version: " << arjun->get_version_info() << endl;
        cout << arjun->get_solver_version_info();
        cout << "c o [arjun] Compilation environment: " << arjun->get_compilation_env() << endl;
        cout << "c o executed with command line: " << command_line << endl;
    }
    if (program["version"] == true) exit(0);

    start_time = cpuTime();
    set_config(arjun);

    //parsing the input
    vector<std::string> files;
    try {
        files = program.get<std::vector<std::string>>("files");
        if (files.size() >= 3) {
            cout << "ERROR: you can only pass at most 3 positional parameters: an INPUT file"
                ", optionally an OUTPUT file, and optionally a RECOVER file" << endl;
            exit(-1);
        }
    } catch (std::logic_error& e) {
        cout << "ERROR: you must give at least an input file" << endl;
        exit(-1);
    }

    input_file = files[0];
    if (files.size() >= 2) elimtofile = files[1];
    cout << "c o [arjun] Input file: " << input_file << endl;
    if (!elimtofile.empty())
        cout << "c o [arjun] Output file: " << elimtofile << endl;
    if (synthesis) {
        do_synthesis();
    } else {
        do_minimize();
    }
    cout << "c o [arjun] All done. T: " << std::setprecision(2) << std::fixed
        << (cpuTime() - start_time) << endl;

    delete arjun;
    return 0;
}
