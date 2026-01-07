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

#include <memory>
#if defined(__GNUC__) && defined(__linux__)
#include <cfenv>
#endif

#include <iostream>
#include <iomanip>
#include <vector>
#include <string>
#include "argparse.hpp"
#include <cryptominisat5/dimacsparser.h>

#include "time_mem.h"
#include "arjun.h"
#include "config.h"
#include "helper.h"

#define myopt(name, var, fun, hhelp) \
    program.add_argument(name) \
        .action([&](const auto& a) {var = std::fun(a.c_str());}) \
        .default_value(var) \
        .help(hhelp)
#define myopt2(name1, name2, var, fun, hhelp) \
    program.add_argument(name1, name2) \
        .action([&](const auto& a) {var = std::fun(a.c_str());}) \
        .default_value(var) \
        .help(hhelp)

using std::cout;
using std::endl;
using std::string;
using std::vector;
using std::unique_ptr;
using namespace CMSat;

argparse::ArgumentParser program = argparse::ArgumentParser("arjun", ArjunNS::Arjun::get_version_sha1(),
        argparse::default_arguments::help);
double start_time;
ArjunInt::Config conf;
std::unique_ptr<ArjunNS::Arjun> arjun;
string input_file;
string elimtofile;

ArjunNS::SimpConf simp_conf;
ArjunNS::Arjun::ElimToFileConf etof_conf;
int do_gates = 1;
int redundant_cls = true;
int simptofile = true;
int sampl_start_at_zero = false;
int do_synth_bve = true;
int do_pre_backbone = 0;

int synthesis = false;
int do_revbce = false;
int do_minim_indep = true;
string debug_minim;
double cms_glob_mult = -1.0;
int mode = 0;
unique_ptr<FieldGen> fg = nullptr;

string print_version() {
    std::stringstream ss;
    ss << "c o Arjun SHA1: " << arjun->get_version_sha1() << endl;
    ss << "c o SBVA SHA1: " << arjun->get_sbva_version_sha1() << endl;
    ss << "c o CMS SHA1: " << arjun->get_solver_version_sha1() << endl;
    ss << arjun->get_thanks_info("c o ") << endl;
    ss << arjun->get_solver_thanks_info("c o ") << endl;
    ss << "c o [arjun] Compilation environment: " << arjun->get_compilation_env();
    return ss.str();
}

void add_arjun_options() {
    myopt2("-v", "--verb", conf.verb, atoi, "Verbosity");
    program.add_argument("-v", "--version") \
        .action([&](const auto&) {print_version(); exit(0);}) \
        .flag()
        .help("Print version and exit");

    myopt("--mode", mode , atoi, "0=counting, 1=weightd counting");
    myopt("--allindep", etof_conf.all_indep , atoi, "All variables can be made part of the indepedent support. Indep support is given ONLY to help the solver.");
    myopt("--maxc", conf.backw_max_confl, atoi,"Maximum conflicts per variable in backward mode");
    myopt("--revbce", do_revbce, atoi,"Perform reverse BCE");
    myopt("--sbva", etof_conf.num_sbva_steps, atoi,"SBVA timeout. 0 = no sbva");
    myopt("--prebackbone", do_pre_backbone, atoi,"Perform backbone before other things");

    // synth
    myopt("--samples", conf.num_samples, atoi,"Number of samples");
    myopt("--unate", etof_conf.do_unate, atoi,"Perform unate analysis");
    myopt("--synthbve", do_synth_bve, atoi,"Perform BVE for synthesis");
    program.add_argument("--synth")
        .action([&](const auto&) {synthesis = 1;})
        .default_value(synthesis)
        .flag()
        .help("Run synthesis");
    myopt("--extend", etof_conf.do_extend_indep, atoi,"Extend independent set just before CNF dumping");
    myopt("--debugsynth", conf.debug_synth, string,"Debug synthesis, prefix with this fname");
    myopt("--manthanminconfl", conf.manthan_maxsat_min_conflict, atoi,"Manthan should try to minimize conflicts via maxsat when repairing");

    // Simplification options for minim
    myopt("--probe", conf.probe_based, atoi,"Do probing during orignal Arjun");
    myopt("--bvepresimp", conf.bve_pre_simplify, atoi,"simplify");
    myopt("--simp", conf.simp, atoi,"Do ~ sort of simplification during indep minimixation");
    myopt("--probe", conf.probe_based, atoi,"Use simple probing to set (and define) some variables");
    myopt("--intree", conf.intree, atoi,"intree");
    myopt("--extendccnr", conf.extend_ccnr, atoi,"Filter extend with CCNR. If 0, none otherwise, in the million mems");
    myopt("--autarkies", conf.autarkies, atoi,"Try to find autaries");

    // Gate options
    myopt("--gates", do_gates, atoi,"Turn on/off all gate-based definability");
    myopt("--nogatebelow", conf.no_gates_below, atof,"Don't use gates below this incidence relative position (1.0-0.0) to minimize the independent set. Gates are not very accurate, but can save a LOT of time. We use them to get rid of most of the uppert part of the sampling set only. Default is 99% is free-for-all, the last 1% we test. At 1.0 we test everything, at 0.0 we try using gates for everything.");
    myopt("--orgate", conf.or_gate_based, atoi,"Use 3-long gate detection in SAT solver to define variables");
    myopt("--irreggate", conf.irreg_gate_based, atoi,"Use irregular gate-based removal of vars from indep set");
    myopt("--itegate", conf.ite_gate_based, atoi,"Use ITE gate detection in SAT solver to define some variables");
    myopt("--xorgate", conf.xor_gates_based, atoi,"Use XOR detection in SAT solver to define some variables");

    // AppMC
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
        .help("Set CNF simplification options for appmc");

    // Detailed Configuration
    myopt("--sbvaclcut", etof_conf.sbva_cls_cutoff, atoi,"SBVA heuristic cutoff. Higher -> only appied to more clauses");
    myopt("--sbvalitcut", etof_conf.sbva_lits_cutoff, atoi,"SBVA heuristic cutoff. Higher -> only appied to larger clauses");
    myopt("--findbins", conf.oracle_find_bins, atoi,"How aggressively find binaries via oracle");
    myopt("--sbvabreak",  etof_conf.sbva_tiebreak, atoi,"SBVA tie break: 1=sbva or 0=bva");
    myopt("--gaussj", conf.gauss_jordan, atoi,"Use XOR finding and Gauss-Jordan elimination");
    myopt("--iter1", simp_conf.iter1, atoi,"Puura iterations before oracle");
    myopt("--iter1grow", simp_conf.bve_grow_iter1, atoi,"Puura BVE grow rate allowed before Oracle");
    myopt("--iter2", simp_conf.iter2, atoi,"Puura iterations after oracle");
    myopt("--iter2grow", simp_conf.bve_grow_iter2, atoi,"Puura BVE grow rate allowed after Oracle");
    myopt("--bveresolvmaxsz", simp_conf.bve_too_large_resolvent, atoi,"Puura BVE max resolvent size in literals. -1 == no limit");
    myopt("--oraclesparsify", simp_conf.oracle_sparsify, atoi,"Use Oracle to sparsify");
    myopt("--oraclevivif", simp_conf.oracle_vivify, atoi,"Use oracle to vivify");
    myopt("--oraclevivifgetl", simp_conf.oracle_vivify_get_learnts, atoi,"Use oracle to vivify get learnts");
    myopt("--distill", conf.distill, atoi, "Distill clauses before minimization of indep");
    myopt("--weakenlim", simp_conf.weaken_limit, atoi, "Limit to weaken BVE resolvents");
    myopt("--bce", etof_conf.do_bce, atoi, "Use blocked clause elimination (BCE) statically");
    myopt("--red", redundant_cls, atoi,"Also dump redundant clauses");

    // Debug
    myopt("--renumber", etof_conf.do_renumber, atoi,"Renumber variables to start from 1...N in CNF.");
    myopt("--specifiedorder", conf.specified_order_fname, string, "Try to remove variables from the independent set in this order. File must contain a variable on each line. Variables start at ZERO. Variable from the BOTTOM will be removed FIRST. This is for DEBUG ONLY");
    myopt("--minimize", do_minim_indep, atoi,"Minimize indep set");
    myopt("--debugminim", debug_minim, string,"Create this file that is the CNF after indep set minimization");
    myopt("--cmsmult", conf.cms_glob_mult, atof,"Multiply timeouts in CMS by this. Default is -1, which means no change. Useful for debugging");

    program.add_argument("files").remaining().help("input file and output file");
}

void print_final_sampl_set(ArjunNS::SimplifiedCNF& cnf, const vector<uint32_t>& orig_sampl_vars) {
    cout
    << "c o [arjun] final set size: " << std::setw(7) << cnf.get_sampl_vars().size()
    << " percent of original: " << std::setw(6) << std::setprecision(3)
    << std::fixed
    << stats_line_percent(cnf.get_sampl_vars().size(), orig_sampl_vars.size()) << " %" << endl;

    cout << "c p show ";
    for(const uint32_t s: cnf.get_sampl_vars()) cout << s+1 << " ";
    cout << "0" << endl;
    cout << "c p optshow ";
    for(const uint32_t s: cnf.get_opt_sampl_vars()) cout << s+1 << " ";
    cout << "0" << endl;
    cout << "c MUST MULTIPLY BY " << *cnf.get_multiplier_weight() << std::endl;
}

void set_config(ArjunNS::Arjun* arj) {
    arj->set_verb(conf.verb);
    arj->set_distill(conf.distill);
    arj->set_specified_order_fname(conf.specified_order_fname);
    arj->set_intree(conf.intree);
    arj->set_extend_ccnr(conf.extend_ccnr);
    arj->set_bve_pre_simplify(conf.bve_pre_simplify);
    arj->set_cms_glob_mult(conf.cms_glob_mult);
    arj->set_autarkies(conf.autarkies);
    if (do_gates) {
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
    arj->set_num_samples(conf.num_samples);
    arj->set_extend_max_confl(conf.extend_max_confl);
    arj->set_oracle_find_bins(conf.oracle_find_bins);
    arj->set_manthan_maxsat_min_conflict(conf.manthan_maxsat_min_conflict);
}

void check_cnf_sat(const ArjunNS::SimplifiedCNF& cnf) {
    CMSat::SATSolver solver;
    solver.set_verbosity(0);
    solver.set_find_xors(false);
    solver.new_vars(cnf.nVars());
    for(const auto& cl: cnf.get_clauses()) solver.add_clause(cl);
    for(const auto& cl: cnf.get_red_clauses()) solver.add_red_clause(cl);
    CMSat::lbool ret = solver.solve();
    if (ret == CMSat::l_False) {
        cout << "c o [arjun] Input CNF is UNSAT!" << endl;
        exit(EXIT_FAILURE);
    }
}

#ifdef SYNTH
void do_synthesis() {
    if (etof_conf.all_indep) {
        cout << "ERROR: synthesis with --allindep makes no sense" << endl;
        exit(EXIT_FAILURE);
    }
    ArjunNS::SimplifiedCNF cnf(fg);
    cnf.set_need_aig();
    read_in_a_file(input_file, &cnf, etof_conf.all_indep, fg);
    if (etof_conf.all_indep) {
        cout << "ERROR: CNF had no indep set, we cannot do synthesis" << endl;
        exit(EXIT_FAILURE);
    }
    cnf.clean_idiotic_mccomp_weights();
    cnf.set_orig_clauses(cnf.get_clauses());
    cnf.set_orig_sampl_vars(cnf.get_sampl_vars());
    assert(cnf.get_need_aig() && cnf.defs_invariant());
    check_cnf_sat(cnf);
    cout << "c o ignoring --backbone option, doing backbone for synth no matter what" << endl;
    if (do_pre_backbone) arjun->standalone_backbone(cnf);
    if (do_synth_bve) {
        /* simp_conf.bve_too_large_resolvent = -1; */
        cnf = arjun->standalone_get_simplified_cnf(cnf, simp_conf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-1-simplified_cnf.aig");
    }

    if (etof_conf.do_extend_indep) {
        arjun->standalone_unsat_define(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-2-unsat_define.aig");
    }

    if (etof_conf.do_unate) {
        arjun->standalone_unate(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-3-unsat_unate.aig");
    }

    // backw_round_synth
    if (do_minim_indep) {
        arjun->standalone_minimize_indep_synt(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-4-minim_idep_synt.aig");
    }

    arjun->standalone_manthan(cnf);
    if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-5-manthan.aig");
    cnf.clear_orig_sampl_defs();
}
#endif

void do_minimize() {
    ArjunNS::SimplifiedCNF cnf(fg);
    read_in_a_file(input_file, &cnf, etof_conf.all_indep, fg);
    cnf.clean_idiotic_mccomp_weights();
    cnf.check_cnf_sampl_sanity();

    if (do_pre_backbone) arjun->standalone_backbone(cnf);
    const auto orig_sampl_vars = cnf.get_sampl_vars();
    if (do_minim_indep) arjun->standalone_minimize_indep(cnf, etof_conf.all_indep);
    if (!debug_minim.empty()) {
        cnf.write_simpcnf(debug_minim, false);
        auto cnf2 = cnf;
        cnf2.renumber_sampling_vars_for_ganak();
        cnf2.write_simpcnf(debug_minim+"-renum", false);
    }

    if (!elimtofile.empty()) {
        arjun->standalone_elim_to_file(cnf, etof_conf, simp_conf);
        cnf.write_simpcnf(elimtofile, redundant_cls);
        cout << "c o [arjun] dumped simplified problem to '" << elimtofile << "'" << endl;
    } else {
        print_final_sampl_set(cnf, orig_sampl_vars);
    }
}

int main(int argc, char** argv) {
    arjun = std::make_unique<ArjunNS::Arjun>();
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
    } catch (const std::exception& err) {
        std::cerr << err.what() << std::endl;
        std::cerr << program;
        exit(EXIT_FAILURE);
    }

    if (etof_conf.sbva_tiebreak != 0 && etof_conf.sbva_tiebreak != 1) {
        cout << "Unrecognized tie break: sbva/bva allowed." << endl;
        exit(EXIT_FAILURE);
    }

    if (conf.verb) {
        cout << print_version() << endl;
        cout << "c o executed with command line: " << command_line << endl;
    }

    switch (mode) {
        case 0:
            fg = std::make_unique<ArjunNS::FGenMpz>();
            break;
        case 1:
            fg = std::make_unique<ArjunNS::FGenMpq>();
            break;
        default:
            cout << "c o [arjun] ERROR: Unknown mode" << endl;
            exit(EXIT_FAILURE);
    }

    if (program["version"] == true) exit(0);

    start_time = cpuTime();
    set_config(arjun.get());

    //parsing the input
    vector<std::string> files;
    try {
        files = program.get<std::vector<std::string>>("files");
        if (files.size() > 2) {
            cout << "ERROR: you can only pass at most 3 positional parameters: an INPUT file"
                ", optionally an OUTPUT file" << endl;
            exit(EXIT_FAILURE);
        }
    } catch (std::logic_error& e) {
        cout << "ERROR: you must give at least an input file" << endl;
        exit(EXIT_FAILURE);
    }

    input_file = files[0];
    if (files.size() >= 2) elimtofile = files[1];
    cout << "c o [arjun] Input file: " << input_file << endl;
    if (!elimtofile.empty())
        cout << "c o [arjun] Output file: " << elimtofile << endl;
    if (synthesis) {
#ifdef SYNTH
        do_synthesis();
#else
        cout << "c o [arjun] ERROR: synthesis not enabled in this build" << endl;
        exit(EXIT_FAILURE);
#endif
    } else {
        do_minimize();
    }
    cout << "c o [arjun] All done. T: " << std::setprecision(2) << std::fixed
        << (cpuTime() - start_time) << endl;

    return 0;
}
