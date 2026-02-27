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

#include "src/constants.h"
#include <memory>
#if defined(__GNUC__) && defined(__linux__)
#include <cfenv>
#endif

#include <charconv>
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
#include "synth.h"

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
ArjunNS::Arjun::ManthanConf mconf;
int do_gates = 1;
int redundant_cls = true;
int simptofile = true;
int sampl_start_at_zero = false;
int do_synth_bve = true;
int do_pre_backbone = 0;
string mstrategy = "const(max_repairs=400),const(max_repairs=400,inv_learnt=1),bve";

int synthesis = false;
int do_unate = false;
int do_unate_def = false;
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

static int fc_int(const std::string& s) {
    int val = 0;
    std::from_chars(s.data(), s.data() + s.size(), val);
    return val;
}
static double fc_double(const std::string& s) {
    size_t pos;
    double val = std::stod(s, &pos);
    if (pos != s.size()) throw std::invalid_argument("trailing characters in double: " + s);
    return val;
}
static const std::string& fc_string(const std::string& s) { return s; }

template<typename T, typename F>
void myopt(const char* name, T& var, F fun, const char* hhelp) {
    using r = std::decay_t<std::invoke_result_t<F, const std::string&>>;
    static_assert(std::is_floating_point_v<r> == std::is_floating_point_v<T>,
        "Floating-point mismatch: use fc_double for floating-point vars, fc_int for integral vars");
    static_assert(std::is_integral_v<r> == std::is_integral_v<T>,
        "Integral/string mismatch: use fc_int for integral vars, fc_string for string vars");
    program.add_argument(name)
        .action([&var, fun](const auto& a) { var = fun(a); })
        .default_value(var)
        .help(hhelp);
}
template<typename T, typename F>
void myopt2(const char* name1, const char* name2, T& var, F fun, const char* hhelp) {
    using r = std::decay_t<std::invoke_result_t<F, const std::string&>>;
    static_assert(std::is_floating_point_v<r> == std::is_floating_point_v<T>,
        "Floating-point mismatch: use fc_double for floating-point vars, fc_int for integral vars");
    static_assert(std::is_integral_v<r> == std::is_integral_v<T>,
        "Integral/string mismatch: use fc_int for integral vars, fc_string for string vars");
    program.add_argument(name1, name2)
        .action([&var, fun](const auto& a) { var = fun(a); })
        .default_value(var)
        .help(hhelp);
}
template<typename T>
void myflag(const char* name, T& var, const char* hhelp) {
    static_assert(std::is_same_v<T, int>, "myflag var must be int");
    program.add_argument(name)
        .action([&var](const auto&) { var = 1; })
        .default_value(var)
        .flag()
        .help(hhelp);
}

void add_arjun_options() {
    myopt2("-v", "--verb", conf.verb, fc_int, "Verbosity");
    program.add_argument("-v", "--version") \
        .action([&](const auto&) {print_version(); exit(0);}) \
        .flag()
        .help("Print version and exit");

    myopt("--mode", mode , fc_int, "0=counting, 1=weightd counting");
    myopt("--allindep", etof_conf.all_indep , fc_int, "All variables can be made part of the indepedent support. Indep support is given ONLY to help the solver.");
    myopt("--maxc", conf.backw_max_confl, fc_int,"Maximum conflicts per variable in backward mode");
    myopt("--revbce", do_revbce, fc_int,"Perform reverse BCE");
    myopt("--sbva", etof_conf.num_sbva_steps, fc_int,"SBVA timeout. 0 = no sbva");
    myopt("--prebackbone", do_pre_backbone, fc_int,"Perform backbone before other things");
    myopt("--seed", conf.seed, fc_int, "Random seed");

    // synth main
    myflag("--synth", synthesis, "Run synthesis");
    myflag("--synthmore", synthesis, "Run synthesis, with more aggressive BVE options");
    myopt("--maxsat", mconf.maxsat_better_ctx, fc_int, "Use maxsat to find better counterexamples during Manthan");
    myopt("--synthbve", do_synth_bve, fc_int,"Perform BVE for synthesis");
    myopt("--extend", etof_conf.do_extend_indep, fc_int,"Extend independent set just before CNF dumping");
    myopt("--minimconfl", mconf.minimize_conflict, fc_int,"Minimize conflict size when repairing");
    myopt("--simpevery", mconf.simplify_every, fc_int,"Simplify solvers inside Manthan every K loops");
    myopt("--unate", do_unate, fc_int,"Perform unate analysis");
    myopt("--unatedef", do_unate_def, fc_int,"Perform definition-aware unate analysis");
    myopt("--autarky", etof_conf.do_autarky, fc_int,"Perform unate analysis");
    myopt("--monflyorder", mconf.manthan_on_the_fly_order, fc_int,"Use on-the-fly training order and post-training topological order");
    myopt("--moneperloop", mconf.one_repair_per_loop, fc_int,"One repair per CEX loop");
    myopt("--minvertlearn", mconf.inv_learnt, fc_int,"Invert learnt functions");

    // repairing on vars
    myopt("--bwequal", mconf.force_bw_equal, fc_int,"Force BW vars' indicators to be TRUE -- prevents repairing with them, but faster to repair");
    myopt("--bvaxor", mconf.bva_xor_vars, fc_int,"Add XOR over input vars as BVA vars, so we can repair with them");
    myopt("--silentupdate", mconf.silent_var_update, fc_int,"Silently update variables while repairing");
    // Strategy
    myopt("--mstrategy", mstrategy, fc_string,
        "Comma-separated synthesis strategy list, e.g. "
        "\"learn(samples=1,max_repairs=100),learn(max_repairs=800),bve\". "
        "Each non-last strategy runs for 20*max_repairs tries; the last runs unlimited. "
        "Params: manthan_bve, samples, samples_ccnr, minGainSplit, "
        "maximumDepth, sampler_fixed_conflicts, and other ManthanConf fields.");
    // Order
    myopt("--morder", mconf.manthan_order, fc_int,"Order vars: indicence (0), cluster-incidence (1), BVE (2)");
    myopt("--maxsatorder", mconf.maxsat_order, fc_int,"Which order to use to try to fix vars? 0 = norm, 1 = rev");
    myopt("--mbackwsynthorder", mconf.backward_synth_order, fc_int,"Which order to use to try to do backward? 0 = normal, 1 = reverse");
    // solver config
    myopt("--ctxsolver", mconf.ctx_solver_type, fc_int,"Context solver type. 0 = CryptoMiniSat, 1 = CaDiCaL");
    myopt("--repairsolver", mconf.repair_solver_type, fc_int,"Context solver type. 0 = CryptoMiniSat, 1 = CaDiCaL");
    myopt("--repaircache", mconf.repair_cache_size, fc_int,"Repair cache size. 0 = no cache");
    // synth -- sampling
    myopt("--samples", mconf.samples, fc_int,"Number of samples");
    myopt("--samplesccnr", mconf.samples_ccnr, fc_int,"Number of samples from CCNR");
    myopt("--uniqsamp", mconf.do_unique_input_samples, fc_int, "Unique samples on input vars");
    myopt("--filtersamples", mconf.filter_samples, fc_int,"Filter samples from useless ones");
    myopt("--biasedsampling", mconf.biased_sampling, fc_int,"Biased sampling");
    myopt("--fixedconf", mconf.sampler_fixed_conflicts, fc_int,"Restart conflict limit in CMSGen");
    // synth -- decision tree
    myopt("--maxdepth", mconf.max_depth, fc_int,"Maximum depth of decision tree");
    myopt("--minleaf", mconf.min_leaf_size, fc_int,"Minimum leaf size in decision tree");
    myopt("--mingainsplit", mconf.min_gain_split, fc_double,"Minimum gain for a split in decision tree");
    myopt("--learnuseall", mconf.use_all_vars_as_feats, fc_int,"Use all variables as features in decision tree learning. 0 = only inputs");
    // synth -- debug
    myopt("--manthancnf", mconf.write_manthan_cnf, fc_string, "Write Manthan CNF to this file");
    myopt("--debugsynth", conf.debug_synth, fc_string,"Debug synthesis, prefix with this fname");


    // Simplification options for minim
    myopt("--probe", conf.probe_based, fc_int,"Do probing during orignal Arjun");
    myopt("--bvepresimp", conf.bve_pre_simplify, fc_int,"simplify");
    myopt("--simp", conf.simp, fc_int,"Do ~ sort of simplification during indep minimixation");
    myopt("--probe", conf.probe_based, fc_int,"Use simple probing to set (and define) some variables");
    myopt("--intree", conf.intree, fc_int,"intree");

    // Gate options
    myopt("--gates", do_gates, fc_int,"Turn on/off all gate-based definability");
    myopt("--nogatebelow", conf.no_gates_below, fc_double,"Don't use gates below this incidence relative position (1.0-0.0) to minimize the independent set. Gates are not very accurate, but can save a LOT of time. We use them to get rid of most of the uppert part of the sampling set only. Default is 99% is free-for-all, the last 1% we test. At 1.0 we test everything, at 0.0 we try using gates for everything.");
    myopt("--orgate", conf.or_gate_based, fc_int,"Use 3-long gate detection in SAT solver to define variables");
    myopt("--irreggate", conf.irreg_gate_based, fc_int,"Use irregular gate-based removal of vars from indep set");
    myopt("--itegate", conf.ite_gate_based, fc_int,"Use ITE gate detection in SAT solver to define some variables");
    myopt("--xorgate", conf.xor_gates_based, fc_int,"Use XOR detection in SAT solver to define some variables");

    // AppMC
    program.add_argument("--appmc")
        .flag()
        .action([&](const auto&) {simp_conf.appmc = true;})
        .help("Set CNF simplification options for appmc");

    // Detailed Configuration
    myopt("--sbvaclcut", etof_conf.sbva_cls_cutoff, fc_int,"SBVA heuristic cutoff. Higher -> only appied to more clauses");
    myopt("--sbvalitcut", etof_conf.sbva_lits_cutoff, fc_int,"SBVA heuristic cutoff. Higher -> only appied to larger clauses");
    myopt("--findbins", conf.oracle_find_bins, fc_int,"How aggressively find binaries via oracle");
    myopt("--sbvabreak",  etof_conf.sbva_tiebreak, fc_int,"SBVA tie break: 1=sbva or 0=bva");
    myopt("--gaussj", conf.gauss_jordan, fc_int,"Use XOR finding and Gauss-Jordan elimination");
    myopt("--bve", simp_conf.do_bve, fc_int,"Perform BVE during CNF simplification");
    myopt("--iter1", simp_conf.iter1, fc_int,"Puura iterations before oracle");
    myopt("--iter1grow", simp_conf.bve_grow_iter1, fc_int,"Puura BVE grow rate allowed before Oracle");
    myopt("--iter2", simp_conf.iter2, fc_int,"Puura iterations after oracle");
    myopt("--iter2grow", simp_conf.bve_grow_iter2, fc_int,"Puura BVE grow rate allowed after Oracle");
    myopt("--bvegrownonstop", simp_conf.bve_grow_nonstop, fc_int,"Do not stop BVE if nothing got eliminated, keep going until grow factor limit");
    myopt("--bveresolvmaxsz", simp_conf.bve_too_large_resolvent, fc_int,"Puura BVE max resolvent size in literals. -1 == no limit");
    myopt("--oraclesparsify", simp_conf.oracle_sparsify, fc_int,"Use Oracle to sparsify");
    myopt("--oraclevivif", simp_conf.oracle_vivify, fc_int,"Use oracle to vivify");
    myopt("--oraclevivifgetl", simp_conf.oracle_vivify_get_learnts, fc_int,"Use oracle to vivify get learnts");
    myopt("--distill", conf.distill, fc_int, "Distill clauses before minimization of indep");
    myopt("--weakenlim", simp_conf.weaken_limit, fc_int, "Limit to weaken BVE resolvents");
    myopt("--bce", etof_conf.do_bce, fc_int, "Use blocked clause elimination (BCE) statically");
    myopt("--red", redundant_cls, fc_int,"Also dump redundant clauses");

    // Debug
    myopt("--renumber", etof_conf.do_renumber, fc_int,"Renumber variables to start from 1...N in CNF.");
    myopt("--specifiedorder", conf.specified_order_fname, fc_string, "Try to remove variables from the independent set in this order. File must contain a variable on each line. Variables start at ZERO. Variable from the BOTTOM will be removed FIRST. This is for DEBUG ONLY");
    myopt("--minimize", do_minim_indep, fc_int,"Minimize indep set");
    myopt("--debugminim", debug_minim, fc_string,"Create this file that is the CNF after indep set minimization");
    myopt("--cmsmult", conf.cms_glob_mult, fc_double,"Multiply timeouts in CMS by this. Default is -1, which means no change. Useful for debugging");

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
    arj->set_bve_pre_simplify(conf.bve_pre_simplify);
    arj->set_cms_glob_mult(conf.cms_glob_mult);
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
    arj->set_seed(conf.seed);
    arj->set_gauss_jordan(conf.gauss_jordan);
    arj->set_simp(conf.simp);
    arj->set_extend_max_confl(conf.extend_max_confl);
    arj->set_oracle_find_bins(conf.oracle_find_bins);
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
    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_synthesis");

    if (do_synth_bve && !cnf.synth_done()) {
        cnf = arjun->standalone_get_simplified_cnf(cnf, simp_conf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-simplified_cnf.aig");
    }
    if (etof_conf.do_autarky && !cnf.synth_done()) {
        arjun->standalone_autarky(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-autarky.aig");
    }
    if (etof_conf.do_extend_indep && !cnf.synth_done()) {
        arjun->standalone_unsat_define(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-extend_synth.aig");
        cnf.simplify_aigs(conf.verb);
    }
    if (do_minim_indep && !cnf.synth_done()) {
        arjun->standalone_backward_round_synth(cnf, mconf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-minim_idep_synt.aig");
        cnf.simplify_aigs(conf.verb);
    }
    if (do_unate && !cnf.synth_done()) {
        arjun->standalone_unate(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-unsat_unate.aig");
    }
    if (do_unate_def && !cnf.synth_done()) {
        arjun->standalone_unate_def(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-unsat_unate_def.aig");
    }

    SynthRunner synth_runner(conf, arjun);
    auto strategies = synth_runner.parse_mstrategy(mstrategy);
    synth_runner.run_manthan_strategies(cnf, mconf, strategies);
    release_assert(cnf.synth_done() && "Synthesis should be done by now, but it is not!");
    if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-5-manthan.aig");
    if (!conf.debug_synth.empty()) {
        auto final_cnf = cnf;
        final_cnf.simplify_aigs();
        final_cnf.simplify_aigs();
        final_cnf.clear_orig_sampl_defs(); // final should not have orig sampl set defined
        final_cnf.write_aig_defs_to_file(conf.debug_synth + "-final.aig");
        cout << "c o [arjun] you can check correctness by running: " << endl;
        cout << "./test-synth -u -v 1 " << input_file << " " << conf.debug_synth + "-final.aig" << endl;
        if (conf.verb >= 3) final_cnf.write_aig_defs_to_file_txt(conf.debug_synth + "-final.txt");
    }
}

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

    if (simp_conf.appmc) {
        assert(!synthesis && "Cannot use synthesis and appmc simplification at the same time");
        cout << "c o [arjun] Setting defaults for AppMC CNF simplification" << endl;
        simp_conf.appmc = true;
        if (!program.is_used("--oraclevivif")) simp_conf.oracle_vivify = true;
        if (!program.is_used("--oraclesparsify")) simp_conf.oracle_sparsify = false;
        if (!program.is_used("--oraclevivifgetl")) simp_conf.oracle_vivify_get_learnts = 1;
        if (!program.is_used("--iter1")) simp_conf.iter1 = 2;
        if (!program.is_used("--iter2")) simp_conf.iter2 = 0;
    }

    if (program.is_used("--synth")) {
        assert(!simp_conf.appmc && "Cannot use synthesis and appmc simplification at the same time");
    }

    if (program.is_used("--synthmore")) {
        assert(!simp_conf.appmc && "Cannot use synthesis and appmc simplification at the same time");
        cout << "c o [arjun] Setting defaults for synthesis mode" << endl;
        if (!program.is_used("--bveresolvmaxsz")) simp_conf.bve_too_large_resolvent = 1000;
        /* if (!program.is_used("--iter1grow")) simp_conf.bve_grow_iter1 = 200; */
        if (!program.is_used("--iter2grow")) simp_conf.bve_grow_iter2 = 500;
        if (!program.is_used("--bvegrownonstop")) simp_conf.bve_grow_nonstop = true;
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
        do_synthesis();
    } else {
        do_minimize();
    }
    cout << "c o [arjun] All done. T: " << std::setprecision(2) << std::fixed
        << (cpuTime() - start_time) << endl;

    return 0;
}
