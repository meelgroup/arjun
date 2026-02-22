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
#define myflag(name, var, hhelp) \
    program.add_argument(name) \
        .action([&](const auto&) {var = 1;}) \
        .default_value(var) \
        .flag() \
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
ArjunNS::Arjun::ManthanConf mconf;
int do_gates = 1;
int redundant_cls = true;
int simptofile = true;
int sampl_start_at_zero = false;
int do_synth_bve = true;
int do_pre_backbone = 0;
int manthan_rep_mult = 4;
int manthan_strategy = 0;

int synthesis = false;
int do_unate = false;
int do_unate_def = false;
int do_revbce = false;
int do_minim_indep = true;
string debug_minim;
string candidate_defs_file;
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
    myopt("--seed", conf.seed, atoi, "Random seed");

    // synth main
    myflag("--synth", synthesis, "Run synthesis");
    myflag("--synthmore", synthesis, "Run synthesis, with more aggressive BVE options");
    myopt("--maxsat", mconf.do_maxsat_better_ctx, atoi, "Use maxsat to find better counterexamples during Manthan");
    myopt("--synthbve", do_synth_bve, atoi,"Perform BVE for synthesis");
    myopt("--extend", etof_conf.do_extend_indep, atoi,"Extend independent set just before CNF dumping");
    myopt("--minimconfl", mconf.do_minimize_conflict, atoi,"Minimize conflict size when repairing");
    myopt("--simpevery", mconf.simplify_every, atoi,"Simplify solvers inside Manthan every K loops");
    myopt("--unate", do_unate, atoi,"Perform unate analysis");
    myopt("--unatedef", do_unate_def, atoi,"Perform definition-aware unate analysis");
    myopt("--autarky", etof_conf.do_autarky, atoi,"Perform unate analysis");
    myopt("--mbve", mconf.manthan_bve, atoi,"Use BVE with constants instead of training");
    myopt("--monflyorder", mconf.manthan_on_the_fly_order, atoi,"Use on-the-fly training order and post-training topological order");
    myopt("--moneperloop", mconf.one_repair_per_loop, atoi,"One repair per CEX loop");

    // repairing on vars
    myopt("--bwequal", mconf.force_bw_equal, atoi,"Force BW vars' indicators to be TRUE -- prevents repairing with them, but faster to repair");
    myopt("--bvaxor", mconf.bva_xor_vars, atoi,"Add XOR over input vars as BVA vars, so we can repair with them");
    myopt("--silentupdate", mconf.silent_var_update, atoi,"Silently update variables while repairing");
    // Strategy
    myopt("--mtryrepmult", manthan_rep_mult, atoi,"Repair tries will be multiplied by this");
    myopt("--mstrategy", manthan_strategy, atoi,"Go directly to strategy N");
    // Order
    myopt("--morder", mconf.manthan_order, atoi,"Order vars: indicence (0), cluster-incidence (1), BVE (2)");
    myopt("--maxsatorder", mconf.maxsat_order, atoi,"Which order to use to try to fix vars? 0 = norm, 1 = rev");
    myopt("--mbackwsynthorder", mconf.backward_synth_order, atoi,"Which order to use to try to do backward? 0 = normal, 1 = reverse");
    // solver config
    myopt("--ctxsolver", mconf.ctx_solver_type, atoi,"Context solver type. 0 = CryptoMiniSat, 1 = CaDiCaL");
    myopt("--repairsolver", mconf.repair_solver_type, atoi,"Context solver type. 0 = CryptoMiniSat, 1 = CaDiCaL");
    myopt("--repaircache", mconf.repair_cache_size, atoi,"Repair cache size. 0 = no cache");
    // synth -- sampling
    myopt("--samples", mconf.num_samples, atoi,"Number of samples");
    myopt("--samplesccnr", mconf.num_samples_ccnr, atoi,"Number of samples from CCNR");
    myopt("--uniqsamp", mconf.do_unique_input_samples, atoi, "Unique samples on input vars");
    myopt("--filtersamples", mconf.do_filter_samples, atoi,"Filter samples from useless ones");
    myopt("--biasedsampling", mconf.do_biased_sampling, atoi,"Biased sampling");
    myopt("--fixedconf", mconf.sampler_fixed_conflicts, atoi,"Restart conflict limit in CMSGen");
    // synth -- decision tree
    myopt("--maxdepth", mconf.maximumDepth, atoi,"Maximum depth of decision tree");
    myopt("--minleaf", mconf.minimumLeafSize, atoi,"Minimum leaf size in decision tree");
    myopt("--mingainsplit", mconf.minGainSplit, atof,"Minimum gain for a split in decision tree");
    myopt("--learnuseall", mconf.do_use_all_variables_as_features, atoi,"Use all variables as features in decision tree learning. 0 = only inputs");
    // synth -- debug
    myopt("--manthancnf", mconf.write_manthan_cnf, string, "Write Manthan CNF to this file");
    myopt("--debugsynth", conf.debug_synth, string,"Debug synthesis, prefix with this fname");
    myopt("--candidatefuns", candidate_defs_file, string, "Load candidate functions from AIG-defs file");


    // Simplification options for minim
    myopt("--probe", conf.probe_based, atoi,"Do probing during orignal Arjun");
    myopt("--bvepresimp", conf.bve_pre_simplify, atoi,"simplify");
    myopt("--simp", conf.simp, atoi,"Do ~ sort of simplification during indep minimixation");
    myopt("--probe", conf.probe_based, atoi,"Use simple probing to set (and define) some variables");
    myopt("--intree", conf.intree, atoi,"intree");

    // Gate options
    myopt("--gates", do_gates, atoi,"Turn on/off all gate-based definability");
    myopt("--nogatebelow", conf.no_gates_below, atof,"Don't use gates below this incidence relative position (1.0-0.0) to minimize the independent set. Gates are not very accurate, but can save a LOT of time. We use them to get rid of most of the uppert part of the sampling set only. Default is 99% is free-for-all, the last 1% we test. At 1.0 we test everything, at 0.0 we try using gates for everything.");
    myopt("--orgate", conf.or_gate_based, atoi,"Use 3-long gate detection in SAT solver to define variables");
    myopt("--irreggate", conf.irreg_gate_based, atoi,"Use irregular gate-based removal of vars from indep set");
    myopt("--itegate", conf.ite_gate_based, atoi,"Use ITE gate detection in SAT solver to define some variables");
    myopt("--xorgate", conf.xor_gates_based, atoi,"Use XOR detection in SAT solver to define some variables");

    // AppMC
    program.add_argument("--appmc")
        .flag()
        .action([&](const auto&) {simp_conf.appmc = true;})
        .help("Set CNF simplification options for appmc");

    // Detailed Configuration
    myopt("--sbvaclcut", etof_conf.sbva_cls_cutoff, atoi,"SBVA heuristic cutoff. Higher -> only appied to more clauses");
    myopt("--sbvalitcut", etof_conf.sbva_lits_cutoff, atoi,"SBVA heuristic cutoff. Higher -> only appied to larger clauses");
    myopt("--findbins", conf.oracle_find_bins, atoi,"How aggressively find binaries via oracle");
    myopt("--sbvabreak",  etof_conf.sbva_tiebreak, atoi,"SBVA tie break: 1=sbva or 0=bva");
    myopt("--gaussj", conf.gauss_jordan, atoi,"Use XOR finding and Gauss-Jordan elimination");
    myopt("--bve", simp_conf.do_bve, atoi,"Perform BVE during CNF simplification");
    myopt("--iter1", simp_conf.iter1, atoi,"Puura iterations before oracle");
    myopt("--iter1grow", simp_conf.bve_grow_iter1, atoi,"Puura BVE grow rate allowed before Oracle");
    myopt("--iter2", simp_conf.iter2, atoi,"Puura iterations after oracle");
    myopt("--iter2grow", simp_conf.bve_grow_iter2, atoi,"Puura BVE grow rate allowed after Oracle");
    myopt("--bvegrownonstop", simp_conf.bve_grow_nonstop, atoi,"Do not stop BVE if nothing got eliminated, keep going until grow factor limit");
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

void import_candidate_functions(ArjunNS::SimplifiedCNF& cnf, const string& fname) {
    ArjunNS::SimplifiedCNF cand(fg);
    cand.read_aig_defs_from_file(fname);
    if (!cand.get_need_aig()) {
        cout << "ERROR: candidate file does not contain AIG data: " << fname << endl;
        exit(EXIT_FAILURE);
    }

    vector<ArjunNS::aig_ptr> aigs(cnf.nVars(), nullptr);
    std::map<uint32_t, uint32_t> orig_to_current_new;
    uint32_t imported = 0;
    uint32_t skipped_already_defined = 0;
    uint32_t skipped_missing = 0;
    const auto& orig_inputs = cnf.get_orig_sampl_vars();
    for (const auto& [orig_v, new_lit] : cnf.get_orig_to_new_var()) {
        orig_to_current_new[orig_v] = new_lit.var();
        if (orig_inputs.count(orig_v)) continue;
        if (cnf.defined(orig_v)) {
            skipped_already_defined++;
            continue;
        }
        if (orig_v >= cand.num_defs()) {
            skipped_missing++;
            continue;
        }
        const auto& cand_aig = cand.get_def(orig_v);
        if (cand_aig == nullptr) {
            skipped_missing++;
            continue;
        }
        aigs[new_lit.var()] = cand_aig;
        imported++;
    }

    cnf.map_aigs_to_orig(aigs, cnf.nVars(), &orig_to_current_new);
    cnf.simplify_aigs(conf.verb);
    cout << "c o [synth] imported candidate defs from '" << fname << "'"
         << " imported: " << imported
         << " skipped-already-defined: " << skipped_already_defined
         << " skipped-missing: " << skipped_missing << endl;
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
    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_synthesis");
    if (!candidate_defs_file.empty()) {
        cnf.set_preserve_existing_defs(true);
        import_candidate_functions(cnf, candidate_defs_file);
        cnf.get_var_types(conf.verb | verbose_debug_enabled, "after importing candidate functions");
    }
    const bool has_candidate_funs = !candidate_defs_file.empty();
    const bool candidate_all_specified = (has_candidate_funs && cnf.synth_done());
    if (candidate_all_specified) {
        cout << "c o [synth] all non-input functions provided by candidate file;"
             << " skipping synth preprocessing and starting from counterexample checks" << endl;
    }
    if (has_candidate_funs && do_synth_bve) {
        cout << "c o [synth] candidate functions supplied; skipping --synthbve preprocessing" << endl;
    }

    if (!has_candidate_funs && !candidate_all_specified && do_synth_bve && !cnf.synth_done()) {
        /* simp_conf.bve_too_large_resolvent = -1; */
        cnf = arjun->standalone_get_simplified_cnf(cnf, simp_conf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-simplified_cnf.aig");
    }

    if (!candidate_all_specified && etof_conf.do_autarky && !cnf.synth_done()) {
        arjun->standalone_autarky(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-autarky.aig");
    }

    if (!candidate_all_specified && etof_conf.do_extend_indep && !cnf.synth_done()) {
        arjun->standalone_unsat_define(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-extend_synth.aig");
        cnf.simplify_aigs(conf.verb);
    }

     if (!candidate_all_specified && do_minim_indep && !cnf.synth_done()) {
        arjun->standalone_backward_round_synth(cnf, mconf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-minim_idep_synt.aig");
        cnf.simplify_aigs(conf.verb);
    }

    if (!candidate_all_specified && do_unate && !cnf.synth_done()) {
        arjun->standalone_unate(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-unsat_unate.aig");
    }

    if (!candidate_all_specified && do_unate_def && !cnf.synth_done()) {
        arjun->standalone_unate_def(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-unsat_unate_def.aig");
    }

    auto mconf_orig = mconf;
    int effective_strategy = manthan_strategy;
    if (has_candidate_funs && effective_strategy == 4) {
        cout << "c o [synth] candidate functions supplied; ignoring --mstrategy 4 (BVE-only), using strategy 2" << endl;
        effective_strategy = 2;
    }
    uint32_t tries;
    if (effective_strategy > 4) {
        cout << "ERROR: unknown strategy " << effective_strategy << endl;
        exit(EXIT_FAILURE);
    }
    const bool all_defined_before_manthan = cnf.synth_done();
    if (all_defined_before_manthan) {
        mconf = mconf_orig;
        if (!candidate_all_specified) {
            cout << "c o [synth] all non-input functions are already defined;"
                 << " running final counterexample check before returning" << endl;
        }
        mconf.start_from_candidate_cex = 1;
        mconf.manthan_bve = 0;
        if (mconf.manthan_order == 2) mconf.manthan_order = 0;
        tries = std::numeric_limits<uint32_t>::max();
        cnf = arjun->standalone_manthan(cnf, mconf, tries);
    } else if (!cnf.synth_done() && (effective_strategy == 0 || effective_strategy == 1)) {
        mconf = mconf_orig;
        // Learning with no samples
        mconf.manthan_bve = 0;
        if (has_candidate_funs && mconf.manthan_order == 2) mconf.manthan_order = 0;
        mconf.num_samples = 1;
        mconf.num_samples_ccnr = 0;
        mconf.manthan_bve = 0;
        tries = 20*manthan_rep_mult;
        if (effective_strategy == 1) tries = std::numeric_limits<uint32_t>::max();
        cnf = arjun->standalone_manthan(cnf, mconf, tries);
        if (cnf.synth_done()) verb_print(1, "Manthan finished with strategy 1");
    }
    if (!candidate_all_specified && !cnf.synth_done() && (effective_strategy == 0 || effective_strategy == 2)) {
        // Learning with (larger) samples size
        mconf = mconf_orig;
        mconf.manthan_bve = 0;
        if (has_candidate_funs && mconf.manthan_order == 2) mconf.manthan_order = 0;
        tries = 100*manthan_rep_mult;
        if (effective_strategy == 2) tries = std::numeric_limits<uint32_t>::max();
        cnf = arjun->standalone_manthan(cnf, mconf, tries);
        if (cnf.synth_done()) verb_print(1, "Manthan finished with strategy 2");
    }
    if (!cnf.synth_done() && (effective_strategy == 0 || effective_strategy == 3)) {
        // Learning, no BW, only input var learning, no silent update
        mconf = mconf_orig;
        mconf.manthan_bve = 0;
        mconf.force_bw_equal = 1;
        mconf.silent_var_update = 0;
        mconf.do_use_all_variables_as_features = 0;
        tries = 100*manthan_rep_mult;
        if (effective_strategy == 3) tries = std::numeric_limits<uint32_t>::max();
        cnf = arjun->standalone_manthan(cnf, mconf, tries);
        if (cnf.synth_done()) verb_print(1, "Manthan finished with strategy 3");
    }
    if (!has_candidate_funs && !cnf.synth_done() && (effective_strategy == 0 || effective_strategy == 4)) {
        // BVE strategy
        mconf = mconf_orig;
        mconf.manthan_bve = 1;
        tries = std::numeric_limits<uint32_t>::max();
        cnf = arjun->standalone_manthan(cnf, mconf, tries);
        if (cnf.synth_done()) verb_print(1, "Manthan finished with strategy 4");
    }
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
