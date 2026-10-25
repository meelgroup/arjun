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

#include "constants.h"
#include <memory>
#if defined(__GNUC__) && defined(__linux__)
#include <cfenv>
#endif

#include <charconv>
#include <type_traits>
#include <iostream>
#include <iomanip>
#include <vector>
#include <string>
#include <filesystem>
#include "argparse.hpp"

#include "time_mem.h"
#include "arjun.h"
#include <cryptominisat5/cryptominisat.h>
#include "config.h"
#include "file_read_helper.h"
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
string output_file;

ArjunNS::SimpConf simp_conf;
ArjunNS::Arjun::ElimToFileConf etof_conf;
ArjunNS::Arjun::CegrConf mconf;
ArjunNS::Arjun::InterpConf iconf;
int do_gates = 1;
int redundant_cls = true;
int simptofile = true;
int do_puura = true;
int do_pre_backbone = 0;
string mstrategy = "const(max_repairs=400),const(max_repairs=400,inv_guess=1),rnd(max_repairs=400),cover(ticks=5000),bve";

int synthesis = false;
int qbf2 = false;
size_t qbf2_num_cls = 0;
int debug_verilog = 0;
ArjunNS::Arjun::CoverConf cover_conf;
double cover_ticks = 200;
double cover_late_ticks = 100;
double cover_orig_ticks = 2000;
bool cover_done = false;
int use_brute_force_synth = 1;
int do_unate_def = true;
int do_backward = true;
string debug_minim;
int mode = 0;
unique_ptr<FieldGen> fg = nullptr;
int mpfr_precision = 128;

string print_version() {
    std::stringstream ss;
    ss << "c o Arjun SHA1: " << arjun->get_version_sha1() << endl;
    ss << "c o SBVA SHA1: " << arjun->get_sbva_version_sha1() << endl;
    ss << "c o CMS SHA1: " << arjun->get_solver_version_sha1() << endl;
#ifndef OLD_CMS
    ss << "c o CaDiCaL SHA1: " << CMSat::SATSolver::get_cadical_version_sha1() << endl;
    ss << "c o CadiBack SHA1: " << CMSat::SATSolver::get_cadiback_version_sha1() << endl;
#endif
    ss << arjun->get_thanks_info("c o ") << endl;
    ss << arjun->get_solver_thanks_info("c o ") << endl;
    ss << "c o [arjun] Compilation environment: " << arjun->get_compilation_env();
    return ss.str();
}

template<class T> static T parse_opt(const std::string& s) {
    if constexpr (std::is_same_v<T, std::string>) {
        return s;
    } else if constexpr (std::is_same_v<T, bool>) {
        return parse_opt<int>(s) != 0;
    } else if constexpr (std::is_floating_point_v<T>) {
        size_t pos = 0;
        double val;
        try { val = std::stod(s, &pos); }
        catch (const std::exception&) { throw std::invalid_argument("not a number: " + s); }
        if (pos != s.size()) throw std::invalid_argument("trailing characters in number: " + s);
        return val;
    } else if constexpr (std::is_integral_v<T>) {
        T val{};
        auto [ptr, ec] = std::from_chars(s.data(), s.data() + s.size(), val);
        if (ec == std::errc::result_out_of_range) throw std::invalid_argument("integer out of range: " + s);
        if (ec != std::errc{}) throw std::invalid_argument("not an integer: " + s);
        if (ptr != s.data() + s.size()) throw std::invalid_argument("trailing characters in integer: " + s);
        return val;
    } else {
        static_assert(sizeof(T) == 0, "parse_opt: unsupported option type");
    }
}

template<typename T>
void myopt(const char* name, T& var, const char* hhelp) {
    program.add_argument(name)
        .action([&var](const std::string& a) { var = parse_opt<T>(a); })
        .default_value(var)
        .help(hhelp);
}
template<typename T>
void myopt2(const char* name1, const char* name2, T& var, const char* hhelp) {
    program.add_argument(name1, name2)
        .action([&var](const std::string& a) { var = parse_opt<T>(a); })
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
    myopt2("-v", "--verb", conf.verb, "Verbosity");
    program.add_argument("--version") \
        .action([&](const auto&) {cout << print_version() << endl; exit(0);}) \
        .flag()
        .help("Print version and exit");

    myopt("--mode", mode , "0=counting, 1=weightd counting");
    myopt("--allindep", etof_conf.all_indep,
          "All variables can be made part of the indepedent support. Indep "
          "support is given ONLY to help the solver.");
    myopt("--maxc", conf.backw_max_confl,"Maximum conflicts per variable in backward mode");
    myopt("--sbva", etof_conf.num_sbva_steps,"SBVA timeout in K steps. 0 = no sbva");
    myopt("--prebackbone", do_pre_backbone,"Perform backbone before other things");
    myopt("--seed", conf.seed, "Random seed");
    myopt("--mpfrprec", mpfr_precision, "MPFR precision in bits");

    // synth main
    myflag("--synth", synthesis, "Run synthesis");
    myflag("--2qbf", qbf2, "Solve the 2QBF: forall the 'a' (or 'c p show') vars, exists the rest. Exits with 10 (true) or 20 (false). If an output file is given, the Skolem functions are written to it");
    myopt("--cover", cover_conf.budget, "Before synthesis, try to cover all inputs with a few models of the CNF. Its budget: a refinement that names fraction f of the helper variables costs f^2. 0 = off");
    myopt("--coverlateticks", cover_late_ticks, "As --coverticks, for the covering run after the definition passes");
    myopt("--coverorigticks", cover_orig_ticks, "As --coverticks, for the covering run of --2qbf on the original clauses");
    myopt("--coverminim", cover_conf.minim, "How covering shortens a refinement, a sum: 1 = SAT calls for a model of the same input whose existentials satisfy more clauses, 2 = flipping existentials no clause needs, 4 = dropping what another part of it implies");
    myopt("--coverticks", cover_ticks, "A covering run gives up after this many million ticks of SAT solver work. 0 = no limit. The 1st runs are short, the long one is cover(ticks=N) of --cstrategy");
    myopt("--maxsat", mconf.maxsat_better_ctx, "Use maxsat to find better counterexamples during Cegr");
    myopt("--synthpuura", do_puura,"Run Puura, the CNF simplification, for synthesis and 2QBF");
    myopt("--extend", etof_conf.do_extend_indep,"Extend independent set just before CNF dumping");
    myopt("--minimconfl", mconf.minimize_conflict,"Minimize conflict size when repairing");
    myopt("--unatedef", do_unate_def,"Perform definition-aware unate analysis");
    myopt("--unatedefmaxconfl", conf.unate_def_max_confl,"Conflict budget per SAT call in the standard unate_def probe");
    myopt("--unatedefeq", conf.unate_def_eq,"In unate_def, also detect equiv defs of the form t = L or t = ~L for some literal L");
    myopt("--unatedefeqmax", conf.unate_def_eq_max_per_var,"Max equiv candidates to test per to-define variable in unate_def");
    myopt("--unatedefeqconfl", conf.unate_def_eq_max_confl,"Conflict budget per SAT call inside the equiv unate_def search");
    myopt("--unatedefmaxconfltot", conf.unate_def_max_confl_total,"Conflict budget for the WHOLE unate_def pass, not per call. 0 = no limit");
    myopt("--unatedefeqdry", conf.unate_def_eq_dry_streak,
          "Disable equiv unate_def probe after this many consecutive misses "
          "with zero hits so far (very low = bail aggressively, very high = effectively never disable)");
    myopt("--unatedefeqnoninp", conf.unate_def_eq_noninput,
          "Allow non-input vars (to-define + already-tested) as the candidate "
          "L in t = L. Inputs are still tried first; non-inputs only after the "
          "input list is exhausted. 0 = inputs only");
    myopt("--autarky", etof_conf.do_autarky,"Perform autarky analysis");
    myopt("--coverdrop", etof_conf.cover_drop_mticks, "After Puura, remove the clauses of non-sampling vars that every allowed sampling assignment can satisfy, checked by model covering (2QBF). Its budget in millions of SAT solver ticks, 0 = off");
    myopt("--coverdropcubes", etof_conf.cover_drop_max_cubes, "With --coverdrop, also replace the clauses by at most this many clauses over the sampling vars that rule out the assignments with no model of them. 0 = only remove");
    myopt("--coverdropw", etof_conf.cover_drop_weighted_as_x, "With --coverdrop, take the weighted defined vars as sampling ones, so that the parts with them can also be removed or replaced");
    // CNF rewrite via AIG lifting

    // repairing on vars
    myopt("--bwequal", mconf.force_bw_equal,"Force BW vars' indicators to be TRUE -- prevents repairing with them, but faster to repair");
    // Strategy
    myopt("--cstrategy", mstrategy,
        "Comma-separated synthesis strategy list, e.g. "
        "\"learn(samples=1,max_repairs=100),learn(max_repairs=800),bve\". "
        "Each non-last strategy runs for 20*max_repairs tries; the last runs unlimited. "
        "cover(ticks=N) is a covering run of N million ticks, never the last. "
        "Params: max_repairs, samples, seed, min_gain_split, "
        "max_depth, sampler_fixed_conflicts, and other CegrConf fields.");

    // Restarting
    myopt("--crestart", mconf.restart,
        "Exit Cegr every N repairs, compact ALL per-var AIGs via the AIG rewriter, "
        "and re-enter Cegr with the compacted AIGs as the initial guess. 0 = never");
    myopt("--dumprestartaig", conf.dump_restart_aig,
        "Dump the pre-compaction guess AIGs at every Cegr restart to "
        "<prefix>-restart<N>.aig (binary defs) and .v (verilog), for offline "
        "rewrite experiments");

    // solver config
    myopt("--ctxsolver", mconf.ctx_solver_type,"Context solver type. 0 = CryptoMiniSat, 1 = CaDiCaL");
    myopt("--ctxlightinproc", mconf.ctx_light_inproc,
        "Cegr context solver CaDiCaL inprocessing: 0 = stock, 1 = no lucky phases under "
        "assumptions, 2 = also no inprobing/congruence/sweep/factor");
    myopt("--repairsolver", mconf.repair_solver_type,"Repair solver type. 0 = CryptoMiniSat, 1 = CaDiCaL");
    myopt("--repaircache", mconf.repair_cache_size,"Repair cache size. 0 = no cache");

    // Cegr learn synth -- sampling
    myopt("--samples", mconf.samples,"Number of samples");
    myopt("--uniqsamp", mconf.do_unique_input_samples, "Unique samples on input vars");
    myopt("--filtersamples", mconf.filter_samples,"Filter samples from useless ones");
    myopt("--fixedconf", mconf.sampler_fixed_conflicts,"Restart conflict limit in CMSGen");

    // synth -- decision tree
    myopt("--maxdepth", mconf.max_depth,"Maximum depth of decision tree");
    myopt("--minleaf", mconf.min_leaf_size,"Minimum leaf size in decision tree");
    myopt("--mingainsplit", mconf.min_gain_split,"Minimum gain for a split in decision tree");
    // synth -- cutoff/tuning constants
    myopt("--coneperloop", mconf.one_repair_per_loop,"One repair per CEX loop");
    myopt("--cinvertguessed", mconf.inv_guess,"Invert guessed functions");
    myopt("--statsevery", mconf.stats_every, "Print stats every N repair loops");
    myopt("--detailedstatsevery", mconf.detailed_stats_every, "Print detailed stats every N repair loops");
    myopt("--confldropy", mconf.conflict_drop_y_max, "Max conflict size to try dropping y-vars");
    myopt("--batchminimmin", mconf.batch_minim_min, "Min conflict size for batch minimization");
    myopt("--minimbudgetthresh", mconf.minim_budget_threshold, "Conflict size above which minim budget is capped");
    myopt("--minimbudgetmax", mconf.minim_budget_max, "Max minimization solver calls");
    myopt("--minimbudgetmult", mconf.minim_budget_mult, "Minim budget = conflict.size * mult (up to max)");
    myopt("--czhighratio", mconf.cz_high_ratio, "cost_zero > tot_repaired * this triggers tightest cz_threshold");
    myopt("--czlowratio", mconf.cz_low_ratio, "cost_zero > tot_repaired * this triggers medium cz_threshold");
    myopt("--czthreshhigh", mconf.cz_threshold_high, "Consecutive cost-zero break count when high cz ratio");
    myopt("--czthreshmid", mconf.cz_threshold_mid, "Consecutive cost-zero break count when medium cz ratio");
    myopt("--czthreshlow", mconf.cz_threshold_low, "Consecutive cost-zero break count when low cz ratio");
    // synth -- debug
    myopt("--cegrcnf", mconf.write_cegr_cnf, "Write Cegr CNF to this file");
    myopt("--debugsynth", conf.debug_synth,"Debug synthesis or 2QBF (with an output file): write each stage's functions to files with this prefix");
    myopt("--debugverilog", debug_verilog, "With --debugsynth: write the final functions as Verilog (-final.v) instead of -final.aig");
    myopt("--interprebuildevery", iconf.interp_rebuild_every,
          "Rebuild the doubled-CNF interpolation solver every N interpolants "
          "(bounds tracer maps; smaller = exercise the rebuild path more).");
    myopt("--interpmaxconfl", iconf.interp_max_confl,
          "Per-interpolant conflict budget; over this, skip the var. 0 = unlimited.");
    myopt("--interprebuildmaxconfl", iconf.interp_rebuild_max_confl,
          "Rebuild the interpolation solver once it burns this many conflicts "
          "since the last rebuild (bounds tracer maps after "
          "skipped/conflict-heavy solves). 0 = off.");
    myflag("--checkrepair", mconf.check_repair,
           "Check that error formula count decreases monotonically after each repair iteration (uses ganak)");
    myopt("--ganakbin", mconf.ganak_binary, "Path to ganak binary (for --checkrepair)");

    // Brute-force synthesis
    myopt("--bruteforcesynth", use_brute_force_synth,
          "Try brute-force synthesis for the final synthesis "
          "step before Cegr. Viable when |orig_sampl_cnf| ≤ "
          "--bruteforcesynththresh (after the minim pre-pass); above that it "
          "declines and Cegr takes over. 0=Cegr only, 1=try brute-force "
          "first (default).");
    myopt("--bruteforcesynththresh", mconf.brute_force_synth_threshold,
          "Cap: brute_force_synth runs only when |orig_sampl_cnf| ≤ this "
          "(after the minim pre-pass); above it it declines to Cegr. Each y "
          "allocates 2^N truth-table entries, so raising past ~20 OOMs.");
    myopt("--bruteforcesynthminim", mconf.brute_force_synth_minim,
          "Dry-run backward minim on orig_sampl_cnf before enumeration: prunes "
          "sampling vars that the post-preproc CNF defines from the rest, "
          "shrinking the 2^N truth tables. 0=off, 1=on (default).");
    myopt("--bruteforcesynthminimmax", mconf.brute_force_synth_minim_max,
        "Only attempt the minim pre-pass when |orig_sampl_cnf| ≤ this (default "
        "40). Above it the doubled-CNF minim is too expensive and unlikely to "
        "shrink below --bruteforcesynththresh, so it is skipped.");

    // Simplification options for minim
    myopt("--probe", conf.probe_based,"Use simple probing to set (and define) some variables");
    myopt("--bvepresimp", conf.bve_pre_simplify,"simplify");
    myopt("--simp", conf.simp,"Do ~ sort of simplification during indep minimixation");
    myopt("--intree", conf.intree,"intree");

    // Gate options
    myopt("--gates", do_gates,"Turn on/off all gate-based definability");
    myopt("--nogatebelow", conf.no_gates_below,
          "Don't use gates below this incidence relative position (1.0-0.0) to "
          "minimize the independent set. Gates are not very accurate, but can "
          "save a LOT of time. We use them to get rid of most of the uppert "
          "part of the sampling set only. Default is 99% is free-for-all, the "
          "last 1% we test. At 1.0 we test everything, at 0.0 we try using "
          "gates for everything.");
    myopt("--orgate", conf.or_gate_based,"Use 3-long gate detection in SAT solver to-define variables");
    myopt("--irreggate", conf.irreg_gate_based,"Use irregular gate-based removal of vars from indep set");
    myopt("--itegate", conf.ite_gate_based,"Use ITE gate detection in SAT solver to-define some variables");
    myopt("--xorgate", conf.xor_gates_based,"Use XOR detection in SAT solver to-define some variables");

    // AppMC
    program.add_argument("--appmc")
        .flag()
        .action([&](const auto&) {simp_conf.appmc = true;})
        .help("Set CNF simplification options for appmc");

    // Detailed Configuration
    myopt("--sbvaclcut", etof_conf.sbva_cls_cutoff,"SBVA heuristic cutoff. Higher -> only appied to more clauses");
    myopt("--sbvalitcut", etof_conf.sbva_lits_cutoff,"SBVA heuristic cutoff. Higher -> only appied to larger clauses");
    myopt("--findbins", conf.oracle_find_bins,"How aggressively find binaries via oracle");
    myopt("--sbvabreak",  etof_conf.sbva_tiebreak,"SBVA tie break: 1=sbva or 0=bva");
    myopt("--sbvamaxnewvars", etof_conf.sbva_max_new_vars,"Max number of new variables SBVA may add. 0 = no limit");
    myopt("--gaussj", conf.gauss_jordan,"Use XOR finding and Gauss-Jordan elimination");
    myopt("--bve", simp_conf.do_bve,"Perform BVE during CNF simplification");
    myopt("--iter1", simp_conf.iter1,"Puura iterations before oracle");
    myopt("--iter1grow", simp_conf.bve_grow_iter1,"Puura BVE grow rate allowed before Oracle");
    myopt("--iter2", simp_conf.iter2,"Puura iterations after oracle");
    myopt("--iter2grow", simp_conf.bve_grow_iter2,"Puura BVE grow rate allowed after Oracle");
    myopt("--iter2growlarge", simp_conf.bve_grow_iter2_large,"If >= 0: used instead of --iter2grow when more than --iter2growlargevars vars are left before iter2");
    myopt("--iter2growlargevars", simp_conf.bve_grow_iter2_large_vars,"Vars-left threshold for --iter2growlarge");
    myopt("--bveresolvmaxsz", simp_conf.bve_too_large_resolvent,"Puura BVE max resolvent size in literals. -1 == no limit");
    myopt("--bveresolvmaxsz2", simp_conf.bve_too_large_resolvent2,"Like --bveresolvmaxsz, for the 2nd pass");
    myopt("--oraclemult", simp_conf.oracle_mult,"Oracle multiplier for timeout (i.e. steps-out)");
    myopt("--oraclesparsify", simp_conf.oracle_sparsify,"Use Oracle to sparsify");
    myopt("--oraclevivif", simp_conf.oracle_vivify,"Use oracle to vivify");
    myopt("--oraclevivifgetl", simp_conf.oracle_vivify_get_learnts,"Use oracle to vivify get learnts");
    myopt("--oracleextra", simp_conf.oracle_extra,"Run an extra oracle-vivif-fast + oracle-sparsify-fast + occ-bve pass at the end of Puura's strategy");
    myopt("--distill", conf.distill, "Distill clauses before minimization of indep");
    myopt("--weakenlim", simp_conf.weaken_limit, "Limit to weaken BVE resolvents");
    myopt("--xorgatemaxsize", simp_conf.xor_gate_find_maxsize, "Max clause size for XOR-gate finding");
    myopt("--bveocclim", simp_conf.bve_occ_cutoff, "BVE: refuse a var whose more frequent polarity occurs more than this often (CaDiCaL's elimocclim). 0 = no such limit");
    myopt("--bveprodlim", simp_conf.bve_occ_prod_cutoff, "BVE: refuse a var whose pos*neg occurrence product is over this. This is the bound on resolution work");
    myopt("--bveclsmaxsz", simp_conf.bve_cls_max_size, "BVE: refuse a var that occurs in a clause longer than this. 0 = no limit");
    myopt("--bveschedtouched", simp_conf.bve_sched_only_touched, "BVE: only schedule vars whose clauses changed since BVE last looked. 0 = schedule every eligible var");
    myopt("--bvetieminocc", simp_conf.bve_tie_min_occ, "BVE: among equal-size clauses, take first the one whose rarest var occurs the least. 0 = order them by clause ID");
    myopt("--ccnrbudget", simp_conf.backbone_ccnr_mems_limitM, "Mems budget, in millions, for each CCNR local search try that pre-filters backbone candidates. If no model is found, cadiback must test every variable");
    myopt("--puuradistill", simp_conf.puura_distill, "Distillation inside Puura's simplification strategy. 1 = as scheduled, 0 = drop every distill token, 2 = drop only the ones that run before the first occ-bve");
    myopt("--distillremlevel", simp_conf.distill_rem_level, "Clause removal during Puura's distillation. 0 = never, 1 = only on a real conflict, 2 = also when a literal is positively implied. Levels below 2 keep gate clauses that BVE needs to recover definitions");
    myopt("--red", redundant_cls,"Also dump redundant clauses");

    // Debug
    myopt("--renumber", etof_conf.do_renumber,"Renumber variables to start from 1...N in CNF.");
    myopt("--specifiedorder", conf.specified_order_fname, "Try to remove variables from the independent set in this order. File must contain a variable on each line. Variables start at ZERO. Variable from the BOTTOM will be removed FIRST. This is for DEBUG ONLY");
    myopt("--backward", do_backward,"Run the backward pass to minimize the independent set");
    myopt("--debugminim", debug_minim,"Create this file that is the CNF after indep set minimization");
    myopt("--cmsmult", conf.cms_glob_mult,"Multiply timeouts in CMS by this. Default is -1, which means no change. Useful for debugging");
    myopt("--cmsabsbudget", conf.cms_abs_budget, "CMS: absolute intree/distill budgets instead of search-relative ones");
    myopt("--cmssweep", conf.cms_sweep, "CMS: SAT sweeping (occ-sweep)");

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
    arj->set_dump_restart_aig(conf.dump_restart_aig);
    arj->set_intree(conf.intree);
    arj->set_bve_pre_simplify(conf.bve_pre_simplify);
    arj->set_cms_glob_mult(conf.cms_glob_mult);
    arj->set_cms_abs_budget(conf.cms_abs_budget);
    arj->set_cms_sweep(conf.cms_sweep);
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
    arj->set_unate_def_max_confl(conf.unate_def_max_confl);
    arj->set_unate_def_max_confl_total(conf.unate_def_max_confl_total);
    arj->set_unate_def_eq(conf.unate_def_eq);
    arj->set_unate_def_eq_max_per_var(conf.unate_def_eq_max_per_var);
    arj->set_unate_def_eq_max_confl(conf.unate_def_eq_max_confl);
    arj->set_unate_def_eq_dry_streak(conf.unate_def_eq_dry_streak);
    arj->set_unate_def_eq_noninput(conf.unate_def_eq_noninput);
    arj->set_oracle_find_bins(conf.oracle_find_bins);
}

[[noreturn]] void qbf2_result(const ArjunNS::SimplifiedCNF& cnf, const bool is_true,
        const vector<CMSat::lbool>& cex = {}) {
    cout << "c o [arjun] All done. T: " << std::setprecision(2) << std::fixed
        << (cpuTime() - start_time) << endl;
    cout << "s cnf " << is_true << " " << cnf.get_orig_num_vars() << " " << qbf2_num_cls << endl;
    if (!is_true) {
        vector<CMSat::lbool> full(cnf.get_orig_num_vars(), CMSat::l_False);
        for (uint32_t v = 0; v < cex.size() && v < full.size(); v++) if (cex[v] == CMSat::l_True) full[v] = CMSat::l_True;
        SLOW_DEBUG_DO(assert(cnf.is_2qbf_cex(full)));
        for(const auto& v: cnf.get_orig_sampl_vars())
            cout << "V " << (full[v] == CMSat::l_True ? "" : "-") << v+1 << " 0" << endl;
    }
    exit(is_true ? 10 : 20);
}

void check_2qbf_prefix(const ArjunNS::SimplifiedCNF& cnf) {
    if (cnf.get_bad_quant_block()) {
        cout << "ERROR: --2qbf needs a forall-exists quantifier prefix, but block "
            << cnf.get_bad_quant_block() << " of the file is an 'a' block after an 'e' one" << endl;
        exit(EXIT_FAILURE);
    }
    if (cnf.get_num_quant_blocks() == 0) return;
    for(const auto& cl: cnf.get_clauses()) for(const auto& l: cl) if (!cnf.get_quant_vars().count(l.var())) {
        cout << "ERROR: variable " << l.var()+1 << " is free, i.e. existential "
            "BEFORE the universals, so this is not a forall-exists 2QBF" << endl;
        exit(EXIT_FAILURE);
    }
}

// the orig lit of each var of the CNF
vector<CMSat::Lit> new_to_orig(const ArjunNS::SimplifiedCNF& cnf) {
    vector<CMSat::Lit> ret(cnf.nVars(), CMSat::lit_Undef);
    for (const auto& [n, o] : cnf.get_new_to_orig_var()) ret[n] = o;
    return ret;
}

void check_2qbf_univ_clause(const ArjunNS::SimplifiedCNF& cnf) {
    const auto to_orig = new_to_orig(cnf);
    for(const auto& cl: cnf.get_clauses()) {
        vector<CMSat::lbool> cex(cnf.num_defs(), CMSat::l_Undef);
        bool all_univ = true;
        for(const auto& l: cl) {
            const CMSat::Lit o = to_orig[l.var()] ^ l.sign();
            all_univ &= cnf.get_orig_sampl_vars().count(o.var());
            cex[o.var()] = CMSat::boolToLBool(o.sign());
        }
        if (!all_univ) continue;
        qbf2_result(cnf, false, cex);
    }
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
        if (qbf2) qbf2_result(cnf, false);
        cout << "c o [arjun] Input CNF is UNSAT!" << endl;
        exit(EXIT_FAILURE);
    }
}

bool has_univ(const ArjunNS::SimplifiedCNF& cnf) {
    const auto to_orig = new_to_orig(cnf);
    for(const auto& cl: cnf.get_clauses()) for(const auto& l: cl)
        if (cnf.get_orig_sampl_vars().count(to_orig[l.var()].var())) return true;
    return false;
}

bool has_defined(const ArjunNS::SimplifiedCNF& cnf) {
    const auto to_orig = new_to_orig(cnf);
    for(const auto& cl: cnf.get_clauses()) for(const auto& l: cl) {
        const uint32_t o = to_orig[l.var()].var();
        if (!cnf.get_orig_sampl_vars().count(o) && cnf.defined(o)) return true;
    }
    return false;
}

// SLOW_DEBUG: SAT-check defs after each stage; names the offending pass.
void check_stage(ArjunNS::SimplifiedCNF& cnf, const std::string& stage) {
    int bad = cnf.check_synth_funs_sat();
    if (bad >= 0) {
        cout << "c o [check_stage] WRONG def after stage '" << stage
             << "' for var " << (bad+1) << endl;
        assert(false && "wrong synth def after stage");
    }
}

void try_cover(ArjunNS::SimplifiedCNF& cnf, const bool need_funs, const double budget, const double ticks) {
    vector<CMSat::lbool> cex;
    auto my_conf = cover_conf;
    my_conf.partial = true;
    my_conf.budget = budget;
    my_conf.max_ticks = ticks * 1e6;
    my_conf.stop_at_cex = qbf2;
    my_conf.need_funs = need_funs;
    const auto ret = arjun->standalone_cover(cnf, my_conf, cex);
    if (ret != CMSat::l_Undef) verb_print(1, "[arjun] solved by covering");
    SLOW_DEBUG_DO(if (need_funs && ret != CMSat::l_False) check_stage(cnf, "cover"));
    // the functions are in place, and get written out by do_synth_2qbf()
    cover_done = ret == CMSat::l_True;
    if (ret == CMSat::l_False || (cover_done && !need_funs)) qbf2_result(cnf, cover_done, cex);
}

void simplify_for_synth_2qbf(ArjunNS::SimplifiedCNF& cnf, const bool need_funs) {
    cnf = arjun->standalone_get_simplified_cnf(cnf, simp_conf);
    verb_print(1, "[2qbf-puura] cls: " << cnf.get_clauses().size() << " T: " << (cpuTime() - start_time));
    if (qbf2) {
        const auto cex = cnf.get_2qbf_def_cex();
        if (!cex.empty()) {
            verb_print(1, "[arjun] simplification defined a universal: false");
            qbf2_result(cnf, false, cex);
        }
        check_2qbf_univ_clause(cnf);
    }
    if (!need_funs && !has_univ(cnf)) {
        verb_print(1, "[arjun] no universal left, and the CNF is satisfiable");
        qbf2_result(cnf, true);
    }
    if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-simplified_cnf.aig");
    SLOW_DEBUG_DO(check_stage(cnf, "simplified_cnf"));
}

void check_synth_2qbf_input(const ArjunNS::SimplifiedCNF& cnf) {
    if (cnf.get_num_no_touch()) {
        cout << "ERROR: synthesis with 'c p no-touch' is not supported" << endl;
        exit(EXIT_FAILURE);
    }
    if (qbf2) {
        check_2qbf_prefix(cnf);
        if (cnf.get_weighted() || !cnf.get_multiplier_weight()->is_one()) {
            cout << "ERROR: --2qbf does not take weights or a multiplier" << endl;
            exit(EXIT_FAILURE);
        }
    } else if (etof_conf.all_indep) {
        // No projection (or it covers all vars) => no defined vars to synth.
        cout << "ERROR: no defined vars to synthesize "
                "(no projection set, or projection covers all vars)" << endl;
        exit(EXIT_FAILURE);
    }
}

void do_synth_2qbf() {
    SynthRunner synth_runner(conf, arjun);
    const auto strategies = synth_runner.parse_mstrategy(mstrategy);
    if (etof_conf.all_indep) {
        cout << "ERROR: synthesis with --allindep makes no sense" << endl;
        exit(EXIT_FAILURE);
    }
    ArjunNS::SimplifiedCNF cnf(fg);
    cnf.set_need_aig();
    read_in_a_file(input_file, &cnf, etof_conf.all_indep, fg);
    check_synth_2qbf_input(cnf);
    if (qbf2 && !cnf.get_sampl_vars_set()) {
      // neither 'a' nor 'c p show': no universals, a plain SAT problem
      cnf.set_sampl_vars(vector<uint32_t>(), true);
    }
    cnf.clean_idiotic_mccomp_weights();
    cnf.check_cnf_sampl_sanity();
    cnf.check_cnf_vars();
    cnf.set_orig_clauses(cnf.get_clauses());
    cnf.set_orig_sampl_vars(cnf.get_sampl_vars());
    qbf2_num_cls = cnf.get_clauses().size();
    SLOW_DEBUG_DO(assert(cnf.get_need_aig() && cnf.defs_invariant()));
    check_cnf_sat(cnf);
    if (qbf2) {
        if (cnf.get_sampl_vars().empty()) qbf2_result(cnf, true);
        check_2qbf_univ_clause(cnf);
    }
    const bool need_funs = !qbf2 || !output_file.empty();
    if (!need_funs && !conf.debug_synth.empty()) {
        cout << "ERROR: --debugsynth needs the functions to be kept: give an output file for them" << endl;
        exit(EXIT_FAILURE);
    }
    if (conf.verb) cnf.get_var_types(conf.verb, "start do_synthesis");

    // Only 2QBF: an X with no Y ends it early here, synthesis has no such early exit to win
    if (qbf2 && !cnf.all_ys_defined())
        try_cover(cnf, need_funs, std::min(cover_conf.budget, 50.0), cover_orig_ticks);

    if (do_puura && !cnf.all_ys_defined())
        simplify_for_synth_2qbf(cnf, need_funs);

    if (!cnf.all_ys_defined())
        try_cover(cnf, need_funs, cover_conf.budget, cover_ticks);

    if (etof_conf.do_autarky && !cnf.all_ys_defined()) {
        arjun->standalone_autarky(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-autarky.aig");
        SLOW_DEBUG_DO(check_stage(cnf, "autarky"));
    }

    if (etof_conf.do_extend_indep && !cnf.all_ys_defined()) {
        arjun->standalone_extend_synth(cnf, iconf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-extend_synth.aig");
        cnf.simplify_aigs(conf.verb);
        SLOW_DEBUG_DO(check_stage(cnf, "extend_synth"));
    }

    if (do_backward && !cnf.all_ys_defined()) {
        arjun->standalone_backward_round_synth(cnf, iconf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-minim_idep_synt.aig");
        cnf.simplify_aigs(conf.verb);
        SLOW_DEBUG_DO(check_stage(cnf, "minim_idep_synt"));
    }

    if (do_unate_def && !cnf.all_ys_defined()) {
        arjun->standalone_unate_def(cnf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-unate_def.aig");
        SLOW_DEBUG_DO(check_stage(cnf, "unate_def"));
    }

    if (!cnf.all_ys_defined() && has_defined(cnf))
        try_cover(cnf, need_funs, cover_conf.budget, cover_late_ticks);

    cnf.rewrite_aigs(conf.verb);
    SLOW_DEBUG_DO(check_stage(cnf, "rewrite_aigs"));
    if (use_brute_force_synth && !cnf.all_ys_defined()) {
        verb_print(1, "[arjun] Synthesis: brute-force decision trees");
        cnf = arjun->standalone_brute_force_synth(std::move(cnf), mconf, iconf);
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-brute_force_synth.aig");
        SLOW_DEBUG_DO(check_stage(cnf, "brute_force_synth"));
    }

    if (!cnf.all_ys_defined()) {
        synth_runner.run_strategies(cnf, mconf, strategies, [&](const double ticks) {
            try_cover(cnf, need_funs, cover_conf.budget, ticks);
        });

        release_assert(cnf.all_ys_defined() && "All Ys should have functions by now (synthesis or 2QBF), but some do not!");
        if (!conf.debug_synth.empty()) cnf.write_aig_defs_to_file(conf.debug_synth + "-cegr.aig");
        SLOW_DEBUG_DO(check_stage(cnf, "cegr"));
    }

    // Final output-side compaction, with balance: nothing downstream
    // re-encodes these into a repair loop, so the smallest form wins.
    cnf.rewrite_aigs(conf.verb, true);
    auto final_cnf = cnf;
    final_cnf.clear_orig_sampl_defs(); // final should not have orig sampl set defined
    if (!output_file.empty()) {
        if (!output_file.ends_with(".v")) final_cnf.write_aig_defs_to_file(output_file);
        else final_cnf.write_aig_def_to_verilog(output_file);
        cout << "c o [arjun] dumped synthesized functions to '" << output_file << "'" << endl;
    }
    if (!conf.debug_synth.empty()) {
        const string final_fname = conf.debug_synth + (debug_verilog ? "-final.v" : "-final.aig");
        if (debug_verilog) final_cnf.write_aig_def_to_verilog(final_fname);
        else final_cnf.write_aig_defs_to_file(final_fname);
        cout << "c o [arjun] you can check correctness by running: " << endl;
        cout << "./test-synth -u -v 1 " << input_file << " " << final_fname << endl;
        if (conf.verb >= 3) final_cnf.write_aig_defs_to_file_txt(conf.debug_synth + "-final.txt");
    }
    if (qbf2) {
        if (cover_done) qbf2_result(cnf, true);
        const auto cex = cnf.get_2qbf_cex();
        qbf2_result(cnf, cex.empty(), cex);
    }
}

void do_backward_pass() {
    ArjunNS::SimplifiedCNF cnf(fg);
    read_in_a_file(input_file, &cnf, etof_conf.all_indep, fg);
    cnf.clean_idiotic_mccomp_weights();
    cnf.check_cnf_sampl_sanity();
    if (cnf.get_num_no_touch() && !etof_conf.do_renumber) {
        cout << "ERROR: 'c p no-touch' needs --renumber 1, it's what puts the "
            "no-touch variables back to 1..k" << endl;
        exit(EXIT_FAILURE);
    }

    if (do_pre_backbone) arjun->standalone_backbone(cnf);
    const auto orig_sampl_vars = cnf.get_sampl_vars();
    if (do_backward) arjun->standalone_minimize_indep(cnf, iconf, etof_conf.all_indep);
    if (!debug_minim.empty()) {
        cnf.write_simpcnf(debug_minim, false);
        auto cnf2 = cnf;
        cnf2.renumber_sampling_vars_for_ganak();
        cnf2.write_simpcnf(debug_minim+"-renum", false);
    }

    if (!output_file.empty()) {
        arjun->standalone_elim_to_file(cnf, etof_conf, simp_conf, iconf);
        cnf.write_simpcnf(output_file, redundant_cls);
        cout << "c o [arjun] dumped simplified problem to '" << output_file << "'" << endl;
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
        if (synthesis || qbf2) {
            cout << "ERROR: Cannot use synthesis and appmc simplification at the same time" << endl;
            exit(EXIT_FAILURE);
        }
        cout << "c o [arjun] Setting defaults for AppMC CNF simplification" << endl;
        simp_conf.appmc = true;
        if (!program.is_used("--oraclevivif")) simp_conf.oracle_vivify = true;
        if (!program.is_used("--oraclesparsify")) simp_conf.oracle_sparsify = false;
        if (!program.is_used("--oraclevivifgetl")) simp_conf.oracle_vivify_get_learnts = 1;
        if (!program.is_used("--iter1")) simp_conf.iter1 = 2;
        if (!program.is_used("--iter2")) simp_conf.iter2 = 0;
    }

    if (program.is_used("--synth")) {
        if (simp_conf.appmc) {
            cout << "ERROR: Cannot use synthesis and appmc simplification at the same time" << endl;
            exit(EXIT_FAILURE);
        }
    }

    // Default ganak binary: look next to arjun binary, or in ../ganak/build/
    if (mconf.check_repair && mconf.ganak_binary.empty()) {
        namespace fs = std::filesystem;
        fs::path arjun_path = fs::canonical(fs::path(argv[0])).parent_path();
        // Try sibling directory convention: ../../ganak/build/ganak
        fs::path candidate = arjun_path / "../../ganak/build/ganak";
        if (fs::exists(candidate)) {
            mconf.ganak_binary = fs::canonical(candidate).string();
        } else {
            // Try same directory
            candidate = arjun_path / "ganak";
            if (fs::exists(candidate)) {
                mconf.ganak_binary = fs::canonical(candidate).string();
            } else {
                // Fall back to PATH
                mconf.ganak_binary = "ganak";
            }
        }
        verb_print(1, "[checkrepair] Using ganak binary: " << mconf.ganak_binary);
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
        case 2:
            fg = std::make_unique<ArjunNS::FGenComplex>();
            break;
        case 6:
            fg = std::make_unique<ArjunNS::FGenMPFComplex>(mpfr_precision);
            break;
        default:
            cout << "c o [arjun] ERROR: Unknown mode: " << mode << endl;
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
            cout << "ERROR: you can only pass at most 2 positional parameters: an INPUT file"
                ", optionally an OUTPUT file" << endl;
            exit(EXIT_FAILURE);
        }
    } catch (std::logic_error& e) {
        cout << "ERROR: you must give at least an input file" << endl;
        exit(EXIT_FAILURE);
    }

    input_file = files[0];
    if (files.size() >= 2) output_file = files[1];
    cout << "c o [arjun] Input file: " << input_file << endl;
    if (!output_file.empty())
        cout << "c o [arjun] Output file: " << output_file << endl;
    if (synthesis && !qbf2 && output_file.empty()) {
        cout << "ERROR: --synth needs an output file for the functions, ending in .aig or .v, or /dev/null" << endl;
        exit(EXIT_FAILURE);
    }
    if ((synthesis || qbf2) && !output_file.empty() && output_file != "/dev/null"
            && !output_file.ends_with(".aig") && !output_file.ends_with(".v")) {
        cout << "ERROR: the output file for the functions must end in .aig or .v, or be /dev/null" << endl;
        exit(EXIT_FAILURE);
    }
    if (synthesis || qbf2) {
        do_synth_2qbf();
    } else {
        do_backward_pass();
    }
    cout << "c o [arjun] All done. T: " << std::setprecision(2) << std::fixed
        << (cpuTime() - start_time) << endl;

    return 0;
}
