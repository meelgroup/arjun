/*
 Arjun - AIGRewriter Fuzzer

 Generates a random AIG `A`, simplifies it through AIGRewriter to `B`,
 and checks A and B are logically equivalent using two orthogonal methods:

   (1) SAT equivalence via a naive Tseitin encoding of both AIGs: encode
       each with one helper per AND node (the trivial, obviously-correct
       encoder), force the two output lits to differ, and expect UNSAT.
       Shares the implementation with fuzz_aig_to_cnf.

   (2) Random evaluation: 40 random input assignments, comparing
       AIG::evaluate(A) to AIG::evaluate(B). Less exhaustive but cheap and
       independent of the SAT encoder, so it catches mistakes the SAT
       check might miss (e.g. both encodings wrong in the same way).

 The generator corpus / shape distribution come from aig_fuzz_gen.h, which
 is shared with fuzz_aig_to_cnf — so if the rewriter breaks on a shape the
 encoder already exercises, we see it here too.

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#include "aig_rewrite.h"
#include "aig_fuzz_gen.h"
#include <cryptominisat5/cryptominisat.h>
#include <cassert>
#include <chrono>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <vector>

using namespace ArjunNS;
using namespace CMSat;
using std::cout;
using std::cerr;
using std::endl;
using std::vector;
using std::map;

static AIGManager aig_mng;

// Naive Tseitin encoding: one helper per AND node, 3 clauses each; constants
// via a single unit-clauses helper. Returns the output literal. Identical in
// spirit to the baseline used by fuzz_aig_to_cnf.
static Lit naive_encode(const aig_lit& aig, SATSolver& solver,
                        Lit& true_lit, bool& true_lit_set)
{
    map<aig_lit, Lit> cache;
    auto visitor = [&](AIGT type, uint32_t var,
                       const Lit* left, const Lit* right) -> Lit {
        if (type == AIGT::t_const) {
            if (!true_lit_set) {
                solver.new_var();
                true_lit = Lit(solver.nVars() - 1, false);
                solver.add_clause({true_lit});
                true_lit_set = true;
            }
            return true_lit;
        }
        if (type == AIGT::t_lit) return Lit(var, false);
        assert(type == AIGT::t_and);
        Lit l = *left;
        Lit r = *right;
        solver.new_var();
        Lit g(solver.nVars() - 1, false);
        solver.add_clause({~g, l});
        solver.add_clause({~g, r});
        solver.add_clause({g, ~l, ~r});
        return g;
    };
    return AIG::transform<Lit>(aig, visitor, cache);
}

// A <-> B equivalence: encode both, force out_a != out_b via a fresh
// activation lit, solve under that assumption, expect UNSAT.
static bool sat_equivalent(SATSolver& s, Lit a, Lit b) {
    s.new_var();
    Lit act = Lit(s.nVars() - 1, false);
    s.add_clause({~act, a, b});
    s.add_clause({~act, ~a, ~b});
    vector<Lit> assumps{act};
    lbool ret = s.solve(&assumps);
    s.add_clause({~act}); // retire the activation lit
    return ret == l_False;
}

// Largest variable index referenced by any literal in `aig`. Used to size
// the SAT solver before encoding.
static uint32_t max_var(const aig_lit& aig) {
    std::set<uint32_t> seen;
    AIG::get_dependent_vars(aig, seen,
                            std::numeric_limits<uint32_t>::max());
    return seen.empty() ? 0u : *seen.rbegin();
}

// Random-value check: pick random input assignments, evaluate both AIGs,
// expect identical results. Defs are empty — these AIGs have no defined
// variables, only primary inputs.
static bool random_check(const aig_lit& orig, const aig_lit& simplified,
                         uint32_t num_vars, std::mt19937& rng,
                         uint32_t num_trials)
{
    vector<aig_lit> defs(num_vars, nullptr);
    for (uint32_t t = 0; t < num_trials; t++) {
        vector<lbool> vals(num_vars);
        for (uint32_t v = 0; v < num_vars; v++) {
            vals[v] = (rng() & 1) ? l_True : l_False;
        }
        map<aig_lit, lbool> c_orig, c_simp;
        lbool e_orig = AIG::evaluate(vals, orig, defs, c_orig);
        lbool e_simp = AIG::evaluate(vals, simplified, defs, c_simp);
        if (e_orig != e_simp) {
            cerr << "  random_check: mismatch at trial " << t
                 << " orig=" << (e_orig == l_True ? "T" : e_orig == l_False ? "F" : "U")
                 << " simp=" << (e_simp == l_True ? "T" : e_simp == l_False ? "F" : "U")
                 << "  assignment:";
            for (uint32_t v = 0; v < num_vars; v++) {
                cerr << " x" << v << "=" << (vals[v] == l_True ? 1 : 0);
            }
            cerr << endl;
            return false;
        }
    }
    return true;
}

struct FuzzStats {
    uint64_t iters = 0;
    uint64_t nodes_before = 0;
    uint64_t nodes_after = 0;
    double total_time_s = 0;

    // Aggregated rule-firing counters across all iters. Used to assert that
    // each rewrite rule was exercised by the corpus — if a new rule lands
    // and its counter stays at 0 after N>>0 iters, the fuzzer is silently
    // not covering it and we want a loud signal.
    uint64_t total_const_prop = 0;
    uint64_t total_complement_elim = 0;
    uint64_t total_idempotent_elim = 0;
    uint64_t total_absorption = 0;
    uint64_t total_and_or_distrib = 0;
    uint64_t total_xor_simplify = 0;
    uint64_t total_struct_hash_hits = 0;

    void print() const {
        cout << "\n=== fuzz_aig_rewrite statistics ===" << endl;
        cout << "Iterations:           " << iters << endl;
        cout << "Avg nodes before:     " << std::fixed << std::setprecision(1)
             << (iters ? (double)nodes_before / iters : 0.0) << endl;
        cout << "Avg nodes after:      " << std::fixed << std::setprecision(1)
             << (iters ? (double)nodes_after / iters : 0.0) << endl;
        if (nodes_before > 0) {
            double pct = 100.0 * (1.0 - (double)nodes_after / nodes_before);
            cout << "Node reduction:       "
                 << std::setprecision(1) << pct << "%" << endl;
        }
        cout << "Time:                 " << std::fixed << std::setprecision(1)
             << total_time_s << "s" << endl;
        cout << "Rule fires:           "
             << "const_prop="     << total_const_prop
             << "  complement="   << total_complement_elim
             << "  idempotent="   << total_idempotent_elim
             << "  absorption="   << total_absorption
             << "  distrib="      << total_and_or_distrib
             << "  xor_simp="     << total_xor_simplify
             << "  hash_hits="    << total_struct_hash_hits
             << endl;
    }

    // Verify every rule was triggered at least once. Called at end of a run
    // long enough that zero fires implies the shape corpus or the rule body
    // is broken. Returns the count of rules that never fired.
    int report_unfired_rules() const {
        struct Rule { const char* name; uint64_t count; };
        Rule rules[] = {
            {"const_prop",      total_const_prop},
            {"complement_elim", total_complement_elim},
            {"idempotent_elim", total_idempotent_elim},
            {"absorption",      total_absorption},
            {"and_or_distrib",  total_and_or_distrib},
            {"xor_simplify",    total_xor_simplify},
            {"struct_hash_hits",total_struct_hash_hits},
        };
        int unfired = 0;
        for (const auto& r : rules) {
            if (r.count == 0) {
                cerr << "WARNING: rule '" << r.name
                     << "' never fired across " << iters << " iterations"
                     << endl;
                unfired++;
            }
        }
        return unfired;
    }
};

static void report_failure(const aig_lit& orig, const aig_lit& simp,
                           uint32_t num_vars, uint64_t seed, uint64_t iter,
                           const char* phase)
{
    cerr << "\n!!! FAILURE in phase '" << phase << "' at iter " << iter << " !!!" << endl;
    cerr << "Seed: " << seed << "  num_vars: " << num_vars << endl;
    cerr << "ORIG:       " << orig << endl;
    cerr << "SIMPLIFIED: " << simp << endl;
}

static bool run_one(const aig_lit& orig, uint32_t num_vars,
                    uint64_t seed, uint64_t iter, std::mt19937& rng,
                    FuzzStats& fs, bool verbose, bool deep)
{
    // 1. Rewrite.
    AIGRewriter rw;
    rw.do_deep_passes = deep;
    aig_lit simp = rw.rewrite(orig);
    if (!simp) simp = orig;

    // 1a. Idempotence: rewriting an already-rewritten AIG must keep it
    // equivalent and must never make it bigger. A growth here would mean a
    // rewrite rule is non-confluent / oscillating; a mismatch would mean a
    // rule is unsound only on already-canonical input.
    {
        AIGRewriter rw2;
        rw2.do_deep_passes = deep;
        aig_lit simp2 = rw2.rewrite(simp);
        if (!simp2) simp2 = simp;
        if (!random_check(simp, simp2, num_vars, rng, 40)) {
            report_failure(orig, simp2, num_vars, seed, iter,
                           "random_check(idempotence)");
            return false;
        }
        if (AIG::count_aig_nodes_fast(simp2)
                > AIG::count_aig_nodes_fast(simp)) {
            report_failure(orig, simp2, num_vars, seed, iter,
                           "rewrite grew an already-rewritten AIG");
            return false;
        }
    }

    size_t before = AIG::count_aig_nodes_fast(orig);
    size_t after  = AIG::count_aig_nodes_fast(simp);
    fs.nodes_before += before;
    fs.nodes_after  += after;

    const auto& s = rw.get_stats();
    fs.total_const_prop       += s.const_prop;
    fs.total_complement_elim  += s.complement_elim;
    fs.total_idempotent_elim  += s.idempotent_elim;
    fs.total_absorption       += s.absorption;
    fs.total_and_or_distrib   += s.and_or_distrib;
    fs.total_xor_simplify     += s.xor_simplify;
    fs.total_struct_hash_hits += s.structural_hash_hits;

    if (verbose) {
        cout << "[" << std::setw(6) << iter << "] "
             << "nodes " << std::setw(5) << before << " -> " << std::setw(5) << after
             << "  (num_vars=" << num_vars << ")" << endl;
    }

    // 2. Random-value check (40 trials, as the user requested).
    if (!random_check(orig, simp, num_vars, rng, 40)) {
        report_failure(orig, simp, num_vars, seed, iter, "random_check");
        return false;
    }

    // 3. SAT-based equivalence. Both AIGs are encoded by the trivial Tseitin
    // baseline — same variable range for primary inputs (the first num_vars
    // vars in the solver), fresh helpers per AND node for each.
    SATSolver solver;
    solver.set_verbosity(0);
    uint32_t mv_orig = max_var(orig);
    uint32_t mv_simp = max_var(simp);
    uint32_t mv = std::max(mv_orig, mv_simp);
    solver.new_vars(mv + 1);

    Lit true_lit_unused;
    bool true_set = false;
    Lit out_orig = naive_encode(orig, solver, true_lit_unused, true_set);
    Lit out_simp = naive_encode(simp, solver, true_lit_unused, true_set);

    if (!sat_equivalent(solver, out_orig, out_simp)) {
        report_failure(orig, simp, num_vars, seed, iter, "sat_equivalent");
        cerr << "  out_orig=" << out_orig << "  out_simp=" << out_simp << endl;
        return false;
    }

    return true;
}

static void print_usage(const char* prog) {
    cout << "Usage: " << prog
         << " [--num N] [--seed S] [--vars V] [--depth D] [--nodes N] [--verbose]" << endl;
    cout << "  --num N     Number of iterations (0 = infinite, default 0)" << endl;
    cout << "  --seed S    Random seed (default: random)" << endl;
    cout << "  --vars V    Max input variables (default: 8)" << endl;
    cout << "  --depth D   Max AIG depth (default: 10)" << endl;
    cout << "  --nodes N   Max nodes per AIG (default: 50)" << endl;
    cout << "  --verbose   Per-iteration progress output" << endl;
    cout << "  --require-all-rules  Fail run if any rewrite rule was never" << endl;
    cout << "                       triggered. Useful when adding new rules" << endl;
    cout << "                       to confirm the shape corpus covers them." << endl;
}

int main(int argc, char** argv) {
    uint64_t num_iters = 0;
    uint64_t seed = std::random_device{}();
    uint32_t max_vars = 8;
    uint32_t max_depth = 10;
    uint32_t max_nodes_cfg = 50;
    bool verbose = false;
    bool require_all_rules = false;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--num") == 0 && i + 1 < argc) num_iters = std::stoull(argv[++i]);
        else if (strcmp(argv[i], "--seed") == 0 && i + 1 < argc) seed = std::stoull(argv[++i]);
        else if (strcmp(argv[i], "--vars") == 0 && i + 1 < argc) max_vars = std::stoul(argv[++i]);
        else if (strcmp(argv[i], "--depth") == 0 && i + 1 < argc) max_depth = std::stoul(argv[++i]);
        else if (strcmp(argv[i], "--nodes") == 0 && i + 1 < argc) max_nodes_cfg = std::stoul(argv[++i]);
        else if (strcmp(argv[i], "--verbose") == 0) verbose = true;
        else if (strcmp(argv[i], "--require-all-rules") == 0) require_all_rules = true;
        else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            print_usage(argv[0]);
            return 0;
        } else {
            cerr << "Unknown option: " << argv[i] << endl;
            print_usage(argv[0]);
            return 1;
        }
    }

    cout << "fuzz_aig_rewrite" << endl;
    cout << "Seed: " << seed << "  max_vars: " << max_vars
         << "  max_depth: " << max_depth << "  max_nodes: " << max_nodes_cfg << endl;
    cout << "Reproduce: fuzz_aig_rewrite --seed " << seed
         << " --vars " << max_vars << " --depth " << max_depth
         << " --nodes " << max_nodes_cfg << endl;
    if (num_iters > 0) cout << "Running " << num_iters << " iterations" << endl;
    else cout << "Running indefinitely (Ctrl-C to stop)" << endl;

    std::mt19937 rng(seed);
    FuzzStats fs;
    auto t_start = std::chrono::steady_clock::now();

    for (uint64_t iter = 0; num_iters == 0 || iter < num_iters; iter++) {
        uint32_t num_vars = 2 + rng() % (max_vars - 1);
        uint32_t depth = 3 + rng() % (max_depth - 2);
        uint32_t max_nodes = 8 + rng() % max_nodes_cfg;

        aig_lit aig = fuzz::gen_random_shape(aig_mng, rng, num_vars, depth, max_nodes);
        if (!aig) continue;

        // Exercise both the default (cheap) and --deeprewrite (deep) pass sets.
        const bool deep = (rng() & 1);

        if (!run_one(aig, num_vars, seed, iter, rng, fs, verbose, deep)) return 1;
        fs.iters++;

        if (iter > 0 && iter % 500 == 0) {
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - t_start).count();
            double pct = fs.nodes_before > 0
                ? 100.0 * (1.0 - (double)fs.nodes_after / fs.nodes_before) : 0.0;
            cout << "[" << iter << "] OK  "
                 << std::fixed << std::setprecision(0) << iter / elapsed << " it/s  "
                 << "avg-nodes=" << std::setprecision(1)
                 << (double)fs.nodes_before / fs.iters
                 << " -> " << (double)fs.nodes_after / fs.iters
                 << "  (-" << pct << "%)"
                 << endl;
        }
    }

    auto t_end = std::chrono::steady_clock::now();
    fs.total_time_s = std::chrono::duration<double>(t_end - t_start).count();
    fs.print();
    if (require_all_rules) {
        const int unfired = fs.report_unfired_rules();
        if (unfired > 0) {
            cerr << "FAIL: " << unfired
                 << " rewrite rules never fired (use --require-all-rules)" << endl;
            return 1;
        }
        cout << "All rewrite rules fired at least once." << endl;
    }
    cout << "\nAll tests passed!" << endl;
    return 0;
}
