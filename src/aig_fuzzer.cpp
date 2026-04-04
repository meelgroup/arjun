/*
 Arjun - AIG Rewriter Fuzzer

 Generates random AIGs, simplifies them, and checks equivalence
 against the original using a SAT solver (Tseitin encoding).

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.
 MIT License
 */

#include "aig_rewrite.h"
#include <cryptominisat5/cryptominisat.h>
#include <iostream>
#include <random>
#include <chrono>

#include <cassert>
#include <cstring>
#include <map>

#include <vector>
#include <functional>
#include <iomanip>

using namespace ArjunNS;
using namespace CMSat;
using std::cout;
using std::cerr;
using std::endl;
using std::vector;
using std::map;


static AIGManager aig_mng;

// Generate a random AIG with given number of input variables and approximate depth
static aig_ptr gen_random_aig(
    std::mt19937& rng,
    uint32_t num_vars,
    uint32_t depth,
    uint32_t max_nodes)
{
    // Pool of available sub-expressions
    vector<aig_ptr> pool;
    for (uint32_t v = 0; v < num_vars; v++) {
        pool.push_back(AIG::new_lit(v, false));
        pool.push_back(AIG::new_lit(v, true));
    }
    // Occasionally add constants
    if (rng() % 10 == 0) pool.push_back(aig_mng.new_const(true));
    if (rng() % 10 == 0) pool.push_back(aig_mng.new_const(false));

    uint32_t nodes_built = 0;
    for (uint32_t d = 0; d < depth && nodes_built < max_nodes; d++) {
        uint32_t new_this_level = 1 + rng() % 3;
        for (uint32_t i = 0; i < new_this_level && nodes_built < max_nodes; i++) {
            if (pool.size() < 2) break;
            uint32_t idx_a = rng() % pool.size();
            uint32_t idx_b = rng() % pool.size();
            if (idx_a == idx_b) idx_b = (idx_b + 1) % pool.size();

            aig_ptr a = pool[idx_a];
            aig_ptr b = pool[idx_b];

            uint32_t op = rng() % 6;
            aig_ptr node;
            switch (op) {
                case 0: node = AIG::new_and(a, b, false); break;
                case 1: node = AIG::new_and(a, b, true); break;  // NAND
                case 2: node = AIG::new_or(a, b, false); break;
                case 3: node = AIG::new_or(a, b, true); break;   // NOR
                case 4: node = AIG::new_not(a); break;
                case 5: {
                    // ITE with a random branch variable
                    uint32_t bvar = rng() % num_vars;
                    bool bneg = rng() % 2;
                    node = AIG::new_ite(a, b, Lit(bvar, bneg));
                    break;
                }
            }
            pool.push_back(node);
            nodes_built++;
        }
    }

    // Pick a random non-trivial node from the pool (prefer deeper ones)
    if (pool.size() <= num_vars * 2) {
        // Only literals, pick any
        return pool[rng() % pool.size()];
    }
    // Pick from the latter half of the pool (deeper nodes)
    uint32_t start = pool.size() / 2;
    return pool[start + rng() % (pool.size() - start)];
}

// Tseitin-encode an AIG into a SAT solver, returning the output literal
static Lit aig_to_sat(const aig_ptr& aig, SATSolver& solver, uint32_t num_input_vars,
                       map<aig_ptr, Lit>& cache)
{
    std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> visitor =
        [&](AIGT type, uint32_t var, bool neg, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                // We need a "true" literal. Create one and force it.
                solver.new_var();
                Lit tlit = Lit(solver.nVars() - 1, false);
                solver.add_clause(vector<Lit>{tlit}); // force true
                return neg ? ~tlit : tlit;
            }
            if (type == AIGT::t_lit) {
                assert(var < num_input_vars);
                return Lit(var, neg);
            }
            if (type == AIGT::t_and) {
                Lit l = *left;
                Lit r = *right;
                solver.new_var();
                Lit out = Lit(solver.nVars() - 1, false);
                // Tseitin: out <=> (l AND r)
                solver.add_clause(vector<Lit>{~out, l});
                solver.add_clause(vector<Lit>{~out, r});
                solver.add_clause(vector<Lit>{~l, ~r, out});
                return neg ? ~out : out;
            }
            assert(false && "Unknown AIG type");
            return Lit(0, false);
        };
    return AIG::transform<Lit>(aig, visitor, cache);
}

// Check equivalence of two AIGs using SAT
// Returns true if they are equivalent
static bool check_equivalence_sat(const aig_ptr& orig, const aig_ptr& simplified,
                                   uint32_t num_vars)
{
    SATSolver solver;
    solver.set_verbosity(0);

    // Create input variables
    solver.new_vars(num_vars);

    // Encode both AIGs
    map<aig_ptr, Lit> cache_orig, cache_simp;
    Lit out_orig = aig_to_sat(orig, solver, num_vars, cache_orig);
    Lit out_simp = aig_to_sat(simplified, solver, num_vars, cache_simp);

    // Assert XOR of outputs (they must differ for SAT)
    // XOR(a,b) = (a OR b) AND (~a OR ~b)
    solver.new_var();
    Lit xor_out = Lit(solver.nVars() - 1, false);

    // xor_out <=> (out_orig XOR out_simp)
    // xor_out => (out_orig OR out_simp) AND (~out_orig OR ~out_simp)
    // ~xor_out => (out_orig <=> out_simp)
    // Encode: xor_out = out_orig XOR out_simp
    solver.add_clause(vector<Lit>{~xor_out, out_orig, out_simp});
    solver.add_clause(vector<Lit>{~xor_out, ~out_orig, ~out_simp});
    solver.add_clause(vector<Lit>{xor_out, ~out_orig, out_simp});
    solver.add_clause(vector<Lit>{xor_out, out_orig, ~out_simp});

    // Force xor_out to be true (i.e., outputs differ)
    solver.add_clause(vector<Lit>{xor_out});

    lbool ret = solver.solve();
    return ret == l_False; // UNSAT means equivalent
}

// Also check with brute-force evaluation for small variable counts
static bool check_equivalence_eval(const aig_ptr& orig, const aig_ptr& simplified,
                                    uint32_t num_vars)
{
    if (num_vars > 20) return true; // too many to enumerate
    uint32_t limit = 1u << num_vars;
    vector<aig_ptr> defs(num_vars, nullptr);
    for (uint32_t mask = 0; mask < limit; mask++) {
        vector<lbool> vals(num_vars);
        for (uint32_t v = 0; v < num_vars; v++) {
            vals[v] = ((mask >> v) & 1) ? l_True : l_False;
        }
        map<aig_ptr, lbool> cache1, cache2;
        lbool r1 = AIG::evaluate(vals, orig, defs, cache1);
        lbool r2 = AIG::evaluate(vals, simplified, defs, cache2);
        if (r1 != r2) return false;
    }
    return true;
}

struct FuzzerStats {
    uint64_t total_tests = 0;
    uint64_t sat_equiv_pass = 0;
    uint64_t eval_equiv_pass = 0;
    uint64_t nodes_before_total = 0;
    uint64_t nodes_after_total = 0;
    uint64_t rewrite_reduced = 0;   // cases where rewriting reduced nodes
    uint64_t rewrite_same = 0;      // cases where rewriting didn't change node count
    uint64_t rewrite_grew = 0;      // cases where rewriting increased nodes (shouldn't happen often)
    double total_sat_time_ms = 0;
    double total_rewrite_time_ms = 0;

    void print() const {
        cout << "\n=== Fuzzer Statistics ===" << endl;
        cout << "Tests run:      " << total_tests << endl;
        cout << "SAT equiv pass: " << sat_equiv_pass << endl;
        cout << "Eval equiv pass:" << eval_equiv_pass << endl;
        cout << "Avg nodes before: " << std::fixed << std::setprecision(1)
             << (total_tests > 0 ? (double)nodes_before_total / total_tests : 0) << endl;
        cout << "Avg nodes after:  "
             << (total_tests > 0 ? (double)nodes_after_total / total_tests : 0) << endl;
        cout << "Reduced: " << rewrite_reduced
             << "  Same: " << rewrite_same
             << "  Grew: " << rewrite_grew << endl;
        cout << "Avg SAT time:     "
             << (total_tests > 0 ? total_sat_time_ms / total_tests : 0) << " ms" << endl;
        cout << "Avg rewrite time: "
             << (total_tests > 0 ? total_rewrite_time_ms / total_tests : 0) << " ms" << endl;
    }
};

static void print_usage(const char* prog) {
    cout << "Usage: " << prog << " [--num N] [--seed S] [--vars V] [--depth D] [--verbose]" << endl;
    cout << "  --num N     Number of iterations (0 = infinite, default)" << endl;
    cout << "  --seed S    Random seed (default: time-based)" << endl;
    cout << "  --vars V    Max input variables (default: 6)" << endl;
    cout << "  --depth D   Max AIG depth (default: 8)" << endl;
    cout << "  --verbose   Print each AIG before/after" << endl;
}

int main(int argc, char** argv) {
    uint64_t num_iters = 0; // 0 = infinite
    uint64_t seed = std::random_device{}();
    uint32_t max_vars = 6;
    uint32_t max_depth = 8;
    bool verbose = false;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--num") == 0 && i + 1 < argc) {
            num_iters = std::stoull(argv[++i]);
        } else if (strcmp(argv[i], "--seed") == 0 && i + 1 < argc) {
            seed = std::stoull(argv[++i]);
        } else if (strcmp(argv[i], "--vars") == 0 && i + 1 < argc) {
            max_vars = std::stoul(argv[++i]);
        } else if (strcmp(argv[i], "--depth") == 0 && i + 1 < argc) {
            max_depth = std::stoul(argv[++i]);
        } else if (strcmp(argv[i], "--verbose") == 0) {
            verbose = true;
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            print_usage(argv[0]);
            return 0;
        } else {
            cerr << "Unknown option: " << argv[i] << endl;
            print_usage(argv[0]);
            return 1;
        }
    }

    cout << "AIG Rewriter Fuzzer" << endl;
    cout << "Seed: " << seed << "  Max vars: " << max_vars
         << "  Max depth: " << max_depth << endl;
    cout << "Reproduce: aig-fuzzer --seed " << seed
         << " --vars " << max_vars << " --depth " << max_depth << endl;
    if (num_iters > 0) cout << "Running " << num_iters << " iterations" << endl;
    else cout << "Running indefinitely (Ctrl-C to stop)" << endl;
    cout << endl;

    std::mt19937 rng(seed);
    FuzzerStats stats;

    for (uint64_t iter = 0; num_iters == 0 || iter < num_iters; iter++) {
        // Randomize parameters for this iteration
        uint32_t num_vars = 2 + rng() % (max_vars - 1);
        uint32_t depth = 2 + rng() % (max_depth - 1);
        uint32_t max_nodes = 5 + rng() % 30;

        // Generate random AIG
        if (verbose) cout << "[" << iter << "] Generating..." << std::flush;
        aig_ptr orig = gen_random_aig(rng, num_vars, depth, max_nodes);
        if (!orig) {
            if (verbose) cout << "[" << iter << "] Generated null AIG, skipping" << endl;
            continue;
        }

        size_t nodes_before = AIG::count_aig_nodes(orig);

        if (verbose) {
            cout << "[" << iter << "] Original (" << nodes_before << " nodes, "
                 << num_vars << " vars): " << orig << endl;
        }

        // Simplify
        auto t_rw_start = std::chrono::steady_clock::now();
        AIGRewriter rw;
        aig_ptr simplified = rw.rewrite(orig);
        auto t_rw_end = std::chrono::steady_clock::now();
        double rw_ms = std::chrono::duration<double, std::milli>(t_rw_end - t_rw_start).count();

        if (!simplified) {
            cerr << "ERROR: rewrite returned null for non-null input at iter " << iter << endl;
            cerr << "Seed: " << seed << "  Iter: " << iter << endl;
            cerr << "Original: " << orig << endl;
            return 1;
        }

        size_t nodes_after = AIG::count_aig_nodes(simplified);

        if (verbose) {
            cout << "  Simplified (" << nodes_after << " nodes): " << simplified << endl;
        }

        // Check equivalence with SAT solver
        auto t_sat_start = std::chrono::steady_clock::now();
        bool sat_ok = check_equivalence_sat(orig, simplified, num_vars);
        auto t_sat_end = std::chrono::steady_clock::now();
        double sat_ms = std::chrono::duration<double, std::milli>(t_sat_end - t_sat_start).count();

        if (!sat_ok) {
            cerr << "\n!!! EQUIVALENCE FAILURE (SAT) at iter " << iter << " !!!" << endl;
            cerr << "Seed: " << seed << "  Iter: " << iter << endl;
            cerr << "Num vars: " << num_vars << "  Depth: " << depth << endl;
            cerr << "Original  (" << nodes_before << " nodes): " << orig << endl;
            cerr << "Simplified (" << nodes_after << " nodes): " << simplified << endl;

            // Print truth table
            cerr << "Truth table:" << endl;
            vector<aig_ptr> defs(num_vars, nullptr);
            for (uint32_t mask = 0; mask < (1u << num_vars) && mask < 64; mask++) {
                vector<lbool> vals(num_vars);
                for (uint32_t v = 0; v < num_vars; v++)
                    vals[v] = ((mask >> v) & 1) ? l_True : l_False;
                map<aig_ptr, lbool> c1, c2;
                lbool r1 = AIG::evaluate(vals, orig, defs, c1);
                lbool r2 = AIG::evaluate(vals, simplified, defs, c2);
                if (r1 != r2) {
                    cerr << "  DIFFER at mask=" << mask << ": orig="
                         << (r1 == l_True ? "T" : "F")
                         << " simp=" << (r2 == l_True ? "T" : "F") << endl;
                }
            }
            return 1;
        }

        // Cross-check with evaluation for small cases
        bool eval_ok = check_equivalence_eval(orig, simplified, num_vars);
        if (!eval_ok) {
            cerr << "\n!!! EQUIVALENCE FAILURE (EVAL) at iter " << iter << " !!!" << endl;
            cerr << "Seed: " << seed << "  Iter: " << iter << endl;
            cerr << "Original  (" << nodes_before << " nodes): " << orig << endl;
            cerr << "Simplified (" << nodes_after << " nodes): " << simplified << endl;
            return 1;
        }

        // Update stats
        stats.total_tests++;
        stats.sat_equiv_pass++;
        stats.eval_equiv_pass++;
        stats.nodes_before_total += nodes_before;
        stats.nodes_after_total += nodes_after;
        stats.total_sat_time_ms += sat_ms;
        stats.total_rewrite_time_ms += rw_ms;
        if (nodes_after < nodes_before) stats.rewrite_reduced++;
        else if (nodes_after == nodes_before) stats.rewrite_same++;
        else stats.rewrite_grew++;

        // Progress output
        if (iter % 100 == 0 && iter > 0) {
            cout << "[" << iter << "] All OK. Avg nodes: "
                 << std::fixed << std::setprecision(1)
                 << (double)stats.nodes_before_total / stats.total_tests
                 << " -> "
                 << (double)stats.nodes_after_total / stats.total_tests
                 << "  reduced: " << stats.rewrite_reduced
                 << "  same: " << stats.rewrite_same
                 << "  grew: " << stats.rewrite_grew
                 << endl;
        } else if (iter < 10 || (iter < 100 && iter % 10 == 0)) {
            cout << "[" << iter << "] OK (" << nodes_before << " -> " << nodes_after
                 << " nodes, SAT: " << std::fixed << std::setprecision(2)
                 << sat_ms << "ms)" << endl;
        }
    }

    stats.print();
    cout << "\nAll " << stats.total_tests << " tests passed!" << endl;
    return 0;
}
