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

// Generate a random AIG with given number of input variables
static aig_ptr gen_random_aig(
    std::mt19937& rng,
    uint32_t num_vars,
    uint32_t depth,
    uint32_t max_nodes)
{
    vector<aig_ptr> pool;
    for (uint32_t v = 0; v < num_vars; v++) {
        pool.push_back(AIG::new_lit(v, false));
        pool.push_back(AIG::new_lit(v, true));
    }
    if (rng() % 8 == 0) pool.push_back(aig_mng.new_const(true));
    if (rng() % 8 == 0) pool.push_back(aig_mng.new_const(false));

    uint32_t nodes_built = 0;
    for (uint32_t d = 0; d < depth && nodes_built < max_nodes; d++) {
        // Build more nodes per level for deeper AIGs
        uint32_t new_this_level = 1 + rng() % 4;
        for (uint32_t i = 0; i < new_this_level && nodes_built < max_nodes; i++) {
            if (pool.size() < 2) break;

            // Bias toward recent nodes to build deeper structures
            auto pick = [&]() -> uint32_t {
                if (rng() % 3 == 0) return rng() % pool.size(); // uniform
                uint32_t lo = pool.size() > 4 ? pool.size() - pool.size()/2 : 0;
                return lo + rng() % (pool.size() - lo);
            };
            uint32_t idx_a = pick();
            uint32_t idx_b = pick();
            if (idx_a == idx_b) idx_b = (idx_b + 1) % pool.size();

            aig_ptr a = pool[idx_a];
            aig_ptr b = pool[idx_b];

            uint32_t op = rng() % 7;
            aig_ptr node;
            switch (op) {
                case 0: node = AIG::new_and(a, b, false); break;
                case 1: node = AIG::new_and(a, b, true); break;
                case 2: node = AIG::new_or(a, b, false); break;
                case 3: node = AIG::new_or(a, b, true); break;
                case 4: node = AIG::new_not(a); break;
                case 5: {
                    uint32_t bvar = rng() % num_vars;
                    bool bneg = rng() % 2;
                    node = AIG::new_ite(a, b, Lit(bvar, bneg));
                    break;
                }
                case 6: {
                    // XOR: new_or(new_and(a, new_not(b)), new_and(new_not(a), b))
                    node = AIG::new_or(
                        AIG::new_and(a, AIG::new_not(b)),
                        AIG::new_and(AIG::new_not(a), b));
                    break;
                }
            }
            pool.push_back(node);
            nodes_built++;
        }
    }

    if (pool.size() <= num_vars * 2) {
        return pool[rng() % pool.size()];
    }
    // Pick from the last third (deepest nodes)
    uint32_t start = pool.size() * 2 / 3;
    return pool[start + rng() % (pool.size() - start)];
}

// Generate multiple random AIGs that share substructure
static vector<aig_ptr> gen_random_aig_batch(
    std::mt19937& rng,
    uint32_t num_vars,
    uint32_t count)
{
    vector<aig_ptr> pool;
    for (uint32_t v = 0; v < num_vars; v++) {
        pool.push_back(AIG::new_lit(v, false));
        pool.push_back(AIG::new_lit(v, true));
    }

    // Build shared internal nodes
    uint32_t shared_nodes = 5 + rng() % 20;
    for (uint32_t i = 0; i < shared_nodes; i++) {
        if (pool.size() < 2) break;
        uint32_t idx_a = rng() % pool.size();
        uint32_t idx_b = rng() % pool.size();
        if (idx_a == idx_b) idx_b = (idx_b + 1) % pool.size();
        uint32_t op = rng() % 5;
        aig_ptr node;
        switch (op) {
            case 0: node = AIG::new_and(pool[idx_a], pool[idx_b]); break;
            case 1: node = AIG::new_or(pool[idx_a], pool[idx_b]); break;
            case 2: node = AIG::new_not(pool[idx_a]); break;
            case 3: node = AIG::new_and(pool[idx_a], pool[idx_b], true); break;
            case 4: {
                uint32_t bvar = rng() % num_vars;
                node = AIG::new_ite(pool[idx_a], pool[idx_b], Lit(bvar, rng() % 2));
                break;
            }
        }
        pool.push_back(node);
    }

    // Pick `count` outputs from the pool
    vector<aig_ptr> results;
    for (uint32_t i = 0; i < count; i++) {
        uint32_t start = pool.size() > 4 ? pool.size() / 2 : 0;
        results.push_back(pool[start + rng() % (pool.size() - start)]);
    }
    return results;
}

// Tseitin-encode an AIG into a SAT solver, returning the output literal
static Lit aig_to_sat(const aig_ptr& aig, SATSolver& solver, uint32_t num_input_vars,
                       map<aig_ptr, Lit>& cache)
{
    std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> visitor =
        [&](AIGT type, uint32_t var, bool neg, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                solver.new_var();
                Lit tlit = Lit(solver.nVars() - 1, false);
                solver.add_clause(vector<Lit>{tlit});
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

// Check equivalence of two AIGs using SAT (UNSAT = equivalent)
static bool check_equivalence_sat(const aig_ptr& orig, const aig_ptr& simplified,
                                   uint32_t num_vars)
{
    SATSolver solver;
    solver.set_verbosity(0);
    solver.new_vars(num_vars);

    map<aig_ptr, Lit> cache_orig, cache_simp;
    Lit out_orig = aig_to_sat(orig, solver, num_vars, cache_orig);
    Lit out_simp = aig_to_sat(simplified, solver, num_vars, cache_simp);

    // XOR encoding: force outputs to differ
    solver.new_var();
    Lit xor_out = Lit(solver.nVars() - 1, false);
    solver.add_clause(vector<Lit>{~xor_out, out_orig, out_simp});
    solver.add_clause(vector<Lit>{~xor_out, ~out_orig, ~out_simp});
    solver.add_clause(vector<Lit>{xor_out, ~out_orig, out_simp});
    solver.add_clause(vector<Lit>{xor_out, out_orig, ~out_simp});
    solver.add_clause(vector<Lit>{xor_out});

    return solver.solve() == l_False;
}

// Brute-force evaluation check for small variable counts
static bool check_equivalence_eval(const aig_ptr& orig, const aig_ptr& simplified,
                                    uint32_t num_vars)
{
    if (num_vars > 18) return true;
    uint32_t limit = 1u << num_vars;
    vector<aig_ptr> defs(num_vars, nullptr);
    for (uint32_t mask = 0; mask < limit; mask++) {
        vector<lbool> vals(num_vars);
        for (uint32_t v = 0; v < num_vars; v++)
            vals[v] = ((mask >> v) & 1) ? l_True : l_False;
        map<aig_ptr, lbool> c1, c2;
        lbool r1 = AIG::evaluate(vals, orig, defs, c1);
        lbool r2 = AIG::evaluate(vals, simplified, defs, c2);
        if (r1 != r2) return false;
    }
    return true;
}

static void report_failure(const char* method, const aig_ptr& orig, const aig_ptr& simplified,
                           uint32_t num_vars, uint64_t seed, uint64_t iter,
                           size_t nodes_before, size_t nodes_after)
{
    cerr << "\n!!! EQUIVALENCE FAILURE (" << method << ") at iter " << iter << " !!!" << endl;
    cerr << "Seed: " << seed << "  Iter: " << iter << endl;
    cerr << "Num vars: " << num_vars << endl;
    cerr << "Original  (" << nodes_before << " nodes): " << orig << endl;
    cerr << "Simplified (" << nodes_after << " nodes): " << simplified << endl;

    if (num_vars <= 6) {
        cerr << "Truth table differences:" << endl;
        vector<aig_ptr> defs(num_vars, nullptr);
        for (uint32_t mask = 0; mask < (1u << num_vars); mask++) {
            vector<lbool> vals(num_vars);
            for (uint32_t v = 0; v < num_vars; v++)
                vals[v] = ((mask >> v) & 1) ? l_True : l_False;
            map<aig_ptr, lbool> c1, c2;
            lbool r1 = AIG::evaluate(vals, orig, defs, c1);
            lbool r2 = AIG::evaluate(vals, simplified, defs, c2);
            if (r1 != r2) {
                cerr << "  mask=" << mask << " (";
                for (uint32_t v = 0; v < num_vars; v++)
                    cerr << "x" << v+1 << "=" << ((mask >> v) & 1);
                cerr << "): orig=" << (r1 == l_True ? "T" : "F")
                     << " simp=" << (r2 == l_True ? "T" : "F") << endl;
            }
        }
    }
}

// Verify a single AIG transformation
static bool verify_rewrite(const aig_ptr& orig, const aig_ptr& simplified,
                           uint32_t num_vars, uint64_t seed, uint64_t iter,
                           const char* method)
{
    if (!simplified) {
        cerr << "ERROR: " << method << " returned null at iter " << iter << endl;
        return false;
    }

    size_t nb = AIG::count_aig_nodes(orig);
    size_t na = AIG::count_aig_nodes(simplified);

    if (!check_equivalence_sat(orig, simplified, num_vars)) {
        report_failure(method, orig, simplified, num_vars, seed, iter, nb, na);
        return false;
    }
    if (!check_equivalence_eval(orig, simplified, num_vars)) {
        report_failure(method, orig, simplified, num_vars, seed, iter, nb, na);
        return false;
    }
    return true;
}

struct FuzzerStats {
    uint64_t total_tests = 0;
    uint64_t rewrite_tests = 0;
    uint64_t rewrite_all_tests = 0;
    uint64_t simplify_tests = 0;
    uint64_t double_rewrite_tests = 0;
    uint64_t nodes_before_total = 0;
    uint64_t nodes_after_total = 0;
    uint64_t rewrite_reduced = 0;
    uint64_t rewrite_same = 0;
    uint64_t rewrite_grew = 0;
    double total_time_ms = 0;

    void print() const {
        cout << "\n=== Fuzzer Statistics ===" << endl;
        cout << "Total iterations: " << total_tests << endl;
        cout << "  rewrite:        " << rewrite_tests << endl;
        cout << "  rewrite_all:    " << rewrite_all_tests << endl;
        cout << "  simplify_aig:   " << simplify_tests << endl;
        cout << "  double_rewrite: " << double_rewrite_tests << endl;
        cout << "Avg nodes: " << std::fixed << std::setprecision(1)
             << (total_tests > 0 ? (double)nodes_before_total / total_tests : 0)
             << " -> "
             << (total_tests > 0 ? (double)nodes_after_total / total_tests : 0)
             << endl;
        cout << "Reduced: " << rewrite_reduced
             << "  Same: " << rewrite_same
             << "  Grew: " << rewrite_grew << endl;
        cout << "Total time: " << std::fixed << std::setprecision(1)
             << total_time_ms / 1000.0 << "s" << endl;
    }
};

static void print_usage(const char* prog) {
    cout << "Usage: " << prog << " [--num N] [--seed S] [--vars V] [--depth D] [--verbose]" << endl;
    cout << "  --num N     Number of iterations (0 = infinite, default)" << endl;
    cout << "  --seed S    Random seed (default: random)" << endl;
    cout << "  --vars V    Max input variables (default: 8)" << endl;
    cout << "  --depth D   Max AIG depth (default: 10)" << endl;
    cout << "  --verbose   Print each AIG before/after" << endl;
}

int main(int argc, char** argv) {
    uint64_t num_iters = 0;
    uint64_t seed = std::random_device{}();
    uint32_t max_vars = 8;
    uint32_t max_depth = 10;
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
    auto t_global_start = std::chrono::steady_clock::now();

    for (uint64_t iter = 0; num_iters == 0 || iter < num_iters; iter++) {
        uint32_t num_vars = 2 + rng() % (max_vars - 1);
        uint32_t depth = 3 + rng() % (max_depth - 2);
        uint32_t max_nodes = 8 + rng() % 40;
        uint32_t test_type = rng() % 4; // 0=rewrite, 1=rewrite_all, 2=simplify_aig, 3=double_rewrite

        if (test_type == 0 || test_type == 3) {
            // Single AIG rewrite (and optionally double-rewrite)
            aig_ptr orig = gen_random_aig(rng, num_vars, depth, max_nodes);
            if (!orig) continue;

            size_t nodes_before = AIG::count_aig_nodes(orig);

            if (verbose) {
                cout << "[" << iter << "] rewrite (" << nodes_before << " nodes, "
                     << num_vars << " vars): " << orig << endl;
            }

            AIGRewriter rw;
            aig_ptr simplified = rw.rewrite(orig);

            if (!verify_rewrite(orig, simplified, num_vars, seed, iter, "rewrite"))
                return 1;

            size_t nodes_after = AIG::count_aig_nodes(simplified);
            stats.rewrite_tests++;

            // Double-rewrite: rewrite the already-rewritten AIG
            if (test_type == 3) {
                AIGRewriter rw2;
                aig_ptr double_simplified = rw2.rewrite(simplified);
                if (!verify_rewrite(orig, double_simplified, num_vars, seed, iter, "double_rewrite"))
                    return 1;

                // Also check the double-rewritten is equivalent to single-rewritten
                if (!verify_rewrite(simplified, double_simplified, num_vars, seed, iter, "double_vs_single"))
                    return 1;

                nodes_after = AIG::count_aig_nodes(double_simplified);
                stats.double_rewrite_tests++;
            }

            stats.nodes_before_total += nodes_before;
            stats.nodes_after_total += nodes_after;
            if (nodes_after < nodes_before) stats.rewrite_reduced++;
            else if (nodes_after == nodes_before) stats.rewrite_same++;
            else stats.rewrite_grew++;

        } else if (test_type == 1) {
            // rewrite_all: multiple AIGs sharing structure
            uint32_t batch_size = 2 + rng() % 4;
            vector<aig_ptr> originals = gen_random_aig_batch(rng, num_vars, batch_size);
            vector<aig_ptr> to_rewrite = originals; // copy

            AIGRewriter rw;
            rw.rewrite_all(to_rewrite, 0);

            size_t total_before = 0, total_after = 0;
            for (uint32_t j = 0; j < batch_size; j++) {
                if (!originals[j] || !to_rewrite[j]) continue;
                if (!verify_rewrite(originals[j], to_rewrite[j], num_vars, seed, iter, "rewrite_all"))
                    return 1;
                total_before += AIG::count_aig_nodes(originals[j]);
                total_after += AIG::count_aig_nodes(to_rewrite[j]);
            }

            stats.rewrite_all_tests++;
            stats.nodes_before_total += total_before;
            stats.nodes_after_total += total_after;

        } else {
            // simplify_aig (the static method)
            aig_ptr orig = gen_random_aig(rng, num_vars, depth, max_nodes);
            if (!orig) continue;

            size_t nodes_before = AIG::count_aig_nodes(orig);
            aig_ptr simplified = AIG::simplify_aig(orig);
            if (!verify_rewrite(orig, simplified, num_vars, seed, iter, "simplify_aig"))
                return 1;

            size_t nodes_after = AIG::count_aig_nodes(simplified);
            stats.simplify_tests++;
            stats.nodes_before_total += nodes_before;
            stats.nodes_after_total += nodes_after;
            if (nodes_after < nodes_before) stats.rewrite_reduced++;
            else if (nodes_after == nodes_before) stats.rewrite_same++;
            else stats.rewrite_grew++;
        }

        stats.total_tests++;

        // Progress output
        if (iter % 500 == 0 && iter > 0) {
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - t_global_start).count();
            cout << "[" << iter << "] All OK ("
                 << std::fixed << std::setprecision(0) << iter / elapsed << " iter/s). "
                 << "Avg nodes: " << std::setprecision(1)
                 << (double)stats.nodes_before_total / stats.total_tests
                 << " -> "
                 << (double)stats.nodes_after_total / stats.total_tests
                 << "  reduced:" << stats.rewrite_reduced
                 << " same:" << stats.rewrite_same
                 << " grew:" << stats.rewrite_grew
                 << endl;
        } else if (iter < 10) {
            size_t nb = stats.nodes_before_total;
            size_t na = stats.nodes_after_total;
            cout << "[" << iter << "] OK" << endl;
            (void)nb; (void)na;
        }
    }

    auto now = std::chrono::steady_clock::now();
    stats.total_time_ms = std::chrono::duration<double, std::milli>(now - t_global_start).count();
    stats.print();
    cout << "\nAll " << stats.total_tests << " tests passed!" << endl;
    return 0;
}
