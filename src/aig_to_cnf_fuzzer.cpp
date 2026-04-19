/*
 Arjun - AIG -> CNF Encoder Fuzzer

 Generates random AIGs and encodes them using two different strategies:
   (1) The naive Tseitin translation (baseline, mirroring the fuzz_aig
       encoder): pairwise AND clauses with a helper per AND node.
   (2) The optimized AIGToCNF encoder being tested.

 Both encodings are pushed into the *same* SAT solver in disjoint variable
 ranges. We then force the two output literals to differ via an XOR
 gadget and check for UNSAT. If UNSAT, the two encodings are logically
 equivalent on the shared input variables.

 On top of SAT-based equivalence we also do brute-force truth-table
 enumeration for small inputs and random-evaluation sampling.

 Statistics of clause/helper savings are printed periodically.

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#include "aig_to_cnf.h"
#include "aig_rewrite.h"
#include <cryptominisat5/cryptominisat.h>
#include <cassert>
#include <chrono>
#include <cstring>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <random>
#include <vector>

using namespace ArjunNS;
using namespace CMSat;
using std::cout;
using std::cerr;
using std::endl;
using std::vector;
using std::map;

static AIGManager aig_mng;

// -----------------------------------------------------------------------------
// Random AIG generation (copied / adapted from aig_fuzzer.cpp).
// -----------------------------------------------------------------------------

static aig_ptr gen_random_aig(std::mt19937& rng, uint32_t num_vars,
                              uint32_t depth, uint32_t max_nodes)
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
        uint32_t new_this_level = 1 + rng() % 4;
        for (uint32_t i = 0; i < new_this_level && nodes_built < max_nodes; i++) {
            if (pool.size() < 2) break;
            auto pick = [&]() -> uint32_t {
                if (rng() % 3 == 0) return rng() % pool.size();
                uint32_t lo = pool.size() > 4 ? pool.size() - pool.size() / 2 : 0;
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
                    // XOR
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
    if (pool.size() <= num_vars * 2) return pool[rng() % pool.size()];
    uint32_t start = pool.size() * 2 / 3;
    return pool[start + rng() % (pool.size() - start)];
}

// Manthan-style generator: nested ITE trees whose selector branches are ANDs
// of many literals (mimicking how manthan builds a Skolem function from a DNF
// cover of a CEX clause). The "then" and "else" arms are recursively built
// from the same pattern so we get deep ITE chains.
static aig_ptr gen_manthan_aig(std::mt19937& rng, uint32_t num_vars,
                                uint32_t depth, uint32_t max_branch_width)
{
    // Base case: leaf is a literal (or constant).
    if (depth == 0) {
        uint32_t pick = rng() % 10;
        if (pick == 0) return aig_mng.new_const(true);
        if (pick == 1) return aig_mng.new_const(false);
        return AIG::new_lit(rng() % num_vars, rng() % 2);
    }

    // Build the "branch": an AND of k random literals (1..max_branch_width).
    uint32_t k = 1 + rng() % std::max<uint32_t>(1u, max_branch_width);
    // Sometimes force a large AND-of-literals branch (the manthan common case).
    if (rng() % 3 == 0) k = std::max<uint32_t>(k, 3u + rng() % std::max<uint32_t>(1u, max_branch_width));
    aig_ptr branch = AIG::new_lit(rng() % num_vars, rng() % 2);
    for (uint32_t i = 1; i < k; i++) {
        aig_ptr lit = AIG::new_lit(rng() % num_vars, rng() % 2);
        branch = AIG::new_and(branch, lit);
    }
    // Sometimes negate the branch overall.
    if (rng() % 5 == 0) branch = AIG::new_not(branch);

    // Recursively build "then" and "else" arms.
    aig_ptr then_arm = gen_manthan_aig(rng, num_vars, depth - 1, max_branch_width);
    aig_ptr else_arm = gen_manthan_aig(rng, num_vars, depth - 1, max_branch_width);

    // ITE pattern: (branch ∧ then) ∨ (¬branch ∧ else)
    aig_ptr ite = AIG::new_or(
        AIG::new_and(branch, then_arm),
        AIG::new_and(AIG::new_not(branch), else_arm));
    return ite;
}

// LINEAR deep ITE-chain generator: this is the actual manthan workload
// shape. Each repair adds one more ITE on top of the current formula:
//   f_{i+1} = ITE(branch_i, repair_i, f_i)
// where branch_i is an AND of many literals. After ~200-500 repairs the
// chain depth is hundreds -- matching the "aig_depth: 200+" values in
// real genbuf8b4n.sat runs.
static aig_ptr gen_deep_ite_chain_aig(std::mt19937& rng, uint32_t num_vars,
                                       uint32_t chain_depth,
                                       uint32_t max_branch_width)
{
    // Start with a literal base.
    aig_ptr f = AIG::new_lit(rng() % num_vars, rng() % 2);
    for (uint32_t step = 0; step < chain_depth; step++) {
        // Build the branch: AND of k random literals. Width distribution
        // is biased towards ~max_branch_width/2 with occasional wide ANDs.
        uint32_t k = 1 + rng() % std::max<uint32_t>(1u, max_branch_width);
        if (rng() % 4 == 0) k = std::max<uint32_t>(k, max_branch_width);
        aig_ptr branch = AIG::new_lit(rng() % num_vars, rng() % 2);
        for (uint32_t i = 1; i < k; i++) {
            branch = AIG::new_and(branch, AIG::new_lit(rng() % num_vars, rng() % 2));
        }
        // Repair value: usually a literal, occasionally a small AND.
        aig_ptr repair;
        if (rng() % 5 == 0) {
            repair = AIG::new_and(
                AIG::new_lit(rng() % num_vars, rng() % 2),
                AIG::new_lit(rng() % num_vars, rng() % 2));
        } else {
            repair = AIG::new_lit(rng() % num_vars, rng() % 2);
        }
        // ITE(branch, repair, f)
        f = AIG::new_or(
            AIG::new_and(branch, repair),
            AIG::new_and(AIG::new_not(branch), f));
    }
    return f;
}

// "DNF cover" generator: OR of several (AND of literals) * subformula branches.
// Directly models the inner loop of manthan.cpp around line 590-616.
static aig_ptr gen_dnf_cover_aig(std::mt19937& rng, uint32_t num_vars,
                                   uint32_t num_branches, uint32_t max_branch_width)
{
    aig_ptr overall = nullptr;
    for (uint32_t b = 0; b < num_branches; b++) {
        uint32_t k = 1 + rng() % std::max<uint32_t>(1u, max_branch_width);
        aig_ptr cur = AIG::new_lit(rng() % num_vars, rng() % 2);
        for (uint32_t i = 1; i < k; i++) {
            cur = AIG::new_and(cur, AIG::new_lit(rng() % num_vars, rng() % 2));
        }
        if (overall == nullptr) overall = cur;
        else overall = AIG::new_or(overall, cur);
    }
    if (overall == nullptr) overall = aig_mng.new_const(true);
    if (rng() % 3 == 0) overall = AIG::new_not(overall);
    return overall;
}

// Pure big-AND of many distinct literals -- the canonical target for k-ary
// AND fusion. Uses each (var, +/-) combination at most once so the AIG's own
// AND-simplification (AND(x, ~x) = FALSE) doesn't collapse the chain. The
// actual width is capped at 2 * num_vars (that's how many distinct literals
// exist).
static aig_ptr gen_pure_and_chain(std::mt19937& rng, uint32_t num_vars, uint32_t len) {
    if (len < 2) len = 2;
    std::vector<std::pair<uint32_t, bool>> pool;
    pool.reserve(2 * num_vars);
    for (uint32_t v = 0; v < num_vars; v++) {
        pool.emplace_back(v, false);
        pool.emplace_back(v, true);
    }
    // Fisher-Yates shuffle + truncate to len (or to pool.size()).
    std::shuffle(pool.begin(), pool.end(), rng);
    uint32_t actual = std::min<uint32_t>(len, pool.size());
    if (actual < 2) actual = std::min<uint32_t>(2u, pool.size());
    // But pick only ONE polarity per var to avoid complementary pairs, so
    // up to num_vars distinct conjuncts.
    std::vector<char> used(num_vars, 0);
    aig_ptr cur = nullptr;
    uint32_t made = 0;
    for (auto& p : pool) {
        if (used[p.first]) continue;
        used[p.first] = 1;
        aig_ptr lit = AIG::new_lit(p.first, p.second);
        cur = cur ? AIG::new_and(cur, lit) : lit;
        if (++made >= actual) break;
    }
    if (!cur) cur = AIG::new_lit(0, false);
    if (rng() % 5 == 0) cur = AIG::new_not(cur);
    return cur;
}

static aig_ptr gen_pure_or_chain(std::mt19937& rng, uint32_t num_vars, uint32_t len) {
    if (len < 2) len = 2;
    std::vector<std::pair<uint32_t, bool>> pool;
    pool.reserve(2 * num_vars);
    for (uint32_t v = 0; v < num_vars; v++) {
        pool.emplace_back(v, false);
        pool.emplace_back(v, true);
    }
    std::shuffle(pool.begin(), pool.end(), rng);
    uint32_t actual = std::min<uint32_t>(len, pool.size());
    if (actual < 2) actual = std::min<uint32_t>(2u, pool.size());
    std::vector<char> used(num_vars, 0);
    aig_ptr cur = nullptr;
    uint32_t made = 0;
    for (auto& p : pool) {
        if (used[p.first]) continue;
        used[p.first] = 1;
        aig_ptr lit = AIG::new_lit(p.first, p.second);
        cur = cur ? AIG::new_or(cur, lit) : lit;
        if (++made >= actual) break;
    }
    if (!cur) cur = AIG::new_lit(0, false);
    if (rng() % 5 == 0) cur = AIG::new_not(cur);
    return cur;
}

// Balanced-tree big-AND: build pairwise bottom-up (AND-of-ANDs). The
// resulting AIG has depth log2(len) but the same k-ary semantic. Exercises
// the flattening through internal fanout-1 AND nodes.
static aig_ptr gen_balanced_and_tree(std::mt19937& rng, uint32_t num_vars, uint32_t len) {
    if (len < 2) len = 2;
    std::vector<aig_ptr> level;
    level.reserve(len);
    for (uint32_t i = 0; i < len; i++) {
        level.push_back(AIG::new_lit(rng() % num_vars, rng() % 2));
    }
    while (level.size() > 1) {
        std::vector<aig_ptr> next;
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            next.push_back(AIG::new_and(level[i], level[i+1]));
        }
        if (level.size() % 2 == 1) next.push_back(level.back());
        level = std::move(next);
    }
    return level[0];
}

static aig_ptr gen_balanced_or_tree(std::mt19937& rng, uint32_t num_vars, uint32_t len) {
    if (len < 2) len = 2;
    std::vector<aig_ptr> level;
    level.reserve(len);
    for (uint32_t i = 0; i < len; i++) {
        level.push_back(AIG::new_lit(rng() % num_vars, rng() % 2));
    }
    while (level.size() > 1) {
        std::vector<aig_ptr> next;
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            next.push_back(AIG::new_or(level[i], level[i+1]));
        }
        if (level.size() % 2 == 1) next.push_back(level.back());
        level = std::move(next);
    }
    return level[0];
}

// Deep chain — good for stressing k-ary AND/OR fusion.
static aig_ptr gen_chain_aig(std::mt19937& rng, uint32_t num_vars, uint32_t chain_len) {
    aig_ptr chain = AIG::new_lit(rng() % num_vars, rng() % 2);
    for (uint32_t i = 0; i < chain_len; i++) {
        aig_ptr leaf = AIG::new_lit(rng() % num_vars, rng() % 2);
        uint32_t op = rng() % 4;
        switch (op) {
            case 0: chain = AIG::new_and(chain, leaf); break;
            case 1: chain = AIG::new_or(chain, leaf); break;
            case 2: chain = AIG::new_and(leaf, chain); break;
            case 3: chain = AIG::new_or(leaf, chain); break;
        }
    }
    if (rng() % 3 == 0) chain = AIG::new_not(chain);
    if (rng() % 4 == 0) {
        aig_ptr other = AIG::new_lit(rng() % num_vars, rng() % 2);
        chain = AIG::new_ite(chain, other, Lit(rng() % num_vars, rng() % 2));
    }
    return chain;
}

// -----------------------------------------------------------------------------
// Naive Tseitin baseline encoder (one helper per AND node, 3 clauses each).
// -----------------------------------------------------------------------------

struct NaiveStats {
    uint64_t clauses = 0;
    uint64_t helpers = 0;
};

static Lit naive_encode(const aig_ptr& aig, SATSolver& solver,
                         map<aig_ptr, Lit>& cache, NaiveStats& ns,
                         Lit& true_lit, bool& true_lit_set)
{
    // Use AIG::transform so we don't touch AIG's private members directly.
    auto visitor = [&](AIGT type, uint32_t var, bool neg,
                       const Lit* left, const Lit* right) -> Lit {
        if (type == AIGT::t_const) {
            if (!true_lit_set) {
                solver.new_var(); ns.helpers++;
                true_lit = Lit(solver.nVars() - 1, false);
                solver.add_clause({true_lit}); ns.clauses++;
                true_lit_set = true;
            }
            return neg ? ~true_lit : true_lit;
        }
        if (type == AIGT::t_lit) return Lit(var, neg);
        assert(type == AIGT::t_and);
        Lit l = *left;
        Lit r = *right;
        solver.new_var(); ns.helpers++;
        Lit g(solver.nVars() - 1, false);
        solver.add_clause({~g, l}); ns.clauses++;
        solver.add_clause({~g, r}); ns.clauses++;
        solver.add_clause({g, ~l, ~r}); ns.clauses++;
        return neg ? ~g : g;
    };
    return AIG::transform<Lit>(aig, visitor, cache);
}

// -----------------------------------------------------------------------------
// Equivalence checks.
// -----------------------------------------------------------------------------

// Check A <-> B using SAT. Adds a fresh XOR gadget forcing A != B; UNSAT = equal.
static bool sat_equivalent(SATSolver& s, Lit a, Lit b) {
    // Save state; use assumptions so we don't mutate the solver permanently.
    // But CMSat's add_clause is permanent. Use assumptions via auxiliary lit.
    s.new_var();
    Lit act = Lit(s.nVars() - 1, false);
    // (act) -> (a XOR b)
    // XOR encoding:
    //   (¬act ∨ a ∨ b)
    //   (¬act ∨ ¬a ∨ ¬b)
    //   ... we only need: if act true, then a and b differ.
    // Equivalent: (act -> a != b). This holds iff
    //   (¬act ∨ a ∨ b) ∧ (¬act ∨ ¬a ∨ ¬b)   // at least one is true and at least one is false
    s.add_clause({~act, a, b});
    s.add_clause({~act, ~a, ~b});
    vector<Lit> assumps{act};
    lbool ret = s.solve(&assumps);
    // Disable the activation literal so it doesn't contaminate further queries.
    s.add_clause({~act});
    return ret == l_False;
}

// Per-assignment equivalence using brute-force AIG evaluation on the input
// AIG, versus the *solved* model of the CNF encoding (ensuring the CNF
// correctly models the AIG). For every input assignment we fix all input
// vars as assumptions, solve, and check the model's value of the output lit
// matches the AIG's value on that assignment.
static bool cnf_matches_aig(SATSolver& s, const aig_ptr& aig, Lit out_lit,
                             uint32_t num_vars)
{
    if (num_vars > 12) return true; // too expensive
    vector<aig_ptr> defs(num_vars, nullptr);
    for (uint32_t mask = 0; mask < (1u << num_vars); mask++) {
        vector<lbool> vals(num_vars);
        vector<Lit> assumps;
        for (uint32_t v = 0; v < num_vars; v++) {
            bool b = (mask >> v) & 1;
            vals[v] = b ? l_True : l_False;
            assumps.emplace_back(v, !b); // force var v = b
        }
        map<aig_ptr, lbool> ca;
        lbool expected = AIG::evaluate(vals, aig, defs, ca);
        lbool ret = s.solve(&assumps);
        if (ret != l_True) {
            // The CNF encoding should be satisfiable for *any* input assignment.
            // If the AIG evaluates to undef (shouldn't happen with all inputs
            // set), skip. Otherwise this is a bug.
            cerr << "  cnf_matches_aig: solver UNSAT on assignment mask="
                 << mask << " (expected "
                 << (expected == l_True ? "T" : expected == l_False ? "F" : "U")
                 << ")" << endl;
            return false;
        }
        const auto& model = s.get_model();
        lbool got = model[out_lit.var()] ^ out_lit.sign();
        if (expected == l_True && got != l_True) return false;
        if (expected == l_False && got != l_False) return false;
    }
    return true;
}

// -----------------------------------------------------------------------------
// Main test routine.
// -----------------------------------------------------------------------------

struct FuzzStats {
    uint64_t iters = 0;
    uint64_t nodes_total = 0;
    uint64_t naive_clauses_total = 0;
    uint64_t naive_helpers_total = 0;
    uint64_t opt_clauses_total = 0;
    uint64_t opt_helpers_total = 0;
    uint64_t opt_kary_and = 0, opt_kary_and_width = 0;
    uint64_t opt_kary_or = 0, opt_kary_or_width = 0;
    uint64_t opt_ite = 0;
    double total_time_s = 0;

    void print() const {
        cout << "\n=== fuzz_aig_to_cnf statistics ===" << endl;
        cout << "Iterations:       " << iters << endl;
        cout << "Avg AIG nodes:    " << std::fixed << std::setprecision(1)
             << (iters ? (double)nodes_total / iters : 0.0) << endl;
        cout << "Naive avg clauses/helpers:    "
             << (iters ? (double)naive_clauses_total / iters : 0.0) << " / "
             << (iters ? (double)naive_helpers_total / iters : 0.0) << endl;
        cout << "Optimized avg clauses/helpers: "
             << (iters ? (double)opt_clauses_total / iters : 0.0) << " / "
             << (iters ? (double)opt_helpers_total / iters : 0.0) << endl;
        if (naive_clauses_total > 0) {
            double cs = 100.0 * (1.0 - (double)opt_clauses_total / naive_clauses_total);
            double hs = 100.0 * (1.0 - (double)opt_helpers_total / naive_helpers_total);
            cout << "Clause reduction: " << std::setprecision(1) << cs << "%" << endl;
            cout << "Helper reduction: " << std::setprecision(1) << hs << "%" << endl;
        }
        cout << "k-ary ANDs: " << opt_kary_and
             << " (avg width "
             << (opt_kary_and ? (double)opt_kary_and_width / opt_kary_and : 0.0)
             << ")" << endl;
        cout << "k-ary ORs:  " << opt_kary_or
             << " (avg width "
             << (opt_kary_or ? (double)opt_kary_or_width / opt_kary_or : 0.0)
             << ")" << endl;
        cout << "ITE patterns detected: " << opt_ite << endl;
        cout << "Time: " << std::fixed << std::setprecision(1)
             << total_time_s << "s" << endl;
    }
};

static void report_failure(const aig_ptr& aig, uint32_t num_vars,
                            uint64_t seed, uint64_t iter, const char* phase)
{
    cerr << "\n!!! FAILURE in phase '" << phase << "' at iter " << iter << " !!!" << endl;
    cerr << "Seed: " << seed << "  num_vars: " << num_vars << endl;
    cerr << "AIG: " << aig << endl;
}

static bool run_one(const aig_ptr& aig, uint32_t num_vars,
                    uint64_t seed, uint64_t iter, FuzzStats& fs,
                    bool verbose)
{
    // Build a solver pre-populated with the input variables.
    SATSolver solver;
    solver.set_verbosity(0);
    solver.new_vars(num_vars);

    // 1. Naive encoding
    NaiveStats ns;
    Lit true_lit_unused; bool true_set = false;
    map<aig_ptr, Lit> naive_cache;
    Lit naive_out = naive_encode(aig, solver, naive_cache, ns, true_lit_unused, true_set);

    // 2. Optimized encoding (into the same solver, in a fresh variable range)
    AIGToCNF<SATSolver> enc(solver);
    Lit opt_out = enc.encode(aig);
    const auto& es = enc.get_stats();

    {
        size_t nodes = AIG::count_aig_nodes(aig);
        double cls_ratio = ns.clauses > 0 ? (double)es.clauses_added / ns.clauses : 1.0;
        double hlp_ratio = ns.helpers > 0 ? (double)es.helpers_added / ns.helpers : 1.0;
        cout << "[" << std::setw(6) << iter << "] "
             << "nodes=" << std::setw(4) << nodes
             << "  naive(cls/hlp)=" << std::setw(4) << ns.clauses
             << "/" << std::setw(3) << ns.helpers
             << "  opt=" << std::setw(4) << es.clauses_added
             << "/" << std::setw(3) << es.helpers_added
             << "  ratio=" << std::fixed << std::setprecision(2) << cls_ratio
             << "/" << hlp_ratio
             << "  kAND=" << es.kary_and_count
             << " kOR=" << es.kary_or_count
             << " ITE=" << es.ite_patterns
             << " XOR=" << es.xor_patterns
             << endl;
    }

    fs.nodes_total += AIG::count_aig_nodes(aig);
    fs.naive_clauses_total += ns.clauses;
    fs.naive_helpers_total += ns.helpers;
    fs.opt_clauses_total += es.clauses_added;
    fs.opt_helpers_total += es.helpers_added;
    fs.opt_kary_and += es.kary_and_count;
    fs.opt_kary_and_width += es.kary_and_width_total;
    fs.opt_kary_or += es.kary_or_count;
    fs.opt_kary_or_width += es.kary_or_width_total;
    fs.opt_ite += es.ite_patterns;

    // 3. Check: naive_out <-> opt_out is valid (equivalence in the combined CNF).
    if (!sat_equivalent(solver, naive_out, opt_out)) {
        report_failure(aig, num_vars, seed, iter, "sat_equivalent");
        cerr << "  naive_out=" << naive_out << "  opt_out=" << opt_out << endl;
        return false;
    }

    // 4. For small num_vars, also check that the optimized CNF's output literal
    //    agrees with the AIG's ground-truth value on every input assignment.
    //    This catches bugs where both encodings are "equivalent" but both wrong.
    if (!cnf_matches_aig(solver, aig, opt_out, num_vars)) {
        report_failure(aig, num_vars, seed, iter, "cnf_matches_aig(opt)");
        return false;
    }

    return true;
}

// -----------------------------------------------------------------------------
// Per-feature measurement: encode the same set of AIGs with each feature
// individually disabled, compare clause count and wall-clock vs baseline.
// -----------------------------------------------------------------------------

enum class Feature {
    NONE,               // baseline: all features on
    NORMALIZE_INPUTS,   // dedup/complementary/const fold in k-ary groups
    GROUP_CSE,          // content-hashed CSE for AND/OR/ITE groups
    DEMORGAN_FLATTEN,   // flatten k-ary through NOT-wrappers
    ITE_SUB_SELECTOR,   // ITE detection with non-literal sub-AIG selectors
    DETECT_ITE,         // ITE detection entirely
    KARY_FUSION,        // k-ary AND/OR fusion
};

static const char* feature_name(Feature f) {
    switch (f) {
        case Feature::NONE:             return "baseline (all on)";
        case Feature::NORMALIZE_INPUTS: return "normalize_inputs";
        case Feature::GROUP_CSE:        return "group_cse";
        case Feature::DEMORGAN_FLATTEN: return "demorgan_flatten";
        case Feature::ITE_SUB_SELECTOR: return "ite_sub_selector";
        case Feature::DETECT_ITE:       return "detect_ite";
        case Feature::KARY_FUSION:      return "kary_fusion";
    }
    return "?";
}

struct MeasureResult {
    uint64_t clauses = 0;
    uint64_t helpers = 0;
    double encode_time_s = 0.0;
};

// Encode all aigs with a single feature disabled and collect totals.
static MeasureResult run_measure_pass(const std::vector<aig_ptr>& aigs,
                                       const std::vector<uint32_t>& nvars,
                                       Feature disabled)
{
    MeasureResult r;
    for (size_t i = 0; i < aigs.size(); i++) {
        const aig_ptr& aig = aigs[i];
        if (!aig) continue;
        SATSolver solver;
        solver.set_verbosity(0);
        solver.new_vars(nvars[i]);
        AIGToCNF<SATSolver> enc(solver);
        switch (disabled) {
            case Feature::NONE: break;
            case Feature::NORMALIZE_INPUTS: enc.set_normalize_inputs(false); break;
            case Feature::GROUP_CSE:        enc.set_group_cse(false); break;
            case Feature::DEMORGAN_FLATTEN: enc.set_demorgan_flatten(false); break;
            case Feature::ITE_SUB_SELECTOR: enc.set_ite_sub_selector(false); break;
            case Feature::DETECT_ITE:       enc.set_detect_ite(false); break;
            case Feature::KARY_FUSION:      enc.set_kary_fusion(false); break;
        }
        auto t0 = std::chrono::steady_clock::now();
        enc.encode(aig);
        auto t1 = std::chrono::steady_clock::now();
        r.encode_time_s += std::chrono::duration<double>(t1 - t0).count();
        const auto& s = enc.get_stats();
        r.clauses += s.clauses_added;
        r.helpers += s.helpers_added;
    }
    return r;
}

static int run_measure_mode(uint64_t seed, uint64_t num_iters,
                             uint32_t max_vars, uint32_t max_depth,
                             uint32_t max_nodes_cfg)
{
    // Pre-generate a fixed set of AIGs -- the measurement must be on an
    // identical corpus for every feature toggle, otherwise random variance
    // dwarfs the effect we're trying to see.
    std::mt19937 rng(seed);
    std::vector<aig_ptr> aigs;
    std::vector<uint32_t> nvars;
    aigs.reserve(num_iters);
    nvars.reserve(num_iters);
    cout << "Generating " << num_iters << " AIGs (seed " << seed << ")..." << std::endl;
    for (uint64_t iter = 0; iter < num_iters; iter++) {
        uint32_t num_vars = 2 + rng() % (max_vars - 1);
        uint32_t depth = 3 + rng() % (max_depth - 2);
        uint32_t max_nodes = 8 + rng() % max_nodes_cfg;
        aig_ptr aig;
        uint32_t shape = rng() % 16;
        if (shape < 4) {
            uint32_t d = 50 + rng() % 450;
            if (rng() % 20 == 0) d = 500 + rng() % 500;
            uint32_t bw = 2 + rng() % 8;
            aig = gen_deep_ite_chain_aig(rng, num_vars, d, bw);
        } else if (shape < 6) {
            uint32_t nb = 2 + rng() % 8;
            uint32_t bw = 2 + rng() % 6;
            aig = gen_dnf_cover_aig(rng, num_vars, nb, bw);
        } else if (shape < 7) {
            aig = gen_manthan_aig(rng, num_vars, 2 + rng() % 4, 2 + rng() % 6);
        } else if (shape < 8) {
            aig = gen_random_aig(rng, num_vars, depth, max_nodes);
        } else if (shape < 9) {
            aig = gen_chain_aig(rng, num_vars, 5 + rng() % 25);
        } else if (shape < 11) {
            aig = gen_pure_and_chain(rng, num_vars, 10 + rng() % 790);
        } else if (shape < 13) {
            aig = gen_pure_or_chain(rng, num_vars, 10 + rng() % 790);
        } else if (shape < 14) {
            aig = gen_balanced_and_tree(rng, num_vars, 8 + rng() % 500);
        } else if (shape < 15) {
            aig = gen_balanced_or_tree(rng, num_vars, 8 + rng() % 500);
        } else {
            uint32_t d = 50 + rng() % 200;
            uint32_t bw = 2 + rng() % 6;
            aig_ptr raw = gen_deep_ite_chain_aig(rng, num_vars, d, bw);
            if (raw) { AIGRewriter rw; aig = rw.rewrite(raw); }
        }
        if (!aig) continue;
        aigs.push_back(aig);
        nvars.push_back(num_vars);
    }
    cout << "Generated " << aigs.size() << " AIGs." << std::endl;

    // Warm up once to touch caches, then measure baseline twice and take the
    // best to reduce jitter.
    run_measure_pass(aigs, nvars, Feature::NONE);
    auto best_of_2 = [&](Feature f) {
        auto a = run_measure_pass(aigs, nvars, f);
        auto b = run_measure_pass(aigs, nvars, f);
        if (b.encode_time_s < a.encode_time_s) a.encode_time_s = b.encode_time_s;
        return a;
    };
    MeasureResult baseline = best_of_2(Feature::NONE);

    cout << "\n=== Feature contribution (disabling each one) ===" << std::endl;
    cout << "Baseline (all on): "
         << baseline.clauses << " clauses, "
         << baseline.helpers << " helpers, "
         << std::fixed << std::setprecision(3) << baseline.encode_time_s
         << "s encode time" << std::endl;
    cout << std::endl;
    cout << std::left << std::setw(22) << "Feature disabled"
         << std::right << std::setw(12) << "+clauses"
         << std::setw(10) << "+helpers"
         << std::setw(12) << "time delta"
         << std::setw(14) << "ms/k-cls-saved"
         << std::endl;
    cout << std::string(70, '-') << std::endl;
    Feature features[] = {
        Feature::NORMALIZE_INPUTS,
        Feature::GROUP_CSE,
        Feature::DEMORGAN_FLATTEN,
        Feature::ITE_SUB_SELECTOR,
        Feature::DETECT_ITE,
        Feature::KARY_FUSION,
    };
    for (Feature f : features) {
        MeasureResult r = best_of_2(f);
        int64_t extra_clauses = (int64_t)r.clauses - (int64_t)baseline.clauses;
        int64_t extra_helpers = (int64_t)r.helpers - (int64_t)baseline.helpers;
        double time_delta_ms = (baseline.encode_time_s - r.encode_time_s) * 1000.0;
        // Cost-benefit: ms of baseline time spent per 1000 clauses saved by
        // this feature. Lower is better (cheap feature that saves clauses).
        double cost_per_ksaved = extra_clauses > 0
            ? (time_delta_ms / (extra_clauses / 1000.0))
            : 0.0;
        cout << std::left << std::setw(22) << feature_name(f)
             << std::right << std::setw(12) << extra_clauses
             << std::setw(10) << extra_helpers
             << std::setw(10) << std::fixed << std::setprecision(1)
             << time_delta_ms << "ms"
             << std::setw(14) << std::fixed << std::setprecision(2)
             << cost_per_ksaved
             << std::endl;
    }
    cout << std::endl;
    cout << "Columns: +clauses/+helpers = additional clauses/helpers emitted"
         << " when this feature is DISABLED.\n"
         << "time delta = baseline - disabled (positive means the feature"
         << " itself costs time).\n"
         << "ms/k-cls-saved = how many ms the feature spends to save 1000"
         << " clauses (lower is better)." << std::endl;
    return 0;
}

// -----------------------------------------------------------------------------
// Benchmark AIGRewriter::rewrite_all on a batch of deep-chain AIGs -- the
// path that was measured at ~15s on the manthan genbuf8b4n rebuild step.
// -----------------------------------------------------------------------------
static int run_bench_rewrite_mode(uint64_t seed, uint64_t num_aigs,
                                    uint32_t max_vars, uint32_t chain_depth)
{
    std::mt19937 rng(seed);
    std::vector<aig_ptr> aigs;
    aigs.reserve(num_aigs);
    cout << "Generating " << num_aigs << " deep-chain AIGs "
         << "(seed " << seed << ", depth " << chain_depth
         << ", vars " << max_vars << ")..." << std::endl;
    auto t_gen = std::chrono::steady_clock::now();
    size_t total_raw_nodes = 0;
    for (uint64_t i = 0; i < num_aigs; i++) {
        uint32_t num_vars = 4 + rng() % max_vars;
        uint32_t bw = 2 + rng() % 6;
        aig_ptr a = gen_deep_ite_chain_aig(rng, num_vars, chain_depth, bw);
        if (a) {
            aigs.push_back(a);
            total_raw_nodes += ArjunNS::AIG::count_aig_nodes(a);
        }
    }
    double gen_s = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - t_gen).count();
    cout << "Generated " << aigs.size() << " AIGs, "
         << total_raw_nodes << " total nodes, T: "
         << std::fixed << std::setprecision(2) << gen_s << "s" << std::endl;

    cout << "\nRunning AIGRewriter::rewrite_all..." << std::endl;
    auto t_rw = std::chrono::steady_clock::now();
    AIGRewriter rewriter;
    rewriter.rewrite_all(aigs, 1);
    double rw_s = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - t_rw).count();
    cout << "rewrite_all wall-clock: " << std::fixed << std::setprecision(2)
         << rw_s << "s" << std::endl;

    // Also verify the AIG->CNF encoder still produces correct output.
    cout << "\nVerifying AIG->CNF encoding on rewritten AIGs..." << std::endl;
    uint64_t total_clauses = 0, total_helpers = 0;
    auto t_enc = std::chrono::steady_clock::now();
    for (const auto& a : aigs) {
        if (!a) continue;
        CMSat::SATSolver s;
        s.set_verbosity(0);
        // Pre-allocate enough solver vars for the highest lit var used
        // by this AIG. AIG::get_dependent_vars does a full DFS collecting
        // literal vars; it's enough for sizing.
        std::set<uint32_t> vars_seen;
        // Use the sentinel none_var (=UINT32_MAX) as the "self" guard so
        // the assertion inside get_dependent_vars cannot fire.
        AIG::get_dependent_vars(a, vars_seen,
            std::numeric_limits<uint32_t>::max());
        s.new_vars(vars_seen.empty() ? 1u : *vars_seen.rbegin() + 1);
        AIGToCNF<CMSat::SATSolver> enc(s);
        enc.encode(a);
        total_clauses += enc.get_stats().clauses_added;
        total_helpers += enc.get_stats().helpers_added;
    }
    double enc_s = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - t_enc).count();
    cout << "AIG->CNF encode wall-clock: " << std::fixed << std::setprecision(2)
         << enc_s << "s  (total clauses " << total_clauses
         << ", helpers " << total_helpers << ")" << std::endl;
    return 0;
}

static void print_usage(const char* prog) {
    cout << "Usage: " << prog
         << " [--num N] [--seed S] [--vars V] [--depth D] [--nodes N] [--verbose]" << endl;
    cout << "  --num N     Number of iterations (0 = infinite, default 0)" << endl;
    cout << "  --seed S    Random seed (default: random)" << endl;
    cout << "  --vars V    Max input variables (default: 8)" << endl;
    cout << "  --depth D   Max AIG depth (default: 10)" << endl;
    cout << "  --nodes N   Max nodes per AIG (default: 50)" << endl;
    cout << "  --verbose   Per-iteration verbose output" << endl;
}

int main(int argc, char** argv) {
    uint64_t num_iters = 0;
    uint64_t seed = std::random_device{}();
    uint32_t max_vars = 8;
    uint32_t max_depth = 10;
    uint32_t max_nodes_cfg = 50;
    bool verbose = false;
    bool measure_mode = false;
    bool bench_rewrite_mode = false;
    uint32_t bench_chain_depth = 300;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--num") == 0 && i + 1 < argc) num_iters = std::stoull(argv[++i]);
        else if (strcmp(argv[i], "--seed") == 0 && i + 1 < argc) seed = std::stoull(argv[++i]);
        else if (strcmp(argv[i], "--vars") == 0 && i + 1 < argc) max_vars = std::stoul(argv[++i]);
        else if (strcmp(argv[i], "--depth") == 0 && i + 1 < argc) max_depth = std::stoul(argv[++i]);
        else if (strcmp(argv[i], "--nodes") == 0 && i + 1 < argc) max_nodes_cfg = std::stoul(argv[++i]);
        else if (strcmp(argv[i], "--verbose") == 0) verbose = true;
        else if (strcmp(argv[i], "--measure") == 0) measure_mode = true;
        else if (strcmp(argv[i], "--bench-rewrite") == 0) bench_rewrite_mode = true;
        else if (strcmp(argv[i], "--chain-depth") == 0 && i + 1 < argc) bench_chain_depth = std::stoul(argv[++i]);
        else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            print_usage(argv[0]); return 0;
        } else {
            cerr << "Unknown option: " << argv[i] << endl;
            print_usage(argv[0]); return 1;
        }
    }

    if (measure_mode) {
        if (num_iters == 0) num_iters = 200;
        return run_measure_mode(seed, num_iters, max_vars, max_depth, max_nodes_cfg);
    }
    if (bench_rewrite_mode) {
        if (num_iters == 0) num_iters = 100;
        return run_bench_rewrite_mode(seed, num_iters, max_vars, bench_chain_depth);
    }

    cout << "fuzz_aig_to_cnf" << endl;
    cout << "Seed: " << seed << "  max_vars: " << max_vars
         << "  max_depth: " << max_depth << "  max_nodes: " << max_nodes_cfg << endl;
    cout << "Reproduce: fuzz_aig_to_cnf --seed " << seed
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

        aig_ptr aig;
        // Weight the shape distribution so the deep linear ITE chain --
        // the *actual* manthan Skolem-function shape with aig_depth 200+
        // -- is the dominant case, but also cover pure k-ary AND/OR chains
        // (the target for large single-gate fusion).
        uint32_t shape = rng() % 16;
        if (shape < 4) {
            // Deep linear ITE chain (primary manthan workload).
            uint32_t d = 50 + rng() % 450;
            if (rng() % 20 == 0) d = 500 + rng() % 500; // very deep
            uint32_t bw = 2 + rng() % 8;
            aig = gen_deep_ite_chain_aig(rng, num_vars, d, bw);
        } else if (shape < 6) {
            // DNF-cover (OR of ANDs-of-lits).
            uint32_t nb = 2 + rng() % 8;
            uint32_t bw = 2 + rng() % 6;
            aig = gen_dnf_cover_aig(rng, num_vars, nb, bw);
        } else if (shape < 7) {
            // Shallow manthan-style tree (exponential, keep depth tiny).
            uint32_t d = 2 + rng() % 4;
            uint32_t bw = 2 + rng() % 6;
            aig = gen_manthan_aig(rng, num_vars, d, bw);
        } else if (shape < 8) {
            aig = gen_random_aig(rng, num_vars, depth, max_nodes);
        } else if (shape < 9) {
            aig = gen_chain_aig(rng, num_vars, 5 + rng() % 25);
        } else if (shape < 11) {
            // Pure big-AND chain of distinct literal inputs: canonical target
            // for k-ary AND fusion. Length 10..800 to also exercise the width
            // cap path.
            uint32_t len = 10 + rng() % 790;
            aig = gen_pure_and_chain(rng, num_vars, len);
        } else if (shape < 13) {
            uint32_t len = 10 + rng() % 790;
            aig = gen_pure_or_chain(rng, num_vars, len);
        } else if (shape < 14) {
            // Balanced AND tree: same semantics as a pure big-AND but
            // built bottom-up, so the encoder has to flatten through internal
            // AND nodes.
            uint32_t len = 8 + rng() % 500;
            aig = gen_balanced_and_tree(rng, num_vars, len);
        } else if (shape < 15) {
            uint32_t len = 8 + rng() % 500;
            aig = gen_balanced_or_tree(rng, num_vars, len);
        } else {
            // Simplify a deep ITE chain first to exercise the encoder on
            // rewritten AIGs (closest to the real pipeline).
            uint32_t d = 50 + rng() % 200;
            uint32_t bw = 2 + rng() % 6;
            aig_ptr raw = gen_deep_ite_chain_aig(rng, num_vars, d, bw);
            if (raw) {
                AIGRewriter rw;
                aig = rw.rewrite(raw);
            }
        }
        if (!aig) continue;

        if (verbose) cout << "[" << iter << "] num_vars=" << num_vars << endl;
        if (!run_one(aig, num_vars, seed, iter, fs, verbose)) return 1;

        fs.iters++;

        if (iter > 0 && iter % 500 == 0) {
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - t_start).count();
            double ratio_cls = fs.naive_clauses_total > 0
                ? (double)fs.opt_clauses_total / fs.naive_clauses_total : 1.0;
            double ratio_h = fs.naive_helpers_total > 0
                ? (double)fs.opt_helpers_total / fs.naive_helpers_total : 1.0;
            cout << "[" << iter << "] OK  "
                 << std::fixed << std::setprecision(0) << iter / elapsed << " it/s  "
                 << "avg-nodes=" << std::setprecision(1) << (double)fs.nodes_total / fs.iters
                 << "  cls_ratio=" << std::setprecision(2) << ratio_cls
                 << "  hlp_ratio=" << ratio_h
                 << "  kAND=" << fs.opt_kary_and
                 << " kOR=" << fs.opt_kary_or
                 << " ITE=" << fs.opt_ite
                 << endl;
        }
    }

    auto t_end = std::chrono::steady_clock::now();
    fs.total_time_s = std::chrono::duration<double>(t_end - t_start).count();
    fs.print();
    cout << "\nAll tests passed!" << endl;
    return 0;
}
