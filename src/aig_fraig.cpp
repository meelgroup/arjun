/*
 Arjun - AIG SAT sweeping (FRAIG)

 Copyright (c) 2026, Mate Soos. MIT License.
 */

#include "aig_fraig.h"
#include "metasolver.h"
#include "time_mem.h"
#include "constants.h"

#include <algorithm>
#include <iomanip>
#include <iostream>
#include <map>
#include <random>
#include <unordered_map>

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::cout;
using std::endl;
using std::vector;

void AIGFraigStats::print(int verb) const {
    if (verb < 1) return;
    cout << "c o [aig-fraig] T:" << std::fixed << std::setprecision(2) << time
         << " ands:" << and_nodes << " leaves:" << leaves
         << " sim-classes:" << sim_classes << "/" << sim_class_nodes
         << " const-cands:" << const_cands
         << " checks:" << checks << " eq:" << proved_eq << " const:" << proved_const
         << " neq:" << disproved << " tout:" << timeouts << " cex:" << cex_patterns
         << " confl:" << conflicts
         << " nodes:" << nodes_before << "->" << nodes_after << endl;
}

namespace {

aig_lit flip(const aig_lit& a, bool n) { return n ? ~a : a; }

struct Node {
    aig_lit self;
    uint32_t l = 0, r = 0;
    bool l_neg = false, r_neg = false;
    bool is_and = false;
    bool is_const = false;
    uint32_t var = 0;
};

}

bool AIGFraig::fraig(vector<aig_lit>& roots) {
    const double t0 = cpuTime();
    stats = AIGFraigStats();
    stats.nodes_before = AIG::count_aig_nodes_fast(roots);

    vector<Node> nodes;
    std::unordered_map<const AIG*, uint32_t> idx;
    {
        struct Frame { aig_lit e; bool done; };
        vector<Frame> st;
        for (const auto& r : roots) if (r) st.push_back({aig_lit(r.node, false), false});
        while (!st.empty()) {
            Frame f = st.back(); st.pop_back();
            const AIG* n = f.e.get();
            if (idx.count(n)) continue;
            if (n->type != AIGT::t_and) {
                Node nd; nd.self = f.e; nd.is_const = n->type == AIGT::t_const; nd.var = n->var;
                idx[n] = nodes.size(); nodes.push_back(nd);
                continue;
            }
            if (!f.done) {
                st.push_back({f.e, true});
                if (!idx.count(n->l.get())) st.push_back({aig_lit(n->l.node, false), false});
                if (!idx.count(n->r.get())) st.push_back({aig_lit(n->r.node, false), false});
                continue;
            }
            Node nd; nd.self = f.e; nd.is_and = true;
            nd.l = idx.at(n->l.get()); nd.l_neg = n->l.neg;
            nd.r = idx.at(n->r.get()); nd.r_neg = n->r.neg;
            idx[n] = nodes.size(); nodes.push_back(nd);
        }
    }
    const uint32_t N = nodes.size();
    for (const auto& nd : nodes) { if (nd.is_and) stats.and_nodes++; else if (!nd.is_const) stats.leaves++; }
    if (stats.and_nodes < 2) { stats.nodes_after = stats.nodes_before; stats.time = cpuTime() - t0; return false; }

    const uint32_t W = conf.sim_words;
    vector<uint64_t> sig((size_t)N * W);
    std::mt19937_64 rng(0x5eed1234abcdULL);
    std::unordered_map<uint32_t, uint32_t> var_first;
    for (uint32_t i = 0; i < N; i++) {
        uint64_t* s = &sig[(size_t)i * W];
        const Node& nd = nodes[i];
        if (nd.is_const) { for (uint32_t w = 0; w < W; w++) s[w] = ~0ULL; continue; }
        if (!nd.is_and) {
            auto it = var_first.find(nd.var);
            if (it != var_first.end()) { const uint64_t* o = &sig[(size_t)it->second * W]; for (uint32_t w = 0; w < W; w++) s[w] = o[w]; }
            else { var_first[nd.var] = i; for (uint32_t w = 0; w < W; w++) s[w] = rng(); }
            continue;
        }
        const uint64_t* a = &sig[(size_t)nd.l * W];
        const uint64_t* b = &sig[(size_t)nd.r * W];
        for (uint32_t w = 0; w < W; w++) s[w] = (nd.l_neg ? ~a[w] : a[w]) & (nd.r_neg ? ~b[w] : b[w]);
    }

    MetaSolver solver(SolverType::cadical);
    solver.set_verbosity(0);
    std::unordered_map<uint32_t, uint32_t> var_sv;
    vector<Lit> sv(N, lit_Undef);
    for (uint32_t i = 0; i < N; i++) {
        const Node& nd = nodes[i];
        if (nd.is_const) { solver.new_var(); sv[i] = Lit(solver.nVars() - 1, false); solver.add_clause({sv[i]}); continue; }
        if (!nd.is_and) {
            auto it = var_sv.find(nd.var);
            if (it == var_sv.end()) { solver.new_var(); it = var_sv.emplace(nd.var, solver.nVars() - 1).first; }
            sv[i] = Lit(it->second, false);
            continue;
        }
        solver.new_var();
        const Lit h(solver.nVars() - 1, false);
        sv[i] = h;
        const Lit a = sv[nd.l] ^ nd.l_neg, b = sv[nd.r] ^ nd.r_neg;
        solver.add_clause({~h, a});
        solver.add_clause({~h, b});
        solver.add_clause({h, ~a, ~b});
    }

    vector<vector<uint64_t>> cex(N);
    uint32_t ncex = 0;
    auto add_cex = [&](const vector<lbool>& model) {
        if (ncex >= conf.max_cex) return;
        const uint32_t w = ncex / 64, b = ncex % 64;
        vector<char> val(N, 0);
        for (uint32_t i = 0; i < N; i++) {
            const Node& nd = nodes[i];
            if (nd.is_const) val[i] = 1;
            else if (!nd.is_and) { const uint32_t v = sv[i].var(); val[i] = v < model.size() && model[v] == l_True; }
            else val[i] = ((val[nd.l] != 0) != nd.l_neg) && ((val[nd.r] != 0) != nd.r_neg);
            if (cex[i].size() <= w) cex[i].resize(w + 1, 0);
            if (val[i]) cex[i][w] |= 1ULL << b;
        }
        ncex++;
        stats.cex_patterns++;
    };
    auto cex_match = [&](uint32_t a, uint32_t b, bool neg) {
        const uint32_t words = (ncex + 63) / 64;
        for (uint32_t w = 0; w < words; w++) {
            const uint64_t x = w < cex[a].size() ? cex[a][w] : 0;
            uint64_t y = w < cex[b].size() ? cex[b][w] : 0;
            if (neg) y = ~y;
            uint64_t mask = ~0ULL;
            if (w == words - 1 && (ncex % 64)) mask = (1ULL << (ncex % 64)) - 1;
            if ((x ^ y) & mask) return false;
        }
        return true;
    };

    std::map<vector<uint64_t>, vector<uint32_t>> classes;
    vector<uint64_t> key(W);
    vector<char> is_const_cand(N, 0);
    for (uint32_t i = 0; i < N; i++) {
        if (!nodes[i].is_and) continue;
        const uint64_t* s = &sig[(size_t)i * W];
        bool all0 = true, all1 = true;
        for (uint32_t w = 0; w < W; w++) { if (s[w]) all0 = false; if (~s[w]) all1 = false; }
        if (all0 || all1) { is_const_cand[i] = 1; stats.const_cands++; continue; }
        const bool flip = s[0] & 1;
        for (uint32_t w = 0; w < W; w++) key[w] = flip ? ~s[w] : s[w];
        classes[key].push_back(i);
    }
    vector<int32_t> class_of(N, -1);
    vector<vector<uint32_t>> reps;
    for (auto& [k, members] : classes) {
        if (members.size() < 2) continue;
        stats.sim_classes++;
        stats.sim_class_nodes += members.size();
        const uint32_t c = reps.size();
        reps.emplace_back();
        for (const uint32_t m : members) class_of[m] = c;
    }

    vector<aig_lit> repl(N);
    vector<char> merged(N, 0);
    vector<uint32_t> merged_to(N, 0);
    vector<char> merged_neg(N, 0);
    vector<char> merged_const(N, 0);
    vector<char> merged_const_val(N, 0);
    int64_t confl_start = solver.get_sum_conflicts();
    bool budget_out = false;
    auto check = [&](vector<Lit>& assumps) -> lbool {
        if (budget_out || stats.checks >= conf.max_checks) return l_Undef;
        if ((stats.checks & 15) == 0 && cpuTime() - t0 > conf.max_time) { budget_out = true; return l_Undef; }
        stats.checks++;
        solver.set_max_confl(conf.max_confl_per_check);
        const lbool ret = solver.solve(&assumps);
        stats.conflicts = solver.get_sum_conflicts() - confl_start;
        if ((int64_t)stats.conflicts > conf.max_confl_total) budget_out = true;
        if (ret == l_Undef) stats.timeouts++;
        return ret;
    };

    for (uint32_t i = 0; i < N; i++) {
        const Node& nd = nodes[i];
        if (!nd.is_and) continue;
        if (is_const_cand[i]) {
            const bool val = sig[(size_t)i * W] & 1;
            vector<Lit> assumps{sv[i] ^ val};
            const lbool ret = check(assumps);
            if (ret == l_False) { merged[i] = 1; merged_const[i] = 1; merged_const_val[i] = val; stats.proved_const++; }
            else if (ret == l_True) { stats.disproved++; add_cex(solver.get_model()); }
            continue;
        }
        if (class_of[i] < 0) continue;
        vector<uint32_t>& rl = reps[class_of[i]];
        const bool par_i = sig[(size_t)i * W] & 1;
        bool done = false;
        for (const uint32_t r : rl) {
            const bool neg = par_i != (bool)(sig[(size_t)r * W] & 1);
            if (!cex_match(i, r, neg)) continue;
            solver.new_var();
            const Lit s(solver.nVars() - 1, false);
            const Lit a = sv[i], b = sv[r] ^ neg;
            solver.add_clause({~s, a, b});
            solver.add_clause({~s, ~a, ~b});
            vector<Lit> assumps{s};
            const lbool ret = check(assumps);
            solver.add_clause({~s});
            if (ret == l_False) {
                merged[i] = 1; merged_to[i] = r; merged_neg[i] = neg; stats.proved_eq++;
                done = true; break;
            }
            if (ret == l_True) { stats.disproved++; add_cex(solver.get_model()); }
        }
        if (!done) rl.push_back(i);
    }

    if (stats.proved_eq == 0 && stats.proved_const == 0) {
        stats.nodes_after = stats.nodes_before;
        stats.time = cpuTime() - t0;
        stats.print(conf.verb);
        return false;
    }

    for (uint32_t i = 0; i < N; i++) {
        const Node& nd = nodes[i];
        if (!nd.is_and) { repl[i] = nd.self; continue; }
        if (merged[i]) {
            if (merged_const[i]) repl[i] = AIG::new_const(merged_const_val[i]);
            else repl[i] = flip(repl[merged_to[i]], merged_neg[i]);
            continue;
        }
        const aig_lit a = flip(repl[nd.l], nd.l_neg), b = flip(repl[nd.r], nd.r_neg);
        if (a.node == nd.self->l.node && a.neg == nd.self->l.neg && b.node == nd.self->r.node && b.neg == nd.self->r.neg)
            repl[i] = nd.self;
        else repl[i] = AIG::new_and(a, b);
    }
    for (auto& r : roots) {
        if (!r) continue;
        r = flip(repl[idx.at(r.get())], r.neg);
    }
    stats.nodes_after = AIG::count_aig_nodes_fast(roots);
    stats.time = cpuTime() - t0;
    stats.print(conf.verb);
    return true;
}
