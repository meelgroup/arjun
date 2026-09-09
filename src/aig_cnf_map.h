/*
 Arjun - Cut-based AIG to CNF mapping

 Technology-mapping style CNF generation: every AND node enumerates
 k-feasible cuts (k <= 5) plus one wide k-ary AND supergate, each cut priced
 by the minimum-clause CNF of its truth table (cut_cnf.h) plus a helper
 weight. Best cuts are chosen by area flow, the cover is selected from the
 roots down, and each selected cut becomes one helper variable with its
 minimum CNF. Same Solver interface as AIGToCNF.

 Copyright (c) 2026, Mate Soos. MIT License.
 */

#pragma once

#include "arjun.h"
#include "cut_cnf.h"
#include <cryptominisat5/solvertypesmini.h>
#include <algorithm>
#include <cstdint>
#include <unordered_map>
#include <vector>

namespace ArjunNS {

struct AIGCnfMapStats {
    uint64_t and_nodes = 0;
    uint64_t cuts_enumerated = 0;
    uint64_t selected = 0;
    uint64_t selected_kand = 0;
    uint64_t alias_nodes = 0;
    uint64_t helpers = 0;
    uint64_t clauses = 0;
    uint64_t dup_interior = 0;
    void clear() { *this = AIGCnfMapStats(); }
};

template<class Solver>
class AIGCnfMapper {
public:
    explicit AIGCnfMapper(Solver& s) : solver(s) {}
    std::vector<CMSat::Lit> encode_batch(const std::vector<aig_lit>& roots);
    void set_true_lit(CMSat::Lit t) { my_true_lit = t; my_has_true_lit = true; }
    void set_max_leaves(uint32_t k) { max_leaves = std::min<uint32_t>(5, std::max<uint32_t>(2, k)); }
    void set_max_cuts(uint32_t c) { max_cuts = std::max<uint32_t>(1, c); }
    void set_helper_weight(double w) { helper_weight = w; }
    void set_kand(bool b) { use_kand = b; }
    void set_max_kand(uint32_t k) { max_kand = k; }
    const AIGCnfMapStats& get_stats() const { return stats; }

private:
    struct Node {
        const AIG* n = nullptr;
        uint32_t l = 0, r = 0;
        bool l_neg = false, r_neg = false;
        bool is_and = false, is_const = false;
        uint32_t var = 0;
        uint32_t fanout = 0;
    };
    struct Cut {
        std::vector<uint32_t> leaves;
        std::vector<bool> leaf_neg;
        uint32_t tt = 0;
        uint32_t cost = 0;
        double flow = 0;
        bool kand = false;
        bool alias = false;
        CMSat::Lit alias_lit = CMSat::lit_Undef;
        bool alias_neg = false;
        uint32_t alias_leaf = 0;
        int alias_const = -1;
    };

    Solver& solver;
    AIGCnfMapStats stats;
    CMSat::Lit my_true_lit = CMSat::Lit(0, false);
    bool my_has_true_lit = false;
    uint32_t max_leaves = 5;
    uint32_t max_cuts = 8;
    double helper_weight = 1.0;
    bool use_kand = true;
    uint32_t max_kand = 1u << 30;

    std::vector<Node> nodes;
    std::unordered_map<const AIG*, uint32_t> idx;
    std::vector<Cut> best;
    std::vector<std::vector<Cut>> cuts_of;
    std::vector<double> flow;
    std::vector<CMSat::Lit> lit_of;

    CMSat::Lit true_lit() {
        if (!my_has_true_lit) {
            solver.new_var();
            my_true_lit = CMSat::Lit(solver.nVars() - 1, false);
            my_has_true_lit = true;
            stats.helpers++;
            add_clause({my_true_lit});
        }
        return my_true_lit;
    }
    void add_clause(const std::vector<CMSat::Lit>& cl) {
        std::vector<CMSat::Lit> tmp(cl);
        std::sort(tmp.begin(), tmp.end());
        tmp.erase(std::unique(tmp.begin(), tmp.end()), tmp.end());
        for (size_t i = 1; i < tmp.size(); i++) if (tmp[i].var() == tmp[i-1].var()) return;
        solver.add_clause(tmp);
        stats.clauses++;
    }
    void build(const std::vector<aig_lit>& roots);
    uint32_t eval_tt(uint32_t i, const std::vector<uint32_t>& leaves, std::unordered_map<uint32_t, uint32_t>& memo, uint32_t full);
    bool make_cut(uint32_t i, std::vector<uint32_t> leaves, Cut& out);
    void collect_kand(uint32_t i, bool neg, std::vector<uint32_t>& lv, std::vector<bool>& ln);
    void enumerate(uint32_t i);
    static bool merge_leaves(const std::vector<uint32_t>& a, const std::vector<uint32_t>& b, uint32_t k, std::vector<uint32_t>& out);
};

template<class Solver>
void AIGCnfMapper<Solver>::build(const std::vector<aig_lit>& roots) {
    nodes.clear(); idx.clear();
    struct Frame { const AIG* n; bool done; };
    std::vector<Frame> st;
    for (const auto& r : roots) if (r) st.push_back({r.get(), false});
    while (!st.empty()) {
        Frame f = st.back(); st.pop_back();
        if (idx.count(f.n)) continue;
        if (f.n->type != AIGT::t_and) {
            Node nd; nd.n = f.n; nd.is_const = f.n->type == AIGT::t_const; nd.var = f.n->var;
            idx[f.n] = nodes.size(); nodes.push_back(nd);
            continue;
        }
        if (!f.done) {
            st.push_back({f.n, true});
            if (!idx.count(f.n->l.get())) st.push_back({f.n->l.get(), false});
            if (!idx.count(f.n->r.get())) st.push_back({f.n->r.get(), false});
            continue;
        }
        Node nd; nd.n = f.n; nd.is_and = true;
        nd.l = idx.at(f.n->l.get()); nd.l_neg = f.n->l.neg;
        nd.r = idx.at(f.n->r.get()); nd.r_neg = f.n->r.neg;
        idx[f.n] = nodes.size(); nodes.push_back(nd);
    }
    for (const auto& nd : nodes) if (nd.is_and) { nodes[nd.l].fanout++; nodes[nd.r].fanout++; stats.and_nodes++; }
    for (const auto& r : roots) if (r) nodes[idx.at(r.get())].fanout++;
}

template<class Solver>
uint32_t AIGCnfMapper<Solver>::eval_tt(uint32_t i, const std::vector<uint32_t>& leaves,
                                       std::unordered_map<uint32_t, uint32_t>& memo, uint32_t full) {
    auto it = memo.find(i);
    if (it != memo.end()) return it->second;
    const Node& nd = nodes[i];
    uint32_t v;
    if (nd.is_const) v = full;
    else {
        assert(nd.is_and);
        const uint32_t a = eval_tt(nd.l, leaves, memo, full), b = eval_tt(nd.r, leaves, memo, full);
        v = (nd.l_neg ? (~a & full) : a) & (nd.r_neg ? (~b & full) : b);
    }
    memo[i] = v;
    return v;
}

template<class Solver>
bool AIGCnfMapper<Solver>::merge_leaves(const std::vector<uint32_t>& a, const std::vector<uint32_t>& b,
                                        uint32_t k, std::vector<uint32_t>& out) {
    out.clear();
    size_t i = 0, j = 0;
    while (i < a.size() || j < b.size()) {
        uint32_t x;
        if (j >= b.size() || (i < a.size() && a[i] < b[j])) x = a[i++];
        else if (i >= a.size() || b[j] < a[i]) x = b[j++];
        else { x = a[i]; i++; j++; }
        out.push_back(x);
        if (out.size() > k) return false;
    }
    return true;
}

template<class Solver>
bool AIGCnfMapper<Solver>::make_cut(uint32_t i, std::vector<uint32_t> leaves, Cut& out) {
    const uint32_t k = leaves.size();
    const uint32_t nmt = 1u << k;
    const uint32_t full = nmt >= 32 ? 0xFFFFFFFFu : ((1u << nmt) - 1);
    std::unordered_map<uint32_t, uint32_t> memo;
    for (uint32_t s = 0; s < k; s++) {
        uint32_t m = 0;
        for (uint32_t mt = 0; mt < nmt; mt++) if ((mt >> s) & 1) m |= 1u << mt;
        memo[leaves[s]] = m;
    }
    const uint32_t tt = eval_tt(i, leaves, memo, full);
    out = Cut();
    out.leaves = std::move(leaves);
    out.tt = tt;
    if (tt == 0 || tt == full) { out.alias = true; out.alias_const = tt == full; out.cost = 0; return true; }
    for (uint32_t s = 0; s < k; s++) {
        const uint32_t m = memo.at(out.leaves[s]);
        if (tt == m) { out.alias = true; out.alias_leaf = s; out.alias_neg = false; out.cost = 0; return true; }
        if (tt == (~m & full)) { out.alias = true; out.alias_leaf = s; out.alias_neg = true; out.cost = 0; return true; }
    }
    out.cost = cut_cnf::min_cnf_for_tt(k, tt).clauses.size();
    return true;
}

template<class Solver>
void AIGCnfMapper<Solver>::collect_kand(uint32_t i, bool neg, std::vector<uint32_t>& lv, std::vector<bool>& ln) {
    const Node& nd = nodes[i];
    if (nd.is_and && !neg && nd.fanout <= 1 && lv.size() < max_kand) {
        collect_kand(nd.l, nd.l_neg, lv, ln);
        collect_kand(nd.r, nd.r_neg, lv, ln);
        return;
    }
    lv.push_back(i); ln.push_back(neg);
}

template<class Solver>
void AIGCnfMapper<Solver>::enumerate(uint32_t i) {
    const Node& nd = nodes[i];
    std::vector<Cut> cands;
    auto leaf_sets = [&](uint32_t c) {
        std::vector<std::vector<uint32_t>> out;
        out.push_back({c});
        if (nodes[c].is_and && !best[c].alias && !best[c].kand)
            for (const auto& cut : cuts_of[c]) out.push_back(cut.leaves);
        return out;
    };
    const auto ls = leaf_sets(nd.l), rs = leaf_sets(nd.r);
    std::vector<uint32_t> merged;
    for (const auto& a : ls) for (const auto& b : rs) {
        if (!merge_leaves(a, b, max_leaves, merged)) continue;
        std::vector<uint32_t> lv;
        for (const uint32_t x : merged) if (!nodes[x].is_const) lv.push_back(x);
        if (lv.empty()) continue;
        Cut c;
        if (!make_cut(i, lv, c)) continue;
        stats.cuts_enumerated++;
        c.flow = c.cost + (c.alias ? 0.0 : helper_weight);
        for (const uint32_t x : c.leaves) if (nodes[x].is_and) c.flow += flow[x] / std::max<uint32_t>(1, nodes[x].fanout);
        cands.push_back(std::move(c));
    }
    if (use_kand) {
        Cut c; c.kand = true;
        collect_kand(nd.l, nd.l_neg, c.leaves, c.leaf_neg);
        collect_kand(nd.r, nd.r_neg, c.leaves, c.leaf_neg);
        if (c.leaves.size() > max_leaves) {
            c.cost = c.leaves.size() + 1;
            c.flow = c.cost + helper_weight;
            for (const uint32_t x : c.leaves) if (nodes[x].is_and) c.flow += flow[x] / std::max<uint32_t>(1, nodes[x].fanout);
            cands.push_back(std::move(c));
        }
    }
    std::sort(cands.begin(), cands.end(), [](const Cut& a, const Cut& b) {
        if (a.flow != b.flow) return a.flow < b.flow;
        return a.leaves.size() < b.leaves.size();
    });
    if (cands.size() > max_cuts) cands.resize(max_cuts);
    best[i] = cands.front();
    flow[i] = best[i].flow;
    cuts_of[i].clear();
    for (const auto& c : cands) if (!c.kand && !c.alias) cuts_of[i].push_back(c);
}

template<class Solver>
std::vector<CMSat::Lit> AIGCnfMapper<Solver>::encode_batch(const std::vector<aig_lit>& roots) {
    stats.clear();
    build(roots);
    const uint32_t N = nodes.size();
    best.assign(N, Cut());
    flow.assign(N, 0.0);
    cuts_of.assign(N, {});
    for (uint32_t i = 0; i < N; i++) if (nodes[i].is_and) enumerate(i);

    std::vector<char> required(N, 0);
    for (const auto& r : roots) if (r && r->type == AIGT::t_and) required[idx.at(r.get())] = 1;
    for (uint32_t i = N; i-- > 0;) {
        if (!required[i] || !nodes[i].is_and) continue;
        const Cut& c = best[i];
        if (c.alias) {
            if (c.alias_const < 0) required[c.leaves[c.alias_leaf]] = 1;
            continue;
        }
        for (const uint32_t x : c.leaves) if (nodes[x].is_and) required[x] = 1;
    }

    lit_of.assign(N, CMSat::lit_Undef);
    for (uint32_t i = 0; i < N; i++) {
        const Node& nd = nodes[i];
        if (nd.is_const) { if (required[i]) lit_of[i] = true_lit(); continue; }
        if (!nd.is_and) { lit_of[i] = CMSat::Lit(nd.var, false); continue; }
        if (!required[i]) continue;
        const Cut& c = best[i];
        if (c.alias) {
            stats.alias_nodes++;
            if (c.alias_const >= 0) lit_of[i] = c.alias_const ? true_lit() : ~true_lit();
            else lit_of[i] = lit_of[c.leaves[c.alias_leaf]] ^ c.alias_neg;
            assert(lit_of[i] != CMSat::lit_Undef);
            continue;
        }
        solver.new_var();
        stats.helpers++;
        const CMSat::Lit h(solver.nVars() - 1, false);
        lit_of[i] = h;
        stats.selected++;
        if (c.kand) {
            stats.selected_kand++;
            std::vector<CMSat::Lit> back{h};
            for (size_t s = 0; s < c.leaves.size(); s++) {
                CMSat::Lit l = lit_of[c.leaves[s]];
                if (l == CMSat::lit_Undef) l = nodes[c.leaves[s]].is_const ? true_lit() : l;
                assert(l != CMSat::lit_Undef);
                l = l ^ c.leaf_neg[s];
                add_clause({~h, l});
                back.push_back(~l);
            }
            add_clause(back);
            continue;
        }
        const auto& mc = cut_cnf::min_cnf_for_tt(c.leaves.size(), c.tt);
        for (const auto& cl : mc.clauses) {
            std::vector<CMSat::Lit> lits;
            for (uint32_t s = 0; s < c.leaves.size(); s++) {
                if (!((cl.present >> s) & 1)) continue;
                CMSat::Lit l = lit_of[c.leaves[s]];
                assert(l != CMSat::lit_Undef);
                lits.push_back(l ^ (bool)((cl.sign >> s) & 1));
            }
            lits.push_back(h ^ (bool)cl.g_sign);
            add_clause(lits);
        }
    }
    std::vector<CMSat::Lit> res;
    for (const auto& r : roots) {
        if (!r) { res.emplace_back(0, false); continue; }
        if (r->type == AIGT::t_const) { res.push_back(true_lit() ^ r.neg); continue; }
        const CMSat::Lit l = lit_of[idx.at(r.get())];
        assert(l != CMSat::lit_Undef);
        res.push_back(l ^ r.neg);
    }
    return res;
}

}
