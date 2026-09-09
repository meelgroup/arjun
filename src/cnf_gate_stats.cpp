/*
 Arjun - CNF gate / AIG shape analyzer

 Reads a CNF, optionally runs the puura simplifier on it, lifts the
 recoverable gate logic into an AIG with CnfRewrite::lift_only and prints
 shape statistics: gate histograms, cone sizes, depth, fanout, cone
 classification (AND/OR/XOR/ITE/mixed) and NPN function classes of small
 cones. Used to decide which AIG rewrite rules are worth adding.

 Copyright (c) 2026, Mate Soos. MIT License.
*/

#include <algorithm>
#include <array>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <map>
#include <random>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <cryptominisat5/cryptominisat.h>
#include "arjun.h"
#include "aig_rewrite.h"
#include "aig_to_cnf.h"
#include "cnf_rewrite.h"
#include "config.h"
#include "argparse.hpp"
#include "file_read_helper.h"
#include "time_mem.h"

using namespace ArjunNS;
using namespace ArjunInt;
using std::cout;
using std::endl;
using std::setw;
using std::vector;
using std::string;

namespace {

struct ConeInfo {
    uint32_t and_nodes = 0;
    uint32_t leaves = 0;
    uint32_t depth = 0;
    uint32_t shared_nodes = 0;
    string shape;
    uint16_t tt = 0;
    uint16_t npn = 0;
};

uint16_t tt_transform(uint16_t tt, uint32_t n, const std::array<uint8_t,4>& perm, uint8_t negmask, bool outneg) {
    uint16_t res = 0;
    for (uint32_t m = 0; m < (1u << n); m++) {
        uint32_t old = 0;
        for (uint32_t i = 0; i < n; i++) {
            const uint32_t bit = ((m >> i) & 1) ^ ((negmask >> i) & 1);
            old |= bit << perm[i];
        }
        uint32_t v = (tt >> old) & 1;
        if (outneg) v ^= 1;
        res |= v << m;
    }
    return res;
}

uint16_t npn_canon(uint16_t tt, uint32_t n) {
    std::array<uint8_t,4> perm = {0, 1, 2, 3};
    uint16_t best = 0xffff;
    const uint16_t full = (n == 4) ? 0xffff : (uint16_t)((1u << (1u << n)) - 1);
    tt &= full;
    do {
        for (uint8_t neg = 0; neg < (1u << n); neg++) {
            for (int o = 0; o < 2; o++) {
                const uint16_t t = tt_transform(tt, n, perm, neg, o) & full;
                best = std::min(best, t);
            }
        }
    } while (std::next_permutation(perm.begin(), perm.begin() + n));
    return best;
}

template<class F> uint16_t tt_of(uint32_t n, F f) {
    uint16_t tt = 0;
    for (uint32_t m = 0; m < (1u << n); m++) if (f(m)) tt |= 1u << m;
    return tt;
}

std::map<std::pair<uint32_t,uint16_t>, string> known_classes() {
    std::map<std::pair<uint32_t,uint16_t>, string> k;
    auto bit = [](uint32_t m, uint32_t i) { return (m >> i) & 1; };
    auto add = [&](uint32_t n, const string& name, auto f) {
        k[{n, npn_canon(tt_of(n, f), n)}] = name;
    };
    add(1, "BUF", [&](uint32_t m){ return bit(m,0); });
    add(2, "AND2", [&](uint32_t m){ return bit(m,0)&&bit(m,1); });
    add(2, "XOR2", [&](uint32_t m){ return bit(m,0)^bit(m,1); });
    add(3, "AND3", [&](uint32_t m){ return bit(m,0)&&bit(m,1)&&bit(m,2); });
    add(3, "XOR3", [&](uint32_t m){ return bit(m,0)^bit(m,1)^bit(m,2); });
    add(3, "MAJ3", [&](uint32_t m){ return bit(m,0)+bit(m,1)+bit(m,2) >= 2; });
    add(3, "MUX", [&](uint32_t m){ return bit(m,0) ? bit(m,1) : bit(m,2); });
    add(3, "AND-OR", [&](uint32_t m){ return bit(m,0) && (bit(m,1)||bit(m,2)); });
    add(3, "AND-XOR", [&](uint32_t m){ return bit(m,0) && (bit(m,1)^bit(m,2)); });
    add(3, "OR-XOR", [&](uint32_t m){ return bit(m,0) || (bit(m,1)^bit(m,2)); });
    add(3, "XOR-AND", [&](uint32_t m){ return bit(m,0) ^ (bit(m,1)&&bit(m,2)); });
    add(3, "ONEHOT3", [&](uint32_t m){ return bit(m,0)+bit(m,1)+bit(m,2) == 1; });
    add(4, "AND4", [&](uint32_t m){ return bit(m,0)&&bit(m,1)&&bit(m,2)&&bit(m,3); });
    add(4, "XOR4", [&](uint32_t m){ return bit(m,0)^bit(m,1)^bit(m,2)^bit(m,3); });
    add(4, "AND2-AND2-OR", [&](uint32_t m){ return (bit(m,0)&&bit(m,1)) || (bit(m,2)&&bit(m,3)); });
    add(4, "AND3-OR", [&](uint32_t m){ return (bit(m,0)&&bit(m,1)&&bit(m,2)) || bit(m,3); });
    add(4, "AND2-OR2-AND", [&](uint32_t m){ return (bit(m,0)&&bit(m,1)) && (bit(m,2)||bit(m,3)); });
    add(4, "MUX-AND", [&](uint32_t m){ return (bit(m,0) ? bit(m,1) : bit(m,2)) && bit(m,3); });
    add(4, "MUX-XOR", [&](uint32_t m){ return (bit(m,0) ? bit(m,1) : bit(m,2)) ^ bit(m,3); });
    add(4, "XOR2-XOR2-AND", [&](uint32_t m){ return (bit(m,0)^bit(m,1)) && (bit(m,2)^bit(m,3)); });
    add(4, "XOR2-AND2-OR", [&](uint32_t m){ return (bit(m,0)^bit(m,1)) || (bit(m,2)&&bit(m,3)); });
    add(4, "MAJ3-AND", [&](uint32_t m){ return (bit(m,0)+bit(m,1)+bit(m,2) >= 2) && bit(m,3); });
    add(4, "MAJ3-XOR", [&](uint32_t m){ return (bit(m,0)+bit(m,1)+bit(m,2) >= 2) ^ bit(m,3); });
    add(4, "FA-SUM", [&](uint32_t m){ return bit(m,0)^bit(m,1)^bit(m,2)^bit(m,3); });
    add(4, "AND-OR-OR", [&](uint32_t m){ return bit(m,0) && (bit(m,1)||bit(m,2)||bit(m,3)); });
    add(4, "OR-AND-AND", [&](uint32_t m){ return bit(m,0) || (bit(m,1)&&bit(m,2)&&bit(m,3)); });
    add(4, "AND2-OR-AND", [&](uint32_t m){ return bit(m,0) && (bit(m,1) || (bit(m,2)&&bit(m,3))); });
    add(4, "XOR-AND-OR", [&](uint32_t m){ return bit(m,0) ^ (bit(m,1) && (bit(m,2)||bit(m,3))); });
    add(4, "ITE-chain2", [&](uint32_t m){ return bit(m,0) ? bit(m,1) : (bit(m,2) ? bit(m,3) : 0); });
    return k;
}

bool is_or_edge(const aig_lit& e) { return e && e->type == AIGT::t_and && e.neg; }
bool is_and_edge(const aig_lit& e) { return e && e->type == AIGT::t_and && !e.neg; }

void flatten(const aig_lit& e, bool as_or, vector<aig_lit>& out) {
    const aig_lit l = as_or ? ~e->l : e->l;
    const aig_lit r = as_or ? ~e->r : e->r;
    for (const aig_lit& c : {l, r}) {
        if (as_or ? is_or_edge(c) : is_and_edge(c)) flatten(c, as_or, out);
        else out.push_back(c);
    }
}

bool is_xor2(const aig_lit& e, aig_lit& a, aig_lit& b) {
    if (!e || e->type != AIGT::t_and) return false;
    const aig_lit L = e->l, R = e->r;
    if (!is_and_edge(L) && !(L->type == AIGT::t_and && L.neg)) return false;
    if (!L.node || !R.node || L->type != AIGT::t_and || R->type != AIGT::t_and) return false;
    if (!L.neg || !R.neg) return false;
    const aig_lit la = L->l, lb = L->r, ra = R->l, rb = R->r;
    auto compl_ = [](const aig_lit& x, const aig_lit& y) { return x.node == y.node && x.neg != y.neg; };
    if (compl_(la, ra) && compl_(lb, rb)) { a = la; b = lb; return true; }
    if (compl_(la, rb) && compl_(lb, ra)) { a = la; b = lb; return true; }
    return false;
}

string classify(const aig_lit& root, uint32_t depth_limit = 64) {
    if (!root) return "null";
    if (root->type == AIGT::t_lit) return "LEAF";
    if (root->type == AIGT::t_const) return "CONST";
    aig_lit a, b;
    if (is_xor2(root, a, b)) {
        uint32_t k = 2;
        std::function<uint32_t(const aig_lit&)> chain = [&](const aig_lit& x) -> uint32_t {
            aig_lit p, q;
            if (x->type == AIGT::t_and && is_xor2(x, p, q)) return chain(p) + chain(q);
            return 1;
        };
        k = chain(a) + chain(b);
        return "XOR" + std::to_string(k);
    }
    vector<aig_lit> ops;
    const bool as_or = root.neg;
    flatten(root, as_or, ops);
    bool all_leaf = true;
    for (const auto& o : ops) if (o->type != AIGT::t_lit) { all_leaf = false; break; }
    const string op = as_or ? "OR" : "AND";
    if (all_leaf) return op + std::to_string(ops.size());
    if (as_or && ops.size() == 2 && is_and_edge(ops[0]) && is_and_edge(ops[1])) {
        const aig_lit& A = ops[0]; const aig_lit& B = ops[1];
        auto compl_ = [](const aig_lit& x, const aig_lit& y) { return x.node == y.node && x.neg != y.neg; };
        if (compl_(A->l, B->l) || compl_(A->l, B->r) || compl_(A->r, B->l) || compl_(A->r, B->r)) return "ITE";
    }
    (void)depth_limit;
    return op + std::to_string(ops.size()) + "-mixed";
}

ConeInfo analyze_cone(const aig_lit& root, const std::unordered_map<const AIG*, uint32_t>& parents) {
    ConeInfo ci;
    std::unordered_map<const AIG*, uint32_t> depth;
    std::unordered_set<uint32_t> leaves;
    struct Frame { const AIG* n; bool done; };
    vector<Frame> st{{root.get(), false}};
    while (!st.empty()) {
        Frame f = st.back(); st.pop_back();
        if (depth.count(f.n)) continue;
        if (f.n->type == AIGT::t_lit) { depth[f.n] = 0; leaves.insert(f.n->var); continue; }
        if (f.n->type == AIGT::t_const) { depth[f.n] = 0; continue; }
        if (!f.done) {
            st.push_back({f.n, true});
            if (!depth.count(f.n->l.get())) st.push_back({f.n->l.get(), false});
            if (!depth.count(f.n->r.get())) st.push_back({f.n->r.get(), false});
            continue;
        }
        depth[f.n] = 1 + std::max(depth.at(f.n->l.get()), depth.at(f.n->r.get()));
        ci.and_nodes++;
        auto it = parents.find(f.n);
        if (it != parents.end() && it->second > 1) ci.shared_nodes++;
    }
    ci.depth = root->type == AIGT::t_and ? depth.at(root.get()) : 0;
    ci.leaves = leaves.size();
    ci.shape = classify(root);
    if (ci.leaves <= 4 && ci.leaves >= 1) {
        vector<uint32_t> lv(leaves.begin(), leaves.end());
        std::sort(lv.begin(), lv.end());
        std::unordered_map<uint32_t, uint32_t> pos;
        for (uint32_t i = 0; i < lv.size(); i++) pos[lv[i]] = i;
        uint16_t tt = 0;
        for (uint32_t m = 0; m < (1u << lv.size()); m++) {
            vector<CMSat::lbool> vals(lv.empty() ? 1 : lv.back() + 1, CMSat::l_Undef);
            for (uint32_t i = 0; i < lv.size(); i++) vals[lv[i]] = ((m >> i) & 1) ? CMSat::l_True : CMSat::l_False;
            std::map<aig_lit, CMSat::lbool> cache;
            vector<aig_lit> nodefs(vals.size(), aig_lit());
            const CMSat::lbool r = AIG::evaluate(vals, root, nodefs, cache);
            if (r == CMSat::l_True) tt |= 1u << m;
        }
        ci.tt = tt;
        ci.npn = npn_canon(tt, lv.size());
    }
    return ci;
}

void count_parents(const vector<aig_lit>& roots, std::unordered_map<const AIG*, uint32_t>& parents) {
    std::unordered_set<const AIG*> seen;
    vector<const AIG*> st;
    for (const auto& r : roots) {
        if (!r || r->type != AIGT::t_and) continue;
        parents[r.get()]++;
        st.push_back(r.get());
    }
    while (!st.empty()) {
        const AIG* n = st.back(); st.pop_back();
        if (!seen.insert(n).second) continue;
        if (n->type != AIGT::t_and) continue;
        for (const AIG* c : {n->l.get(), n->r.get()}) {
            if (c->type != AIGT::t_and) continue;
            parents[c]++;
            st.push_back(c);
        }
    }
}

struct Collector {
    uint32_t nv = 0;
    vector<vector<CMSat::Lit>> cls;
    void new_var() { nv++; }
    uint32_t nVars() const { return nv; }
    void add_clause(const vector<CMSat::Lit>& cl) { cls.push_back(cl); }
};

void gain_table(const CnfRewrite::Lifted& lifted, const vector<aig_lit>& roots, int top) {
    struct Acc { uint32_t n = 0; uint64_t orig_lits = 0, orig_cls = 0, new_lits = 0, new_cls = 0, helpers = 0; };
    std::map<string, Acc> by_shape;
    for (size_t i = 0; i < roots.size(); i++) {
        Collector cc;
        cc.nv = lifted.nvars;
        AIGToCNF<Collector> enc(cc);
        const CMSat::Lit r = enc.encode(roots[i]);
        uint64_t lits = 0;
        for (const auto& c : cc.cls) lits += c.size();
        uint32_t ncls = cc.cls.size(), helpers = cc.nv - lifted.nvars;
        if (r.var() >= lifted.nvars) helpers--;
        else { ncls += 2; lits += 4; }
        Acc& a = by_shape[classify(roots[i])];
        a.n++;
        a.orig_lits += lifted.root_gate_lits[i];
        a.orig_cls += lifted.root_gate_cls[i];
        a.new_lits += lits;
        a.new_cls += ncls;
        a.helpers += helpers;
    }
    vector<std::pair<uint32_t, string>> order;
    for (const auto& [k, a] : by_shape) order.push_back({a.n, k});
    std::sort(order.rbegin(), order.rend());
    cout << "c per-shape re-encode of each root alone (top " << top << "):" << endl;
    cout << "c " << std::left << setw(14) << "shape" << std::right << setw(8) << "n" << setw(11) << "orig-lits"
         << setw(10) << "new-lits" << setw(10) << "orig-cls" << setw(9) << "new-cls" << setw(9) << "+vars" << endl;
    int k = 0;
    for (const auto& [n, sh] : order) {
        if (k++ >= top) break;
        const Acc& a = by_shape[sh];
        cout << "c " << std::left << setw(14) << sh << std::right << setw(8) << a.n << setw(11) << a.orig_lits
             << setw(10) << a.new_lits << setw(10) << a.orig_cls << setw(9) << a.new_cls << setw(9) << a.helpers << endl;
    }
}

void comp_table(const vector<CnfRewrite::CompInfo>& comps, int top) {
    struct Acc { uint32_t n = 0, acc = 0; uint64_t gates = 0, orig_lits = 0, new_lits = 0, orig_cls = 0, new_cls = 0; int64_t dvars = 0; };
    std::map<string, Acc> by_shape;
    Acc tot_acc, tot_rej;
    for (const auto& c : comps) {
        string shape = "DEAD";
        size_t best = 0, best_sz = 0;
        for (size_t i = 0; i < c.roots.size(); i++) {
            const size_t sz = AIG::count_aig_nodes_fast(c.roots[i]);
            if (sz >= best_sz) { best_sz = sz; best = i; }
        }
        if (!c.roots.empty()) shape = classify(c.roots[best]);
        if (c.roots.size() > 1) shape += "+" + std::to_string(c.roots.size() - 1);
        Acc& a = by_shape[shape];
        for (Acc* x : {&a, c.accepted ? &tot_acc : &tot_rej}) {
            x->n++; x->acc += c.accepted; x->gates += c.gates;
            x->orig_lits += c.orig_lits; x->new_lits += c.new_lits;
            x->orig_cls += c.orig_cls; x->new_cls += c.new_cls;
            x->dvars += (int64_t)c.helpers - (int64_t)c.removable;
        }
    }
    auto row = [](const string& name, const Acc& a) {
        cout << "c " << std::left << setw(16) << name << std::right << setw(7) << a.n << setw(7) << a.acc
             << setw(7) << a.gates << setw(10) << a.orig_lits << setw(10) << a.new_lits
             << setw(9) << a.orig_cls << setw(9) << a.new_cls << setw(8) << a.dvars << endl;
    };
    cout << "c per-component rewrite (shape = biggest root, +k = other roots), top " << top << ":" << endl;
    cout << "c " << std::left << setw(16) << "shape" << std::right << setw(7) << "comps" << setw(7) << "accept"
         << setw(7) << "gates" << setw(10) << "orig-lits" << setw(10) << "new-lits" << setw(9) << "orig-cls"
         << setw(9) << "new-cls" << setw(8) << "dvars" << endl;
    vector<std::pair<uint64_t, string>> order;
    for (const auto& [k, a] : by_shape) order.push_back({a.orig_lits, k});
    std::sort(order.rbegin(), order.rend());
    int k = 0;
    for (const auto& [n, sh] : order) { if (k++ >= top) break; row(sh, by_shape[sh]); }
    row("TOTAL-accepted", tot_acc);
    row("TOTAL-rejected", tot_rej);
}

void sim_equiv_candidates(const vector<aig_lit>& roots, uint32_t nvars) {
    constexpr uint32_t W = 8;
    std::mt19937_64 rng(12345);
    vector<std::array<uint64_t, W>> leaf_sig(nvars);
    for (auto& a : leaf_sig) for (auto& w : a) w = rng();
    std::unordered_map<const AIG*, std::array<uint64_t, W>> sig;
    struct Frame { const AIG* n; bool done; };
    vector<Frame> st;
    auto edge_sig = [&](const aig_lit& e) {
        std::array<uint64_t, W> r;
        if (e->type == AIGT::t_lit) r = leaf_sig[e->var];
        else if (e->type == AIGT::t_const) r.fill(~0ULL);
        else r = sig.at(e.get());
        if (e.neg) for (auto& w : r) w = ~w;
        return r;
    };
    for (const auto& root : roots) {
        if (!root || root->type != AIGT::t_and) continue;
        st.push_back({root.get(), false});
        while (!st.empty()) {
            Frame f = st.back(); st.pop_back();
            if (sig.count(f.n) || f.n->type != AIGT::t_and) continue;
            if (!f.done) {
                st.push_back({f.n, true});
                if (f.n->l->type == AIGT::t_and && !sig.count(f.n->l.get())) st.push_back({f.n->l.get(), false});
                if (f.n->r->type == AIGT::t_and && !sig.count(f.n->r.get())) st.push_back({f.n->r.get(), false});
                continue;
            }
            auto a = edge_sig(f.n->l), b = edge_sig(f.n->r);
            for (uint32_t i = 0; i < W; i++) a[i] &= b[i];
            sig[f.n] = a;
        }
    }
    std::map<std::array<uint64_t, W>, vector<const AIG*>> classes;
    uint32_t consts = 0;
    for (const auto& [n, sg] : sig) {
        bool all0 = true, all1 = true;
        for (auto w : sg) { if (w) all0 = false; if (~w) all1 = false; }
        if (all0 || all1) { consts++; continue; }
        auto key = sg;
        if (key[0] & 1) for (auto& w : key) w = ~w;
        classes[key].push_back(n);
    }
    std::unordered_set<const AIG*> root_nodes;
    for (const auto& r : roots) if (r && r->type == AIGT::t_and) root_nodes.insert(r.get());
    uint32_t ncls = 0, nodes_in = 0, roots_in = 0, root_pairs = 0;
    for (const auto& [k, v] : classes) {
        if (v.size() < 2) continue;
        ncls++; nodes_in += v.size();
        uint32_t rc = 0;
        for (const AIG* n : v) if (root_nodes.count(n)) rc++;
        roots_in += rc;
        if (rc >= 2) root_pairs += rc - 1;
    }
    for (const auto& [k, v] : classes) {
        if (v.size() < 2) continue;
        for (const AIG* n : v) if (root_nodes.count(n)) { roots_in += 0; break; }
    }
    uint32_t root_in_any = 0;
    for (const auto& [k, v] : classes) {
        if (v.size() < 2) continue;
        for (const AIG* n : v) if (root_nodes.count(n)) root_in_any++;
    }
    cout << "c sim-equiv (512 random patterns): AND nodes " << sig.size() << " const-candidates " << consts
         << " nontrivial classes " << ncls << " nodes in them " << nodes_in
         << " roots in them " << root_in_any << " (mergeable root pairs " << root_pairs << ")" << endl;
}

void report(const string& title, const vector<aig_lit>& roots, const vector<uint32_t>& root_vars,
            uint32_t nvars, int top) {
    cout << "c ===== " << title << " =====" << endl;
    std::unordered_map<const AIG*, uint32_t> parents;
    count_parents(roots, parents);
    std::map<string, uint32_t> shapes;
    std::map<std::pair<uint32_t,uint16_t>, uint32_t> classes;
    std::map<uint32_t, uint32_t> leaf_hist, node_hist, depth_hist;
    uint64_t tot_nodes = 0, tot_shared = 0;
    vector<std::pair<uint32_t, uint32_t>> biggest;
    for (size_t i = 0; i < roots.size(); i++) {
        const ConeInfo ci = analyze_cone(roots[i], parents);
        shapes[ci.shape]++;
        if (ci.leaves >= 1 && ci.leaves <= 4) classes[{ci.leaves, ci.npn}]++;
        leaf_hist[std::min<uint32_t>(ci.leaves, 33)]++;
        node_hist[std::min<uint32_t>(ci.and_nodes, 65)]++;
        depth_hist[std::min<uint32_t>(ci.depth, 33)]++;
        tot_nodes += ci.and_nodes;
        tot_shared += ci.shared_nodes;
        biggest.push_back({ci.and_nodes, (uint32_t)i});
    }
    const size_t total_and = AIG::count_aig_nodes_fast(roots);
    cout << "c roots " << roots.size() << " nvars " << nvars << " AIG nodes (incl. leaves) " << total_and
         << " sum cone AND nodes " << tot_nodes << " shared-node refs " << tot_shared << endl;
    auto hist = [&](const char* name, const std::map<uint32_t,uint32_t>& h, uint32_t cap) {
        cout << "c " << std::left << setw(14) << name << std::right;
        for (const auto& [k, v] : h) cout << " " << (k >= cap ? std::to_string(cap) + "+" : std::to_string(k)) << ":" << v;
        cout << endl;
    };
    hist("cone-leaves", leaf_hist, 33);
    hist("cone-ANDs", node_hist, 65);
    hist("cone-depth", depth_hist, 33);
    vector<std::pair<uint32_t, string>> sh;
    for (const auto& [s, c] : shapes) sh.push_back({c, s});
    std::sort(sh.rbegin(), sh.rend());
    cout << "c shapes (top " << top << "):";
    for (int i = 0; i < top && i < (int)sh.size(); i++) cout << " " << sh[i].second << ":" << sh[i].first;
    cout << endl;
    const auto known = known_classes();
    vector<std::pair<uint32_t, std::pair<uint32_t,uint16_t>>> cl;
    for (const auto& [k, c] : classes) cl.push_back({c, k});
    std::sort(cl.rbegin(), cl.rend());
    cout << "c NPN classes of <=4-leaf cones (top " << top << "):";
    for (int i = 0; i < top && i < (int)cl.size(); i++) {
        const auto& k = cl[i].second;
        auto it = known.find(k);
        cout << " " << (it != known.end() ? it->second : "n" + std::to_string(k.first) + "-tt" + std::to_string(k.second))
             << ":" << cl[i].first;
    }
    cout << endl;
    sim_equiv_candidates(roots, nvars);
    std::sort(biggest.rbegin(), biggest.rend());
    cout << "c biggest cones:";
    for (int i = 0; i < std::min<int>(top, biggest.size()); i++) {
        const uint32_t idx = biggest[i].second;
        cout << " x" << root_vars[idx] + 1 << "(" << biggest[i].first << "," << classify(roots[idx]) << ")";
    }
    cout << endl;

    Collector cc;
    cc.nv = nvars;
    AIGToCNF<Collector> enc(cc);
    enc.set_group_cse(true);
    enc.encode_batch(roots);
    uint64_t lits = 0;
    for (const auto& c : cc.cls) lits += c.size();
    cout << "c encoded: helpers " << (cc.nv - nvars) << " cls " << cc.cls.size() << " lits " << lits << endl;
    enc.get_stats().print(2);
}

}

int main(int argc, char** argv) {
    argparse::ArgumentParser program("cnf_gate_stats", "1.0", argparse::default_arguments::help);
    program.add_description("Gate recovery / AIG shape analyzer for CNFs (see cnf_rewrite.cpp).");
    program.add_argument("--mode").default_value(0).scan<'i', int>().help("0 = unweighted, 1 = weighted");
    program.add_argument("--puura").default_value(1).scan<'i', int>().help("run puura before analyzing");
    program.add_argument("--backward").default_value(1).scan<'i', int>().help("minimize the independent support first (as arjun does)");
    program.add_argument("--rewrite").default_value(1).scan<'i', int>().help("also analyze after AIGRewriter");
    program.add_argument("--balance").default_value(0).scan<'i', int>().help("balance in AIGRewriter");
    program.add_argument("--irreg").default_value(1).scan<'i', int>().help("irregular gate detection");
    program.add_argument("--maxxor").default_value(8).scan<'i', int>().help("max XOR clause size");
    program.add_argument("--top").default_value(12).scan<'i', int>().help("top-N entries per list");
    program.add_argument("--dump").default_value(string("")).help("dump lifted AIGs (before/after) to <prefix>-lift.aig / -rw.aig");
    program.add_argument("-v", "--verb").default_value(0).scan<'i', int>();
    program.add_argument("file").help("input CNF");
    try { program.parse_args(argc, argv); }
    catch (const std::exception& e) { std::cerr << e.what() << endl << program; return 1; }

    const int mode = program.get<int>("--mode");
    std::unique_ptr<CMSat::FieldGen> fg;
    if (mode == 0) fg = std::make_unique<FGenMpz>();
    else fg = std::make_unique<FGenMpq>();
    SimplifiedCNF cnf(fg);
    bool all_indep = false;
    read_in_a_file(program.get<string>("file"), &cnf, all_indep, fg);
    cnf.clean_idiotic_mccomp_weights();
    cnf.check_cnf_sampl_sanity();
    cout << "c input: vars " << cnf.nVars() << " cls " << cnf.get_clauses().size()
         << " sampl " << cnf.get_sampl_vars().size() << " opt-sampl " << cnf.get_opt_sampl_vars().size() << endl;

    Arjun arjun;
    arjun.set_verb(program.get<int>("--verb"));
    Arjun::InterpConf iconf;
    if (program.get<int>("--backward")) {
        arjun.standalone_minimize_indep(cnf, iconf, false);
        cout << "c after backward: sampl " << cnf.get_sampl_vars().size() << endl;
    }
    if (program.get<int>("--puura")) {
        SimpConf sc;
        cnf = arjun.standalone_get_simplified_cnf(cnf, sc);
        cout << "c after puura: vars " << cnf.nVars() << " cls " << cnf.get_clauses().size() << endl;
    }
    uint64_t lits = 0;
    for (const auto& c : cnf.get_clauses()) lits += c.size();
    cout << "c analyzed CNF: vars " << cnf.nVars() << " cls " << cnf.get_clauses().size() << " lits " << lits << endl;

    Config conf;
    conf.verb = 1;
    conf.cnfrw_irreg = program.get<int>("--irreg");
    conf.cnfrw_max_xor_size = program.get<int>("--maxxor");
    CnfRewrite rw(conf);
    const double t0 = cpuTime();
    auto lifted = rw.lift_only(cnf);
    cout << "c lift T: " << std::fixed << std::setprecision(2) << (cpuTime() - t0) << endl;
    rw.get_stats().print(1, "");
    uint32_t removable = 0;
    for (const char r : lifted.removable) removable += r;
    cout << "c gate outputs " << rw.get_stats().gate_outputs << " removable (inlined) " << removable
         << " roots " << lifted.roots.size() << endl;
    const int top = program.get<int>("--top");
    report("lifted AIG", lifted.roots, lifted.root_vars, lifted.nvars, top);
    gain_table(lifted, lifted.roots, top);
    const string dump = program.get<string>("--dump");
    auto dump_aigs = [&](const vector<aig_lit>& roots, const string& suffix) {
        if (dump.empty()) return;
        SimplifiedCNF d(fg);
        d.set_need_aig();
        d.new_vars(lifted.nvars);
        for (size_t i = 0; i < roots.size(); i++) d.set_def(lifted.root_vars[i], roots[i]);
        d.write_aig_defs_to_file(dump + suffix);
        cout << "c dumped " << dump + suffix << endl;
    };
    dump_aigs(lifted.roots, "-lift.aig");
    {
        SimplifiedCNF copy = cnf;
        Config conf2 = conf;
        conf2.verb = 0;
        conf2.cnfrw_rewrite = program.get<int>("--rewrite");
        conf2.cnfrw_balance = program.get<int>("--balance");
        CnfRewrite rw2(conf2);
        rw2.set_collect_comp_info(true);
        rw2.run(copy, "");
        comp_table(rw2.get_comp_info(), top);
        uint64_t l2 = 0;
        for (const auto& c : copy.get_clauses()) l2 += c.size();
        cout << "c after cnfrw run: vars " << copy.nVars() << " cls " << copy.get_clauses().size() << " lits " << l2 << endl;
    }
    if (program.get<int>("--rewrite")) {
        vector<aig_lit> rwroots = lifted.roots;
        AIGRewriter r;
        r.rewrite_all(rwroots, 1, program.get<int>("--balance"));
        report("after AIGRewriter", rwroots, lifted.root_vars, lifted.nvars, top);
        gain_table(lifted, rwroots, top);
        dump_aigs(rwroots, "-rw.aig");
    }
    return 0;
}
