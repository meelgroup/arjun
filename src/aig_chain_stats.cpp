/*
 Arjun - repair-chain shape analyzer

 Loads a --dumprestartaig dump and prints per-def and aggregate stats on the
 Manthan repair-chain structure (decision-list runs, cube widths, two-level
 minimization opportunities). Used to design AIGRewriter rules.

 Copyright (c) 2026, Mate Soos. MIT License.
*/

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <set>
#include <vector>
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>
#include "arjun.h"
#include "aig_rewrite.h"
#include "argparse.hpp"
#include "time_mem.h"

using namespace ArjunNS;
using std::cout;
using std::endl;
using std::vector;

// A cube as a sorted vector of literals (var*2+sign encoding).
using Cube = vector<uint32_t>;

static bool collect_cube(const aig_lit& e, Cube& out) {
    if (!e) return false;
    if (e->type == AIGT::t_lit) {
        out.push_back(e->var * 2 + (e.neg ? 1 : 0));
        return true;
    }
    if (e->type == AIGT::t_and && !e.neg) {
        return collect_cube(e->l, out) && collect_cube(e->r, out);
    }
    return false;
}

static bool is_or_edge(const aig_lit& e) {
    return e && e->type == AIGT::t_and && e.neg;
}

struct RunStats {
    char op; // 'O' = OR of cubes, 'A' = AND of clauses
    vector<Cube> cubes;
};

// Walk the decision-list chain, collecting same-op runs; returns layer count.
static size_t walk_chain(aig_lit e, vector<RunStats>& runs) {
    size_t layers = 0;
    while (e && e->type == AIGT::t_and) {
        Cube c;
        aig_lit next;
        char op;
        if (is_or_edge(e)) {
            // OR(~e->l, ~e->r); the cube side is a cube.
            c.clear();
            if (collect_cube(~e->l, c)) next = ~e->r;
            else { c.clear(); if (collect_cube(~e->r, c)) next = ~e->l; else break; }
            op = 'O';
        } else {
            // AND(x, y); the "clause" side is ~cube.
            c.clear();
            if (collect_cube(~e->l, c)) next = e->r;
            else { c.clear(); if (collect_cube(~e->r, c)) next = e->l; else break; }
            op = 'A';
        }
        std::sort(c.begin(), c.end());
        if (runs.empty() || runs.back().op != op) runs.push_back({op, {}});
        runs.back().cubes.push_back(c);
        layers++;
        e = next;
    }
    return layers;
}

// dist-1: identical except exactly one literal is complemented.
static bool distance1(const Cube& a, const Cube& b) {
    if (a.size() != b.size()) return false;
    int diff = 0;
    for (size_t i = 0; i < a.size(); i++) {
        if (a[i] == b[i]) continue;
        if ((a[i] ^ 1) == b[i]) { if (++diff > 1) return false; }
        else return false;
    }
    return diff == 1;
}

// a subsumes b: a's literals are a subset of b's.
static bool subset_of(const Cube& a, const Cube& b) {
    if (a.size() > b.size()) return false;
    size_t i = 0;
    for (size_t j = 0; j < b.size() && i < a.size(); j++)
        if (a[i] == b[j]) i++;
    return i == a.size();
}

// ===== Minimal BDD package for run-size measurement =====
// Plain BDD with a unique table and OR-apply cache, capped at `cap` nodes.
struct MiniBdd {
    // node 0 = FALSE, node 1 = TRUE
    struct Node { uint32_t level, hi, lo; };
    vector<Node> nodes;
    std::map<std::tuple<uint32_t,uint32_t,uint32_t>, uint32_t> uniq;
    std::map<std::pair<uint32_t,uint32_t>, uint32_t> or_cache;
    size_t cap;
    bool blown = false;

    explicit MiniBdd(size_t _cap) : cap(_cap) {
        nodes.push_back({UINT32_MAX, 0, 0}); // FALSE
        nodes.push_back({UINT32_MAX, 1, 1}); // TRUE
    }
    uint32_t mk(uint32_t level, uint32_t hi, uint32_t lo) {
        if (hi == lo) return hi;
        auto key = std::make_tuple(level, hi, lo);
        auto it = uniq.find(key);
        if (it != uniq.end()) return it->second;
        if (nodes.size() >= cap) { blown = true; return 0; }
        nodes.push_back({level, hi, lo});
        uniq[key] = nodes.size() - 1;
        return nodes.size() - 1;
    }
    uint32_t bdd_or(uint32_t a, uint32_t b) {
        if (blown) return 0;
        if (a == 1 || b == 1) return 1;
        if (a == 0) return b;
        if (b == 0) return a;
        if (a == b) return a;
        if (a > b) std::swap(a, b);
        auto key = std::make_pair(a, b);
        auto it = or_cache.find(key);
        if (it != or_cache.end()) return it->second;
        const uint32_t la = nodes[a].level, lb = nodes[b].level;
        const uint32_t l = std::min(la, lb);
        const uint32_t ahi = (la == l) ? nodes[a].hi : a;
        const uint32_t alo = (la == l) ? nodes[a].lo : a;
        const uint32_t bhi = (lb == l) ? nodes[b].hi : b;
        const uint32_t blo = (lb == l) ? nodes[b].lo : b;
        const uint32_t hi = bdd_or(ahi, bhi);
        const uint32_t lo = bdd_or(alo, blo);
        const uint32_t r = mk(l, hi, lo);
        or_cache[key] = r;
        return r;
    }
    // Cube given as (level, positive?) pairs sorted by level ascending.
    uint32_t cube(const vector<std::pair<uint32_t,bool>>& cs) {
        uint32_t acc = 1;
        for (size_t i = cs.size(); i-- > 0; ) {
            acc = cs[i].second ? mk(cs[i].first, acc, 0)
                               : mk(cs[i].first, 0, acc);
            if (blown) return 0;
        }
        return acc;
    }
    // Live nodes reachable from root.
    size_t live(uint32_t root) const {
        if (root <= 1) return 0;
        std::set<uint32_t> seen;
        vector<uint32_t> todo{root};
        while (!todo.empty()) {
            uint32_t n = todo.back(); todo.pop_back();
            if (n <= 1 || !seen.insert(n).second) continue;
            todo.push_back(nodes[n].hi);
            todo.push_back(nodes[n].lo);
        }
        return seen.size();
    }
};

// BDD size of OR(cubes) under a given var order (level = position in order).
// Returns (live nodes, blown?).
static std::pair<size_t,bool> bdd_size_of_run(
        const vector<Cube>& cubes, const vector<uint32_t>& var_order, size_t cap) {
    std::map<uint32_t, uint32_t> level_of;
    for (uint32_t i = 0; i < var_order.size(); i++) level_of[var_order[i]] = i;
    MiniBdd bdd(cap);
    uint32_t acc = 0;
    for (const auto& c : cubes) {
        vector<std::pair<uint32_t,bool>> cs;
        cs.reserve(c.size());
        for (auto l : c) cs.push_back({level_of.at(l / 2), (l & 1) == 0});
        std::sort(cs.begin(), cs.end());
        acc = bdd.bdd_or(acc, bdd.cube(cs));
        if (bdd.blown) return {0, true};
    }
    return {bdd.live(acc), false};
}

// Adaptive greedy trie: branch on the most frequent literal at each step;
// counts decision nodes.
static size_t adaptive_trie_nodes(vector<Cube> cubes) {
    if (cubes.empty()) return 0;
    // Terminal: sum of remaining literal counts (each lit = one AND edge).
    size_t total = 0;
    std::map<uint32_t, size_t> f;
    for (const auto& c : cubes) for (auto l : c) f[l]++;
    if (f.empty()) return 0;
    uint32_t best = 0; size_t bestf = 0;
    for (auto& [l, cnt] : f) if (cnt > bestf) { bestf = cnt; best = l; }
    if (bestf <= 1) {
        for (const auto& c : cubes) total += c.size();
        return total;
    }
    vector<Cube> with, without;
    for (auto& c : cubes) {
        auto it = std::find(c.begin(), c.end(), best);
        if (it != c.end()) { c.erase(it); with.push_back(std::move(c)); }
        else without.push_back(std::move(c));
    }
    // 1 node for the factored literal + recursion
    return 1 + adaptive_trie_nodes(std::move(with)) + adaptive_trie_nodes(std::move(without));
}

// Espresso-style EXPAND via SAT cores: if c -> cover\c (UNSAT), the conflict
// core is a shorter cube c' replacing c without changing the function.
static vector<Cube> sat_expand_run(const vector<Cube>& cubes, size_t& n_expanded,
                                   size_t& n_sat_kept) {
    uint32_t max_var = 0;
    for (const auto& c : cubes)
        for (auto l : c) max_var = std::max(max_var, l / 2);
    CMSat::SATSolver s;
    s.new_vars(max_var + 1 + cubes.size());
    const uint32_t sel0 = max_var + 1; // selector var for clause i = sel0+i
    // clause_i = ~c_i OR s_i  (assume ~s_i to activate)
    for (size_t i = 0; i < cubes.size(); i++) {
        vector<CMSat::Lit> cl;
        cl.reserve(cubes[i].size() + 1);
        for (auto l : cubes[i]) cl.push_back(CMSat::Lit(l / 2, (l & 1) == 0)); // ~lit
        cl.push_back(CMSat::Lit(sel0 + i, false));
        s.add_clause(cl);
    }
    vector<Cube> out;
    n_expanded = n_sat_kept = 0;
    vector<CMSat::Lit> assumps;
    for (size_t i = 0; i < cubes.size(); i++) {
        assumps.clear();
        for (auto l : cubes[i]) assumps.push_back(CMSat::Lit(l / 2, (l & 1) != 0));
        for (size_t j = 0; j < cubes.size(); j++)
            if (j != i) assumps.push_back(CMSat::Lit(sel0 + j, true)); // activate
        const auto ret = s.solve(&assumps);
        if (ret != CMSat::l_False) { out.push_back(cubes[i]); n_sat_kept++; continue; }
        // Core: conflict lits are negations of failed assumptions.
        Cube c2;
        for (const auto& l : s.get_conflict()) {
            const uint32_t v = l.var();
            if (v >= sel0) continue;
            c2.push_back(v * 2 + (l.sign() ? 0u : 1u)); // ~conflict lit = orig
        }
        std::sort(c2.begin(), c2.end());
        c2.erase(std::unique(c2.begin(), c2.end()), c2.end());
        if (c2.size() < cubes[i].size()) n_expanded++;
        out.push_back(std::move(c2));
    }
    return out;
}

// Dedup + single-cube containment reduction (general cube absorbs supersets).
static vector<Cube> reduce_cover(vector<Cube> cs) {
    std::set<Cube> uniqs(cs.begin(), cs.end());
    vector<Cube> u(uniqs.begin(), uniqs.end());
    std::sort(u.begin(), u.end(), [](const Cube& a, const Cube& b) {
        return a.size() < b.size();
    });
    vector<Cube> kept;
    for (const auto& c : u) {
        bool absorbed = false;
        for (const auto& k : kept)
            if (subset_of(k, c)) { absorbed = true; break; }
        if (!absorbed) kept.push_back(c);
    }
    return kept;
}

// ===== Exact emitted-AIG-size measurement for run rebuild strategies =====
// Builds real hash-consed AIGs and counts unique nodes.
struct EmitSim {
    std::map<std::tuple<uint64_t,bool,uint64_t,bool>, aig_lit> hash;
    std::map<uint32_t, aig_lit> lits;
    aig_lit lit(uint32_t l) {
        auto it = lits.find(l / 2);
        if (it == lits.end()) {
            it = lits.emplace(l / 2, AIG::new_lit(l / 2, false)).first;
        }
        return aig_lit(it->second.node, (l & 1) != 0);
    }
    aig_lit mk_and(aig_lit a, aig_lit b) {
        if (a->nid > b->nid || (a->nid == b->nid && a.neg && !b.neg)) std::swap(a, b);
        auto key = std::make_tuple(a->nid, a.neg, b->nid, b.neg);
        auto it = hash.find(key);
        if (it != hash.end()) return it->second;
        aig_lit r = AIG::new_and(a, b);
        if (r->type == AIGT::t_and) hash[key] = r;
        return r;
    }
    aig_lit mk_or(const aig_lit& a, const aig_lit& b) { return ~mk_and(~a, ~b); }
    // cube emitted right-deep, LAST literal deepest
    aig_lit cube(const Cube& order_sorted) {
        aig_lit acc = lit(order_sorted.back());
        for (size_t i = order_sorted.size() - 1; i-- > 0; )
            acc = mk_and(lit(order_sorted[i]), acc);
        return acc;
    }
};

// Strategy A (current): global-order suffix-shared cubes + balanced OR spine.
static size_t emit_suffix_spine(const vector<Cube>& cubes,
                                const std::map<uint32_t, size_t>& ord) {
    EmitSim em;
    vector<Cube> cs = cubes;
    for (auto& c : cs)
        std::sort(c.begin(), c.end(), [&](uint32_t a, uint32_t b) {
            return ord.at(a) > ord.at(b); // rarest first, most frequent deepest
        });
    std::sort(cs.begin(), cs.end());
    vector<aig_lit> roots;
    roots.reserve(cs.size());
    for (const auto& c : cs) roots.push_back(em.cube(c));
    std::function<aig_lit(size_t, size_t)> tree = [&](size_t lo, size_t hi) -> aig_lit {
        if (hi - lo == 1) return roots[lo];
        size_t mid = lo + (hi - lo) / 2;
        return em.mk_or(tree(lo, mid), tree(mid, hi));
    };
    aig_lit root = tree(0, cs.size());
    return AIG::count_aig_nodes_fast(root);
}

// Strategy B: adaptive greedy prefix factoring; terminals in the global order.
static size_t emit_adaptive_factored(const vector<Cube>& cubes,
                                     const std::map<uint32_t, size_t>& ord) {
    EmitSim em;
    std::function<aig_lit(vector<Cube>&&)> emit = [&](vector<Cube>&& cs) -> aig_lit {
        // Fold factor-splits iteratively (without-branch as loop).
        vector<std::pair<aig_lit, bool>> pending; // (lit or cube aig, is_factor)
        vector<aig_lit> factor_lits;
        vector<aig_lit> factor_bodies;
        vector<aig_lit> loose;
        while (true) {
            if (cs.empty()) break;
            if (cs.size() == 1) {
                Cube c = cs[0];
                std::sort(c.begin(), c.end(), [&](uint32_t a, uint32_t b) {
                    return ord.at(a) > ord.at(b);
                });
                loose.push_back(em.cube(c));
                break;
            }
            std::map<uint32_t, size_t> f;
            for (const auto& c : cs) for (auto l : c) f[l]++;
            uint32_t best = 0; size_t bestf = 0;
            for (auto& [l, cnt] : f)
                if (cnt > bestf || (cnt == bestf && l < best)) { bestf = cnt; best = l; }
            if (bestf <= 1) {
                for (auto& c : cs) {
                    std::sort(c.begin(), c.end(), [&](uint32_t a, uint32_t b) {
                        return ord.at(a) > ord.at(b);
                    });
                    loose.push_back(em.cube(c));
                }
                break;
            }
            vector<Cube> with, without;
            for (auto& c : cs) {
                auto it = std::find(c.begin(), c.end(), best);
                if (it != c.end()) { c.erase(it); with.push_back(std::move(c)); }
                else without.push_back(std::move(c));
            }
            // Empty residual: factor lit alone covers that branch
            bool has_empty = false;
            for (auto& c : with) if (c.empty()) has_empty = true;
            if (has_empty) {
                loose.push_back(em.lit(best));
            } else {
                factor_lits.push_back(em.lit(best));
                factor_bodies.push_back(emit(std::move(with)));
            }
            cs = std::move(without);
        }
        vector<aig_lit> terms;
        for (size_t i = 0; i < factor_lits.size(); i++)
            terms.push_back(em.mk_and(factor_lits[i], factor_bodies[i]));
        for (auto& l : loose) terms.push_back(l);
        if (terms.empty()) return aig_lit(); // unreachable for nonempty input
        aig_lit acc = terms[0];
        for (size_t i = 1; i < terms.size(); i++) acc = em.mk_or(acc, terms[i]);
        return acc;
    };
    vector<Cube> cs = cubes;
    aig_lit root = emit(std::move(cs));
    return AIG::count_aig_nodes_fast(root);
}

// Compact structural printer: node kind (by edge), subtree node count,
// chain-collapsed. Helps see what the non-chain tails are made of.
static void print_shape(const aig_lit& e, int depth, int max_depth) {
    for (int i = 0; i < depth; i++) cout << "  ";
    if (!e) { cout << "NULL" << endl; return; }
    if (e->type == AIGT::t_lit) {
        cout << (e.neg ? "~" : "") << "x" << (e->var + 1) << endl;
        return;
    }
    if (e->type == AIGT::t_const) {
        cout << (e.neg ? "FALSE" : "TRUE") << endl;
        return;
    }
    const bool is_or = e.neg;
    // Flatten same-op chain.
    vector<aig_lit> units;
    vector<aig_lit> todo{e};
    while (!todo.empty()) {
        aig_lit n = todo.back(); todo.pop_back();
        const aig_lit c1 = is_or ? ~n->l : n->l;
        const aig_lit c2 = is_or ? ~n->r : n->r;
        for (const aig_lit& c : {c1, c2}) {
            const bool same = c.node && c->type == AIGT::t_and
                && (is_or ? is_or_edge(c) : !c.neg);
            if (same) todo.push_back(c);
            else units.push_back(c);
        }
    }
    const size_t sz = AIG::count_aig_nodes_fast(e);
    size_t n_lits = 0, n_cubes = 0, n_other = 0;
    vector<aig_lit> others;
    for (const auto& u : units) {
        if (u->type == AIGT::t_lit) { n_lits++; continue; }
        Cube c;
        if (collect_cube(is_or ? u : ~u, c)) n_cubes++;
        else { n_other++; others.push_back(u); }
    }
    cout << (is_or ? "OR" : "AND") << "[" << sz << "] units:" << units.size()
         << " (lits:" << n_lits << " cubes:" << n_cubes
         << " other:" << n_other << ")" << endl;
    if (depth >= max_depth) return;
    for (const auto& o : others) print_shape(o, depth + 1, max_depth);
}

// Deep-dive one run: support, literal frequency, pairwise overlap, and
// trie-node simulations. Optionally writes a PLA file for espresso.
static void analyze_run(const vector<Cube>& cubes, const std::string& pla_fname) {
    // Support + literal frequencies
    std::map<uint32_t, size_t> lit_freq;
    std::set<uint32_t> support;
    size_t wsum = 0;
    for (const auto& c : cubes) {
        wsum += c.size();
        for (auto l : c) { lit_freq[l]++; support.insert(l / 2); }
    }
    cout << "  run: " << cubes.size() << " cubes, sum lits " << wsum
         << ", support " << support.size() << " vars, distinct lits "
         << lit_freq.size() << endl;

    // Frequency histogram (top literals)
    vector<std::pair<size_t, uint32_t>> freq;
    for (auto& [l, f] : lit_freq) freq.push_back({f, l});
    std::sort(freq.rbegin(), freq.rend());
    cout << "  top lit freq (of " << cubes.size() << "):";
    for (size_t i = 0; i < 10 && i < freq.size(); i++)
        cout << " " << freq[i].first;
    cout << endl;
    // Literals present in (nearly) every cube
    size_t in_all = 0, in_90 = 0;
    for (auto& [f, l] : freq) {
        if (f == cubes.size()) in_all++;
        if (f * 10 >= cubes.size() * 9) in_90++;
    }
    cout << "  lits in ALL cubes: " << in_all << "  in >=90%: " << in_90 << endl;

    // Pairwise overlap sample (adjacent + random-stride pairs)
    if (cubes.size() > 1) {
        size_t inter_sum = 0, n = 0;
        auto isect = [](const Cube& a, const Cube& b) {
            size_t i = 0, j = 0, cnt = 0;
            while (i < a.size() && j < b.size()) {
                if (a[i] == b[j]) { cnt++; i++; j++; }
                else if (a[i] < b[j]) i++;
                else j++;
            }
            return cnt;
        };
        for (size_t i = 0; i + 1 < cubes.size(); i++) {
            inter_sum += isect(cubes[i], cubes[i+1]); n++;
        }
        cout << "  avg overlap of ADJACENT cubes: "
             << (double)inter_sum / (double)n << " lits" << endl;
        inter_sum = 0; n = 0;
        const size_t stride = cubes.size() / 2 + 1;
        for (size_t i = 0; i < cubes.size(); i++) {
            size_t j = (i + stride) % cubes.size();
            if (j == i) continue;
            inter_sum += isect(cubes[i], cubes[j]); n++;
        }
        cout << "  avg overlap of RANDOM pairs:   "
             << (double)inter_sum / (double)n << " lits" << endl;
    }

    // Trie simulation: nodes needed under a canonical literal order (var-id
    // and freq-desc).
    auto trie_nodes = [&](const std::map<uint32_t, size_t>& order_of) {
        std::set<vector<uint32_t>> prefixes;
        for (const auto& c : cubes) {
            Cube s = c;
            std::sort(s.begin(), s.end(), [&](uint32_t a, uint32_t b) {
                return order_of.at(a) < order_of.at(b);
            });
            vector<uint32_t> pref;
            for (auto l : s) { pref.push_back(l); prefixes.insert(pref); }
        }
        return prefixes.size();
    };
    std::map<uint32_t, size_t> ord_var, ord_freq;
    for (auto& [l, f] : lit_freq) ord_var[l] = l;
    // Most frequent literal first (deepest shared prefix)
    for (size_t i = 0; i < freq.size(); i++) ord_freq[freq[i].second] = i;
    cout << "  raw AND nodes (sum w-1):        " << (wsum - cubes.size()) << endl;
    cout << "  trie nodes, var-id order:       " << trie_nodes(ord_var) << endl;
    cout << "  trie nodes, freq-desc order:    " << trie_nodes(ord_freq) << endl;
    cout << "  adaptive-trie nodes:            " << adaptive_trie_nodes(cubes) << endl;
    cout << "  EMIT suffix+spine (current):    " << emit_suffix_spine(cubes, ord_freq) << endl;
    cout << "  EMIT adaptive factored:         " << emit_adaptive_factored(cubes, ord_freq) << endl;

    // BDD size under several variable orders
    {
        std::map<uint32_t, size_t> var_freq;
        for (auto& [l, f] : lit_freq) var_freq[l / 2] += f;
        vector<std::pair<size_t, uint32_t>> vf;
        for (auto& [v, f] : var_freq) vf.push_back({f, v});
        std::sort(vf.rbegin(), vf.rend());
        vector<uint32_t> ord_fdesc, ord_fasc, ord_vid;
        for (auto& [f, v] : vf) ord_fdesc.push_back(v);
        ord_fasc = ord_fdesc;
        std::reverse(ord_fasc.begin(), ord_fasc.end());
        for (auto& [v, f] : var_freq) ord_vid.push_back(v);
        constexpr size_t kCap = 2'000'000;
        auto [b1, x1] = bdd_size_of_run(cubes, ord_fdesc, kCap);
        auto [b2, x2] = bdd_size_of_run(cubes, ord_fasc, kCap);
        auto [b3, x3] = bdd_size_of_run(cubes, ord_vid, kCap);
        cout << "  BDD nodes, freq-desc order:     " << (x1 ? std::string("BLOWN") : std::to_string(b1)) << endl;
        cout << "  BDD nodes, freq-asc order:      " << (x2 ? std::string("BLOWN") : std::to_string(b2)) << endl;
        cout << "  BDD nodes, var-id order:        " << (x3 ? std::string("BLOWN") : std::to_string(b3)) << endl;
    }

    // Espresso EXPAND via SAT cores + containment reduction
    {
        const double t0 = cpuTime();
        size_t n_exp = 0, n_sat = 0;
        auto expanded = sat_expand_run(cubes, n_exp, n_sat);
        auto reduced = reduce_cover(expanded);
        size_t wsum2 = 0;
        for (const auto& c : reduced) wsum2 += c.size();
        cout << "  SAT-EXPAND: " << cubes.size() << " -> " << reduced.size()
             << " cubes (expanded " << n_exp << ", SAT-kept " << n_sat
             << "), sum lits " << wsum2
             << ", avg w " << (reduced.empty() ? 0.0 : (double)wsum2 / reduced.size())
             << ", T: " << (cpuTime() - t0) << endl;
        // Structure sizes on the reduced cover
        std::map<uint32_t, size_t> lf2;
        for (const auto& c : reduced) for (auto l : c) lf2[l]++;
        vector<std::pair<size_t, uint32_t>> fq2;
        for (auto& [l, f2] : lf2) fq2.push_back({f2, l});
        std::sort(fq2.rbegin(), fq2.rend());
        std::map<uint32_t, size_t> ord2;
        for (size_t i = 0; i < fq2.size(); i++) ord2[fq2[i].second] = i;
        auto trie2 = [&]() {
            std::set<vector<uint32_t>> prefixes;
            for (const auto& c : reduced) {
                Cube ss = c;
                std::sort(ss.begin(), ss.end(), [&](uint32_t a, uint32_t b) {
                    return ord2.at(a) < ord2.at(b);
                });
                vector<uint32_t> pref;
                for (auto l : ss) { pref.push_back(l); prefixes.insert(pref); }
            }
            return prefixes.size();
        };
        cout << "  after expand: trie freq-desc:   " << trie2()
             << "  adaptive-trie: " << adaptive_trie_nodes(reduced) << endl;
    }

    if (!pla_fname.empty()) {
        // PLA for espresso: columns = support vars (sorted)
        vector<uint32_t> sup(support.begin(), support.end());
        std::map<uint32_t, size_t> col;
        for (size_t i = 0; i < sup.size(); i++) col[sup[i]] = i;
        FILE* f = fopen(pla_fname.c_str(), "w");
        fprintf(f, ".i %zu\n.o 1\n.p %zu\n", sup.size(), cubes.size());
        for (const auto& c : cubes) {
            std::string row(sup.size(), '-');
            for (auto l : c) row[col[l / 2]] = (l & 1) ? '0' : '1';
            fprintf(f, "%s 1\n", row.c_str());
        }
        fprintf(f, ".e\n");
        fclose(f);
        cout << "  wrote PLA: " << pla_fname << endl;
    }
}

// ===== Collapse-to-SOP analysis =====
// OR view collapse: e interpreted as an OR of its flattened operands.
static bool collapse_rec(const aig_lit& e, vector<Cube>& out,
                         size_t max_cubes, size_t max_w);

// SOP of a single edge (any polarity).
static bool sop_of_edge(const aig_lit& e, vector<Cube>& out,
                        size_t max_cubes, size_t max_w) {
    if (!e) return false;
    if (e->type == AIGT::t_const) {
        if (!e.neg) out.push_back({});
        return true;
    }
    if (e->type == AIGT::t_lit) {
        out.push_back({e->var * 2 + (e.neg ? 1u : 0u)});
        return true;
    }
    if (e.neg) return collapse_rec(e, out, max_cubes, max_w); // OR node
    // AND node: product of the two children's SOPs.
    vector<Cube> a, b;
    if (!sop_of_edge(e->l, a, max_cubes, max_w)) return false;
    if (!sop_of_edge(e->r, b, max_cubes, max_w)) return false;
    if (a.size() * b.size() > max_cubes) return false;
    for (const auto& ca : a) {
        for (const auto& cb : b) {
            Cube c = ca;
            c.insert(c.end(), cb.begin(), cb.end());
            std::sort(c.begin(), c.end());
            c.erase(std::unique(c.begin(), c.end()), c.end());
            bool is_false = false;
            for (size_t i = 0; i + 1 < c.size(); i++)
                if ((c[i] ^ 1u) == c[i+1]) { is_false = true; break; }
            if (is_false) continue;
            if (c.size() > max_w) return false;
            out.push_back(std::move(c));
            if (out.size() > max_cubes) return false;
        }
    }
    return true;
}

static bool collapse_rec(const aig_lit& e, vector<Cube>& out,
                         size_t max_cubes, size_t max_w) {
    // e is an OR edge: union of operand SOPs.
    vector<aig_lit> ops;
    {
        vector<aig_lit> todo{e};
        while (!todo.empty()) {
            aig_lit n = todo.back(); todo.pop_back();
            for (const aig_lit c : {~n->l, ~n->r}) {
                if (!c.node) continue;
                if (is_or_edge(c)) todo.push_back(c);
                else ops.push_back(c);
            }
        }
    }
    for (const auto& op : ops) {
        if (!sop_of_edge(op, out, max_cubes, max_w)) return false;
        if (out.size() > max_cubes) return false;
    }
    return true;
}

// Iterated dedup + containment + distance-1 merge on a cover.
static vector<Cube> minimize_cover(vector<Cube> cs, size_t& n_d1_merges) {
    bool changed = true;
    while (changed) {
        changed = false;
        cs = reduce_cover(std::move(cs));
        // distance-1 merge: identical except one complemented literal.
        std::map<Cube, uint32_t> half; // cube-with-slot-removed -> lit
        for (size_t i = 0; i < cs.size() && !changed; i++) {
            for (size_t j = i + 1; j < cs.size(); j++) {
                if (distance1(cs[i], cs[j])) {
                    // merge: drop the complemented literal pair
                    Cube m;
                    for (size_t k = 0; k < cs[i].size(); k++)
                        if (cs[i][k] == cs[j][k]) m.push_back(cs[i][k]);
                    cs[i] = std::move(m);
                    cs.erase(cs.begin() + j);
                    n_d1_merges++;
                    changed = true;
                    break;
                }
            }
        }
    }
    return cs;
}

// Dump the AIG of one def as a Graphviz DOT graph.
//   - AND nodes         : filled blue boxes (shared, one per node)
//   - variable inputs   : non-filled boxes with the (1-indexed) var number;
//                         NOT shared -- one fresh box per use, so the graph is
//                         a readable tree at the leaves rather than a hairball
//   - complemented edges : a filled circle (dot arrowhead)
//   - the output        : a box at the top labelled with the output variable
static void write_aig_dot(const aig_lit& root, uint32_t out_var_0idx,
                          const std::string& dot_fname) {
    FILE* f = fopen(dot_fname.c_str(), "w");
    if (!f) {
        std::cerr << "ERROR: cannot open " << dot_fname << " for writing" << endl;
        return;
    }
    fprintf(f, "digraph aig {\n");
    fprintf(f, "  rankdir=TB;\n");
    fprintf(f, "  node [fontname=\"Helvetica\"];\n");
    // Output node, pinned to the top rank.
    fprintf(f, "  { rank=source; out [label=\"var %u\", shape=box, "
               "style=rounded, penwidth=2]; }\n", out_var_0idx + 1);

    std::set<const AIG*> seen_and;  // AND nodes are shared (keyed by pointer)
    uint64_t leaf_id = 0;           // unique id for per-use leaf (input/const) boxes

    // Emit the edge parent -> child. AND children reference the shared node;
    // variable / const children get a fresh, unshared leaf box each time.
    auto emit_edge = [&](const std::string& parent, const aig_lit& ch) {
        std::string cname;
        if (ch->type == AIGT::t_and) {
            cname = "n" + std::to_string(ch->nid);
        } else {
            cname = "l" + std::to_string(leaf_id++);
            if (ch->type == AIGT::t_lit)
                fprintf(f, "  %s [label=\"%u\", shape=box];\n", cname.c_str(), ch->var + 1);
            else // t_const (TRUE; complemented edge = FALSE)
                fprintf(f, "  %s [label=\"1\", shape=box];\n", cname.c_str());
        }
        fprintf(f, "  %s -> %s%s;\n", parent.c_str(), cname.c_str(),
                ch.neg ? " [arrowhead=dot, arrowsize=2]" : "");
    };

    std::function<void(const AIG*)> dfs = [&](const AIG* n) {
        if (!n || n->type != AIGT::t_and) return; // leaves handled at the edge
        if (!seen_and.insert(n).second) return;
        fprintf(f, "  n%llu [label=\"\", shape=box, style=filled, "
                   "fillcolor=\"steelblue\"];\n", (unsigned long long)n->nid);
        const std::string parent = "n" + std::to_string(n->nid);
        for (const aig_lit& ch : {n->l, n->r}) {
            dfs(ch.get());
            emit_edge(parent, ch);
        }
    };
    dfs(root.get());
    // Edge from the output to the def's root (complemented if root is negated).
    emit_edge("out", root);
    fprintf(f, "}\n");
    fclose(f);
}

int main(int argc, char** argv) {
    argparse::ArgumentParser program("aig_chain_stats", "1.0",
            argparse::default_arguments::help);
    program.add_description(
        "Repair-chain shape analyzer: loads a --dumprestartaig dump and prints "
        "per-def and aggregate stats on the Manthan repair-chain structure.");
    program.add_argument("-r", "--rewrite")
        .flag()
        .help("run AIGRewriter::rewrite_all on the defs first");
    program.add_argument("-R", "--verify")
        .flag()
        .help("rewrite, then SAT-miter each changed def to prove equivalence");
    program.add_argument("-c", "--collapse")
        .flag()
        .help("collapse each top def to a flat SOP and report refactored size");
    program.add_argument("--all")
        .flag()
        .help("print ALL var defs, not just the top ones (overrides --top)");
    program.add_argument("-n", "--top")
        .default_value(10).scan<'i', int>()
        .help("number of top defs to print / analyze");
    program.add_argument("-t", "--top-filter")
        .default_value(0).scan<'i', int>()
        .help("keep only the K biggest defs (approximates the in-run to_define "
              "population at a Manthan restart)");
    program.add_argument("-T", "--drop-top")
        .default_value(0).scan<'i', int>()
        .help("drop the K biggest defs, keep the rest");
    program.add_argument("-B", "--blif")
        .default_value(std::string(""))
        .help("dump the (possibly rewritten) union DAG as BLIF to this file");
    program.add_argument("--deep")
        .default_value(0).scan<'i', int>()
        .help("deep-dive the largest run of this 1-indexed var");
    program.add_argument("--viz")
        .default_value(0).scan<'i', int>()
        .help("dump the AIG of this 1-indexed var as DOT + PDF");
    program.add_argument("--pla")
        .default_value(std::string(""))
        .help("write the deep-dived run as a PLA file for espresso");
    program.add_argument("file").help("input AIG dump");

    try {
        program.parse_args(argc, argv);
    } catch (const std::exception& err) {
        std::cerr << err.what() << endl << program;
        return 1;
    }

    const bool do_verify = program.get<bool>("--verify");
    const bool do_rewrite = program.get<bool>("--rewrite") || do_verify;
    const bool do_collapse = program.get<bool>("--collapse");
    const bool do_all = program.get<bool>("--all");
    // With --all, print/analyze every def rather than just the top ones.
    const int top_n = do_all ? std::numeric_limits<int>::max()
                             : program.get<int>("--top");
    const std::string blif_out = program.get<std::string>("--blif");
    // -t keeps the top K, -T drops the top K (encoded as a negative filter).
    int top_filter = program.get<int>("--top-filter");
    if (top_filter == 0) top_filter = -program.get<int>("--drop-top");
    const std::string fname = program.get<std::string>("file");
    const int deep_var = program.get<int>("--deep");
    const int viz_var = program.get<int>("--viz");
    const std::string pla_fname = program.get<std::string>("--pla");
    // These take a variable number; a bare "--deep"/"--viz" resolves to 0 and
    // would otherwise silently do nothing. Reject that explicitly.
    if (program.is_used("--deep") && deep_var <= 0) {
        std::cerr << "ERROR: --deep needs a 1-indexed variable number, e.g. --deep 861" << endl;
        return 1;
    }
    if (program.is_used("--viz") && viz_var <= 0) {
        std::cerr << "ERROR: --viz needs a 1-indexed variable number, e.g. --viz 861" << endl;
        return 1;
    }
    auto fg = std::make_unique<FGenMpz>();
    SimplifiedCNF cnf(fg.get());
    cnf.read_aig_defs_from_file(fname);

    // Local def list (var, aig) so we can filter to the top K defs; the
    // in-run Manthan restart compaction only rewrites the to_define chain
    // AIGs, which -t approximates.
    vector<uint32_t> def_vars;
    vector<aig_lit> defs_local;
    for (uint32_t v = 0; v < cnf.num_defs(); v++) {
        if (!cnf.get_def(v)) continue;
        def_vars.push_back(v);
        defs_local.push_back(cnf.get_def(v));
    }
    if (top_filter != 0) {
        vector<std::pair<size_t, size_t>> sizes; // (nodes, idx)
        for (size_t i = 0; i < defs_local.size(); i++)
            sizes.push_back({AIG::count_aig_nodes_fast(defs_local[i]), i});
        std::sort(sizes.rbegin(), sizes.rend());
        std::set<size_t> keep;
        if (top_filter > 0) {
            for (int i = 0; i < top_filter && i < (int)sizes.size(); i++)
                keep.insert(sizes[i].second);
        } else { // -T: drop the top K, keep the rest
            for (size_t i = (size_t)(-top_filter); i < sizes.size(); i++)
                keep.insert(sizes[i].second);
        }
        vector<uint32_t> fv;
        vector<aig_lit> fd;
        for (size_t i = 0; i < defs_local.size(); i++) {
            if (!keep.count(i)) continue;
            fv.push_back(def_vars[i]);
            fd.push_back(defs_local[i]);
        }
        def_vars = std::move(fv);
        defs_local = std::move(fd);
        cout << "kept top " << defs_local.size() << " defs" << endl;
    }
    // -R: keep pre-rewrite copies for SAT-miter equivalence checking.
    vector<aig_lit> before_defs;
    if (do_verify) before_defs = defs_local;
    if (do_rewrite) {
        AIGRewriter rw;
        rw.rewrite_all(defs_local, 2, true);
        if (getenv("CHAIN_STATS_TWICE")) {
            AIGRewriter rw2;
            rw2.rewrite_all(defs_local, 2, true);
        }
    }
    if (do_verify) {
        // SAT miter per changed def: old XOR new must be UNSAT.
        size_t checked = 0, changed = 0;
        for (size_t i = 0; i < defs_local.size(); i++) {
            const uint32_t v = def_vars[i];
            const auto& oldd = before_defs[i];
            const auto& newd = defs_local[i];
            if (!oldd || !newd) { if (oldd != newd) { cout << "DEF DISAPPEARED v=" << v+1 << endl; return 1; } continue; }
            if (oldd == newd) continue;
            changed++;
            CMSat::SATSolver s;
            CMSat::Lit true_lit;
            bool have_true = false;
            auto true_fn = [&]() {
                if (!have_true) {
                    s.new_var();
                    true_lit = CMSat::Lit(s.nVars()-1, false);
                    s.add_clause({true_lit});
                    have_true = true;
                }
                return true_lit;
            };
            auto leaf_fn = [&](uint32_t var) {
                while (s.nVars() <= var) s.new_var();
                return CMSat::Lit(var, false);
            };
            CMSat::Lit a = AIG::tseitin_encode(oldd, s, true_fn, leaf_fn);
            CMSat::Lit b = AIG::tseitin_encode(newd, s, true_fn, leaf_fn);
            // a != b?
            s.new_var();
            CMSat::Lit diff(s.nVars()-1, false);
            s.add_clause({~diff, a, b});
            s.add_clause({~diff, ~a, ~b});
            s.add_clause({diff});
            if (s.solve() != CMSat::l_False) {
                cout << "MITER SAT: def v=" << v+1 << " NOT equivalent after rewrite!" << endl;
                return 1;
            }
            checked++;
        }
        cout << "verify: " << checked << " changed defs proven equivalent (of "
             << changed << " changed)" << endl;
    }

    if (!blif_out.empty()) {
        // Dump the (possibly rewritten) union DAG as BLIF for abc experiments.
        FILE* f = fopen(blif_out.c_str(), "w");
        fprintf(f, ".model aig_defs\n");
        std::map<const AIG*, std::string> name;
        std::set<uint32_t> inputs;
        vector<const AIG*> order;
        {
            std::set<const AIG*> seen;
            std::function<void(const AIG*)> dfs = [&](const AIG* n) {
                if (!n || !seen.insert(n).second) return;
                if (n->type == AIGT::t_lit) { inputs.insert(n->var); return; }
                if (n->type == AIGT::t_const) return;
                dfs(n->l.get());
                dfs(n->r.get());
                order.push_back(n);
            };
            for (const auto& d : defs_local) if (d) dfs(d.get());
        }
        fprintf(f, ".inputs");
        for (auto v : inputs) fprintf(f, " x%u", v + 1);
        fprintf(f, "\n.outputs");
        for (size_t i = 0; i < def_vars.size(); i++)
            if (defs_local[i]) fprintf(f, " o%u", def_vars[i] + 1);
        fprintf(f, "\n");
        bool have_const = false;
        auto nm = [&](const AIG* n) -> std::string {
            if (n->type == AIGT::t_lit) return "x" + std::to_string(n->var + 1);
            if (n->type == AIGT::t_const) { have_const = true; return "CONST1"; }
            return "n" + std::to_string(n->nid);
        };
        for (const AIG* n : order) {
            fprintf(f, ".names %s %s %s\n%c%c 1\n",
                    nm(n->l.get()).c_str(), nm(n->r.get()).c_str(), nm(n).c_str(),
                    n->l.neg ? '0' : '1', n->r.neg ? '0' : '1');
        }
        for (size_t i = 0; i < def_vars.size(); i++) {
            const auto& d = defs_local[i];
            if (!d) continue;
            fprintf(f, ".names %s o%u\n%c 1\n", nm(d.get()).c_str(),
                    def_vars[i] + 1, d.neg ? '0' : '1');
        }
        if (have_const) fprintf(f, ".names CONST1\n1\n");
        fprintf(f, ".end\n");
        fclose(f);
        cout << "wrote BLIF: " << blif_out << " (" << order.size()
             << " AND nodes)" << endl;
    }

    struct DefInfo {
        uint32_t var;
        size_t nodes, layers, runs, cubes;
        size_t dup = 0, subs = 0, d1 = 0;
        size_t max_run = 0;
        double avg_w = 0;
    };
    vector<DefInfo> infos;
    const size_t tot_nodes_union = AIG::count_aig_nodes_fast(defs_local);
    std::map<Cube, size_t> global_cubes; // cross-def duplication census

    for (size_t di = 0; di < defs_local.size(); di++) {
        const auto& d = defs_local[di];
        if (!d) continue;
        DefInfo in;
        in.var = def_vars[di];
        in.nodes = AIG::count_aig_nodes_fast(d);
        vector<RunStats> runs;
        in.layers = walk_chain(d, runs);
        in.runs = runs.size();
        size_t cube_cnt = 0, wsum = 0;
        for (auto& r : runs) {
            in.max_run = std::max(in.max_run, r.cubes.size());
            cube_cnt += r.cubes.size();
            for (auto& c : r.cubes) { wsum += c.size(); global_cubes[c]++; }
            // Opportunity counts within the run.
            std::set<Cube> seen;
            for (auto& c : r.cubes) {
                if (!seen.insert(c).second) in.dup++;
            }
            vector<Cube> uniq(seen.begin(), seen.end());
            for (size_t i = 0; i < uniq.size(); i++)
                for (size_t j = 0; j < uniq.size(); j++) {
                    if (i == j) continue;
                    if (subset_of(uniq[i], uniq[j])) { in.subs++; break; }
                }
            for (size_t i = 0; i < uniq.size(); i++)
                for (size_t j = i+1; j < uniq.size(); j++)
                    if (distance1(uniq[i], uniq[j])) in.d1++;
        }
        in.cubes = cube_cnt;
        in.avg_w = cube_cnt ? (double)wsum / cube_cnt : 0;
        infos.push_back(in);
    }

    std::sort(infos.begin(), infos.end(),
              [](const DefInfo& a, const DefInfo& b) { return a.nodes > b.nodes; });

    size_t tot_cubes = 0, tot_dup = 0, tot_subs = 0, tot_d1 = 0, tot_layers = 0;
    size_t tot_standalone = 0;
    for (auto& in : infos) {
        tot_cubes += in.cubes; tot_dup += in.dup; tot_subs += in.subs;
        tot_d1 += in.d1; tot_layers += in.layers;
        tot_standalone += in.nodes;
    }
    size_t multi_def_cubes = 0, multi_def_insts = 0;
    for (const auto& [c, cnt] : global_cubes)
        if (cnt > 1) { multi_def_cubes++; multi_def_insts += cnt; }
    cout << "defs: " << infos.size()
         << "  union nodes: " << tot_nodes_union
         << "  sum standalone: " << tot_standalone
         << "  chain layers: " << tot_layers
         << "  cubes: " << tot_cubes
         << "  dup: " << tot_dup
         << "  subsumed: " << tot_subs
         << "  dist1-pairs: " << tot_d1 << endl;
    cout << "global cube census: distinct " << global_cubes.size()
         << "  appearing >1x: " << multi_def_cubes
         << " (covering " << multi_def_insts << " instances)" << endl;
    cout << (do_all ? "all defs by node count:" : "top defs by node count:") << endl;
    cout << "  column legend (per def):" << endl;
    cout << "    layers = number of AND-chain layers walked in the decision-list chain" << endl;
    cout << "    runs   = number of maximal same-operator (OR/AND) runs in that chain" << endl;
    cout << "    maxrun = cube count of the largest single run" << endl;
    cout << "    cubes  = total cubes across all runs" << endl;
    cout << "    avg_w  = average cube width (literals per cube)" << endl;
    cout << "    dup    = duplicate cubes within a run (exact repeats)" << endl;
    cout << "    subs   = cubes subsumed by another cube in the same run" << endl;
    cout << "    d1     = distance-1 cube pairs (differ in one complemented literal)" << endl;
    cout << "  var    nodes layers  runs maxrun  cubes  avg_w    dup   subs     d1" << endl;
    for (int i = 0; i < top_n && i < (int)infos.size(); i++) {
        auto& in = infos[i];
        printf("  %-5u %7zu %6zu %5zu %6zu %6zu %6.1f %6zu %6zu %6zu\n",
               in.var+1, in.nodes, in.layers, in.runs, in.max_run,
               in.cubes, in.avg_w, in.dup, in.subs, in.d1);
    }

    {
        // FRAIG potential estimate: random-simulate the union DAG with 4x64
        // deterministic patterns; nodes sharing a (polarity-normalized)
        // signature are candidate functional merges.
        auto sm64 = [](uint64_t x) {
            x += 0x9e3779b97f4a7c15ULL;
            x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
            x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
            return x ^ (x >> 31);
        };
        constexpr int W = 4;
        using Sig = std::array<uint64_t, W>;
        std::map<const AIG*, Sig> sig;
        std::map<Sig, size_t> classes;
        size_t n_nodes = 0, n_const = 0;
        std::function<Sig(const aig_lit&)> sim = [&](const aig_lit& e) -> Sig {
            Sig s;
            const AIG* n = e.get();
            auto it = sig.find(n);
            if (it != sig.end()) s = it->second;
            else {
                if (n->type == AIGT::t_const) s.fill(~0ULL);
                else if (n->type == AIGT::t_lit)
                    for (int w = 0; w < W; w++) s[w] = sm64(n->var * 977 + w);
                else {
                    const Sig a = sim(n->l);
                    const Sig b = sim(n->r);
                    for (int w = 0; w < W; w++) s[w] = a[w] & b[w];
                }
                sig[n] = s;
                if (n->type == AIGT::t_and) {
                    n_nodes++;
                    bool all0 = true, all1 = true;
                    for (int w = 0; w < W; w++) {
                        if (s[w]) all0 = false;
                        if (~s[w]) all1 = false;
                    }
                    if (all0 || all1) n_const++;
                    else {
                        Sig norm = s;
                        if (s[0] & 1) for (int w = 0; w < W; w++) norm[w] = ~s[w];
                        classes[norm]++;
                    }
                }
            }
            if (e.neg) for (int w = 0; w < W; w++) s[w] = ~s[w];
            return s;
        };
        for (const auto& d : defs_local)
            if (d) sim(d);
        size_t mergeable = 0;
        for (const auto& [s, cnt] : classes) mergeable += cnt - 1;
        cout << "FRAIG potential: AND nodes " << n_nodes
             << "  const-candidates " << n_const
             << "  sig-merge candidates " << mergeable << endl;
    }

    if (do_collapse) {
        // Collapse each top def to a flat SOP (with caps), minimize the
        // cover, and report the re-emitted factored size vs the current one.
        cout << "collapse-to-SOP analysis (top " << top_n << " defs):" << endl;
        cout << "  var    nodes    sop_cubes  min_cubes  d1merges  refactored" << endl;
        std::map<uint32_t, size_t> var2idx;
        for (size_t i = 0; i < def_vars.size(); i++) var2idx[def_vars[i]] = i;
        for (int i = 0; i < top_n && i < (int)infos.size(); i++) {
            const auto& in = infos[i];
            const auto& d = defs_local[var2idx.at(in.var)];
            vector<Cube> sop;
            const bool ok = sop_of_edge(d, sop, 20000, 64);
            if (!ok) {
                printf("  %-5u %7zu    BLOWN\n", in.var+1, in.nodes);
                continue;
            }
            const size_t raw_cubes = sop.size();
            size_t d1 = 0;
            sop = minimize_cover(std::move(sop), d1);
            size_t refac = 0;
            if (!sop.empty()) {
                std::map<uint32_t, size_t> lf, ord;
                for (const auto& c : sop) for (auto l : c) lf[l]++;
                vector<std::pair<size_t, uint32_t>> fq;
                for (auto& [l, f] : lf) fq.push_back({f, l});
                std::sort(fq.rbegin(), fq.rend());
                for (size_t k = 0; k < fq.size(); k++) ord[fq[k].second] = k;
                refac = emit_adaptive_factored(sop, ord);
            }
            printf("  %-5u %7zu %10zu %10zu %9zu %11zu\n",
                   in.var+1, in.nodes, raw_cubes, sop.size(), d1, refac);
        }
    }

    if (deep_var > 0) {
        aig_lit d;
        for (size_t i = 0; i < def_vars.size(); i++)
            if (def_vars[i] == (uint32_t)(deep_var - 1)) d = defs_local[i];
        if (!d) { cout << "deep var has no def" << endl; return 1; }
        vector<RunStats> runs;
        walk_chain(d, runs);
        cout << "deep dive var " << deep_var << " (" << runs.size() << " runs):" << endl;
        cout << "shape:" << endl;
        print_shape(d, 0, 8);
        if (!runs.empty()) {
            // largest run
            size_t best = 0;
            for (size_t i = 1; i < runs.size(); i++)
                if (runs[i].cubes.size() > runs[best].cubes.size()) best = i;
            cout << "  largest run op=" << runs[best].op << endl;
            analyze_run(runs[best].cubes, pla_fname);
        }
    }

    if (viz_var > 0) {
        aig_lit d;
        for (size_t i = 0; i < def_vars.size(); i++)
            if (def_vars[i] == (uint32_t)(viz_var - 1)) d = defs_local[i];
        if (!d) { cout << "viz var " << viz_var << " has no def" << endl; return 1; }
        const std::string dot_fname = fname + "-var" + std::to_string(viz_var) + ".dot";
        const std::string pdf_fname = fname + "-var" + std::to_string(viz_var) + ".pdf";
        write_aig_dot(d, viz_var - 1, dot_fname);
        const std::string cmd = "dot -Tpdf " + dot_fname + " -o " + pdf_fname;
        cout << "wrote DOT: " << dot_fname << endl;
        cout << "convert to PDF with: " << cmd << endl;
        const int rc = system(cmd.c_str());
        if (rc != 0) cout << "WARNING: '" << cmd << "' returned " << rc
                          << " (is graphviz installed?)" << endl;
        else cout << "wrote PDF: " << pdf_fname << endl;
    }

    if (do_rewrite) {
        // Dump the rewritten defs next to the input. rewrite_aigs() applies the
        // same deterministic AIGRewriter::rewrite_all to the cnf's own (full,
        // unfiltered) def set, so the file is a rewritten twin of the input.
        cnf.rewrite_aigs(0, true);
        const std::string out_fname = fname + "-rewritten.aig";
        cnf.write_aig_defs_to_file(out_fname);
        cout << "wrote rewritten AIG defs: " << out_fname << endl;
    }
    return 0;
}
