/*
 Arjun - CNF rewriting through AIG lifting

 Copyright (c) 2026, Mate Soos. MIT License.
 */

#include "cnf_rewrite.h"
#include "aig_rewrite.h"
#include "aig_to_cnf.h"
#include "aig_cnf_map.h"
#include "constants.h"
#include "time_mem.h"

#include <algorithm>
#include <functional>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <set>

using namespace ArjunNS;
using namespace ArjunInt;
using namespace CMSat;
using std::cout;
using std::endl;
using std::setw;
using std::vector;
using std::string;

const char* ArjunInt::gate_type_name(GateType t) {
    switch (t) {
        case GateType::AND: return "AND";
        case GateType::XOR: return "XOR";
        case GateType::ITE: return "ITE";
        case GateType::EQUIV: return "EQUIV";
        case GateType::IRREG: return "IRREG";
        default: return "?";
    }
}

uint32_t ArjunInt::fanin_bucket(uint32_t f) {
    if (f <= 4) return f == 0 ? 0 : f - 1;
    if (f <= 8) return 4;
    if (f <= 16) return 5;
    if (f <= 32) return 6;
    return 7;
}

const char* ArjunInt::fanin_bucket_name(uint32_t b) {
    static const char* names[kFaninBuckets] = {"1", "2", "3", "4", "5-8", "9-16", "17-32", "33+"};
    return b < kFaninBuckets ? names[b] : "?";
}

void CnfRwStats::print(int verb, const string& prefix) const {
    if (verb < 1) return;
    auto line = [&](const std::ostringstream& ss) {
        cout << "c o " << prefix << ss.str() << endl;
    };
    std::ostringstream ss;
    ss << "[cnfrw] " << std::left << setw(8) << "gate" << std::right
       << setw(9) << "cand" << setw(9) << "cand-in" << setw(9) << "sel"
       << setw(9) << "sel-in" << setw(9) << "avg-in" << setw(9) << "sel-cls";
    line(ss);
    for (size_t t = 0; t < (size_t)GateType::NUM; t++) {
        if (cand_gates[t] == 0) continue;
        std::ostringstream s2;
        s2 << "[cnfrw] " << std::left << setw(8) << gate_type_name((GateType)t) << std::right
           << setw(9) << cand_gates[t] << setw(9) << cand_inputs[t]
           << setw(9) << sel_gates[t] << setw(9) << sel_inputs[t]
           << setw(9) << std::fixed << std::setprecision(2)
           << safe_div(sel_inputs[t], sel_gates[t])
           << setw(9) << sel_clauses[t];
        line(s2);
    }
    for (size_t t = 0; t < (size_t)GateType::NUM; t++) {
        if (sel_gates[t] == 0) continue;
        std::ostringstream sh;
        sh << "[cnfrw] " << std::left << setw(8) << gate_type_name((GateType)t) << std::right << " fanin:";
        for (uint32_t b = 0; b < kFaninBuckets; b++) {
            if (fanin_hist[t][b] == 0) continue;
            sh << " " << fanin_bucket_name(b) << ":" << fanin_hist[t][b];
        }
        line(sh);
    }
    std::ostringstream s3;
    s3 << "[cnfrw] rejected: cl-conflict " << rej_clause_conflict
       << " var-defined " << rej_var_defined << " cycle " << rej_cycle
       << " | irreg tried " << irreg_tried << " taut-ok " << irreg_taut_ok
       << " bf-ok " << irreg_bf_ok << " too-big " << irreg_too_big;
    line(s3);
    std::ostringstream s4;
    s4 << "[cnfrw] outputs " << gate_outputs << " removable " << removable_outputs
       << " kept " << kept_outputs << " (dont-elim " << kept_dont_elim
       << " ext-use " << kept_external_use << ") leaves " << leaf_vars
       << " max-fanin " << max_fanin;
    line(s4);
    std::ostringstream s5;
    s5 << "[cnfrw] roots " << roots << " -> helper " << roots_helper
       << " shared " << roots_shared << " leaf " << roots_leaf << " dead-gates " << dead_gates
       << " | comps accepted " << comp_accepted << " (gain " << comp_gain_cost
       << ") rejected " << comp_rejected << " (would lose " << comp_rej_cost << ")"
       << " | enc won: aig2cnf " << enc_aig2cnf_won << " mapper " << enc_mapper_won
       << " | aig nodes " << aig_nodes_before << " -> " << aig_nodes_after
       << " (" << std::fixed << std::setprecision(1)
       << (aig_nodes_before ? 100.0 * (1.0 - (double)aig_nodes_after / (double)aig_nodes_before) : 0.0)
       << "% less) depth " << aig_max_depth;
    line(s5);
    std::ostringstream s6;
    s6 << "[cnfrw] cls removed " << cls_removed << " (lits " << lits_removed
       << ") added " << cls_added << " (lits " << lits_added << ") equiv-bins " << equiv_bins_added
       << " red-dropped " << red_cls_dropped
       << " | vars removed " << vars_removed << " added " << vars_added;
    line(s6);
    std::ostringstream s7;
    s7 << "[cnfrw] CNF vars " << vars_in << " -> " << vars_out
       << " cls " << cls_in << " -> " << cls_out
       << " lits " << lits_in << " -> " << lits_out
       << std::fixed << std::setprecision(1)
       << " (" << (vars_in ? 100.0 * ((double)vars_out / (double)vars_in - 1.0) : 0.0) << "% vars, "
       << (cls_in ? 100.0 * ((double)cls_out / (double)cls_in - 1.0) : 0.0) << "% cls, "
       << (lits_in ? 100.0 * ((double)lits_out / (double)lits_in - 1.0) : 0.0) << "% lits)";
    line(s7);
    std::ostringstream s8;
    s8 << "[cnfrw] T detect " << std::fixed << std::setprecision(2) << t_detect
       << " select " << t_select << " build " << t_build << " rewrite " << t_rewrite
       << " encode " << t_encode << " assemble " << t_assemble << " total " << t_total;
    line(s8);
}

uint64_t CnfRewrite::bin_key(Lit a, Lit b) {
    if (b < a) std::swap(a, b);
    return ((uint64_t)a.toInt() << 32) | (uint64_t)b.toInt();
}

uint64_t CnfRewrite::tern_key(Lit a, Lit b, Lit c) {
    uint32_t x[3] = {a.toInt(), b.toInt(), c.toInt()};
    std::sort(x, x + 3);
    uint64_t h = x[0];
    h = h * 0x9e3779b97f4a7c15ULL + x[1];
    h = h * 0xff51afd7ed558ccdULL + x[2];
    h ^= h >> 29;
    return h;
}

uint32_t CnfRewrite::find_bin(Lit a, Lit b) const {
    auto it = bin_map.find(bin_key(a, b));
    if (it == bin_map.end()) return no_cl;
    return it->second;
}

uint32_t CnfRewrite::find_tern(Lit a, Lit b, Lit c) const {
    auto it = tern_map.find(tern_key(a, b, c));
    if (it == tern_map.end()) return no_cl;
    const auto& cl = cls[it->second];
    if (cl.size() != 3) return no_cl;
    Lit x[3] = {a, b, c};
    std::sort(x, x + 3);
    if (cl[0] != x[0] || cl[1] != x[1] || cl[2] != x[2]) return no_cl;
    return it->second;
}

void CnfRewrite::reset() {
    nvars = 0;
    cls.clear();
    occ.clear();
    bin_occ.clear();
    bin_map.clear();
    tern_map.clear();
    dont_elim.clear();
    cl_used.clear();
    cands.clear();
    gate_of_var.clear();
    mark_buf.clear();
    pos_buf.clear();
}

void CnfRewrite::build_occ(const SimplifiedCNF& cnf) {
    nvars = cnf.nVars();
    cls.clear();
    cls.reserve(cnf.get_clauses().size());
    for (const auto& c : cnf.get_clauses()) {
        vector<Lit> tmp(c);
        std::sort(tmp.begin(), tmp.end());
        cls.push_back(std::move(tmp));
    }
    occ.assign(2 * nvars, {});
    bin_occ.assign(2 * nvars, 0);
    for (uint32_t i = 0; i < cls.size(); i++) {
        const auto& c = cls[i];
        for (const Lit l : c) occ[l.toInt()].push_back(i);
        if (c.size() == 2) {
            bin_occ[c[0].toInt()]++;
            bin_occ[c[1].toInt()]++;
            bin_map.emplace(bin_key(c[0], c[1]), i);
        } else if (c.size() == 3) {
            tern_map.emplace(tern_key(c[0], c[1], c[2]), i);
        }
    }
    cl_used.assign(cls.size(), 0);
    gate_of_var.assign(nvars, -1);
}

void CnfRewrite::setup_dont_elim(const SimplifiedCNF& cnf) {
    dont_elim.assign(nvars, 0);
    for (const uint32_t v : cnf.get_sampl_vars()) dont_elim[v] = 1;
    if (cnf.get_weighted()) {
        for (uint32_t v = 0; v < nvars; v++) if (cnf.weight_set(v)) dont_elim[v] = 1;
    }
}

void CnfRewrite::detect_and_gates() {
    for (uint32_t ci = 0; ci < cls.size(); ci++) {
        const auto& c = cls[ci];
        if (c.size() < 2) continue;
        if ((int)c.size() - 1 > conf.cnfrw_max_gate_inputs) continue;
        for (const Lit o : c) {
            if (bin_occ[(~o).toInt()] + 1 < c.size()) continue;
            Gate g;
            g.type = c.size() == 2 ? GateType::EQUIV : GateType::AND;
            g.out = o;
            g.cls.push_back(ci);
            bool ok = true;
            for (const Lit l : c) {
                if (l == o) continue;
                const uint32_t bi = find_bin(~o, ~l);
                if (bi == no_cl) { ok = false; break; }
                g.cls.push_back(bi);
                g.ins.push_back(~l);
            }
            if (!ok) continue;
            stats.cand_gates[(size_t)g.type]++;
            stats.cand_inputs[(size_t)g.type] += g.ins.size();
            cands.push_back(std::move(g));
        }
    }
}

void CnfRewrite::detect_xor_gates() {
    const uint32_t max_sz = conf.cnfrw_max_xor_size;
    if (max_sz < 3) return;
    std::map<uint64_t, vector<uint32_t>> groups;
    for (uint32_t ci = 0; ci < cls.size(); ci++) {
        const auto& c = cls[ci];
        if (c.size() < 3 || c.size() > max_sz) continue;
        uint64_t h = c.size();
        for (const Lit l : c) h = h * 0x9e3779b97f4a7c15ULL + l.var() + 1;
        groups[h].push_back(ci);
    }
    vector<uint32_t> vars;
    for (auto& [h, ids] : groups) {
        const uint32_t s = cls[ids[0]].size();
        const uint32_t need = 1u << (s - 1);
        if (ids.size() < need) continue;
        vars.clear();
        for (const Lit l : cls[ids[0]]) vars.push_back(l.var());
        std::set<uint32_t> masks[2];
        vector<uint32_t> ids_by_par[2];
        for (const uint32_t ci : ids) {
            const auto& c = cls[ci];
            if (c.size() != s) continue;
            bool same = true;
            uint32_t mask = 0;
            for (uint32_t i = 0; i < s; i++) {
                if (c[i].var() != vars[i]) { same = false; break; }
                if (c[i].sign()) mask |= 1u << i;
            }
            if (!same) continue;
            const uint32_t par = __builtin_popcount(mask) & 1;
            if (masks[par].insert(mask).second) ids_by_par[par].push_back(ci);
        }
        for (uint32_t par = 0; par < 2; par++) {
            if (masks[par].size() != need) continue;
            const bool rhs = (par == 0);
            for (uint32_t oi = 0; oi < s; oi++) {
                Gate g;
                g.type = GateType::XOR;
                g.out = Lit(vars[oi], rhs);
                for (uint32_t i = 0; i < s; i++) if (i != oi) g.ins.push_back(Lit(vars[i], false));
                g.cls = ids_by_par[par];
                stats.cand_gates[(size_t)g.type]++;
                stats.cand_inputs[(size_t)g.type] += g.ins.size();
                cands.push_back(std::move(g));
            }
        }
    }
}

void CnfRewrite::detect_ite_gates() {
    vector<uint32_t> neg_terns;
    for (uint32_t v = 0; v < nvars; v++) {
        const Lit g(v, false);
        neg_terns.clear();
        for (const uint32_t ci : occ[(~g).toInt()]) if (cls[ci].size() == 3) neg_terns.push_back(ci);
        if (neg_terns.size() < 2 || neg_terns.size() > 40) continue;
        for (size_t a = 0; a < neg_terns.size(); a++) {
            const auto& A = cls[neg_terns[a]];
            for (size_t b = 0; b < neg_terns.size(); b++) {
                if (a == b) continue;
                const auto& B = cls[neg_terns[b]];
                for (const Lit la : A) {
                    if (la == ~g) continue;
                    bool compl_in_b = false;
                    for (const Lit lb : B) if (lb == ~la) { compl_in_b = true; break; }
                    if (!compl_in_b) continue;
                    const Lit s = ~la;
                    Lit t = lit_Undef, e = lit_Undef;
                    for (const Lit x : A) if (x != ~g && x != la) t = x;
                    for (const Lit x : B) if (x != ~g && x != s) e = x;
                    if (t == lit_Undef || e == lit_Undef) continue;
                    if (t.var() == s.var() || e.var() == s.var() || t.var() == v || e.var() == v) continue;
                    const uint32_t c3 = find_tern(g, ~s, ~t);
                    if (c3 == no_cl) continue;
                    const uint32_t c4 = find_tern(g, s, ~e);
                    if (c4 == no_cl) continue;
                    Gate gt;
                    gt.type = GateType::ITE;
                    gt.out = g;
                    gt.ins = {s, t, e};
                    gt.cls = {neg_terns[a], neg_terns[b], c3, c4};
                    stats.cand_gates[(size_t)gt.type]++;
                    stats.cand_inputs[(size_t)gt.type] += 3;
                    cands.push_back(std::move(gt));
                }
            }
        }
    }
}

bool CnfRewrite::irreg_check(uint32_t v, Gate& g) {
    const Lit p(v, false);
    const auto& P = occ[p.toInt()];
    const auto& N = occ[(~p).toInt()];
    if (P.empty() || N.empty()) return false;
    if (P.size() * N.size() > (size_t)conf.cnfrw_irreg_max_prod) { stats.irreg_too_big++; return false; }
    stats.irreg_tried++;
    if (mark_buf.size() < 2 * nvars) mark_buf.assign(2 * nvars, 0);
    vector<char>& mark = mark_buf;
    for (const uint32_t pi : P) {
        for (const Lit l : cls[pi]) mark[l.toInt()] = 1;
        for (const uint32_t ni : N) {
            bool taut = false;
            for (const Lit l : cls[ni]) if (l.var() != v && mark[(~l).toInt()]) { taut = true; break; }
            if (!taut) {
                for (const Lit l : cls[pi]) mark[l.toInt()] = 0;
                return false;
            }
        }
        for (const Lit l : cls[pi]) mark[l.toInt()] = 0;
    }
    stats.irreg_taut_ok++;
    vector<uint32_t> lv;
    for (const uint32_t ci : P) for (const Lit l : cls[ci]) if (l.var() != v) lv.push_back(l.var());
    for (const uint32_t ci : N) for (const Lit l : cls[ci]) if (l.var() != v) lv.push_back(l.var());
    std::sort(lv.begin(), lv.end());
    lv.erase(std::unique(lv.begin(), lv.end()), lv.end());
    if (lv.size() > (size_t)conf.cnfrw_irreg_max_vars) { stats.irreg_too_big++; return false; }
    if (pos_buf.size() < nvars) pos_buf.assign(nvars, 0);
    vector<uint32_t>& pos_of = pos_buf;
    for (uint32_t i = 0; i < lv.size(); i++) pos_of[lv[i]] = i;
    const uint32_t n = lv.size();
    auto cl_sat = [&](const vector<Lit>& c, uint64_t asg) {
        for (const Lit l : c) {
            if (l.var() == v) continue;
            const bool val = (asg >> pos_of[l.var()]) & 1;
            if (val != l.sign()) return true;
        }
        return false;
    };
    for (uint64_t asg = 0; asg < (1ULL << n); asg++) {
        bool all = true;
        for (const uint32_t ci : P) if (!cl_sat(cls[ci], asg)) { all = false; break; }
        if (!all) continue;
        for (const uint32_t ci : N) if (!cl_sat(cls[ci], asg)) { all = false; break; }
        if (all) return false;
    }
    stats.irreg_bf_ok++;
    size_t lits_n = 0, lits_p = 0;
    for (const uint32_t ci : N) lits_n += cls[ci].size() - 1;
    for (const uint32_t ci : P) lits_p += cls[ci].size() - 1;
    const bool use_n = lits_n <= lits_p;
    g.type = GateType::IRREG;
    g.out = use_n ? p : ~p;
    for (const uint32_t ci : (use_n ? N : P)) {
        vector<Lit> term;
        for (const Lit l : cls[ci]) if (l.var() != v) term.push_back(l);
        g.terms.push_back(std::move(term));
    }
    for (const uint32_t ci : P) g.cls.push_back(ci);
    for (const uint32_t ci : N) g.cls.push_back(ci);
    for (const uint32_t x : lv) g.ins.push_back(Lit(x, false));
    return true;
}

void CnfRewrite::detect_irreg_gates() {
    if (!conf.cnfrw_irreg) return;
    vector<char> has_cand(nvars, 0);
    for (const auto& g : cands) has_cand[g.out.var()] = 1;
    for (uint32_t v = 0; v < nvars; v++) {
        if (has_cand[v]) continue;
        if (occ[Lit(v, false).toInt()].empty() || occ[Lit(v, true).toInt()].empty()) continue;
        Gate g;
        if (!irreg_check(v, g)) continue;
        stats.cand_gates[(size_t)g.type]++;
        stats.cand_inputs[(size_t)g.type] += g.ins.size();
        cands.push_back(std::move(g));
    }
}

void CnfRewrite::print_gate(const Gate& g) const {
    cout << "c o [cnfrw-gate] " << gate_type_name(g.type) << " " << g.out << " = f(";
    for (const Lit l : g.ins) cout << l << " ";
    cout << ") cls:";
    for (const uint32_t ci : g.cls) cout << " [" << cls[ci] << "]";
    cout << endl;
}

bool CnfRewrite::gate_eval(const Gate& g, const std::function<bool(Lit)>& val) const {
    bool f = false;
    switch (g.type) {
        case GateType::EQUIV:
        case GateType::AND:
            f = true;
            for (const Lit l : g.ins) f = f && val(l);
            break;
        case GateType::XOR:
            f = false;
            for (const Lit l : g.ins) f = f != val(l);
            break;
        case GateType::ITE:
            f = val(g.ins[0]) ? val(g.ins[1]) : val(g.ins[2]);
            break;
        case GateType::IRREG:
            f = true;
            for (const auto& term : g.terms) {
                bool t = false;
                for (const Lit l : term) t = t || val(l);
                f = f && t;
            }
            break;
        default: assert(false);
    }
    return f != g.out.sign();
}

void CnfRewrite::verify_gates() const {
    for (uint32_t v = 0; v < nvars; v++) {
        if (gate_of_var[v] == -1) continue;
        const Gate& g = cands[gate_of_var[v]];
        vector<uint32_t> vars;
        vars.push_back(v);
        for (const Lit l : g.ins) vars.push_back(l.var());
        std::sort(vars.begin(), vars.end());
        vars.erase(std::unique(vars.begin(), vars.end()), vars.end());
        if (vars.size() > 16) continue;
        std::unordered_map<uint32_t, uint32_t> pos;
        for (uint32_t i = 0; i < vars.size(); i++) pos[vars[i]] = i;
        for (uint64_t asg = 0; asg < (1ULL << vars.size()); asg++) {
            auto val = [&](Lit l) { return (bool)((asg >> pos.at(l.var())) & 1) != l.sign(); };
            bool cls_ok = true;
            for (const uint32_t ci : g.cls) {
                bool sat = false;
                for (const Lit l : cls[ci]) if (val(l)) { sat = true; break; }
                if (!sat) { cls_ok = false; break; }
            }
            const bool def_ok = val(Lit(v, false)) == gate_eval(g, val);
            if (cls_ok != def_ok) {
                cout << "ERROR: gate is not a definition:" << endl;
                print_gate(g);
                assert(false && "cnfrw gate verification failed");
            }
        }
    }
}

uint32_t CnfRewrite::Gate::priority() const {
    uint32_t p = cls.size() * 8;
    switch (type) {
        case GateType::XOR: p += 4; break;
        case GateType::ITE: p += 3; break;
        case GateType::AND: p += 2; break;
        case GateType::EQUIV: p += 1; break;
        default: break;
    }
    return p;
}

void CnfRewrite::select_gates() {
    vector<uint32_t> order(cands.size());
    for (uint32_t i = 0; i < order.size(); i++) order[i] = i;
    std::stable_sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) {
        const uint32_t pa = cands[a].priority(), pb = cands[b].priority();
        if (pa != pb) return pa > pb;
        const bool da = dont_elim[cands[a].out.var()], db = dont_elim[cands[b].out.var()];
        if (da != db) return !da;
        return cands[a].out.var() < cands[b].out.var();
    });
    for (const uint32_t gi : order) {
        const Gate& g = cands[gi];
        const uint32_t v = g.out.var();
        if (gate_of_var[v] != -1) { stats.rej_var_defined++; continue; }
        bool conflict = false;
        for (const uint32_t ci : g.cls) if (cl_used[ci]) { conflict = true; break; }
        if (conflict) { stats.rej_clause_conflict++; continue; }
        for (const uint32_t ci : g.cls) cl_used[ci] = 1;
        gate_of_var[v] = gi;
    }
}

void CnfRewrite::break_cycles() {
    enum : uint8_t { WHITE, GREY, BLACK };
    vector<uint8_t> color(nvars, WHITE);
    struct Frame { uint32_t v; uint32_t next; };
    vector<Frame> stack;
    auto drop = [&](uint32_t v) {
        const Gate& g = cands[gate_of_var[v]];
        for (const uint32_t ci : g.cls) cl_used[ci] = 0;
        gate_of_var[v] = -1;
        stats.rej_cycle++;
    };
    for (uint32_t root = 0; root < nvars; root++) {
        if (gate_of_var[root] == -1 || color[root] != WHITE) continue;
        color[root] = GREY;
        stack.push_back({root, 0});
        while (!stack.empty()) {
            Frame& f = stack.back();
            if (gate_of_var[f.v] == -1) { color[f.v] = BLACK; stack.pop_back(); continue; }
            const Gate& g = cands[gate_of_var[f.v]];
            if (f.next >= g.ins.size()) { color[f.v] = BLACK; stack.pop_back(); continue; }
            const uint32_t w = g.ins[f.next++].var();
            if (gate_of_var[w] == -1) continue;
            if (color[w] == GREY) { drop(f.v); color[f.v] = BLACK; stack.pop_back(); continue; }
            if (color[w] == WHITE) { color[w] = GREY; stack.push_back({w, 0}); }
        }
    }
}

aig_lit CnfRewrite::gate_aig(const Gate& g, const vector<aig_lit>& var_aig) const {
    auto in = [&](Lit l) -> aig_lit {
        const aig_lit& a = var_aig[l.var()];
        assert(a);
        return l.sign() ? ~a : a;
    };
    aig_lit res;
    switch (g.type) {
        case GateType::EQUIV:
        case GateType::AND: {
            res = in(g.ins[0]);
            for (size_t i = 1; i < g.ins.size(); i++) res = AIG::new_and(res, in(g.ins[i]));
            break;
        }
        case GateType::XOR: {
            res = in(g.ins[0]);
            for (size_t i = 1; i < g.ins.size(); i++) {
                const aig_lit b = in(g.ins[i]);
                res = AIG::new_or(AIG::new_and(res, ~b), AIG::new_and(~res, b));
            }
            break;
        }
        case GateType::ITE: {
            res = AIG::new_ite(in(g.ins[1]), in(g.ins[2]), in(g.ins[0]));
            break;
        }
        case GateType::IRREG: {
            for (const auto& term : g.terms) {
                aig_lit t = in(term[0]);
                for (size_t i = 1; i < term.size(); i++) t = AIG::new_or(t, in(term[i]));
                res = res ? AIG::new_and(res, t) : t;
            }
            break;
        }
        default: assert(false);
    }
    return g.out.sign() ? ~res : res;
}

void CnfRewrite::compute_removable(vector<char>& removable) const {
    removable.assign(nvars, 0);
    for (uint32_t v = 0; v < nvars; v++) {
        if (gate_of_var[v] == -1 || dont_elim[v]) continue;
        bool all_in_gates = true;
        for (const uint32_t ci : occ[Lit(v, false).toInt()]) if (!cl_used[ci]) { all_in_gates = false; break; }
        if (all_in_gates)
            for (const uint32_t ci : occ[Lit(v, true).toInt()]) if (!cl_used[ci]) { all_in_gates = false; break; }
        removable[v] = all_in_gates;
    }
}

void CnfRewrite::build_aigs(const vector<char>& removable, vector<aig_lit>& var_aig,
                            vector<uint32_t>& root_vars, vector<aig_lit>& roots) {
    var_aig.assign(nvars, aig_lit());
    vector<uint8_t> state(nvars, 0);
    struct Frame { uint32_t v; uint32_t next; };
    vector<Frame> stack;
    vector<aig_lit> gate_val(nvars, aig_lit());
    for (uint32_t r = 0; r < nvars; r++) {
        if (gate_of_var[r] == -1 || state[r] == 2) continue;
        state[r] = 1;
        stack.push_back({r, 0});
        while (!stack.empty()) {
            Frame& f = stack.back();
            const Gate& g = cands[gate_of_var[f.v]];
            if (f.next < g.ins.size()) {
                const uint32_t w = g.ins[f.next++].var();
                if (gate_of_var[w] != -1 && removable[w] && state[w] == 0) {
                    state[w] = 1;
                    stack.push_back({w, 0});
                }
                continue;
            }
            for (const Lit l : g.ins) {
                const uint32_t w = l.var();
                if (var_aig[w]) continue;
                assert(!(gate_of_var[w] != -1 && removable[w]) || state[w] == 2);
                var_aig[w] = AIG::new_lit(w);
            }
            const aig_lit val = gate_aig(g, var_aig);
            gate_val[f.v] = val;
            if (removable[f.v]) var_aig[f.v] = val;
            else if (!var_aig[f.v]) var_aig[f.v] = AIG::new_lit(f.v);
            state[f.v] = 2;
            stack.pop_back();
        }
    }
    for (uint32_t v = 0; v < nvars; v++) {
        if (gate_of_var[v] == -1 || removable[v]) continue;
        root_vars.push_back(v);
        roots.push_back(gate_val[v]);
    }
}

void CnfRewrite::fill_root_info(Lifted& out) const {
    for (const uint32_t v : out.root_vars) {
        const Gate& g = cands[gate_of_var[v]];
        out.root_type.push_back(g.type);
        out.root_gate_cls.push_back(g.cls.size());
        uint32_t lits = 0;
        for (const uint32_t ci : g.cls) lits += cls[ci].size();
        out.root_gate_lits.push_back(lits);
    }
}

namespace {
struct ClauseCollector {
    uint32_t nv = 0;
    vector<vector<Lit>> cls;
    void new_var() { nv++; }
    uint32_t nVars() const { return nv; }
    void add_clause(const vector<Lit>& cl) { cls.push_back(cl); }
};

uint64_t aig_depth(const vector<aig_lit>& roots) {
    std::unordered_map<const AIG*, uint64_t> d;
    uint64_t best = 0;
    struct Frame { const AIG* n; bool done; };
    vector<Frame> st;
    for (const auto& r : roots) {
        if (!r) continue;
        st.push_back({r.get(), false});
        while (!st.empty()) {
            Frame f = st.back(); st.pop_back();
            if (d.count(f.n)) continue;
            if (f.n->type != AIGT::t_and) { d[f.n] = 0; continue; }
            if (!f.done) {
                st.push_back({f.n, true});
                if (!d.count(f.n->l.get())) st.push_back({f.n->l.get(), false});
                if (!d.count(f.n->r.get())) st.push_back({f.n->r.get(), false});
                continue;
            }
            const uint64_t v = 1 + std::max(d.at(f.n->l.get()), d.at(f.n->r.get()));
            d[f.n] = v;
            best = std::max(best, v);
        }
    }
    return best;
}
}

CnfRewrite::Lifted CnfRewrite::lift_only(const SimplifiedCNF& cnf) {
    reset();
    stats = CnfRwStats();
    build_occ(cnf);
    setup_dont_elim(cnf);
    detect_and_gates();
    detect_xor_gates();
    detect_ite_gates();
    detect_irreg_gates();
    select_gates();
    break_cycles();
    for (uint32_t v = 0; v < nvars; v++) {
        if (gate_of_var[v] == -1) continue;
        const Gate& g = cands[gate_of_var[v]];
        stats.sel_gates[(size_t)g.type]++;
        stats.sel_inputs[(size_t)g.type] += g.ins.size();
        stats.sel_clauses[(size_t)g.type] += g.cls.size();
        stats.fanin_hist[(size_t)g.type][fanin_bucket(g.ins.size())]++;
        stats.max_fanin = std::max<uint64_t>(stats.max_fanin, g.ins.size());
        stats.gate_outputs++;
    }
    Lifted out;
    compute_removable(out.removable);
    vector<aig_lit> var_aig;
    build_aigs(out.removable, var_aig, out.root_vars, out.roots);
    out.nvars = nvars;
    fill_root_info(out);
    return out;
}

CnfRewrite::EncResult CnfRewrite::encode_component(const vector<aig_lit>& croots,
        const vector<uint32_t>& cvars, bool use_mapper) {
    EncResult er;
    ClauseCollector cc;
    cc.nv = nvars;
    vector<Lit> root_lits;
    if (use_mapper) {
        AIGCnfMapper<ClauseCollector> enc(cc);
        enc.set_max_leaves(conf.cnfrw_map_leaves);
        enc.set_max_cuts(conf.cnfrw_map_cuts);
        enc.set_helper_weight(conf.cnfrw_map_helper_w);
        enc.set_kand(conf.cnfrw_kary_fusion);
        enc.set_max_kand(conf.cnfrw_max_kary);
        root_lits = enc.encode_batch(croots);
    } else {
        AIGToCNF<ClauseCollector> enc(cc);
        enc.set_group_cse(conf.cnfrw_group_cse);
        enc.set_cut_cnf(conf.cnfrw_cut_cnf);
        enc.set_detect_ite(conf.cnfrw_detect_ite);
        enc.set_detect_xor(conf.cnfrw_detect_xor);
        enc.set_kary_fusion(conf.cnfrw_kary_fusion);
        enc.set_max_kary_width(conf.cnfrw_max_kary);
        enc.set_max_mux_chain(conf.cnfrw_max_mux_chain);
        root_lits = enc.encode_batch(croots);
    }
    er.nv = cc.nv;
    er.helper_map.assign(cc.nv, lit_Undef);
    for (size_t i = 0; i < croots.size(); i++) {
        const uint32_t g = cvars[i];
        const Lit r = root_lits[i];
        if (r.var() >= nvars) {
            if (er.helper_map[r.var()] == lit_Undef) { er.helper_map[r.var()] = Lit(g, r.sign()); er.n_helper++; }
            else {
                const Lit other = er.helper_map[r.var()] ^ r.sign();
                er.cls.push_back({Lit(g, false), ~other});
                er.cls.push_back({Lit(g, true), other});
                er.n_shared++;
            }
        } else {
            er.cls.push_back({Lit(g, false), ~r});
            er.cls.push_back({Lit(g, true), r});
            er.n_leaf++;
        }
    }
    for (uint32_t h = nvars; h < cc.nv; h++) if (er.helper_map[h] == lit_Undef) er.helpers++;
    for (auto& cl : cc.cls) er.cls.push_back(std::move(cl));
    for (const auto& cl : er.cls) er.lits += cl.size();
    return er;
}

bool CnfRewrite::run(SimplifiedCNF& cnf, const string& tag) {
    const double t_start = cpuTime();
    reset();
    stats = CnfRwStats();
    if (cnf.get_need_aig()) {
        verb_print(1, "[cnfrw] skipping: not supported with AIG definitions (synthesis)");
        return false;
    }
    const string prefix = tag.empty() ? "" : (tag + " ");

    build_occ(cnf);
    setup_dont_elim(cnf);
    stats.vars_in = nvars;
    stats.cls_in = cls.size();
    for (const auto& c : cls) stats.lits_in += c.size();

    double t = cpuTime();
    detect_and_gates();
    detect_xor_gates();
    detect_ite_gates();
    detect_irreg_gates();
    stats.t_detect = cpuTime() - t;

    t = cpuTime();
    select_gates();
    break_cycles();
    SLOW_DEBUG_DO(verify_gates());
    for (uint32_t v = 0; v < nvars; v++) {
        if (gate_of_var[v] == -1) continue;
        const Gate& g = cands[gate_of_var[v]];
        VERBOSE_DEBUG_DO(print_gate(g));
        stats.sel_gates[(size_t)g.type]++;
        stats.sel_inputs[(size_t)g.type] += g.ins.size();
        stats.sel_clauses[(size_t)g.type] += g.cls.size();
        stats.fanin_hist[(size_t)g.type][fanin_bucket(g.ins.size())]++;
        stats.max_fanin = std::max<uint64_t>(stats.max_fanin, g.ins.size());
        stats.gate_outputs++;
    }
    stats.t_select = cpuTime() - t;
    if (stats.gate_outputs == 0) {
        stats.t_total = cpuTime() - t_start;
        verb_print(1, prefix << "[cnfrw] no gates found. T: " << std::fixed << std::setprecision(2) << stats.t_total);
        return false;
    }

    t = cpuTime();
    vector<char> removable;
    compute_removable(removable);
    vector<aig_lit> var_aig;
    vector<uint32_t> root_vars;
    vector<aig_lit> roots;
    build_aigs(removable, var_aig, root_vars, roots);
    {
        vector<char> is_leaf(nvars, 0);
        {
            std::unordered_set<const AIG*> seen;
            vector<const AIG*> st;
            for (const auto& r : roots) if (r) st.push_back(r.get());
            while (!st.empty()) {
                const AIG* n = st.back(); st.pop_back();
                if (!seen.insert(n).second) continue;
                if (n->type == AIGT::t_lit) { is_leaf[n->var] = 1; continue; }
                if (n->type != AIGT::t_and) continue;
                st.push_back(n->l.get());
                st.push_back(n->r.get());
            }
        }
        for (uint32_t v = 0; v < nvars; v++) {
            if (gate_of_var[v] == -1) { if (is_leaf[v]) stats.leaf_vars++; continue; }
            if (removable[v]) { stats.removable_outputs++; continue; }
            stats.kept_outputs++;
            if (dont_elim[v]) stats.kept_dont_elim++; else stats.kept_external_use++;
        }
    }
    stats.roots = roots.size();
    stats.aig_nodes_before = AIG::count_aig_nodes_fast(roots);
    stats.t_build = cpuTime() - t;

    t = cpuTime();
    if (conf.cnfrw_rewrite) {
        AIGRewriter rw;
        rw.rewrite_all(roots, conf.verb >= 2 ? conf.verb : 0, conf.cnfrw_balance);
    }
    stats.aig_nodes_after = AIG::count_aig_nodes_fast(roots);
    stats.aig_max_depth = aig_depth(roots);
    stats.t_rewrite = cpuTime() - t;

    t = cpuTime();
    vector<uint32_t> uf(nvars);
    for (uint32_t v = 0; v < nvars; v++) uf[v] = v;
    std::function<uint32_t(uint32_t)> find = [&](uint32_t v) {
        while (uf[v] != v) { uf[v] = uf[uf[v]]; v = uf[v]; }
        return v;
    };
    auto unite = [&](uint32_t a, uint32_t b) {
        a = find(a); b = find(b);
        if (a != b) uf[std::max(a, b)] = std::min(a, b);
    };
    for (uint32_t v = 0; v < nvars; v++) {
        if (gate_of_var[v] == -1) continue;
        for (const Lit l : cands[gate_of_var[v]].ins) if (removable[l.var()]) unite(v, l.var());
    }
    {
        std::unordered_map<const AIG*, uint32_t> owner;
        std::unordered_set<const AIG*> seen;
        vector<const AIG*> st;
        for (size_t i = 0; i < roots.size(); i++) {
            if (!roots[i] || roots[i]->type != AIGT::t_and) continue;
            seen.clear();
            st.push_back(roots[i].get());
            while (!st.empty()) {
                const AIG* n = st.back(); st.pop_back();
                if (n->type != AIGT::t_and || !seen.insert(n).second) continue;
                auto it = owner.find(n);
                if (it != owner.end()) { unite(root_vars[i], root_vars[it->second]); continue; }
                owner[n] = i;
                st.push_back(n->l.get());
                st.push_back(n->r.get());
            }
        }
    }
    std::map<uint32_t, vector<uint32_t>> comp_roots;
    std::map<uint32_t, vector<uint32_t>> comp_gates;
    for (uint32_t v = 0; v < nvars; v++) if (gate_of_var[v] != -1) comp_gates[find(v)].push_back(v);
    for (size_t i = 0; i < roots.size(); i++) comp_roots[find(root_vars[i])].push_back(i);

    vector<vector<Lit>> added_cls;
    uint32_t next_var = nvars;
    vector<char> accepted_gate(nvars, 0);
    comp_info.clear();
    for (const auto& [c, gates] : comp_gates) {
        uint64_t rem_lits = 0, rem_cls = 0, rem_vars = 0;
        for (const uint32_t v : gates) {
            for (const uint32_t ci : cands[gate_of_var[v]].cls) { rem_cls++; rem_lits += cls[ci].size(); }
            if (removable[v]) rem_vars++;
        }
        CompInfo info;
        if (collect_comp_info) {
            info.gates = gates.size();
            info.removable = rem_vars;
            info.orig_lits = rem_lits;
            info.orig_cls = rem_cls;
            auto rit2 = comp_roots.find(c);
            if (rit2 != comp_roots.end())
                for (const uint32_t i : rit2->second) { info.roots.push_back(roots[i]); info.root_vars.push_back(root_vars[i]); }
        }
        auto rit = comp_roots.find(c);
        EncResult er;
        if (rit != comp_roots.end()) {
            vector<aig_lit> croots;
            vector<uint32_t> cvars;
            for (const uint32_t i : rit->second) { croots.push_back(roots[i]); cvars.push_back(root_vars[i]); }
            if (conf.cnfrw_encoder == 0) er = encode_component(croots, cvars, false);
            else if (conf.cnfrw_encoder == 1) er = encode_component(croots, cvars, true);
            else {
                er = encode_component(croots, cvars, false);
                EncResult em = encode_component(croots, cvars, true);
                const int64_t c0 = er.lits + conf.cnfrw_cls_weight * er.cls.size() + conf.cnfrw_var_weight * er.helpers;
                const int64_t c1 = em.lits + conf.cnfrw_cls_weight * em.cls.size() + conf.cnfrw_var_weight * em.helpers;
                if (c1 < c0) { er = std::move(em); stats.enc_mapper_won++; } else stats.enc_aig2cnf_won++;
            }
            vector<vector<Lit>>& comp_cls = er.cls;
            vector<Lit>& helper_map = er.helper_map;
            const uint32_t helpers = er.helpers, n_helper = er.n_helper, n_shared = er.n_shared, n_leaf = er.n_leaf;
            const uint32_t cc_nv = er.nv;
            const uint64_t add_lits = er.lits;
            const int64_t rem_cost = rem_lits + conf.cnfrw_cls_weight * rem_cls + conf.cnfrw_var_weight * rem_vars;
            const int64_t add_cost = add_lits + conf.cnfrw_cls_weight * comp_cls.size() + conf.cnfrw_var_weight * helpers;
            bool too_long = false;
            if (conf.cnfrw_max_cls_len > 0)
                for (const auto& cl : comp_cls) if ((int)cl.size() > conf.cnfrw_max_cls_len) { too_long = true; break; }
            if (collect_comp_info) {
                info.new_lits = add_lits; info.new_cls = comp_cls.size(); info.helpers = helpers;
                info.accepted = !((conf.cnfrw_guard && add_cost + conf.cnfrw_min_gain >= rem_cost) || too_long);
                comp_info.push_back(info);
            }
            if ((conf.cnfrw_guard && add_cost + conf.cnfrw_min_gain >= rem_cost) || too_long) {
                stats.comp_rej_cost += add_cost - rem_cost;
                stats.comp_rejected++;
                for (const uint32_t v : gates) {
                    for (const uint32_t ci : cands[gate_of_var[v]].cls) cl_used[ci] = 0;
                    removable[v] = 0;
                }
                continue;
            }
            stats.comp_gain_cost += rem_cost - add_cost;
            stats.roots_helper += n_helper;
            stats.roots_shared += n_shared;
            stats.roots_leaf += n_leaf;
            stats.equiv_bins_added += 2 * (n_shared + n_leaf);
            for (uint32_t h = nvars; h < cc_nv; h++)
                if (helper_map[h] == lit_Undef) helper_map[h] = Lit(next_var++, false);
            for (auto& cl : comp_cls) {
                for (auto& l : cl) if (l.var() >= nvars) l = helper_map[l.var()] ^ l.sign();
                stats.cls_added++;
                stats.lits_added += cl.size();
                added_cls.push_back(std::move(cl));
            }
        } else {
            stats.dead_gates += gates.size();
            if (collect_comp_info) { info.accepted = true; comp_info.push_back(info); }
        }
        stats.comp_accepted++;
        for (const uint32_t v : gates) accepted_gate[v] = 1;
    }
    stats.vars_added = next_var - nvars;
    stats.t_encode = cpuTime() - t;

    t = cpuTime();
    vector<vector<Lit>> new_cls;
    new_cls.reserve(cls.size() + added_cls.size());
    for (uint32_t ci = 0; ci < cls.size(); ci++) {
        if (cl_used[ci]) { stats.cls_removed++; stats.lits_removed += cls[ci].size(); continue; }
        new_cls.push_back(cls[ci]);
    }
    for (auto& c : added_cls) new_cls.push_back(std::move(c));
    vector<vector<Lit>> new_red;
    for (const auto& c : cnf.get_red_clauses()) {
        bool touches = false;
        for (const Lit l : c) if (removable[l.var()]) { touches = true; break; }
        if (touches) { stats.red_cls_dropped++; continue; }
        new_red.push_back(c);
    }

    constexpr uint32_t m = std::numeric_limits<uint32_t>::max();
    vector<uint32_t> vmap(next_var, m);
    uint32_t at = 0;
    for (uint32_t v = 0; v < nvars; v++) {
        if (removable[v]) { stats.vars_removed++; continue; }
        vmap[v] = at++;
    }
    for (uint32_t v = nvars; v < next_var; v++) vmap[v] = at++;
    const uint32_t new_nvars = at;
    if (stats.cls_removed == 0 && stats.cls_added == 0) {
        stats.vars_out = nvars; stats.cls_out = cls.size(); stats.lits_out = stats.lits_in;
        stats.t_assemble = cpuTime() - t;
        stats.t_total = cpuTime() - t_start;
        stats.print(conf.verb, prefix);
        return false;
    }

    vector<Lit> removed_lits;
    for (uint32_t v = 0; v < nvars; v++) if (removable[v]) removed_lits.push_back(Lit(v, false));
    cnf.remove_sampling_vars(removed_lits);
    cnf.set_all_clauses(std::move(new_cls), std::move(new_red));
    cnf.renumber_vars(vmap, new_nvars);
    stats.vars_out = cnf.nVars();
    stats.cls_out = cnf.get_clauses().size();
    for (const auto& c : cnf.get_clauses()) stats.lits_out += c.size();
    stats.t_assemble = cpuTime() - t;
    stats.t_total = cpuTime() - t_start;
    stats.print(conf.verb, prefix);
    SLOW_DEBUG_DO(cnf.check_red_cls_deriveable());
    return true;
}
