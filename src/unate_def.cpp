/*
 Arjun

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#include "unate_def.h"
#include "constants.h"
#include "metasolver.h"
#include "time_mem.h"
#include <iomanip>
#include <queue>
#include <unordered_map>
#include <unordered_set>

using namespace ArjunNS;
using namespace CMSat;
using std::setprecision;
using std::fixed;
using std::setw;
using std::vector;
using std::set;
using std::unique_ptr;

void Unate::synthesis_unate_def(SimplifiedCNF& cnf) {
    const double my_time = cpuTime();

    // Syntactic gate-def pass first — every gate found here saves a SAT
    // call later, plus a downstream Manthan repair sequence.
    {
        const uint32_t gate_defs = synthesis_gate_def(cnf);
        (void)gate_defs;
    }

    std::vector<Lit> pure_pre_units;
    {
        // Re-fetch types (could change between calls if iterated).
        cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate_def").unpack_to(input, to_define, backward_defined);
        if (to_define.empty()) {
            verb_print(1, "[unate_def] No variables to define, skipping");
            return;
        }

        // Pure-literal pre-pass: a to-define var that appears with only one
        // polarity in F is unate at the *opposite* polarity for free — no SAT
        // call. Lagniez-Marquis's "Improving Model Counting by Leveraging
        // Definability" lists this as a syntactic shortcut that should always
        // run before the SAT-based test. CMS's normal preprocessing strips
        // these for solver vars, but we run on the raw CNF here, so the check
        // pays its own way. We pin each find as a unit clause and drop the
        // var from to_define so the dual-rail solver below doesn't redundantly
        // re-test it.
        const double pl_start = cpuTime();
        std::vector<uint32_t> pos_count(cnf.nVars(), 0);
        std::vector<uint32_t> neg_count(cnf.nVars(), 0);
        for (const auto& cl : cnf.get_clauses()) {
            for (const auto& l : cl) {
                if (l.sign()) neg_count[l.var()]++;
                else pos_count[l.var()]++;
            }
        }
        for (const auto& v : to_define) {
            if (pos_count[v] == 0 && neg_count[v] == 0) {
                pure_pre_units.emplace_back(v, true);
            } else if (pos_count[v] == 0) {
                pure_pre_units.emplace_back(v, true);
            } else if (neg_count[v] == 0) {
                pure_pre_units.emplace_back(v, false);
            }
        }
        for (const auto& l : pure_pre_units) cnf.add_clause({l});
        cnf.add_fixed_values(pure_pre_units);
        verb_print(1, "[unate_def/pure-lit] units: " << setw(4) << pure_pre_units.size()
            << " out of " << setw(5) << to_define.size()
            << " T: " << setprecision(3) << fixed << (cpuTime() - pl_start));
    }

    // Iterative fix-point: pinning a unit may unblock another var on the
    // next pass via unit propagation. add_fixed_values is called at the
    // end of each pass so cnf.get_var_types reclassifies the pinned vars
    // out of to_define on the next pass; otherwise the pass would
    // re-confirm them (UNSAT under their own unit clause) and the loop
    // would never terminate.
    std::vector<Lit> all_unates = std::move(pure_pre_units);
    uint32_t iter = 0;
    while (true) {
        iter++;
        std::vector<Lit> pass_unates;
        const uint32_t found = synthesis_unate_def_pass(cnf, pass_unates);
        verb_print(1, "[unate_def/iter " << iter << "] found " << found
            << " new units (cumulative " << (all_unates.size() + pass_unates.size()) << ")");
        if (found == 0) break;
        cnf.add_fixed_values(pass_unates);
        all_unates.insert(all_unates.end(), pass_unates.begin(), pass_unates.end());
    }
    auto [input2, to_define2, backward_defined2] = cnf.get_var_types(0 | verbose_debug_enabled, "end do_unate_def");
    verb_print(1, COLRED "[unate_def] Done. synthesis_unate_def (iters=" << iter << ")"
        << " total units: " << all_unates.size()
        << " still to define: " << to_define2.size()
        << " T: " << (cpuTime() - my_time));
}

uint32_t Unate::synthesis_gate_def(SimplifiedCNF& cnf) {
    const double t0 = cpuTime();
    cnf.get_var_types(0 | verbose_debug_enabled, "start gate_def").unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) return 0;

    // Build polarity-keyed occurrence lists. For each (var, sign) we list
    // the clauses that contain that signed literal. CNF here is the
    // post-simplifier CNF passed in by the caller — clauses are over
    // "new"-space var ids.
    const auto& clauses = cnf.get_clauses();
    std::vector<std::vector<size_t>> pos_occ(cnf.nVars()); // clauses with +v
    std::vector<std::vector<size_t>> neg_occ(cnf.nVars()); // clauses with ¬v
    for (size_t ci = 0; ci < clauses.size(); ci++) {
        for (const auto& l : clauses[ci]) {
            (l.sign() ? neg_occ : pos_occ)[l.var()].push_back(ci);
        }
    }

    // Hash-set of binary clauses (canonical-sorted lit pair) for O(1)
    // membership checks during the equivalence pattern match. Using
    // packed-int representation: low bit = sign, rest = var.
    auto pack = [](Lit l) -> uint64_t { return ((uint64_t)l.var() << 1) | (uint64_t)l.sign(); };
    auto unpack = [](uint64_t x) -> Lit { return Lit((uint32_t)(x >> 1), (bool)(x & 1)); };
    auto clause_key = [&](Lit a, Lit b) -> uint64_t {
        uint64_t pa = pack(a), pb = pack(b);
        if (pa > pb) std::swap(pa, pb);
        return (pa << 32) | pb;
    };
    std::unordered_set<uint64_t> bin_set;
    bin_set.reserve(clauses.size());
    for (const auto& cl : clauses) {
        if (cl.size() == 2) bin_set.insert(clause_key(cl[0], cl[1]));
    }

    std::vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    uint32_t n_eq = 0, n_and = 0, n_or = 0;

    auto try_equiv = [&](uint32_t y) -> bool {
        // y ↔ a iff (¬y ∨ a) ∧ (y ∨ ¬a) both binary clauses present.
        // Walk binary clauses containing y (either polarity) and check the
        // negated mate.
        const Lit pos_y(y, false);
        const Lit neg_y(y, true);
        for (const auto ci : pos_occ[y]) {
            if (clauses[ci].size() != 2) continue;
            // clause is (y ∨ x) for some x. Match needs (¬y ∨ ¬x).
            const Lit x = (clauses[ci][0] == pos_y) ? clauses[ci][1] : clauses[ci][0];
            assert((clauses[ci][0] == pos_y || clauses[ci][1] == pos_y));
            if (clauses[ci][0] != pos_y && clauses[ci][1] != pos_y) continue;
            if (bin_set.count(clause_key(neg_y, ~x))) {
                // (y ∨ x) ∧ (¬y ∨ ¬x) ⇒ y = ¬x.
                aigs[y] = AIG::new_lit(x.var(), !x.sign());
                return true;
            }
        }
        for (const auto ci : neg_occ[y]) {
            if (clauses[ci].size() != 2) continue;
            // clause is (¬y ∨ x) for some x. Match needs (y ∨ ¬x).
            const Lit x = (clauses[ci][0] == neg_y) ? clauses[ci][1] : clauses[ci][0];
            if (clauses[ci][0] != neg_y && clauses[ci][1] != neg_y) continue;
            if (bin_set.count(clause_key(pos_y, ~x))) {
                // (¬y ∨ x) ∧ (y ∨ ¬x) ⇒ y = x.
                aigs[y] = AIG::new_lit(x.var(), x.sign());
                return true;
            }
        }
        return false;
    };

    // For AND-gate y = ⋀ aᵢ:
    //   long clause:   (y ∨ ¬a₁ ∨ … ∨ ¬aₖ)
    //   binary mates:  (¬y ∨ aᵢ) for each i
    // For OR-gate y = ⋁ aᵢ:
    //   long clause:   (¬y ∨ a₁ ∨ … ∨ aₖ)
    //   binary mates:  (y ∨ ¬aᵢ) for each i
    auto try_and_or_gate = [&](uint32_t y) -> bool {
        const Lit pos_y(y, false);
        const Lit neg_y(y, true);

        // AND-gate: long clause containing +y, binary mates (¬y ∨ aᵢ).
        for (const auto ci : pos_occ[y]) {
            const auto& cl = clauses[ci];
            if (cl.size() < 3) continue;
            // Collect the aᵢ candidates: every other lit in cl, negated.
            std::vector<Lit> as;
            as.reserve(cl.size() - 1);
            for (const auto& l : cl) {
                if (l == pos_y) continue;
                as.push_back(~l);
            }
            // Each (¬y ∨ aᵢ) must be a binary clause.
            bool all_present = true;
            for (const auto& a : as) {
                if (!bin_set.count(clause_key(neg_y, a))) { all_present = false; break; }
            }
            if (all_present) {
                aig_ptr cur = AIG::new_lit(as[0].var(), as[0].sign());
                for (size_t i = 1; i < as.size(); i++) {
                    cur = AIG::new_and(cur, AIG::new_lit(as[i].var(), as[i].sign()));
                }
                aigs[y] = cur;
                return true;
            }
        }

        // OR-gate: long clause containing ¬y, binary mates (y ∨ ¬aᵢ).
        for (const auto ci : neg_occ[y]) {
            const auto& cl = clauses[ci];
            if (cl.size() < 3) continue;
            std::vector<Lit> as;
            as.reserve(cl.size() - 1);
            for (const auto& l : cl) {
                if (l == neg_y) continue;
                as.push_back(l);
            }
            bool all_present = true;
            for (const auto& a : as) {
                if (!bin_set.count(clause_key(pos_y, ~a))) { all_present = false; break; }
            }
            if (all_present) {
                // y = ⋁ aᵢ — build via new_or which de-Morgans into the AIG.
                aig_ptr cur = AIG::new_lit(as[0].var(), as[0].sign());
                for (size_t i = 1; i < as.size(); i++) {
                    cur = AIG::new_or(cur, AIG::new_lit(as[i].var(), as[i].sign()));
                }
                aigs[y] = cur;
                return true;
            }
        }
        return false;
    };

    // Sort to_define so that vars defined by other-gate-defined vars are
    // discovered after their dependencies. The simple cycle-prevention
    // policy: only accept a definition whose RHS doesn't reference any
    // already-defined var transitively. This keeps the def order acyclic
    // by construction without needing a topological sort.
    for (uint32_t y : to_define) {
        if (try_equiv(y))           {
            n_eq++;
            verb_print(2, "[gate-def] eq: y=" << y+1 << " AIG: " << aigs[y]);
            continue;
        }
        if (try_and_or_gate(y))     {
            n_and++;
            verb_print(2, "[gate-def] and/or: y=" << y+1 << " AIG: " << aigs[y]);
            continue;
        }
    }

    // Cycle-safety check. A candidate def for y_new = f(d_new₁, …, d_newₖ)
    // is unsafe if any d_orig (the orig-space image of d_newᵢ) transitively
    // reaches y_orig via the *existing* cnf defs (set by extend.cpp or
    // backward.cpp earlier in the pipeline) or via another candidate gate-
    // def we're about to install. The check walks through both: we BFS from
    // each d_orig and stop on hitting y_orig.
    {
        const auto new_to_orig_var = cnf.get_new_to_orig_var();
        auto orig_of = [&](uint32_t v_new) -> uint32_t {
            auto it = new_to_orig_var.find(v_new);
            // not all new vars have an orig mapping (e.g. helpers); treat
            // unmapped as "unknown — conservatively drop the candidate".
            if (it == new_to_orig_var.end()) return std::numeric_limits<uint32_t>::max();
            return it->second.var();
        };
        // Build orig-space images of every candidate def's RHS deps.
        std::unordered_map<uint32_t, std::vector<uint32_t>> cand_deps_orig; // y_orig -> list of d_orig
        std::unordered_map<uint32_t, uint32_t> y_new_of;
        for (uint32_t v = 0; v < cnf.nVars(); v++) {
            if (!aigs[v]) continue;
            const uint32_t y_orig = orig_of(v);
            if (y_orig == std::numeric_limits<uint32_t>::max()) { aigs[v] = nullptr; continue; }
            std::set<uint32_t> ds;
            AIG::get_dependent_vars(aigs[v], ds, v);
            std::vector<uint32_t> ds_orig;
            ds_orig.reserve(ds.size());
            bool ok = true;
            for (auto d : ds) {
                const uint32_t d_orig = orig_of(d);
                if (d_orig == std::numeric_limits<uint32_t>::max()) { ok = false; break; }
                if (d_orig == y_orig) { ok = false; break; } // direct self-ref
                ds_orig.push_back(d_orig);
            }
            if (!ok) { aigs[v] = nullptr; continue; }
            cand_deps_orig[y_orig] = std::move(ds_orig);
            y_new_of[y_orig] = v;
        }
        // For each candidate y_orig, BFS from each d_orig and drop if it
        // reaches y_orig. The BFS follows: (a) cnf.get_def(d_orig) edges,
        // (b) candidate edges from cand_deps_orig if d_orig is itself a
        // candidate.
        std::vector<uint32_t> to_drop;
        for (const auto& [y_orig, ds] : cand_deps_orig) {
            std::queue<uint32_t> q;
            std::unordered_set<uint32_t> visited;
            for (auto d : ds) { q.push(d); visited.insert(d); }
            bool cycle = false;
            while (!q.empty() && !cycle) {
                uint32_t cur = q.front(); q.pop();
                if (cur == y_orig) { cycle = true; break; }
                // Existing-def edges:
                const auto& def_aig = cnf.get_def(cur);
                if (def_aig != nullptr) {
                    std::set<uint32_t> defds;
                    AIG::get_dependent_vars(def_aig, defds, cur);
                    for (auto d : defds) {
                        if (visited.insert(d).second) q.push(d);
                    }
                }
                // Candidate-def edges:
                auto it = cand_deps_orig.find(cur);
                if (it != cand_deps_orig.end()) {
                    for (auto d : it->second) {
                        if (visited.insert(d).second) q.push(d);
                    }
                }
            }
            if (cycle) to_drop.push_back(y_orig);
        }
        for (uint32_t y_orig : to_drop) aigs[y_new_of[y_orig]] = nullptr;
    }

    uint32_t total = 0;
    for (uint32_t v = 0; v < cnf.nVars(); v++) if (aigs[v]) total++;
    if (total > 0) cnf.map_aigs_to_orig(aigs, cnf.nVars());
    verb_print(1, "[unate_def/gate-def]"
        << " eq: " << n_eq
        << " and-or: " << n_and
        << " (cycles dropped: " << (n_eq + n_and - total) << ")"
        << " T: " << setprecision(3) << fixed << (cpuTime() - t0));
    return total;
}

uint32_t Unate::synthesis_unate_def_pass(SimplifiedCNF& cnf, std::vector<Lit>& unates) {
    const double my_time = cpuTime();
    uint32_t new_units = 0;
    // Refresh classification: prior passes added unit clauses, which may
    // have promoted some to_define vars into the "settled" buckets.
    cnf.get_var_types(0 | verbose_debug_enabled, "unate_def_pass").unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) return 0;

    auto s = setup_f_not_f(cnf);

    // Add copied-side definition constraints: i' <-> H_i(X, Y') for all i in I.
    const auto new_to_orig = cnf.get_new_to_orig_var();
    Lit true_lit = lit_Undef;
    auto get_true_lit = [&]() -> Lit {
        if (true_lit == lit_Undef) {
            s->new_var();
            true_lit = Lit(s->nVars()-1, false);
            s->add_clause({true_lit});
        }
        return true_lit;
    };

    for(const auto& i_new: backward_defined) {
        if (input.count(i_new)) continue;

        assert(new_to_orig.count(i_new) > 0);
        const Lit orig = new_to_orig.at(i_new);
        const auto& aig = cnf.get_def(orig.var());
        assert(aig != nullptr && "Already-defined var must have an AIG definition");

        std::vector<Lit> tmp;
        std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> aig_to_copy_visitor =
          [&](AIGT type, const uint32_t var_orig, const bool neg, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                return neg ? ~get_true_lit() : get_true_lit();
            }
            if (type == AIGT::t_lit) {
                const Lit lit_new = cnf.orig_to_new_lit(Lit(var_orig, neg));
                if (input.count(lit_new.var())) return lit_new;
                assert(lit_new.var() < cnf.nVars());
                return Lit(lit_new.var() + cnf.nVars(), lit_new.sign());
            }
            if (type == AIGT::t_and) {
                const Lit l_lit = *left;
                const Lit r_lit = *right;
                s->new_var();
                const Lit and_out = Lit(s->nVars() - 1, false);
                tmp.clear();
                tmp = {~and_out, l_lit};
                s->add_clause(tmp);
                tmp = {~and_out, r_lit};
                s->add_clause(tmp);
                tmp = {~l_lit, ~r_lit, and_out};
                s->add_clause(tmp);
                return neg ? ~and_out : and_out;
            }
            release_assert(false && "Unhandled AIG type in synthesis_unate_def");
          };

        std::map<aig_ptr, Lit> cache;
        const Lit out_lit = AIG::transform<Lit>(aig, aig_to_copy_visitor, cache);

        // new_to_orig stores whether CNF var is sign-flipped wrt orig var.
        const Lit out_in_new_space = out_lit ^ orig.sign();
        const Lit i_copy = Lit(i_new + cnf.nVars(), false);
        s->add_clause({~i_copy, out_in_new_space});
        s->add_clause({i_copy, ~out_in_new_space});
    }

    verb_print(2, "[unate_def] already-defined vars in CNF: " << backward_defined.size());

    assert(var_to_indic.empty());
    var_to_indic.resize(cnf.nVars(), var_Undef);
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        if (backward_defined.count(i)) continue;
        s->new_var();
        const Lit ind_l = Lit(s->nVars()-1, false);

        // when indic is TRUE, they are equal
        const auto y = Lit (i, false);
        const auto y_hat = Lit(i + cnf.nVars(), false);
        vector<Lit> tmp;
        tmp.push_back(~ind_l);
        tmp.push_back(y_hat);
        tmp.push_back(~y);
        s->add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        s->add_clause(tmp);

        tmp.clear();
        tmp.push_back(ind_l);
        tmp.push_back(~y_hat);
        tmp.push_back(~y);
        s->add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        s->add_clause(tmp);
        var_to_indic[i] = ind_l.var();
    }
    /* if (conf.verb >= 3) dump_cnf<Lit>(*s, "unate_def-start.cnf", input); */

    vector<Lit> assumps;
    vector<Lit> cl;

    // Precompute the candidate-indicator list once. Each iteration of the
    // outer test loop previously rebuilt this by walking every CNF variable
    // and doing log-time set lookups (input/backward_defined/already_tested);
    // for benchmarks with thousands of variables and hundreds of to_define
    // tests, that was tens of millions of map operations on the hot path
    // before the SAT call. Now it's a fixed-size O(to_define) copy plus a
    // single index swap to drop the current test var.
    vector<Lit> cand_indics;
    vector<uint32_t> cand_var;
    cand_indics.reserve(to_define.size());
    cand_var.reserve(to_define.size());
    vector<int> var_to_cand_pos(cnf.nVars(), -1);
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        if (backward_defined.count(i)) continue;
        const auto ind = var_to_indic.at(i);
        if (ind == var_Undef) continue;
        var_to_cand_pos[i] = (int)cand_indics.size();
        cand_indics.push_back(Lit(ind, false));
        cand_var.push_back(i);
    }
    // Tested vars get a permanent clause forcing their indic; we also pop
    // them out of cand_indics by swapping with the back. cand_indics keeps
    // exactly the still-untested indics, so the per-test assumps copy is
    // proportional to remaining work, not to the whole CNF.

    uint32_t tested_num = 0;
    for(uint32_t test: to_define) {
        assert(input.count(test) == 0);
        verb_print(3, "[unate_def] testing var: " << test+1);
        tested_num++;
        if (tested_num % 300 == 299) {
            verb_print(1, "[unate_def] test no: " << setw(5) << tested_num
                << " new units: " << setw(4) << new_units
                << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
        }

        // Drop test's own indic from cand_indics (swap-with-back) so its
        // y_hat=y constraint isn't asserted for this test's flip.
        const int test_pos = var_to_cand_pos[test];
        assert(test_pos >= 0 && test_pos < (int)cand_indics.size());
        const int last = (int)cand_indics.size() - 1;
        if (test_pos != last) {
            std::swap(cand_indics[test_pos], cand_indics[last]);
            std::swap(cand_var[test_pos],    cand_var[last]);
            var_to_cand_pos[cand_var[test_pos]] = test_pos;
        }
        cand_indics.pop_back();
        cand_var.pop_back();
        var_to_cand_pos[test] = -1;

        assumps = cand_indics;
        for(int flip = 0; flip < 2; flip++) {
            assumps.push_back(Lit(test, !flip));
            assumps.push_back(Lit(test+cnf.nVars(), flip));
            verb_print(3, "[unate_def] assumps : " << assumps);
            const auto ret = s->solve(&assumps);
            if (ret == l_False) {
                Lit l = {Lit(test, flip)};
                unates.push_back(l);
                cnf.add_clause({l});
                verb_print(2, "[unate_def] good test. Setting: " << std::setw(3)  << l
                    << " T: " << fixed << setprecision(2) << (cpuTime() - my_time));
                l = Lit(test+cnf.nVars(), flip);
                cl = {l};
                s->add_clause(cl);
                new_units++;
                break;
            }
            assumps.pop_back();
            assumps.pop_back();
        }
        s->add_clause({Lit(var_to_indic.at(test), false)});
    }

    const double total_time = cpuTime() - my_time;
    verb_print(1, COLYEL "[unate_def/pass] "
            << " units: " << setw(7) << new_units
            << " tested: " << setw(7) << tested_num
            << " tests/s: " << setprecision(2) << fixed << setw(6) << safe_div(tested_num, total_time)
            << " T: " << setprecision(2) << fixed << total_time);

    // var_to_indic was sized fresh for this pass; clear so the next pass
    // (with its own setup_f_not_f) can reuse the slot.
    var_to_indic.clear();
    return new_units;
}

void Unate::synthesis_unate(SimplifiedCNF& cnf) {
    double my_time = cpuTime();
    uint32_t new_units = 0;
    cnf.get_var_types(conf.verb | verbose_debug_enabled, "start do_unate").unpack_to(input, to_define, backward_defined);
    if (to_define.empty()) {
        verb_print(1, "[unate] No variables to define, skipping");
        return;
    }

    auto s = setup_f_not_f(cnf);
    var_to_indic.clear();
    var_to_indic.resize(cnf.nVars(), var_Undef);
    for(uint32_t i = 0; i < cnf.nVars(); i++) {
        if (input.count(i)) continue;
        s->new_var();
        const Lit ind_l = Lit(s->nVars()-1, false);

        // when indic is TRUE, they are equal
        const auto y = Lit (i, false);
        const auto y_hat = Lit(i + cnf.nVars(), false);
        vector<Lit> tmp;
        tmp.push_back(~ind_l);
        tmp.push_back(y_hat);
        tmp.push_back(~y);
        s->add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        s->add_clause(tmp);

        tmp.clear();
        tmp.push_back(ind_l);
        tmp.push_back(~y_hat);
        tmp.push_back(~y);
        s->add_clause(tmp);
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        s->add_clause(tmp);
        var_to_indic[i] = ind_l.var();
    }
    /* if (conf.verb >= 3) dump_cnf<Lit>(*s, "unate-start.cnf", input); */

    vector<Lit> assumps;
    vector<Lit> cl;

    uint32_t tested_num = 0;
    vector<Lit> unates;
    for(uint32_t test: to_define) {
        assert(input.count(test) == 0);
        verb_print(3, "[unate] testing var: " << test+1);
        /* if (s->removed_var(test)) continue; */
        tested_num++;
        if (tested_num % 300 == 299) {
            verb_print(1, "[unate] test no: " << setw(5) << tested_num
                << " new units: " << setw(4) << new_units
                << " T: " << setprecision(2) << fixed << (cpuTime() - my_time));
        }

        for(int flip = 0; flip < 2; flip++) {
            assumps.clear();
            assumps.push_back(Lit(test, !flip));
            assumps.push_back(Lit(test+cnf.nVars(), flip));
            for(uint32_t i = 0; i < cnf.nVars(); i++) {
                if (i == test) continue;
                if (input.count(i)) continue;
                auto ind = var_to_indic.at(i);
                assert(ind != var_Undef);
                assumps.push_back(Lit(ind, false));
            }
            verb_print(3, "[unate] assumps : " << assumps);
            const auto ret = s->solve(&assumps);
            if (ret == l_False) {

                Lit l = {Lit(test, flip)};
                unates.push_back(l);
                cnf.add_clause({l});
                verb_print(2, "[unate] good test. Setting: " << std::setw(3)  << l
                    << " T: " << fixed << setprecision(2) << (cpuTime() - my_time));

                l = Lit(test+cnf.nVars(), flip);
                cl = {l};
                s->add_clause(cl);
                new_units++;
                break;
            }
        }
    }

    cnf.add_fixed_values(unates);
    auto [input2, to_define2, backward_defined2] = cnf.get_var_types(0 | verbose_debug_enabled, "end do_unate");
    verb_print(1, COLRED "[unate] Done. synthesis_unate"
        << " tested: " << tested_num
        << " defined: " << to_define.size() - to_define2.size()
        << " still to define: " << to_define2.size()
        << " T: " << (cpuTime() - my_time));
}

unique_ptr<ArjunInt::MetaSolver> Unate::setup_f_not_f(const SimplifiedCNF& cnf) {
    double my_time = cpuTime();

    vector<Lit> tmp;
    auto s = std::make_unique<ArjunInt::MetaSolver>();
    s->new_vars(cnf.nVars()*2); // one for orig, one for copy
    s->set_verbosity(0);

    vector<Lit> not_f_cls;
    for(const auto& cl: cnf.get_clauses()) {
        // F(x)
        s->add_clause(cl);

        // !F(y)
        s->new_var(); // new var for each clause
                      // z is true iff clause is TRUE
        const Lit z = Lit(s->nVars()-1, false);

        // (C shifted) V -z
        tmp.clear();
        for(const auto& l: cl) {
            if (input.count(l.var())) tmp.push_back(l);
            else tmp.push_back(Lit(l.var()+cnf.nVars(), l.sign()));
        }
        tmp.push_back(~z);
        s->add_clause(tmp);

        // (each -lit in C, shifted) V z
        for(const auto& l: cl) {
            tmp.clear();
            if (input.count(l.var())) tmp = {~l,  z};
            else tmp = {Lit(l.var()+cnf.nVars(), !l.sign()),  z};
            s->add_clause(tmp);
        }
        not_f_cls.push_back(~z);
    }

    // At least ONE clause must be FALSE
    s->add_clause(not_f_cls);

    verb_print(1, "[unate/def] Built up the F and ~F_x_y solver. T: "
            << fixed << setprecision(2) << (cpuTime() - my_time));
    return s;
}
