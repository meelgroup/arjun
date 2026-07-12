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

#include "interpolant.h"
#include "constants.h"
#include "time_mem.h"

#include <cadical.hpp>
#include <algorithm>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <memory>
#include <sstream>

using namespace CMSat;
using namespace CaDiCaL;
using namespace ArjunInt;
using namespace ArjunNS;
using std::vector;
using std::set;
using std::endl;
using std::cout;

Interpolant::~Interpolant() {
    // Detach the tracer, else the solver's destructor deletes it.
    if (solver && tracer) solver->disconnect_proof_tracer(tracer.get());
}

// Apply each indicator equality (v' := v) to a copy of the pristine doubled
// CNF (folding copy-2 vars into copy-1), drop tautologies/dups. Returns merges.
uint32_t Interpolant::build_effective_clauses(vector<vector<Lit>>& out_cls) const {
    vector<uint32_t> subst_var(tot_num_vars);
    for (uint32_t i = 0; i < tot_num_vars; i++) subst_var[i] = i;
    uint32_t num_merged = 0;
    for (const auto& u : indicator_units) {
        auto it = indic_to_defvar.find(u.var());
        if (it == indic_to_defvar.end()) continue; // not an equality indic
        const uint32_t v2 = it->second + orig_num_vars;
        if (v2 < tot_num_vars && subst_var[v2] != it->second) {
            subst_var[v2] = it->second;
            num_merged++;
        }
    }

    out_cls.clear();
    out_cls.reserve(all_cls.size());
    std::set<vector<Lit>> seen;
    vector<Lit> nc;
    for (const auto& c : all_cls) {
        nc.clear();
        for (const auto& l : c) nc.emplace_back(subst_var[l.var()], l.sign());
        std::sort(nc.begin(), nc.end());
        nc.erase(std::unique(nc.begin(), nc.end()), nc.end());
        bool taut = false;
        for (size_t i = 0; i + 1 < nc.size(); i++)
            if (nc[i].var() == nc[i+1].var()) { taut = true; break; } // v and ¬v adjacent
        if (taut) continue;
        if (seen.insert(nc).second) out_cls.push_back(nc);
    }
    return num_merged;
}

void Interpolant::load_solver(bool is_rebuild) {
    // Fresh CaDiCaL + tracer, (re)load the effective doubled CNF.
    const double my_time = cpuTime();
    solver = std::make_unique<Solver>();
    tracer = std::make_unique<InterpTracerMcMillan>(conf, *aig_mng, *input_vars);
    tracer->b_local_from = orig_num_vars;
    solver->connect_proof_tracer(tracer.get(), true);

    vector<vector<Lit>> eff_cls;
    const uint32_t num_merged = build_effective_clauses(eff_cls);
    for (const auto& c : eff_cls) {
        tracer->next_is_b = is_b_clause(c);
        for (const auto& l : c) solver->add(lit_to_pl(l));
        solver->add(0);
        tracer->next_is_b = false;
    }

    if (is_rebuild) {
        num_rebuilds++;
        verb_print(1, "[interp] rebuild #" << num_rebuilds
                << " after " << solves_since_rebuild << " defines"
                << " conf: " << solver->conflicts()
                << " --  merged " << num_merged << " vars"
                << ", clauses " << all_cls.size() << " -> " << eff_cls.size()
                << " mem: " << memUsedTotal()/(1024*1024) << " MB"
                << " T: " << std::fixed << std::setprecision(2)
                << (cpuTime() - my_time));
    }
    solves_since_rebuild = 0;
}

void Interpolant::fill_from_solver(SATSolver* cms_solver,
        uint32_t _orig_num_vars, const AIGManager& _aig_mng,
        const set<uint32_t>& _input_vars,
        const vector<uint32_t>& var_to_indic) {
    orig_num_vars = _orig_num_vars;
    tot_num_vars = cms_solver->nVars();
    aig_mng = &_aig_mng;
    input_vars = &_input_vars;

    // Reverse var_to_indic: indic var -> the copy-1 var v it ties (v' := v).
    indic_to_defvar.clear();
    for (uint32_t v = 0; v < orig_num_vars && v < var_to_indic.size(); v++) {
        const uint32_t indic = var_to_indic[v];
        if (indic != var_Undef) indic_to_defvar[indic] = v;
    }

    // Extract the doubled CNF once; indicator units arrive via add_unit_cl.
    all_cls.clear();
    cms_solver->start_getting_constraints(false);
    vector<Lit> cl;
    bool is_xor, rhs;
    while (cms_solver->get_next_constraint(cl, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        all_cls.push_back(cl);
    }
    cms_solver->end_getting_constraints();

    load_solver(false);
    verb_print(2, "[interp] doubled CNF loaded into incremental solver: "
            << all_cls.size() << " clauses, " << tot_num_vars << " vars");
}

void Interpolant::add_unit_cl(const vector<Lit>& cl) {
    assert(cl.size() == 1);
    tracer->next_is_b = true;
    solver->add(lit_to_pl(cl[0]));
    solver->add(0);
    tracer->next_is_b = false;
    indicator_units.push_back(cl[0]);
}

bool Interpolant::generate_interpolant(const vector<Lit>& assumptions,
        uint32_t test_var) {
    verb_print(3, "[interp] generating interpolant for var: " << test_var+1);
    verb_print(3, "[interp] assumptions: " << assumptions);

    if (!conf.debug_synth.empty()) {
        std::stringstream name;
        name << conf.debug_synth << "-core-" << test_var+1 << ".cnf";
        verb_print(1, "[interp] writing doubled CNF to: " << name.str());
        const size_t n = all_cls.size() + indicator_units.size()
                + assumptions.size();
        auto f = std::ofstream(name.str());
        f << "p cnf " << tot_num_vars << " " << n << endl;
        f << "c orig_num_vars: " << orig_num_vars << endl;
        f << "c output: " << test_var+1 << endl;
        for (const auto& c : all_cls) f << c << " 0" << endl;
        for (const auto& l : indicator_units) f << l << " 0" << endl;
        for (const auto& l : assumptions) f << l << " 0" << endl;
        f.close();
    }

    // One assumption-based solve; assumptions are assumed (not added as
    // clauses), so the doubled CNF stays reusable for the next call.
    tracer->reset_per_solve();
    // Skip deep vars whose proof would OOM or stall.
    if (iconf.interp_max_confl != 0)
        solver->limit("conflicts", (int)iconf.interp_max_confl);
    for (const auto& l : assumptions) solver->assume(lit_to_pl(l));
    const int ret = solver->solve();
    release_assert(ret != 10 && "interpolant solve must not be SAT");
    if (ret != 20) {
        // Budget exhausted: no definition. maybe_rebuild's conflict trigger
        // frees the maps rather than rebuilding an identical solver per skip.
        verb_print(1, "[interp] var " << test_var+1 << " exceeded "
                << iconf.interp_max_confl << " conflicts; skipping definition");
        maybe_rebuild();
        return false;
    }
    // conclude() emits the proof conclusion so the tracer sees the refutation.
    solver->conclude();

    aig_lit interp = tracer->build_interpolant();
    release_assert(interp != nullptr
        && "interpolant: build_interpolant returned null after UNSAT proof");
    defs[test_var] = interp;
    verb_print(5, "[interp] definition of var " << test_var+1
            << " is: " << interp);

    // Periodically rebuild: bounds the tracer's clause maps and re-simplifies
    // the doubled CNF with the accumulated indicator equalities substituted in.
    ++solves_since_rebuild;
    maybe_rebuild();
    return true;
}

// Rebuild on either trigger: enough defines or enough conflicts
void Interpolant::maybe_rebuild() {
    const bool by_defines = solves_since_rebuild >= iconf.interp_rebuild_every;
    const bool by_confl = iconf.interp_rebuild_max_confl != 0
            && (uint64_t)solver->conflicts() >= iconf.interp_rebuild_max_confl;
    if (!by_defines && !by_confl) return;
    solver->disconnect_proof_tracer(tracer.get());
    load_solver(true);
}

aig_lit InterpTracerMcMillan::lit_aig(Lit l) {
    auto it = lit_to_aig.find(l);
    if (it != lit_to_aig.end()) return it->second;
    aig_lit a = AIG::new_lit(l);
    lit_to_aig[l] = a;
    return a;
}

// new_and with structural hash-consing: reuse an existing AND with the same
// child edges, so equal cones collapse into a shared DAG before simplify_aig.
aig_lit InterpTracerMcMillan::hash_and(const aig_lit& l, const aig_lit& r) {
    // Key over child edges (ordered by nid, then sign), so we hit the table
    // before new_and allocates.
    uint64_t lnid = l.node->nid, rnid = r.node->nid;
    bool lneg = l.neg, rneg = r.neg;
    if (std::tie(rnid, rneg) < std::tie(lnid, lneg)) {
        std::swap(lnid, rnid);
        std::swap(lneg, rneg);
    }
    const AIG::AIGKey key{AIGT::t_and, 0u, lnid, lneg, rnid, rneg};
    auto it = and_table.find(key);
    if (it != and_table.end()) return it->second;

    aig_lit res = AIG::new_and(l, r);
    // Cache only positive AND nodes (new_and may fold to const/leaf/neg edge).
    if (res.node != nullptr && res->type == AIGT::t_and && !res.neg)
        and_table.emplace(key, res);
    return res;
}

aig_lit InterpTracerMcMillan::hash_or(const aig_lit& l, const aig_lit& r) {
    return ~hash_and(~l, ~r);
}

// OR over the shared (B-visible) literals in `cl` — the McMillan label
// for an A-side clause. Empty shared set => label FALSE.
aig_lit InterpTracerMcMillan::or_of_shared_lits(const vector<Lit>& cl) {
    // Fold shared literals in canonical order so clauses with the same
    // shared-literal set produce an identical OR-AIG (shared via hash_or).
    vector<Lit> ins;
    ins.reserve(cl.size());
    for (const auto& l : cl) {
        if (is_shared(l.var())) ins.push_back(l);
    }
    if (ins.empty()) return aig_mng.new_const(false);
    std::sort(ins.begin(), ins.end());
    ins.erase(std::unique(ins.begin(), ins.end()), ins.end());

    vector<aig_lit> leaves;
    leaves.reserve(ins.size());
    for (const auto& l : ins) leaves.push_back(lit_aig(l));

    // Balanced binary fold to keep AIG depth small.
    while (leaves.size() > 1) {
        vector<aig_lit> next;
        next.reserve((leaves.size() + 1) / 2);
        for (size_t i = 0; i < leaves.size(); i += 2) {
            if (i + 1 >= leaves.size()) next.push_back(leaves[i]);
            else next.push_back(hash_or(leaves[i], leaves[i+1]));
        }
        leaves.swap(next);
    }
    assert(!leaves.empty());
    return leaves[0];
}

void InterpTracerMcMillan::add_original_clause(uint64_t id, bool /*red*/,
        const vector<int>& clause, bool restored) {
    // Restored clauses are re-announced after weakening with a stale
    // next_is_b; they were recorded on first add, so skip the re-record.
    if (restored && cls.count(id)) return;
    orig_count++;
    cls[id] = pl_to_lit_cl(clause);
    if (next_is_b) b_clause_ids.insert(id);
    // Label deferred to build_interpolant(): it depends on input_vars (which
    // grow between solves) and only proof-core clauses ever need one.
    VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 5) {
        cout << "c o [interp] orig id=" << id
             << (next_is_b ? " B" : " A")
             << " sz=" << cls[id].size() << endl;
    });
}

// McMillan label of an original clause from the current input_vars.
aig_lit InterpTracerMcMillan::original_label(uint64_t id) {
    const vector<Lit>& cl = cls[id];
    if (!b_clause_ids.count(id)) {
        // A-side clause: label = OR of shared lits in the clause. Shared
        // lits are 'b'-labelled, so they are the disjuncts.
        return or_of_shared_lits(cl);
    }
    // B-side clause: shared lits are 'b'-labelled → label TRUE.
    return aig_mng.new_const(true);
}

void InterpTracerMcMillan::reset_per_solve() {
    // cls / antec / b_clause_ids persist across solves; labels and the
    // and-table don't (they depend on input_vars, which may have grown).
    labels.clear();
    and_table.clear();
    empty_id = UINT64_MAX;
    conclusion_type = 0;
    conclusion_root = UINT64_MAX;
    out = nullptr;
    derived_count = 0;
    core_count = 0;
}

void InterpTracerMcMillan::add_assumption_clause(uint64_t id,
        const vector<int>& clause, const vector<uint64_t>& antecedents) {
    // The failing-assumption clause: the negation of the assumption core,
    // derived purely from the formula. Treat it like any derived clause.
    derived_count++;
    cls[id] = pl_to_lit_cl(clause);
    antec[id] = antecedents;
}

void InterpTracerMcMillan::conclude_unsat(CaDiCaL::ConclusionType type,
        const vector<uint64_t>& ids) {
    conclusion_type = type;
    // ASSUMPTIONS: failing-assumption clause id. CONFLICT: empty clause id.
    // (Doubled-CNF interpolation uses assumptions only, so ids[0] suffices.)
    if (!ids.empty()) conclusion_root = ids[0];
}

void InterpTracerMcMillan::add_derived_clause(uint64_t id, bool /*red*/,
        const vector<int>& clause,
        const vector<uint64_t>& antecedents) {
    derived_count++;
    // Record only; label building is deferred to build_interpolant() so we
    // resolve just the proof core, not every derived clause cadical streams.
    cls[id] = pl_to_lit_cl(clause);
    antec[id] = antecedents;
    if (cls[id].empty() && empty_id == UINT64_MAX) {
        empty_id = id;
        VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 4) {
            cout << "c o [interp] empty clause derived id=" << id << endl;
        });
    }
}

aig_lit InterpTracerMcMillan::build_interpolant() {
    // Refutation root: failing-assumption clause for ASSUMPTIONS UNSAT,
    // else the derived empty clause.
    uint64_t root;
    if (conclusion_type == CaDiCaL::ASSUMPTIONS) {
        if (conclusion_root == UINT64_MAX) return nullptr;
        root = conclusion_root;
    } else {
        if (empty_id == UINT64_MAX) return nullptr;
        root = empty_id;
    }

    // Backward reachability from the root over the recorded antecedent
    // chains. Only these clauses contribute to the interpolant.
    std::unordered_set<uint64_t> reach;
    vector<uint64_t> stack{root};
    while (!stack.empty()) {
        const uint64_t id = stack.back();
        stack.pop_back();
        if (!reach.insert(id).second) continue;
        auto it = antec.find(id);
        if (it == antec.end()) continue;  // original clause: a proof leaf
        for (const uint64_t a : it->second) stack.push_back(a);
    }

    // Forward pass: cadical IDs are monotonic, so ascending-ID order is a
    // valid topological order. Labels (both kinds) are built here.
    vector<uint64_t> order(reach.begin(), reach.end());
    std::sort(order.begin(), order.end());
    for (const uint64_t id : order) {
        if (antec.count(id)) {
            build_derived_label(id);
            core_count++;
        } else {
            labels[id] = original_label(id);
        }
    }

    auto it = labels.find(root);
    aig_lit res = (it != labels.end()) ? it->second : nullptr;

    if (res != nullptr && conclusion_type == CaDiCaL::ASSUMPTIONS) {
        // Root clause is {¬a : a failing assumption}. Resolve with each unit a
        // to the empty clause: B-side units AND in TRUE (no-op), A-side OR in.
        for (const Lit m : cls[root]) {           // m = ¬a
            const Lit a = ~m;
            const aig_lit unit_lab = (a.var() >= b_local_from)
                ? aig_mng.new_const(true)             // B-side unit → TRUE
                : or_of_shared_lits(vector<Lit>{a});  // A-side unit
            const bool want_and =
                is_shared(m.var()) || m.var() >= b_local_from;
            res = want_and ? hash_and(res, unit_lab) : hash_or(res, unit_lab);
        }
    }

    out = res;
    return out;
}

void InterpTracerMcMillan::build_derived_label(uint64_t id) {
    const vector<uint64_t>& antecedents = antec[id];
    if (antecedents.empty()) {
        // A derived clause always has antecedents.
        assert(false && "derived clause with no antecedents");
    }
    // cadical usually lists antecedents in reverse resolution order; try
    // reversed first, fall back to forward.
    if (resolve_chain(id, antecedents, /*reversed=*/true)) return;
    if (resolve_chain(id, antecedents, /*reversed=*/false)) return;
    assert(false && "failed to resolve derived clause's antecedent chain");
}

bool InterpTracerMcMillan::resolve_chain(uint64_t id,
        const vector<uint64_t>& chain, bool reversed) {
    release_assert(!chain.empty());
    const size_t n = chain.size();
    // Walk `chain` forward or reversed without copying it.
    auto at = [&](size_t i) { return reversed ? chain[n - 1 - i] : chain[i]; };

    // Initial resolvent = first clause in the chain + its label.
    const uint64_t id1 = at(0);
    auto it_lab = labels.find(id1);
    release_assert(it_lab != labels.end() && "antecedent label must exist");
    aig_lit lab = it_lab->second;
    // Generation-stamped resolvent membership: O(1) has/add/del, no hashing.
    res_gen++;
    auto res_has = [&](Lit l) {
        const uint32_t i = l.toInt();
        return i < res_stamp.size() && res_stamp[i] == res_gen;
    };
    auto res_add = [&](Lit l) {
        const uint32_t i = l.toInt();
        if (i >= res_stamp.size()) res_stamp.resize(i + 1, 0);
        res_stamp[i] = res_gen;
    };
    auto res_del = [&](Lit l) {
        const uint32_t i = l.toInt();
        if (i < res_stamp.size()) res_stamp[i] = 0;  // 0 == untouched; res_gen is always >=1
    };
    for (const auto& l : cls[id1]) res_add(l);

    // Batch consecutive same-op steps into balanced ANDs/ORs to avoid
    // stack-blowing left-leaning chains.
    vector<aig_lit> batch;
    bool batch_is_and = false;
    auto flush_batch = [&]() {
        if (batch.empty()) return;
        // Balanced fold over batch.
        while (batch.size() > 1) {
            vector<aig_lit> next;
            next.reserve((batch.size() + 1) / 2);
            for (size_t i = 0; i < batch.size(); i += 2) {
                if (i + 1 >= batch.size()) next.push_back(batch[i]);
                else if (batch_is_and)
                    next.push_back(hash_and(batch[i], batch[i+1]));
                else
                    next.push_back(hash_or (batch[i], batch[i+1]));
            }
            batch.swap(next);
        }
        lab = batch[0];
        batch.clear();
    };

    for (size_t i = 1; i < n; i++) {
        const uint64_t id2 = at(i);
        auto it_cl = cls.find(id2);
        auto it_l2 = labels.find(id2);
        release_assert(it_cl != cls.end() && it_l2 != labels.end() &&
                       "antecedent clause and label must exist");
        const vector<Lit>& cl = it_cl->second;

        // Find the resolution pivot: the unique literal in the new
        // antecedent whose negation is currently in the resolvent.
        Lit pivot = lit_Undef;
        for (const auto& l : cl) {
            if (res_has(~l)) {
                release_assert(pivot == lit_Undef && "chain step has multiple pivots");
                pivot = ~l;
            }
        }
        release_assert(pivot != lit_Undef && "chain step has no pivot");

        // Update resolvent.
        res_del(pivot);
        for (const auto& l : cl) {
            if (l == ~pivot) continue;
            res_add(l);
        }

        const bool pivot_is_shared = is_shared(pivot.var());

        // McMillan: shared or B-local pivot → AND, A-local → OR.
        const bool want_and = pivot_is_shared || pivot.var() >= b_local_from;

        if (!batch.empty() && batch_is_and != want_and) flush_batch();
        if (batch.empty()) {
            batch_is_and = want_and;
            batch.push_back(lab);
        }
        batch.push_back(it_l2->second);
    }
    flush_batch();
    labels[id] = lab;
    return true;
}
