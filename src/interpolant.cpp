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

#include <cadical.hpp>
#include <algorithm>
#include <fstream>
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

void Interpolant::load_solver() {
    // Fresh CaDiCaL + tracer, (re)load doubled CNF + indicator units.
    // A = clauses entirely in copy 1, B = everything else.
    solver = std::make_unique<Solver>();
    tracer = std::make_unique<InterpTracerMcMillan>(conf, *aig_mng, *input_vars);
    tracer->b_local_from = orig_num_vars;
    solver->connect_proof_tracer(tracer.get(), true);

    for (const auto& c : all_cls) {
        tracer->next_is_b = is_b_clause(c);
        for (const auto& l : c) solver->add(lit_to_pl(l));
        solver->add(0);
        tracer->next_is_b = false;
    }
    for (const auto& l : indicator_units) {
        tracer->next_is_b = true;
        solver->add(lit_to_pl(l));
        solver->add(0);
        tracer->next_is_b = false;
    }
    solves_since_rebuild = 0;
}

void Interpolant::fill_from_solver(SATSolver* cms_solver,
        uint32_t _orig_num_vars, const AIGManager& _aig_mng,
        const set<uint32_t>& _input_vars) {
    orig_num_vars = _orig_num_vars;
    tot_num_vars = cms_solver->nVars();
    aig_mng = &_aig_mng;
    input_vars = &_input_vars;

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

    load_solver();
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
    if (conf.interp_max_confl != 0)
        solver->limit("conflicts", (int)conf.interp_max_confl);
    for (const auto& l : assumptions) solver->assume(lit_to_pl(l));
    const int ret = solver->solve();
    release_assert(ret != 10 && "interpolant solve must not be SAT");
    if (ret != 20) {
        // Budget exhausted: rebuild to free the tracer maps.
        verb_print(1, "[interp] var " << test_var+1 << " exceeded "
                << conf.interp_max_confl << " conflicts; skipping definition");
        solver->disconnect_proof_tracer(tracer.get());
        load_solver();
        return false;
    }
    // conclude() emits the proof conclusion so the tracer sees the refutation.
    solver->conclude();

    aig_lit interp = tracer->build_interpolant();
    release_assert(interp != nullptr
        && "interpolant: build_interpolant returned null after UNSAT proof");
    interp = AIG::simplify_aig(interp);
    release_assert(interp != nullptr
        && "interpolant: simplify_aig returned null");

    defs[test_var] = interp;
    verb_print(5, "[interp] definition of var " << test_var+1
            << " is: " << interp);

    // Periodically rebuild so the tracer's clause maps don't grow unbounded.
    if (++solves_since_rebuild >= conf.interp_rebuild_every) {
        verb_print(2, "[interp] rebuilding incremental solver after "
                << solves_since_rebuild << " interpolants");
        solver->disconnect_proof_tracer(tracer.get());
        load_solver();
    }
    return true;
}

aig_lit InterpTracerMcMillan::lit_aig(Lit l) {
    auto it = lit_to_aig.find(l);
    if (it != lit_to_aig.end()) return it->second;
    aig_lit a = AIG::new_lit(l);
    lit_to_aig[l] = a;
    return a;
}

// new_and + structural hash-consing: if an AND node with the same
// child edges already exists, reuse it. Equal cones across the proof
// thus collapse into a shared DAG before simplify_aig ever runs.
aig_lit InterpTracerMcMillan::hash_and(const aig_lit& l, const aig_lit& r) {
    aig_lit res = AIG::new_and(l, r);
    // new_and may have folded to a constant, a leaf, or an input node.
    if (res.node == nullptr || res->type != AIGT::t_and) return res;

    // Canonical key: order the two child edges by (nid, neg).
    uint64_t lnid = res->l.node->nid, rnid = res->r.node->nid;
    bool lneg = res->l.neg, rneg = res->r.neg;
    if (std::tie(rnid, rneg) < std::tie(lnid, lneg)) {
        std::swap(lnid, rnid);
        std::swap(lneg, rneg);
    }
    const AIG::AIGKey key{AIGT::t_and, 0u, lnid, lneg, rnid, rneg};
    auto it = and_table.find(key);
    if (it != and_table.end()) return res.neg ? ~it->second : it->second;

    and_table.emplace(key, aig_lit(res.node, false));
    return res;
}

aig_lit InterpTracerMcMillan::hash_or(const aig_lit& l, const aig_lit& r) {
    return ~hash_and(~l, ~r);
}

// OR over the shared (B-visible) literals in `cl` — the McMillan label
// for an A-side clause. Empty shared set => label FALSE.
aig_lit InterpTracerMcMillan::or_of_shared_lits(const vector<Lit>& cl) {
    // Collect the shared literals and fold them in a canonical order:
    // two A-clauses with the same shared-literal *set* (in any clause
    // order) then produce the identical OR-AIG, so hash_or's table
    // shares it instead of building two structurally-equal cones.
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
    // A restored clause was already recorded on its first add; cadical
    // re-announces it after weakening, when next_is_b no longer reflects
    // its side — so skip the re-record.
    if (restored && cls.count(id)) return;
    orig_count++;
    cls[id] = pl_to_lit_cl(clause);
    if (next_is_b) b_clause_ids.insert(id);
    // The label is *not* computed here: it depends on input_vars, which
    // a persistent tracer sees grow between solves, and only proof-core
    // clauses ever need one. See original_label() / build_interpolant().
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
    // cls / antec / b_clause_ids persist — the clause database outlives a
    // single incremental solve — but labels and the and-table do not:
    // both depend on input_vars, which may have grown since last solve.
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
    // ASSUMPTIONS: one failing-assumption clause id. CONFLICT: the empty
    // clause id. (Failing constraints would give several ids, but the
    // doubled-CNF interpolation uses assumptions only.)
    if (!ids.empty()) conclusion_root = ids[0];
}

void InterpTracerMcMillan::add_derived_clause(uint64_t id, bool /*red*/,
        const vector<int>& clause,
        const vector<uint64_t>& antecedents) {
    derived_count++;
    // Record only — label construction is deferred to build_interpolant()
    // so we resolve solely the clauses on the proof core (those reachable
    // from the empty clause), not every derived clause cadical streams.
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
    // Refutation root: the failing-assumption clause for an
    // assumption-based UNSAT (conclude_unsat reported ASSUMPTIONS),
    // otherwise the derived empty clause.
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
    set<uint64_t> reach;
    vector<uint64_t> stack{root};
    while (!stack.empty()) {
        const uint64_t id = stack.back();
        stack.pop_back();
        if (!reach.insert(id).second) continue;
        auto it = antec.find(id);
        if (it == antec.end()) continue;  // original clause: a proof leaf
        for (const uint64_t a : it->second) stack.push_back(a);
    }

    // Forward pass: a derived clause's antecedents always have smaller
    // IDs (cadical hands out IDs monotonically), so ascending-ID order —
    // which is how std::set iterates — is a valid topological order. Both
    // original- and derived-clause labels are built here (deferred from
    // add_original_clause), so they use the current input_vars.
    for (const uint64_t id : reach) {
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
        // The root clause is {¬a : a a failing assumption}. Resolving it
        // with each assumption unit a reaches the empty clause; the label
        // of that empty clause is the interpolant. A B-side unit's label
        // is TRUE and is AND'd in (no change); an A-side unit's label is
        // OR'd in. So these steps only matter for an A-side input
        // assumption — but doing them keeps the result fully general.
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
    // cadical usually hands the antecedent list in reverse linear-
    // resolution order, so replaying it reversed reconstructs the chain;
    // fall back to forward order if that is not a clean linear chain.
    const vector<uint64_t> rev(antecedents.rbegin(), antecedents.rend());
    if (resolve_chain(id, rev)) return;
    if (resolve_chain(id, antecedents)) return;
    assert(false && "failed to resolve derived clause's antecedent chain");
}

bool InterpTracerMcMillan::resolve_chain(uint64_t id,
        const vector<uint64_t>& chain) {
    release_assert(!chain.empty());

    // Initial resolvent = first clause in the chain + its label.
    const uint64_t id1 = chain[0];
    auto it_lab = labels.find(id1);
    if (it_lab == labels.end()) {
        // Antecedent label missing — the chain cannot be reconstructed.
        labels[id] = aig_mng.new_const(false);
        return false;
    }
    aig_lit lab = it_lab->second;
    set<Lit> resolvent(cls[id1].begin(), cls[id1].end());

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

    for (size_t i = 1; i < chain.size(); i++) {
        const uint64_t id2 = chain[i];
        auto it_cl = cls.find(id2);
        auto it_l2 = labels.find(id2);
        if (it_cl == cls.end() || it_l2 == labels.end()) {
            // Antecedent missing: chain cannot be reconstructed.
            flush_batch();
            labels[id] = lab;
            return false;
        }
        const vector<Lit>& cl = it_cl->second;

        // Find the resolution pivot: the unique literal in the new
        // antecedent whose negation is currently in the resolvent.
        Lit pivot = lit_Undef;
        for (const auto& l : cl) {
            if (resolvent.count(~l)) {
                if (pivot != lit_Undef) {
                    // Multiple pivots — non-linear chain step. Bail.
                    flush_batch();
                    labels[id] = lab;
                    return false;
                }
                pivot = ~l;
            }
        }
        if (pivot == lit_Undef) {
            // No pivot — not a real resolution step. Bail.
            flush_batch();
            labels[id] = lab;
            return false;
        }

        // Update resolvent.
        resolvent.erase(pivot);
        for (const auto& l : cl) {
            if (l == ~pivot) continue;
            resolvent.insert(l);
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
