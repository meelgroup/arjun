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

#include "interp_repair.h"
#include "constants.h"
#include <cadical.hpp>
#include <climits>
#include <iomanip>
#include <iostream>
#include <random>

using namespace ArjunInt;
using namespace ArjunNS;
using namespace CaDiCaL;
using namespace CMSat;
using std::vector;
using std::set;
using std::map;
using std::cout;
using std::endl;
using std::setprecision;
using std::fixed;

aig_ptr InterpTracerMcMillan::lit_aig(Lit l) {
    auto it = lit_to_aig.find(l);
    if (it != lit_to_aig.end()) return it->second;
    aig_ptr a = AIG::new_lit(l);
    lit_to_aig[l] = a;
    return a;
}

// new_and + structural hash-consing: if an AND node with the same
// child edges already exists, reuse it. Equal cones across the proof
// thus collapse into a shared DAG before simplify_aig ever runs.
aig_ptr InterpTracerMcMillan::hash_and(const aig_ptr& l, const aig_ptr& r) {
    aig_ptr res = AIG::new_and(l, r);
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

    and_table.emplace(key, aig_ptr(res.node, false));
    return res;
}

aig_ptr InterpTracerMcMillan::hash_or(const aig_ptr& l, const aig_ptr& r) {
    return ~hash_and(~l, ~r);
}

// OR over the input literals in `cl` — the McMillan/Pudlák label for an
// A-side clause. Empty input set => label FALSE.
aig_ptr InterpTracerMcMillan::or_of_input_lits(const vector<Lit>& cl) {
    // Collect the input literals and fold them in a canonical order:
    // two A-clauses with the same input-literal *set* (in any clause
    // order) then produce the identical OR-AIG, so hash_or's table
    // shares it instead of building two structurally-equal cones.
    vector<Lit> ins;
    ins.reserve(cl.size());
    for (const auto& l : cl) {
        if (input_vars.count(l.var())) ins.push_back(l);
    }
    if (ins.empty()) return aig_mng.new_const(false);
    std::sort(ins.begin(), ins.end());
    ins.erase(std::unique(ins.begin(), ins.end()), ins.end());

    vector<aig_ptr> leaves;
    leaves.reserve(ins.size());
    for (const auto& l : ins) leaves.push_back(lit_aig(l));

    // Balanced binary fold to keep AIG depth small.
    while (leaves.size() > 1) {
        vector<aig_ptr> next;
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
        const vector<int>& clause, bool /*restored*/) {
    orig_count++;
    vector<Lit> cl_lits = pl_to_lit_cl(clause);
    cls[id] = cl_lits;

    if (next_is_b) {
        b_clause_ids.insert(id);
        if (system == SYS_PUDLAK) {
            // Pudlák: shared (input) lits are 'ab'-labelled, so a B-side
            // clause's partial interpolant is ∧ ¬l over its shared lits.
            // Our B clauses are input units, so this is just ¬(the lit).
            aig_ptr lab = aig_mng.new_const(true);
            for (const auto& l : cl_lits)
                if (input_vars.count(l.var())) lab = hash_and(lab, lit_aig(~l));
            labels[id] = lab;
        } else {
            // McMillan: shared lits are 'b'-labelled → B-clause label TRUE.
            labels[id] = aig_mng.new_const(true);
        }
    } else {
        // A-side clause: label = OR of input lits in the clause. Shared
        // lits are 'b' (McMillan) or 'ab' (Pudlák); either way they are
        // the disjuncts, so this base label is the same for both systems.
        labels[id] = or_of_input_lits(cl_lits);
    }
    VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 5) {
        cout << "c o [interp] orig id=" << id
             << (next_is_b ? " B" : " A")
             << " sz=" << cl_lits.size() << endl;
    });
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

aig_ptr InterpTracerMcMillan::build_interpolant() {
    if (empty_id == UINT64_MAX) return nullptr;

    // Backward reachability from the empty clause over the recorded
    // antecedent chains. Only these clauses contribute to the interpolant.
    set<uint64_t> reach;
    vector<uint64_t> stack{empty_id};
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
    // which is how std::set iterates — is a valid topological order.
    for (const uint64_t id : reach) {
        if (antec.count(id)) {
            build_derived_label(id);
            core_count++;
        }
    }

    auto it = labels.find(empty_id);
    out = (it != labels.end()) ? it->second : nullptr;
    return out;
}

void InterpTracerMcMillan::build_derived_label(uint64_t id) {
    const vector<uint64_t>& antecedents = antec[id];
    if (antecedents.empty()) {
        // Shouldn't happen for a derived clause — abandon the interpolant.
        assert(false && "derived clause with no antecedents?");
    }
    // cadical hands the antecedent list in reverse linear-resolution
    // order, so replaying it reversed reconstructs the chain.
    const vector<uint64_t> rev(antecedents.rbegin(), antecedents.rend());
    if (resolve_chain(id, rev)) return;
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
    aig_ptr lab = it_lab->second;
    set<Lit> resolvent(cls[id1].begin(), cls[id1].end());

    // Batch consecutive same-op steps into balanced ANDs/ORs to avoid
    // stack-blowing left-leaning chains.
    vector<aig_ptr> batch;
    bool batch_is_and = false;
    auto flush_batch = [&]() {
        if (batch.empty()) return;
        // Balanced fold over batch.
        while (batch.size() > 1) {
            vector<aig_ptr> next;
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

        const bool pivot_is_input = input_vars.count(pivot.var());

        // Pudlák: a shared (input) pivot is 'ab'-labelled, so the
        // partial interpolant is the selector (v∨I1)∧(¬v∨I2), where I1
        // belongs to the parent containing the variable positively and
        // I2 to the parent containing it negatively. `lab` is the
        // running parent (which holds `pivot`); `it_l2->second` is the
        // new antecedent (which holds `~pivot`).
        if (pivot_is_input && system == SYS_PUDLAK) {
            flush_batch();
            const aig_ptr I_run = lab;               // parent with `pivot`
            const aig_ptr I_new = it_l2->second;     // parent with `~pivot`
            aig_ptr I1, I2;
            if (!pivot.sign()) { I1 = I_run; I2 = I_new; }
            else               { I1 = I_new; I2 = I_run; }
            const aig_ptr v_pos = lit_aig(Lit(pivot.var(), false));
            const aig_ptr v_neg = lit_aig(Lit(pivot.var(), true));
            lab = hash_and(hash_or(v_pos, I1), hash_or(v_neg, I2));
            continue;
        }

        // McMillan: shared (input) pivot → AND, A-local pivot → OR.
        const bool want_and = pivot_is_input;

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

InterpRepair::InterpRepair(const Config& _conf,
        const SimplifiedCNF& _cnf,
        const set<uint32_t>& _input_vars,
        AIGManager& _aig_mng)
    : conf(_conf), cnf(_cnf), input_vars(_input_vars), aig_mng(_aig_mng)
{
    is_input.assign(cnf.nVars(), 0);
    for (const auto& v : input_vars) {
        if (v < is_input.size()) is_input[v] = 1;
    }
}

uint32_t InterpRepair::setup_mini_cnf(CaDiCaL::Solver& solver,
        InterpTracerMcMillan& tracer, Lit to_repair_lit,
        const std::vector<Lit>& conflict) const
{
    auto add_unit_a = [&](Lit l) {
        tracer.next_is_b = false;
        solver.add(lit_to_pl(l));
        solver.add(0);
    };
    auto add_unit_b = [&](Lit l) {
        tracer.next_is_b = true;
        solver.add(lit_to_pl(l));
        solver.add(0);
        tracer.next_is_b = false;
    };

    // Non-input conflict units (A side) + ~to_repair (A side). The
    // conflict is the negated assumptions, so we add ~l to reproduce the
    // original assumptions.
    for (const auto& l : conflict) {
        if (l.var() < is_input.size() && is_input[l.var()]) continue;
        add_unit_a(~l);
    }
    add_unit_a(~to_repair_lit);

    // Input conflict units (B side).
    uint32_t b_marked = 0;
    for (const auto& l : conflict) {
        if (l.var() >= is_input.size() || !is_input[l.var()]) continue;
        add_unit_b(~l);
        b_marked++;
    }

    // 1) Original CNF clauses (all A-side) — only the subset relevant to
    // this conflict. Clauses the assumption units already satisfy, and
    // clauses in disjoint variable components, contribute nothing to the
    // UNSAT proof and so are left out, shrinking the solver's state.
    const auto& clauses = cnf.get_clauses();
    const std::vector<uint32_t> relevant =
        collect_relevant_clauses(to_repair_lit, conflict);
    tracer.next_is_b = false;
    for (const uint32_t ci : relevant) {
        for (const auto& l : clauses[ci]) solver.add(lit_to_pl(l));
        solver.add(0);
    }
    total_minicnf_clauses += clauses.size();
    total_minicnf_clauses_kept += relevant.size();
    VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 3) {
        cout << "c o [interp-repair] mini-CNF: " << relevant.size() << " / "
             << clauses.size() << " original clauses kept" << endl;
    });

    return b_marked;
}

void InterpRepair::build_serialized_cnf() const {
    // Serialise once: lits as cadical signed ints, each clause terminated
    // by 0. Concatenated so we can solver->add(...) in a tight loop on
    // every interp call without re-walking cnf.get_clauses().
    cnf_serialized.clear();
    size_t total = 0;
    for (const auto& cl : cnf.get_clauses()) total += cl.size() + 1;
    cnf_serialized.reserve(total);
    for (const auto& cl : cnf.get_clauses()) {
        for (const auto& l : cl) cnf_serialized.push_back(lit_to_pl(l));
        cnf_serialized.push_back(0);
    }
    cnf_serialized_built = true;
}

void InterpRepair::build_occ() const {
    // Per-literal occurrence lists, keyed by Lit::toInt() (= var*2+sign).
    // Built once and reused: collect_relevant_clauses walks them on every
    // interp call to do unit propagation and the connectivity sweep.
    const auto& clauses = cnf.get_clauses();
    occ.assign((size_t)cnf.nVars() * 2, {});
    for (uint32_t ci = 0; ci < clauses.size(); ci++) {
        for (const auto& l : clauses[ci]) {
            const uint32_t li = l.toInt();
            if (li < occ.size()) occ[li].push_back(ci);
        }
    }
    occ_built = true;
}

// Find the original-CNF clauses that actually matter for the interpolant
// of this conflict.
//
// The mini-CNF is M = F ∪ U, where F is the original CNF and U is the set
// of assumption units (~conflict lits, ~to_repair). M is UNSAT. We want a
// subset M' ⊆ M that (a) keeps every B-side input unit, (b) is still
// UNSAT, and (c) yields an interpolant valid for the full partition. Any
// such M' works: the McMillan/Pudlák interpolant of M' satisfies A'→I and
// I∧B unsat, and since A' ⊆ A the always-on miter A→I still holds.
//
// Two reductions, both sound:
//
//  1. Unit propagation. Propagate U through F. A clause satisfied by the
//     propagated assignment is redundant *provided* the clauses that
//     forced the assignment are kept (the "reason" clauses) — then the
//     solver re-derives the same forced literals and M' is equisatisfiable
//     to M. Reason clauses are themselves original F clauses, so the A/B
//     partition is unchanged.
//
//  2. Connectivity. The UNSAT proof stays within one connected component
//     of the variable graph (resolution never crosses disjoint
//     sub-formulas); that is the component holding the assumption units.
//     Other components are sub-formulas of the satisfiable spec, hence
//     satisfiable, and are dropped.
//
// If UP alone refutes M, the conflicting clause plus the transitive reason
// chain behind it is a complete UNSAT proof — everything else is dropped.
std::vector<uint32_t> InterpRepair::collect_relevant_clauses(
        Lit to_repair_lit, const vector<Lit>& conflict) const
{
    if (!occ_built) build_occ();
    const auto& clauses = cnf.get_clauses();
    const uint32_t n_cls = clauses.size();

    // Variable universe: the CNF, plus any assumption var beyond nVars().
    uint32_t n_vars = cnf.nVars();
    auto bump = [&](uint32_t v) { if (v + 1 > n_vars) n_vars = v + 1; };
    for (const auto& l : conflict) bump(l.var());
    bump(to_repair_lit.var());

    // Ternary assignment from unit propagation: 0=unset, 1=true, 2=false.
    vector<uint8_t> val(n_vars, 0);
    vector<int64_t> reason(n_vars, -1);   // forcing clause idx, -1=assumption
    vector<Lit> trail;
    trail.reserve(n_vars);
    bool conflict_hit = false;
    int64_t conflict_cl = -1;

    auto lit_val = [&](Lit l) -> uint8_t {   // 0 undef, 1 true, 2 false
        const uint8_t v = val[l.var()];
        if (v == 0) return 0;
        return ((v == 1) ^ l.sign()) ? 1 : 2;
    };
    auto enqueue = [&](Lit l, int64_t rsn) {
        const uint32_t v = l.var();
        const uint8_t want = l.sign() ? 2 : 1;
        if (val[v] == 0) { val[v] = want; reason[v] = rsn; trail.push_back(l); }
        else if (val[v] != want) conflict_hit = true;
    };

    // Assumption units (direct): ~conflict lits and ~to_repair.
    for (const auto& l : conflict) enqueue(~l, -1);
    enqueue(~to_repair_lit, -1);
    // Original-CNF unit clauses force their literal unconditionally.
    for (uint32_t ci = 0; ci < n_cls && !conflict_hit; ci++) {
        if (clauses[ci].size() == 1) enqueue(clauses[ci][0], (int64_t)ci);
    }

    // Unit propagation to fixpoint (or first conflict).
    for (size_t qi = 0; qi < trail.size() && !conflict_hit; qi++) {
        const Lit l = trail[qi];                  // l is now true
        const uint32_t false_idx = (~l).toInt();  // clauses with ~l falsified
        if (false_idx >= occ.size()) continue;
        for (const uint32_t ci : occ[false_idx]) {
            uint32_t n_undef = 0;
            Lit last_undef = lit_Undef;
            bool sat = false;
            for (const auto& cli : clauses[ci]) {
                const uint8_t lv = lit_val(cli);
                if (lv == 1) { sat = true; break; }
                if (lv == 0) { n_undef++; last_undef = cli; }
            }
            if (sat) continue;
            if (n_undef == 0) { conflict_hit = true; conflict_cl = (int64_t)ci; break; }
            if (n_undef == 1) enqueue(last_undef, (int64_t)ci);
        }
    }

    vector<char> keep(n_cls, 0);

    if (conflict_hit) {
        // UP alone refutes the mini-CNF: keep the conflicting clause and
        // the transitive set of reason clauses behind its literals.
        vector<uint32_t> work;
        auto add_reasons_of = [&](const vector<Lit>& cl) {
            for (const auto& cli : cl) {
                if (cli.var() >= n_vars) continue;
                const int64_t r = reason[cli.var()];
                if (r >= 0 && !keep[r]) { keep[r] = 1; work.push_back((uint32_t)r); }
            }
        };
        if (conflict_cl >= 0) {
            keep[conflict_cl] = 1;
            add_reasons_of(clauses[conflict_cl]);
        }
        while (!work.empty()) {
            const uint32_t ci = work.back(); work.pop_back();
            add_reasons_of(clauses[ci]);
        }
        vector<uint32_t> out;
        for (uint32_t ci = 0; ci < n_cls; ci++) if (keep[ci]) out.push_back(ci);
        return out;
    }

    // No UP conflict: keep clauses not satisfied by the propagated
    // assignment, plus every reason clause (the solver needs them to
    // re-derive the forced literals).
    for (uint32_t ci = 0; ci < n_cls; ci++) {
        bool sat = false;
        for (const auto& cli : clauses[ci]) {
            if (lit_val(cli) == 1) { sat = true; break; }
        }
        if (!sat) keep[ci] = 1;
    }
    for (uint32_t v = 0; v < n_vars; v++) {
        if (reason[v] >= 0) keep[reason[v]] = 1;
    }

    // Connectivity sweep. The mini-CNF's UNSAT lives entirely within one
    // connected component of its variable-incidence graph — a resolution
    // proof never crosses variable-disjoint sub-formulas. That component
    // is the one holding the assumption units: every other component is a
    // sub-formula of the (satisfiable) spec CNF and so is itself
    // satisfiable, contributing nothing. BFS the kept clauses outward
    // from the assumption variables and drop whatever is not reached.
    vector<char> var_seen(n_vars, 0);
    vector<char> cl_seen(n_cls, 0);
    vector<uint32_t> vq;
    auto see_var = [&](uint32_t v) {
        if (v < n_vars && !var_seen[v]) { var_seen[v] = 1; vq.push_back(v); }
    };
    for (const auto& l : conflict) see_var(l.var());
    see_var(to_repair_lit.var());
    while (!vq.empty()) {
        const uint32_t v = vq.back(); vq.pop_back();
        for (uint32_t s = 0; s < 2; s++) {
            const uint32_t li = Lit(v, s != 0).toInt();
            if (li >= occ.size()) continue;
            for (const uint32_t ci : occ[li]) {
                if (!keep[ci] || cl_seen[ci]) continue;
                cl_seen[ci] = 1;
                for (const auto& cli : clauses[ci]) see_var(cli.var());
            }
        }
    }

    vector<uint32_t> out;
    for (uint32_t ci = 0; ci < n_cls; ci++) {
        // An empty clause (degenerate, refutes on its own) carries no
        // variable, so the sweep never reaches it — keep it regardless.
        if (keep[ci] && (cl_seen[ci] || clauses[ci].empty())) out.push_back(ci);
    }

    SLOW_DEBUG_DO({
        // Every dropped clause must be provably inert: either already
        // satisfied by the UP assignment (keep[ci]==0 is only set for
        // satisfied non-reason clauses), or in a variable component
        // disjoint from the assumption units (!cl_seen). A clause that is
        // neither live-and-connected nor inert is a keep-logic bug.
        for (uint32_t ci = 0; ci < n_cls; ci++) {
            if (keep[ci] && (cl_seen[ci] || clauses[ci].empty())) continue;
            bool sat = false;
            for (const auto& cli : clauses[ci])
                if (lit_val(cli) == 1) { sat = true; break; }
            release_assert((sat || !cl_seen[ci])
                && "collect_relevant_clauses dropped a live, connected clause");
        }
    });
    return out;
}

aig_ptr InterpRepair::solve_one_interpolant(
        Lit to_repair_lit, const vector<Lit>& conflict,
        uint64_t conflict_budget,
        int system, int& out_ret)
{
    out_ret = 0;
    // Build the mini CNF and solve on a fresh CaDiCaL with proof
    // tracing; the tracer produces the McMillan interpolant.
    auto solver = std::make_unique<Solver>();
    // Disable in-processing & vivification: they mutate original clauses
    // while the tracer is attached, leaving derived clauses whose
    // antecedent IDs don't map to our labels.
    solver->set("inprocessing", 0);
    solver->set("preprocessing", 0);
    if (conflict_budget > 0) {
        // Clamp to int max — cadical's limit API takes an int.
        const int64_t clamped = (conflict_budget > (uint64_t)INT_MAX)
            ? INT_MAX : (int64_t)conflict_budget;
        solver->limit("conflicts", (int)clamped);
    }
    InterpTracerMcMillan tracer(conf, aig_mng, input_vars);
    tracer.system = system;
    solver->connect_proof_tracer(&tracer, true);

    const uint32_t b_marked = setup_mini_cnf(*solver, tracer,
            to_repair_lit, conflict);
    if (b_marked == 0) {
        // No input units. Interpolant would be trivial. Bail.
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] no input B units; bailing" << endl);
        solver->disconnect_proof_tracer(&tracer);
        out_ret = 20;  // not a solver failure; just nothing to interpolate
        return nullptr;
    }

    const int ret = solver->solve();
    solver->disconnect_proof_tracer(&tracer);
    out_ret = ret;
    // The mini CNF asserts the conflict, so the search must come back UNSAT
    // — never SAT (10). ret==0 (UNKNOWN) is only legitimate when a conflict
    // budget capped the search; with no budget the solve must terminate.
    release_assert(ret != 10
        && "interp-repair mini CNF came back SAT — conflict was not a real conflict");
    release_assert((ret == 20 || conflict_budget > 0)
        && "interp-repair solve returned UNKNOWN with no conflict budget");
    if (ret != 20) return nullptr;  // 20=UNSAT, 0=UNKNOWN(budget exhausted)

    aig_ptr one = tracer.build_interpolant();
    // The proof exists (UNSAT) and the tracer recorded it, so reconstructing
    // the interpolant from the proof trace must always succeed.
    release_assert(one != nullptr
        && "interp-repair tracer failed to reconstruct interpolant from proof");
    // Diagnostics: proof-core trim ratio and chain-reconstruction bails.
    total_proof_derived += tracer.derived_count;
    total_proof_core += tracer.core_count;
    VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 3) {
        cout << "c o [interp-repair] proof core: "
             << tracer.core_count << " / " << tracer.derived_count
             << " derived clauses"
    });
    return one;
}

aig_ptr InterpRepair::compute_interpolant(
        [[maybe_unused]] uint32_t y_rep, Lit to_repair_lit,
        const vector<Lit>& conflict, uint32_t max_aig_nodes,
        uint64_t conflict_budget,
        int system)
{
    calls++;
    total_conflict_lits += conflict.size();

    // Empty conflict: y_rep forced to ctx[y_rep]; perform_repair already
    // special-cases this. No interpolation needed.
    if (conflict.empty()) {
        calls_failed_empty_or_no_input++;
        return nullptr;
    }

    // No input lits in conflict => no B side => trivial interpolant.
    bool has_input = false;
    for (const auto& l : conflict) {
        if (l.var() < is_input.size() && is_input[l.var()]) {
            has_input = true; break;
        }
    }
    if (!has_input) {
        calls_failed_empty_or_no_input++;
        return nullptr;
    }

    // Compute the interpolant from a single cadical search. I satisfies
    // A→I and I∧B UNSAT, so its negation is the must-flip region the
    // repair generalises over.
    int ret = 0;
    aig_ptr interp = solve_one_interpolant(to_repair_lit, conflict,
            conflict_budget, system, ret);
    if (interp == nullptr) {
        if (ret == 0) {
            // UNKNOWN is only reachable with a conflict budget set (asserted
            // in solve_one_interpolant), so the budget was exhausted.
            calls_budget_exhausted++;
            VERBOSE_DEBUG_DO(cout << "c o [interp-repair] budget exhausted ("
                << conflict_budget << " conflicts); falling back" << endl);
        } else {
            // ret==20 with no input B units: nothing to interpolate.
            calls_failed_other++;
            VERBOSE_DEBUG_DO(cout << "c o [interp-repair] no input B units;"
                " falling back" << endl);
        }
        return nullptr;
    }

    // Clean up the proof-driven AIG before returning.
    interp = AIG::simplify_aig(interp);

    // SLOW_DEBUG: verify the interpolant only references input vars.
    SLOW_DEBUG_DO({
        if (interp != nullptr) {
            set<const AIG*> seen2;
            std::function<bool(const aig_ptr&)> check = [&](const aig_ptr& a) -> bool {
                if (a == nullptr) return true;
                if (a->type == AIGT::t_const) return true;
                if (a->type == AIGT::t_lit) {
                    if (a->var >= is_input.size() || !is_input[a->var]) {
                        cout << "c o [interp-repair] SLOW_DEBUG: interpolant has non-input leaf var="
                             << (a->var+1) << endl;
                        return false;
                    }
                    return true;
                }
                if (!seen2.insert(a.get()).second) return true;
                return check(a->l) && check(a->r);
            };
            if (!check(interp)) {
                assert(false && "interpolant has non-input leaf — tracer bug");
            }
        }
    });

    // I = TRUE would make the must-flip region empty (infinite loop);
    // it also contradicts the UNSAT. Bail.
    if (interp != nullptr && interp->type == AIGT::t_const && !interp.neg) {
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] interpolant = TRUE; bailing" << endl);
        calls_failed_other++;
        return nullptr;
    }
    // I = FALSE means y_rep is forced to ctx[y_rep] everywhere; allowed
    // through, SLOW_DEBUG checks catch any unsoundness.
    VERBOSE_DEBUG_DO(if (interp != nullptr && interp->type == AIGT::t_const && interp.neg) {
        cout << "c o [interp-repair] interpolant = FALSE; y_rep forced to ctx everywhere" << endl;
    });

    // Quick sanity: interpolant must evaluate to FALSE on the CEX inputs.
    if (!quick_check_interpolant_excludes_cex(interp, conflict)) {
        calls_quick_check_failed++;
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] quick_check_excludes_cex FAILED — bailing" << endl);
        return nullptr;
    }

    SLOW_DEBUG_DO(
        if (!slow_check_a_implies_i(to_repair_lit, conflict, interp, conflict_budget)) {
            VERBOSE_DEBUG_DO(cout << "c o [interp-repair] A→I verification FAILED"
                " — falling back to conflict clause" << endl);
            assert(false && "interpolant failed A→I check — tracer or verifier bug");
        }
    );

    // Size: count internal AND nodes in this AIG sub-tree.
    set<const AIG*> seen;
    std::function<void(const aig_ptr&)> walk = [&](const aig_ptr& a) {
        if (a == nullptr) return;
        if (a->type == AIGT::t_const || a->type == AIGT::t_lit) return;
        if (!seen.insert(a.get()).second) return;
        walk(a->l);
        walk(a->r);
    };
    walk(interp);
    const size_t interp_nodes = seen.size();

    if (max_aig_nodes > 0 && interp_nodes > max_aig_nodes) {
        calls_failed_oversize++;
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] interp has "
            << interp_nodes << " AIG nodes > cap " << max_aig_nodes
            << "; falling back" << endl);
        // A McMillan interpolant can be much larger than the Pudlák
        // selector form. Rather than dropping straight to the conflict
        // clause, retry once with Pudlák — it is weaker but often fits.
        if (system == InterpTracerMcMillan::SYS_MCMILLAN) {
            calls_oversize_pudlak_retry++;
            VERBOSE_DEBUG_DO(cout << "c o [interp-repair] retrying oversize "
                "McMillan interpolant with Pudlák" << endl);
            return compute_interpolant(y_rep, to_repair_lit, conflict,
                max_aig_nodes, conflict_budget,
                InterpTracerMcMillan::SYS_PUDLAK);
        }
        return nullptr;
    }
    total_interp_nodes += interp_nodes;
    if (interp_nodes > max_interp_nodes_seen) max_interp_nodes_seen = interp_nodes;
    if (interp_nodes < conflict.size()) interp_smaller_than_conflict++;
    else if (interp_nodes > conflict.size()) interp_larger_than_conflict++;
    interp_size_hist[bucket_of(interp_nodes)]++;
    conflict_size_hist[bucket_of(conflict.size())]++;

    // Interpolant input support vs conflict input-literal count, for
    // the support-shrinkage stat.
    {
        std::set<uint32_t> support;
        std::set<const AIG*> seen_supp;
        std::function<void(const aig_ptr&)> walk_supp = [&](const aig_ptr& a) {
            if (a == nullptr) return;
            if (a->type == AIGT::t_lit) {
                if (a->var < is_input.size() && is_input[a->var]) support.insert(a->var);
                return;
            }
            if (a->type == AIGT::t_const) return;
            if (!seen_supp.insert(a.get()).second) return;
            walk_supp(a->l);
            walk_supp(a->r);
        };
        walk_supp(interp);
        total_interp_support += support.size();
        uint64_t input_lits = 0;
        for (const auto& l : conflict)
            if (l.var() < is_input.size() && is_input[l.var()]) input_lits++;
        total_input_lits_in_conflict += input_lits;
    }

    calls_succeeded++;
    return interp;
}

// Full miter: check A & ~I is UNSAT (i.e. A -> I), with I Tseitin-encoded
// inline. `conflict_budget` (0 = unlimited) caps the solve; an exhausted
// budget is reported as a verification failure so the caller falls back.
bool InterpRepair::slow_check_a_implies_i(
        Lit to_repair_lit,
        const vector<Lit>& conflict,
        const aig_ptr& interp,
        uint64_t conflict_budget) const
{
    if (interp == nullptr) return true;

    auto solver = std::make_unique<Solver>();
    solver->set("inprocessing", 0);
    solver->set("preprocessing", 0);
    if (conflict_budget > 0) {
        const int64_t clamped = (conflict_budget > (uint64_t)INT_MAX)
            ? INT_MAX : (int64_t)conflict_budget;
        solver->limit("conflicts", (int)clamped);
    }
    auto add_cl = [&](const vector<Lit>& cl) {
        for (const auto& l : cl) solver->add(lit_to_pl(l));
        solver->add(0);
    };
    auto add_unit = [&](Lit l) {
        solver->add(lit_to_pl(l));
        solver->add(0);
    };

    // A-side original CNF — added from the pre-serialised buffer rather
    // than re-walking cnf.get_clauses() on every (always-on) verify.
    if (!cnf_serialized_built) build_serialized_cnf();
    for (int v : cnf_serialized) solver->add(v);
    // A-side: original CNF + ~to_repair, plus the non-input (y_other)
    // conflict units.
    for (const auto& l : conflict) {
        if (l.var() < is_input.size() && is_input[l.var()]) continue;
        add_unit(~l);
    }
    add_unit(~to_repair_lit);

    // Tseitin-encode interp; fresh helper IDs start at cnf.nVars().
    uint32_t next_var = cnf.nVars();
    map<aig_ptr, Lit> cache;
    std::function<Lit(const aig_ptr&)> enc = [&](const aig_ptr& a) -> Lit {
        auto it = cache.find(a);
        if (it != cache.end()) return it->second;
        Lit ret;
        if (a->type == AIGT::t_const) {
            uint32_t tv = next_var++;
            Lit tl(tv, false);
            add_unit(tl);
            ret = a.neg ? ~tl : tl;
        } else if (a->type == AIGT::t_lit) {
            ret = Lit(a->var, a.neg);
        } else { // AND
            Lit lleft = enc(a->l);
            Lit rright = enc(a->r);
            uint32_t gv = next_var++;
            Lit gl(gv, false);
            add_cl({~gl, lleft});
            add_cl({~gl, rright});
            add_cl({gl, ~lleft, ~rright});
            ret = a.neg ? ~gl : gl;
        }
        cache[a] = ret;
        return ret;
    };
    Lit interp_lit = enc(interp);
    add_unit(~interp_lit);  // assert ¬I

    int ret = solver->solve();
    if (ret != 20) {
        // 10 = SAT (interpolant genuinely violates A→I), 0 = budget
        // exhausted (cannot conclude). Either way verification failed.
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] slow_check_a_implies_i: "
             << "miter NOT UNSAT (cadical ret=" << ret << ")" << endl);
        return false;
    }
    return true;
}

bool InterpRepair::sample_check_interpolant(
        Lit to_repair_lit,
        const vector<Lit>& conflict,
        const aig_ptr& interp,
        uint32_t num_samples,
        uint64_t seed) const
{
    if (interp == nullptr) return true;

    // Only I(X)=FALSE samples can violate the must-flip claim.
    std::vector<uint32_t> ins(input_vars.begin(), input_vars.end());
    if (ins.empty()) return true;
    std::mt19937_64 rng(seed);

    // This check verifies against the full A-side CNF, so it needs the
    // complete serialised form (setup_mini_cnf only feeds a subset now).
    if (!cnf_serialized_built) build_serialized_cnf();

    [[maybe_unused]] int num_false_seen = 0;
    for (uint32_t s = 0; s < num_samples; s++) {
        // Build full assignment with random input bits.
        std::vector<lbool> assign(cnf.nVars(), l_Undef);
        for (uint32_t v : ins) {
            assign[v] = (rng() & 1) ? l_True : l_False;
        }
        std::map<aig_ptr, lbool> cache;
        std::vector<aig_ptr> defs(cnf.nVars(), nullptr);
        const lbool ival = AIG::evaluate(assign, interp, defs, cache);
        if (ival != l_False) continue; // only must-flip region matters
        num_false_seen++;

        // Check F(X,Y) & y_rep=wrong is UNSAT for this input pattern.
        auto solver = std::make_unique<Solver>();
        solver->set("inprocessing", 0);
        solver->set("preprocessing", 0);
        for (int v : cnf_serialized) solver->add(v);
        // Pin inputs.
        for (uint32_t v : ins) {
            solver->add(assign[v] == l_True ? (int)v + 1 : -((int)v + 1));
            solver->add(0);
        }
        // ~to_repair = wrong y_rep value
        solver->add(lit_to_pl(~to_repair_lit));
        solver->add(0);
        // The repair only fires when the y_other conflict literals also
        // match the CEX, so the must-flip claim is conditional on them —
        // pin them here too.
        for (const auto& l : conflict) {
            if (l.var() < is_input.size() && is_input[l.var()]) continue;
            solver->add(lit_to_pl(~l));
            solver->add(0);
        }

        int ret = solver->solve();
        if (ret == 10) { // SAT — interp says must-flip but it's not!
            cout << "c o [interp-repair] sample_check FAILED on seed=" << seed
                 << " sample=" << s << ": I(X)=FALSE but F is sat with y_rep=wrong" << endl;
            return false;
        }
        // ret == 20 (UNSAT) or 0 (UNKNOWN, shouldn't happen w/o budget): pass
    }

    VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 4) {
        cout << "c o [interp-repair] sample_check ok ("
             << num_false_seen << " false samples checked, " << num_samples
             << " total)" << endl;
    });
    return true;
}

bool InterpRepair::quick_check_interpolant_excludes_cex(
        const aig_ptr& interp, const vector<Lit>& conflict) const
{
    if (interp == nullptr) return false;

    // Partial assignment from the input lits in conflict; conflict lits
    // are negated assumptions, so use ~l for the CEX value.
    vector<lbool> assign(cnf.nVars(), l_Undef);
    for (const auto& l : conflict) {
        if (l.var() >= assign.size()) continue;
        if (l.var() < is_input.size() && is_input[l.var()]) {
            const Lit asm_lit = ~l;
            assign[l.var()] = asm_lit.sign() ? l_False : l_True;
        }
    }

    // Evaluate the interpolant; l_Undef result => report pass.
    map<aig_ptr, lbool> cache;
    vector<aig_ptr> defs(cnf.nVars(), nullptr);
    lbool v = AIG::evaluate(assign, interp, defs, cache);
    if (v == l_Undef) return true; // can't tell; don't fail
    return v == l_False;
}

void InterpRepair::print_stats(const std::string& prefix) const {
    cout << "c o " << prefix
         << " calls: " << calls
         << " ok: " << calls_succeeded
         << " oversize: " << calls_failed_oversize
         << " quickfail: " << calls_quick_check_failed
         << " trivial: " << calls_failed_empty_or_no_input
         << " other: " << calls_failed_other
         << " avg conflict-lits: "
         << fixed << setprecision(1)
         << (calls ? (double)total_conflict_lits / (double)calls : 0.0)
         << " avg interp-nodes: "
         << (calls_succeeded ? (double)total_interp_nodes / (double)calls_succeeded : 0.0)
         << " max interp-nodes: " << max_interp_nodes_seen
         << " smaller/larger: " << interp_smaller_than_conflict
         << "/" << interp_larger_than_conflict
         << " mini-CNF kept: "
         << (total_minicnf_clauses
                ? safe_div(total_minicnf_clauses_kept*100.0, total_minicnf_clauses)
                : 0.0)
         << "%"
         << endl;
}
