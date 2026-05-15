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
#include "time_mem.h"
#include <cadical.hpp>
#include <iomanip>
#include <iostream>
#include <algorithm>

using namespace ArjunInt;
using namespace ArjunNS;
using namespace CaDiCaL;
using namespace CMSat;
using std::vector;
using std::set;
using std::map;
using std::cout;
using std::endl;
using std::setw;
using std::setprecision;
using std::fixed;

aig_ptr InterpTracerMcMillan::lit_aig(Lit l) {
    auto it = lit_to_aig.find(l);
    if (it != lit_to_aig.end()) return it->second;
    aig_ptr a = AIG::new_lit(l);
    lit_to_aig[l] = a;
    return a;
}

// OR over only the input literals in `cl` (the shared-variable label
// for an A-side clause in McMillan's construction). An empty input set
// means the label is FALSE (no shared lits → can't justify anything).
aig_ptr InterpTracerMcMillan::or_of_input_lits(const vector<Lit>& cl) {
    vector<aig_ptr> leaves;
    leaves.reserve(cl.size());
    for (const auto& l : cl) {
        if (input_vars.count(l.var())) leaves.push_back(lit_aig(l));
    }
    if (leaves.empty()) return aig_mng.new_const(false);

    // Balanced binary fold to keep AIG depth small.
    while (leaves.size() > 1) {
        vector<aig_ptr> next;
        next.reserve((leaves.size() + 1) / 2);
        for (size_t i = 0; i < leaves.size(); i += 2) {
            if (i + 1 >= leaves.size()) next.push_back(leaves[i]);
            else next.push_back(AIG::new_or(leaves[i], leaves[i+1], false));
        }
        leaves.swap(next);
    }
    return leaves[0];
}

void InterpTracerMcMillan::add_original_clause(uint64_t id, bool /*red*/,
        const vector<int>& clause, bool /*restored*/) {
    orig_count++;
    vector<Lit> cl_lits = pl_to_lit_cl(clause);
    cls[id] = cl_lits;

    if (next_is_b) {
        // B-side clause: label = TRUE
        b_clause_ids.insert(id);
        labels[id] = aig_mng.new_const(true);
    } else {
        // A-side clause: label = OR of input lits in the clause
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
    vector<Lit> cl_lits = pl_to_lit_cl(clause);
    cls[id] = cl_lits;

    // Walk the resolution chain (cadical gives antecedents in chain order).
    // Reverse so we can iteratively resolve from the start. Following the
    // pattern used in interpolant.cpp.
    if (antecedents.empty()) {
        // Shouldn't happen for a derived clause, but be defensive.
        labels[id] = aig_mng.new_const(false);
        if (cl_lits.empty()) out = labels[id];
        return;
    }
    const vector<uint64_t> rantec(antecedents.rbegin(), antecedents.rend());

    // Initial resolvent = first antecedent's clause + label.
    const uint64_t id1 = rantec[0];
    auto it_lab = labels.find(id1);
    if (it_lab == labels.end()) {
        // Antecedent label missing — happens if cadical gave us a derived
        // clause whose antecedent we never observed (e.g. a vivified
        // pre-existing internal clause). Fail closed: empty interpolant.
        labels[id] = aig_mng.new_const(false);
        return;
    }
    aig_ptr lab = it_lab->second;
    set<Lit> resolvent(cls[id1].begin(), cls[id1].end());

    // Batch consecutive same-op steps into balanced ANDs/ORs (avoids
    // stack-blowing left-leaning chains, mirrors interpolant.cpp).
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
                    next.push_back(AIG::new_and(batch[i], batch[i+1], false));
                else
                    next.push_back(AIG::new_or (batch[i], batch[i+1], false));
            }
            batch.swap(next);
        }
        lab = batch[0];
        batch.clear();
    };

    for (size_t i = 1; i < rantec.size(); i++) {
        const uint64_t id2 = rantec[i];
        auto it_cl = cls.find(id2);
        auto it_l2 = labels.find(id2);
        if (it_cl == cls.end() || it_l2 == labels.end()) {
            // Antecedent missing: bail safely with what we have so far.
            flush_batch();
            labels[id] = lab;
            return;
        }
        const vector<Lit>& cl = it_cl->second;

        // Find the resolution pivot: the unique literal in the new
        // antecedent whose negation is currently in the resolvent.
        Lit pivot = lit_Undef;
        for (const auto& l : cl) {
            if (resolvent.count(~l)) {
                if (pivot != lit_Undef) {
                    // Multiple pivots — non-standard chain. Bail.
                    flush_batch();
                    labels[id] = lab;
                    return;
                }
                pivot = ~l;
            }
        }
        if (pivot == lit_Undef) {
            // No pivot — this shouldn't happen with a real resolution;
            // fail closed.
            flush_batch();
            labels[id] = lab;
            return;
        }

        // Update resolvent.
        resolvent.erase(pivot);
        for (const auto& l : cl) {
            if (l == ~pivot) continue;
            resolvent.insert(l);
        }

        // McMillan: shared (input) pivot → AND, A-local pivot → OR.
        const bool pivot_is_input = input_vars.count(pivot.var());
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
    if (cl_lits.empty()) {
        out = lab;
        VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 4) {
            cout << "c o [interp] empty clause derived; interpolant set" << endl;
        });
    }
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

aig_ptr InterpRepair::compute_interpolant(
        uint32_t y_rep, Lit to_repair_lit,
        const vector<Lit>& conflict, uint32_t max_aig_nodes)
{
    (void)y_rep;
    calls++;
    total_conflict_lits += conflict.size();
    const double t0 = cpuTime();

    // Build mini CNF:
    //   A side : original CNF clauses + non-input conflict-literal units
    //            + ~to_repair unit
    //   B side : input conflict-literal units
    //
    // Solve on a fresh CaDiCaL with proof tracing connected. Tracer
    // produces the McMillan interpolant in input vars.
    auto solver = std::make_unique<Solver>();
    InterpTracerMcMillan tracer(conf, aig_mng, input_vars);
    solver->connect_proof_tracer(&tracer, true);

    auto add_cl_a = [&](const vector<Lit>& cl) {
        tracer.next_is_b = false;
        for (const auto& l : cl) solver->add(lit_to_pl(l));
        solver->add(0);
    };
    auto add_unit_a = [&](Lit l) {
        tracer.next_is_b = false;
        solver->add(lit_to_pl(l));
        solver->add(0);
    };
    auto add_unit_b = [&](Lit l) {
        tracer.next_is_b = true;
        solver->add(lit_to_pl(l));
        solver->add(0);
        tracer.next_is_b = false;
    };

    // 1) Original CNF clauses (all A-side). We deliberately skip
    // cnf.get_red_clauses(): those are redundant learnts and aren't
    // required for UNSAT-side reproduction.
    for (const auto& cl : cnf.get_clauses()) add_cl_a(cl);

    // get_conflict() returns the negation of the failing assumption set
    // (so it forms a learnable clause). To reproduce the same UNSAT in a
    // fresh solver via unit clauses, we need to add the *original*
    // assumptions, i.e. ~l for each conflict literal l.
    //
    // 2) Non-input conflict units (A side) plus ~to_repair (A side).
    uint32_t b_marked = 0;
    for (const auto& l : conflict) {
        if (l.var() < is_input.size() && is_input[l.var()]) continue;
        add_unit_a(~l);
    }
    add_unit_a(~to_repair_lit);

    // 3) Input conflict units (B side).
    for (const auto& l : conflict) {
        if (l.var() >= is_input.size() || !is_input[l.var()]) continue;
        add_unit_b(~l);
        b_marked++;
    }
    total_setup_time += cpuTime() - t0;

    VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 3) {
        cout << "c o [interp-repair] added " << b_marked
             << " input units as B-side; total orig cls=" << tracer.orig_count
             << " derived (during add) =" << tracer.derived_count
             << endl;
    });
    if (b_marked == 0) {
        // No input units. Interpolant would be trivial. Bail.
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] no input B units; bailing" << endl);
        solver->disconnect_proof_tracer(&tracer);
        calls_failed_other++;
        return nullptr;
    }

    const double t_solve = cpuTime();
    int ret = solver->solve();
    total_solve_time += cpuTime() - t_solve;
    solver->disconnect_proof_tracer(&tracer);

    if (ret != 20) { // 20 = UNSAT in CaDiCaL
        // Should be UNSAT — if not, something is inconsistent.
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] solver returned non-UNSAT: "
                << ret << "; falling back" << endl);
        calls_failed_other++;
        return nullptr;
    }

    aig_ptr interp = tracer.out;
    if (interp == nullptr) {
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] interpolant is null after UNSAT; falling back" << endl);
        calls_failed_other++;
        return nullptr;
    }

    // Quick sanity: under the original CEX inputs (= the input units we
    // added), interpolant should evaluate to FALSE. (This is what makes
    // the repair correct.) Cheap to check.
    if (!quick_check_interpolant_excludes_cex(interp, conflict)) {
        calls_quick_check_failed++;
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] quick_check_excludes_cex FAILED — bailing" << endl);
        return nullptr;
    }

    // Size cap: count nodes in this AIG sub-tree.
    if (max_aig_nodes > 0) {
        set<const AIG*> seen;
        std::function<void(const aig_ptr&)> walk = [&](const aig_ptr& a) {
            if (a == nullptr) return;
            if (a->type == AIGT::t_const || a->type == AIGT::t_lit) return;
            if (!seen.insert(a.get()).second) return;
            walk(a->l);
            walk(a->r);
        };
        walk(interp);
        if (seen.size() > max_aig_nodes) {
            calls_failed_oversize++;
            VERBOSE_DEBUG_DO(cout << "c o [interp-repair] interp has "
                << seen.size() << " AIG nodes > cap " << max_aig_nodes
                << "; falling back" << endl);
            return nullptr;
        }
        total_interp_nodes += seen.size();
    } else {
        // Still count for stats.
        set<const AIG*> seen;
        std::function<void(const aig_ptr&)> walk = [&](const aig_ptr& a) {
            if (a == nullptr) return;
            if (a->type == AIGT::t_const || a->type == AIGT::t_lit) return;
            if (!seen.insert(a.get()).second) return;
            walk(a->l);
            walk(a->r);
        };
        walk(interp);
        total_interp_nodes += seen.size();
    }

    calls_succeeded++;
    return interp;
}

bool InterpRepair::quick_check_interpolant_excludes_cex(
        const aig_ptr& interp, const vector<Lit>& conflict) const
{
    if (interp == nullptr) return false;

    // Build a partial assignment from input lits in conflict. Conflict
    // literals are negations of the original assumptions, so we use ~l
    // for the actual CEX value (matching add_unit_b in compute_interpolant).
    vector<lbool> assign(cnf.nVars(), l_Undef);
    for (const auto& l : conflict) {
        if (l.var() >= assign.size()) continue;
        if (l.var() < is_input.size() && is_input[l.var()]) {
            const Lit asm_lit = ~l;
            assign[l.var()] = asm_lit.sign() ? l_False : l_True;
        }
    }

    // Evaluate the interpolant AIG at this partial assignment. If any
    // input is l_Undef (e.g. interpolant references an input not pinned
    // by the conflict), the result is undefined; we report pass to be
    // conservative.
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
         << " other_fail: " << calls_failed_other
         << " avg conflict-lits: "
         << fixed << setprecision(1)
         << (calls ? (double)total_conflict_lits / (double)calls : 0.0)
         << " avg interp-nodes: "
         << (calls_succeeded ? (double)total_interp_nodes / (double)calls_succeeded : 0.0)
         << " setup-T: " << fixed << setprecision(2) << total_setup_time
         << " solve-T: " << fixed << setprecision(2) << total_solve_time
         << endl;
}
