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
#include <climits>
#include <cstring>
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

// Build a small, stable key from (to_repair, conflict). Sort to make
// it order-independent: cadical may reorder the conflict literals
// between calls. Encoded as a packed string of int32s for std::map.
InterpRepair::CacheKey InterpRepair::make_signature(Lit to_repair_lit,
        const vector<Lit>& conflict) {
    std::vector<int> pls;
    pls.reserve(conflict.size() + 1);
    for (const auto& l : conflict) pls.push_back(lit_to_pl(l));
    pls.push_back(lit_to_pl(to_repair_lit));
    std::sort(pls.begin(), pls.end());
    CacheKey k;
    k.sig.resize(pls.size() * sizeof(int));
    std::memcpy(k.sig.data(), pls.data(), k.sig.size());
    return k;
}

aig_ptr InterpRepair::compute_interpolant(
        uint32_t y_rep, Lit to_repair_lit,
        const vector<Lit>& conflict, uint32_t max_aig_nodes,
        bool full_rewrite, uint64_t conflict_budget, bool unconditional)
{
    (void)y_rep;
    calls++;
    total_conflict_lits += conflict.size();

    // Conflict-signature cache lookup. Identical conflicts produce
    // identical interpolants under McMillan with our partition, so we
    // can skip the cadical setup + proof-walk entirely.
    if (cache_capacity > 0 && !conflict.empty()) {
        const CacheKey key = make_signature(to_repair_lit, conflict);
        auto it = sig_cache.find(key);
        if (it != sig_cache.end()) {
            cache_hits++;
            VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 3) {
                cout << "c o [interp-repair] cache hit for conflict-sig (size "
                     << conflict.size() << ")" << endl;
            });
            // Still apply oversize cap, so a tuning change in
            // --interprepairmaxnodes takes effect on cached entries too.
            if (max_aig_nodes > 0) {
                size_t nodes = AIG::count_aig_nodes_fast(it->second);
                if (nodes > max_aig_nodes) {
                    calls_failed_oversize++;
                    return nullptr;
                }
            }
            calls_succeeded++;
            return it->second;
        }
    }

    // Empty conflict means the candidate is forced to ctx[y_rep] regardless
    // of input — perform_repair already special-cases that into a
    // constant_formula. No interpolation needed (and we don't have any
    // input units, so there'd be no B side anyway).
    if (conflict.empty()) {
        calls_failed_empty_or_no_input++;
        return nullptr;
    }

    // No input lits in conflict → no B side → trivial / undefined
    // interpolant. Bail immediately to skip the cadical setup cost.
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

    const double t0 = cpuTime();

    // Build mini CNF:
    //   A side : original CNF clauses + non-input conflict-literal units
    //            + ~to_repair unit
    //   B side : input conflict-literal units
    //
    // Solve on a fresh CaDiCaL with proof tracing connected. Tracer
    // produces the McMillan interpolant in input vars.
    auto solver = std::make_unique<Solver>();
    // Disable in-processing & vivification: they can delete/strengthen
    // original clauses while the proof tracer is attached, which would
    // give us derived clauses whose antecedent IDs don't map to the
    // labels we computed in add_original_clause. The interpolant CNF is
    // small (typically dominated by the input cnf clauses + a few
    // units), so the standard CDCL solver is fine without simp.
    solver->set("inprocessing", 0);
    solver->set("preprocessing", 0);
    if (conflict_budget > 0) {
        // CaDiCaL exposes per-solve limits via .limit("conflicts", N).
        // Clamp to int max — cadical's limit API takes an int.
        const int64_t clamped = (conflict_budget > (uint64_t)INT_MAX)
            ? INT_MAX : (int64_t)conflict_budget;
        solver->limit("conflicts", (int)clamped);
    }
    InterpTracerMcMillan tracer(conf, aig_mng, input_vars);
    solver->connect_proof_tracer(&tracer, true);

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
    if (!cnf_serialized_built) build_serialized_cnf();
    tracer.next_is_b = false;
    for (int v : cnf_serialized) solver->add(v);

    // get_conflict() returns the negation of the failing assumption set
    // (so it forms a learnable clause). To reproduce the same UNSAT in a
    // fresh solver via unit clauses, we need to add the *original*
    // assumptions, i.e. ~l for each conflict literal l.
    //
    // 2) Non-input conflict units (A side) plus ~to_repair (A side).
    // In unconditional mode we *skip* the y_other units: the
    // interpolant then characterises must-flip universally over
    // y_others (rather than conditional on this CEX's y_other values).
    uint32_t b_marked = 0;
    if (!unconditional) {
        for (const auto& l : conflict) {
            if (l.var() < is_input.size() && is_input[l.var()]) continue;
            add_unit_a(~l);
        }
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

    if (ret != 20) { // 20 = UNSAT, 0 = UNKNOWN (budget hit), 10 = SAT
        if (ret == 0 && conflict_budget > 0) {
            // Cadical hit our conflict limit. Track separately so it
            // tunes differently from "real" failures.
            calls_budget_exhausted++;
            VERBOSE_DEBUG_DO(cout << "c o [interp-repair] budget exhausted ("
                << conflict_budget << " conflicts); falling back" << endl);
        } else {
            VERBOSE_DEBUG_DO(cout << "c o [interp-repair] solver returned non-UNSAT: "
                    << ret << "; falling back" << endl);
            calls_failed_other++;
        }
        return nullptr;
    }

    aig_ptr interp = tracer.out;
    if (interp == nullptr) {
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] interpolant is null after UNSAT; falling back" << endl);
        calls_failed_other++;
        return nullptr;
    }

    // Local AIG simplification (constant propagation, CSE, ITE detection)
    // before returning. The proof-driven construction can leave a lot of
    // redundant ANDs/ORs that the rewriter trivially crushes.
    const double t_simp = cpuTime();
    if (full_rewrite) {
        interp = AIG::rewrite_aig(interp);
    }
    interp = AIG::simplify_aig(interp);
    total_simplify_time += cpuTime() - t_simp;

    // SLOW_DEBUG: verify the interpolant only references input variables.
    // McMillan's construction guarantees this by induction; if it fails
    // we have a bug in the tracer.
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

    // Degenerate cases.
    //
    // I = TRUE  means "wrong y_rep is feasible everywhere" — but A∧B was
    // UNSAT at the CEX inputs, so this is a contradiction. Bail; using
    // ¬I = FALSE as the must-flip region produces an empty branch and
    // perform_repair would not actually fix anything (next loop sees the
    // same CEX → infinite loop).
    if (interp != nullptr && interp->type == AIGT::t_const && !interp.neg) {
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] interpolant = TRUE; bailing" << endl);
        calls_failed_other++;
        return nullptr;
    }
    // I = FALSE  means "wrong y_rep is infeasible everywhere" — y_rep must
    // be ctx[y_rep] universally. compose_or(TRUE, old) makes the function a
    // constant, which is a strong (and possibly correct) claim. Allow it
    // through but log it — and the SLOW_DEBUG miter and downstream
    // SLOW_DEBUG checks catch any soundness violation.
    VERBOSE_DEBUG_DO(if (interp != nullptr && interp->type == AIGT::t_const && interp.neg) {
        cout << "c o [interp-repair] interpolant = FALSE; y_rep forced to ctx everywhere" << endl;
    });

    // Quick sanity: under the original CEX inputs (= the input units we
    // added), interpolant should evaluate to FALSE. (This is what makes
    // the repair correct.) Cheap to check.
    if (!quick_check_interpolant_excludes_cex(interp, conflict)) {
        calls_quick_check_failed++;
        VERBOSE_DEBUG_DO(cout << "c o [interp-repair] quick_check_excludes_cex FAILED — bailing" << endl);
        return nullptr;
    }

    // SLOW_DEBUG full miter: A → I.
    SLOW_DEBUG_DO({
        if (!slow_check_a_implies_i(to_repair_lit, conflict, interp)) {
            cout << "c o [interp-repair] SLOW_DEBUG: A→I miter FAILED" << endl;
            assert(false && "slow_check_a_implies_i: bad interpolant");
        }
    });

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
        return nullptr;
    }
    total_interp_nodes += interp_nodes;
    if (interp_nodes > max_interp_nodes_seen) max_interp_nodes_seen = interp_nodes;
    if (interp_nodes < conflict.size()) interp_smaller_than_conflict++;
    else if (interp_nodes > conflict.size()) interp_larger_than_conflict++;
    interp_size_hist[bucket_of(interp_nodes)]++;
    conflict_size_hist[bucket_of(conflict.size())]++;

    // Count interpolant's input support (distinct input vars in leaves)
    // and the conflict's input-literal count. Both feed into the
    // "support-shrinkage" stat: how much narrower the interp's
    // dependence is vs the raw conflict input footprint.
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

    // Store in conflict-signature cache for future calls.
    if (cache_capacity > 0 && !conflict.empty()) {
        const CacheKey key = make_signature(to_repair_lit, conflict);
        if (sig_cache.size() >= cache_capacity && !sig_cache_order.empty()) {
            // Evict oldest.
            sig_cache.erase(sig_cache_order.front());
            sig_cache_order.erase(sig_cache_order.begin());
        }
        sig_cache[key] = interp;
        sig_cache_order.push_back(key);
    }

    calls_succeeded++;
    return interp;
}

// SLOW_DEBUG full miter: verify that A → I, where
//   A = original CNF + non-input conflict units + ~to_repair_lit
//   I = interpolant AIG over input vars
// We add A's clauses + ¬I as a fresh CNF and check UNSAT. Encoding ¬I
// requires Tseitin over the AIG; we do it inline.
bool InterpRepair::slow_check_a_implies_i(
        Lit to_repair_lit,
        const vector<Lit>& conflict,
        const aig_ptr& interp) const
{
    if (interp == nullptr) return true;

    auto solver = std::make_unique<Solver>();
    auto add_cl = [&](const vector<Lit>& cl) {
        for (const auto& l : cl) solver->add(lit_to_pl(l));
        solver->add(0);
    };
    auto add_unit = [&](Lit l) {
        solver->add(lit_to_pl(l));
        solver->add(0);
    };

    for (const auto& cl : cnf.get_clauses()) add_cl(cl);
    for (const auto& l : conflict) {
        if (l.var() < is_input.size() && is_input[l.var()]) continue;
        add_unit(~l);
    }
    add_unit(~to_repair_lit);

    // Tseitin-encode interp into the same solver. Use cnf.nVars() as the
    // start of fresh helper IDs.
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
        cout << "c o [interp-repair] SLOW_DEBUG slow_check_a_implies_i: "
             << "miter is NOT UNSAT (cadical ret=" << ret << ")" << endl;
        return false;
    }
    return true;
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
         << " setup-T: " << fixed << setprecision(2) << total_setup_time
         << " solve-T: " << fixed << setprecision(2) << total_solve_time
         << " simp-T: " << fixed << setprecision(2) << total_simplify_time
         << endl;
}
