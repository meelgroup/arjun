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
#include <cadical.hpp>
#include <climits>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <algorithm>
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

// OR over the input literals in `cl` — the McMillan label for an
// A-side clause. Empty input set => label FALSE.
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

    // Walk the resolution chain; cadical gives antecedents in chain
    // order, so reverse to resolve iteratively from the start.
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
        // Antecedent label missing — fail closed: empty interpolant.
        labels[id] = aig_mng.new_const(false);
        return;
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

uint32_t InterpRepair::setup_mini_cnf(CaDiCaL::Solver& solver,
        InterpTracerMcMillan& tracer, Lit to_repair_lit,
        const std::vector<Lit>& conflict, bool unconditional) const
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

    // 1) Original CNF clauses (all A-side). Redundant learnts are
    // skipped — not needed to reproduce the UNSAT.
    if (!cnf_serialized_built) build_serialized_cnf();
    tracer.next_is_b = false;
    for (int v : cnf_serialized) solver.add(v);

    // 2) Non-input conflict units (A side) + ~to_repair (A side). The
    // conflict is the negated assumptions, so we add ~l to reproduce the
    // original assumptions. In unconditional mode the y_other units are
    // skipped.
    if (!unconditional) {
        for (const auto& l : conflict) {
            if (l.var() < is_input.size() && is_input[l.var()]) continue;
            add_unit_a(~l);
        }
    }
    add_unit_a(~to_repair_lit);

    // 3) Input conflict units (B side).
    uint32_t b_marked = 0;
    for (const auto& l : conflict) {
        if (l.var() >= is_input.size() || !is_input[l.var()]) continue;
        add_unit_b(~l);
        b_marked++;
    }
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

// Stable key from (to_repair, conflict): sorted so it's order-
// independent, packed into a string.
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
        uint64_t conflict_budget, bool unconditional)
{
    (void)y_rep;
    calls++;
    total_conflict_lits += conflict.size();

    // Conflict-signature cache lookup; identical conflicts give
    // identical interpolants.
    if (cache_capacity > 0 && !conflict.empty()) {
        const CacheKey key = make_signature(to_repair_lit, conflict);
        auto it = sig_cache.find(key);
        if (it != sig_cache.end()) {
            cache_hits++;
            VERBOSE_DEBUG_DO(if (verbose_debug_enabled >= 3) {
                cout << "c o [interp-repair] cache hit for conflict-sig (size "
                     << conflict.size() << ")" << endl;
            });
            // Still apply the oversize cap to cached entries.
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
    solver->connect_proof_tracer(&tracer, true);

    const uint32_t b_marked = setup_mini_cnf(*solver, tracer,
            to_repair_lit, conflict, unconditional);

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

    int ret = solver->solve();
    solver->disconnect_proof_tracer(&tracer);

    if (ret != 20) { // 20 = UNSAT, 0 = UNKNOWN (budget hit), 10 = SAT
        if (ret == 0 && conflict_budget > 0) {
            // Cadical hit our conflict limit; tracked separately.
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

    // Simplify the proof-driven AIG before returning.
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

// SLOW_DEBUG full miter: check A & ~I is UNSAT (i.e. A -> I), with I
// Tseitin-encoded inline.
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
        cout << "c o [interp-repair] SLOW_DEBUG slow_check_a_implies_i: "
             << "miter is NOT UNSAT (cadical ret=" << ret << ")" << endl;
        return false;
    }
    return true;
}

bool InterpRepair::sample_check_interpolant(
        Lit to_repair_lit,
        const vector<Lit>& /*conflict*/,
        const aig_ptr& interp,
        uint32_t num_samples,
        uint64_t seed) const
{
    if (interp == nullptr) return true;

    // Only I(X)=FALSE samples can violate the must-flip claim.
    std::vector<uint32_t> ins(input_vars.begin(), input_vars.end());
    if (ins.empty()) return true;
    std::mt19937_64 rng(seed);

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

        if (cnf_serialized_built) {} // suppress unused warning if any
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
         << endl;
}
