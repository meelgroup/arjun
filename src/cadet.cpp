/*
 Arjun — cadet.cpp

 In-tree port of CADET (Rabe, SAT 2016). Constructs Skolem functions
 for ∀X.∃Y.φ via incremental unique-consequence determinization plus
 SAT-model fallbacks. Phases:
   C: worklist unique-consequence + pure-literal propagation.
   D: forced-constant probes (two-sided), speculative CDCL guesses
      gated by selectors, CEGAR companion at level-0 stalls.
   E: SAT-model enumeration + Shannon trees (small input only).
   F: terminal SAT + UNSAT-core generalization. Always finishes.

 Copyright (c) 2026, Mate Soos. All rights reserved.
*/

#include "cadet.h"

#include "arjun.h"
#include "constants.h"
#include "metasolver.h"
#include "aig_to_cnf.h"
#include "time_mem.h"

#include <cryptominisat5/solvertypesmini.h>

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <set>
#include <unordered_map>
#include <vector>

using std::cout;
using std::endl;
using std::set;
using std::vector;
using std::setprecision;
using std::fixed;

using ArjunNS::AIG;
using ArjunNS::AIGT;
using ArjunNS::aig_ptr;
using ArjunNS::aig_lit;
using ArjunNS::SimplifiedCNF;
using ArjunNS::VarTypes;
using CMSat::Lit;
using CMSat::lbool;

namespace ArjunInt {

Cadet::Cadet(const ArjunInt::Config& _conf,
             const ArjunNS::Arjun::ManthanConf& _mconf,
             ArjunNS::SimplifiedCNF&& _cnf)
    : conf(_conf), mconf(_mconf), cnf(std::move(_cnf))
{
    // Apply mconf overrides to the in-class defaults.
    activity_decay = mconf.cadet_activity_decay;
}

void Cadet::pa_init() {
    pa_value.assign(cnf.nVars(), CMSat::l_Undef);
    pa_reason.assign(cnf.nVars(), PA_REASON_SOURCE);
    pa_level.assign(cnf.nVars(), 0);
    pa_trail.clear();
    pa_bcp_queue.clear();
    pa_bcp_in_queue.assign(cnf.get_clauses().size(), 0);
    pa_conflict_clause = PA_NO_CONFLICT;
    pa_propagations = 0;
    pa_conflicts_caught = 0;
}

CMSat::lbool Cadet::pa_lit_value(CMSat::Lit lit) const {
    const uint32_t v = lit.var();
    if (pa_value[v] == CMSat::l_Undef) return CMSat::l_Undef;
    const bool var_true = (pa_value[v] == CMSat::l_True);
    return (var_true != lit.sign()) ? CMSat::l_True : CMSat::l_False;
}

void Cadet::pa_enqueue_clauses_for_var(uint32_t v) {
    for (const auto& [ci, sign_v] : var_clauses[v]) {
        (void)sign_v;
        if (pa_bcp_in_queue[ci]) continue;
        if (clause_dead[ci]) continue;
        pa_bcp_in_queue[ci] = 1;
        pa_bcp_queue.push_back(ci);
    }
}

void Cadet::pa_assign(uint32_t v, bool val, uint32_t reason) {
    const CMSat::lbool target = val ? CMSat::l_True : CMSat::l_False;
    if (pa_value[v] == target) return;
    if (pa_value[v] != CMSat::l_Undef) {
        // Defensive: shouldn't happen in normal flow.
        if (pa_conflict_clause == PA_NO_CONFLICT) {
            pa_conflict_clause = reason;
            pa_conflicts_caught++;
        }
        return;
    }
    pa_value[v]  = target;
    pa_reason[v] = reason;
    pa_level[v]  = decision_lvl;
    pa_trail.push_back(CMSat::Lit(v, /*sign=*/!val));
    pa_enqueue_clauses_for_var(v);
}

void Cadet::pa_pop_to_level(uint32_t target) {
    while (!pa_trail.empty() && pa_level[pa_trail.back().var()] > target) {
        const uint32_t v = pa_trail.back().var();
        pa_value[v]  = CMSat::l_Undef;
        pa_reason[v] = PA_REASON_SOURCE;
        pa_level[v]  = 0;
        pa_trail.pop_back();
    }
    pa_conflict_clause = PA_NO_CONFLICT;
    for (uint32_t ci : pa_bcp_queue) pa_bcp_in_queue[ci] = 0;
    pa_bcp_queue.clear();
}

void Cadet::two_sided_build(MetaSolver& solver) {
    pos_var.assign(cnf.nVars(), CMSat::Lit(0, false));
    neg_var.assign(cnf.nVars(), CMSat::Lit(0, false));
    std::vector<uint8_t> y_alloc(cnf.nVars(), 0);
    for (uint32_t y : to_define) {
        solver.new_var();
        pos_var[y] = CMSat::Lit(solver.nVars() - 1, /*sign=*/false);
        solver.new_var();
        neg_var[y] = CMSat::Lit(solver.nVars() - 1, /*sign=*/false);
        y_alloc[y] = 1;
    }

    const auto& clauses = cnf.get_clauses();
    std::vector<CMSat::Lit> buf;
    for (uint32_t y : to_define) {
        for (const auto& [ci, sign_y] : var_clauses[y]) {
            const CMSat::Lit& side_var = sign_y ? neg_var[y] : pos_var[y];
            buf.clear();
            for (const auto& l : clauses[ci]) {
                if (l.var() == y) continue;
                buf.push_back(l);
            }
            buf.push_back(side_var);
            solver.add_clause(buf);
        }
    }
    if (conf.verb >= 1) {
        cout << "c o [cadet] two-sided encoding: " << to_define.size()
             << " Y vars, " << (2 * to_define.size())
             << " pos/neg SAT vars added" << endl;
    }
}

void Cadet::minimize_learnt_recursive(std::vector<Lit>& learnt) {
    const auto& clauses = cnf.get_clauses();
    if (learnt.size() <= 1) return;

    const size_t orig_size = learnt.size();
    uip_min_in_lits += orig_size;

    std::vector<uint8_t> in_learnt(cnf.nVars(), 0);
    uint32_t abstract_level = 0;
    for (const Lit& l : learnt) {
        in_learnt[l.var()] = 1;
        abstract_level |= (1u << (pa_level[l.var()] & 31));
    }

    // After a successful walk, marks are kept (cache); on failure
    // they're rolled back via to_clear.
    std::vector<uint8_t> seen(cnf.nVars(), 0);
    for (const Lit& l : learnt) seen[l.var()] = 1;

    std::vector<uint32_t> stack;
    std::vector<uint32_t> to_clear;

    auto lit_redundant = [&](uint32_t v0) -> bool {
        stack.clear();
        stack.push_back(v0);
        const size_t top = to_clear.size();
        while (!stack.empty()) {
            const uint32_t v = stack.back();
            stack.pop_back();
            const uint32_t reason = pa_reason[v];
            assert(reason != PA_REASON_SOURCE);
            for (const Lit& q : clauses[reason]) {
                const uint32_t qv = q.var();
                if (qv == v) continue;
                if (seen[qv]) continue;
                if (pa_level[qv] == 0) continue;
                if (pa_reason[qv] != PA_REASON_SOURCE
                    && (abstract_level & (1u << (pa_level[qv] & 31))) != 0) {
                    seen[qv] = 1;
                    to_clear.push_back(qv);
                    stack.push_back(qv);
                } else {
                    while (to_clear.size() > top) {
                        seen[to_clear.back()] = 0;
                        to_clear.pop_back();
                    }
                    return false;
                }
            }
        }
        return true;
    };

    std::vector<Lit> kept;
    kept.reserve(learnt.size());
    // Sources (decisions, Phase C/pure/CEGAR/Phase-D-forced) are
    // untouchable — no clause reason to fold through. Everything else
    // (clause-reason lits, which can only be lits below conflict_dlvl
    // brought in via the initial absorb pass of 1-UIP) is fair game.
    for (const Lit& l : learnt) {
        const uint32_t v = l.var();
        if (pa_reason[v] == PA_REASON_SOURCE) {
            kept.push_back(l);
            continue;
        }
        if (lit_redundant(v)) continue; // drop
        kept.push_back(l);
    }
    learnt = std::move(kept);
    uip_min_out_lits += learnt.size();
}

bool Cadet::handle_pa_conflict_1uip(std::vector<uint8_t>& outer_in_queue,
                                    std::vector<uint32_t>& outer_neighbour_queue) {
    assert(pa_conflict_clause != PA_NO_CONFLICT);
    const auto& clauses = cnf.get_clauses();
    const auto& cclause = clauses[pa_conflict_clause];

    uint32_t conflict_dlvl = 0;
    for (const Lit& l : cclause) {
        if (pa_level[l.var()] > conflict_dlvl) conflict_dlvl = pa_level[l.var()];
    }
    if (conflict_dlvl == 0) {
        // F UNSAT under level-0 commits — caller bails to Phase E/F.
        pa_conflict_clause = PA_NO_CONFLICT;
        return false;
    }

    std::vector<uint8_t> seen(cnf.nVars(), 0);
    std::vector<Lit> learnt;
    learnt.reserve(cclause.size());
    uint32_t counter = 0;

    auto absorb_lit = [&](const Lit& l) {
        const uint32_t v = l.var();
        if (seen[v]) return;
        if (pa_level[v] == 0) return;
        seen[v] = 1;
        if (v < var_activity.size()) bump_var(v);
        if (pa_level[v] == conflict_dlvl) counter++;
        else learnt.push_back(l);
    };

    for (const Lit& l : cclause) absorb_lit(l);

    int64_t trail_idx = (int64_t)pa_trail.size() - 1;
    while (counter > 0 && trail_idx >= 0) {
        while (trail_idx >= 0) {
            const Lit tl = pa_trail[trail_idx];
            if (seen[tl.var()] && pa_level[tl.var()] == conflict_dlvl) break;
            trail_idx--;
        }
        if (trail_idx < 0) break;
        const Lit tl = pa_trail[trail_idx];
        const uint32_t tv = tl.var();
        const uint32_t reason = pa_reason[tv];

        if (reason == PA_REASON_SOURCE) {
            // The decision at its level → UIP. Non-decision sources
            // (Phase D forced, Phase C const, pure, CEGAR) get
            // synthetic-resolved via "implied by decisions ≤ d".
            const uint32_t d = pa_level[tv];
            const bool is_the_decision =
                (d >= 1 && d <= decision_lits.size()
                 && decision_lits[d - 1].var() == tv);
            if (is_the_decision) {
                learnt.push_back(~tl);
                counter--;
                seen[tv] = 0;
                uip_strict_decision_terminations++;
                break;
            }
            counter--;
            seen[tv] = 0;
            for (uint32_t i = 0; i < d; i++) {
                const Lit dlit = decision_lits[i];
                const uint32_t dv = dlit.var();
                if (seen[dv]) continue;
                if (pa_level[dv] == 0) continue;
                seen[dv] = 1;
                if (dv < var_activity.size()) bump_var(dv);
                if (pa_level[dv] == conflict_dlvl) counter++;
                else learnt.push_back(~dlit);
            }
            uip_strict_synthetic_resolves++;
            trail_idx--;
            continue;
        }

        // Clause reason: resolve tv out via the reason's other lits
        // (all FALSE in PA by unit-prop precondition).
        counter--;
        seen[tv] = 0;
        for (const Lit& other : clauses[reason]) {
            if (other.var() == tv) continue;
            absorb_lit(other);
        }
        trail_idx--;
    }

    if (learnt.empty()) {
        pa_conflict_clause = PA_NO_CONFLICT;
        return false;
    }

    // Runs before backjump while pa_reason / pa_level are valid.
    minimize_learnt_recursive(learnt);

    uint32_t max_lvl = 0, second_lvl = 0;
    for (const Lit& l : learnt) {
        const uint32_t lvl = pa_level[l.var()];
        if (lvl > max_lvl) { second_lvl = max_lvl; max_lvl = lvl; }
        else if (lvl > second_lvl && lvl < max_lvl) { second_lvl = lvl; }
    }
    decay_activities();

    skolem_sat->add_clause(learnt);
    learnt_clauses.push_back(learnt);

    uip_conflicts_handled++;
    uip_learnt_lits_total += learnt.size();

    if (conf.verb >= 2) {
        cout << "c o [cadet] PA-UIP conflict at lvl " << conflict_dlvl
             << ": learnt " << learnt.size() << " lits, backjump to "
             << second_lvl << " (was decision_lvl " << decision_lvl << ")"
             << endl;
    }

    backjump_to_level(second_lvl);

    for (uint32_t y : to_define) {
        if (skol[y] == nullptr && !outer_in_queue[y]) {
            outer_in_queue[y] = 1;
            outer_neighbour_queue.push_back(y);
        }
    }
    return true;
}

bool Cadet::pa_drain_bcp(std::vector<uint8_t>& outer_in_queue,
                         std::vector<uint32_t>& outer_neighbour_queue) {
    const auto& clauses = cnf.get_clauses();
    while (!pa_bcp_queue.empty() && pa_conflict_clause == PA_NO_CONFLICT) {
        const uint32_t ci = pa_bcp_queue.back();
        pa_bcp_queue.pop_back();
        pa_bcp_in_queue[ci] = 0;
        if (clause_dead[ci]) continue;

        const auto& c = clauses[ci];
        CMSat::Lit unit_lit(0, false);
        uint32_t n_undef = 0;
        bool has_undef_universal = false;
        bool sat = false;
        for (const auto& l : c) {
            const auto lv = pa_lit_value(l);
            if (lv == CMSat::l_True) { sat = true; break; }
            if (lv == CMSat::l_Undef) {
                if (n_undef == 0) unit_lit = l;
                n_undef++;
                if (input.count(l.var()) || backward_defined.count(l.var()))
                    has_undef_universal = true;
                if (n_undef >= 2) break;
            }
        }
        if (sat) continue;
        if (n_undef == 0) {
            pa_conflict_clause = ci;
            pa_conflicts_caught++;
            return false;
        }
        if (n_undef > 1) continue;
        // Only commit Y vars; propagating universals would falsely
        // constrain ∀X.
        if (has_undef_universal) continue;
        const uint32_t uv = unit_lit.var();
        // skol[uv] non-null = non-PA-tracked AIG function; don't overwrite.
        if (skol[uv] != nullptr) continue;
        const bool uval = !unit_lit.sign();

        skol[uv] = AIG::new_const(uval);
        trail.push_back({uv, decision_lvl, /*is_decision=*/false,
                         CMSat::Lit(0, false), {}});
        clause_undet_delta(uv, -1);
        mark_clauses_dead_by_constant(uv, uval);
        tseitin_skol_into_skolem_sat(uv);
        pa_assign(uv, uval, ci);
        pa_propagations++;
        if (uv < var_activity.size()) bump_var(uv);
        for (const auto& [cidx, sign_v] : var_clauses[uv]) {
            (void)sign_v;
            for (const auto& l2 : clauses[cidx]) {
                const uint32_t u2 = l2.var();
                if (u2 == uv) continue;
                if (skol[u2] != nullptr) continue;
                if (!outer_in_queue[u2]) {
                    outer_in_queue[u2] = 1;
                    outer_neighbour_queue.push_back(u2);
                }
            }
        }
    }
    return pa_conflict_clause == PA_NO_CONFLICT;
}

template<typename S>
void Cadet::inject_cnf(S& s) const {
    s.new_vars(cnf.nVars());
    for (const auto& c : cnf.get_clauses()) s.add_clause(c);
    for (const auto& c : cnf.get_red_clauses()) s.add_red_clause(c);
}

void Cadet::make_decision(uint32_t v, bool val) {
    assert(skol[v] == nullptr);
    // Allocate fresh selector. sel_d active ⇒ decision in force.
    skolem_sat->new_var();
    const Lit sel(skolem_sat->nVars() - 1, /*sign=*/false);
    sel_lits.push_back(sel);

    // Decision lit: y=val. For val=true: Lit(v, sign=false). For
    // val=false: Lit(v, sign=true).
    const Lit dlit(v, /*sign=*/!val);
    decision_lits.push_back(dlit);
    decision_lvl++;

    // Gated decision clause: (¬sel_d ∨ dlit). When sel_d assumed,
    // dlit must hold.
    skolem_sat->add_clause({~sel, dlit});

    // Commit skol[v] to the constant and trail it as a decision.
    skol[v] = AIG::new_const(val);
    trail.push_back({v, decision_lvl, /*is_decision=*/true, dlit, {}});
    clause_undet_delta(v, -1);
    mark_clauses_dead_by_constant(v, val);
    // PA: record the decision as a source-of-truth assignment at the
    // freshly-opened dec_lvl. BCP can then auto-propagate Y units from
    // it; the caller is responsible for invoking pa_drain_bcp.
    pa_assign(v, val, PA_REASON_SOURCE);
}

std::vector<Lit> Cadet::active_assumps() const {
    // Return [sel_lits[0], ..., sel_lits[decision_lvl-1]] —
    // assumption list that activates all currently-live decision levels.
    return std::vector<Lit>(sel_lits.begin(),
                            sel_lits.begin() + decision_lvl);
}

void Cadet::backjump_to_level(uint32_t target) {
    assert(target <= decision_lvl);
    if (target == decision_lvl) return;
    // Pop trail entries committed at levels > target. Reset their
    // skol[] slots and un-kill their clauses.
    while (!trail.empty() && trail.back().dec_lvl > target) {
        auto& te = trail.back();
        for (uint32_t ci : te.killed_clauses) clause_dead[ci] = 0;
        skol[te.var] = nullptr;
        clause_undet_delta(te.var, +1);
        trail.pop_back();
    }
    // Permanently kill selector vars for levels (target, decision_lvl].
    // After ¬sel_d is added, cadical can simplify away every level-d
    // clause on its next garbage collection.
    for (uint32_t d = target + 1; d <= decision_lvl; d++) {
        const Lit sl = sel_lits[d - 1];
        skolem_sat->add_clause({~sl});
    }
    decision_lits.resize(target);
    sel_lits.resize(target);
    decision_lvl = target;
    pa_pop_to_level(target);
}

void Cadet::bump_var(uint32_t v) {
    assert(v < var_activity.size());
    var_activity[v] += activity_inc;
    if (var_activity[v] > kActivityRescaleThreshold) {
        const double inv = 1.0 / kActivityRescaleThreshold;
        for (auto& a : var_activity) a *= inv;
        activity_inc *= inv;
    }
}

void Cadet::clause_undet_delta(uint32_t v, int delta) {
    for (const auto& [ci, sign_v] : var_clauses[v]) {
        (void)sign_v;
        const int32_t nv = static_cast<int32_t>(n_undet_per_clause[ci]) + delta;
        assert(nv >= 0 && nv <= UINT16_MAX);
        n_undet_per_clause[ci] = static_cast<uint16_t>(nv);
    }
}

void Cadet::decay_activities() {
    activity_inc *= (1.0 / activity_decay);
    if (activity_inc > kActivityRescaleThreshold) {
        const double inv = 1.0 / kActivityRescaleThreshold;
        for (auto& a : var_activity) a *= inv;
        activity_inc *= inv;
    }
}

void Cadet::minimize_failed_selectors(std::set<uint32_t>& kept) {
    // Drop each selector via re-solve; tighten `kept` from the new
    // failed core. Single pass, descending dlvl.
    if (!mconf.cadet_clause_min) return;
    if (kept.size() <= mconf.cadet_clause_min_size_floor) return;

    clause_min_total_in_lits += kept.size();
    const size_t in_size = kept.size();

    std::unordered_map<uint32_t, uint32_t> sel_var_to_dlvl;
    sel_var_to_dlvl.reserve(decision_lvl);
    for (uint32_t d = 1; d <= decision_lvl; d++) {
        sel_var_to_dlvl[sel_lits[d - 1].var()] = d;
    }

    // Descending dlvl so the resulting backjump can go deeper.
    std::vector<uint32_t> cands(kept.begin(), kept.end());
    std::sort(cands.begin(), cands.end(),
              [&](uint32_t a, uint32_t b) {
                  return sel_var_to_dlvl[a] > sel_var_to_dlvl[b];
              });

    MetaSolver& s = *skolem_sat;
    std::vector<Lit> trial;
    trial.reserve(kept.size());
    for (uint32_t sv : cands) {
        if (kept.size() <= 1) break;
        if (!kept.count(sv)) continue;

        trial.clear();
        for (uint32_t k : kept) {
            if (k == sv) continue;
            trial.push_back(sel_lits[sel_var_to_dlvl[k] - 1]);
        }
        clause_min_resolves++;
        if (s.solve(&trial) == CMSat::l_False) {
            std::set<uint32_t> new_kept;
            for (const Lit& f : s.get_conflict()) {
                if (sel_var_to_dlvl.count(f.var())) {
                    new_kept.insert(f.var());
                }
            }
            if (new_kept.empty()) {
                // UNSAT with no failed assumption → F itself UNSAT.
                // Caller short-circuits to backjump-to-0.
                kept.clear();
                clause_min_drops += in_size;
                clause_min_total_out_lits += 0;
                return;
            }
            const size_t dropped = kept.size() - new_kept.size();
            clause_min_drops += dropped;
            kept = std::move(new_kept);
        }
    }
    clause_min_total_out_lits += kept.size();
}

void Cadet::tseitin_skol_into_skolem_sat(uint32_t y) {
    // Level-0: permanent. Level>0: only gate CONSTANT skols (non-const
    // pos_force AIGs stay in skol[] only — selector-gating every
    // AIGToCNF clause needs a wrapper, future work).
    assert(skolem_sat != nullptr);
    assert(skol[y] != nullptr);
    const bool gated = (decision_lvl > 0);
    if (skol[y]->type == AIGT::t_const) {
        const bool val = !skol[y].neg;
        if (gated) {
            const Lit sel = sel_lits[decision_lvl - 1];
            skolem_sat->add_clause({~sel, Lit(y, /*sign=*/!val)});
        } else {
            skolem_sat->add_clause({Lit(y, /*sign=*/!val)});
        }
        return;
    }
    if (gated) return;
    using AIGEnc = ArjunNS::AIGToCNF<MetaSolver>;
    AIGEnc enc(*skolem_sat);
    enc.set_true_lit(skolem_sat_true_lit);
    const Lit root = enc.encode(skol[y]);
    skolem_sat->add_clause({~Lit(y, /*sign=*/false), root});
    skolem_sat->add_clause({Lit(y, /*sign=*/false), ~root});
    skolem_sat_commits_since_build++;
}

uint32_t Cadet::ratify_speculative_decisions() {
    if (decision_lvl == 0) return 0;
    uint32_t ratified = 0;
    for (uint32_t d = 1; d <= decision_lvl; d++) {
        // sel[0..d-2] + ¬decision_lit_d UNSAT ⇒ decision F-implied.
        std::vector<Lit> probe;
        probe.reserve(d);
        for (uint32_t e = 1; e < d; e++) probe.push_back(sel_lits[e - 1]);
        probe.push_back(~decision_lits[d - 1]);
        if (skolem_sat->solve(&probe) != CMSat::l_False) break;
        ratified = d;
    }
    if (ratified == 0) return 0;
    // Promote sel_d to unit for the ratified prefix — ungates the
    // level's clauses, effectively moving them to level 0.
    for (uint32_t d = 1; d <= ratified; d++) {
        skolem_sat->add_clause({sel_lits[d - 1]});
    }
    for (auto& te : trail) {
        if (te.dec_lvl > 0 && te.dec_lvl <= ratified) te.dec_lvl = 0;
    }
    backjump_to_level(ratified);
    decision_lits.clear();
    sel_lits.clear();
    decision_lvl = 0;
    total_ratified += ratified;
    if (conf.verb >= 1) {
        cout << "c o [cadet] ratified " << ratified
             << " speculative level(s) into permanent" << endl;
    }
    return ratified;
}

void Cadet::maybe_replenish_skolem_sat() {
    // Level-0 only: sel_lits / decision_lits reference OLD-solver vars.
    if (mconf.cadet_skolem_sat_replenish_every == 0) return;
    if (skolem_sat_commits_since_build < mconf.cadet_skolem_sat_replenish_every) return;
    if (decision_lvl != 0) return;

    auto new_solver = std::make_unique<MetaSolver>(SolverType::cadical);
    inject_cnf(*new_solver);
    new_solver->new_var();
    const Lit new_true_lit(new_solver->nVars() - 1, /*sign=*/false);
    new_solver->add_clause({new_true_lit});

    using AIGEnc = ArjunNS::AIGToCNF<MetaSolver>;
    AIGEnc enc(*new_solver);
    enc.set_true_lit(new_true_lit);
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) continue;
        if (skol[y]->type == AIGT::t_const) {
            const bool val = !skol[y].neg;
            new_solver->add_clause({Lit(y, /*sign=*/!val)});
        } else {
            const Lit root = enc.encode(skol[y]);
            new_solver->add_clause({~Lit(y, /*sign=*/false), root});
            new_solver->add_clause({Lit(y, /*sign=*/false), ~root});
        }
    }
    for (const auto& lc : learnt_clauses) {
        new_solver->add_red_clause(lc);
    }

    skolem_sat = std::move(new_solver);
    skolem_sat_true_lit = new_true_lit;
    skolem_sat_commits_since_build = 0;
    skolem_sat_replenishes++;
    two_sided_build(*skolem_sat);
    if (conf.verb >= 1) {
        cout << "c o [cadet] skolem_sat replenished (#" << skolem_sat_replenishes
             << ", " << learnt_clauses.size() << " learnt replayed)" << endl;
    }
}

void Cadet::build_solver_with_skols(MetaSolver& s, Lit& out_true_lit) const {
    inject_cnf(s);
    s.new_var();
    const uint32_t tv = s.nVars() - 1;
    out_true_lit = Lit(tv, /*sign=*/false);
    s.add_clause({out_true_lit});
    using AIGEnc = ArjunNS::AIGToCNF<MetaSolver>;
    AIGEnc enc(s);
    enc.set_true_lit(out_true_lit);
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) continue;
        if (skol[y]->type == AIGT::t_const) {
            const bool val = !skol[y].neg;
            s.add_clause({Lit(y, /*sign=*/!val)});
        } else {
            const Lit root = enc.encode(skol[y]);
            s.add_clause({~Lit(y, /*sign=*/false), root});
            s.add_clause({Lit(y, /*sign=*/false), ~root});
        }
    }
    for (const auto& lc : learnt_clauses) s.add_red_clause(lc);
}


aig_ptr Cadet::build_shannon_tree(const vector<bool>& table,
                                  const vector<uint32_t>& sorted_inputs) {
    // Bottom-up pair-merge: level[i] = ITE(sorted_inputs[L],
    //   high=prev[2i+1], low=prev[2i]). ITE folds constant subtrees.
    const uint32_t n = sorted_inputs.size();
    if (n == 0) {
        assert(table.size() == 1);
        return AIG::new_const(table[0]);
    }
    vector<aig_ptr> level;
    level.reserve(table.size());
    for (bool b : table) level.push_back(AIG::new_const(b));

    for (uint32_t lvl = 0; lvl < n; lvl++) {
        const uint32_t split_var = sorted_inputs[lvl];
        const CMSat::Lit branch_lit(split_var, /*sign=*/false);
        vector<aig_ptr> next;
        next.reserve(level.size() / 2);
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            // level[i] = low (bit=0), level[i+1] = high (bit=1).
            next.push_back(AIG::new_ite(level[i + 1], level[i], branch_lit));
        }
        level = std::move(next);
    }
    assert(level.size() == 1);
    return level[0];
}

bool Cadet::try_propagate(uint32_t y,
                          std::map<uint32_t, vector<uint32_t>>& dep_cache,
                          const std::map<uint32_t, Lit>& new_to_orig) {
    if (skol[y] != nullptr) return false;

    // Fast pre-check: any non-dead clause with n_undet > 1 blocks y.
    for (const auto& [ci, sign_y] : var_clauses[y]) {
        (void)sign_y;
        if (clause_dead[ci]) continue;
        if (n_undet_per_clause[ci] > 1) return false;
    }

    const auto& clauses = cnf.get_clauses();
    bool all_determined = true;
    aig_ptr pos_force = AIG::new_const(false);
    // Only accumulate the positive-force region: by F-SAT-for-every-X,
    // pos and neg force regions are disjoint, so y=pos_force is sound.
    for (const auto& [ci, sign_y] : var_clauses[y]) {
        if (sign_y) continue;
        aig_ptr forced = AIG::new_const(true);
        for (const auto& l : clauses[ci]) {
            if (l.var() == y) continue;
            if (skol[l.var()] == nullptr) {
                all_determined = false;
                break;
            }
            aig_ptr lit_aig = skol[l.var()];
            if (l.sign()) lit_aig = ~lit_aig;
            forced = AIG::new_and(forced, ~lit_aig);
        }
        if (!all_determined) break;
        pos_force = AIG::new_or(pos_force, forced);
    }
    // Negative-y clauses must still be CHECKED for "all_determined".
    if (all_determined) {
        for (const auto& [ci, sign_y] : var_clauses[y]) {
            if (!sign_y) continue;
            for (const auto& l : clauses[ci]) {
                if (l.var() == y) continue;
                if (skol[l.var()] == nullptr) {
                    all_determined = false;
                    break;
                }
            }
            if (!all_determined) break;
        }
    }
    if (!all_determined) return false;

    // Cycle check via transitive orig-space deps.
    const uint32_t y_orig = new_to_orig.at(y).var();
    std::set<uint32_t> cnf_leaves;
    AIG::get_dependent_vars(pos_force, cnf_leaves, /*self=*/UINT32_MAX);
    for (uint32_t leaf : cnf_leaves) {
        uint32_t leaf_orig = new_to_orig.at(leaf).var();
        if (leaf_orig == y_orig) return false;
        if (cnf.defined(leaf_orig)) {
            const auto& deps = cnf.get_dependent_vars_recursive(leaf_orig, dep_cache);
            if (std::find(deps.begin(), deps.end(), y_orig) != deps.end()) {
                if (conf.verb >= 3) {
                    cout << "c o [cadet]   skipping y=" << (y + 1)
                         << " (orig " << y_orig + 1
                         << "): commit would create a defs[] cycle" << endl;
                }
                return false;
            }
        }
    }
    // Commit.
    skol[y] = pos_force;
    trail.push_back({y, decision_lvl, /*is_decision=*/false,
                     CMSat::Lit(0, false), {}});
    clause_undet_delta(y, -1);
    if (pos_force->type == AIGT::t_const) {
        const bool val = !pos_force.neg;
        mark_clauses_dead_by_constant(y, val);
        // Phase C constant — fold into the PA so BCP can propagate
        // through pure-Y clauses. Use PA_REASON_SOURCE because the
        // pos_force AIG already encodes the multi-clause derivation;
        // there's no single F-clause to point at as antecedent.
        pa_assign(y, val, PA_REASON_SOURCE);
    }
    tseitin_skol_into_skolem_sat(y);
    // Small activity bump for vars whose Phase-C propagation actually
    // pulled them in — they're more likely to participate in future
    // tight forcing. Bumping all dependent vars too (the leaves of
    // pos_force) would spread activity too thin; just bump y.
    if (y < var_activity.size()) bump_var(y);
    return true;
}

void Cadet::mark_clauses_dead_by_constant(uint32_t v, bool val) {
    // Lit appears as +v when sign=false; that literal is TRUE iff val
    // Satisfying-sign matches !val. Freshly-killed clauses recorded on
    // trail.back() so backjump can un-kill them.
    const bool sat_sign = !val;
    assert(!trail.empty() && "must run AFTER pushing the TrailEntry");
    auto& killed = trail.back().killed_clauses;
    for (const auto& [ci, sign_v] : var_clauses[v]) {
        if (sign_v == sat_sign && !clause_dead[ci]) {
            clause_dead[ci] = 1;
            killed.push_back(ci);
        }
    }
}

bool Cadet::try_pure_literal(uint32_t y) {
    if (skol[y] != nullptr) return false;
    bool has_pos = false, has_neg = false;
    for (const auto& [ci, sign_y] : var_clauses[y]) {
        if (clause_dead[ci]) continue;
        if (sign_y) has_neg = true;
        else has_pos = true;
        if (has_pos && has_neg) return false;
    }
    if (!has_pos && !has_neg) {
        // y unconstrained — pick false (AIG simplifier folds it away).
        skol[y] = AIG::new_const(false);
        trail.push_back({y, decision_lvl, /*is_decision=*/false, Lit(0, false), {}});
        clause_undet_delta(y, -1);
        mark_clauses_dead_by_constant(y, false);
        pa_assign(y, false, PA_REASON_SOURCE);
        tseitin_skol_into_skolem_sat(y);
        return true;
    }
    const bool val = has_pos;
    skol[y] = AIG::new_const(val);
    trail.push_back({y, decision_lvl, /*is_decision=*/false, Lit(0, false), {}});
    clause_undet_delta(y, -1);
    mark_clauses_dead_by_constant(y, val);
    pa_assign(y, val, PA_REASON_SOURCE);
    tseitin_skol_into_skolem_sat(y);
    return true;
}

void Cadet::enqueue_neighbours(uint32_t v,
                               std::vector<uint8_t>& in_queue,
                               std::vector<uint32_t>& queue) const {
    const auto& clauses = cnf.get_clauses();
    for (const auto& [ci, sign_v] : var_clauses[v]) {
        (void)sign_v;
        for (const auto& l : clauses[ci]) {
            const uint32_t u = l.var();
            if (u == v) continue;
            if (skol[u] != nullptr) continue;
            if (!in_queue[u]) {
                in_queue[u] = 1;
                queue.push_back(u);
            }
        }
    }
}

bool Cadet::synth_by_propagation() {
    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase C — unique-consequence propagation" << endl;
    }
    const double t0 = cpuTime();

    const auto new_to_orig = cnf.get_new_to_orig_var();
    std::map<uint32_t, vector<uint32_t>> dep_cache;

    skol.assign(cnf.nVars(), nullptr);
    for (uint32_t v : input) skol[v] = AIG::new_lit(v, /*neg=*/false);
    for (uint32_t v : backward_defined) skol[v] = AIG::new_lit(v, /*neg=*/false);

    pa_init();

    {
        const auto& clauses_ref = cnf.get_clauses();
        for (uint32_t ci = 0; ci < clauses_ref.size(); ci++) {
            uint32_t undet = 0;
            for (const auto& l : clauses_ref[ci]) {
                if (skol[l.var()] == nullptr) undet++;
            }
            n_undet_per_clause[ci] = static_cast<uint16_t>(undet);
        }
    }

    trail.clear();
    decision_lits.clear();
    sel_lits.clear();
    decision_lvl = 0;

    MetaSolver& decision_sat = *skolem_sat;

    // Worklist: only re-check undet neighbours of fresh commits.
    std::vector<uint8_t> in_queue(cnf.nVars(), 0);
    std::vector<uint32_t> queue;
    queue.reserve(to_define.size());
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) { in_queue[y] = 1; queue.push_back(y); }
    }

    // Defensive: handles a partially-built skol on re-entry (no-op today).
    for (uint32_t y : to_define) {
        if (skol[y] != nullptr && skol[y]->type == AIGT::t_const) {
            trail.push_back({y, decision_lvl,
                             /*is_decision=*/false, Lit(0, false), {}});
            mark_clauses_dead_by_constant(y, !skol[y].neg);
        }
    }

    uint32_t total_committed = 0;
    uint32_t total_decisions = 0;
    uint32_t total_pure = 0;
    uint32_t total_conflicts = 0;
    uint32_t total_restarts = 0;
    skolem_sat_replenishes = 0;
    total_ratified = 0;
    skolem_sat_commits_since_build = 0;
    uint32_t restart_threshold = mconf.cadet_restart_initial;
    uint32_t conflicts_since_restart = 0;
    const double restart_factor = mconf.cadet_restart_factor;
    // One more level-0 forced pass after the guess-depth cap.
    bool no_more_guesses = false;
    uint32_t pass = 0;
    while (true) {
        pass++;
        if (pa_conflict_clause != PA_NO_CONFLICT) {
            if (!handle_pa_conflict_1uip(in_queue, queue)) {
                backjump_to_level(0);
                if (conf.verb >= 1) {
                    cout << "c o [cadet] PA-UIP detected level-0 conflict "
                         << "— bailing out of Phase D" << endl;
                }
                break;
            }
            total_conflicts++;
            conflicts_since_restart++;
            continue;
        }
        if (decision_lvl > 0 &&
                conflicts_since_restart >= restart_threshold) {
            backjump_to_level(0);
            conflicts_since_restart = 0;
            restart_threshold = (uint32_t)(restart_threshold * restart_factor);
            total_restarts++;
            if (conf.verb >= 1) {
                cout << "c o [cadet] restart #" << total_restarts
                     << ", next threshold " << restart_threshold
                     << ", learnt=" << learnt_clauses.size() << endl;
            }
            for (uint32_t y : to_define) {
                if (skol[y] == nullptr && !in_queue[y]) {
                    in_queue[y] = 1;
                    queue.push_back(y);
                }
            }
        }
        if (decision_lvl == 0) maybe_replenish_skolem_sat();
        uint32_t committed_this_pass = 0;
        while (!queue.empty()) {
            const uint32_t y = queue.back();
            queue.pop_back();
            in_queue[y] = 0;
            // Unique-consequence first; pure-literal may apply even when
            // not-all-determined (one-sided surviving clauses suffice).
            bool committed = try_propagate(y, dep_cache, new_to_orig);
            if (!committed) {
                if (try_pure_literal(y)) {
                    committed = true;
                    total_pure++;
                }
            }
            if (committed) {
                committed_this_pass++;
                total_committed++;
                enqueue_neighbours(y, in_queue, queue);
                pa_drain_bcp(in_queue, queue);
            }
        }
        if (conf.verb >= 2) {
            cout << "c o [cadet]   prop pass #" << pass
                 << ": committed " << committed_this_pass << endl;
        }

        // Phase D forced-only: try every undet candidate; commit when
        // one polarity is universally forced (¬pos/¬neg UNSAT).

        // Global conflict check: F UNSAT under active selectors → learn.
        if (decision_lvl > 0) {
            vector<Lit> base = active_assumps();
            if (decision_sat.solve(&base) == CMSat::l_False) {
                std::set<uint32_t> kept_selectors;
                for (const Lit& f : decision_sat.get_conflict()) {
                    kept_selectors.insert(f.var());
                }
                minimize_failed_selectors(kept_selectors);

                vector<Lit> learnt;
                uint32_t max_lvl = 0, second_lvl = 0;
                for (uint32_t sv : kept_selectors) {
                    for (uint32_t d = 1; d <= decision_lvl; d++) {
                        if (sel_lits[d - 1].var() == sv) {
                            learnt.push_back(~decision_lits[d - 1]);
                            if (d > max_lvl) {
                                second_lvl = max_lvl;
                                max_lvl = d;
                            } else if (d > second_lvl) {
                                second_lvl = d;
                            }
                            break;
                        }
                    }
                }
                if (max_lvl == 0 || learnt.empty()) {
                    // F itself UNSAT — bail to Phase E/F.
                    backjump_to_level(0);
                    break;
                }
                for (const Lit& l : learnt) {
                    const uint32_t v = l.var();
                    if (v < var_activity.size()) bump_var(v);
                }
                decay_activities();
                // Permanent learnt clause. Refutes the current
                // decision conjunction across all inputs. Also store
                // for Phase E/F to inject into their fresh solvers.
                decision_sat.add_clause(learnt);
                learnt_clauses.push_back(learnt);
                total_conflicts++;
                conflicts_since_restart++;
                backjump_to_level(second_lvl);
                if (conf.verb >= 1) {
                    cout << "c o [cadet] CDCL conflict at lvl "
                         << max_lvl << ": learnt " << learnt.size()
                         << " lits, backjump to " << second_lvl << endl;
                }
                // Re-enqueue every still-undet var — they might be
                // forced under the new learnt clause.
                for (uint32_t y : to_define) {
                    if (skol[y] == nullptr && !in_queue[y]) {
                        in_queue[y] = 1;
                        queue.push_back(y);
                    }
                }
                continue; // restart outer loop with shallower state
            }
        }

        // Order undet by VSIDS activity (highest first). Activities are
        // JW-seeded from clause density and get bumped each time a var
        // shows up in a failed-assumption core, so vars participating
        // in many UNSAT proofs rise to the front.
        vector<uint32_t> undet;
        undet.reserve(to_define.size());
        for (uint32_t y : to_define) {
            if (skol[y] == nullptr) undet.push_back(y);
        }
        if (undet.empty()) break; // nothing left undetermined
        std::sort(undet.begin(), undet.end(),
                  [&](uint32_t a, uint32_t b) {
                      return var_activity[a] > var_activity[b];
                  });

        bool any_decided = false;
        vector<Lit> base_assumps = active_assumps();
        vector<Lit> assumps;
        assumps.reserve(base_assumps.size() + 1);
        for (uint32_t pick : undet) {
            if (skol[pick] != nullptr) continue; // earlier decision propagated

            auto bump_core = [&]() {
                // Every var in the failed-assumption core participated
                // in the UNSAT proof — bump its activity so it floats
                // up next pass.
                const auto failed = decision_sat.get_conflict();
                for (const auto& f : failed) {
                    const uint32_t v = f.var();
                    if (v < var_activity.size()) bump_var(v);
                }
                decay_activities();
            };

            // Two-sided probe: ¬pos_var[pick] UNSAT ⇒ pick forced TRUE.
            assumps = base_assumps;
            assumps.push_back(~pos_var[pick]);
            auto commit_const = [&](bool val) {
                bump_core();
                skol[pick] = AIG::new_const(val);
                trail.push_back({pick, decision_lvl,
                                 /*is_decision=*/false, Lit(0, false), {}});
                clause_undet_delta(pick, -1);
                mark_clauses_dead_by_constant(pick, val);
                pa_assign(pick, val, PA_REASON_SOURCE);
                tseitin_skol_into_skolem_sat(pick);
                total_decisions++;
                any_decided = true;
                enqueue_neighbours(pick, in_queue, queue);
                pa_drain_bcp(in_queue, queue);
                if (conf.verb >= 2) {
                    cout << "c o [cadet]   forced: skol[" << (pick + 1)
                         << "] := " << (val ? "true" : "false")
                         << " at lvl " << decision_lvl << endl;
                }
            };
            if (decision_sat.solve(&assumps) == CMSat::l_False) {
                two_sided_pos_unsat++;
                commit_const(true);
                continue;
            }
            assumps = base_assumps;
            assumps.push_back(~neg_var[pick]);
            if (decision_sat.solve(&assumps) == CMSat::l_False) {
                two_sided_neg_unsat++;
                commit_const(false);
                continue;
            }
        }

        if (!any_decided) {
            // CEGAR before speculative guess: finds y forced under
            // universal cubes (invisible to forced-only).
            if (decision_lvl == 0 && mconf.cadet_cegar) {
                if (cegar_drain_at_level_0(in_queue, queue)) continue;
            }
            uint32_t guess = UINT32_MAX;
            double best = -1.0;
            for (uint32_t y : to_define) {
                if (skol[y] != nullptr) continue;
                if (var_activity[y] > best) {
                    best = var_activity[y];
                    guess = y;
                }
            }
            if (guess == UINT32_MAX) break;
            const uint32_t max_guess_depth = mconf.cadet_max_guess_depth;
            if (no_more_guesses) break;
            if (decision_lvl >= max_guess_depth) {
                if (conf.verb >= 1) {
                    cout << "c o [cadet] Phase D: hit guess-depth cap "
                         << max_guess_depth << ", draining level-0 forced"
                         << endl;
                }
                backjump_to_level(0);
                no_more_guesses = true;
                for (uint32_t y : to_define) {
                    if (skol[y] == nullptr && !in_queue[y]) {
                        in_queue[y] = 1;
                        queue.push_back(y);
                    }
                }
                continue;
            }
            // JW-style polarity on residual undead clauses.
            uint32_t n_pos = 0, n_neg = 0;
            for (const auto& [ci, sign_y] : var_clauses[guess]) {
                if (clause_dead[ci]) continue;
                if (sign_y) n_neg++; else n_pos++;
            }
            const bool guess_val = (n_pos >= n_neg);
            make_decision(guess, guess_val);
            enqueue_neighbours(guess, in_queue, queue);
            pa_drain_bcp(in_queue, queue);
            if (conf.verb >= 1) {
                cout << "c o [cadet] Phase D: guess skol[" << (guess + 1)
                     << "] := " << (guess_val ? "true" : "false")
                     << " (lvl " << decision_lvl
                     << ", undet=" << undet.size() << ")" << endl;
            }
            continue;
        }
    }

    // Phase E/F see only level-0 commits. Ratify F-implied levels
    // before rolling back the rest.
    if (decision_lvl > 0) {
        if (mconf.cadet_ratify_speculative) ratify_speculative_decisions();
        if (decision_lvl > 0) backjump_to_level(0);
    }

    uint32_t remaining = 0;
    for (uint32_t y : to_define) if (skol[y] == nullptr) remaining++;

    if (conf.verb >= 1) {
        const uint32_t prop_only = total_committed > total_pure
                                       ? total_committed - total_pure : 0;
        cout << "c o [cadet] Phase C+D done. passes: " << pass
             << " uc-props: " << prop_only
             << " pure: " << total_pure
             << " forced: " << total_decisions
             << " conflicts: " << total_conflicts
             << " restarts: " << total_restarts
             << " learnt: " << learnt_clauses.size()
             << " remaining: " << remaining
             << " T: " << fixed << setprecision(2) << (cpuTime() - t0) << endl;
        if (two_sided_pos_unsat > 0 || two_sided_neg_unsat > 0) {
            cout << "c o [cadet]   two-sided forced: pos-UNSAT="
                 << two_sided_pos_unsat
                 << " neg-UNSAT=" << two_sided_neg_unsat << endl;
        }
        if (pa_propagations > 0 || uip_conflicts_handled > 0) {
            const double avg_uip_lits = uip_conflicts_handled > 0
                ? double(uip_learnt_lits_total) / double(uip_conflicts_handled)
                : 0.0;
            cout << "c o [cadet]   PA: bcp-propagations=" << pa_propagations
                 << " bcp-conflicts=" << pa_conflicts_caught
                 << " uip-conflicts=" << uip_conflicts_handled
                 << " avg-uip-lits=" << fixed << setprecision(1) << avg_uip_lits
                 << endl;
            if (uip_strict_synthetic_resolves > 0) {
                cout << "c o [cadet]   PA-UIP strict: synthetic-resolves="
                     << uip_strict_synthetic_resolves
                     << " decision-terminations="
                     << uip_strict_decision_terminations << endl;
            }
            if (uip_min_in_lits > 0) {
                const double drop_pct = 100.0
                    * double(uip_min_in_lits - uip_min_out_lits)
                    / double(uip_min_in_lits);
                cout << "c o [cadet]   PA-min: in-lits=" << uip_min_in_lits
                     << " out-lits=" << uip_min_out_lits
                     << " drop=" << fixed << setprecision(1) << drop_pct
                     << "%" << endl;
            }
        }
        if (clause_min_resolves > 0) {
            const double avg_in = double(clause_min_total_in_lits)
                                  / double(total_conflicts ? total_conflicts : 1);
            const double avg_out = double(clause_min_total_out_lits)
                                   / double(total_conflicts ? total_conflicts : 1);
            cout << "c o [cadet]   clausemin: resolves=" << clause_min_resolves
                 << " drops=" << clause_min_drops
                 << " avg-lits " << fixed << setprecision(2) << avg_in
                 << " -> " << avg_out << endl;
        }
        if (skolem_sat_replenishes > 0) {
            cout << "c o [cadet]   skolem_sat replenishes: "
                 << skolem_sat_replenishes << endl;
        }
        if (total_ratified > 0) {
            cout << "c o [cadet]   ratified levels: "
                 << total_ratified << endl;
        }
        if (cegar_stat_rounds > 0) {
            const double avg_kept = cegar_stat_joint_unsat > 0
                ? double(cegar_stat_cube_total)
                  / double(cegar_stat_joint_unsat)
                : 0.0;
            const double pery_ratio = cegar_per_y_checks > 0
                ? double(cegar_per_y_commits)
                  / double(cegar_per_y_checks)
                : 0.0;
            cout << "c o [cadet] CEGAR rounds=" << cegar_stat_rounds
                 << " (joint UNSAT=" << cegar_stat_joint_unsat
                 << " SAT=" << cegar_stat_joint_sat
                 << " UNDEF=" << cegar_stat_joint_undef
                 << ") joint-commits=" << cegar_stat_joint_commits
                 << " per-y-commits=" << cegar_stat_per_y_commits
                 << "/checks=" << cegar_per_y_checks
                 << " (ratio=" << fixed << setprecision(3) << pery_ratio
                 << (cegar_per_y_disabled ? ", DISABLED" : "")
                 << ") avg-kept-cube=" << fixed << setprecision(1) << avg_kept
                 << endl;
        }
    }
    return remaining == 0;
}

bool Cadet::synth_complete_with_models() {
    // Phase E: enumerate consistent X assignments, record undet y
    // values per model, build Shannon trees. Only runs when input
    // space is small enough.
    if (orig_sampl_cnf.size() > mconf.cadet_phase_e_threshold) return false;

    vector<uint32_t> undet;
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) undet.push_back(y);
    }
    if (undet.empty()) return true;

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase E — SAT-model completion on "
             << undet.size() << " undet vars over "
             << orig_sampl_cnf.size() << " orig sampling vars (Phase C+D "
             << "committed " << (to_define.size() - undet.size())
             << "/" << to_define.size() << " already)" << endl;
    }
    const double t0 = cpuTime();

    // Private solver — its forbid clauses must not leak into Phase D/F.
    MetaSolver sat(SolverType::cadical);
    Lit true_lit;
    build_solver_with_skols(sat, true_lit);
    (void)true_lit;

    vector<uint32_t> sorted_inputs(orig_sampl_cnf.begin(), orig_sampl_cnf.end());
    std::sort(sorted_inputs.begin(), sorted_inputs.end());
    const uint32_t n_in = sorted_inputs.size();
    const uint64_t n_assign = 1ull << n_in;

    // UNSAT-input rows stay false (vacuously free; AIG simplifier folds).
    std::unordered_map<uint32_t, vector<bool>> tables;
    tables.reserve(undet.size());
    for (uint32_t y : undet) tables[y].assign(n_assign, false);

    vector<Lit> forbid;
    forbid.reserve(n_in);
    uint64_t covered_count = 0;
    while (true) {
        const auto ret = sat.solve();
        if (ret == CMSat::l_False) break;
        if (ret != CMSat::l_True) return false; // Phase F will finish
        const auto& model = sat.get_model();
        uint64_t mask = 0;
        forbid.clear();
        for (uint32_t i = 0; i < n_in; i++) {
            const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
            if (mv) mask |= (1ull << i);
            forbid.push_back(Lit(sorted_inputs[i], mv));
        }
        if (mask < n_assign) {
            covered_count++;
            for (uint32_t y : undet) {
                tables[y][mask] = (model[y] == CMSat::l_True);
            }
        }
        sat.add_clause(forbid);
    }

    // Build Shannon trees for each undet y and commit.
    for (uint32_t y : undet) {
        skol[y] = build_shannon_tree(tables.at(y), sorted_inputs);
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase E done. covered " << covered_count
             << "/" << n_assign << " consistent input patterns. T: "
             << fixed << setprecision(2) << (cpuTime() - t0) << endl;
    }
    return true;
}

bool Cadet::synth_complete_with_interp_generalization() {
    // Monolithic Phase F (per-component decomposition was unsound;
    // worker kept parametrized for a future correct version).
    vector<uint32_t> all_undet;
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) all_undet.push_back(y);
    }
    if (all_undet.empty()) return true;
    vector<uint32_t> all_inputs(orig_sampl_cnf.begin(), orig_sampl_cnf.end());
    std::sort(all_inputs.begin(), all_inputs.end());
    return synth_phase_f_subset(all_inputs, all_undet);
}


bool Cadet::synth_phase_f_subset(const std::vector<uint32_t>& sub_inputs_in,
                                 const std::vector<uint32_t>& sub_undet) {
    // Per-iter: outer SAT model M → minim UNSAT under (sel + kept
    // input lits) → drop non-core bits → commit Y=M over kept region
    // (or per-y fallback on joint-SAT). No iter cap; ≤ 2^|inputs|.
    static constexpr uint32_t kPhaseFMaxIters = 5000; // logging cadence
    // Periodic AIG simplification keeps ITE-chain growth bounded.
    const uint32_t simplify_every = mconf.cadet_phase_f_simplify_every;

    const std::vector<uint32_t>& undet = sub_undet;
    if (undet.empty()) return true;

    if (conf.verb >= 1) {
        cout << "c o [cadet] Phase F worker — " << undet.size()
             << " undet vars over " << sub_inputs_in.size()
             << " inputs (no iter cap; "
             << "diagnostic-flush every " << kPhaseFMaxIters << ")" << endl;
    }
    const double t0 = cpuTime();

    // Two solvers: `sat` accumulates forbid clauses for outer
    // enumeration; `minim` stays forbid-free so the uniqueness check
    // can't be confused by previous cases overlapping ours.
    MetaSolver sat(SolverType::cadical);
    MetaSolver minim(SolverType::cadical);
    Lit sat_true_lit, minim_true_lit;
    build_solver_with_skols(sat, sat_true_lit);
    build_solver_with_skols(minim, minim_true_lit);
    (void)sat_true_lit; (void)minim_true_lit;

    vector<uint32_t> sorted_inputs = sub_inputs_in;
    std::sort(sorted_inputs.begin(), sorted_inputs.end());
    const uint32_t n_in = sorted_inputs.size();

    // Per-y partial Skolem: ITE chain of cases, FALSE fallback.
    std::unordered_map<uint32_t, aig_ptr> partial;
    partial.reserve(undet.size());
    for (uint32_t y : undet) partial[y] = AIG::new_const(false);

    uint32_t iters = 0;
    uint64_t total_drops = 0;
    bool converged = false;
    uint32_t n_uniq_unsat = 0;
    uint32_t n_uniq_sat = 0;
    uint32_t n_uniq_unknown = 0;
    uint64_t total_core_size = 0;
    uint64_t n_per_y_checks = 0;
    uint64_t n_per_y_commits = 0;
    bool per_y_disabled = false;
    // --cadetpartial K: bail after K outer iters; caller runs Manthan.
    const uint64_t partial_cap = mconf.cadet_partial;
    bool partial_bail = false;
    while (true) {
        const auto ret = sat.solve();
        if (ret == CMSat::l_False) { converged = true; break; }
        if (ret != CMSat::l_True) return false;
        iters++;
        if (partial_cap > 0 && iters > partial_cap) {
            // partial[y] still has FALSE-fallback ITE chains — don't
            // commit them; let Manthan finish.
            partial_bail = true;
            break;
        }

        const auto& model = sat.get_model();

        // Uniqueness clause goes into minim (NOT sat — its forbid
        // clauses would confuse the check).
        minim.new_var();
        const uint32_t sel_var = minim.nVars() - 1;
        const Lit sel_lit(sel_var, /*sign=*/false);
        std::vector<Lit> uniq_clause;
        uniq_clause.reserve(undet.size() + 1);
        uniq_clause.push_back(~sel_lit);
        for (uint32_t y : undet) {
            const bool v = (model[y] == CMSat::l_True);
            uniq_clause.push_back(Lit(y, /*sign=*/v));
        }
        minim.add_clause(uniq_clause);

        // One UNSAT-core solve drops every input bit not in the core.
        std::vector<bool> kept(n_in, true);
        uint32_t bits_dropped = 0;
        lbool joint_unique_result = CMSat::l_Undef;
        {
            std::vector<Lit> assumps;
            assumps.reserve(n_in + 1);
            assumps.push_back(sel_lit);
            for (uint32_t i = 0; i < n_in; i++) {
                const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
                assumps.push_back(Lit(sorted_inputs[i], /*sign=*/!mv));
            }
            const auto r = minim.solve(&assumps);
            joint_unique_result = r;
            if (r == CMSat::l_False) {
                n_uniq_unsat++;
                const auto failed = minim.get_conflict();
                total_core_size += failed.size();
                std::set<uint32_t> failed_vars;
                for (const Lit& f : failed) failed_vars.insert(f.var());
                // Bump every var in the joint UNSAT core — those input
                // bits and undet vars that participated in the proof
                // are the discriminative ones.
                for (uint32_t v : failed_vars) {
                    if (v < var_activity.size()) bump_var(v);
                }
                decay_activities();
                for (uint32_t i = 0; i < n_in; i++) {
                    if (failed_vars.count(sorted_inputs[i]) == 0) {
                        kept[i] = false;
                        bits_dropped++;
                    }
                }
            } else if (r == CMSat::l_True) {
                n_uniq_sat++;
                // joint y=M is not unique at this input pattern
                // (multiple joint y satisfy F here). No bit can be
                // dropped JOINTLY; the joint case covers only this
                // exact input. But individual y's might still be
                // forced — fall through to per-y uniqueness check
                // below the joint commit block.
            } else {
                n_uniq_unknown++;
                // UNDEF — solver gave up. Same fallback: no drops.
            }
        }
        total_drops += bits_dropped;

        // Deactivate the uniqueness clause permanently (we don't need
        // it anymore; future iterations get their own selectors).
        minim.add_clause({~sel_lit});

        // Build min_pattern AIG from the kept bits. If everything was
        // dropped, the case covers the WHOLE input space — joint y =
        // M is the unique Skolem and we can commit constants.
        aig_ptr min_pattern = AIG::new_const(true);
        std::vector<Lit> forbid_clause;
        bool any_kept = false;
        for (uint32_t i = 0; i < n_in; i++) {
            if (!kept[i]) continue;
            any_kept = true;
            const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
            min_pattern = AIG::new_and(min_pattern, AIG::new_lit(sorted_inputs[i], !mv));
            forbid_clause.push_back(Lit(sorted_inputs[i], mv));
        }

        if (!any_kept) {
            // Whole input space → joint y = M is the unique Skolem
            // globally. Commit constants and we're done.
            for (uint32_t y : undet) {
                const bool v = (model[y] == CMSat::l_True);
                partial[y] = AIG::new_const(v);
            }
            if (conf.verb >= 2) {
                cout << "c o [cadet]   iter " << iters
                     << ": commit covers entire input space" << endl;
            }
            converged = true;
            break;
        }

        // Prepend the case to each undet y's partial Skolem:
        //   new_skol = ITE(min_pattern, M[y], old_skol)
        for (uint32_t y : undet) {
            const bool v = (model[y] == CMSat::l_True);
            partial[y] = AIG::new_ite(AIG::new_const(v), partial[y], min_pattern);
        }
        sat.add_clause(forbid_clause);

        if (conf.verb >= 2) {
            cout << "c o [cadet]   iter " << iters
                 << ": kept " << (n_in - bits_dropped)
                 << " / " << n_in << " bits" << endl;
        }

        // Per-y fallback on joint-SAT iters: ask "y forced alone at
        // X*?" — commits `(X ≠ kept) ∨ (y = M[y])`. Static cap +
        // adaptive productivity bail prevent ruinous huge-undet runs.
        const uint32_t per_y_undet_cap = mconf.cadet_phase_f_per_y_undet_cap;
        const uint64_t per_y_window = mconf.cadet_phase_f_per_y_window;
        const double per_y_min_productivity = mconf.cadet_phase_f_per_y_min_productivity;
        const bool was_joint_sat_this_iter = (joint_unique_result == CMSat::l_True);
        if (!per_y_disabled && per_y_window > 0 &&
            n_per_y_checks >= per_y_window) {
            const double ratio = double(n_per_y_commits) / double(n_per_y_checks);
            if (ratio < per_y_min_productivity) {
                per_y_disabled = true;
                if (conf.verb >= 1) {
                    cout << "c o [cadet]   Phase F per-y disabled at iter "
                         << iters << ": productivity "
                         << fixed << setprecision(3) << ratio
                         << " < " << per_y_min_productivity
                         << " ("  << n_per_y_commits << "/" << n_per_y_checks
                         << ")" << endl;
                }
            }
        }
        if (was_joint_sat_this_iter && undet.size() <= per_y_undet_cap
            && !per_y_disabled) {
            std::vector<uint32_t> py_order(undet.begin(), undet.end());
            std::sort(py_order.begin(), py_order.end(),
                      [&](uint32_t a, uint32_t b) {
                          return var_activity[a] > var_activity[b];
                      });
            for (uint32_t y : py_order) {
                n_per_y_checks++;
                minim.new_var();
                const uint32_t sel_y_var = minim.nVars() - 1;
                const Lit sel_y(sel_y_var, /*sign=*/false);
                const bool y_v = (model[y] == CMSat::l_True);
                minim.add_clause({~sel_y, Lit(y, /*sign=*/y_v)});

                std::vector<Lit> assumps;
                assumps.reserve(n_in + 1);
                assumps.push_back(sel_y);
                for (uint32_t i = 0; i < n_in; i++) {
                    const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
                    assumps.push_back(Lit(sorted_inputs[i], /*sign=*/!mv));
                }
                const auto rr = minim.solve(&assumps);
                minim.add_clause({~sel_y});

                if (rr != CMSat::l_False) continue;

                const auto failed = minim.get_conflict();
                std::set<uint32_t> failed_vars;
                for (const Lit& f : failed) failed_vars.insert(f.var());

                bump_var(y);
                for (const auto& f : failed) {
                    const uint32_t v = f.var();
                    if (v < var_activity.size()) bump_var(v);
                }
                decay_activities();

                // Commit (X ≠ kept) ∨ (y = M[y]).
                std::vector<Lit> commit_clause;
                commit_clause.reserve(n_in + 1);
                aig_ptr case_aig = AIG::new_const(true);
                for (uint32_t i = 0; i < n_in; i++) {
                    if (failed_vars.count(sorted_inputs[i]) == 0) continue;
                    const bool mv = (model[sorted_inputs[i]] == CMSat::l_True);
                    commit_clause.push_back(Lit(sorted_inputs[i], /*sign=*/mv));
                    case_aig = AIG::new_and(case_aig,
                        AIG::new_lit(sorted_inputs[i], /*neg=*/!mv));
                }
                commit_clause.push_back(Lit(y, /*sign=*/!y_v));
                sat.add_clause(commit_clause);
                minim.add_clause(commit_clause);

                partial[y] = AIG::new_ite(AIG::new_const(y_v),
                                          partial[y], case_aig);
                n_per_y_commits++;
            }
        }

        if (simplify_every > 0 && iters % simplify_every == 0) {
            for (uint32_t y : undet) {
                partial[y] = AIG::simplify_aig(partial[y]);
            }
            if (conf.verb >= 1) {
                cout << "c o [cadet]   Phase F progress: iter=" << iters
                     << " uniq-UNSAT=" << n_uniq_unsat
                     << " uniq-SAT=" << n_uniq_sat
                     << " per-y-checks=" << n_per_y_checks
                     << " per-y-commits=" << n_per_y_commits
                     << " T=" << fixed << setprecision(2)
                     << (cpuTime() - t0) << endl;
            }
        }
    }

    auto print_phase_f_stats = [&](const std::string& outcome) {
        cout << "c o [cadet] Phase F " << outcome
             << ". iters=" << iters
             << " uniq-UNSAT=" << n_uniq_unsat
             << " uniq-SAT=" << n_uniq_sat
             << " uniq-UNDEF=" << n_uniq_unknown
             << " per-y-commits=" << n_per_y_commits
             << " / checks=" << n_per_y_checks
             << " avg-drops/iter=" << std::fixed << setprecision(1)
             << (iters > 0 ? double(total_drops) / iters : 0.0)
             << " avg-core-size=" << std::fixed << setprecision(1)
             << (n_uniq_unsat > 0 ? double(total_core_size) / n_uniq_unsat : 0.0)
             << " T=" << fixed << setprecision(2) << (cpuTime() - t0) << endl;
    };

    if (partial_bail) {
        if (conf.verb >= 1) {
            print_phase_f_stats("PARTIAL bail (--cadetpartial cap reached)");
            cout << "c o [cadet] Phase F partial bail at iter " << iters
                 << " (--cadetpartial=" << partial_cap << "); "
                 << undet.size() << " undet vars left for Manthan" << endl;
        }
        return true;
    }

    if (!converged) {
        // SAT-solver UNDEF on outer solve.
        if (conf.verb >= 1) {
            print_phase_f_stats("did NOT converge (SAT UNDEF — bailing)");
        }
        return false;
    }

    for (uint32_t y : undet) skol[y] = partial[y];

    if (conf.verb >= 1) {
        print_phase_f_stats("converged + committed");
    }
    return true;
}

void Cadet::cegar_build_interface() {
    // Vars outside the interface can't help force any undet y.
    cegar_interface.clear();
    if (orig_sampl_cnf.empty()) return;
    std::vector<uint8_t> seen_clause(cnf.get_clauses().size(), 0);
    std::vector<uint8_t> in_interface(cnf.nVars(), 0);
    const auto& clauses = cnf.get_clauses();
    for (uint32_t y : to_define) {
        for (const auto& [ci, sign_y] : var_clauses[y]) {
            (void)sign_y;
            if (seen_clause[ci]) continue;
            seen_clause[ci] = 1;
            for (const auto& l : clauses[ci]) {
                const uint32_t u = l.var();
                if (u == y) continue;
                if (in_interface[u]) continue;
                if (orig_sampl_cnf.count(u) == 0) continue;
                in_interface[u] = 1;
                cegar_interface.push_back(u);
            }
        }
    }
    std::sort(cegar_interface.begin(), cegar_interface.end());
    if (conf.verb >= 1) {
        cout << "c o [cadet] CEGAR interface: " << cegar_interface.size()
             << " / " << orig_sampl_cnf.size() << " orig sampling vars"
             << " co-occur with to_define" << endl;
    }
}

void Cadet::cegar_build_exists_solver() {
    // Build from scratch: F + a true-literal + Tseitin of every
    // currently-committed skol[y]. All to_define vars whose skol[]
    // entry is non-null at the time of the call are encoded. Caller is
    // responsible for calling this only at decision_lvl == 0 so the
    // skol[] table represents only permanent commits.
    exists_solver = std::make_unique<MetaSolver>(SolverType::cadical);
    inject_cnf(*exists_solver);
    exists_solver->new_var();
    exists_solver_true_lit = CMSat::Lit(exists_solver->nVars() - 1,
                                         /*sign=*/false);
    exists_solver->add_clause({exists_solver_true_lit});
    // Replay CDCL learnt clauses from Phase D — same logic as
    // build_solver_with_skols, so the fresh exists_solver benefits from
    // the combinatorial pruning Phase D has accumulated.
    for (const auto& lc : learnt_clauses) exists_solver->add_red_clause(lc);
    // Reset per-var encoded flags; sync will fill in skol entries.
    exists_solver_encoded.assign(cnf.nVars(), 0);
    exists_solver_committed_count = 0;
    cegar_sync_exists_solver();
}

void Cadet::cegar_sync_exists_solver() {
    // Bring exists_solver up to date with any to_define-var skol[]
    // entries that have been committed since the last sync. Caller
    // must invoke at decision_lvl == 0 (so every non-null skol[v] for
    // v in to_define is a permanent level-0 commit, not speculative).
    if (!exists_solver) return;
    using AIGEnc = ArjunNS::AIGToCNF<MetaSolver>;
    AIGEnc enc(*exists_solver);
    enc.set_true_lit(exists_solver_true_lit);
    for (uint32_t y : to_define) {
        if (exists_solver_encoded[y]) continue;
        if (skol[y] == nullptr) continue;
        if (skol[y]->type == AIGT::t_const) {
            const bool val = !skol[y].neg;
            exists_solver->add_clause({CMSat::Lit(y, /*sign=*/!val)});
        } else {
            const CMSat::Lit root = enc.encode(skol[y]);
            exists_solver->add_clause({~CMSat::Lit(y, /*sign=*/false), root});
            exists_solver->add_clause({CMSat::Lit(y, /*sign=*/false), ~root});
        }
        exists_solver_encoded[y] = 1;
        exists_solver_committed_count++;
    }
}

Cadet::CegarRoundResult Cadet::cegar_one_round(
    std::vector<uint8_t>& in_queue,
    std::vector<uint32_t>& queue) {
    CegarRoundResult R;
    assert(decision_lvl == 0);
    if (cegar_interface.empty()) return R;

    std::vector<uint32_t> undet;
    undet.reserve(to_define.size());
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) undet.push_back(y);
    }
    if (undet.empty()) return R;

    if (!exists_solver) cegar_build_exists_solver();
    else cegar_sync_exists_solver();

    cegar_stat_rounds++;
    cegar_total_rounds++;

    // Forbid-selectors are CEGAR-only — Phase D probes never assume them.
    const auto outer_ret = cegar_forbid_selectors.empty()
        ? skolem_sat->solve()
        : skolem_sat->solve(&cegar_forbid_selectors);
    if (outer_ret == CMSat::l_False) return R;
    if (outer_ret != CMSat::l_True) return R;
    const auto& model = skolem_sat->get_model();

    std::vector<std::pair<uint32_t, bool>> cube;
    cube.reserve(cegar_interface.size());
    for (uint32_t v : cegar_interface) {
        if (model[v] == CMSat::l_True)  cube.emplace_back(v, true);
        else if (model[v] == CMSat::l_False) cube.emplace_back(v, false);
    }

    exists_solver->new_var();
    const CMSat::Lit sel(exists_solver->nVars() - 1, /*sign=*/false);
    std::vector<CMSat::Lit> uniq_clause;
    uniq_clause.reserve(undet.size() + 1);
    uniq_clause.push_back(~sel);
    for (uint32_t y : undet) {
        const bool v = (model[y] == CMSat::l_True);
        uniq_clause.push_back(CMSat::Lit(y, /*sign=*/v));
    }
    exists_solver->add_clause(uniq_clause);

    std::vector<CMSat::Lit> assumps;
    assumps.reserve(cube.size() + 1);
    assumps.push_back(sel);
    for (const auto& [v, val] : cube) {
        assumps.push_back(CMSat::Lit(v, /*sign=*/!val));
    }
    const auto inner_ret = exists_solver->solve(&assumps);

    exists_solver->add_clause({~sel});

    if (inner_ret == CMSat::l_True) {
        cegar_stat_joint_sat++;
        const bool do_per_y = mconf.cadet_cegar_per_y
                              && !cegar_per_y_disabled
                              && undet.size() <= mconf.cadet_cegar_per_y_undet_cap;

        std::vector<uint32_t> py_order(undet.begin(), undet.end());
        std::sort(py_order.begin(), py_order.end(),
                  [&](uint32_t a, uint32_t b) {
                      return var_activity[a] > var_activity[b];
                  });

        if (do_per_y) for (uint32_t y : py_order) {
            if (skol[y] != nullptr) continue;
            cegar_per_y_checks++;
            exists_solver->new_var();
            const CMSat::Lit sel_y(exists_solver->nVars() - 1,
                                    /*sign=*/false);
            const bool y_v = (model[y] == CMSat::l_True);
            exists_solver->add_clause({~sel_y,
                                       CMSat::Lit(y, /*sign=*/y_v)});

            std::vector<CMSat::Lit> py_assumps;
            py_assumps.reserve(cube.size() + 1);
            py_assumps.push_back(sel_y);
            for (const auto& [v, val] : cube) {
                py_assumps.push_back(CMSat::Lit(v, /*sign=*/!val));
            }
            const auto rr = exists_solver->solve(&py_assumps);
            exists_solver->add_clause({~sel_y});
            if (rr != CMSat::l_False) continue;

            const auto py_failed = exists_solver->get_conflict();
            std::set<uint32_t> py_failed_vars;
            for (const auto& f : py_failed) py_failed_vars.insert(f.var());
            bump_var(y);
            for (const auto& f : py_failed) {
                const uint32_t v = f.var();
                if (v < var_activity.size()) bump_var(v);
            }
            decay_activities();

            std::vector<std::pair<uint32_t, bool>> py_kept;
            py_kept.reserve(cube.size());
            for (const auto& [v, val] : cube) {
                if (py_failed_vars.count(v)) py_kept.emplace_back(v, val);
            }

            if (py_kept.empty()) {
                skol[y] = AIG::new_const(y_v);
                trail.push_back({y, /*dec_lvl=*/0, /*is_decision=*/false,
                                 CMSat::Lit(0, false), {}});
                mark_clauses_dead_by_constant(y, y_v);
                pa_assign(y, y_v, PA_REASON_SOURCE);
                tseitin_skol_into_skolem_sat(y);
                exists_solver_encoded[y] = 0;
                enqueue_neighbours(y, in_queue, queue);
                cegar_per_y_commits++;
                cegar_stat_per_y_commits++;
                R.constant_commit = true;
                R.any_clause_added = true;
                continue;
            }

            // (X ≠ kept) ∨ (y = M[y]). Don't forbid the per-y cube in
            // exists_solver — would block joint rounds where OTHER y's
            // aren't forced there.
            std::vector<CMSat::Lit> py_commit;
            py_commit.reserve(py_kept.size() + 1);
            for (const auto& [v, val] : py_kept) {
                py_commit.push_back(CMSat::Lit(v, /*sign=*/val));
            }
            py_commit.push_back(CMSat::Lit(y, /*sign=*/!y_v));
            skolem_sat->add_clause(py_commit);
            learnt_clauses.push_back(py_commit);
            cegar_per_y_commits++;
            cegar_stat_per_y_commits++;
            R.any_clause_added = true;
        }

        if (!cegar_per_y_disabled &&
            mconf.cadet_cegar_per_y_productivity_window > 0 &&
            cegar_per_y_checks >= mconf.cadet_cegar_per_y_productivity_window) {
            const double ratio =
                double(cegar_per_y_commits) / double(cegar_per_y_checks);
            if (ratio < mconf.cadet_cegar_per_y_min_productivity) {
                cegar_per_y_disabled = true;
                if (conf.verb >= 1) {
                    cout << "c o [cadet] CEGAR per-y disabled: "
                         << "productivity " << fixed << setprecision(3)
                         << ratio << " < "
                         << mconf.cadet_cegar_per_y_min_productivity
                         << " (" << cegar_per_y_commits << "/"
                         << cegar_per_y_checks << ")" << endl;
                }
            }
        }
        // Forbid this X-cube so the next CEGAR solve picks a different
        // M. Gated by a selector (cegar_forbid_selectors) so Phase D
        // probes are unaffected (load-bearing for soundness).
        if (mconf.cadet_cegar_forbid_on_sat && !R.constant_commit && !cube.empty()) {
            skolem_sat->new_var();
            const CMSat::Lit fsel(skolem_sat->nVars() - 1, /*sign=*/false);
            std::vector<CMSat::Lit> forbid;
            forbid.reserve(cube.size() + 1);
            forbid.push_back(~fsel);
            for (const auto& [v, val] : cube) {
                // (v, val) in cube ⇒ literal `v != val`, i.e. sign=val.
                forbid.push_back(CMSat::Lit(v, /*sign=*/val));
            }
            skolem_sat->add_clause(forbid);
            cegar_forbid_selectors.push_back(fsel);
            R.any_clause_added = true;
        }
        return R;
    }
    if (inner_ret != CMSat::l_False) {
        cegar_stat_joint_undef++;
        return R; // UNDEF
    }
    // UNSAT: joint Y is forced under (some subset of) the cube.
    cegar_stat_joint_unsat++;

    // (5) Extract core: which cube lits + sel are in the UNSAT proof?
    // Drop cube vars not in core. Bump every var in the core (VSIDS).
    const auto failed = exists_solver->get_conflict();
    std::set<uint32_t> failed_vars;
    for (const CMSat::Lit& f : failed) failed_vars.insert(f.var());
    for (uint32_t v : failed_vars) {
        if (v < var_activity.size()) bump_var(v);
    }
    decay_activities();

    // Build the kept_cube: cube entries whose var appears in the core.
    std::vector<std::pair<uint32_t, bool>> kept_cube;
    kept_cube.reserve(cube.size());
    for (const auto& [v, val] : cube) {
        if (failed_vars.count(v)) kept_cube.emplace_back(v, val);
    }
    R.kept_cube_size = (uint32_t)kept_cube.size();
    cegar_stat_cube_total += R.kept_cube_size;

    if (kept_cube.empty()) {
        // Joint Y = M[y] universally — commit constants.
        for (uint32_t y : undet) {
            if (skol[y] != nullptr) continue;
            const bool v = (model[y] == CMSat::l_True);
            skol[y] = AIG::new_const(v);
            trail.push_back({y, /*dec_lvl=*/0, /*is_decision=*/false,
                             CMSat::Lit(0, false), {}});
            mark_clauses_dead_by_constant(y, v);
            pa_assign(y, v, PA_REASON_SOURCE);
            tseitin_skol_into_skolem_sat(y);
            exists_solver_encoded[y] = 0;
            enqueue_neighbours(y, in_queue, queue);
            if (y < var_activity.size()) bump_var(y);
            cegar_stat_joint_commits++;
            R.constant_commit = true;
        }
        pa_drain_bcp(in_queue, queue);
        R.any_clause_added = true;
        return R;
    }

    // Per-y: (X ≠ kept) ∨ (y = M[y]) into skolem_sat + learnt_clauses.
    // Forbid (X ≠ kept) only in exists_solver (would conflict with the
    // per-y clauses in skolem_sat).
    std::vector<CMSat::Lit> forbid;
    forbid.reserve(kept_cube.size());
    for (const auto& [v, val] : kept_cube) {
        forbid.push_back(CMSat::Lit(v, /*sign=*/val));
    }
    for (uint32_t y : undet) {
        const bool y_v = (model[y] == CMSat::l_True);
        std::vector<CMSat::Lit> commit_clause = forbid;
        commit_clause.push_back(CMSat::Lit(y, /*sign=*/!y_v));
        skolem_sat->add_clause(commit_clause);
        learnt_clauses.push_back(commit_clause);
        if (y < var_activity.size()) bump_var(y);
    }
    decay_activities();
    exists_solver->add_clause(forbid);
    cegar_stat_joint_commits++;
    R.any_clause_added = true;
    return R;
}

bool Cadet::cegar_drain_at_level_0(std::vector<uint8_t>& in_queue,
                                   std::vector<uint32_t>& queue) {
    assert(decision_lvl == 0);
    if (!mconf.cadet_cegar) return false;
    if (cegar_disabled) return false;
    if (cegar_interface.empty()) return false;
    const uint32_t max_total = mconf.cadet_cegar_max_total_rounds;
    if (max_total > 0 && cegar_total_rounds >= max_total) return false;

    bool any_constant_commit = false;
    uint32_t rounds = 0;
    uint64_t cube_sum = 0;
    uint64_t cube_count = 0;
    uint32_t consec_no_constant = 0;
    uint32_t consec_noop = 0;
    while (rounds < mconf.cadet_cegar_max_rounds_per_stall) {
        if (max_total > 0 && cegar_total_rounds >= max_total) break;
        // Need ≥3 UNSAT rounds before trusting the average.
        if (cube_count >= 3 &&
            (cube_sum / cube_count) > mconf.cadet_cegar_max_avg_cube) {
            if (conf.verb >= 2) {
                cout << "c o [cadet]   CEGAR stall break: avg kept-cube "
                     << (cube_sum / cube_count) << " > "
                     << mconf.cadet_cegar_max_avg_cube << endl;
            }
            break;
        }
        const CegarRoundResult res = cegar_one_round(in_queue, queue);
        rounds++;
        if (res.kept_cube_size != UINT32_MAX && res.kept_cube_size > 0) {
            cube_sum += res.kept_cube_size;
            cube_count++;
        }
        if (res.constant_commit) {
            any_constant_commit = true;
            consec_no_constant = 0;
            consec_noop = 0;
            continue;
        }
        consec_no_constant++;
        if (mconf.cadet_cegar_consec_bail > 0 &&
            consec_no_constant >= mconf.cadet_cegar_consec_bail) break;
        if (!res.any_clause_added) {
            consec_noop++;
            if (mconf.cadet_cegar_noop_bail == 0 ||
                consec_noop >= mconf.cadet_cegar_noop_bail) break;
        } else {
            consec_noop = 0;
        }
    }
    if (conf.verb >= 2 && rounds > 0) {
        cout << "c o [cadet]   CEGAR drain: rounds=" << rounds
             << " const_commits=" << (any_constant_commit ? "yes" : "no")
             << " avg_kept=";
        if (cube_count > 0) cout << (cube_sum / cube_count);
        else cout << "n/a";
        cout << endl;
    }
    // Outer adaptive disable: stop CEGAR after N rounds with no commit.
    if (!cegar_disabled &&
        mconf.cadet_cegar_overall_disable_after > 0 &&
        cegar_total_rounds >= mconf.cadet_cegar_overall_disable_after &&
        cegar_stat_joint_commits == 0 &&
        cegar_per_y_commits == 0) {
        cegar_disabled = true;
        if (conf.verb >= 1) {
            cout << "c o [cadet] CEGAR disabled for rest of Phase D: "
                 << cegar_total_rounds << " rounds without any commit"
                 << endl;
        }
    } else if (!cegar_disabled &&
               mconf.cadet_cegar_overall_disable_after > 0 &&
               cegar_total_rounds >=
                   mconf.cadet_cegar_overall_disable_after * 3 &&
               cegar_stat_joint_commits == 0) {
        // 3× window with per-y clauses but no constant commits.
        cegar_disabled = true;
        if (conf.verb >= 1) {
            cout << "c o [cadet] CEGAR disabled for rest of Phase D: "
                 << cegar_total_rounds
                 << " rounds without any CONSTANT commit (per-y produced "
                 << cegar_per_y_commits << " constraint clauses but "
                 << "nothing to shrink undet)" << endl;
        }
    }
    return any_constant_commit;
}

void Cadet::commit_definitions() {
    // Missing skol[y] only legal under --cadetpartial > 0 (Manthan
    // finishes those).
    vector<aig_ptr> aigs(cnf.nVars(), nullptr);
    for (uint32_t y : to_define) {
        if (skol[y] == nullptr) {
            release_assert(mconf.cadet_partial > 0 &&
                           "cadet must produce a Skolem for every to_define var "
                           "unless --cadetpartial > 0");
            continue;
        }
        aigs[y] = skol[y];
    }
    const uint32_t cnf_nvars = cnf.nVars();
    cnf.map_aigs_to_orig(aigs, cnf_nvars);

    cnf.simplify_aigs(conf.verb);
}

SimplifiedCNF Cadet::do_cadet() {
    const double my_time = cpuTime();
    if (conf.verb >= 1) {
        cout << "c o [cadet] starting; nVars=" << cnf.nVars()
             << " clauses=" << cnf.get_clauses().size() << endl;
    }

    cnf.get_var_types(conf.verb, "start do_cadet").unpack_to(
        input, to_define, backward_defined);

    // VarTypes.input lumps extend-defined vars in; orig_sampl_cnf is
    // the narrower set we actually enumerate over.
    orig_sampl_cnf.clear();
    const auto& o2n = cnf.get_orig_to_new_var();
    for (uint32_t v : cnf.get_orig_sampl_vars()) {
        auto it = o2n.find(v);
        if (it == o2n.end()) continue;
        orig_sampl_cnf.insert(it->second.var());
    }

    if (to_define.empty()) {
        if (conf.verb >= 1) {
            cout << "c o [cadet] nothing to define — returning unchanged CNF" << endl;
        }
        return std::move(cnf);
    }

    if (conf.verb >= 1) {
        cout << "c o [cadet] partition: |orig_sampl|=" << orig_sampl_cnf.size()
             << " |input|=" << input.size()
             << " |to_define|=" << to_define.size()
             << " |backward_defined|=" << backward_defined.size() << endl;
    }

    {
        const auto& clauses = cnf.get_clauses();
        var_clauses.assign(cnf.nVars(), {});
        for (uint32_t ci = 0; ci < clauses.size(); ci++) {
            for (const auto& l : clauses[ci]) {
                var_clauses[l.var()].emplace_back(ci, l.sign());
            }
        }
        clause_dead.assign(clauses.size(), 0);
        n_undet_per_clause.assign(clauses.size(), 0);
    }

    cegar_build_interface();
    exists_solver.reset();
    exists_solver_committed_count = 0;
    cegar_total_rounds = 0;
    cegar_per_y_checks = 0;
    cegar_per_y_commits = 0;
    cegar_per_y_disabled = false;
    cegar_disabled = false;
    cegar_forbid_selectors.clear();
    cegar_stat_rounds = 0;
    cegar_stat_joint_unsat = 0;
    cegar_stat_joint_sat = 0;
    cegar_stat_joint_undef = 0;
    cegar_stat_cube_total = 0;
    cegar_stat_joint_commits = 0;
    cegar_stat_per_y_commits = 0;

    // JW-style seed: short clauses weighted higher (2^-len summed).
    var_activity.assign(cnf.nVars(), 0.0);
    activity_inc = 1.0;
    {
        const auto& clauses = cnf.get_clauses();
        for (const auto& c : clauses) {
            if (c.size() > 10) continue;
            const double w = std::ldexp(1.0, -(int)c.size());
            for (const auto& l : c) var_activity[l.var()] += w;
        }
    }

    skolem_sat = std::make_unique<MetaSolver>(SolverType::cadical);
    inject_cnf(*skolem_sat);
    skolem_sat->new_var();
    skolem_sat_true_lit = Lit(skolem_sat->nVars() - 1, /*sign=*/false);
    skolem_sat->add_clause({skolem_sat_true_lit});

    two_sided_build(*skolem_sat);

    bool done = synth_by_propagation();
    if (!done) done = synth_complete_with_models();
    if (!done) done = synth_complete_with_interp_generalization();

    release_assert(done && "Phase F is terminal");

    commit_definitions();

    if (conf.verb >= 1) {
        uint32_t committed = 0;
        for (uint32_t y : to_define) if (skol[y] != nullptr) committed++;
        if (committed == to_define.size()) {
            cout << "c o [cadet] done — all " << to_define.size()
                 << " to_define vars committed. T: "
                 << fixed << setprecision(2) << (cpuTime() - my_time) << endl;
        } else {
            cout << "c o [cadet] PARTIAL: committed " << committed
                 << " of " << to_define.size() << " to_define vars "
                 << "(--cadetpartial=" << mconf.cadet_partial << "); "
                 << (to_define.size() - committed) << " left for Manthan. T: "
                 << fixed << setprecision(2) << (cpuTime() - my_time) << endl;
        }
    }
    return std::move(cnf);
}

} // namespace ArjunInt
