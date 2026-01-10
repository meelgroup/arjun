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


#include <cstdint>
#include <limits>
#include <sbva/sbva.h>
#include <sstream>
#include "arjun.h"
#include "config.h"
#include "minimize.h"
#include "GitSHA1.h"
#include "puura.h"
#include "extend.h"
#include "time_mem.h"
#include "constants.h"
#ifdef SYNTH
#include "manthan.h"
#endif

using namespace ArjunInt;

#if defined _WIN32
    #define DLL_PUBLIC __declspec(dllexport)
#else
    #define DLL_PUBLIC __attribute__ ((visibility ("default")))
    #define DLL_LOCAL  __attribute__ ((visibility ("hidden")))
#endif

#define set_get_macro(TYPE, NAME) \
DLL_PUBLIC void Arjun::set_##NAME (TYPE NAME) \
{ \
    arjdata->conf.NAME = NAME; \
} \
DLL_PUBLIC TYPE Arjun::get_##NAME () const \
{ \
    return arjdata->conf.NAME; \
} \

namespace ArjunNS {
    struct ArjPrivateData {
        Config conf;
    };
}

using namespace ArjunNS;
using std::make_shared;
using std::stringstream;
using std::function;
using std::tuple;
using std::ifstream;
using std::ofstream;
using std::numeric_limits;

void check_duplicated(bool duplicated) {
    if (!duplicated) return;
    cout << "ERROR: manipulating the solver AFTER call to indep support manipulation" << endl;
    assert(false);
    exit(EXIT_FAILURE);
}

DLL_PUBLIC Arjun::Arjun() { arjdata = new ArjPrivateData; }
DLL_PUBLIC Arjun::~Arjun() { delete arjdata; }
DLL_PUBLIC string Arjun::get_sbva_version_sha1() {
    return SBVA::get_version_sha1();
}

DLL_PUBLIC string Arjun::get_version_sha1() {
    return ArjunIntNS::get_version_sha1();
}

DLL_PUBLIC string Arjun::get_thanks_info(const char* prefix) {
    stringstream ss;
    ss << prefix << "Using ideas by JM Lagniez, and Pierre Marquis" << endl;
    ss << prefix << "    from paper 'Improving Model Counting [..] IJCAI 2016";
    return ss.str();
}

DLL_PUBLIC string Arjun::get_solver_version_sha1() {
    return CMSat::SATSolver::get_version_sha1();
}

DLL_PUBLIC string Arjun::get_solver_thanks_info(const char* prefix) {
    return CMSat::SATSolver::get_thanks_info(prefix);
}

DLL_PUBLIC string Arjun::get_compilation_env() {
    return ArjunIntNS::get_compilation_env();
}

DLL_PUBLIC void Arjun::standalone_minimize_indep(SimplifiedCNF& cnf, bool all_indep) {
    Minimize common(arjdata->conf);
    common.run_minimize_indep(cnf, all_indep);
}

#ifdef SYNTH
DLL_PUBLIC void Arjun::standalone_minimize_indep_synt(SimplifiedCNF& cnf) {
    Minimize common(arjdata->conf);
    common.run_minimize_for_synth(cnf);
}
#endif

DLL_PUBLIC void Arjun::standalone_unsat_define(SimplifiedCNF& cnf) {
    Extend extend(arjdata->conf);
    extend.unsat_define(cnf);
}

DLL_PUBLIC void Arjun::standalone_extend_sampl_set(SimplifiedCNF& cnf)
{
    Extend extend(arjdata->conf);
    extend.extend_round(cnf);
}

DLL_PUBLIC SimplifiedCNF Arjun::standalone_get_simplified_cnf(
                const SimplifiedCNF& cnf, const SimpConf& simp_conf)
{
    Puura puura(arjdata->conf);
    return puura.get_fully_simplified_renumbered_cnf(cnf, simp_conf);
}
#ifdef SYNTH
DLL_PUBLIC SimplifiedCNF Arjun::standalone_manthan(const SimplifiedCNF& cnf)
{
    Manthan manthan(arjdata->conf, cnf.fg);
    return manthan.do_manthan(cnf);
}
#endif

DLL_PUBLIC void Arjun::standalone_rev_bce(SimplifiedCNF& cnf)
{
    Puura puura(arjdata->conf);
    return puura.reverse_bce(cnf);
}

DLL_PUBLIC void Arjun::standalone_unate(SimplifiedCNF& cnf)
{
    Puura puura(arjdata->conf);
    puura.synthesis_unate(cnf);
}

DLL_PUBLIC void Arjun::standalone_sbva(SimplifiedCNF& orig,
            int64_t sbva_steps, uint32_t sbva_cls_cutoff, uint32_t sbva_lits_cutoff, int sbva_tiebreak)
{
    Puura puura(arjdata->conf);
    puura.run_sbva(orig, sbva_steps, sbva_cls_cutoff, sbva_lits_cutoff, sbva_tiebreak);
}

DLL_PUBLIC void Arjun::standalone_bce(SimplifiedCNF& cnf) {
    // Unfortunately, with opt_sampling_set, we rely on a variables
    // being fully deterministic. So we can't block on them
    // otherwise we'd need to remove those variables from the opt_sampling set
    set<uint32_t> dont_block;
    for(const auto& v: cnf.get_sampl_vars()) dont_block.insert(v);
    for(const auto& v: cnf.get_opt_sampl_vars()) dont_block.insert(v);
    if (dont_block.size() == cnf.nVars()) return;

    const double start_time = cpuTime();
    vector<SimplifiedCNF::BCEClause> cls;
    vector<vector<uint32_t>> occs(cnf.nVars()*2);
    uint32_t at = 0;
    for(const auto& cl: cnf.get_clauses()) {
        // UNSAT CNF, just return the CNF
        if (cl.empty()) return;

        SimplifiedCNF::BCEClause c;
        c.lits = cl;
        c.at = at;
        c.red = false;
        cls.push_back(c);
        for(const auto& l: cl) occs[l.toInt()].push_back(at);
        assert(cl.size() > 1 && "CNF must be simplified for BCE");
        at++;
    }

    vector<uint8_t> seen;
    seen.resize(cnf.nVars()*2, 0);

    uint32_t tot_removed = 0;
    bool removed_one;
    do {
        removed_one = false;
        for(auto& cl: cls) {
            if (cl.red) continue;
            bool can_remove = false;
            for(const auto& l: cl.lits) seen[l.toInt()] = true;
            for(const auto& l: cl.lits) {
                if (dont_block.count(l.var())) continue;
                bool all_blocking = true;
                for(const auto& cl2_at: occs[(~l).toInt()]) {
                    const SimplifiedCNF::BCEClause& cl2 = cls[cl2_at];
                    if (cl2.red) continue;
                    bool found_blocking_lit = false;
                    for(const auto& l2: cl2.lits) {
                        if (l2 == ~l) continue;
                        if (seen[(~l2).toInt()]) {found_blocking_lit = true; break;}
                    }
                    if (!found_blocking_lit) {all_blocking = false; break;}
                }
                if (all_blocking) {can_remove = true; break; }
            }
            for(const auto& l: cl.lits) seen[l.toInt()] = 0;
            if (can_remove) {
                cl.red = true;
                removed_one = true;
                tot_removed++;
            }
        }
    } while(removed_one);
    cnf.replace_clauses_with(cls);

    verb_print2(1, "[arjun] BCE removed " << tot_removed << " clauses"
        " T: " << (cpuTime() - start_time));
}

DLL_PUBLIC void Arjun::standalone_backbone(SimplifiedCNF& cnf) {
    Puura puura(arjdata->conf);
    puura.backbone(cnf);
}

DLL_PUBLIC void Arjun::standalone_elim_to_file(SimplifiedCNF& cnf,
        const ElimToFileConf& etof_conf, const SimpConf& simp_conf) {
    cnf.remove_equiv_weights();
    cnf = standalone_get_simplified_cnf(cnf, simp_conf);
    cnf.remove_equiv_weights();
    auto simp_conf2 = simp_conf;
    simp_conf2.bve_grow_iter1 = 0;
    simp_conf2.bve_grow_iter2 = 0;
    simp_conf2.iter1 = 1;
    simp_conf2.iter2 = 1;
    simp_conf2.bve_too_large_resolvent = 4;
    cnf = standalone_get_simplified_cnf(cnf, simp_conf2);
    if (etof_conf.num_sbva_steps > 0)
        standalone_sbva(cnf, etof_conf.num_sbva_steps,
                etof_conf.sbva_cls_cutoff, etof_conf.sbva_lits_cutoff, etof_conf.sbva_tiebreak);
    if (etof_conf.all_indep) {
        vector<uint32_t> all_vars;
        all_vars.reserve(cnf.nVars());
        for(uint32_t i = 0; i < cnf.nVars(); i++) all_vars.push_back(i);
        cnf.set_opt_sampl_vars(all_vars);
    } else {
        if (etof_conf.do_extend_indep && cnf.get_opt_sampl_vars().size() != cnf.nVars())
            standalone_extend_sampl_set(cnf);

        // BCE shoudl be after extension, as opt_sampl_vars
        // could be smaller if BCE is run before... maybe we should try
        // reverse system, though. Would work... but then BCE would be
        // better, and opt_sampl_vars would be smaller
        if (etof_conf.do_bce) standalone_bce(cnf);
    }
    if (etof_conf.do_unate) standalone_unate(cnf);
    cnf.remove_equiv_weights();
    if (etof_conf.do_renumber) cnf.renumber_sampling_vars_for_ganak();
}

DLL_PUBLIC void SimplifiedCNF::get_bve_mapping(SimplifiedCNF& scnf, unique_ptr<CMSat::SATSolver>& solver,
        const uint32_t verb) const {
    vector<uint32_t> elimed_vars = solver->get_elimed_vars();
    const auto new_to_orig_var = get_new_to_orig_var();
    assert(defs_invariant());

    // We are all in NEW here. So we need to map back to orig, both the
    // definition and the target
    const auto map_cl_to_orig = [&new_to_orig_var](const vector<vector<CMSat::Lit>>& def) {
        vector<vector<CMSat::Lit>> ret;
        for(const auto& cl: def) {
            vector<CMSat::Lit> new_cl;
            for(const auto& l: cl) {
                assert(new_to_orig_var.count(l.var()) && "Must be in the new var set");
                const CMSat::Lit l2 = new_to_orig_var.at(l.var());
                new_cl.push_back(l2 ^ l.sign());
            }
            ret.push_back(new_cl);
        }
        return ret;
    };

    for(const auto& target: elimed_vars) {
        const auto def = solver->get_cls_defining_var(target);
        const auto orig_def = map_cl_to_orig(def);
        const auto orig_target = new_to_orig_var.at(target);
        if (orig_sampl_vars.count(orig_target.var())) {
            assert(def.empty() && "When elminating orig sampling vars, they MUST be empty, that's all we allow to be elimed");
            if (verb >= 3) cout << "c o Elimed empty sampling orig var: " << orig_target << endl;
            continue;
        }
        if (verb >= 3)
            cout << "c o [bve-aig] setting aig for orig elimed var: " << orig_target << " def size: " << def.size() << endl;

        uint32_t pos = 0;
        uint32_t neg = 0;
        for(const auto& cl: orig_def) {
            bool found_this_cl = false;
            for(const auto& l: cl) {
                if (l.var() != orig_target.var()) continue;
                found_this_cl = true;
                if (l.sign()) neg++;
                else pos++;
            }
            assert(found_this_cl);
        }
        bool sign = neg > pos;

        auto overall = scnf.aig_mng.new_const(false);
        for(const auto& cl: orig_def) {
            auto current = scnf.aig_mng.new_const(true);

            // Make sure only one side is used, the smaller side
            bool ok = false;
            for(const auto& l: cl) {
                if (l.var() == orig_target.var()) {
                    if (l.sign() == sign) ok = true;
                    break;
                }
            }
            if (!ok) continue;

            for(const auto& l: cl) {
                if (l.var() == orig_target.var()) continue;
                auto aig = AIG::new_lit(~l);
                current = AIG::new_and(current, aig);
            }
            overall = AIG::new_or(overall, current);
        }
        if (sign) overall = AIG::new_not(overall);
        if (orig_target.sign()) overall = AIG::new_not(overall);
        scnf.defs[orig_target.var()] = overall;
        if (verb >= 5)
            cout << "c o [bve-aig] set aig for var: " << orig_target << " from bve elim: " << overall << endl;
    }

    // Finally, set defs for replaced vars that are elimed
    const auto pairs = solver->get_all_binary_xors(); // [replaced, replaced_with]
    map<uint32_t, vector<CMSat::Lit>> var_to_lits_it_replaced;
    for(const auto& [orig, replacement] : pairs) {
        var_to_lits_it_replaced[replacement.var()].push_back(orig ^ replacement.sign());
    }

    // Check if any are like [... orig sampl var...] -> replaced by some non-orig sampl var
    // In these cases, we make SURE the orig sampl var is the one defining the others.
    // ->> Once we flipped it around, we need to add this new replacing var as if it was "elimed"
    //     since it's an orig var, that's fine, it can always define other vars.
    // Annoying as hell.
    vector<uint32_t> add_elimed;
    for(const auto& elimed: elimed_vars) {
        const auto orig_replacing = new_to_orig_var.at(elimed);
        if (orig_sampl_vars.count(orig_replacing.var())) continue;

        Lit bad_lit = lit_Undef;
        for(const auto& lit_replaced: var_to_lits_it_replaced[elimed]) {
            const auto orig_replaced = new_to_orig_var.at(lit_replaced.var()) ^ lit_replaced.sign();
            if (orig_sampl_vars.count(orig_replaced.var())) {
                bad_lit = lit_replaced;
                break;
            }
        }
        if (bad_lit == lit_Undef) continue;

        if (verb >= 3) cout << "c o [bve-aig] Flipping around. Offending elimed orig var: " << orig_replacing << endl;
        const vector<Lit> replaced = var_to_lits_it_replaced.at(elimed);
        var_to_lits_it_replaced.erase(elimed);
        vector<Lit> new_replaced;
        for(const auto& l: replaced) {
            if (bad_lit != l) new_replaced.push_back(l^bad_lit.sign());
        }
        new_replaced.push_back(Lit(elimed, bad_lit.sign()));
        var_to_lits_it_replaced[bad_lit.var()] = new_replaced;
        scnf.defs[elimed] = nullptr;
        add_elimed.push_back(bad_lit.var());
    }
    for(const auto& v: add_elimed) elimed_vars.push_back(v);

    for(const auto& target: elimed_vars) {
        for(const auto& lit_replaced: var_to_lits_it_replaced[target]) {
            const auto orig_replacing = new_to_orig_var.at(target);
            const auto orig_replaced = new_to_orig_var.at(lit_replaced.var()) ^ lit_replaced.sign();
            if (verb >= 3)
                cout << "c o [bve-aig] replacing var: " << orig_replaced << " with aig of " << orig_replacing << endl;
            const auto aig = scnf.defs[orig_replacing.var()];
            if (orig_sampl_vars.count(orig_replaced.var()) && orig_sampl_vars.count(orig_replacing.var())) {
                continue;
            }
            if (aig == nullptr) {
                // The orig_replacing MUST be an orig sampling var
                assert(orig_sampl_vars.count(orig_replacing.var()) &&
                    "Replaced variable must be an original sampling var here");
                scnf.defs[orig_replaced.var()] = AIG::new_lit(orig_replacing ^ orig_replaced.sign());
            } else {
                assert(!orig_sampl_vars.count(orig_replacing.var()));
                assert(aig != nullptr);
                assert(scnf.defs[orig_replaced.var()] == nullptr);
                assert(!orig_sampl_vars.count(orig_replaced.var()) &&
                    "Replaced variable cannot be in the orig sampling set here -- we would have elimed what it got replaced with");
                if (orig_replaced.sign()) scnf.defs[orig_replaced.var()] = AIG::new_not(aig);
                else scnf.defs[orig_replaced.var()] = aig;
            }
        }
    }
}

DLL_PUBLIC void SimplifiedCNF::get_fixed_values(
    SimplifiedCNF& scnf,
    unique_ptr<CMSat::SATSolver>& solver) const
{
    auto new_to_orig_var = get_new_to_orig_var();
    auto fixed = solver->get_zero_assigned_lits();
    for(const auto& l: fixed) {
        CMSat::Lit orig_lit = new_to_orig_var.at(l.var());
        orig_lit ^= l.sign();
        scnf.defs[orig_lit.var()] = scnf.aig_mng.new_const(!orig_lit.sign());
    }
}

DLL_PUBLIC void SimplifiedCNF::set_fixed_values(const vector<Lit>& lits)
{
    auto new_to_orig_var = get_new_to_orig_var();
    for(const auto& l: lits) {
        CMSat::Lit orig_lit = new_to_orig_var.at(l.var());
        orig_lit ^= l.sign();
        defs[orig_lit.var()] = aig_mng.new_const(!orig_lit.sign());
    }
}

DLL_PUBLIC void SimplifiedCNF::map_aigs_to_orig(const map<uint32_t, aig_ptr>& aigs_orig, const uint32_t max_num_vars) {
    const auto new_to_orig_var = get_new_to_orig_var();
    auto aigs = AIG::deep_clone_map(aigs_orig);
    set<aig_ptr> visited;
    function<void(const aig_ptr&)> remap_aig = [&](const aig_ptr& aig) {
        if (aig == nullptr) return;
        if (visited.count(aig)) return;

        assert(aig->invariants());
        visited.insert(aig);

        if (aig->type == AIGT::t_lit) {
            uint32_t v = aig->var;
            assert(v < max_num_vars);
            aig->var = new_to_orig_var.at(v).var();
            aig->neg ^= new_to_orig_var.at(v).sign();
            return;
        }
        if (aig->type == AIGT::t_and) {
            remap_aig(aig->l);
            remap_aig(aig->r);
            return;
        }
        if (aig->type == AIGT::t_const) return;
        assert(false && "Unknown AIG type");
        exit(EXIT_FAILURE);
    };

    for(auto& [v, aig]: aigs) remap_aig(aig);
    for(auto& [v, aig]: aigs) {
        auto l = new_to_orig_var.at(v);
        assert(defs[l.var()] == nullptr && "Variable must not already have a definition");
        assert(orig_sampl_vars.count(l.var()) == 0 && "Original sampling var cannot have definition via unsat_define or backward_round_synth");
        if (l.sign()) defs[l.var()] = AIG::new_not(aig);
        else defs[l.var()] = aig;
    }
}

DLL_PUBLIC void SimplifiedCNF::check_synth_funs_randomly() const {
    ifstream urandom("/dev/urandom", ios::in | ios::binary);
    uint64_t seed = 77;
    if (urandom) {
        urandom.read(reinterpret_cast<char*>(&seed), sizeof(seed));
        urandom.close();
    } else {
        cerr << "c o [synth-debug] could not open /dev/urandom, using default seed" << endl;
        exit(EXIT_FAILURE);
    }

    SATSolver samp_s;
    SATSolver s;
    samp_s.set_up_for_sample_counter(1000);
    samp_s.set_seed(seed);

    samp_s.new_vars(defs.size());
    s.new_vars(defs.size());
    for(const auto& cl: orig_clauses) {
        samp_s.add_clause(cl);
        s.add_clause(cl);
    }
    if (samp_s.solve() == l_False) {
        cout << "ERROR: c o [synth-debug] unsat cnf in random_check_synth_funs" << endl;
        exit(EXIT_FAILURE);
    }

    uint32_t filled_defs = 0;
    uint32_t undefs = 0;
    uint32_t num_checks = 50;
    for (uint32_t check = 0; check < num_checks; ++check) {
        auto ret = samp_s.solve();
        release_assert(ret == l_True);
        auto model = samp_s.get_model();

        // fill in samp vars
        vector<CMSat::lbool> orig_vals(defs.size(), l_Undef);
        for(const auto& l: orig_sampl_vars) orig_vals[l] = model[l];
        auto vals = orig_vals;

        map<aig_ptr, CMSat::lbool> cache;
        for(uint32_t v = 0; v < defs.size(); ++v) {
            if (orig_sampl_vars.count(v)) continue;
            if (defs[v] == nullptr) continue;

            lbool eval_aig = evaluate(orig_vals, v, cache);
            if (eval_aig == l_Undef) continue;
            /* cout << "[synth-debug] var: " << v+1 << " eval_aig: " << eval_aig << endl; */
            vals[v] = eval_aig;
            filled_defs++;
        }
        vector<Lit> assumptions;
        for(uint32_t v = 0; v < defs.size(); ++v) {
            if (vals[v] == l_Undef) {
                undefs++;
                continue;
            }
            assumptions.push_back(Lit(v, vals[v] == l_False));
        }
        auto ret2 = s.solve(&assumptions);
        release_assert(ret2 == l_True);
        /* cout << "c o [synth-debug] check " << check+1 << "/" << num_checks << " successful" << endl; */
    }
    cout << "c o [check_synth_funs_randomly] filled defs total: " << filled_defs << " undefs: " << undefs << " checks: " << num_checks << endl;
}

DLL_PUBLIC SimplifiedCNF SimplifiedCNF::get_cnf(
        unique_ptr<CMSat::SATSolver>& solver,
        const vector<uint32_t>& new_sampl_vars,
        const vector<uint32_t>& empty_sampl_vars,
        uint32_t verb
) const {
    assert(defs_invariant());

    SimplifiedCNF scnf(fg);
    vector<CMSat::Lit> clause;
    bool is_xor, rhs;
    scnf.weighted = weighted;
    scnf.proj = get_projected();
    scnf.new_vars(solver->simplified_nvars());
    scnf.aig_mng = aig_mng;
    scnf.need_aig = need_aig;
    if (need_aig) {
        scnf.defs = defs;
        scnf.aig_mng = aig_mng;
        scnf.set_orig_sampl_vars(orig_sampl_vars);
        scnf.set_orig_clauses(orig_clauses);
    }

    if (verb >= 5) {
        for(const auto& v: new_sampl_vars)
            cout << "c o [w-debug] get_cnf sampl var: " << v+1 << endl;
        for(const auto& v: opt_sampl_vars)
            cout << "c o [w-debug] get_cnf opt sampl var: " << v+1 << endl;
        for(const auto& v: empty_sampl_vars)
            cout << "c o [w-debug] get_cnf empty sampl var: " << v+1 << endl;
    }

    {// We need to fix weights here via cnf2
        auto cnf2(*this);
        cnf2.fix_weights(solver, new_sampl_vars, empty_sampl_vars);
        solver->start_getting_constraints(false, true);
        if (cnf2.weighted) {
            map<CMSat::Lit, unique_ptr<CMSat::Field>> outer_w;
            for(const auto& [v, w]: cnf2.weights) {
                const CMSat::Lit l(v, false);
                outer_w[l] = w.pos->dup();
                outer_w[~l] = w.neg->dup();
                if (verb >= 5) {
                    cout << "c o [w-debug] outer_w " << l << " w: " << *w.pos << endl;
                    cout << "c o [w-debug] outer_w " << ~l << " w: " << *w.neg << endl;
                }
            }

            const auto trans = solver->get_weight_translation();
            map<CMSat::Lit, unique_ptr<CMSat::Field>> inter_w;
            for(const auto& w: outer_w) {
                CMSat::Lit orig = w.first;
                CMSat::Lit t = trans[orig.toInt()];
                inter_w[t] = w.second->dup();
            }

            for(const auto& myw: inter_w) {
                if (myw.first.var() >= scnf.nvars) continue;
                if (verb >= 5)
                    cout << " c o [w-debug] int w: " << myw.first << " " << *myw.second << endl;
                scnf.set_lit_weight(myw.first, myw.second);
            }
        }
        *scnf.multiplier_weight = *cnf2.multiplier_weight;

        // Map orig set to new set
        scnf.set_sampl_vars(solver->translate_sampl_set(cnf2.sampl_vars));
        scnf.set_opt_sampl_vars(solver->translate_sampl_set(cnf2.opt_sampl_vars));
        sort(scnf.sampl_vars.begin(), scnf.sampl_vars.end());
        sort(scnf.opt_sampl_vars.begin(), scnf.opt_sampl_vars.end());
    }

    // Get clauses
    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        scnf.clauses.push_back(clause);
    }

    // Get fixed and BVE AIG mapping
    if (need_aig) {
        get_fixed_values(scnf, solver);
        get_bve_mapping(scnf, solver, verb);
    }
    solver->end_getting_constraints();

    // RED clauses
    solver->start_getting_constraints(true, true);
    while(solver->get_next_constraint(clause, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        scnf.red_clauses.push_back(clause);
    }
    solver->end_getting_constraints();


    if (verb >= 5) {
        cout << "w-debug AFTER PURA FINAL sampl_vars    : ";
        for(const auto& v: scnf.sampl_vars) {
            cout << v+1 << " ";
        }
        cout << endl;
        cout << "w-debug AFTER PURA FINAL opt_sampl_vars: ";
        for(const auto& v: scnf.opt_sampl_vars) cout << v+1 << " ";
        cout << endl;
    }

    // Now we do the mapping. Otherwise, above will be complicated
    // This ALSO gets all the fixed values
    scnf.orig_to_new_var = solver->update_var_mapping(orig_to_new_var);
    fix_mapping_after_renumber(scnf, verb);
    cout << "c o solver orig num vars: " << solver->nVars() << " solver simp num vars: "
        << solver->simplified_nvars() << endl;

    assert(scnf.defs_invariant());
    return scnf;
}

DLL_PUBLIC void SimplifiedCNF::fix_mapping_after_renumber(SimplifiedCNF& scnf, const uint32_t verb) const {
    cout << "c o [get-cnf] Checking for variables mapping to same new var to set AIG definitions..." << endl;
    map<uint32_t, vector<uint32_t>> new_var_to_origs;
    for(const auto& it: scnf.orig_to_new_var) {
        auto& orig = it.first;
        auto& n = it.second;
        new_var_to_origs[n.var()].push_back(orig);
    }

    for(const auto& it: new_var_to_origs) {
        const auto& origs = it.second;
        if (origs.size() <= 1) continue;

        cout << "c o [get-cnf] Found " << origs.size()
            << " original vars mapping to new var " << CMSat::Lit(it.first, false) << ": ";
        for(const auto& o: origs) cout << CMSat::Lit(o, false) << " ";
        cout << endl;

        // Find which orig to keep undefined (prefer orig_sampl_vars)
        uint32_t orig_to_keep = UINT32_MAX;
        for(const auto& o: origs) {
            if (scnf.orig_sampl_vars.count(o)) {
                orig_to_keep = o;
                break;
            }
        }
        if (orig_to_keep == UINT32_MAX) orig_to_keep = origs[0];

        cout << "c o [get-cnf] Keeping orig var " << CMSat::Lit(orig_to_keep, false)
            << " undefined, defining others by it." << endl;

        for(const auto& o: origs) {
            if (o ==  orig_to_keep) continue;
            assert(scnf.defs[o] == nullptr);
            const CMSat::Lit n = scnf.orig_to_new_var.at(o);
            const CMSat::Lit n_keep = scnf.orig_to_new_var.at(orig_to_keep);
            scnf.orig_to_new_var.erase(o);
            scnf.defs[o] = AIG::new_lit(CMSat::Lit(orig_to_keep, n.sign() ^ n_keep.sign()));
            if (verb >= 1)
                cout << "c o [get-cnf] set aig for var: " << CMSat::Lit(o, false)
                    << " to that of " << CMSat::Lit(orig_to_keep, false)
                    << " since both map to the same new var " << n << endl;
        }
    }
}

// Deserialize SimplifiedCNF from binary file
DLL_PUBLIC void SimplifiedCNF::read_aig_defs(ifstream& in) {
    // Read simple fields
    in.read((char*)&nvars, sizeof(nvars));
    in.read((char*)&backbone_done, sizeof(backbone_done));
    in.read((char*)&proj, sizeof(proj));
    in.read((char*)&need_aig, sizeof(need_aig));
    in.read((char*)&after_backward_round_synth, sizeof(after_backward_round_synth));
    in.read((char*)&weighted, sizeof(weighted));
    in.read((char*)&sampl_vars_set, sizeof(sampl_vars_set));
    in.read((char*)&opt_sampl_vars_set, sizeof(opt_sampl_vars_set));
    in.read((char*)&orig_sampl_vars_set, sizeof(orig_sampl_vars_set));

    // Read sampl_vars
    uint32_t sz;
    in.read((char*)&sz, sizeof(sz));
    sampl_vars.resize(sz);
    in.read((char*)sampl_vars.data(), sz * sizeof(uint32_t));

    // Read opt_sampl_vars
    in.read((char*)&sz, sizeof(sz));
    opt_sampl_vars.resize(sz);
    in.read((char*)opt_sampl_vars.data(), sz * sizeof(uint32_t));

    // Read orig_sampl_vars
    in.read((char*)&sz, sizeof(sz));
    vector<uint32_t> orig_sampl_vars_v(sz);
    in.read((char*)orig_sampl_vars_v.data(), sz * sizeof(uint32_t));
    orig_sampl_vars.clear();
    orig_sampl_vars.insert(orig_sampl_vars_v.begin(), orig_sampl_vars_v.end());

    // Read clauses
    in.read((char*)&sz, sizeof(sz));
    clauses.resize(sz);
    for (uint32_t i = 0; i < sz; i++) {
        uint32_t cl_sz;
        in.read((char*)&cl_sz, sizeof(cl_sz));
        clauses[i].resize(cl_sz);
        for (uint32_t j = 0; j < cl_sz; j++) {
            uint32_t v;
            bool sign;
            in.read((char*)&v, sizeof(v));
            in.read((char*)&sign, sizeof(sign));
            clauses[i][j] = CMSat::Lit(v, sign);
        }
    }

    // Read orig_clauses
    in.read((char*)&sz, sizeof(sz));
    orig_clauses.resize(sz);
    for (uint32_t i = 0; i < sz; i++) {
        uint32_t cl_sz;
        in.read((char*)&cl_sz, sizeof(cl_sz));
        orig_clauses[i].resize(cl_sz);
        for (uint32_t j = 0; j < cl_sz; j++) {
            uint32_t v;
            bool sign;
            in.read((char*)&v, sizeof(v));
            in.read((char*)&sign, sizeof(sign));
            orig_clauses[i][j] = CMSat::Lit(v, sign);
        }
    }

    // Read orig_to_new_var
    in.read((char*)&sz, sizeof(sz));
    orig_to_new_var.clear();
    for (uint32_t i = 0; i < sz; i++) {
        uint32_t orig, lit_var;
        bool lit_sign;
        in.read((char*)&orig, sizeof(orig));
        in.read((char*)&lit_var, sizeof(lit_var));
        in.read((char*)&lit_sign, sizeof(lit_sign));
        orig_to_new_var[orig] = CMSat::Lit(lit_var, lit_sign);
    }

    // Read AIGs
    uint32_t num_nodes;
    in.read((char*)&num_nodes, sizeof(num_nodes));
    cout << "c o [aig-io] Reading " << num_nodes << " AIG nodes from file." << endl;

    // Read all nodes
    vector<aig_ptr> id_to_node(num_nodes, nullptr);
    for (uint32_t i = 0; i < num_nodes; i++) {
        auto node = make_shared<AIG>();
        uint32_t id;
        in.read((char*)&id, sizeof(id));
        /* cout << "c o [aig-io] Reading AIG node id: " << id << endl; */
        in.read((char*)&node->type, sizeof(node->type));
        in.read((char*)&node->var, sizeof(node->var));
        in.read((char*)&node->neg, sizeof(node->neg));
        if (node->type == AIGT::t_and) {
            uint32_t lid, rid;
            in.read((char*)&lid, sizeof(lid));
            in.read((char*)&rid, sizeof(rid));
            assert(id_to_node[lid] != nullptr);
            assert(id_to_node[rid] != nullptr);
            node->l = id_to_node[lid];
            node->r = id_to_node[rid];
        }
        assert(id < num_nodes);
        id_to_node[id] = node;
    }

    // Read defs map
    uint32_t num_defs;
    in.read((char*)&num_defs, sizeof(num_defs));
    cout << "c o [aig-io] Reading " << num_defs << " AIG defs from file." << endl;
    defs.clear();
    defs.resize(num_defs);
    for (uint32_t i = 0; i < num_defs; i++) {
        uint32_t id;
        in.read((char*)&id, sizeof(id));
        if (id == UINT32_MAX) {
            /* cout << "c o [aig-io] Reading def for var: " << i+1 << " aig id: UNDEF" << endl; */
            defs[i] = nullptr;
            continue;
        }
        /* cout << "c o [aig-io] Reading def for var: " << i+1 << " aig id: " << id << endl; */
        assert(id < num_nodes);
        assert(id_to_node[id] != nullptr);
        assert(id_to_node.size() > id);
        assert(i < num_defs);
        defs[i] = id_to_node[id];
    }
    get_var_types(1);
}

// Serialize SimplifiedCNF to binary file
DLL_PUBLIC void SimplifiedCNF::write_aig_defs(ofstream& out) const {
    // Write simple fields
    out.write((char*)&nvars, sizeof(nvars));
    out.write((char*)&backbone_done, sizeof(backbone_done));
    out.write((char*)&proj, sizeof(proj));
    out.write((char*)&need_aig, sizeof(need_aig));
    out.write((char*)&after_backward_round_synth, sizeof(after_backward_round_synth));
    out.write((char*)&weighted, sizeof(weighted));
    out.write((char*)&sampl_vars_set, sizeof(sampl_vars_set));
    out.write((char*)&opt_sampl_vars_set, sizeof(opt_sampl_vars_set));
    out.write((char*)&orig_sampl_vars_set, sizeof(orig_sampl_vars_set));

    // Write sampl_vars
    uint32_t sz = sampl_vars.size();
    out.write((char*)&sz, sizeof(sz));
    out.write((char*)sampl_vars.data(), sz * sizeof(uint32_t));

    // Write opt_sampl_vars
    sz = opt_sampl_vars.size();
    out.write((char*)&sz, sizeof(sz));
    out.write((char*)opt_sampl_vars.data(), sz * sizeof(uint32_t));

    // Write orig_sampl_vars
    sz = orig_sampl_vars.size();
    out.write((char*)&sz, sizeof(sz));
    for(const auto& v : orig_sampl_vars) out.write((char*)&v, sizeof(v));

    // Write clauses
    sz = clauses.size();
    out.write((char*)&sz, sizeof(sz));
    for (const auto& cl : clauses) {
        uint32_t cl_sz = cl.size();
        out.write((char*)&cl_sz, sizeof(cl_sz));
        for (const auto& lit : cl) {
            uint32_t v = lit.var();
            bool sign = lit.sign();
            out.write((char*)&v, sizeof(v));
            out.write((char*)&sign, sizeof(sign));
        }
    }

    // Write orig_clauses
    sz = orig_clauses.size();
    out.write((char*)&sz, sizeof(sz));
    for (const auto& cl : orig_clauses) {
        uint32_t cl_sz = cl.size();
        out.write((char*)&cl_sz, sizeof(cl_sz));
        for (const auto& lit : cl) {
            uint32_t v = lit.var();
            bool sign = lit.sign();
            out.write((char*)&v, sizeof(v));
            out.write((char*)&sign, sizeof(sign));
        }
    }

    // Write orig_to_new_var
    sz = orig_to_new_var.size();
    out.write((char*)&sz, sizeof(sz));
    for (const auto& [orig, n] : orig_to_new_var) {
        out.write((char*)&orig, sizeof(orig));
        uint32_t lit_var = n.var();
        bool lit_sign = n.sign();
        out.write((char*)&lit_var, sizeof(lit_var));
        out.write((char*)&lit_sign, sizeof(lit_sign));
    }

    // 1. Collect all unique AIG nodes by traversing the DAG
    map<AIG*, uint32_t> node_to_id;
    map<uint32_t, AIG*> id_to_node;
    uint32_t next_id = 0;
    vector<uint32_t> order;

    function<void(const aig_ptr&)> collect = [&](const aig_ptr& aig) {
        if (!aig || node_to_id.count(aig.get())) return;
        uint32_t id = next_id++;
        node_to_id[aig.get()] = id;
        id_to_node[id] = aig.get();
        if (aig->type == AIGT::t_and) {
            collect(aig->l);
            collect(aig->r);
        }
        order.push_back(id);
        /* cout << "writing out AIG node id: " << id << " type: " << aig->type << endl; */
    };

    for (const auto& aig : defs) collect(aig);

    // 2. Write number of nodes
    uint32_t num_nodes = id_to_node.size();
    cout << "c o [aig-io] Writing " << num_nodes << " AIG nodes to file." << endl;
    out.write((char*)&num_nodes, sizeof(num_nodes));

    // 3. Write each node (postorder: children before parents)
    for (auto id : order) {
        AIG* node = id_to_node[id];
        out.write((char*)&id, sizeof(id));
        out.write((char*)&node->type, sizeof(node->type));
        out.write((char*)&node->var, sizeof(node->var));
        out.write((char*)&node->neg, sizeof(node->neg));
        if (node->type == AIGT::t_and) {
            uint32_t lid = node_to_id[node->l.get()];
            uint32_t rid = node_to_id[node->r.get()];
            out.write((char*)&lid, sizeof(lid));
            out.write((char*)&rid, sizeof(rid));
        }
    }

    // 4. Write defs map
    uint32_t num_defs = defs.size();
    out.write((char*)&num_defs, sizeof(num_defs));
    cout << "c o [aig-io] Writing " << num_defs << " AIG defs to file." << endl;
    for (const auto& aig : defs) {
        if (aig == nullptr) {
            uint32_t id = UINT32_MAX;
            /* cout << "c o [aig-io] Writing def aig id: UNDEF" << endl; */
            out.write((char*)&id, sizeof(id));
            continue;
        }
        uint32_t id = node_to_id[aig.get()];
        /* cout << "c o [aig-io] Writing def for var aig id: " << id << endl; */
        out.write((char*)&id, sizeof(id));
    }
    get_var_types(1);
}

// Write AIG defs to file (opens file for you)
DLL_PUBLIC void SimplifiedCNF::write_aig_defs_to_file(const string& fname) const {
    ofstream out(fname, ios::binary);
    if (!out) {
        cerr << "ERROR: Cannot open file for writing: " << fname << endl;
        exit(EXIT_FAILURE);
    }
    write_aig_defs(out);
    out.close();
    cout << "c o Wrote AIG defs: " << fname << endl;
}

// Read AIG defs from file (opens file for you)
DLL_PUBLIC void SimplifiedCNF::read_aig_defs_from_file(const string& fname) {
    ifstream in(fname, ios::binary);
    if (!in) {
        cerr << "ERROR: Cannot open file for reading: " << fname << endl;
        exit(EXIT_FAILURE);
    }
    read_aig_defs(in);
    in.close();
}

DLL_PUBLIC vector<CMSat::lbool> SimplifiedCNF::extend_sample(const vector<CMSat::lbool>& sample, const bool relaxed) const {
    assert(get_need_aig() && defs_invariant());
    assert(sample.size() == defs.size() && "Sample size must match number of variables");
    assert(check_orig_sampl_vars_undefined());

    for(uint32_t v = 0; v < defs.size(); v++) {
        if (orig_sampl_vars.count(v)) {
            assert(sample[v] != CMSat::l_Undef && "Original sampling variable must be defined in the sample");
        } else {
            if (!relaxed) assert(defs[v] != nullptr && "Non-original sampling variable must have definition");
            assert(sample[v] == CMSat::l_Undef && "Non-original sampling variable must be undefined in the sample");
        }
    }

    auto vals(sample);
    map<aig_ptr, CMSat::lbool> cache;
    for(uint32_t v = 0; v < defs.size(); v++) {
        if (defs[v] == nullptr) continue;
        auto val = AIG::evaluate(sample, defs[v], defs, cache);
        vals[v] = val;
    }
    return vals;
}

// Used after SBVA to replace clauses
DLL_PUBLIC void SimplifiedCNF::replace_clauses_with(vector<int>& ret, uint32_t new_nvars, uint32_t new_nclauses) {
    nvars = new_nvars;
    clauses.clear();
    vector<CMSat::Lit> cl;
    uint32_t at = 0;
    while(ret.size() > at) {
        int l = ret[at++];
        if (l == 0) {
            add_clause(cl);
            cl.clear();
            continue;
        }
        cl.push_back(CMSat::Lit(abs(l)-1, l < 0));
    }
    assert(cl.empty() && "SBVA should have ended with a 0");
    assert(clauses.size() == new_nclauses && "Number of clauses mismatch after SBVA");
}

// returns in CNF (new vars) the dependencies of each variable
// every LHS element in the map is a backward_defined variable
// input variables are NOT included in the dependencies
DLL_PUBLIC map<uint32_t, set<uint32_t>> SimplifiedCNF::compute_backw_dependencies() {
    auto [input, to_define, backward_defined] = get_var_types(0);
    auto new_to_orig_var = get_new_to_orig_var();
    map<uint32_t, set<uint32_t>> cache;
    map<uint32_t, set<uint32_t>> ret;
    for(auto& n: backward_defined) {
        const auto orig_v = new_to_orig_var.at(n).var();
        const auto ret_orig = get_dependent_vars_recursive(orig_v, cache);
        set<uint32_t> ret_new;
        for(const auto& ov: ret_orig) {
            if(!orig_to_new_var.count(ov)) continue;
            if (orig_sampl_vars.count(ov)) continue; //orig sampl vars not included
            const CMSat::Lit nl = orig_to_new_var.at(ov);
            assert(nl != CMSat::lit_Undef);
            ret_new.insert(nl.var());
        }
        ret[n] = ret_new;
    }
    return ret;
}


DLL_PUBLIC void SimplifiedCNF::fix_weights(unique_ptr<CMSat::SATSolver>& solver,
        const vector<uint32_t> new_sampl_vars,
        const vector<uint32_t>& empty_sampling_vars) {
    for(const auto& v: new_sampl_vars) check_var(v);
    for(const auto& v: empty_sampling_vars) check_var(v);
    set<uint32_t> sampling_vars_set(new_sampl_vars.begin(), new_sampl_vars.end());
    set<uint32_t> opt_sampling_vars_set(opt_sampl_vars.begin(), opt_sampl_vars.end());
    constexpr bool debug_w = false;
    if (debug_w)
        cout << __FUNCTION__ << " [w-debug] orig multiplier_weight: "
            << *multiplier_weight << endl;

    // Take units
    for(const auto& l: solver->get_zero_assigned_lits()) {
        if (l.var() >= nVars()) continue;
        if (debug_w)
            cout << __FUNCTION__ << " [w-debug] orig unit l: " << l
                << " w: " << *get_lit_weight(l) << endl;
        sampling_vars_set.erase(l.var());
        opt_sampling_vars_set.erase(l.var());
        if (get_weighted()) {
            *multiplier_weight *= *get_lit_weight(l);
            if (debug_w)
                cout << __FUNCTION__ << " [w-debug] unit: " << l
                    << " multiplier_weight: " << *multiplier_weight << endl;
            unset_var_weight(l.var());
        }
    }

    // Take bin XORs
    // [ replaced, replaced_with ]
    const auto eq_lits = solver->get_all_binary_xors();
    for(auto p: eq_lits) {
        if (p.first.var() >= nVars() || p.second.var() >= nVars()) continue;
        if (debug_w)
            cout << __FUNCTION__ << " [w-debug] repl: " << p.first
                << " with " << p.second << endl;
        if (get_weighted()) {
            auto wp2 = get_lit_weight(p.second);
            auto wn2 = get_lit_weight(~p.second);
            auto wp1 = get_lit_weight(p.first);
            auto wn1 = get_lit_weight(~p.first);
            if (debug_w) {
                cout << __FUNCTION__ << " [w-debug] wp1 " << *wp1
                    << " wn1 " << *wn1 << endl;
                cout << __FUNCTION__ << " [w-debug] wp2 " << *wp2
                    << " wn2 " << *wn2 << endl;
            }
            *wp2 *= *wp1;
            *wn2 *= *wn1;
            set_lit_weight(p.second, wp2);
            set_lit_weight(~p.second, wn2);
            if (debug_w) {
                cout << __FUNCTION__ << " [w-debug] set lit " << p.second
                    << " weight to " << *wp2 << endl;
                cout << __FUNCTION__ << " [w-debug] set lit " << ~p.second
                    << " weight to " << *wn2 << endl;
            }
            unset_var_weight(p.first.var());
        }
    }

    set_sampl_vars(sampling_vars_set, true);
    set_opt_sampl_vars(opt_sampling_vars_set);

    solver->start_getting_constraints(false);
    sampl_vars = solver->translate_sampl_set(new_sampl_vars);
    opt_sampl_vars = solver->translate_sampl_set(opt_sampl_vars);
    auto empty_sampling_vars2 = solver->translate_sampl_set(empty_sampling_vars);
    solver->end_getting_constraints();

    sampling_vars_set.clear();
    sampling_vars_set.insert(sampl_vars.begin(), sampl_vars.end());
    opt_sampling_vars_set.clear();
    opt_sampling_vars_set.insert(opt_sampl_vars.begin(), opt_sampl_vars.end());
    for(const auto& v: empty_sampling_vars2) {
        sampling_vars_set.erase(v);
        opt_sampling_vars_set.erase(v);

        if (debug_w)
            cout << __FUNCTION__ << " [w-debug] empty sampling var: " << v+1 << endl;
        auto tmp = fg->zero();
        if (get_weighted()) {
            CMSat::Lit l(v, false);
            *tmp += *get_lit_weight(l);
            *tmp += *get_lit_weight(~l);
            unset_var_weight(l.var());
        } else {
            *tmp = *fg->one();
            *tmp += *fg->one();
        }
        *multiplier_weight *= *tmp;
        if (debug_w)
            cout << __FUNCTION__ << " [w-debug] empty mul: " << *tmp
                << " final multiplier_weight: " << *multiplier_weight << endl;
    }

    set_sampl_vars(sampling_vars_set, true);
    set_opt_sampl_vars(opt_sampling_vars_set);

    for(uint32_t i = 0; i < nVars(); i++) {
        if (opt_sampling_vars_set.count(i) == 0) unset_var_weight(i);
    }

    if (debug_w) {
        cout << "w-debug FINAL sampl_vars    : ";
        for(const auto& v: sampl_vars) cout << v+1 << " ";
        cout << endl;
        cout << "w-debug FINAL opt_sampl_vars: ";
        for(const auto& v: opt_sampl_vars) {
            cout << v+1 << " ";
        }
        cout << endl;
    }
}

DLL_PUBLIC void SimplifiedCNF::renumber_sampling_vars_for_ganak() {
    assert(!need_aig && "not tested with AIGs");
    assert(sampl_vars.size() <= opt_sampl_vars.size());
    // NOTE: we do not need to update defs, because defs is ORIG to ORIG

    // Create mapping
    constexpr uint32_t m = numeric_limits<uint32_t>::max();
    vector<uint32_t> map_here_to_there(nvars, m);
    uint32_t i = 0;
    for(const auto& v: sampl_vars) {
        assert(v < nvars);
        map_here_to_there[v] = i;
        i++;
    }
    for(const auto& v: opt_sampl_vars) {
        assert(v < nvars);
        if (map_here_to_there[v] == m) {
            map_here_to_there[v] = i;
            i++;
        }
    }
    for(uint32_t x = 0; x < nvars; x++) {
        if (map_here_to_there[x] == m) {
            map_here_to_there[x] = i;
            i++;
        }
    }
    assert(i == nvars);

    // Update var map
    map<uint32_t, CMSat::Lit> upd_vmap;
    for(const auto& [o,n]: orig_to_new_var) {
        if (n != CMSat::lit_Undef) {
            CMSat::Lit l = n;
            l = CMSat::Lit(map_here_to_there[l.var()], l.sign());
            upd_vmap[o] = l;
        } else {
            upd_vmap[o] = n;
        }
    }
    orig_to_new_var = upd_vmap;

    // Now we renumber samp_vars, opt_sampl_vars, weights
    sampl_vars = map_var(sampl_vars, map_here_to_there);
    opt_sampl_vars = map_var(opt_sampl_vars, map_here_to_there);
    for(auto& cl: clauses) map_cl(cl, map_here_to_there);
    for(auto& cl: red_clauses) map_cl(cl, map_here_to_there);
    if (weighted) {
        map<uint32_t, Weight> new_weights;
        for(auto& w: weights)
            new_weights[map_here_to_there[w.first]] = w.second;
        weights = new_weights;
    } else {
        assert(weights.empty());
    }
}

DLL_PUBLIC void SimplifiedCNF::write_simpcnf(const string& fname, bool red) const {
    uint32_t num_cls = clauses.size();
    ofstream outf;
    outf.open(fname.c_str(), ios::out);
    outf << "p cnf " << nvars << " " << num_cls << endl;
    if (weighted  &&  proj) outf << "c t pwmc" << endl;
    if (weighted  && !proj) outf << "c t wmc" << endl;
    if (!weighted &&  proj) outf << "c t pmc" << endl;
    if (!weighted && !proj) outf << "c t mc" << endl;
    if (weighted) {
        for(const auto& it: weights) {
            outf << "c p weight " << CMSat::Lit(it.first,false) << " "
                << *it.second.pos << " 0" << endl;

            outf << "c p weight " << CMSat::Lit(it.first,true) << " "
                << *it.second.neg << " 0" << endl;
        }
    }

    for(const auto& cl: clauses) outf << cl << " 0\n";
    if (red) for(const auto& cl: red_clauses)
        outf << "c red " << cl << " 0\n";

    //Add projection
    outf << "c p show ";
    auto sampl = sampl_vars;
    sort(sampl.begin(), sampl.end());
    for(const auto& v: sampl) {
        assert(v < nvars);
        outf << v+1  << " ";
    }
    outf << "0\n";
    outf << "c p optshow ";
    sampl = opt_sampl_vars;
    sort(sampl.begin(), sampl.end());
    for(const auto& v: sampl) {
        assert(v < nvars);
        outf << v+1  << " ";
    }
    outf << "0\n";
    outf << "c MUST MULTIPLY BY " << *multiplier_weight << " 0" << endl;
}


// Returns NEW vars, i.e. < nVars()
// It is checked that it is correct and total
DLL_PUBLIC tuple<set<uint32_t>, set<uint32_t>, set<uint32_t>>
    SimplifiedCNF::get_var_types([[maybe_unused]] uint32_t verb) const {
    assert(need_aig);
    set<uint32_t> input;
    set<uint32_t> input_orig;
    for (const auto& v: get_orig_sampl_vars()) {
        const auto it = orig_to_new_var.find(v);
        if (it == orig_to_new_var.end()) continue;
        const uint32_t cnf_var = it->second.var();
        /* cout << "c o input var: " << v+1 << " maps to cnf var " */
        /*      << cnf_var+1 << endl; */
        assert(cnf_var < nVars());
        input.insert(cnf_var);
        input_orig.insert(v);
    }
    assert(input.size() == sampl_vars.size());
    set<uint32_t> to_define;
    set<uint32_t> to_define_orig;
    for (uint32_t v = 0; v < num_defs(); v++) {
        if (!get_orig_sampl_vars().count(v) && !defined(v)) {
            const auto it = orig_to_new_var.find(v);
            assert(it != orig_to_new_var.end() && "if it hasn't been defined, it must be in CNF");
            const uint32_t cnf_var = it->second.var();
            /* cout << "c o to_define var: " << v+1 << " maps to cnf var " */
            /*  << cnf_var+1 << endl; */
            assert(cnf_var < nVars());
            to_define.insert(cnf_var);
            to_define_orig.insert(v);
        }
    }
    set<uint32_t> unsat_defined_vars;
    set<uint32_t> unsat_defined_vars_orig;
    set<uint32_t> backw_synth_defined_vars;
    set<uint32_t> backw_synth_defined_vars_orig;
    set<uint32_t> bve_defined_vars_orig;
    set<uint32_t> forced_vars_orig;
    set<uint32_t> scc_vars_orig;
    map<uint32_t, set<uint32_t>> cache;
    for (uint32_t v = 0; v < num_defs(); v++) {
        if (get_orig_sampl_vars().count(v)) continue;
        if (!orig_to_new_var.count(v)) {
            // Eliminated already from the CNF: either BVE, SCC, or forced
            assert(defs[v] != nullptr && "if it is not in the CNF, it must be defined");
            const auto s = get_dependent_vars_recursive(v, cache);
            if (s.empty()) forced_vars_orig.insert(v);
            else if (s.size() == 1) scc_vars_orig.insert(v);
            else bve_defined_vars_orig.insert(v);
            continue;
        }

        // This var is NOT input and IS in the CNF
        if (!defined(v)) continue;
        auto s = get_dependent_vars_recursive(v, cache);
        bool only_input_deps = true;
        for(const auto& d: s) {
            if (!get_orig_sampl_vars().count(d)) {
                only_input_deps = false;
                break;
            }
        }

        const uint32_t cnf_var = orig_to_new_var.at(v).var();
        assert(cnf_var < nVars());
        if (only_input_deps) {
            unsat_defined_vars.insert(cnf_var);
            unsat_defined_vars_orig.insert(v);
        } else {
            backw_synth_defined_vars.insert(cnf_var);
            backw_synth_defined_vars_orig.insert(v);
        }
    }
    if (verb >= 1) {
        if (verb >= 2) {
            cout << "orig_to_new: ";
            for(uint32_t i = 0; i < defs.size(); i++) {
                cout << i << " -> ";
                if (orig_to_new_var.count(i) == 0)
                    cout << "UNMAP";
                else
                    cout << orig_to_new_var.at(i);

                if (defined(i)) cout << "[DEF]";
                else          cout << "[UNDEF]";
                cout << " ";
            }
            cout << endl;
        }

        cout << "c o [get-var-types] Variable types in CNF:" << endl;
        cout << "c o [get-var-types] Num input vars: " << input.size() << endl;
        cout << "c o [get-var-types]   Input vars (new) : ";
        for(const auto& v: input) cout << v+1 << " ";
        cout << endl;
        cout << "c o [get-var-types]   Input vars (orig): ";
        for(const auto& v: input_orig) cout << v+1 << " ";
        cout << endl;

        cout << "c o [get-var-types] Num to-define vars: " << to_define.size() << endl;
        cout << "c o [get-var-types]   To-define vars (new) : ";
        for(const auto& v: to_define) cout << v+1 << " ";
        cout << endl;
        cout << "c o [get-var-types]   To-define vars (orig): ";
        for(const auto& v: to_define_orig) cout << v+1 << " ";
        cout << endl;


        cout << "c o [get-var-types] Num unsat-defined vars: "
            << unsat_defined_vars.size() << endl;
        cout << "c o [get-var-types]   Unsat-defined vars (new) : ";
        for(const auto& v: unsat_defined_vars) cout << v+1 << " ";
        cout << endl;
        cout << "c o [get-var-types]   Unsat-defined vars (orig): ";
        for(const auto& v: unsat_defined_vars_orig) cout << v+1 << " ";
        cout << endl;

        cout << "c o [get-var-types] Num backward-synth-defined vars: "
            << backw_synth_defined_vars.size() << endl;
        cout << "c o [get-var-types]   Backward-synth-defined vars (new) : ";
        for(const auto& v: backw_synth_defined_vars) cout << v+1 << " ";
        cout << endl;
        cout << "c o [get-var-types]   Backward-synth-defined vars (orig): ";
        for(const auto& v: backw_synth_defined_vars_orig) cout << v+1 << " ";
        cout << endl;

        cout << "c o [get-var-types] Num bve-defined vars: "
            << bve_defined_vars_orig.size() << endl;
        cout << "c o [get-var-types]   bve-defined vars (orig): ";
        for(const auto& v: bve_defined_vars_orig) cout << v+1 << " ";
        cout << endl;

        cout << "c o [get-var-types] Num forced vars:      "
            << forced_vars_orig.size() << endl;
        cout << "c o [get-var-types]   forced vars (orig):      ";
        for(const auto& v: forced_vars_orig) cout << v+1 << " ";
        cout << endl;

        cout << "c o [get-var-types] Num SCC vars:         "
            << scc_vars_orig.size() << endl;
        cout << "c o [get-var-types]   SCC vars (orig):         ";
        for(const auto& v: scc_vars_orig) cout << v+1 << " ";
        cout << endl;

        cout << "c o [get-var-types] Total vars in ORIG CNF: " << defs.size() << endl;
        cout << "c o [get-var-types] Total vars in NEW  CNF: " << nVars() << endl;
    }
    assert(input.size() + to_define.size() + unsat_defined_vars.size() + backw_synth_defined_vars.size() == nVars());

    // unsat-defined vars can be treateed as input vars
    for(const auto& v: unsat_defined_vars) input.insert(v);
    return make_tuple(input, to_define, backw_synth_defined_vars);
}

DLL_PUBLIC CMSat::lbool SimplifiedCNF::evaluate(const vector<CMSat::lbool>& vals, uint32_t var, map<aig_ptr, CMSat::lbool>& cache) const {
    assert(var < defs.size());
    assert(vals.size() == defs.size());
    for(uint32_t i = 0; i < vals.size(); i++) {
        if (orig_sampl_vars.count(i)) {
            assert(vals[i] != CMSat::l_Undef && "Original sampling variable must be defined in the sample");
        } else {
            assert(vals[i] == CMSat::l_Undef && "Non-original sampling variable must be undefined in the sample");
        }
    }
    if (defs[var] == nullptr) {
        cout << "ERROR: Variable " << var+1 << " not defined" << endl;
        assert(defs[var] != nullptr && "Must be defined");
        exit(EXIT_FAILURE);
    }
    return AIG::evaluate(vals, defs[var], defs, cache);
}

DLL_PUBLIC bool SimplifiedCNF::check_orig_sampl_vars_undefined() const {
    for(const auto& v: orig_sampl_vars) {
        if(defs[v] == nullptr) continue;
        else if (defs[v]->type == AIGT::t_const) continue;
        else if (defs[v]->type == AIGT::t_lit) {
            assert(orig_sampl_vars.count(defs[v]->var) && "If orig_sampl_var is defined to a literal, that literal must also be an orig_sampl_var");
            continue;
        } else {
            cerr << "ERROR: Orig sampl var " << v+1
                << " cannot be defined to an AIG other than"
                " a const or a lit pointing to another orig_sampl_var, but it is: "
                << defs[v] << endl;
            assert(false);
        }
    }
    return true;
}

DLL_PUBLIC bool SimplifiedCNF::defs_invariant() const {
    check_cnf_sampl_sanity();

    if (!need_aig) return true;
    release_assert(orig_sampl_vars_set && "If need_aig, orig_sampl_vars_set must be set");
    release_assert(sampl_vars_set);
    release_assert(sampl_vars.size() <= opt_sampl_vars.size() && "We add to opt_sampl_vars via unsat_define in extend.cpp");
    release_assert(defs.size() >= nvars && "Defs size must be at least nvars, as nvars can only be smaller");

    check_orig_sampl_vars_undefined();
    check_all_opt_sampl_vars_depend_only_on_orig_sampl_vars();
    check_pre_post_backward_round_synth();
    check_all_vars_accounted_for();
    check_aig_cycles();
    check_self_dependency();
    get_var_types(0);
    check_synth_funs_randomly();
    return true;
}

// Get the orig vars this AIG depends on, recursively expanding defined vars
DLL_PUBLIC set<uint32_t> SimplifiedCNF::get_dependent_vars_recursive(const uint32_t orig_v, map<uint32_t, set<uint32_t>>& cache) const {
    assert(need_aig);
    assert(defined(orig_v));

    function<set<uint32_t>(uint32_t)> visit = [&](uint32_t v) -> set<uint32_t> {
        if (!defined(v)) return {v};
        if (cache.count(v)) return cache.at(v);

        set<uint32_t> dep;
        AIG::get_dependent_vars(defs[v], dep, v);
        set<uint32_t> final_dep;
        for (const auto& d : dep) {
            auto sub_dep = visit(d);
            final_dep.insert(sub_dep.begin(), sub_dep.end());
        }
        cache[v] = final_dep;
        return final_dep;
    };
    return visit(orig_v);
}

DLL_PUBLIC bool SimplifiedCNF::check_aig_cycles() const {
    release_assert(need_aig);

    // For cycle detection: 0 = unvisited, 1 = visiting, 2 = visited
    vector<int> state(defs.size(), 0);
    vector<uint32_t> path; // Current path for cycle reporting

    function<bool(uint32_t)> dfs = [&](uint32_t v) -> bool {
        if (state[v] == 2) return false; // Already fully visited
        if (state[v] == 1) {
            // Cycle detected!
            cout << "ERROR: Cycle detected in AIG dependencies!" << endl;
            cout << "Cycle path: ";
            bool in_cycle = false;
            for (const auto& p : path) {
                if (p == v) in_cycle = true;
                if (in_cycle) {
                    cout << p+1;
                    if (orig_to_new_var.count(p)) {
                        cout << "(CNF var " << orig_to_new_var.at(p).var()+1 << ")";
                    }
                    cout << " -> ";
                }
            }
            cout << v+1 << endl;
            return true;
        }

        if (!defined(v)) {
            state[v] = 2;
            return false;
        }

        state[v] = 1; // Mark as visiting
        path.push_back(v);

        // Get immediate dependencies from the AIG
        set<uint32_t> deps;
        AIG::get_dependent_vars(defs[v], deps, v);

        // Recursively check each dependency
        for (const auto& dep : deps) {
            if (dfs(dep)) {
                path.pop_back();
                return true;
            }
        }

        path.pop_back();
        state[v] = 2; // Mark as fully visited
        return false;
    };

    // Check all variables
    for (uint32_t v = 0; v < defs.size(); v++) {
        if (state[v] == 0 && defined(v)) {
            if (dfs(v)) {
                cout << "ERROR: Cycle found starting from variable " << v+1 << endl;
                release_assert(false && "Cycle detected in AIG dependencies");
            }
        }
    }
    return true;
}

DLL_PUBLIC void SimplifiedCNF::check_self_dependency() const {
    if (!need_aig) return;
    map<uint32_t, set<uint32_t>> cache;
    for(uint32_t orig_v = 0; orig_v < defs.size(); orig_v ++) {
        if (orig_sampl_vars.count(orig_v)) {
            if (!defined(orig_v)) continue;
            else if (defs[orig_v]->type == AIGT::t_lit) {
                release_assert(defs[orig_v]->var != orig_v && "Variable depends on itself? Also this is an orig sampl var defined to a literal that has the same var?");
                release_assert(orig_sampl_vars.count(defs[orig_v]->var) && "If orig_sampl_var is defined to a literal, that literal must also be an orig_sampl_var");
                continue;
            } else if (defs[orig_v]->type == AIGT::t_const) {
                continue;
            } else {
                cerr << "ERROR:Orig sampl var " << orig_v+1 << " cannot be defined to an AIG other than literal or const, but it is: " << defs[orig_v] << endl;
                release_assert(false);
            }
        }
        if (!defined(orig_v)) continue;

        // This checks for self-dependency
        get_dependent_vars_recursive(orig_v, cache);
    }
}

DLL_PUBLIC void SimplifiedCNF::check_cnf_vars() const {
    auto check = [](const vector<CMSat::Lit>& cl, uint32_t _nvars) {
        for(const auto& l: cl) {
            if (l.var() >= _nvars) {
                cout << "ERROR: Found a clause with a variable that has more variables than the number of variables we are supposed to have" << endl;
                cout << "cl: ";
                for(const auto& l2: cl) cout << l2 << " ";
                cout << endl;
                cout << "nvars: " << _nvars+1 << endl;
                exit(EXIT_FAILURE);
            }
            release_assert(l.var() < _nvars);
        }
    };

    // all clauses contain variables that are less than nvars
    for(const auto& cl: clauses) check(cl, nvars);
    for(const auto& cl: red_clauses) check(cl, nvars);


    // Now check orig_to_new_var covers all vars in the CNF
    if (!need_aig) return;
    set<uint32_t> vars_in_cnf;
    for(const auto& cl: clauses) {
        for(const auto& l: cl) {
            vars_in_cnf.insert(l.var());
        }
    }
    for(const auto& cl: red_clauses) {
        for(const auto& l: cl) {
            vars_in_cnf.insert(l.var());
        }
    }
    for(const auto& v: vars_in_cnf) {
        release_assert(v < nvars); // already checked above
        bool in_orig = false;
        for(const auto& [o, n]: orig_to_new_var) {
            if (n.var() == v) {
                in_orig = true;
                break;
            }
        }
        release_assert(in_orig && "All CNF vars must be in orig_to_new_var");
    }
}

// all vars are either: in orig_sampl_vars, defined, or in the cnf
DLL_PUBLIC void SimplifiedCNF::check_all_vars_accounted_for() const {
    release_assert(need_aig);
    for(uint32_t v = 0; v < defs.size(); v ++) {
        if (orig_sampl_vars.count(v)) continue; // we'll get this as input
        if (defined(v)) continue; // already defined
        if (orig_to_new_var.count(v)) continue; // appears in CNF
        cout << "ERROR: Orig var " << v+1 << " is not defined, not in orig_sampl_vars, and not in cnf" << endl;
        release_assert(false && "All vars must be accounted for");
    }
}

DLL_PUBLIC bool SimplifiedCNF::check_all_opt_sampl_vars_depend_only_on_orig_sampl_vars() const {
    release_assert(need_aig);

    // Get reverse mapping from NEW vars to ORIG vars
    const auto new_to_orig_vars = get_new_to_orig_var_list();

    // Check each sampling variable
    map<uint32_t, set<uint32_t>> cache;
    for(const auto& new_v : opt_sampl_vars) {
        release_assert(new_v < nvars);

        // Find the orig var(s) that map to this new var
        auto it = new_to_orig_vars.find(new_v);
        if (it == new_to_orig_vars.end()) {
            cout << "ERROR: Sampling variable in CNF (new: " << new_v+1
                << ") has no mapping in orig_to_new_var" << endl;
            release_assert(false && "All sampling vars must have orig mapping");
        }

        for(const auto& orig_lit : it->second) {
            const uint32_t orig_v = orig_lit.var();

            // Check if this orig var is an orig_sampl_var
            if (orig_sampl_vars.count(orig_v)) {
                // This is fine - it's an input variable
                continue;
            }

            // This orig var is NOT an orig_sampl_var
            // If it's defined, it must only depend on orig_sampl_vars
            release_assert(defined(orig_v) && "Non-orig-sampl var mapping to sampling var must be defined");
            /* if (defined(orig_v)) { */
            const auto deps = get_dependent_vars_recursive(orig_v, cache);
            bool only_orig_sampl = true;
            for(const auto& dep_v : deps) {
                if (!orig_sampl_vars.count(dep_v)) {
                    only_orig_sampl = false;
                    cout << "ERROR: Sampling variable (new: " << new_v+1
                        << ", orig: " << orig_v+1 << ") depends on non-orig-sampl var "
                        << dep_v+1 << endl;
                    cout << "  Dependencies (orig): ";
                    for(const auto& d : deps) {
                        cout << d+1 << (orig_sampl_vars.count(d) ? "(orig)" : "(NOT-orig)") << " ";
                    }
                    cout << endl;
                }
            }
            if (!only_orig_sampl) {
                release_assert(false && "All sampling variables must depend only on orig_sampl_vars");
            }
            return false;
        }
    }
    return true;
}

// this checks that NO unsat-define has been made yet
DLL_PUBLIC void SimplifiedCNF::check_pre_post_backward_round_synth() const {
    if (!need_aig) return;
    map<uint32_t, set<uint32_t>> cache;
    map<uint32_t, set<uint32_t>> dependencies;
    for(const auto& [o, n] : orig_to_new_var) {
        release_assert(o < defs.size());
        release_assert(n != CMSat::lit_Undef && n.var() < nvars);
        if (defined(o)) {
            auto s = get_dependent_vars_recursive(o, cache);
            dependencies[o] = s;
            bool only_orig_sampl = true;
            for(const auto& v: s) {
                if (!orig_sampl_vars.count(v)) {
                    only_orig_sampl = false;
                    break;
                }
            }
            if (!after_backward_round_synth && !only_orig_sampl) {
                cout << "ERROR: Found a variable in CNF, orig: " << o+1 << " new: " << n.var()+1
                    << " that is defined in terms of non-orig-sampl-vars before backward round synth.";
                cout << endl << " in old: ";
                for(const auto& v: s) cout << v+1 << "( " << (orig_sampl_vars.count(v) ? "o" : "n") << " ) ";
                cout << endl << " in new: ";
                for(const auto& v: s) {
                    auto it = orig_to_new_var.find(v);
                    if (it == orig_to_new_var.end()) cout << "undef ";
                    else cout << it->second.var()+1 << "( " << (orig_sampl_vars.count(v) ? "o" : "n") << " ) ";
                }
                cout << endl;
                release_assert(false && "Before backward round synth, variables in CNF must be defined ONLY in terms of orig_sampl_vars");
            }
        }
    }
    for(const auto& [o, dep] : dependencies) {
        release_assert(!orig_sampl_vars.count(o));
        for(const auto& v: dep) {
            // o depends on v
            if (orig_sampl_vars.count(v)) continue;
            auto it = dependencies.find(v);
            if (it == dependencies.end()) continue;
            if (it->second.count(o)) {
                // so v cannot depend on o
                cout << "ERROR: Found a dependency cycle between orig vars "
                    << o+1 << " and " << v+1 << endl;
                release_assert(false && "Dependency cycle found");
            }
        }

    }
}

DLL_PUBLIC void SimplifiedCNF::set_all_opt_indep() {
    opt_sampl_vars.clear();
    for(uint32_t i = 0; i < nvars; i++) opt_sampl_vars.push_back(i);
}

DLL_PUBLIC void SimplifiedCNF::add_opt_sampl_var(const uint32_t v) {
    assert(v < nvars);
    opt_sampl_vars.push_back(v);
}

DLL_PUBLIC void SimplifiedCNF::clean_idiotic_mccomp_weights() {
    set<uint32_t> opt_sampl_vars_s(opt_sampl_vars.begin(), opt_sampl_vars.end());
    set<uint32_t> to_remove;
    for(const auto& w: weights) {
        if (opt_sampl_vars_s.count(w.first) == 0) to_remove.insert(w.first);
    }
    if (to_remove.empty()) return;

    cout << "c o WARNING!!!! "
        << to_remove.size() << " weights removed that weren't in the (opt) sampling set" << endl;
    for(const auto& w: to_remove) weights.erase(w);
}

DLL_PUBLIC void SimplifiedCNF::check_cnf_sampl_sanity() const {
    release_assert(fg != nullptr);

    check_cnf_vars();
    set<uint32_t> sampl_vars_s(sampl_vars.begin(), sampl_vars.end());
    set<uint32_t> opt_sampl_vars_s(opt_sampl_vars.begin(), opt_sampl_vars.end());

    // sampling vars less than nvars
    for(const auto& v: opt_sampl_vars_s) {
        if (v >= nvars) {
            cout << "ERROR: Found a sampling var that is greater than the number of variables we are supposed to have" << endl;
            cout << "sampling var: " << v+1 << endl;
            cout << "nvars: " << nvars+1 << endl;
            exit(EXIT_FAILURE);
        }
        release_assert(v < nvars);
    }

    // all sampling vars are also opt sampling vars
    for(const auto& v: sampl_vars_s) {
        if (!opt_sampl_vars_s.count(v)) {
            cout << "ERROR: Found a sampling var that is not an opt sampling var: "
                << v+1 << endl;
            exit(EXIT_FAILURE);
        }
        release_assert(opt_sampl_vars_s.count(v));
    }

    // weights must be in opt sampling vars
    for(const auto& w: weights) {
        if (w.first >= nvars) {
            cout << "ERROR: Found a weight that is greater than the number of variables we are supposed to have" << endl;
            cout << "weight var: " << w.first+1 << endl;
            cout << "nvars: " << nvars+1 << endl;
            exit(EXIT_FAILURE);
        }
        release_assert(w.first < nvars);
        if (opt_sampl_vars_s.count(w.first) == 0) {
            // Idiotic but we allow 1/1 weights, even though they are useless
            if (w.second.pos->is_one() && w.second.neg->is_one()) continue;

            cout << "ERROR: Found a weight that is not an (opt) sampling var: "
                << w.first+1 << endl;
            exit(EXIT_FAILURE);
        }
        release_assert(opt_sampl_vars_s.count(w.first));
    }
}

// Gives all the orig lits that map to this variable
DLL_PUBLIC map<uint32_t, vector<CMSat::Lit>> SimplifiedCNF::get_new_to_orig_var_list() const {
    map<uint32_t, vector<CMSat::Lit>> ret;
    for(const auto& p: orig_to_new_var) {
        const CMSat::Lit l = p.second;
        if (l != CMSat::lit_Undef) {
            auto it2 = ret.find(l.var());
            if (it2 != ret.end()) ret[l.var()] = vector<CMSat::Lit>();
            ret[l.var()].push_back(CMSat::Lit(p.first, l.sign()));
        }
    }
    return ret;
}

// Gives an example lit, sometimes good enough
DLL_PUBLIC map<uint32_t, CMSat::Lit> SimplifiedCNF::get_new_to_orig_var() const {
    map<uint32_t, CMSat::Lit> ret;
    for(const auto& [origv, l]:  orig_to_new_var) {
        assert(l != CMSat::lit_Undef);
        ret[l.var()] = CMSat::Lit(origv, l.sign());
    }
    return ret;
}

DLL_PUBLIC uint32_t SimplifiedCNF::new_vars(uint32_t vars) {
    nvars+=vars;
    for(uint32_t i = 0; i < vars; i++) {
        const uint32_t v = nvars-vars+i;
        orig_to_new_var[v] = CMSat::Lit(v, false);
        if (need_aig) defs.push_back(nullptr);
    }
    return nvars;
}
DLL_PUBLIC uint32_t SimplifiedCNF::new_var() {
    uint32_t v = nvars;
    nvars++;
    orig_to_new_var[v] = CMSat::Lit(v, false);
    if (need_aig) defs.push_back(nullptr);
    return nvars;
}

DLL_PUBLIC void SimplifiedCNF::start_with_clean_sampl_vars() {
    assert(sampl_vars.empty());
    assert(opt_sampl_vars.empty());
    for(uint32_t i = 0; i < nvars; i++) sampl_vars.push_back(i);
    for(uint32_t i = 0; i < nvars; i++) opt_sampl_vars.push_back(i);
}

DLL_PUBLIC void SimplifiedCNF::check_var(const uint32_t v) const {
    if (v >= nVars()) {
        cout << "ERROR: Tried to access a variable that is too large" << endl;
        cout << "var: " << v+1 << endl;
        cout << "nvars: " << nVars() << endl;
        release_assert(v < nVars());
        exit(EXIT_FAILURE);
    }
}

DLL_PUBLIC void SimplifiedCNF::check_clause(const vector<CMSat::Lit>& cl) const {
    for(const auto& l: cl) check_var(l.var());
}

DLL_PUBLIC void SimplifiedCNF::clear_orig_sampl_defs() {
    for(const auto& v: orig_sampl_vars) defs[v] = nullptr;
}

DLL_PUBLIC void SimplifiedCNF::simplify_aigs() {
    set<aig_ptr> visited;
    for(auto& aig: defs) {
        aig = AIG::simplify(aig, visited);
    }
}

DLL_PUBLIC  aig_ptr AIG::simplify(aig_ptr aig, set<aig_ptr>& visited) {
    if (!aig) return nullptr;
    if (visited.count(aig)) return aig;
    visited.insert(aig);

    if (aig->type == AIGT::t_and) {
        auto l_simp = simplify(aig->l, visited);
        auto r_simp = simplify(aig->r, visited);
        // AND simplifications
        if (aig->neg) {
            if (l_simp->type == AIGT::t_const && r_simp->type == AIGT::t_const) {
                if (l_simp->neg || r_simp->neg) {
                    // !(FALSE & X) = TRUE
                    // !(X & FALSE) = TRUE
                    auto c_t = make_shared<AIG>();
                    c_t->type = AIGT::t_const;
                    c_t->neg = false;
                    return c_t;
                } else {
                    // !(TRUE & TRUE) = FALSE
                    auto c_f = make_shared<AIG>();
                    c_f->type = AIGT::t_const;
                    c_f->neg = true;
                    return c_f;
                }
            } else if (l_simp->type == AIGT::t_const && l_simp->neg == false) { // ~(TRUE & X) = !X
                auto c_f = make_shared<AIG>();
                c_f->type = r_simp->type;
                c_f->neg = !r_simp->neg;
                c_f->var = r_simp->var;
                c_f->l = r_simp->l;
                c_f->r = r_simp->r;
                return c_f;
            } else if (r_simp->type == AIGT::t_const && r_simp->neg == false) { // ~(X & TRUE) = !X
                auto c_f = make_shared<AIG>();
                c_f->type = l_simp->type;
                c_f->neg = !l_simp->neg;
                c_f->var = l_simp->var;
                c_f->l = l_simp->l;
                c_f->r = l_simp->r;
                return c_f;
            } else {
                aig->l = l_simp;
                aig->r = r_simp;
                return aig;
            }
        } else {
            if (l_simp->type == AIGT::t_const) {
                if (!l_simp->neg) return r_simp; // TRUE & X = X
                else return l_simp;              // FALSE & X = FALSE
            } else if (r_simp->type == AIGT::t_const) {
                if (!r_simp->neg) return l_simp; // X & TRUE = X
                else return r_simp;              // X & FALSE = FALSE
            } else if (l_simp == r_simp) {
                return l_simp;                   // X & X = X
            } else if (l_simp->type == AIGT::t_lit && r_simp->type == AIGT::t_lit &&
                       l_simp->var == r_simp->var &&
                       l_simp->neg == r_simp->neg) {
                return l_simp;
            } else {
                aig->l = l_simp;
                aig->r = r_simp;
                return aig;
            }
        }
    }
    return aig;
}


set_get_macro(bool, distill)
set_get_macro(bool, intree)
set_get_macro(bool, bve_pre_simplify)
set_get_macro(int, simp)
set_get_macro(uint32_t, incidence_count)
set_get_macro(bool, or_gate_based)
set_get_macro(bool, xor_gates_based)
set_get_macro(bool, probe_based)
set_get_macro(uint32_t, backw_max_confl)
set_get_macro(bool, gauss_jordan)
set_get_macro(bool, ite_gate_based)
set_get_macro(bool, irreg_gate_based)
set_get_macro(double, no_gates_below)
set_get_macro(string, specified_order_fname)
set_get_macro(uint32_t, verb)
set_get_macro(uint32_t, extend_max_confl)
set_get_macro(int, oracle_find_bins)
set_get_macro(int, num_samples)
set_get_macro(double, cms_glob_mult)
set_get_macro(int, extend_ccnr)
set_get_macro(int, autarkies)
