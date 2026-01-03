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
#include <sbva/sbva.h>
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
    std::stringstream ss;
    ss << prefix << "Using ideas by JM Lagniez, and Pierre Marquis" << endl;
    ss << prefix << "    from paper 'Improving Model Counting [..] IJCAI 2016";
    return ss.str();
}

DLL_PUBLIC std::string Arjun::get_solver_version_sha1() {
    return CMSat::SATSolver::get_version_sha1();
}

DLL_PUBLIC std::string Arjun::get_solver_thanks_info(const char* prefix) {
    return CMSat::SATSolver::get_thanks_info(prefix);
}

DLL_PUBLIC std::string Arjun::get_compilation_env() {
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

DLL_PUBLIC void SimplifiedCNF::get_bve_mapping(SimplifiedCNF& scnf, std::unique_ptr<CMSat::SATSolver>& solver,
            const uint32_t verb) const {
        std::vector<uint32_t> vs = solver->get_elimed_vars();
        const auto new_to_orig_var = get_new_to_orig_var();
        assert(defs_invariant());

        // We are all in NEW here. So we need to map back to orig, both the
        // definition and the target
        auto map_cl_to_orig = [&new_to_orig_var](const std::vector<std::vector<CMSat::Lit>>& def) {
            std::vector<std::vector<CMSat::Lit>> ret;
            for(const auto& cl: def) {
                std::vector<CMSat::Lit> new_cl;
                for(const auto& l: cl) {
                    assert(new_to_orig_var.count(l.var()) && "Must be in the new var set");
                    const CMSat::Lit l2 = new_to_orig_var.at(l.var());
                    new_cl.push_back(l2 ^ l.sign());
                }
                ret.push_back(new_cl);
            }
            return ret;
        };

        for(const auto& target: vs) {
            auto def = solver->get_cls_defining_var(target);
            auto orig_def = map_cl_to_orig(def);
            auto orig_target = new_to_orig_var.at(target);
            assert(scnf.get_orig_sampl_vars().count(orig_target.var()) == 0 &&
                "Elimed variable cannot be in the orig sampling set");

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
                std::cout << "c o [bve-aig] set aig for var: " << orig_target << " from bve elim" << std::endl;
        }

        // Finally, set defs for replaced vars that are elimed
        auto pairs = solver->get_all_binary_xors(); // [replaced, replaced_with]
        std::map<uint32_t, std::vector<CMSat::Lit>> var_to_lits_it_replaced;
        for(const auto& [orig, replacement] : pairs) {
            var_to_lits_it_replaced[replacement.var()].push_back(orig ^ replacement.sign());
        }
        for(const auto& target: vs) {
            for(const auto& l: var_to_lits_it_replaced[target]) {
                auto orig_target = new_to_orig_var.at(target);
                auto orig_lit = new_to_orig_var.at(l.var()) ^ l.sign();
                const auto aig = scnf.defs[orig_target.var()];
                assert(aig != nullptr);
                assert(scnf.defs[orig_lit.var()] == nullptr);
                assert(scnf.get_orig_sampl_vars().count(orig_lit.var()) == 0 &&
                    "Replaced variable cannot be in the orig sampling set here -- we would have elimed what it got replaced with");
                if (orig_lit.sign()) {
                    scnf.defs[orig_lit.var()] = AIG::new_not(aig);
                } else {
                    scnf.defs[orig_lit.var()] = aig;
                }
                if (verb >= 5)
                    std::cout << "c o [bve-aig] replaced var: " << orig_lit
                        << " with aig of " << orig_target << std::endl;
            }
        }
    }

    DLL_PUBLIC void SimplifiedCNF::get_fixed_values(
        SimplifiedCNF& scnf,
        std::unique_ptr<CMSat::SATSolver>& solver) const
    {
        auto new_to_orig_var = get_new_to_orig_var();
        auto fixed = solver->get_zero_assigned_lits();
        for(const auto& l: fixed) {
            CMSat::Lit orig_lit = new_to_orig_var.at(l.var());
            orig_lit ^= l.sign();
            scnf.defs[orig_lit.var()] = scnf.aig_mng.new_const(!orig_lit.sign());
        }
    }

    DLL_PUBLIC void SimplifiedCNF::map_aigs_to_orig(std::map<uint32_t, std::shared_ptr<AIG>>& aigs, uint32_t max_num_vars) {
        const auto new_to_orig_var = get_new_to_orig_var();
        std::function<void(const aig_ptr&)> remap_aig = [&](const aig_ptr& aig) {
            if (aig == nullptr) return;
            if (aig->marked()) return;
            assert(aig->invariants());
            aig->set_mark();

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

        for(auto& [v, aig]: aigs) AIG::unmark_all(aig);
        for(auto& [v, aig]: aigs) remap_aig(aig);
        for(auto& [v, aig]: aigs) {
            auto l = new_to_orig_var.at(v);
            assert(defs[l.var()] == nullptr && "Variable must not already have a definition");
            assert(orig_sampl_vars.count(l.var()) == 0 && "Original sampling var cannot have definition via unsat_define or backward_round_synth");
            if (l.sign()) defs[l.var()] = AIG::new_not(aig);
            else defs[l.var()] = aig;
        }
    }

    DLL_PUBLIC void SimplifiedCNF::random_check_synth_funs() const {
        std::ifstream urandom("/dev/urandom", std::ios::in | std::ios::binary);
        uint64_t seed = 77;
        if (urandom) {
            urandom.read(reinterpret_cast<char*>(&seed), sizeof(seed));
            urandom.close();
        } else {
            std::cerr << "c o [synth-debug] could not open /dev/urandom, using default seed" << std::endl;
        }

        SATSolver samp_s;
        SATSolver s;
        samp_s.set_up_for_sample_counter(100);
        samp_s.set_seed(seed);

        samp_s.new_vars(defs.size());
        s.new_vars(defs.size());
        for(const auto& cl: orig_clauses) {
            samp_s.add_clause(cl);
            s.add_clause(cl);
        }
        if (samp_s.solve() == l_False) {
            std::cout << "ERROR: c o [synth-debug] unsat cnf in random_check_synth_funs" << std::endl;
            exit(EXIT_FAILURE);
        }

        uint32_t filled_defs = 0;
        uint32_t undefs = 0;
        for (uint32_t check = 0; check < 10; ++check) {
            auto ret = samp_s.solve();
            assert(ret == l_True);
            auto model = samp_s.get_model();

            // fill in samp vars
            vector<CMSat::lbool> orig_vals(defs.size(), l_Undef);
            for(const auto& l: orig_sampl_vars) orig_vals[l] = model[l];
            auto vals = orig_vals;

            for(uint32_t v = 0; v < defs.size(); ++v) {
                if (orig_sampl_vars.count(v)) continue;
                if (defs[v] == nullptr) continue;

                lbool eval_aig = evaluate(orig_vals, v);
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
            assert(ret2 == l_True);
        }
        cout << "[CHECK] filled defs total: " << filled_defs << " undefs: " << undefs << " checks: " << 100 << endl;
    }

    DLL_PUBLIC SimplifiedCNF SimplifiedCNF::get_cnf(
            std::unique_ptr<CMSat::SATSolver>& solver,
            const std::vector<uint32_t>& new_sampl_vars,
            const std::vector<uint32_t>& empty_sampl_vars,
            uint32_t verb
    ) const {
        assert(defs_invariant());

        SimplifiedCNF scnf(fg);
        std::vector<CMSat::Lit> clause;
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
                std::cout << "c o [w-debug] get_cnf sampl var: " << v+1 << std::endl;
            for(const auto& v: opt_sampl_vars)
                std::cout << "c o [w-debug] get_cnf opt sampl var: " << v+1 << std::endl;
            for(const auto& v: empty_sampl_vars)
                std::cout << "c o [w-debug] get_cnf empty sampl var: " << v+1 << std::endl;
        }

        {// We need to fix weights here via cnf2
            auto cnf2(*this);
            cnf2.fix_weights(solver, new_sampl_vars, empty_sampl_vars);
            solver->start_getting_constraints(false, true);
            if (cnf2.weighted) {
                std::map<CMSat::Lit, std::unique_ptr<CMSat::Field>> outer_w;
                for(const auto& [v, w]: cnf2.weights) {
                    const CMSat::Lit l(v, false);
                    outer_w[l] = w.pos->dup();
                    outer_w[~l] = w.neg->dup();
                    if (verb >= 5) {
                        std::cout << "c o [w-debug] outer_w " << l << " w: " << *w.pos << std::endl;
                        std::cout << "c o [w-debug] outer_w " << ~l << " w: " << *w.neg << std::endl;
                    }
                }

                const auto trans = solver->get_weight_translation();
                std::map<CMSat::Lit, std::unique_ptr<CMSat::Field>> inter_w;
                for(const auto& w: outer_w) {
                    CMSat::Lit orig = w.first;
                    CMSat::Lit t = trans[orig.toInt()];
                    inter_w[t] = w.second->dup();
                }

                for(const auto& myw: inter_w) {
                    if (myw.first.var() >= scnf.nvars) continue;
                    if (verb >= 5)
                        std::cout << " c o [w-debug] int w: " << myw.first << " " << *myw.second << std::endl;
                    scnf.set_lit_weight(myw.first, myw.second);
                }
            }
            *scnf.multiplier_weight = *cnf2.multiplier_weight;

            // Map orig set to new set
            scnf.set_sampl_vars(solver->translate_sampl_set(cnf2.sampl_vars));
            scnf.set_opt_sampl_vars(solver->translate_sampl_set(cnf2.opt_sampl_vars));
            std::sort(scnf.sampl_vars.begin(), scnf.sampl_vars.end());
            std::sort(scnf.opt_sampl_vars.begin(), scnf.opt_sampl_vars.end());
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
            std::cout << "w-debug AFTER PURA FINAL sampl_vars    : ";
            for(const auto& v: scnf.sampl_vars) {
                std::cout << v+1 << " ";
            }
            std::cout << std::endl;
            std::cout << "w-debug AFTER PURA FINAL opt_sampl_vars: ";
            for(const auto& v: scnf.opt_sampl_vars) std::cout << v+1 << " ";
            std::cout << std::endl;
        }

        // Now we do the mapping. Otherwise, above will be complicated
        // This ALSO gets all the fixed values
        scnf.orig_to_new_var = solver->update_var_mapping(orig_to_new_var);
        fix_mapping_after_renumber(scnf, verb);
        std::cout << "c o solver orig num vars: " << solver->nVars() << " solver simp num vars: "
            << solver->simplified_nvars() << std::endl;

        assert(scnf.defs_invariant());
        return scnf;
    }

    DLL_PUBLIC void SimplifiedCNF::fix_mapping_after_renumber(SimplifiedCNF& scnf, const uint32_t verb) const {
        std::cout << "c o [get-cnf] Checking for variables mapping to same new var to set AIG definitions..." << std::endl;
        std::map<uint32_t, std::vector<uint32_t>> new_var_to_origs;
        for(const auto& it: scnf.orig_to_new_var) {
            auto& orig = it.first;
            auto& n = it.second;
            new_var_to_origs[n.var()].push_back(orig);
        }

        for(const auto& it: new_var_to_origs) {
            const auto& origs = it.second;
            if (origs.size() <= 1) continue;

            std::cout << "c o [get-cnf] Found " << origs.size()
                << " original vars mapping to new var " << CMSat::Lit(it.first, false) << ": ";
            for(const auto& o: origs) std::cout << CMSat::Lit(o, false) << " ";
            std::cout << std::endl;

            // Find which orig to keep undefined (prefer orig_sampl_vars)
            uint32_t orig_to_keep = UINT32_MAX;
            for(const auto& o: origs) {
                if (scnf.orig_sampl_vars.count(o)) {
                    orig_to_keep = o;
                    break;
                }
            }
            if (orig_to_keep == UINT32_MAX) orig_to_keep = origs[0];

            std::cout << "c o [get-cnf] Keeping orig var " << CMSat::Lit(orig_to_keep, false)
                << " undefined, defining others by it." << std::endl;

            for(const auto& o: origs) {
                if (o ==  orig_to_keep) continue;
                assert(scnf.defs[o] == nullptr);
                const CMSat::Lit n = scnf.orig_to_new_var.at(o);
                const CMSat::Lit n_keep = scnf.orig_to_new_var.at(orig_to_keep);
                scnf.orig_to_new_var.erase(o);
                scnf.defs[o] = AIG::new_lit(CMSat::Lit(orig_to_keep, n.sign() ^ n_keep.sign()));
                if (verb >= 1)
                    std::cout << "c o [get-cnf] set aig for var: " << CMSat::Lit(o, false)
                        << " to that of " << CMSat::Lit(orig_to_keep, false)
                        << " since both map to the same new var " << n << std::endl;
            }
        }
    }

    // Deserialize SimplifiedCNF from binary file
    DLL_PUBLIC void SimplifiedCNF::read_aig_defs(std::ifstream& in) {
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
        std::vector<aig_ptr> id_to_node(num_nodes, nullptr);
        for (uint32_t i = 0; i < num_nodes; i++) {
            auto node = std::make_shared<AIG>();
            uint32_t id;
            in.read((char*)&id, sizeof(id));
            cout << "c o [aig-io] Reading AIG node id: " << id << endl;
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
                cout << "c o [aig-io] Reading def for var: " << i+1 << " aig id: UNDEF" << endl;
                defs[i] = nullptr;
                continue;
            }
            cout << "c o [aig-io] Reading def for var: " << i+1 << " aig id: " << id << endl;
            assert(id < num_nodes);
            assert(id_to_node[id] != nullptr);
            assert(id_to_node.size() > id);
            assert(i < num_defs);
            defs[i] = id_to_node[id];
        }
        get_var_types(1);
    }


    // Serialize SimplifiedCNF to binary file
    DLL_PUBLIC void SimplifiedCNF::write_aig_defs(std::ofstream& out) const {
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
        std::map<AIG*, uint32_t> node_to_id;
        std::map<uint32_t, AIG*> id_to_node;
        uint32_t next_id = 0;
        std::vector<uint32_t> order;

        std::function<void(const aig_ptr&)> collect = [&](const aig_ptr& aig) {
            if (!aig || node_to_id.count(aig.get())) return;
            uint32_t id = next_id++;
            node_to_id[aig.get()] = id;
            id_to_node[id] = aig.get();
            if (aig->type == AIGT::t_and) {
                collect(aig->l);
                collect(aig->r);
            }
            order.push_back(id);
            cout << "writing out AIG node id: " << id << " type: " << aig->type << endl;
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
                cout << "c o [aig-io] Writing def aig id: UNDEF" << endl;
                out.write((char*)&id, sizeof(id));
                continue;
            }
            uint32_t id = node_to_id[aig.get()];
            cout << "c o [aig-io] Writing def for var aig id: " << id << endl;
            out.write((char*)&id, sizeof(id));
        }
        get_var_types(1);
    }


    // Write AIG defs to file (opens file for you)
    DLL_PUBLIC void SimplifiedCNF::write_aig_defs_to_file(const std::string& fname) const {
        std::ofstream out(fname, std::ios::binary);
        if (!out) {
            std::cerr << "ERROR: Cannot open file for writing: " << fname << std::endl;
            exit(EXIT_FAILURE);
        }
        write_aig_defs(out);
        out.close();
        std::cout << "c o Wrote AIG defs: " << fname << std::endl;
    }

    // Read AIG defs from file (opens file for you)
    DLL_PUBLIC void SimplifiedCNF::read_aig_defs_from_file(const std::string& fname) {
        std::ifstream in(fname, std::ios::binary);
        if (!in) {
            std::cerr << "ERROR: Cannot open file for reading: " << fname << std::endl;
            exit(EXIT_FAILURE);
        }
        read_aig_defs(in);
        in.close();
    }

    DLL_PUBLIC std::vector<CMSat::lbool> SimplifiedCNF::extend_sample(const std::vector<CMSat::lbool>& sample) const {
        assert(get_need_aig() && defs_invariant());
        assert(sample.size() == defs.size() && "Sample size must match number of variables");

        for(uint32_t v = 0; v < defs.size(); v++) {
            if (orig_sampl_vars.count(v)) {
                assert(defs[v] == nullptr && "Original sampling variable cannot have definition");
                assert(sample[v] != CMSat::l_Undef && "Original sampling variable must be defined in the sample");

            } else {
                assert(defs[v] != nullptr && "Non-original sampling variable must have definition");
                assert(sample[v] == CMSat::l_Undef && "Non-original sampling variable must be undefined in the sample");
            }
        }

        auto vals(sample);
        for(uint32_t v = 0; v < defs.size(); v++) {
            if (defs[v] == nullptr) continue;
            auto val = AIG::evaluate(sample, defs[v], defs);
            vals[v] = val;
        }
        return vals;
    }

    // Used after SBVA to replace clauses
    DLL_PUBLIC void SimplifiedCNF::replace_clauses_with(std::vector<int>& ret, uint32_t new_nvars, uint32_t new_nclauses) {
        nvars = new_nvars;
        clauses.clear();
        std::vector<CMSat::Lit> cl;
        uint32_t at = 0;
        while(ret.size() > at) {
            int l = ret[at++];
            if (l == 0) {
                add_clause(cl);
                cl.clear();
                continue;
            }
            cl.push_back(CMSat::Lit(std::abs(l)-1, l < 0));
        }
        assert(cl.empty() && "SBVA should have ended with a 0");
        assert(clauses.size() == new_nclauses && "Number of clauses mismatch after SBVA");
    }

    // returns in CNF (new vars) the dependencies of each variable
    // every LHS element in the map is a backward_defined variable
    DLL_PUBLIC std::map<uint32_t, std::set<uint32_t>> SimplifiedCNF::compute_backw_dependencies() {
        std::map<uint32_t, std::set<uint32_t>> ret;
        for(uint32_t orig_v = 0; orig_v < defs.size(); orig_v ++) {
            // Skip orig sampl vars
            if (orig_sampl_vars.count(orig_v)) continue; // if orig_sampl_var, skip
            if (!defined(orig_v)) continue; // if undefined, skip
            if (orig_to_new_var.count(orig_v) == 0) continue; // if NOT mapped to CNF, skip
            const CMSat::Lit n = orig_to_new_var.at(orig_v);
            assert(n != CMSat::lit_Undef);

            // var n IS backward_defined
            auto ret_orig = get_dependent_vars_recursive(defs[orig_v], orig_v);
            std::set<uint32_t> ret_new;
            for(const auto& ov: ret_orig) {
                if(!orig_to_new_var.count(ov)) continue;
                if (orig_sampl_vars.count(ov)) continue; //orig sampl vars not included
                const CMSat::Lit nl = orig_to_new_var.at(ov);
                assert(nl != CMSat::lit_Undef);
                ret_new.insert(nl.var());
            }
            if (ret_new.empty()) continue; //unsat defined
            ret[n.var()] = ret_new;
        }
        return ret;
    }


    DLL_PUBLIC void SimplifiedCNF::fix_weights(std::unique_ptr<CMSat::SATSolver>& solver,
            const std::vector<uint32_t> new_sampl_vars,
            const std::vector<uint32_t>& empty_sampling_vars) {
        for(const auto& v: new_sampl_vars) check_var(v);
        for(const auto& v: empty_sampling_vars) check_var(v);
        std::set<uint32_t> sampling_vars_set(new_sampl_vars.begin(), new_sampl_vars.end());
        std::set<uint32_t> opt_sampling_vars_set(opt_sampl_vars.begin(), opt_sampl_vars.end());
        constexpr bool debug_w = false;
        if (debug_w)
            std::cout << __FUNCTION__ << " [w-debug] orig multiplier_weight: "
                << *multiplier_weight << std::endl;

        // Take units
        for(const auto& l: solver->get_zero_assigned_lits()) {
            if (l.var() >= nVars()) continue;
            if (debug_w)
                std::cout << __FUNCTION__ << " [w-debug] orig unit l: " << l
                    << " w: " << *get_lit_weight(l) << std::endl;
            sampling_vars_set.erase(l.var());
            opt_sampling_vars_set.erase(l.var());
            if (get_weighted()) {
                *multiplier_weight *= *get_lit_weight(l);
                if (debug_w)
                    std::cout << __FUNCTION__ << " [w-debug] unit: " << l
                        << " multiplier_weight: " << *multiplier_weight << std::endl;
                unset_var_weight(l.var());
            }
        }

        // Take bin XORs
        // [ replaced, replaced_with ]
        const auto eq_lits = solver->get_all_binary_xors();
        for(auto p: eq_lits) {
            if (p.first.var() >= nVars() || p.second.var() >= nVars()) continue;
            if (debug_w)
                std::cout << __FUNCTION__ << " [w-debug] repl: " << p.first
                    << " with " << p.second << std::endl;
            if (get_weighted()) {
                auto wp2 = get_lit_weight(p.second);
                auto wn2 = get_lit_weight(~p.second);
                auto wp1 = get_lit_weight(p.first);
                auto wn1 = get_lit_weight(~p.first);
                if (debug_w) {
                    std::cout << __FUNCTION__ << " [w-debug] wp1 " << *wp1
                        << " wn1 " << *wn1 << std::endl;
                    std::cout << __FUNCTION__ << " [w-debug] wp2 " << *wp2
                        << " wn2 " << *wn2 << std::endl;
                }
                *wp2 *= *wp1;
                *wn2 *= *wn1;
                set_lit_weight(p.second, wp2);
                set_lit_weight(~p.second, wn2);
                if (debug_w) {
                    std::cout << __FUNCTION__ << " [w-debug] set lit " << p.second
                        << " weight to " << *wp2 << std::endl;
                    std::cout << __FUNCTION__ << " [w-debug] set lit " << ~p.second
                        << " weight to " << *wn2 << std::endl;
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
                std::cout << __FUNCTION__ << " [w-debug] empty sampling var: " << v+1 << std::endl;
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
                std::cout << __FUNCTION__ << " [w-debug] empty mul: " << *tmp
                    << " final multiplier_weight: " << *multiplier_weight << std::endl;
        }

        set_sampl_vars(sampling_vars_set, true);
        set_opt_sampl_vars(opt_sampling_vars_set);

        for(uint32_t i = 0; i < nVars(); i++) {
            if (opt_sampling_vars_set.count(i) == 0) unset_var_weight(i);
        }

        if (debug_w) {
            std::cout << "w-debug FINAL sampl_vars    : ";
            for(const auto& v: sampl_vars) std::cout << v+1 << " ";
            std::cout << std::endl;
            std::cout << "w-debug FINAL opt_sampl_vars: ";
            for(const auto& v: opt_sampl_vars) {
                std::cout << v+1 << " ";
            }
            std::cout << std::endl;
        }
    }

    DLL_PUBLIC bool SimplifiedCNF::aig_contains(const aig_ptr& aig, const uint32_t v) const {
        check_var(v);
        if (aig == nullptr) return false;
        assert(aig->invariants());
        if (aig->type == AIGT::t_lit) {
            if (aig->var == v) return true;

            /// Need to be recursive
            if (defs[aig->var] != nullptr) {
                const auto& aig2 = defs[aig->var];
                return aig_contains(aig2, v);
            }
            return false;
        }
        if (aig->type == AIGT::t_const) return false;
        if (aig->type == AIGT::t_and) {
            return aig_contains(aig->l, v) || aig_contains(aig->r, v);
        }
        assert(false && "Unknown AIG type");
        exit(EXIT_FAILURE);
    }


    DLL_PUBLIC void SimplifiedCNF::renumber_sampling_vars_for_ganak() {
        assert(sampl_vars.size() <= opt_sampl_vars.size());
        // NOTE: we do not need to update defs, because defs is ORIG to ORIG

        // Create mapping
        constexpr uint32_t m = std::numeric_limits<uint32_t>::max();
        std::vector<uint32_t> map_here_to_there(nvars, m);
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
        std::map<uint32_t, CMSat::Lit> upd_vmap;
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
            std::map<uint32_t, Weight> new_weights;
            for(auto& w: weights)
                new_weights[map_here_to_there[w.first]] = w.second;
            weights = new_weights;
        } else {
            assert(weights.empty());
        }
    }

    DLL_PUBLIC void SimplifiedCNF::write_simpcnf(const std::string& fname, bool red) const {
        uint32_t num_cls = clauses.size();
        std::ofstream outf;
        outf.open(fname.c_str(), std::ios::out);
        outf << "p cnf " << nvars << " " << num_cls << std::endl;
        if (weighted  &&  proj) outf << "c t pwmc" << std::endl;
        if (weighted  && !proj) outf << "c t wmc" << std::endl;
        if (!weighted &&  proj) outf << "c t pmc" << std::endl;
        if (!weighted && !proj) outf << "c t mc" << std::endl;
        if (weighted) {
            for(const auto& it: weights) {
                outf << "c p weight " << CMSat::Lit(it.first,false) << " "
                    << *it.second.pos << " 0" << std::endl;

                outf << "c p weight " << CMSat::Lit(it.first,true) << " "
                    << *it.second.neg << " 0" << std::endl;
            }
        }

        for(const auto& cl: clauses) outf << cl << " 0\n";
        if (red) for(const auto& cl: red_clauses)
            outf << "c red " << cl << " 0\n";

        //Add projection
        outf << "c p show ";
        auto sampl = sampl_vars;
        std::sort(sampl.begin(), sampl.end());
        for(const auto& v: sampl) {
            assert(v < nvars);
            outf << v+1  << " ";
        }
        outf << "0\n";
        outf << "c p optshow ";
        sampl = opt_sampl_vars;
        std::sort(sampl.begin(), sampl.end());
        for(const auto& v: sampl) {
            assert(v < nvars);
            outf << v+1  << " ";
        }
        outf << "0\n";
        outf << "c MUST MULTIPLY BY " << *multiplier_weight << " 0" << std::endl;
    }


    // Returns NEW vars, i.e. < nVars()
    // It is checked that it is correct and total
    DLL_PUBLIC std::tuple<std::set<uint32_t>, std::set<uint32_t>, std::set<uint32_t>>
        SimplifiedCNF::get_var_types([[maybe_unused]] uint32_t verb) const {
        assert(need_aig);
        std::set<uint32_t> input;
        for (const auto& v: get_orig_sampl_vars()) {
            const auto it = orig_to_new_var.find(v);
            if (it == orig_to_new_var.end()) continue;
            const uint32_t cnf_var = it->second.var();
            /* std::cout << "c o input var: " << v+1 << " maps to cnf var " */
            /*      << cnf_var+1 << std::endl; */
            assert(cnf_var < nVars());
            input.insert(cnf_var);
        }
        assert(input.size() == sampl_vars.size());
        std::set<uint32_t> to_define;
        std::set<uint32_t> to_define_orig;
        for (uint32_t v = 0; v < num_defs(); v++) {
            if (!get_orig_sampl_vars().count(v) && !defined(v)) {
                const auto it = orig_to_new_var.find(v);
                if (it == orig_to_new_var.end()) continue;
                const uint32_t cnf_var = it->second.var();
                /* std::cout << "c o to_define var: " << v+1 << " maps to cnf var " */
                /*  << cnf_var+1 << std::endl; */
                assert(cnf_var < nVars());
                to_define.insert(cnf_var);
                to_define_orig.insert(v);
            }
        }
        std::set<uint32_t> unsat_defined_vars;
        std::set<uint32_t> backw_synth_defined_vars;
        for (uint32_t v = 0; v < num_defs(); v++) {
            if (get_orig_sampl_vars().count(v)) continue;
            if (orig_to_new_var.count(v) == 0) continue;
            // This var is NOT input and IS in the CNF
            if (defined(v) == false) continue;
            auto s = get_dependent_vars_recursive(defs[v], v);
            bool only_input_deps = true;
            for(const auto& d: s) {
                if (!get_orig_sampl_vars().count(d)) {
                    only_input_deps = false;
                    break;
                }
            }

            const uint32_t cnf_var = orig_to_new_var.at(v).var();
            assert(cnf_var < nVars());
            if (only_input_deps) unsat_defined_vars.insert(cnf_var);
            else backw_synth_defined_vars.insert(cnf_var);
        }
        if (verb >= 1) {
            std::cout << "c o [get-var-types] Variable types in CNF:" << std::endl;
            std::cout << "c o [get-var-types] Num input vars: " << input.size() << std::endl;
            std::cout << "c o [get-var-types]   Input vars: ";
            for(const auto& v: input) {
                std::cout << v+1 << " ";
            }
            std::cout << std::endl;

            std::cout << "c o [get-var-types] Num to-define vars: " << to_define.size() << std::endl;
            std::cout << "c o [get-var-types]   To-define vars (new): ";
            for(const auto& v: to_define) std::cout << v+1 << " ";
            std::cout << std::endl;
            std::cout << "c o [get-var-types]   To-define vars (orig): ";
            for(const auto& v: to_define_orig) std::cout << v+1 << " ";
            std::cout << std::endl;


            std::cout << "c o [get-var-types] Num unsat-defined vars: "
                << unsat_defined_vars.size() << std::endl;
            std::cout << "c o [get-var-types] Num backward-synth-defined vars: "
                << backw_synth_defined_vars.size() << std::endl;
            std::cout << "c o [get-var-types] Total vars in ORIG CNF: " << defs.size() << std::endl;
            std::cout << "c o [get-var-types] Total vars in NEW  CNF: " << nVars() << std::endl;
        }
        assert(input.size() + to_define.size() + unsat_defined_vars.size() + backw_synth_defined_vars.size() == nVars());

        // unsat-defined vars can be treateed as input vars
        for(const auto& v: unsat_defined_vars) input.insert(v);
        return std::make_tuple(input, to_define, backw_synth_defined_vars);
    }

    DLL_PUBLIC CMSat::lbool SimplifiedCNF::evaluate(const std::vector<CMSat::lbool>& vals, uint32_t var) const {
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
            std::cout << "ERROR: Variable " << var+1 << " not defined" << std::endl;
            assert(defs[var] != nullptr && "Must be defined");
            exit(EXIT_FAILURE);
        }
        return AIG::evaluate(vals, defs[var], defs);
    }

    DLL_PUBLIC std::set<uint32_t> SimplifiedCNF::get_vars_need_definition() const {
        std::set<uint32_t> ret;
        std::set<uint32_t> osv(opt_sampl_vars.begin(), opt_sampl_vars.end());
        for(uint32_t i = 0; i < defs.size(); i++) {
            if (defs[i] == nullptr && !osv.count(i))
                ret.insert(i);
        }
        return ret;
    }

    DLL_PUBLIC bool SimplifiedCNF::defs_invariant() const {
        check_cnf_sampl_sanity();

        if (!need_aig) return true;
        assert(orig_sampl_vars_set && "If need_aig, orig_sampl_vars_set must be set");
        assert(sampl_vars_set);
        assert(sampl_vars.size() == opt_sampl_vars.size());
        assert(defs.size() >= nvars && "Defs size must be at least nvars, as nvars can only be smaller");


        for(const auto& v: orig_sampl_vars) {
            if(defs[v] == nullptr) continue;
            else if (defs[v]->type == AIGT::t_const) {
                continue;
            }
            else if (defs[v]->type == AIGT::t_lit) {
                assert(orig_sampl_vars.count(defs[v]->var) && "If orig_sampl_var is defined to a literal, that literal must also be an orig_sampl_var");
                continue;
            } else {
                std::cerr << "ERROR: Orig sampl var " << v+1
                    << " cannot be defined to an AIG other than"
                    " a const or a lit pointing to another orig_sampl_var, but it is: "
                    << defs[v] << std::endl;
                assert(false);
            }

        }
        check_pre_post_backward_round_synth();
        all_vars_accounted_for();
        check_self_dependency();
        get_var_types(0);
        random_check_synth_funs();
        return true;
    }

    // Get the orig vars this AIG depends on, recursively expanding defined vars
    DLL_PUBLIC std::set<uint32_t> SimplifiedCNF::get_dependent_vars_recursive(const aig_ptr& aig, uint32_t orig_v) const {
        assert(need_aig);
        std::set<uint32_t> dep;
        std::map<uint32_t, std::set<uint32_t>> cache;
        AIG::get_dependent_vars(aig, dep, orig_v);
        bool changed = true;
        while(changed) {
            changed = false;
            std::set<uint32_t> new_dep;
            for(const auto& v: dep) {
                if (!defined(v)) new_dep.insert(v);
                else {
                    std::set<uint32_t> sub_dep;
                    if (cache.count(v)) sub_dep = cache.at(v);
                    else {
                        AIG::get_dependent_vars(defs[v], sub_dep, v);
                        assert(!sub_dep.count(v) && "Variable cannot depend on itself");
                        cache[v] = sub_dep;
                    }
                    new_dep.insert(sub_dep.begin(), sub_dep.end());
                }
            }
            if (new_dep != dep) changed = true;
            dep = new_dep;
        }
        assert(!dep.count(orig_v) && "Variable cannot depend on itself");
        return dep;
    }

    DLL_PUBLIC void SimplifiedCNF::check_self_dependency() const {
        if (!need_aig) return;
        for(uint32_t orig_v = 0; orig_v < defs.size(); orig_v ++) {
            if (orig_sampl_vars.count(orig_v)) {
                if (!defined(orig_v)) continue;
                else if (defs[orig_v]->type == AIGT::t_lit) {
                    assert(defs[orig_v]->var != orig_v && "Variable depends on itself? Also this is an orig sampl var defined to a literal that has the same var?");
                    assert(orig_sampl_vars.count(defs[orig_v]->var) && "If orig_sampl_var is defined to a literal, that literal must also be an orig_sampl_var");
                    continue;
                } else if (defs[orig_v]->type == AIGT::t_const) {
                    continue;
                } else {
                    std::cerr << "ERROR:Orig sampl var " << orig_v+1 << " cannot be defined to an AIG other than literal or const, but it is: " << defs[orig_v] << std::endl;
                    assert(false);
                }
            }
            if (!defined(orig_v)) continue;

            // This checks for self-dependency
            get_dependent_vars_recursive(defs[orig_v], orig_v);
        }
    }

    DLL_PUBLIC void SimplifiedCNF::check_cnf_vars() const {
        auto check = [](const std::vector<CMSat::Lit>& cl, uint32_t _nvars) {
            for(const auto& l: cl) {
                if (l.var() >= _nvars) {
                    std::cout << "ERROR: Found a clause with a variable that has more variables than the number of variables we are supposed to have" << std::endl;
                    std::cout << "cl: ";
                    for(const auto& l2: cl) std::cout << l2 << " ";
                    std::cout << std::endl;
                    std::cout << "nvars: " << _nvars+1 << std::endl;
                    exit(EXIT_FAILURE);
                }
                assert(l.var() < _nvars);
            }
        };

        // all clauses contain variables that are less than nvars
        for(const auto& cl: clauses) check(cl, nvars);
        for(const auto& cl: red_clauses) check(cl, nvars);


        // Now check orig_to_new_var covers all vars in the CNF
        if (!need_aig) return;
        std::set<uint32_t> vars_in_cnf;
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
            assert(v < nvars); // already checked above
            bool in_orig = false;
            for(const auto& [o, n]: orig_to_new_var) {
                if (n.var() == v) {
                    in_orig = true;
                    break;
                }
            }
            assert(in_orig && "All CNF vars must be in orig_to_new_var");
        }
    }

    // all vars are either: in orig_sampl_vars, defined, or in the cnf
    DLL_PUBLIC void SimplifiedCNF::all_vars_accounted_for() const {
        assert(need_aig);
        for(uint32_t v = 0; v < defs.size(); v ++) {
            if (orig_sampl_vars.count(v)) continue; // we'll get this as input
            if (defined(v)) continue; // already defined
            if (orig_to_new_var.count(v)) continue; // appears in CNF
            std::cout << "ERROR: Orig var " << v+1 << " is not defined, not in orig_sampl_vars, and not in cnf" << std::endl;
            assert(false && "All vars must be accounted for");
        }
    }

    // this checks that NO unsat-define has been made yet
    DLL_PUBLIC void SimplifiedCNF::check_pre_post_backward_round_synth() const {
        if (!need_aig) return;
        std::map<uint32_t, std::set<uint32_t>> dependencies;
        for(const auto& [o, n] : orig_to_new_var) {
            assert(o < defs.size());
            assert(n != CMSat::lit_Undef && n.var() < nvars);
            if (defined(o)) {
                auto s = get_dependent_vars_recursive(defs[o], o);
                dependencies[o] = s;
                bool only_orig_sampl = true;
                for(const auto& v: s) {
                    if (!orig_sampl_vars.count(v)) {
                        only_orig_sampl = false;
                        break;
                    }
                }
                if (!after_backward_round_synth && !only_orig_sampl) {
                    std::cout << "ERROR: Found a variable in CNF, orig: " << o+1 << " new: " << n.var()+1
                        << " that is defined in terms of non-orig-sampl-vars before backward round synth.";
                    std::cout << std::endl << " in old: ";
                    for(const auto& v: s) std::cout << v+1 << "( " << (orig_sampl_vars.count(v) ? "o" : "n") << " ) ";
                    std::cout << std::endl << " in new: ";
                    for(const auto& v: s) {
                        auto it = orig_to_new_var.find(v);
                        if (it == orig_to_new_var.end()) std::cout << "undef ";
                        else std::cout << it->second.var()+1 << "( " << (orig_sampl_vars.count(v) ? "o" : "n") << " ) ";
                    }
                    std::cout << std::endl;
                    assert(false && "Before backward round synth, variables in CNF must be defined ONLY in terms of orig_sampl_vars");
                }
            }
        }
        for(const auto& [o, dep] : dependencies) {
            assert(!orig_sampl_vars.count(o));
            for(const auto& v: dep) {
                // o depends on v
                if (orig_sampl_vars.count(v)) continue;
                auto it = dependencies.find(v);
                if (it == dependencies.end()) continue;
                if (it->second.count(o)) {
                    // so v cannot depend on o
                    std::cout << "ERROR: Found a dependency cycle between orig vars "
                        << o+1 << " and " << v+1 << std::endl;
                    assert(false && "Dependency cycle found");
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
        std::set<uint32_t> opt_sampl_vars_s(opt_sampl_vars.begin(), opt_sampl_vars.end());
        std::set<uint32_t> to_remove;
        for(const auto& w: weights) {
            if (opt_sampl_vars_s.count(w.first) == 0) to_remove.insert(w.first);
        }
        if (to_remove.empty()) return;

        std::cout << "c o WARNING!!!! "
            << to_remove.size() << " weights removed that weren't in the (opt) sampling set" << std::endl;
        for(const auto& w: to_remove) weights.erase(w);
    }

    DLL_PUBLIC void SimplifiedCNF::check_cnf_sampl_sanity() const {
        assert(fg != nullptr);

        check_cnf_vars();
        std::set<uint32_t> sampl_vars_s(sampl_vars.begin(), sampl_vars.end());
        std::set<uint32_t> opt_sampl_vars_s(opt_sampl_vars.begin(), opt_sampl_vars.end());

        // sampling vars less than nvars
        for(const auto& v: opt_sampl_vars_s) {
            if (v >= nvars) {
                std::cout << "ERROR: Found a sampling var that is greater than the number of variables we are supposed to have" << std::endl;
                std::cout << "sampling var: " << v+1 << std::endl;
                std::cout << "nvars: " << nvars+1 << std::endl;
                exit(EXIT_FAILURE);
            }
            assert(v < nvars);
        }

        // all sampling vars are also opt sampling vars
        for(const auto& v: sampl_vars_s) {
            if (!opt_sampl_vars_s.count(v)) {
                std::cout << "ERROR: Found a sampling var that is not an opt sampling var: "
                    << v+1 << std::endl;
                exit(EXIT_FAILURE);
            }
            assert(opt_sampl_vars_s.count(v));
        }

        // weights must be in opt sampling vars
        for(const auto& w: weights) {
            if (w.first >= nvars) {
                std::cout << "ERROR: Found a weight that is greater than the number of variables we are supposed to have" << std::endl;
                std::cout << "weight var: " << w.first+1 << std::endl;
                std::cout << "nvars: " << nvars+1 << std::endl;
                exit(EXIT_FAILURE);
            }
            assert(w.first < nvars);
            if (opt_sampl_vars_s.count(w.first) == 0) {
                // Idiotic but we allow 1/1 weights, even though they are useless
                if (w.second.pos->is_one() && w.second.neg->is_one()) continue;

                std::cout << "ERROR: Found a weight that is not an (opt) sampling var: "
                    << w.first+1 << std::endl;
                exit(EXIT_FAILURE);
            }
            assert(opt_sampl_vars_s.count(w.first));
        }
    }

    // Gives all the orig lits that map to this variable
    DLL_PUBLIC std::map<uint32_t, std::vector<CMSat::Lit>> SimplifiedCNF::get_new_to_orig_var_list() const {
        std::map<uint32_t, std::vector<CMSat::Lit>> ret;
        for(const auto& p: orig_to_new_var) {
            const CMSat::Lit l = p.second;
            if (l != CMSat::lit_Undef) {
                auto it2 = ret.find(l.var());
                if (it2 != ret.end()) ret[l.var()] = std::vector<CMSat::Lit>();
                ret[l.var()].push_back(CMSat::Lit(p.first, l.sign()));
            }
        }
        return ret;
    }

    // Gives an example lit, sometimes good enough
    DLL_PUBLIC std::map<uint32_t, CMSat::Lit> SimplifiedCNF::get_new_to_orig_var() const {
        std::map<uint32_t, CMSat::Lit> ret;
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
            std::cout << "ERROR: Tried to access a variable that is too large" << std::endl;
            std::cout << "var: " << v+1 << std::endl;
            std::cout << "nvars: " << nVars() << std::endl;
            assert(v < nVars());
            exit(EXIT_FAILURE);
        }
    }

    DLL_PUBLIC void SimplifiedCNF::check_clause(const std::vector<CMSat::Lit>& cl) const {
        for(const auto& l: cl) check_var(l.var());
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
set_get_macro(std::string, specified_order_fname)
set_get_macro(uint32_t, verb)
set_get_macro(uint32_t, extend_max_confl)
set_get_macro(int, oracle_find_bins)
set_get_macro(int, num_samples)
set_get_macro(double, cms_glob_mult)
set_get_macro(int, extend_ccnr)
set_get_macro(int, autarkies)
