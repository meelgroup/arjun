/*
 Arjun

 Copyright (c) 2019, Mate Soos and Kuldeep S. Meel. All rights reserved.

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
#include <iomanip>
#include <map>

#include "src/arjun.h"
#include "src/time_mem.h"
#include "extend.h"
#include "constants.h"
#include "cryptominisat5/solvertypesmini.h"

/* extern "C" { */
/* #include "mpicosat/mpicosat.h" */
/* } */
#include "cadical.hpp"
#include "tracer.hpp"

using namespace ArjunInt;
using namespace ArjunNS;
using namespace CaDiCaL;
using std::setw;

void Extend::add_all_indics_except(const set<uint32_t>& except) {
    assert(dont_elim.empty());
    assert(var_to_indic.empty());
    assert(indic_to_var.empty());

    var_to_indic.resize(orig_num_vars*2, var_Undef);

    vector<Lit> tmp;
    for(uint32_t var = 0; var < orig_num_vars; var++) {
        if (except.count(var)) continue;

        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        //torem_orig.push_back(Lit(this_indic, false));
        var_to_indic[var] = this_indic;
        var_to_indic[var+orig_num_vars] = this_indic;
        dont_elim.push_back(Lit(this_indic, false));
        indic_to_var.resize(this_indic+1, var_Undef);
        indic_to_var[this_indic] = var;

        // Below two mean var == (var+orig) in case indic is TRUE
        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,        true));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,        true));
        solver->add_clause(tmp);
    }
    seen.clear();
    seen.resize(indic_to_var.size()*2, 0);
}

// lit to picolit
int lit_to_pl(const Lit l) {
    int picolit = (l.var()+1) * (l.sign() ? -1 : 1);
    return picolit;
}

void Extend::unsat_define(SimplifiedCNF& cnf) {
    double start_round_time = cpuTime();
    assert(cnf.sampl_vars.size() == cnf.opt_sampl_vars.size());
    assert(cnf.opt_sampl_vars_set);
    uint32_t start_size = cnf.opt_sampl_vars.size();
    fill_solver(cnf);
    solver->set_verbosity(0);
    solver->set_scc(1);

    // Fill no need
    set<uint32_t> no_need;
    // [ replaced, replaced_with ]
    /* auto ret1 = solver->get_all_binary_xors(); */
    /* for(const auto& p: ret1) no_need.insert(p.first.var()); */
    auto ret2 = solver->get_zero_assigned_lits();
    for(const auto& p: ret2) no_need.insert(p.var());
    for(const auto& v: cnf.opt_sampl_vars) no_need.insert(v);
    add_all_indics_except(no_need);

    assert(ps == nullptr);
    ps = picosat_init();
    int pret = picosat_enable_trace_generation(ps);
    release_assert(pret != 0 && "Traces cannot be generated in PicoSAT");

    // Don't mess with already set/replaced variables
    std::string str = "must-scc-vrepl, clean-cls";
    solver->simplify(nullptr, &str);

    set_vals.clear();
    set_vals.resize(solver->nVars(), l_Undef);

    solver->start_getting_constraints(false);
    vector<Lit> cl;
    bool is_xor, rhs;
    for(uint32_t i = 0; i < indic_to_var.size(); i++) picosat_inc_max_var(ps);
    while(solver->get_next_constraint(cl, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        cl_map[cl_num++] = cl;
        for (const auto& l: cl) picosat_add(ps, lit_to_pl(l));
        picosat_add(ps, 0);
    }
    solver->end_getting_constraints();

    for(const auto& x: seen) assert(x == 0);
    for(const auto& v: cnf.opt_sampl_vars) {
        if (var_to_indic[v] == var_Undef) continue;
        cl.clear();
        auto ind_v = var_to_indic[v];
        Lit ind_l = Lit(ind_v, false);
        cl.push_back(ind_l);
        solver->add_clause(cl);
        cl_map[cl_num++] = cl;
        picosat_add(ps, lit_to_pl(ind_l));
        picosat_add(ps, 0);
        set_vals[ind_l.var()] = l_True;
    }

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (no_need.count(i)) continue;
        unknown.push_back(i);
    }

    sort_unknown(unknown, incidence);
    verb_print(1,"[arjun] Start unknown size: " << unknown.size());
    uint32_t sat = 0;
    set<uint32_t> unknown_set(unknown.begin(), unknown.end());

    vector<Lit> assumptions;
    uint32_t num_done = 0;
    uint32_t num_unsat = 0;
    while(!unknown.empty()) {
        if (num_done % 100 == 99) {
            verb_print(1, "[padoa] done: " << setw(4) << num_done
                    << " unsat: " << setw(4) << num_unsat
                    << " left: " << setw(4) << unknown.size()
                    << " T: " << std::setprecision(2) << std::fixed << setw(6)
                    << (cpuTime() - start_round_time)
                    << " var/s: " << setw(6) << (double)num_done/(cpuTime() - start_round_time));

        }
        uint32_t test_var = unknown.back();
        unknown.pop_back();
        if (unknown_set.count(test_var) == 0) continue;

        assert(test_var < orig_num_vars);
        verb_print(5, "Testing: " << test_var);

        //Assumption filling -- assume everything in indep is the same
        assert(test_var != var_Undef);

        assumptions.clear();
        uint32_t indic = var_to_indic[test_var];
        assumptions.push_back(Lit(test_var, false));
        set_vals[test_var] = l_True;
        assumptions.push_back(Lit(test_var + orig_num_vars, true));
        set_vals[test_var+orig_num_vars] = l_False;

        //TODO: Actually, we should get conflict, that will make things easier
        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        ret = solver->solve(&assumptions);
        num_done++;

        if (ret == l_False) verb_print(5, "[arjun] extend solve(): False");
        else if (ret == l_True) {verb_print(5, "[arjun] extend solve(): True");sat++;}
        else if (ret == l_Undef) verb_print(5, "[arjun] extend solve(): Undef");

        if (ret == l_False) {
            num_unsat++;
            // Dependent fully on `indep`
            // TODO: run get_conflict and then we know which were
            // actually needed, so we can do an easier generation/check
            generate_picosat(assumptions, test_var, cnf);
            cl.clear();
            Lit l(indic, false);
            cl.push_back(l);
            solver->add_clause(cl);
            cl_map[cl_num++] = cl;
            picosat_add(ps, lit_to_pl(l));
            picosat_add(ps, 0);
            set_vals[indic] = l_True;

            cnf.opt_sampl_vars.push_back(test_var);

        } else if (ret == l_True) {
            // Optimisation: if we see both true and false, then it cannot be independent
            for(uint32_t v = 0; v < orig_num_vars; v++) {
                if (!unknown_set.count(v)) continue;
                uint32_t other_v = v + orig_num_vars;
                if (solver->get_model()[other_v] != solver->get_model()[v]) {
                    verb_print(5,"TRUE erasing v: " << v + 1 << " because it's been seen both true&false");
                    unknown_set.erase(v);
                }
            }
            // Not fully dependent
            set_vals[indic] = l_Undef;
        } else {
            set_vals[indic] = l_Undef;
        }
        set_vals[test_var] = l_Undef;
        set_vals[test_var+orig_num_vars] = l_Undef;
    }
    picosat_reset(ps);

    verb_print(1, "defined via Padoa: " << cnf.opt_sampl_vars.size()-start_size
            << " SAT: " << sat
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();
}

class MyTracer : public Tracer {
  void add_derived_clause (uint64_t ID, bool red, const std::vector<int> & clause,
                                   const std::vector<uint64_t> & antec) override {
      cout << "red ID:" << setw(4) << ID << " red:" << (int)red;
      cout << " cl: ";
      for(const auto& l: clause) cout << l << " "; cout << endl;
      cout << "atec: ";
      for(const auto& l: antec) cout << l << " "; cout << endl;
  }

  void add_original_clause (uint64_t ID, bool red, const std::vector<int> & clause, bool) override {
      assert(red == false);
      cout << "orig ID:" << setw(4)<< ID;
      cout << " cl: ";
      for(const auto& l: clause) cout << l << " "; cout << endl;
  }

};

void Extend::generate_picosat(const vector<Lit>& assumptions, uint32_t test_var, SimplifiedCNF& cnf) {
    verb_print(2, "generating unsat proof for: " << test_var+1);
    // FIRST, we get an UNSAT core
    for(const auto& l: assumptions) picosat_assume(ps, lit_to_pl(l));

    auto pret = picosat_sat(ps, 10000000);
    verb_print(5, "c pret: " << pret);
    if (pret == PICOSAT_SATISFIABLE) {
        cout << "BUG, core should be UNSAT" << endl;
        assert(false);
        exit(-1);
    }
    if (pret == PICOSAT_UNKNOWN) {
        cout << "OOOpps, we should give more time for picosat, got UNKNOWN" << endl;
        assert(false);
        exit(-1);
    }
    release_assert(pret == PICOSAT_UNSATISFIABLE);

    // NEXT we generate the small CNF that is UNSAT and is simplified
    vector<Lit> cl;
    vector<vector<Lit>> mini_cls;
    for(uint32_t cl_at = 0; cl_at < cl_num; cl_at++) {
        if (picosat_coreclause(ps, cl_at)) {
            bool taut = false;
            cl.clear();
            for(auto l: cl_map[cl_at]) {
                // Deal with set vars
                if (set_vals[l.var()] != l_Undef) {
                    int val = (set_vals[l.var()] == l_True);
                    val ^= l.sign();
                    if (val) goto end; //satisfied clause
                    continue; // false value in clausee
                }

                // if it's a var that's the image that has been
                // forced to be equal, then replace
                if (l.var() < orig_num_vars*2 && l.var() >= orig_num_vars) {
                    auto indic = var_to_indic[l.var()-orig_num_vars];
                    if (indic != var_Undef && set_vals[indic] == l_True)
                        l = Lit (l.var()-orig_num_vars, l.sign());
                }

                if (seen[(~l).toInt()]) {taut = true; break;}
                if (seen[l.toInt()]) continue;
                seen[l.toInt()] = true;
                cl.push_back(l);
            }
            if (taut) goto end;
            for(const auto& l: cl) assert(l.var() < orig_num_vars*2);
            mini_cls.push_back(cl);
            end:
            for(const auto& l: cl) seen[l.toInt()] = false;
        }
    }


    bool debug_core = true;
    if (debug_core) {
        std::stringstream name;
        name << "core-" << test_var+1 << ".cnf";
        verb_print(5, "Writing core to: " << name.str());
        auto f = std::ofstream(name.str());
        f << "p cnf " << orig_num_vars*2 << " " << mini_cls.size() << endl;
        f << "c orig_num_vars: " << orig_num_vars << endl;
        f << "c output: " << test_var +1 << endl;
        f << "c output2: " << orig_num_vars+test_var +1 << endl;
        f << "c num inputs: " << cnf.sampl_vars.size() << endl;
        f << "c inputs: "; for(const auto& l: cnf.sampl_vars) f << (l+1) << " "; f << endl;
        for(const auto& c: mini_cls) f << c << " 0" << endl;
        f.close();
    }

    // picosat on the core only, on a simplified CNF
    CaDiCaL::Solver* cdcl = new Solver();
    MyTracer t;
    cdcl->connect_proof_tracer(&t, true);
    /* std::stringstream name; */
    /* name << "core-" << test_var+1 << ".cnf.trace"; */
    /* FILE* core = fopen(name.str().c_str(), "w"); */
    release_assert(pret != 0 && "Traces cannot be generated in PicoSAT");
    for(const auto& l: assumptions) {
        cdcl->add(lit_to_pl(l));
        cdcl->add(0);
    }
    for(const auto& c: mini_cls) {
        for(const auto& l: c) cdcl->add(lit_to_pl(l));
        cdcl->add(0);
    }
    pret = cdcl->solve();
    verb_print(5, "c pret: " << pret);
    if (pret == Status::SATISFIABLE) {
        cout << "BUG, core should be UNSAT" << endl;
        assert(false);
        exit(-1);
    }
    if (pret == Status::UNKNOWN) {
        cout << "OOOpps, we should give more time for picosat, got UNKNOWN" << endl;
        assert(false);
        exit(-1);
    }
    release_assert(pret == Status::UNSATISFIABLE);
    /* if (debug_core) { */
    /*     std::stringstream name; */
    /*     name << "core-" << test_var+1 << ".cnf.trace"; */
    /*     FILE* trace = fopen(name.str().c_str(), "w"); */
    /*     picosat_write_rup_trace(ps2, trace); */
    /* } */
    /* TraceData dat; */
    /* dat.data = (int*)malloc(1024*sizeof(int)); */
    /* dat.size = 0; */
    /* dat.capacity = 1024; */
    /* verb_print(2, "[arjun] Proof size: " << dat.size); */
    /* free(dat.data); */
    /* picosat_reset(cdcl); */
    /* fclose(core); */
    cdcl->disconnect_proof_tracer(&t);
    delete cdcl;
    cout << "----------------------------" << endl;
}

void Extend::extend_round(SimplifiedCNF& cnf) {
    assert(cnf.opt_sampl_vars_set = true);
    double start_round_time = cpuTime();
    const uint32_t orig_size = cnf.opt_sampl_vars.size();
    fill_solver(cnf);
    solver->set_verbosity(0);
    set<uint32_t> opt_sampl(cnf.opt_sampl_vars.begin(), cnf.opt_sampl_vars.end());

    /* auto xors = solver->get_recovered_xors(false); */
    /* for(const auto& g: xors) { */
    /*     int bad = 0; */
    /*     for(const auto& v: g.first) { */
    /*         if (!opt_sampl.count(v)) bad++; */
    /*         if (v >= orig_num_vars) bad = 100; */
    /*         if (bad > 1) break; */
    /*     } */
    /*     if (bad != 1) continue; */
    /*     for(const auto& v: g.first) { opt_sampl.insert(v); } */
    /* } */
    auto ites = solver->get_recovered_ite_gates();
    for(const auto& g: ites) {
        if (g.rhs.var() >= orig_num_vars) continue;
        bool ok = true;
        for(const auto& l: g.lhs) if (!opt_sampl.count(l.var())) {
            ok = false;
            break;
        }
        if (!ok) continue;
        opt_sampl.insert(g.rhs.var());
    }
    auto ors = solver->get_recovered_or_gates();
    for(const auto& g: ors) {
        if (g.rhs.var() >= orig_num_vars) continue;
        bool ok = true;
        for(const auto& l: g.get_lhs()) if (!opt_sampl.count(l.var())) {
            ok = false;
            break;
        }
        if (!ok) continue;
        opt_sampl.insert(g.rhs.var());
    }
    verb_print(1, "[extend-gates] Gates added to opt indep: " << opt_sampl.size()-orig_size << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));

    // Fill no need
    set<uint32_t> no_need;
    auto ret2 = solver->get_zero_assigned_lits();
    for(const auto& p: ret2) no_need.insert(p.var());
    add_all_indics_except(no_need);

    vector<Lit> cl;
    for(const auto& v: opt_sampl) {
        if (var_to_indic[v] == var_Undef) continue;
        cl.clear();
        cl.push_back(Lit(var_to_indic[v], false));
        solver->add_clause(cl);
    }

    //Initially, all of vars are unknown, except sampling set & replaced & set
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (no_need.count(i)) continue;
        if (opt_sampl.count(i)) continue;
        if (solver->removed_var(i)) continue;
        unknown.push_back(i);
    }

    sort_unknown(unknown, incidence);
    /* std::reverse(unknown.begin(), unknown.end()); */
    verb_print(1,"[arjun-extend] Start unknown size: " << unknown.size());

    vector<Lit> assumptions;
    uint32_t ret_undef = 0;
    /* conf.verb = 5; */
    set<uint32_t> unknown_set(unknown.begin(), unknown.end());
    uint32_t num_done = 0;
    while(!unknown.empty()) {
        uint32_t test_var = unknown.back();
        unknown.pop_back();
        if (unknown_set.count(test_var) == 0) continue;
        unknown_set.erase(test_var);
        num_done++;
        if (num_done == 300 && unknown_set.size() > 1000) {
            verb_print(1, "[arjun] extend: too many to do, after 100 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 2;
        }
        if (num_done == 500 && unknown_set.size() > 1000) {
            verb_print(1, "[arjun] extend: too many to do, after 1000 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 2;
        }
        if (num_done == 1000 && unknown_set.size() > 2000) {
            verb_print(1, "[arjun] extend: too many to do, after 2000 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 4;
        }
        if (num_done == 3000 && unknown_set.size() > 3000) {
            verb_print(1, "[arjun] extend: too many to do, after 3000 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 4;
        }
        if (num_done == 6000 && unknown_set.size() > 3000) {
            verb_print(1, "[arjun] extend: too many to do, after 6000 still lots left. Lowering conflict limit");
            // Too many to do, to expensive
            conf.extend_max_confl /= 4;
        }
        if (num_done == 15000 && unknown_set.size() > 3000) {
            verb_print(1, "[arjun] extend: too many to do, after 9000 still lots left. BREAKING");
            break;
        }
        /* cout << "num_done: " << num_done << " unknown_set.size(): " << unknown_set.size() << " confl: " << (double)solver->get_sum_conflicts()/((double)num_done*conf.extend_max_confl) << endl; */

        assert(test_var < orig_num_vars);
        verb_print(5, "Testing: " << test_var);

        //Assumption filling
        assert(test_var != var_Undef);
        assumptions.clear();
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        solver->set_max_confl(conf.extend_max_confl);
        ret = solver->solve(&assumptions);
        if (ret == l_False) {
            verb_print(5, "[arjun] extend solve(): False");
        } else if (ret == l_True) {
            verb_print(5, "[arjun] extend solve(): True");
        } else if (ret == l_Undef) {
            verb_print(5, "[arjun] extend solve(): Undef");
            ret_undef++;
        }

        if (ret == l_Undef) {
            // Timed out, we'll treat is as unknown
            assert(test_var < orig_num_vars);
        } else if (ret == l_True) {
            for(uint32_t v = 0; v < orig_num_vars; v++) {
                if (!unknown_set.count(v)) continue;
                uint32_t other_v = v + orig_num_vars;
                if (solver->get_model()[other_v] != solver->get_model()[v]) {
                    verb_print(5,"TRUE erasing v: " << v + 1);
                    unknown_set.erase(v);
                }
            }
            // Not fully dependent
        } else if (ret == l_False) {
            // Dependent fully on `indep`
            opt_sampl.insert(test_var);
            cl.clear();
            cl.push_back(Lit(var_to_indic[test_var], false));
            solver->add_clause(cl);
        }
    }
    cnf.set_opt_sampl_vars(opt_sampl);

    verb_print(1, "[arjun-extend] Extend finished "
            << " orig size: " << orig_size
            << " final size: " << cnf.opt_sampl_vars.size()
            << " Undef: " << ret_undef
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 4) solver->print_stats();
}

void Extend::get_incidence() {
    assert(orig_num_vars == solver->nVars());

    incidence.clear();
    incidence.resize(orig_num_vars, 0);
    assert(solver->nVars() == orig_num_vars);
    vector<uint32_t> inc = solver->get_lit_incidence();
    assert(inc.size() == orig_num_vars*2);
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        Lit l = Lit(i, true);
        incidence[l.var()] = std::min(inc[l.toInt()],inc[(~l).toInt()]);
    }
}

void Extend::fill_solver(const SimplifiedCNF& cnf) {
    assert(solver == nullptr);
    solver = new SATSolver;
    solver->set_verbosity(conf.verb);
    solver->set_prefix("c o ");
    solver->set_find_xors(false);
    assert(solver->nVars() == 0); // Solver here is empty

    // Inject original CNF
    orig_num_vars = cnf.nvars;
    solver->new_vars(orig_num_vars);
    for(const auto& cl: cnf.clauses) solver->add_clause(cl);
    for(const auto& cl: cnf.red_clauses) solver->add_red_clause(cl);
    get_incidence();

    // Double vars
    solver->new_vars(orig_num_vars);
    seen.clear();
    seen.resize(solver->nVars()*2, 0);

    // We only need to double the non-opt-sampling vars
    for(const auto& v: cnf.opt_sampl_vars) seen[v] = 1;
    vector<Lit> cl2;
    for(const auto& cl: cnf.clauses) {
        cl2.clear();
        for (const auto& l: cl) {
            if (seen[l.var()]) cl2.push_back(l);
            else cl2.push_back(Lit(l.var()+orig_num_vars, l.sign()));
        }
        solver->add_clause(cl2);
    }
    for(const auto& v: cnf.sampl_vars) seen[v] = 0;
}
