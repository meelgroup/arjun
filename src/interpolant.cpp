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

#include "src/constants.h"
extern "C" {
#include "mpicosat/mpicosat.h"
}

#include "interpolant.h"

using namespace CMSat;
using namespace CaDiCaL;

void MyTracer::add_derived_clause(uint64_t id, bool /*red*/, const std::vector<int> & clause,
                               const std::vector<uint64_t> & oantec) {
  cout << "red ID:" << setw(4) << id;//  << " red: " << (int)red;
  cout << " cl: "; for(const auto& l: clause) cout << l << " "; cout << endl;
  cout << "atec: "; for(const auto& l: oantec) cout << l << " "; cout << endl;
  cls[id] = pl_to_lit_cl(clause);
  auto rantec = oantec;
  std::reverse(rantec.begin(), rantec.end());
  assert(rantec.size() >= 2);

  const uint64_t id1 = rantec[0];
  FHolder::Formula f = fs_clid[id1];
  set<Lit> resolvent(cls[id1].begin(),cls[id1].end());
  for(uint32_t i = 1; i < rantec.size(); i++) {
      cout << "resolvent: "; for(const auto& l: resolvent) cout << l << " "; cout << endl;

      const uint64_t id2 = rantec[i];
      const vector<Lit>& cl = cls[id2];
      cout << "resolving with: " << cl << endl;;
      Lit res_lit = lit_Undef;
      for(const auto& l: cl) {
          if (resolvent.count(~l)) {
              assert(res_lit == lit_Undef);
              res_lit = ~l;
              resolvent.erase(~l);
          } else {
              assert(resolvent.count(~l) == 0 && "not tautological resolvent!");
              resolvent.insert(l);
          }
      }
      assert(res_lit != lit_Undef);
      bool input_or_copy = input.count(res_lit.var()) || res_lit.var() >= (uint32_t)orig_num_vars;
      if (input_or_copy) f = fh->compose_and(f, fs_clid[id2]);
      else f = fh->compose_or(f, fs_clid[id2]);
  }
  fs_clid[id] = f;
  cout << "intermediate formula: " << fs_clid[id] << endl;
  if (clause.empty()) {
      out = f;
      cout << "Final formula: " << f << endl;
  }
}

void MyTracer::add_original_clause(uint64_t id, bool red, const std::vector<int> & clause, bool) {
  assert(red == false);
  cout << "orig ID:" << setw(4)<< id;
  cout << " cl: "; for(const auto& l: clause) cout << l << " "; cout << endl;
  cls[id] = pl_to_lit_cl(clause);

  bool formula_a = true;
  for(const auto& l : clause) {
      if (abs(l)-1 >= orig_num_vars) {formula_a = false; break;}
  }
  if (formula_a) {
      // output of formula is equal to the set of inputs being satisfied or not in this CL
      vector<Lit> cl;
      for(const auto& l: clause) {
          int32_t v = abs(l)-1;
          if (input.count(v)) cl.push_back(pl_to_lit(l));
      }
      FHolder::Formula f;
      fh->solver->new_var();
      f.out = Lit(fh->solver->nVars()-1, false);
      auto cl2 = cl;
      cl2.push_back(~f.out);
      f.clauses.push_back(cl2);
      for(const auto& l: cl) {
          f.clauses.push_back({~l, f.out});
      }
      fs_clid[id] = f;
  } else {
      fs_clid[id] = fh->constant_formula(true);
  }
  cout << "intermediate formula: " << fs_clid[id] << endl;
}

void Interpolant::generate_interpolant(
        const vector<Lit>& assumptions, uint32_t test_var, ArjunNS::SimplifiedCNF& cnf) {
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
    vector<vector<Lit>> mini_cls;
    vector<Lit> cl;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (set_vals[i] != l_Undef) {
            if (i == test_var) continue;
            cl.clear();
            cl.push_back(Lit(i, set_vals[i] == l_False));
            mini_cls.push_back(cl);
        }
    }
    for(uint32_t cl_at = 0; cl_at < cl_num; cl_at++) {
        if (picosat_coreclause(ps, cl_at)) {
            cl.clear();
            cout << "cl: " << cl_map[cl_at] << endl;
            for(auto l: cl_map[cl_at]) {
                // if it's a var that's the image that has been
                // forced to be equal, then replace
                if (l.var() < orig_num_vars*2 && l.var() >= orig_num_vars) {
                    auto indic = var_to_indic[l.var()-orig_num_vars];
                    if (indic != var_Undef && set_vals[indic] == l_True)
                        l = Lit (l.var()-orig_num_vars, l.sign());
                }
                cl.push_back(l);
            }
            cout << "cl: " << cl << endl;
            for(const auto& l: cl) assert(l.var() < orig_num_vars*2);
            mini_cls.push_back(cl);
        }
    }
    for(const auto& l: assumptions) mini_cls.push_back({l});

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

    // CaDiCaL on the core only
    CaDiCaL::Solver* cdcl = new Solver();
    MyTracer t(orig_num_vars, cnf.opt_sampl_vars);
    t.fh = new FHolder();
    t.fh->solver = solver;
    t.fh->my_true_lit = my_true_lit;
    verb_print(1, "true lit: " << t.fh->my_true_lit);

    cdcl->connect_proof_tracer(&t, true);
    /* std::stringstream name; */
    /* name << "core-" << test_var+1 << ".cnf.trace"; */
    /* FILE* core = fopen(name.str().c_str(), "w"); */
    for(const auto& c: mini_cls) {
        for(const auto& l: c) cdcl->add(lit_to_pl(l));
        cdcl->add(0);
    }
    pret = cdcl->solve();
    verb_print(3, "c CaDiCaL ret: " << pret);
    if (pret == Status::SATISFIABLE) {
        cout << "ERROR: core should be UNSAT" << endl;
        assert(false);
        exit(-1);
    }
    if (pret == Status::UNKNOWN) {
        cout << "ERROR: OOOpps, we should give more time for picosat, got UNKNOWN" << endl;
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

    //TODO: test_var's definition is now computed, and should be saved
    /* cnf.fh->fs[test_var] = t.out; */
    /* cnf.fh->fs[test_var].finished = true; */
    verb_print(1, "definition of var: " << test_var+1 << " is: " << t.out);
    verb_print(1, "----------------------------");
}

void Interpolant::fill_picolsat(uint32_t _orig_num_vars) {
    set_vals.clear();
    set_vals.resize(solver->nVars(), l_Undef);
    orig_num_vars = _orig_num_vars;

    solver->start_getting_constraints(false);
    vector<Lit> cl;
    bool is_xor, rhs;
    for(uint32_t i = 0; i < solver->nVars(); i++) picosat_inc_max_var(ps);
    while(solver->get_next_constraint(cl, is_xor, rhs)) {
        assert(!is_xor); assert(rhs);
        cl_map[cl_num++] = cl;
        for (const auto& l: cl) picosat_add(ps, lit_to_pl(l));
        picosat_add(ps, 0);
    }
    solver->end_getting_constraints();
}

void Interpolant::fill_var_to_indic(const vector<uint32_t>& _var_to_indic) {
    var_to_indic = _var_to_indic;
}

void Interpolant::add_clause(const vector<Lit>& cl) {
    assert(cl.size() == 1);

    cl_map[cl_num++] = cl;
    picosat_add(ps, lit_to_pl(cl[0]));
    picosat_add(ps, 0);
    set_vals[cl[0].var()] = l_True;
}
