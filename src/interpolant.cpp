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
#include <cryptominisat5/mpicosat.h>
}

#include "interpolant.h"
#include <memory>
#include "constants.h"

using namespace CMSat;
using namespace CaDiCaL;

void MyTracer::add_derived_clause(uint64_t id, bool /*red*/, const std::vector<int> & clause,
                               const std::vector<uint64_t> & oantec) {
  if (conf.verb >= 3) {
      cout << "red ID:" << setw(4) << id;//  << " red: " << (int)red;
      cout << " cl: "; for(const auto& l: clause) cout << l << " "; cout << endl;
      cout << "antec: "; for(const auto& l: oantec) cout << l << " "; cout << endl;
  }
  cls[id] = pl_to_lit_cl(clause);
  auto rantec = oantec;
  std::reverse(rantec.begin(), rantec.end());

  const uint64_t id1 = rantec[0];
  auto aig = fs_clid[id1];
  set<Lit> resolvent(cls[id1].begin(),cls[id1].end());
  for(uint32_t i = 1; i < rantec.size(); i++) {
      if (conf.verb >= 4) {
          cout << "resolvent: "; for(const auto& l: resolvent) cout << l << " "; cout << endl;
      }

      const uint64_t id2 = rantec[i];
      const vector<Lit>& cl = cls[id2];
      verb_print(3, "resolving with: " << cl);
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
      if (input_or_copy) aig = AIG::new_and(aig, fs_clid[id2]);
      else aig = AIG::new_or(aig, fs_clid[id2]);
  }
  fs_clid[id] = aig;
  verb_print(5, "intermediate formula: " << fs_clid[id]);
  if (clause.empty()) {
      out = aig;
      verb_print(5, "Final formula: " << aig);
  }
}

void MyTracer::add_original_clause(uint64_t id, bool red, const std::vector<int> & clause, bool) {
  assert(red == false);
  if (conf.verb >= 3) {
      cout << "orig ID:" << setw(4)<< id << " cl: ";
      for(const auto& l: clause) cout << l << " ";
      cout << endl;
  }
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
      auto aig = aig_mng.new_const(false);
      for(const auto& l: cl) aig = AIG::new_or(aig, AIG::new_lit(l));
      fs_clid[id] = aig;
  } else {
      fs_clid[id] = aig_mng.new_const(true);
  }
  verb_print(5, "intermediate formula: " << fs_clid[id]);
}

void Interpolant::generate_interpolant(
        const vector<Lit>& assumptions, uint32_t test_var, const ArjunNS::SimplifiedCNF& cnf, const set<uint32_t>& input_vars) {
    verb_print(2, "generating unsat proof for: " << test_var+1);
    verb_print(3, "assumptions: " << assumptions);
    verb_print(3, "orig_num_vars: " << orig_num_vars);

    // FIRST, we get an UNSAT core
    for(const auto& l: assumptions) picosat_assume(ps, lit_to_pl(l));
    auto pret = picosat_sat(ps, 10000000);
    verb_print(5, "c pret: " << pret);
    if (pret == PICOSAT_SATISFIABLE) {
        cout << "BUG, should be UNSAT" << endl;
        assert(false);
        exit(EXIT_FAILURE);
    }
    if (pret == PICOSAT_UNKNOWN) {
        cout << "OOOpps, we should give more time for picosat, got UNKNOWN" << endl;
        assert(false);
        exit(EXIT_FAILURE);
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
            verb_print(3, "cl: " << cl_map[cl_at]);
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
            verb_print(3, "[interpolant] picosat says need cl: " << cl);
            mini_cls.push_back(cl);
        }
    }
    for(const auto& l: assumptions) mini_cls.push_back({l});

    if (!conf.debug_synth.empty()) {
        std::stringstream name;
        name << "core-" << test_var+1 << ".cnf";
        verb_print(1, "Writing core to: " << name.str());
        auto f = std::ofstream(name.str());
        f << "p cnf " << orig_num_vars*2 << " " << mini_cls.size() << endl;
        f << "c orig_num_vars: " << orig_num_vars << endl;
        f << "c output: " << test_var +1 << endl;
        f << "c output2: " << orig_num_vars+test_var +1 << endl;
        f << "c num inputs: " << cnf.get_sampl_vars().size() << endl;
        f << "c inputs: "; for(const auto& l: cnf.get_sampl_vars()) f << (l+1) << " "; f << endl;
        for(const auto& c: mini_cls) f << c << " 0" << endl;
        f.close();
    }

    // CaDiCaL on the core only
    auto cdcl = std::make_unique<Solver>();
    MyTracer t(orig_num_vars, input_vars, conf);

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
        exit(EXIT_FAILURE);
    }
    if (pret == Status::UNKNOWN) {
        cout << "ERROR: OOOpps, we should give more time for picosat, got UNKNOWN" << endl;
        assert(false);
        exit(EXIT_FAILURE);
    }
    release_assert(pret == Status::UNSATISFIABLE);
    cdcl->disconnect_proof_tracer(&t);

    defs[test_var] = t.out;
    verb_print(5, "definition of var: " << test_var+1 << " is: " << t.out);
    verb_print(5, "----------------------------");
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

void Interpolant::add_unit_cl(const vector<Lit>& cl) {
    assert(cl.size() == 1);

    cl_map[cl_num++] = cl;
    picosat_add(ps, lit_to_pl(cl[0]));
    picosat_add(ps, 0);
    assert(cl[0].sign() == false);
    set_vals[cl[0].var()] = l_True;
}
