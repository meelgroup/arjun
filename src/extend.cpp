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

#include "common.h"
#include "cryptominisat5/solvertypesmini.h"
#include <algorithm>
#include <map>
extern "C" {
#include "mpicosat/mpicosat.h"
}

using namespace ArjunInt;

template<class T>
void Common::fill_assumptions_extend(vector<Lit>& assumptions, const T& indep)
{
    verb_print(5, "Filling assumps BEGIN");
    assumptions.clear();

    //Add known independent as assumptions
    for(const auto& var: indep) {
        assert(var < orig_num_vars);
        uint32_t indic = var_to_indic[var];
        assumptions.push_back(Lit(indic, false));
        verb_print(5, "Filled assump with indep: " << var + 1);
    }
    verb_print(5, "Filling assumps END, total assumps size: " << assumptions.size());
}

void Common::add_all_indics()
{
    // [ replaced, replaced_with ]
    auto ret = solver->get_all_binary_xors();
    set<uint32_t> no_need;
    for(const auto& p: ret) no_need.insert(p.first.var());

    vector<Lit> tmp;
    for(uint32_t var = 0; var < orig_num_vars; var++) {
        // Already has an indicator variable
        if (var_to_indic[var] != var_Undef) continue;

        if (solver->removed_var(var) || no_need.count(var)) continue;

        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        //torem_orig.push_back(Lit(this_indic, false));
        var_to_indic[var] = this_indic;
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
}

// lit to picolit
int lit_to_pl(const Lit l) {
    int picolit = (l.var()+1) * (l.sign() ? -1 : 1);
    return picolit;
}

void Common::unsat_define(const vector<uint32_t>& orig_sampl_vars) {
    assert(already_duplicated);
    solver->set_verbosity(0);
    add_all_indics();

    assert(ps == nullptr);
    ps = picosat_init();
    int pret = picosat_enable_trace_generation(ps);
    release_assert(pret != 0 && "Traces cannot be generated in PicoSAT");

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
    set_vals.resize(solver->nVars(), l_Undef);

    for(const auto& x: seen) assert(x == 0);
    double start_round_time = cpuTimeTotal();
    set<uint32_t> orig_sampl_set(orig_sampl_vars.begin(), orig_sampl_vars.end());
    for(const auto& v: sampling_set) {
        if (var_to_indic[v] == var_Undef) continue;
        cl.clear();
        auto v2 = var_to_indic[v];
        Lit l2 = Lit(v2, false);
        cl.push_back(l2);
        solver->add_clause(cl);
        cl_map[cl_num++] = cl;
        picosat_add(ps, lit_to_pl(l2));
        picosat_add(ps, 0);
        set_vals[l2.var()] = l_True;
    }

    // Already replaced
    auto binx = solver->get_all_binary_xors();
    set<uint32_t> no_need;
    for(const auto& p: binx) no_need.insert(p.first.var());
    auto setl = solver->get_zero_assigned_lits();
    for(const auto& p: setl) no_need.insert(p.var());

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (no_need.count(i)) continue;
        if (solver->removed_var(i)) continue;
        if (orig_sampl_set.count(i)) continue;
        unknown.push_back(i);
    }

    sort_unknown(unknown);
    verb_print(1,"[arjun] Start unknown size: " << unknown.size());
    uint32_t sat = 0;

    vector<Lit> assumptions;
    while(!unknown.empty()) {
        uint32_t test_var = unknown.back();
        unknown.pop_back();

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

        if (ret == l_False) verb_print(5, "[arjun] extend solve(): False");
        else if (ret == l_True) {verb_print(5, "[arjun] extend solve(): True");sat++;}
        else if (ret == l_Undef) verb_print(5, "[arjun] extend solve(): Undef");

        if (ret == l_False) {
            // Dependent fully on `indep`
            // TODO: run get_conflict and then we know which were
            // actually needed, so we can do an easier generation/check
            generate_picosat(assumptions, test_var);
            cl.clear();
            Lit l(indic, false);
            cl.push_back(l);
            solver->add_clause(cl);
            cl_map[cl_num++] = cl;
            picosat_add(ps, lit_to_pl(l));
            picosat_add(ps, 0);
            set_vals[indic] = l_True;

            sampling_set.push_back(test_var);
        } else {
            set_vals[indic] = l_Undef;
        }
        set_vals[test_var] = l_Undef;
        set_vals[test_var+orig_num_vars] = l_Undef;
    }
    picosat_reset(ps);
    verb_print(1, "defined via Padoa: " << sampling_set.size()-orig_sampling_vars.size()
            << " SAT: " << sat
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();
}

void Common::generate_picosat(const vector<Lit>& assumptions, uint32_t test_var) {
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
    seen.resize(indic_to_var.size()*2, 0);
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
        f << "c num inputs: " << sampling_set.size() << endl;
        f << "c inputs: "; for(const auto& l: sampling_set) f << (l+1) << " "; f << endl;
        for(const auto& c: mini_cls) f << c << " 0" << endl;
        f.close();
    }

    // picosat on the core only, on a simplified CNF
    PicoSAT* ps2 = picosat_init();
    pret = picosat_enable_trace_generation(ps2);
    release_assert(pret != 0 && "Traces cannot be generated in PicoSAT");
    for(uint32_t i = 0; i < orig_num_vars*2; i++) picosat_inc_max_var(ps2);
    for(const auto& c: mini_cls) {
        for(const auto& l: c) picosat_add(ps2, lit_to_pl(l));
        picosat_add(ps2, 0);
    }
    for(const auto& l: assumptions) {
        /* cl_map[cl_num++] = vector<Lit>{l}; */
        picosat_assume(ps2, lit_to_pl(l));
    }
    pret = picosat_sat(ps2, 10000000);
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
    if (debug_core) {
        std::stringstream name;
        name << "proof-" << test_var+1 << ".trace";
        FILE* trace = fopen(name.str().c_str(), "w");
        picosat_write_extended_trace (ps2, trace);
    }
    TraceData dat;
    dat.data = (int*)malloc(1024*sizeof(int));
    dat.size = 0;
    dat.capacity = 1024;
    picosat_write_extended_trace_data (ps2, &dat);
    cout << "c [arjun] Proof size: " << dat.size << endl;
    free(dat.data);
    picosat_reset(ps2);
}


// TODO; This is confluent!! We can just mess up the SAT solver
// and ONLY have to use assumption for the indic + var + NOT var
void Common::extend_round()
{
    assert(already_duplicated);
    solver->set_verbosity(0);
    add_all_indics();

    for(const auto& x: seen) assert(x == 0);
    double start_round_time = cpuTimeTotal();
    double my_time = cpuTime();
    set<uint32_t> indep(sampling_set.begin(), sampling_set.end());
    vector<Lit> cl;
    for(const auto& v: indep) {
        if (var_to_indic[v] == var_Undef) continue;
        cl.clear();
        cl.push_back(Lit(var_to_indic[v], false));
        solver->add_clause(cl);
    }

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (indep.count(i)) continue;
        if (solver->removed_var(i)) continue;
        unknown.push_back(i);
    }

    sort_unknown(unknown);
    verb_print(1,"[arjun] Start unknown size: " << unknown.size());

    vector<Lit> assumptions;
    uint32_t iter = 0;
    uint32_t ret_false = 0;
    uint32_t ret_true = 0;
    uint32_t ret_undef = 0;
    while(!unknown.empty()) {
        uint32_t test_var = unknown.back();
        unknown.pop_back();

        assert(test_var < orig_num_vars);
        verb_print(5, "Testing: " << test_var);

        //Assumption filling
        assert(test_var != var_Undef);
        fill_assumptions_extend(assumptions, indep);
        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        solver->set_max_confl(conf.backw_max_confl);
        ret = solver->solve(&assumptions);
        if (ret == l_False) {
            ret_false++;
            verb_print(5, "[arjun] extend solve(): False");
        } else if (ret == l_True) {
            ret_true++;
            verb_print(5, "[arjun] extend solve(): True");
        } else if (ret == l_Undef) {
            verb_print(5, "[arjun] extend solve(): Undef");
            ret_undef++;
        }

        if (ret == l_Undef) {
            // Timed out, we'll treat is as unknown
            assert(test_var < orig_num_vars);
        } else if (ret == l_True) {
            // Not fully dependent
        } else if (ret == l_False) {
            // Dependent fully on `indep`
            indep.insert(test_var);
            cl.clear();
            cl.push_back(Lit(var_to_indic[test_var], false));
            solver->add_clause(cl);
        }

        if (conf.verb >= 5) {
            cout
            << "c [arjun] iter: " << std::setw(5) << iter;
            cout
            << " T/F/U: ";
            std::stringstream ss;
            ss << ret_true << "/" << ret_false << "/" << ret_undef;
            cout << std::setw(10) << std::left << ss.str() << std::right;
            ret_true = 0;
            ret_false = 0;
            ret_undef = 0;
            cout
            << " by: " << std::setw(3) << 1
            << " U: " << std::setw(7) << unknown.size()
            << " I: " << std::setw(7) << indep.size()
            << " X: " << std::setw(7) << ret_false
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - my_time) << endl;
            my_time = cpuTime();
        }
        iter++;

    }
    sampling_set.clear();
    sampling_set.insert(sampling_set.begin(), indep.begin(), indep.end());

    verb_print(1, "[arjun] extend round finished "
            << " final size: " << indep.size()
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();
}
