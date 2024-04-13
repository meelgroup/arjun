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
    vector<Lit> tmp;
    for(uint32_t var = 0; var < orig_num_vars; var++) {
        // Already has an indicator variable
        if (var_to_indic[var] != var_Undef) continue;
        if (solver->removed_var(var)) {
            var_to_indic[var] = var_Undef;
            continue;
        }

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

void Common::generate_picosat(const vector<Lit>& assumptions, uint32_t test_var) {
    verb_print(2, "generating unsat proof for: " << test_var+1);
    // FIRST, we get an UNSAT core
    PicoSAT* ps = picosat_init();
    int pret = picosat_enable_trace_generation(ps);
    release_assert(pret != 0 && "Traces cannot be generated in PicoSAT");
    map<uint32_t, vector<Lit>> cl_map;
    uint32_t cl_num = 0;

    solver->start_getting_constraints(false);
    bool ret = true;
    vector<Lit> cl;
    bool is_xor, rhs;
    for(uint32_t i = 0; i < solver->nVars(); i++) picosat_inc_max_var(ps);
    while(ret) {
        ret = solver->get_next_constraint(cl, is_xor, rhs);
        if (!ret) break;
        assert(!is_xor); assert(rhs);
        cl_map[cl_num++] = cl;
        for (const auto& l: cl) picosat_add(ps, lit_to_pl(l));
        picosat_add(ps, 0);
    }
    solver->end_getting_constraints();
    for(const auto& v: sampling_set) {
        if (var_to_indic[v] == var_Undef) continue;
        auto l = Lit(var_to_indic[v], false);
        cl_map[cl_num++] = vector<Lit>{l};
        picosat_add(ps, lit_to_pl(l));
        picosat_add(ps, 0);
    }
    for(const auto& l: assumptions) {
        cl_map[cl_num++] = vector<Lit>{l};
        picosat_add(ps, lit_to_pl(l));
        picosat_add(ps, 0);
    }
    pret = picosat_sat(ps, 10000000);
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

    // NEXT we extract information we'll need to make simplified UNSAT core
    // in particular, we'll make sure that variables that are equivalent are
    // not represented as two different variables
    map<uint32_t, uint32_t> indic_map;
    map<uint32_t, lbool> set_vals;
    for(const auto& m: cl_map) {
        if (picosat_coreclause(ps, m.first)) {
            if (m.second.size() != 1) continue;
            Lit l = m.second[0];
            set_vals[l.var()] = l.sign() ? l_False : l_True;
            if (l.var() < indic_to_var.size() && indic_to_var[l.var()] != var_Undef) {

                verb_print(5, "indic: " << l << " indidates var: " << indic_to_var[l.var()]+1 << " is equivalent to " << indic_to_var[l.var()]+orig_num_vars+1);
                verb_print(5, "replacing var: " << indic_to_var[l.var()]+orig_num_vars << " with " << indic_to_var[l.var()]+1);
                /* indic_map[l.var()] = indic_to_var[l.var()]; */
                indic_map[indic_to_var[l.var()]+orig_num_vars] = indic_to_var[l.var()];
            }
        }
    }

    // NEXT we generate the small CNF that is UNSAT and is simplified
    // TODO: simplify away the SET values of x && \neg x
    vector<vector<Lit>> mini_cls;
    seen.resize(indic_to_var.size(), 0);

    for(const auto& m: cl_map) {
        if (picosat_coreclause(ps, m.first)) {
            bool indic = false;
            bool taut = false;
            cl = m.second;
            cl.clear();
            for(auto l: m.second) {
                if (set_vals.count(l.var())) {
                    int val = set_vals[l.var()] == l_True;
                    val ^= l.sign();
                    if (val) goto end; //satisfied clause
                    continue; // false value in clausee
                }
                if (indic_map.count(l.var())) l = Lit(indic_map[l.var()], l.sign());
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

    // Write the CORE file
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
    picosat_reset(ps);

    // picosat on the core only, on a simplified CNF
    ps = picosat_init();
    pret = picosat_enable_trace_generation(ps);
    release_assert(pret != 0 && "Traces cannot be generated in PicoSAT");
    for(uint32_t i = 0; i < orig_num_vars*2; i++) picosat_inc_max_var(ps);
    for(const auto& c: mini_cls) {
        for(const auto& l: c) picosat_add(ps, lit_to_pl(l));
        picosat_add(ps, 0);
    }
    pret = picosat_sat(ps, 10000000);
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
    name.str("");
    name.clear();
    name << "proof-" << test_var+1 << ".trace";
    FILE* trace = fopen(name.str().c_str(), "w");
    picosat_write_extended_trace (ps, trace);
    picosat_reset(ps);
    fclose(trace);
}

void Common::unsat_define(const vector<uint32_t>& orig_sampl_vars) {
    assert(already_duplicated);
    solver->set_verbosity(0);
    add_all_indics();

    for(const auto& x: seen) assert(x == 0);
    double start_round_time = cpuTimeTotal();
    set<uint32_t> orig_sampl_set(orig_sampl_vars.begin(), orig_sampl_vars.end());
    for(const auto& v: sampling_set) {
        if (var_to_indic[v] == var_Undef) continue;
        vector<Lit> cl;
        auto v2 = var_to_indic[v];
        cl.push_back(Lit(v2, false));
        solver->add_clause(cl);
    }

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (solver->removed_var(i)) continue;
        if (orig_sampl_set.count(i)) continue;
        unknown.push_back(i);
    }

    sort_unknown(unknown);
    verb_print(1,"[arjun] Start unknown size: " << unknown.size());

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
        assumptions.push_back(Lit(indic, false));

        assumptions.push_back(Lit(test_var, false));
        assumptions.push_back(Lit(test_var + orig_num_vars, true));

        //TODO: Actually, we should get conflict, that will make things easier
        solver->set_no_confl_needed();

        lbool ret = l_Undef;
        // TODO we probably shouldn't use this, removing.
        /* solver->set_max_confl(conf.backw_max_confl); */
        ret = solver->solve(&assumptions);

        if (ret == l_False) verb_print(5, "[arjun] extend solve(): False");
        else if (ret == l_True) verb_print(5, "[arjun] extend solve(): True");
        else if (ret == l_Undef) verb_print(5, "[arjun] extend solve(): Undef");

        if (ret == l_Undef) {
            // Timed out, we'll treat is as unknown
            assert(test_var < orig_num_vars);
        } else if (ret == l_True) {
            // Not fully dependent
        } else if (ret == l_False) {
            // Dependent fully on `indep`
            // TODO: run get_conflict and then we know which were
            // actually needed, so we can do an easier generation/check
            generate_picosat(assumptions, test_var);
            vector<Lit> cl;
            cl.push_back(Lit(indic, false));
            solver->add_clause(cl);
            sampling_set.push_back(test_var);
        }
    }
    verb_print(1, "new sampl set:" << sampling_set.size()
            << " old sampl set:" << orig_sampling_vars.size()
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();
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
    vector<uint32_t> indep = sampling_set;
    for(const auto& v: indep) seen[v] = 1;

    //Initially, all of samping_set is unknown
    vector<uint32_t> unknown;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (seen[i]) continue;
        if (solver->removed_var(i)) continue;
        unknown.push_back(i);
    }
    for(const auto& v: indep) seen[v] = 0;

    sort_unknown(unknown);
    verb_print(1,"[arjun] Start unknown size: " << unknown.size());

    vector<Lit> assumptions;
    uint32_t iter = 0;

    //Calc mod:
    uint32_t mod = 1;
    if (unknown.size() > 20 ) {
        uint32_t will_do_iters = unknown.size();
        uint32_t want_printed = 30;
        mod = will_do_iters/want_printed;
        mod = std::max<int>(mod, 1);
    }

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
            indep.push_back(test_var);
        }

        if (iter % mod == (mod-1) && conf.verb) {
            cout
            << "c [arjun] iter: " << std::setw(5) << iter;
            if (mod == 1) cout << " ret: " << std::setw(8) << ret;
            else {
                cout
                << " T/F/U: ";
                std::stringstream ss;
                ss << ret_true << "/" << ret_false << "/" << ret_undef;
                cout << std::setw(10) << std::left << ss.str() << std::right;
                ret_true = 0;
                ret_false = 0;
                ret_undef = 0;
            }
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
    sampling_set = indep;

    verb_print(1, "[arjun] extend round finished "
            << " final size: " << indep.size()
            << " T: " << std::setprecision(2) << std::fixed << (cpuTime() - start_round_time));
    if (conf.verb >= 2) solver->print_stats();
}
