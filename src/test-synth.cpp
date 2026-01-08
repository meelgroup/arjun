/*
 test-synth

 Copyright (c) 2024. All rights reserved.

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

#include <armadillo>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include "argparse.hpp"
#include "arjun.h"
#include <cryptominisat5/dimacsparser.h>
#include "cryptominisat5/solvertypesmini.h"
#include "helper.h"
#include "formula.h"
#include <random>
#include <map>

#define myopt(name, var, fun, hhelp) \
    program.add_argument(name) \
        .action([&](const auto& a) {var = std::fun(a.c_str());}) \
        .default_value(var) \
        .help(hhelp)
#define myopt2(name1, name2, var, fun, hhelp) \
    program.add_argument(name1, name2) \
        .action([&](const auto& a) {var = std::fun(a.c_str());}) \
        .default_value(var) \
        .help(hhelp)

using std::cout;
using std::endl;
using std::string;
using std::vector;
using std::unique_ptr;
using std::map;
using std::set;
using namespace ArjunNS;

int verb = 1;
int mode = 0;
int num_samples = 2;
long long seed = 42;
std::mt19937 mt;
int unsat_verif = 0;

void fill_solver_from_cnf(ArjunNS::SimplifiedCNF& cnf, SATSolver& solver) {
    solver.new_vars(cnf.nVars());
    for (const auto& clause : cnf.get_clauses()) {
        solver.add_clause(clause);
    }
}

std::pair<bool, vector<lbool>> get_random_sol(ArjunNS::SimplifiedCNF& cnf, SATSolver* solver) {
    vector<lbool> sample(cnf.nVars(), l_Undef);
    auto ret = solver->solve();
    if (ret != CMSat::l_True) {
        cout << "c [test-synth] CNF is unsat!" << endl;
        return std::make_pair(false, sample);
    }

    return std::make_pair(true, sample);
}

vector<lbool> get_random_sol(SATSolver& rnd_solver) {
    auto ret = rnd_solver.solve();
    if (ret != CMSat::l_True) {
        cout << "ERROR: CNF is UNSAT but we have already tested for that!!!" << endl;
        exit(EXIT_FAILURE);
    }
    const auto& model = rnd_solver.get_model();
    return model;
}

void assert_sample_satisfying(const vector<lbool>& sample, SATSolver& solver) {
    assert(sample.size() == solver.nVars());
    vector<Lit> assumps;
    assumps.reserve(sample.size());
    for (uint32_t v = 0; v < sample.size(); v++) {
        if (sample[v] == l_Undef) continue;
        assumps.push_back(Lit(v, sample[v] == l_False));
    }
    auto ret = solver.solve(&assumps);
    if (ret != l_True) {
        cout << "ERROR: Sample does not satisfy the CNF!" << endl;
        exit(EXIT_FAILURE);
    }
}

// Add ~F(x, y_hat) to the solver - at least one clause must be unsatisfied when using y_hat
void add_not_F_x_yhat(SATSolver& solver, const SimplifiedCNF& orig_cnf,
                      const set<uint32_t>& aig_vs,
                      map<uint32_t, uint32_t>& y_to_y_hat) {
    if (verb) cout << "c [F_x_yhat] Adding ~F(x, y_hat)..." << endl;

    vector<Lit> tmp;
    // Create variables for y_hat
    for(const auto& y: aig_vs) {
        solver.new_var();
        const uint32_t y_hat = solver.nVars()-1;
        y_to_y_hat[y] = y_hat;
        if (verb >= 2) cout << "c [~F_x_yhat]   y: " << y+1 << " -> y_hat: " << y_hat+1 << endl;
    }

    // Adds ~F(x, y_hat)
    vector<Lit> cl_indics; // if true, clause is satisfied, if false, clause is unsatisfied
    for(const auto& cl_orig: orig_cnf.get_clauses()) {
        // Replace y with y_hat in the clause
        vector<Lit> cl;
        for(const auto& l: cl_orig) {
            if (aig_vs.count(l.var())) {
                cl.push_back(Lit(y_to_y_hat.at(l.var()), l.sign()));
            } else {
                cl.push_back(l);
            }
        }

        solver.new_var();
        uint32_t v = solver.nVars()-1;
        Lit cl_indic(v, false);
        cout << "[~F_x_yhat] clause indicator: " << cl_indic << endl;
        tmp.clear();
        tmp.push_back(~cl_indic);
        for(const auto&l : cl) tmp.push_back(l);
        solver.add_clause(tmp);
        cout << "[~F(x, y_hat)] clause: " << tmp << endl;

        for(const auto&l : cl) {
            tmp.clear();
            tmp.push_back(cl_indic);
            tmp.push_back(~l);
            solver.add_clause(tmp);
            cout << "[~F(x, y_hat)] clause: " << tmp << endl;
        }
        cl_indics.push_back(cl_indic);
    }
    tmp.clear();
    for(const auto& l: cl_indics) tmp.push_back(~l); // at least one is unsatisfied
    solver.add_clause(tmp);
    cout << "[~F(x, y_hat)] at-least-one-unsat clause: " << tmp << endl;

    if (verb) cout << "c [~F(x,y_at)] with " << cl_indics.size() << " clause indicators" << endl;
}

// Fill var_to_formula by converting AIGs to CNF formulas
void fill_var_to_formula(SATSolver& solver, FHolder& fh,
                                        const SimplifiedCNF& cnf,
                                        const set<uint32_t>& aig_vars,
                                        const map<uint32_t, uint32_t>& y_to_y_hat,
                                        const set<uint32_t>& sampling_vars,
                                        map<uint32_t, FHolder::Formula>& var_to_formula) {
    if (verb) cout << "c [var-to-formula] Converting AIGs to formulas..." << endl;

    for(const auto& v_def: aig_vars) {
        FHolder::Formula f;
        const auto& aig = cnf.get_def(v_def);
        assert(aig != nullptr);

        // Create a lambda to transform AIG to CNF using the transform function
        std::function<Lit(AIGT, uint32_t, bool, const Lit*, const Lit*)> aig_to_cnf_visitor =
          [&](AIGT type, const uint32_t v, const bool neg, const Lit* left, const Lit* right) -> Lit {
            if (type == AIGT::t_const) {
                return neg ? ~fh.get_true_lit() : fh.get_true_lit();
            }

            if (type == AIGT::t_lit) {
                const Lit lit = Lit(v, neg);

                // Check if this is an input variable or needs y_to_y_hat mapping
                Lit result_lit;
                if (sampling_vars.count(lit.var())) {
                    result_lit = lit;
                } else {
                    assert(aig_vars.count(lit.var()));
                    const uint32_t y_hat = y_to_y_hat.at(lit.var());
                    result_lit = Lit(y_hat, neg);
                }
                return result_lit;
            }

            if (type == AIGT::t_and) {
                const Lit l_lit = *left;
                const Lit r_lit = *right;

                // Create fresh variable for AND gate
                solver.new_var();
                const Lit and_out = Lit(solver.nVars() - 1, false);

                // Generate Tseitin clauses for AND gate
                // and_out represents (l_lit & r_lit)
                f.clauses.push_back({~and_out, l_lit});
                f.clauses.push_back({~and_out, r_lit});
                f.clauses.push_back({~l_lit, ~r_lit, and_out});

                // Apply negation if needed
                return neg ? ~and_out : and_out;
            }
            assert(false && "Unhandled AIG type in visitor");
            exit(EXIT_FAILURE);
        };

        // Recursively generate clauses for the AIG using the transform function
        map<aig_ptr, Lit> cache;
        const Lit out_lit = AIG::transform<Lit>(aig, aig_to_cnf_visitor, cache);
        f.out = out_lit;
        f.aig = aig;
        assert(var_to_formula.count(v_def) == 0);
        var_to_formula[v_def] = f;

        if (verb >= 5) cout << "c [test-synth]   Created formula for var " << v_def+1 << " with "
                           << f.clauses.size() << " clauses, out=" << f.out << endl;
    }
    if (verb) cout << "c [test-synth] Converted " << var_to_formula.size() << " AIGs to formulas" << endl;
}

// Check if the AIGs are correct by verifying UNSAT
bool verify_aigs_correct(SATSolver& solver,
                        const set<uint32_t>& aig_vs,
                        const map<uint32_t, uint32_t>& y_to_y_hat,
                        const map<uint32_t, FHolder::Formula>& var_to_formula) {
    if (verb) cout << "c [test-synth] Verifying AIGs are correct..." << endl;

    // Inject formulas into solver (make sure it's all x & y_hat, no y!)
    for(auto& [var, form]: var_to_formula) {
        cout << "[formula] adding formula for var: " << var+1 << endl;
        /* cout << " var_to_formula[var]:" << var_to_formula.at(var).aig << endl; */
        for(auto& cl: form.clauses) {
            vector<Lit> cl2;
            for(const auto& l: cl) {
                assert(!aig_vs.count(l.var()) && "we replaced all aig vars with y_hat already!");
                cl2.push_back(l);
            }
            solver.add_clause(cl2);
            cout << "[formula] added clause: " << cl2 << endl;
        }
    }

    // Create indicator variables: ind is true when y_hat == form_out
    vector<Lit> tmp;
    map<uint32_t, uint32_t> y_hat_to_indic;
    for(const auto& y: aig_vs) {
        solver.new_var();
        const uint32_t ind = solver.nVars()-1;

        assert(var_to_formula.count(y));
        const auto& form_out = var_to_formula.at(y).out;
        const auto& y_hat = y_to_y_hat.at(y);

        y_hat_to_indic[y_hat] = ind;
        if (verb >= 3) cout << "c [test-synth]   ind: " << ind+1 << " y_hat: " << y_hat+1
                           << " form_out: " << form_out << endl;

        // when indic is TRUE, y_hat and form_out are EQUAL
        auto y_hat_l = Lit(y_hat, false);
        auto ind_l = Lit(ind, false);
        cout << "adding clauses for y_hat: " << y_hat_l << " ind: " << ind_l << " form_out: " << form_out << endl;
        tmp.clear();
        tmp.push_back(~ind_l);
        tmp.push_back(y_hat_l);
        tmp.push_back(~form_out);
        solver.add_clause(tmp);
        cout << "indic clause: " << tmp << endl;
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        solver.add_clause(tmp);
        cout << "indic clause: " << tmp << endl;

        tmp.clear();
        tmp.push_back(ind_l);
        tmp.push_back(~y_hat_l);
        tmp.push_back(~form_out);
        solver.add_clause(tmp);
        cout << "indic clause: " << tmp << endl;
        tmp[1] = ~tmp[1];
        tmp[2] = ~tmp[2];
        solver.add_clause(tmp);
        cout << "indic clause: " << tmp << endl;
    }

    // Assume all indicators are true (all y_hat must equal their computed functions)
    for(const auto& [y_hat, ind]: y_hat_to_indic) {
        tmp = {Lit(ind, false)};
        solver.add_clause(tmp);
        cout << "indic force: " << tmp << endl;
    }
    auto ret = solver.solve();
    assert(ret != l_Undef);

    if (ret == l_True) {
        if (verb) cout << "c [test-synth] RESULT: SAT - AIGs are INCORRECT (counterexample found)" << endl;
        return false;
    } else {
        assert(ret == l_False);
        if (verb) cout << "c [test-synth] RESULT: UNSAT - AIGs are CORRECT!" << endl;
        return true;
    }
}

void unsat_verify(const SimplifiedCNF& orig_cnf, const SimplifiedCNF& cnf) {
    cout << "c [test-synth] Performing UNSAT verification of AIGs" << endl;

    // Determine which variables are defined by AIGs
    set<uint32_t> aig_vs;
    for(uint32_t v = 0; v < orig_cnf.nVars(); v++) {
        if (cnf.get_def(v) != nullptr) aig_vs.insert(v);
    }
    cout << "aig_defined_vars size: " << aig_vs.size() << endl;

    assert(aig_vs.size() == orig_cnf.nVars() - orig_cnf.get_sampl_vars().size());
    assert(cnf.get_orig_sampl_vars().size() == orig_cnf.get_sampl_vars().size());

    if (aig_vs.empty()) {
        cout << "c [test-synth] WARNING: No AIG-defined variables found!" << endl;
        exit(EXIT_SUCCESS);
    }

    if (verb) {
        cout << "c [test-synth] Found " << aig_vs.size() << " AIG-defined variables" << endl;
        if (verb >= 2) {
            cout << "c [test-synth] AIG-defined variables: ";
            for(const auto& v: aig_vs) cout << v+1 << " ";
            cout << endl;
        }
    }

    // Create verification solver
    SATSolver verify_solver;
    verify_solver.new_vars(orig_cnf.nVars());
    for (const auto& clause : orig_cnf.get_clauses()) {
        cout << "adding orig clause: " << clause << endl;
        verify_solver.add_clause(clause);
    }

    // Create FHolder for formula management
    FHolder fh(&verify_solver);

    // Map from original variable to y_hat variable
    map<uint32_t, uint32_t> y_to_y_hat;

    // Step 1: Add ~F(x, y_hat)
    add_not_F_x_yhat(verify_solver, orig_cnf, aig_vs, y_to_y_hat);

    // Step 2: Fill var_to_formula with backward definitions
    map<uint32_t, FHolder::Formula> var_to_formula;
    set<uint32_t> sampling_vars(orig_cnf.get_sampl_vars().begin(), orig_cnf.get_sampl_vars().end());
    fill_var_to_formula(verify_solver, fh, cnf, aig_vs,
                                      y_to_y_hat, sampling_vars, var_to_formula);

    // Step 3: Verify AIGs are correct (should be UNSAT)
    cout << "true lit: " << fh.get_true_lit() << endl;
    bool aigs_correct = verify_aigs_correct(verify_solver, aig_vs,
                                            y_to_y_hat, var_to_formula);

    cout << "c [test-synth] ======================================" << endl;
    if (aigs_correct) {
        cout << "c [test-synth] SUCCESS: AIGs are verified CORRECT!" << endl;
        exit(EXIT_SUCCESS);
    } else {
        cout << "c [test-synth] FAILURE: AIGs are INCORRECT!" << endl;
        exit(EXIT_FAILURE);
    }
}

bool check_cnf_unsat(ArjunNS::SimplifiedCNF& orig_cnf) {
    SATSolver solver;
    fill_solver_from_cnf(orig_cnf, solver);
    auto sat = solver.solve();
    assert(sat != CMSat::l_Undef && "Solver returned undef on a CNF without assumptions");
    return sat == CMSat::l_False;
}

void randomized_sample_verify(ArjunNS::SimplifiedCNF& orig_cnf,
          ArjunNS::SimplifiedCNF& cnf) {
    SATSolver solver;
    fill_solver_from_cnf(orig_cnf, solver);
    SATSolver rnd_solver;
    fill_solver_from_cnf(orig_cnf, rnd_solver);

    rnd_solver.set_up_for_sample_counter(100);
    for(int i = 0; i < num_samples; i++) {
        auto sample = get_random_sol(rnd_solver);
        assert(sample.size() == orig_cnf.nVars());
        vector<lbool> restricted_sample(orig_cnf.nVars(), l_Undef);
        for(const auto& var : orig_cnf.get_sampl_vars()) {
            restricted_sample[var] = sample[var];
        }
        const auto extended_sample = cnf.extend_sample(restricted_sample, true);
        assert_sample_satisfying(extended_sample, solver);
    }
}

int main(int argc, char** argv) {
    argparse::ArgumentParser program = argparse::ArgumentParser("test-synth", "1.0",
            argparse::default_arguments::help);

    // Add options
    myopt2("-v", "--verb", verb, atoi, "Verbosity");
    myopt2("-m", "--mode", mode, atoi, "Field mode (0=FGenMpz, 1=FGenMpq)");
    myopt("--samples", num_samples, atoi, "Number of samples");
    myopt2("-s", "--seed", seed, atoll, "Random seed");
    program.add_argument("-u", "--unsat") \
        .action([&](const auto&) {unsat_verif = true;}) \
        .flag()
        .help("UNSAT verify, i.e. all AIGs must be present and correct");

    // Add positional argument for input file
    program.add_argument("files").remaining().help("input AIG file");

    try {
        program.parse_args(argc, argv);
    } catch (const std::exception& err) {
        std::cerr << err.what() << std::endl;
        std::cerr << program;
        return EXIT_FAILURE;
    }
    cout << "c o [test-synth] Random seed: " << seed << endl;
    cout << "c o [test-synth] Number of samples: " << num_samples << endl;
    mt.seed(seed);

    // Get input file
    vector<string> files;
    try {
        files = program.get<std::vector<std::string>>("files");
        if (files.empty()) {
            cout << "ERROR: you must provide an input file" << endl;
            return EXIT_FAILURE;
        }
        if (files.size() != 2) {
            cout << "ERROR: You MUST pass in an AIG and a CNF file" << endl;
            return EXIT_FAILURE;
        }
    } catch (std::logic_error& e) {
        cout << "ERROR: you must give 2 input files" << endl;
        return EXIT_FAILURE;
    }

    const string cnf_fname = files[0];
    const string aig_fname = files[1];

    // Create field generator
    unique_ptr<CMSat::FieldGen> fg;
    switch (mode) {
        case 0:
            fg = std::make_unique<FGenMpz>();
            break;
        case 1:
            fg = std::make_unique<FGenMpq>();
            break;
        default:
            cout << "ERROR: Unknown mode " << mode << endl;
            return EXIT_FAILURE;
    }

    // Read the original CNF file, check satisfiability
    ArjunNS::SimplifiedCNF orig_cnf(fg);
    orig_cnf.set_need_aig();
    bool all_indep = false;
    read_in_a_file(cnf_fname, &orig_cnf, all_indep, fg);

    // Read the AIG file
    SimplifiedCNF cnf(fg);
    if (verb) cout << "c [test-synth] Reading AIG file: " << aig_fname << endl;
    cnf.read_aig_defs_from_file(aig_fname);
    /* cnf.defs_invariant(); */

    if (verb) {
        cout << "c [test-synth] Successfully read AIG file" << endl;
        cout << "c [test-synth] Number of ORIG vars      : " << cnf.num_defs() << endl;
        cout << "c [test-synth] Number of ORIG sampl vars: " << cnf.get_orig_sampl_vars().size() << endl;
        cout << "c [test-synth] Number of NEW  vars      : " << cnf.nVars() << endl;
        cout << "c [test-synth] Number of sampl_vars     : " << cnf.get_sampl_vars().size() << endl;
        cout << "c [test-synth] Number of opt_sampl_vars : " << cnf.get_opt_sampl_vars().size() << endl;
        cout << "c [test-synth] Number of NEW  cls     : " << cnf.get_clauses().size() << endl;
        cout << "c [test-synth] Number of NEW  red  cls: " << cnf.get_red_clauses().size() << endl;
        cout << "c [test-synth] need_aig: " << cnf.get_need_aig() << endl;
        cout << "c [test-synth] projected: " << cnf.is_projected() << endl;
        cout << "c [test-synth] backbone_done: " << cnf.get_backbone_done() << endl;
        cout << "c [test-synth] ======================================" << endl;
        cout << "c ORIG CNF vars: " << orig_cnf.nVars() << endl;
        cout << "c ORIG CNF sampl_vars: " << orig_cnf.get_sampl_vars().size() << endl;
    }

    // Check for UNSAT
    if (check_cnf_unsat(orig_cnf)) {
        cout << "c [test-synth] Original CNF is UNSAT, exiting." << endl;
        return EXIT_SUCCESS;
    }

    if (!unsat_verif) {
        randomized_sample_verify(orig_cnf, cnf);
    } else {
        unsat_verify(orig_cnf, cnf);
    }
    cout << "c [test-synth] OK, all samples satisfied the original CNF!" << endl;
    return EXIT_SUCCESS;
}
