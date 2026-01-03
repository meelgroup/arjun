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

#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include "argparse.hpp"
#include "arjun.h"
#include <cryptominisat5/dimacsparser.h>
#include "cryptominisat5/solvertypesmini.h"
#include "helper.h"
#include <random>

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
using namespace ArjunNS;

int verb = 1;
int mode = 0;
int num_samples = 10;
long long seed = 42;
std::mt19937 mt;

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

int main(int argc, char** argv) {
    argparse::ArgumentParser program = argparse::ArgumentParser("test-synth", "1.0",
            argparse::default_arguments::help);

    // Add options
    myopt2("-v", "--verb", verb, atoi, "Verbosity");
    myopt2("-m", "--mode", mode, atoi, "Field mode (0=FGenMpz, 1=FGenMpq)");
    myopt("--samples", num_samples, atoi, "Number of samples");
    myopt2("-s", "--seed", seed, atoll, "Random seed");

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
    SATSolver solver;
    SATSolver rnd_solver;
    ArjunNS::SimplifiedCNF orig_cnf(fg);
    orig_cnf.set_need_aig();
    bool all_indep = false;
    read_in_a_file(cnf_fname, &orig_cnf, all_indep, fg);
    fill_solver_from_cnf(orig_cnf, solver);
    fill_solver_from_cnf(orig_cnf, rnd_solver);
    rnd_solver.set_up_for_sample_counter(100);
    auto sat = solver.solve();
    assert(sat != CMSat::l_Undef && "Solver returned undef on a CNF without assumptions");
    if (sat == CMSat::l_False) {
        cout << "c [test-synth] WARNING: Original CNF is unsat! Returning." << endl;
        return EXIT_SUCCESS;
    }

    // Read the AIG file
    SimplifiedCNF cnf(fg);
    if (verb) cout << "c [test-synth] Reading AIG file: " << aig_fname << endl;
    cnf.read_aig_defs_from_file(aig_fname);
    cnf.defs_invariant();
    if (verb) {
        cout << "c [test-synth] Successfully read AIG file" << endl;
        cout << "c [test-synth] Number of variables: " << cnf.nVars() << endl;
        cout << "c [test-synth] Number of clauses: " << cnf.get_clauses().size() << endl;
        cout << "c [test-synth] Number of red clauses: " << cnf.get_red_clauses().size() << endl;
        cout << "c [test-synth] Number of sampl_vars: " << cnf.get_sampl_vars().size() << endl;
        cout << "c [test-synth] Number of opt_sampl_vars: " << cnf.get_opt_sampl_vars().size() << endl;
        cout << "c [test-synth] Number of AIG defs: " << cnf.num_defs() << endl;
        cout << "c [test-synth] need_aig: " << cnf.get_need_aig() << endl;
        cout << "c [test-synth] projected: " << cnf.is_projected() << endl;
        cout << "c [test-synth] backbone_done: " << cnf.get_backbone_done() << endl;
    }

    for(int i = 0; i < num_samples; i++) {
        auto sample = get_random_sol(rnd_solver);
        assert(sample.size() == orig_cnf.nVars());
        vector<lbool> restricted_sample(orig_cnf.nVars(), l_Undef);
        for(const auto& var : orig_cnf.get_sampl_vars()) {
            restricted_sample[var] = sample[var];
        }
        auto extended_sample = cnf.extend_sample(restricted_sample, true);
        assert_sample_satisfying(extended_sample, solver);
    }

    return EXIT_SUCCESS;
}
