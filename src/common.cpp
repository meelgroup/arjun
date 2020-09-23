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

void Common::print_indep_set()
{
    cout << "vp ";
    for(const uint32_t s: *sampling_set) {
        cout << s+1 << " ";
    }
    cout << "0" << endl;

//     cout << "c inc ";
//     for(const uint32_t s: *sampling_set) {
//         cout << incidence[s] << " ";
//     }
//     cout << "0" << endl;

    cout << "c set size: " << std::setw(8)
    << sampling_set->size()
    << " fraction of original: "
    <<  std::setw(6) << std::setprecision(4)
    << (double)sampling_set->size()/(double)orig_samples_set_size
    << endl << std::flush;
}


void Common::update_sampling_set(
    const vector<uint32_t>& unknown,
    const vector<char>& unknown_set,
    const vector<uint32_t>& indep
)
{
    other_sampling_set->clear();
    for(const auto& var: unknown) {
        if (unknown_set[var]) {
            other_sampling_set->push_back(var);

        }
    }
    for(const auto& var: indep) {
        other_sampling_set->push_back(var);
    }
    //TODO: atomic swap
    std::swap(sampling_set, other_sampling_set);

}


void Common::init_samping_set(bool recompute)
{
    if (sampling_set->empty() || recompute) {
        if (recompute && !sampling_set->empty()) {
            cout << "c [mis] WARNING: recomputing independent set even though" << endl;
            cout << "c [mis]          a sampling/independent set was part of the CNF" << endl;
            cout << "c [mis]          orig sampling set size: " << sampling_set->size() << endl;
        }

        if (sampling_set->empty()) {
            cout << "c [mis] No sample set given, starting with full" << endl;
        }
        sampling_set->clear();

        vector<Lit> already_assigned = solver->get_zero_assigned_lits();
        for (Lit l: already_assigned) {
            seen[l.var()] = 1;
        }

        //Only set up for sampling if it's not already set
        for (size_t i = 0; i < solver->nVars(); i++) {
            if (seen[i] == 0) {
                sampling_set->push_back(i);
            }
        }

        //Clear seen
        for (Lit l: already_assigned) {
            seen[l.var()] = 0;
        }
    }

    if (sampling_set->size() > 100) {
        cout
        << "c [mis] Sampling var set contains over 100 variables, not displaying"
        << endl;
    } else {
        cout << "c [mis] Sampling set: ";
        for (auto v: *sampling_set) {
            cout << v+1 << ", ";
        }
        cout << endl;
    }
    cout << "c [mis] Orig size         : " << sampling_set->size() << endl;
}

void Common::add_fixed_clauses()
{
    dont_elim.clear();
    var_to_indic.clear();
    var_to_indic.resize(orig_num_vars, var_Undef);
    indic_to_var.clear();
    indic_to_var.resize(solver->nVars(), var_Undef);

    //Indicator variable is TRUE when they are NOT equal
    for(uint32_t var: *sampling_set) {
        //(a=b) = !f
        //a  V -b V  f
        //-a V  b V  f
        //a  V  b V -f
        //-a V -b V -f
        solver->new_var();
        uint32_t this_indic = solver->nVars()-1;
        //torem_orig.push_back(Lit(this_indic, false));
        var_to_indic[var] = this_indic;
        dont_elim.push_back(Lit(this_indic, false));
        indic_to_var.resize(this_indic+1, var_Undef);
        indic_to_var[this_indic] = var;

        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,      false));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,      false));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               false));
        tmp.push_back(Lit(var+orig_num_vars, false));
        tmp.push_back(Lit(this_indic,      true));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var,               true));
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(this_indic,      true));
        solver->add_clause(tmp);
    }

    if (!conf.force_by_one) {
        //This is a single clause: indic1 V indic2 V ... indicN V mult_or_invers_var
        tmp.clear();
        solver->new_var();
        mult_or_invers_var = solver->nVars()-1;
        dont_elim.push_back(Lit(mult_or_invers_var, false));
        tmp.push_back(Lit(mult_or_invers_var, false));
        for(uint32_t var = 0; var < var_to_indic.size(); var++) {
            uint32_t indic = var_to_indic[var];
            if (indic == var_Undef)
                continue;

            tmp.push_back(Lit(indic, false));
        }
        solver->add_clause(tmp);
    }

    //This is a set of clauses where k1..kN are new indicators:
    // a1 V -k1
    //-b1 V -k1
    // --> i.e. if a1=False or b1=True --> k1 is False
    // --> one of the ks must be TRUE
    //k1 V k2 V ... kN
    vector<Lit> tmp2;
    for(uint32_t var: *sampling_set) {
        solver->new_var();
        uint32_t k = solver->nVars()-1;
//         dont_elim.push_back(Lit(k, false));

        tmp.clear();
        tmp.push_back(Lit(var, false));
        tmp.push_back(Lit(k, true));
        solver->add_clause(tmp);

        tmp.clear();
        tmp.push_back(Lit(var+orig_num_vars, true));
        tmp.push_back(Lit(k, true));
        solver->add_clause(tmp);

        tmp2.push_back(Lit(k, false));
    }
    solver->add_clause(tmp2);

    //Don't eliminate the orignial variables
    for(uint32_t i = 0; i < orig_num_vars; i ++) {
        dont_elim.push_back(Lit(i, false));
        dont_elim.push_back(Lit(i+orig_num_vars, false));
    }
}

void Common::init_solver_setup(bool init_sampling, string fname)
{
    saved_fname = fname;
    delete solver;
    double myTime = cpuTime();
    solver = new SATSolver();
    if (conf.verb > 2) {
        solver->set_verbosity(conf.verb-2);
    }
    solver->set_up_for_arjun();
    if (!conf.bve) {
        solver->set_no_bve();
    }
    solver->set_intree_probe(conf.intree);
    solver->set_distill(conf.distill);

    //Read in file and set sampling_set in case we are starting with empty
    readInAFile(fname.c_str(), 0, init_sampling);
    if (init_sampling) {
        seen.clear();
        seen.resize(solver->nVars(), 0);
        init_samping_set(conf.recompute_sampling_set);
    }
    orig_num_vars = solver->nVars();
    if (sampling_set->size() > 0) {
        orig_samples_set_size = sampling_set->size();
    } else {
        orig_samples_set_size = orig_num_vars;
    }
    simp();
    incidence = solver->get_var_incidence();

    //Read in file again, with offset
    readInAFile(fname.c_str(), orig_num_vars, false);
    solver->set_intree_probe(false);

    //Add the connection clauses, indicator variables, etc.
    add_fixed_clauses();

    //Seen needs re-init, because we got new variables
    seen.clear();
    seen.resize(solver->nVars(), 0);

    //Print stats
    cout << "c [mis] CNF read-in time: " << (cpuTime()-myTime) << endl;
}

void Common::readInAFile(const string& filename, uint32_t var_offset, bool get_sampling_set)
{
    #ifndef USE_ZLIB
    FILE * in = fopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<FILE*, FN>, SATSolver > parser(solver, NULL, 0);
    #else
    gzFile in = gzopen(filename.c_str(), "rb");
    DimacsParser<StreamBuffer<gzFile, GZ>, SATSolver> parser(solver, NULL, 0);
    #endif

    if (in == NULL) {
        std::cerr
        << "ERROR! Could not open file '"
        << filename
        << "' for reading: " << strerror(errno) << endl;

        std::exit(-1);
    }

    if (!parser.parse_DIMACS(in, false, var_offset)) {
        exit(-1);
    }
    if (get_sampling_set) {
        *sampling_set = parser.sampling_vars;
    }

    #ifndef USE_ZLIB
        fclose(in);
    #else
        gzclose(in);
    #endif
}
