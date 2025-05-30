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

#pragma once

#include <cryptominisat5/solvertypesmini.h>
extern "C" {
#include <cryptominisat5/mpicosat.h>
}
#include "constants.h"
#include "arjun.h"
#include "config.h"
#include "formula.h"
#include <vector>
#include <map>
#include <cstdint>
#include <cadical.hpp>
#include <tracer.hpp>

using std::vector;
using std::map;
using namespace ArjunNS;

struct MyTracer : public CaDiCaL::Tracer {
    MyTracer(uint32_t _orig_num_vars, vector<uint32_t> _opt_sampl_vars, AIGManager* _aig_mng, const ArjunInt::Config& _conf) :
      conf(_conf),
      aig_mng(_aig_mng),
      orig_num_vars(_orig_num_vars)
    {
      input.insert(_opt_sampl_vars.begin(), _opt_sampl_vars.end());
    }
    const ArjunInt::Config& conf;
    map<uint64_t, vector<Lit>> cls;
    std::map<uint64_t, AIG*> fs_clid;  // clause ID to formula
    AIGManager* aig_mng = nullptr;
    AIG* out; // Final output formula
    int32_t orig_num_vars;
    set<uint32_t> input;

    void add_derived_clause (uint64_t id, bool red, const std::vector<int> & clause,
                                   const std::vector<uint64_t> & oantec) override;
    void add_original_clause (uint64_t id, bool red, const std::vector<int> & clause, bool) override;
};

class Interpolant {
public:
    Interpolant(const ArjunInt::Config& _conf) :
        conf(_conf) {
        assert(ps == nullptr);
        ps = picosat_init();
        int pret = picosat_enable_trace_generation(ps);
        release_assert(pret != 0 && "Traces cannot be generated in PicoSAT");
    }
    ~Interpolant() {
        picosat_reset(ps);
    }
    void fill_picolsat(uint32_t _orig_num_vars);
    void fill_var_to_indic(const vector<uint32_t>& var_to_indic);
    void generate_interpolant(const vector<Lit>& assumptions, uint32_t test_var, SimplifiedCNF& cnf);
    void add_clause(const vector<Lit>& cl);
    const AIGManager& get_aig_mng() const { return aig_mng; }
    const map<uint32_t, AIG*>& get_defs() const { return defs; }
    bool evaluate(const vector<CMSat::lbool>& vals, uint32_t test_var) {
        if (!defs.count(test_var)) {
            cout << "ERROR: Variable " << test_var+1 << " not defined by this interpolant" << endl;
            assert(defs.count(test_var) && "Don't query variables that haven't been defined, please");
            exit(-1);
        }
        return ::evaluate(vals, defs[test_var], defs);
    }

    // Internal really
    CMSat::SATSolver* solver = nullptr;

private:
    PicoSAT* ps = nullptr;
    map<uint32_t, vector<Lit>> cl_map;
    uint32_t cl_num = 0;
    vector<CMSat::lbool> set_vals;
    const ArjunInt::Config conf;
    uint32_t orig_num_vars;
    vector<uint32_t> var_to_indic; //maps an ORIG VAR to an INDICATOR VAR
    AIGManager aig_mng;
    map<uint32_t, AIG*> defs; // the definitions of the variables
};

