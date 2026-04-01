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
#include <vector>
#include <map>
#include <cstdint>
#include <cadical.hpp>
#include <tracer.hpp>

namespace ArjunInt {

struct MyTracer : public CaDiCaL::Tracer {
    MyTracer(const uint32_t _orig_num_vars, const std::set<uint32_t>& input_vars,
            const Config& _conf, std::map<CMSat::Lit, ArjunNS::aig_ptr>& _lit_to_aig,
            const ArjunNS::AIGManager& _aig_mng) :
      conf(_conf),
      aig_mng(_aig_mng),
      orig_num_vars(_orig_num_vars),
      input(input_vars),
      lit_to_aig(_lit_to_aig)
    {}

    const Config& conf;
    std::map<uint64_t, std::vector<CMSat::Lit>> cls;
    std::map<uint64_t, ArjunNS::aig_ptr> fs_clid;  // clause ID to formula
    const ArjunNS::AIGManager& aig_mng;
    ArjunNS::aig_ptr out; // Final output formula
    int32_t orig_num_vars;
    std::set<uint32_t> input;

    // AIG cache
    std::map<CMSat::Lit, ArjunNS::aig_ptr>& lit_to_aig;

    // Balanced binary tree reduction using Op (AIG::new_and or AIG::new_or).
    // Avoids deep recursion/stack overflow compared to linear left-to-right folding.
    template<ArjunNS::aig_ptr (*Op)(const ArjunNS::aig_ptr&, const ArjunNS::aig_ptr&, bool neg)>
    static ArjunNS::aig_ptr combine_balanced(std::vector<ArjunNS::aig_ptr> terms) {
        release_assert(!terms.empty());
        std::vector<ArjunNS::aig_ptr> next;
        while (terms.size() > 1) {
            next.clear();
            for (size_t i = 0; i < terms.size(); i += 2) {
                if (i + 1 >= terms.size()) next.push_back(terms[i]);
                else next.push_back(Op(terms[i], terms[i + 1], false));
            }
            terms = next;
        }
        return terms[0];
    }

    ArjunNS::aig_ptr get_aig(const CMSat::Lit l) {
      if (lit_to_aig.count(l)) return lit_to_aig.at(l);
      ArjunNS::aig_ptr aig = ArjunNS::AIG::new_lit(l);
      lit_to_aig[l] = aig;
      return aig;
    }

    ArjunNS::aig_ptr get_aig(const std::vector<CMSat::Lit>& unsorted_cl) {
      std::vector<CMSat::Lit> cl = unsorted_cl;
      std::sort(cl.begin(), cl.end());
      if (cl.empty()) return aig_mng.new_const(false);
      std::vector<ArjunNS::aig_ptr> leaves;
      leaves.reserve(cl.size());
      for (const auto& l: cl) leaves.push_back(get_aig(l));
      return combine_balanced<ArjunNS::AIG::new_or>(leaves);
    }

    void add_derived_clause (uint64_t id, bool red, const std::vector<int> & clause,
                                   const std::vector<uint64_t> & oantec) override;
    void add_original_clause (uint64_t id, bool red, const std::vector<int> & clause, bool) override;
};

class Interpolant {
public:
    Interpolant(const Config& _conf, const uint32_t num_vars) :
        conf(_conf) {
        assert(ps == nullptr);
        ps = picosat_init();
        int pret = picosat_enable_trace_generation(ps);
        release_assert(pret != 0 && "Traces cannot be generated in PicoSAT");
        defs.resize(num_vars, nullptr);
    }
    ~Interpolant() {
        picosat_reset(ps);
    }
    void fill_picolsat(uint32_t _orig_num_vars);
    void fill_var_to_indic(const std::vector<uint32_t>& var_to_indic);
    void generate_interpolant(const std::vector<CMSat::Lit>& assumptions, uint32_t test_var,
        const ArjunNS::SimplifiedCNF& cnf, const std::set<uint32_t>& input_vars);
    void add_unit_cl(const std::vector<CMSat::Lit>& cl);
    auto& get_defs() { return defs; }

    // Internal really
    CMSat::SATSolver* solver = nullptr;

private:
    void fix_up_aig(ArjunNS::aig_ptr& aig);

    // AIG cache
    std::map<CMSat::Lit, ArjunNS::aig_ptr> lit_to_aig;

    PicoSAT* ps = nullptr;
    std::map<uint32_t, std::vector<CMSat::Lit>> cl_map;
    uint32_t cl_num = 0;
    std::vector<CMSat::lbool> set_vals;
    const Config conf;
    uint32_t orig_num_vars;
    std::vector<uint32_t> var_to_indic; //maps an ORIG VAR to an INDICATOR VAR
    std::vector<ArjunNS::aig_ptr> defs; //definition of variables in terms of AIG. ORIGINAL number space
};
}
