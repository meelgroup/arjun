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
#include <cstdint>
#include <set>
#include <vector>
#include <memory>
#include <cryptominisat5/solvertypesmini.h>
#include <cryptominisat5/cryptominisat.h>
#include "arjun.h"
#include "config.h"
#include "metasolver.h"

class Unate {
    public:
        Unate(const ArjunInt::Config& _conf) : conf(_conf) {}
        ~Unate() = default;

        void synthesis_unate_def(ArjunNS::SimplifiedCNF& cnf);
        void synthesis_unate(ArjunNS::SimplifiedCNF& cnf);
        // Syntactic gate detection on the to_define set. Looks for pairwise
        // clause patterns that uniquely define a y-var as a small Boolean
        // function of others — no SAT calls. Patterns covered (Lagniez-
        // Marquis "Improving Model Counting by Leveraging Definability"):
        //   • binary equivalence: (¬y ∨ a) ∧ (y ∨ ¬a)        ⇒ y = a
        //   • AND-gate:           (¬y ∨ aᵢ) for each i ∧ (y ∨ ¬a₁ ∨ … ∨ ¬aₖ)
        //                                                     ⇒ y = ⋀aᵢ
        //   • OR-gate (dual)
        // Found definitions are written as AIGs and the var moves out of
        // to_define. Returns the number of vars defined.
        uint32_t synthesis_gate_def(ArjunNS::SimplifiedCNF& cnf);
        // SAT-based equivalence detection: for each pair (yᵢ, yⱼ) of
        // to-define vars (or yᵢ in to_define and xⱼ in input), test whether
        // F entails (yᵢ ↔ yⱼ) or (yᵢ ↔ ¬yⱼ). Uses CMSGen sampling to bucket
        // candidates by value-vector signature so only in-bucket pairs hit
        // the SAT path. Definitions extract as one-node AIGs (yᵢ = yⱼ or
        // yᵢ = ¬yⱼ). Returns the number of vars defined.
        uint32_t synthesis_equiv_def(ArjunNS::SimplifiedCNF& cnf, bool include_input);
    private:
        // One pass of SAT-based unate detection over the current to_define
        // set. Caller is expected to drive it in a fix-point loop, since
        // each pass's pinned units may unblock further unates in the next
        // pass via propagation. Returns the number of new units found.
        // Mutates cnf (adds unit clauses) and the unates accumulator.
        uint32_t synthesis_unate_def_pass(ArjunNS::SimplifiedCNF& cnf,
                                          std::vector<CMSat::Lit>& unates);

        ArjunInt::Config conf;
        std::set<uint32_t> input;
        std::set<uint32_t> to_define;
        std::set<uint32_t> backward_defined;

        std::vector<uint32_t> var_to_indic; // for each var, the indicator
                                            // variable in the SAT solver that is true iff the var is equal to its copy (i.e. not flipped)
        std::unique_ptr<ArjunInt::MetaSolver> setup_f_not_f(const ArjunNS::SimplifiedCNF& cnf);
};
