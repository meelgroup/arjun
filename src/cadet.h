/*
 Arjun

 cadet.h — In-tree port of CADET's incremental-determinization core (Markus
 N. Rabe, SAT 2016). Used in place of Manthan when --cadet 1 is set.

 Copyright (c) 2026, Mate Soos. All rights reserved.

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

#include "arjun.h"
#include "config.h"
#include <cryptominisat5/solvertypesmini.h>

#include <cstdint>
#include <set>
#include <vector>

namespace ArjunInt {

// Cadet — synthesis driver that mirrors Manthan's API surface but uses a
// CADET-style incremental-determinization algorithm to construct Skolem
// functions for the unsynthesized variables of a SimplifiedCNF.
//
// Like Manthan, it consumes a SimplifiedCNF where some variables are already
// synthesized (have an AIG in cnf.defs[v]) and others are not; it produces a
// SimplifiedCNF where every previously-unsynthesized variable has been
// assigned an AIG definition over the inputs and previously-synthesized
// variables. The result satisfies cnf.synth_done().
class Cadet {
public:
    Cadet(const ArjunInt::Config& _conf,
          const ArjunNS::Arjun::ManthanConf& _mconf,
          ArjunNS::SimplifiedCNF&& _cnf);

    ArjunNS::SimplifiedCNF do_cadet();

private:
    const ArjunInt::Config& conf;
    const ArjunNS::Arjun::ManthanConf& mconf;
    ArjunNS::SimplifiedCNF cnf;
    ArjunNS::AIGManager aig_mng;

    // Var partitions, mirroring Manthan's split. NB: `input` here matches
    // VarTypes.input — it lumps `extend-defined` vars (those with an AIG
    // def depending only on orig sampling vars) together with the orig
    // sampling vars themselves, since the SAT solver treats both as free
    // for synthesis purposes. The narrower "true" set of orig sampling
    // vars (cnf-numbering) is held in `orig_sampl_cnf` and is the one we
    // actually enumerate over.
    std::set<uint32_t> input;            // free + extend-defined
    std::set<uint32_t> to_define;        // vars without an AIG def — Cadet must produce one
    std::set<uint32_t> backward_defined; // vars already defined upstream
    std::set<uint32_t> orig_sampl_cnf;   // orig sampling vars in CNF numbering

    // skol[v] = Skolem function for v in terms of input vars (and previously-
    // synthesized vars). For inputs, this is the literal AIG. For backward
    // vars, this is cnf.defs[v]. For to_define vars, this starts nullptr and
    // gets filled by the algorithm.
    std::vector<ArjunNS::aig_ptr> skol;

    // --- algorithm pieces ---

    // True iff |input| <= small_input_threshold so an exhaustive table is
    // affordable. This drives the simple v1 path.
    bool inputs_are_small() const;

    // Phase A: for each y in to_define, build its Skolem by enumerating
    // every orig-sampling-var assignment, calling SAT under the assumption,
    // and reading y's value from the model. Each y's Skolem is then built
    // as a Shannon-decomposition binary tree of ITEs over the sorted
    // input vars — vastly smaller than a flat OR-of-minterms when the
    // function has structure (constant subtrees collapse).
    bool synth_by_enumeration();

    // Build a Skolem AIG from a value table by Shannon decomposition over
    // `sorted_inputs`. `table[mask]` is the y-value for the input
    // assignment whose bit i corresponds to sorted_inputs[i]. Identical
    // sibling subtrees collapse, so constants and pure-literal cases come
    // out at minimal cost.
    ArjunNS::aig_ptr build_shannon_tree(const std::vector<bool>& table,
                                        const std::vector<uint32_t>& sorted_inputs);

    // Inject the entire CNF into the given solver.
    template<typename S>
    void inject_cnf(S& s) const;

    // Set defs[v] for every v in to_define from skol[v], via map_aigs_to_orig.
    void commit_definitions();
};

} // namespace ArjunInt
