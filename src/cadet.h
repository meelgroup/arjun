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

    // Phase E: complete-the-synthesis pass. Unlike Phase A/B (which reset
    // skol[] and only run when Phase C+D committed nothing), Phase E
    // RESPECTS Phase C+D's prior commits by Tseitin-encoding them into a
    // fresh SAT solver, then enumerates input patterns via SAT model
    // search to fill in tables for the still-undet vars. SAT models
    // automatically satisfy the Tseitin constraints, so the values
    // collected for the undet y's are jointly consistent with everything
    // already committed.
    //
    // Enumeration bound is the same as Phase A (|orig_sampl_cnf| <= 16),
    // but Phase E ADDS to the partial state rather than starting over.
    // This is what makes "--cadet 1" useful when Phase C+D committed
    // some vars but not all: previously the only choice was Manthan
    // handoff; now Phase E finishes locally when feasible.
    bool synth_complete_with_models();

    // Phase C+D: incremental determinization (CADET's signature).
    //
    // Phase C — unique-consequence propagation. For each undetermined
    // to_define var y, iterate over the clauses mentioning y. When
    // every other literal in a clause is already a function of inputs /
    // earlier-determined vars, the clause forces y to a specific value
    // over the "forced region" (where all other literals are false).
    // Accumulating the positive-force region over all positive-y
    // clauses gives a candidate Skolem.
    //
    // Phase D — decisions. When Phase C reaches a fixpoint with vars
    // still undetermined, pick the undetermined var with the fewest
    // clauses (least-constrained = least likely to need a non-constant
    // function) and commit a constant Skolem chosen by SAT: try
    // y=false first, fall back to y=true if F+y=false is unsat under
    // the running solver state. This is CADET's "decision" step.
    //
    // What's MISSING vs full CADET: conflict analysis. Real CADET, on
    // an inconsistent decision, derives a learnt clause that prunes
    // the relevant input region and backtracks. Here we accept the
    // decision at face value and rely on:
    //   (a) the synthesis precondition (F satisfiable for every input)
    //       making most decisions sound,
    //   (b) the SAT-based test in Phase D rejecting decisions that
    //       are constant-unsat under the running state,
    //   (c) the per-commit cycle check from Phase C catching
    //       structural cycles,
    //   (d) Phase B / Phase A as fallbacks if Phase C+D produces a
    //       Skolem that fails downstream verification.
    //
    // Returns true iff every to_define var was determinized.
    bool synth_by_propagation();

    // Phase B: connected-component enumeration. The CNF clause graph,
    // treating already-determined vars (orig sampling + extend-defined +
    // backward-defined) as opaque sinks, partitions the to_define vars
    // into connected components. Each component carries its own
    // restricted set of "input" sinks; we Phase-A-enumerate each
    // component over its restricted inputs only.
    //
    // Why a whole component at once (not one y at a time): the to_define
    // vars in a component are jointly determined by F restricted to that
    // component. Synthesizing them one at a time would let the SAT
    // solver pick mutually-inconsistent values across calls.
    //
    // Why this scales: when F decomposes into many small components,
    // each component's enumeration is 2^(small). The full-input
    // exponential blowup (Phase A) only hits monolithic CNFs.
    bool synth_by_components();

    // Compute the connected component (of the CNF clause graph, with
    // sinks at `stop_set` boundaries) containing `seed_var`. Output is
    // split into:
    //   - support_out: orig sampling vars reached (sinks; the component's
    //     "inputs")
    //   - to_def_out: to_define vars in the component (Skolems to build)
    //   - clauses_out: clause indices that lie entirely inside the
    //     component (their literals are subsumed by support ∪ to_def ∪
    //     other stop_set members) — i.e. the clauses to satisfy. Each
    //     clause index that touches the component is included.
    void collect_component(uint32_t seed_var,
                           const std::set<uint32_t>& stop_set,
                           const std::vector<std::vector<uint32_t>>& var_to_clauses,
                           std::vector<uint32_t>& support_out,
                           std::vector<uint32_t>& to_def_out,
                           std::vector<uint32_t>& clauses_out) const;

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
