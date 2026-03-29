# Plan: Strengthen Manthan Repair to Decrease Error Faster

## Context

The Manthan repair loop is a CEGAR (counterexample-guided abstraction refinement) loop. Each iteration:
1. Finds **one** counterexample (input assignment where F(x,y_hat) is violated)
2. Repairs variables whose y != y_hat for that counterexample
3. Each repair wraps the formula in `ITE(NOT_conflict, constant(ctx[y_rep]), old_formula)`

The error count decreases monotonically but slowly because each iteration only handles **one counterexample**, and each repair's ITE branch uses a **constant** value, covering only the input-space region where the conflict condition holds.

The conflict is already minimized via UNSAT core + `minimize_conflict()`, so single-counterexample generalization is already near-optimal. The gains must come from **using information from multiple counterexamples** and/or **richer repair functions**.

## Assessment: Why the decrease is slow

1. **One counterexample per iteration**: The CEX solver finds one satisfying assignment. The repair only guarantees correctness for inputs "near" that one assignment (where the conflict condition matches).

2. **Constant repair value**: `ITE(cond, CONSTANT, old)` can only fix errors where the correct output equals that one constant. Inputs in the same conflict region but needing the opposite value are not fixed.

3. **No cross-counterexample learning**: Each repair is independent -- no information from previous counterexamples informs the current repair beyond the formula itself growing.

## Proposed Improvements (ranked by expected impact / feasibility)

### 1. Multi-counterexample generalized repair (High impact, Medium complexity)

**Idea**: Before repairing, collect k counterexamples. Find the common input values across them. Use only the common values as assumptions in `find_conflict`, leaving differing inputs free. This produces a **weaker conflict** that's valid for all k counterexamples simultaneously.

**Why this helps**: If 5 counterexamples agree on inputs {x1=T, x3=F} but differ on {x2, x4, x5}, freeing {x2, x4, x5} means the repair covers all 2^3 = 8 combinations, not just the 5 specific ones. The conflict will be even more general.

**Implementation**:
- In the outer loop, after `get_counterexample(ctx1)`:
  - Add temporary blocking clause for ctx1's input assignment
  - Call `cex_solver.solve()` up to k-1 more times to get ctx2..ctxk
  - Remove blocking clauses
- Compute `common_inputs` = {x : ctx1[x] == ctx2[x] == ... == ctxk[x]}
- For each y needing repair: check if correct value is the same across all cex
  - If yes: call modified `find_conflict` that only assumes `common_inputs`
  - If UNSAT: great, generalized repair
  - If SAT: fall back to single-cex repair

**Files to modify**: `manthan.cpp` (outer repair loop ~L848, `find_conflict` ~L1014)

### 2. Input don't-care probing (Medium impact, Low complexity)

**Idea**: After getting a counterexample, explicitly probe which inputs are don't-cares by testing if the counterexample holds with each input flipped. Don't assume don't-care inputs in `find_conflict`.

**Why this is different from UNSAT core minimization**: The UNSAT core tells us which inputs the *proof* needed. But an input might be in the proof yet still be a don't-care for the *counterexample* -- the proof just happened to use it. By not assuming it upfront, the solver is forced to find a proof that doesn't depend on it.

**Implementation**:
- After `get_counterexample(ctx)`, for each input x_i:
  - Flip x_i in ctx, re-evaluate y_hat values
  - If still a counterexample for the same y-vars with same correct values: mark x_i as don't-care
- In `find_conflict`, skip assumptions for don't-care inputs
- If result is SAT, progressively add back don't-cares until UNSAT

**Probing cost**: One formula evaluation per input variable (cheap if done via AIG/ternary sim, moderate if via SAT).

**Files to modify**: `manthan.cpp` (`find_conflict` ~L1014, add probing function)

### 3. Non-constant repair branch via dual-counterexample (High impact, Medium-High complexity)

**Idea**: Currently `ITE(cond, CONSTANT, old)`. If we have two counterexamples in the same conflict region needing **opposite** values for y_rep, instead of a constant, use a small distinguishing function.

**Implementation**:
- When collecting multiple counterexamples (from idea 1), if two cex need opposite values of y_rep:
  - Find an input variable that distinguishes them (differs between the two)
  - Use `ITE(cond, ITE(x_distinguisher, val1, val2), old)` -- a 1-variable function instead of a constant
  - This doubles the coverage of each repair

**Files to modify**: `manthan.cpp` (`perform_repair` ~L1158)

### 4. Smarter counterexample selection (Medium impact, Low complexity)

**Idea**: Instead of taking the first counterexample the SAT solver returns, bias toward counterexamples with fewer needs_repair variables or more don't-care inputs.

**Implementation**:
- Find k counterexamples (using blocking as in idea 1)
- Score each by: fewer needs_repair vars, more common inputs with others
- Pick the best one as the primary repair target

**Files to modify**: `manthan.cpp` (outer loop)

## Recommended Implementation Order

**Phase 1** (biggest bang for the buck): Ideas 1 + 2 together
- Collect multiple cex, identify common inputs, probe don't-cares
- Modified `find_conflict` with partial input assumptions
- Fallback to current behavior when generalized approach gives SAT

**Phase 2** (if Phase 1 shows promise): Idea 3
- Non-constant repair for conflicting counterexample pairs

## Verification

- Run `fuzz_repair.py` and compare error count sequences: the counts list should be shorter (fewer iterations to reach 0)
- Compare average decrease per iteration before/after
- Run on larger instances to measure wall-clock speedup
- Ensure monotonic decrease is preserved (the generalized repair is still sound)
