# Manthan Improvement Ideas

## Context

The pipeline is: heavy CNF simplification (1567->358 vars, defining 1209 via
BVE) -> UNSAT extension (defines 288 more) -> backward synthesis (defines 3
more) -> **Manthan guess-and-repair on the remaining 28 variables**.

Manthan runs 3 rounds:
1. **1 sample, ML**: 0% training error (trivially), fails after 6 loops
2. **5000 samples, ML**: Training errors 30-50% on most vars, fails after 60 loops
3. **BVE-based (structural)**: Succeeds with 734 repairs over 512 loops, 2.2s

The structural approach wins. The ML approach is essentially guessing randomly
for half the variables.

---

## 1. The ML model is the wrong abstraction for this problem

Decision trees learn Shannon decompositions from random samples. But for many
Boolean functions (anything involving XOR/parity/arithmetic), decision trees
need exponential depth. The 30-50% training errors in round 2 confirm this --
for those variables, the decision tree is no better than a coin flip.

The deeper issue: by sampling F(x,y) and treating it as a supervised learning
problem, you **throw away all the structural information in the CNF**. The BVE
approach (round 3) uses clause structure and succeeds precisely because it
doesn't do that.

**Radical alternative: don't use ML at all for the initial guess.**
Instead, use the BVE/structural approach as the *primary* strategy, and use
samples only to *refine* when the structural approach produces ambiguous/large
formulas. The output already shows this is the winning strategy -- make it the
default rather than the last resort.

## 2. The repair loop builds an unbounded decision list -- it needs periodic compaction

Each `perform_repair` wraps the existing formula in an ITE:
`ITE(conflict_satisfied, constant, old_formula)`. After 734 repairs, you have
734 nested ITEs -- a decision list. This means:
- The AIG grows monotonically during repair (no simplification happens)
- The cex_solver accumulates clauses permanently (the Tseitin encoding of each
  ITE is never removed)
- Each subsequent repair gets slower (you can see rep/s dropping from ~500 to ~330)

**Idea: periodic re-synthesis from accumulated counterexamples.** 
After every K repairs, you have a truth table for the variable (from all
counterexamples seen so far). Re-synthesize a *clean* function from that truth
table (Espresso minimization, or even just retrain a fresh decision tree on the
counterexamples). Then replace the bloated ITE chain with the compact new
formula and restart the repair loop. This keeps formula size bounded and the
solver fast.

## 3. Counterexamples are massively underutilized
--> Bullshit I think. We can collect CEX-es, and see if they
are CEX-es again, but I think this is not useful.

Each counterexample gives you simultaneous information about *all 28
variables*, but you only use it to repair one (or a few) variables per loop
iteration. The information about the other variables is discarded.

**Idea: treat counterexamples as training data for future rounds.** 
Accumulate all counterexamples and periodically retrain *all* variable
functions from the union of (original samples + counterexamples).
Counterexamples are not random -- they specifically target where the current
functions are wrong, making them far more informative per-sample than uniform
samples. This could turn the repair loop into a *learning* loop.

## 4. The variable ordering should be adaptive, not fixed

Once you fix the order, a variable at position `i` can only depend on variables
at positions `< i`. If the *true* function for variable `v` requires variable
`w` but `w` comes after `v` in the order, `v` will *never* be synthesizable
correctly -- the repair loop will patch it forever with an ever-growing ITE
chain that overfits to specific counterexamples.

**Idea: detect "stuck" variables and reorder.** 
If a variable keeps needing repair (say, it appears in `needs_repair` in >50%
of loops), it's a signal the ordering is wrong for it. Promote its dependencies
or demote the variable. This is essentially CEGAR on the ordering itself.

## 5. Exploit the component structure more aggressively

Line 582 says "Found 1 components" -- but in general there could be multiple.
Even within a single connected component, there's often near-decomposability:
clusters of variables that interact densely among themselves but sparsely with
others.

**Idea: identify variable clusters and synthesize them jointly.** 
Rather than synthesizing one variable at a time in a fixed order, identify
tightly-coupled groups (e.g., via the dependency matrix or clause-variable
incidence hypergraph) and synthesize each group simultaneously. For a group of
`k` variables with `m` relevant inputs, you could build a joint BDD or use QBF
solving directly on the sub-problem. This avoids the cascading-error problem
where one variable's wrong function poisons the next.

## 6. Use interpolation for exact synthesis of "easy" variables

Before entering the expensive guess-and-repair loop, some variables may have
*exact* synthesis possible via Craig interpolation. If `F(x, y_i=0, y_rest) AND
NOT F(x, y_i=1, y_rest)` is unsatisfiable, the interpolant gives you the exact
function for `y_i`. This is already hinted at by the UNSAT extension step, but
interpolation is more general and could knock out more variables before Manthan
even starts.
