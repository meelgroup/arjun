# bug_real: Manthan produces wrong AIG under --synthmore --minimize 0

## Symptom

`/tmp/bug_real.cnf` — an 86-var CNF with 20 sampling vars — run under the
flag-set in `/tmp/run_many.sh` produces a `-final.aig` whose miter against
the orig CNF is SAT. `test-synth -u` reports many `* MISMATCH *` y vs y_hat
pairs (x2, x17, x26, x28, x29, x35, x36, …). The bug reproduces
bit-identically across 8 runs — it's deterministic, not a race.

Trigger flag combination (minimal known set):
- `--synthmore`
- `--synthbve 1` (BVE pass on)
- `--minimize 0` (skip minim-indep — keeps more vars in to_define)
- `--extend 0`
- `--mstrategy "bve(...)"` (Manthan base = bve_and_substitute)

With `--minimize 1` (default), the bug doesn't trigger — presumably because
the backward-minim round removes the specific to_define vars that expose the
inconsistency.

## Layer 1 (FIXED in 25b410c): compose_and/compose_or helpers leak

`FHolder<T>::compose_{and,or}` in `formula.h` created fresh SAT vars via
`solver->new_var()` but never inserted them into the caller's `helpers`
set. With `SLOW_DEBUG` on, `check_functions_for_y_vars` — which asserts
every var in a formula clause is y_hat, helper, input, or true_lit — fired
as soon as `perform_repair`'s ITE-collapse path (OR/AND between guard and
old formula) introduced one of these untracked vars.

This was a bookkeeping bug, not the root cause. Fixing it unblocks the
SLOW_DEBUG path so the real bug (layer 2) surfaces.

## Layer 2 (OPEN): ctx_y_hat_correct fails at iteration 1

With `SLOW_DEBUG` on, the next layer's assert fires:

```
ERROR: ctx for y_hat    27: ctx has    1 but computed y_hat has    0
Assertion `incorrect.empty()' failed.
```

This is inside `do_manthan`'s main loop, iteration 1, right after the first
`get_counterexample()` call. `ctx_y_hat_correct` builds a fresh SAT solver
with the formula clauses (in y_hat-space) and inputs pinned to `ctx[x]`,
then solves. The resulting model's `y_hat[27]` is 0. But `ctx[y_hat[27]]`
(from `cex_solver.get_model()`) is 1. Both "models" should coincide — the
formulas are Tseitin-encoded circuits, so `y_hat` is uniquely determined
by inputs.

### What I verified

Diagnostic prints confirmed:

1. The local solver's model satisfies every clause in `f.clauses`.
2. The ctx (from cex_solver) *does not* satisfy clause `13 -32 -4 -224` in
   `var_to_formula[27].clauses`. Values: `ctx[12]=0, ctx[31]=1, ctx[3]=1,
   ctx[223]=1` — all four literals FALSE → clause UNSAT in ctx.
3. Forcing `y_hat[27] = ctx value(1)` against the same inputs makes the
   local solver UNSAT. So the formulas genuinely determine `y_hat[27] = 0`
   given these inputs.
4. All formula clauses are in `cex_solver` (they're added via
   `inject_formulas_into_solver`, which loops `updated_y_funcs` =
   to_define_full on iteration 1).
5. The specific clause `13 -32 -4 -224` references vars 12 (input),
   31 (y_hat), 3 (input), 223 (helper). No var in `to_define_full` →
   no y→y_hat substitution on injection → cex_solver has the same
   literal form.
6. `cex_solver.solve()` returns `l_True`. A SAT model must satisfy all
   clauses. Yet the returned model does not.
7. Same ctx vs. `var_to_formula[27].clauses` check run inside
   `get_counterexample` (right after `get_model()`) reports viol=0.
   The same check inside `ctx_y_hat_correct` a few lines later reports
   viol=1. Same ctx reference, same formulas. This is the most suspicious
   finding — something changes between those two points but I couldn't
   pin it down with direct diagnostic.

### Current best hypothesis

`MetaSolver2::simplify(&assumps)` (called inside `get_counterexample` on
iteration 1 and periodically) may be eliminating a helper var in
cex_solver — CMS BVE — and the post-solve `get_model()` then returns a
value for the eliminated var that isn't consistent with the *visible*
clause set. If that eliminated var is a helper referenced by `f.clauses`
(like helper 215 in y=27's formula, which is shared with y=15's formula
via the persistent encoder cache in `bve_and_substitute`), the local
ctx_y_hat_correct solver (which has no BVE history) computes a different
value and they disagree.

Unverified. Would need to either trace cex_solver's internal elim
history or reproduce with CMS simplify disabled.

### What I have NOT ruled out

- The two viol-check calls genuinely see different data. Possible causes:
  some caller of `get_counterexample` re-solves cex_solver between the
  two points (but `ctx_is_sat` creates its own local solver, and
  `compute_needs_repair` / `print_cnf_debug_info` take `const sample&`).
- A build-cache issue where the two diagnostics were compiled against
  different versions of the struct layout. Low probability — same
  translation unit.

## How to repro

1. Turn SLOW_DEBUG on in `src/constants.h` (uncomment `#define SLOW_DEBUG`).
2. `cd build && make -j12`.
3. `bash /tmp/run_many.sh` — all 8 runs produce the same wrong-AIG md5sum.
4. `./test-synth -u -v 1 /tmp/bug_real.cnf /tmp/d1-final.aig` → SAT /
   INCORRECT.
5. To hit the `ctx_y_hat_correct` assert, run the single `./arjun …`
   command from `run_many.sh` directly (without the `timeout`). The
   assert fires on iter 1 of the outer repair loop.

## Useful existing debug infrastructure (committed)

- `SimplifiedCNF::check_synth_funs_sat()` — full UNSAT-style miter check,
  returns -1 on correct else a var index. Call this at any pipeline
  stage boundary.
- `main.cpp do_synthesis()` wraps every stage with
  `SLOW_DEBUG_DO(check_stage("<name>"))` — so a wrong def gets
  attributed to the stage that introduced it.
- `test-synth` dumps a CEX model (inputs, y vs y_hat with MISMATCH
  flags) when the miter is SAT.
- `[check] / [bve-sub] / [trace]` prints in `manthan.cpp` gated to
  `verb >= 4`.
