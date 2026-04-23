# bug_real: Manthan wrong AIG under --synthmore — progress log

## Original symptom

`/tmp/bug_real.cnf` — an 86-var CNF — produced a semantically wrong
`-final.aig` under the flag set in `/tmp/run_many.sh`. test-synth reported
many `* MISMATCH *` y vs y_hat pairs.

## Fix 1 (committed 25b410c): compose_and/compose_or helpers leak

`FHolder<T>::compose_{and,or}` created fresh SAT vars via
`solver->new_var()` but never inserted them into the caller's `helpers`
set. With `SLOW_DEBUG` on, `check_functions_for_y_vars` (the assert that
every var in a formula clause is y_hat, helper, input, or true_lit) fired
as soon as `perform_repair`'s ITE-collapse path ran. Pure bookkeeping
bug — fixing it unblocked SLOW_DEBUG so the next layer surfaced.

## Fix 2 (committed f72aac9): stale y_hat values after repair

Root cause. Commit b216dd2 (Apr 3 2026) turned
`recompute_all_y_hat_cnf(ctx)` after `perform_repair` into
```c
if (!backward_defined.empty()) recompute_all_y_hat_cnf(ctx);
```
reasoning that "without backward-defined vars, each formula only depends
on inputs and its own y_hat".

That reasoning is false for `bve_and_substitute` (manthan_base=2):

```c
// bve_and_substitute's per-clause loop
if (later_in_order(y, l.var())) {
    aig_ptr aig = get_aig(~l);   // include l as a leaf
    ...
}
```

`later_in_order(y, l)` is true when `order_val[y] > order_val[l]`, i.e.
when `l` comes EARLIER in y_order than `y`. Those earlier vars are
to_define y's — and when the AIG is later transformed via
`map_y_to_y_hat`, each such leaf becomes a y_hat. So y=5's formula
legitimately depends on y_hat_1, y_hat_3, y_hat_4.

After `perform_repair(y=3, …)` mutates `var_to_formula[3]` (via
compose_or), y_hat_3's formula-computed value shifts. But
`ctx[y_hat_5]` came from cex_solver pre-repair and now no longer matches
what the post-repair formulas compute. The next
`SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)))` in the repair loop
fires:

```
ERROR: ctx for y_hat 5: ctx has 1 but computed y_hat has 0
Assertion `incorrect.empty()' failed.
```

**Fix**: always call `recompute_all_y_hat_cnf(ctx)` after
perform_repair in the non-one-repair-per-loop path. Reverts b216dd2's
11 % speedup on backward_defined-empty workloads; correctness wins.

Possible follow-up optimization: gate on whether the formulas actually
cross-reference y_hats. const_functions never does pre-repair;
bve_and_substitute always does.

## Minimal repro (committed as `bug_real.cnf` at repo root)

```
p cnf 5 8
1 -2 -3 0
-1 2 -3 0
1 2 3 0
-1 -2 3 0
-3 4 -5 0
3 -4 -5 0
-3 -4 5 0
3 4 5 0
c t pmc
c p show 2 0
```

Two XOR-3 constraints: `(1 ⊕ 2 ⊕ 3 = 1) ∧ (3 ⊕ 4 ⊕ 5 = 1)`, only
var 2 in the projection. Reduced from a 90-clause fuzzer-generated CNF
by `scripts/cnf_delta.py` (see the commit adding both). Fuzz seed for
the original: `8042426018130559357`.

## How to re-hunt

1. Turn SLOW_DEBUG on in `src/constants.h`, `cd build && make -j12`.
2. `./fuzz_synth.py --num 100` — with SLOW_DEBUG on, any SLOW_DEBUG
   assert (including `check_functions_for_y_vars`, `ctx_y_hat_correct`,
   `check_stage("<name>")`) aborts with signal 6 and the fuzzer
   reports the reproducing seed.
3. From that seed's failing run, copy the candidate CNF out of
   `build/out/`.
4. Write a short bash oracle that runs arjun with the same flags and
   greps stdout for the specific assert string, exit 0 on hit / 1 on
   miss. `scripts/cnf_delta.py <cnf> <out.cnf> <oracle.sh>` minimizes it.

## Remaining open issue (NOT fixed by f72aac9)

`/tmp/bug_real.cnf` — the 86-var CNF from the original run_many.sh —
is still wrong WITHOUT SLOW_DEBUG after f72aac9 (test-synth reports
INCORRECT, md5 `1a8173aa`, bit-identical across 8 runs).

With SLOW_DEBUG on, behaviour becomes non-deterministic across runs:
some abort at `check_stage("manthan")`, some produce verified-correct
AIGs (md5s `724398fc` or `88e83cd4`). The determinism change suggests
the extra SLOW_DEBUG SAT-solver calls perturb the repair trajectory.

This is a separate class of bug from Fix 2 — likely still in the
repair logic but not the y_hat staleness we just fixed. Next step:
delta-debug the 86-var CNF to minimize, then investigate.

## Useful existing debug infrastructure (committed)

- `SimplifiedCNF::check_synth_funs_sat()` — full UNSAT-style miter
  check; returns -1 on correct else a var index.
- `main.cpp do_synthesis()` wraps every pipeline stage in
  `SLOW_DEBUG_DO(check_stage("<name>"))`.
- `test-synth` dumps a CEX model (inputs, y vs y_hat with MISMATCH
  flags) on miter SAT.
- `[check] / [bve-sub] / [trace]` prints in `manthan.cpp` gated to
  `verb >= 4`.
- `scripts/cnf_delta.py` + oracle-script pattern for clause-level
  delta debugging.
