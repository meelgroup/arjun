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

`bug_real_big.cnf` at the repo root (minimized via cnf_delta.py from
the original 86-var /tmp/bug_real.cnf, 269 → 74 clauses) still
produces a semantically wrong final AIG after f72aac9.

Failure pattern: manthan finishes its first repair strategy with
`repairs: 5 repair_failed: 2 still to define: 0` — it thinks it's
done — then `check_synth_funs_sat` catches a wrong def:

```
[check_synth_funs_sat] DEFS SEMANTICALLY WRONG (F ∧ ¬F[y←y_hat] SAT)
  first broken orig clause idx=14 cl=3 16 -52
    x3  (free,    val=0, lit_val=0)
    x16 (defined, y_hat=0, lit_val=0)
    x52 (defined, y_hat=1, lit_val=0)
[check_stage] WRONG def after stage 'manthan' for var 1
```

So manthan's cex_solver returned UNSAT (no CEX found) but the
resulting AIGs are actually wrong — cex_solver failed to catch the
violation of orig clause `(3 ∨ 16 ∨ ¬52)`.

Classes of hypotheses to investigate:

1. **Stale indicator clauses.** Each `perform_repair` + `inject_…`
   cycle adds a new indicator `ind_i` for y_hat_y with
   `ind_i ↔ (y_hat_y ↔ new_form_out)`, but the old `ind_{i-1}`
   clauses referring to the OLD form_out stay in cex_solver. The
   fresh `y_hat_to_indic[y_hat] = new_ind` silently abandons the
   old indicator. That's formally sound (solver can falsify the old
   indicator), but if a stale OLD form_out refers to a helper var
   that has since been reused (impossible by construction?) or that
   simplify eliminated, we could end up with a degenerate model.

2. **Cross-formula helper sharing via bve_and_substitute's
   persistent encoder.** The comment at manthan.cpp:655
   explicitly notes helpers are "attributed" to whichever formula
   first emits their defining clauses. If perform_repair's
   compose_or modifies formula Y's clauses but those helpers' defs
   live in formula Z's clause list, we could lose synchronisation
   when the old formula Y is replaced. Specifically, `cl.inserted =
   true` on old clauses means inject won't re-emit them on the new
   formula, but the helper's defining clauses are in a DIFFERENT
   formula and stay valid.

3. **`compute_needs_repair` under-reports.** After repair, the loop
   checks `needs_repair.empty()`; if this set is computed from
   ctx (which may still be stale for cascading y_hats despite Fix 2
   recomputing via SAT), we might exit the repair loop early.

Next steps: add `check_synth_funs_sat` inside the manthan repair
loop (between repairs, SLOW_DEBUG-gated) to localise which repair
breaks correctness. Delta-debug bug_real_big.cnf further with a
per-strategy oracle to shrink the 74-clause case.

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
