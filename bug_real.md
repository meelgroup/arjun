# bug_real: Manthan wrong AIG under --synthmore — resolved

Two distinct Manthan correctness bugs hit by `/tmp/bug_real.cnf` and
related fuzzer-generated inputs under `--synthmore`. Both now fixed.

## Fix 1 (25b410c): compose_and/compose_or helpers leak

`FHolder<T>::compose_{and,or}` in `formula.h` created fresh SAT vars
via `solver->new_var()` but never inserted them into the caller's
`helpers` set. With `SLOW_DEBUG` on, `check_functions_for_y_vars`
(every var in a formula clause must be y_hat, helper, input, or
true_lit) fired as soon as `perform_repair`'s ITE-collapse path ran.
Pure bookkeeping bug — fixing it unblocked SLOW_DEBUG so the next
layers surfaced.

## Fix 2 (f72aac9): stale y_hat values after repair

Commit `b216dd2` (Apr 3 2026) replaced
```c
recompute_all_y_hat_cnf(ctx);
```
after `perform_repair` with
```c
if (!backward_defined.empty()) recompute_all_y_hat_cnf(ctx);
```
reasoning that "without backward-defined vars, each formula only
depends on inputs and its own y_hat". That reasoning is false for
`bve_and_substitute` (manthan_base=2):

```c
// bve_and_substitute's per-clause loop
if (later_in_order(y, l.var())) {
    aig_ptr aig = get_aig(~l);   // include l as a leaf
    ...
}
```

`later_in_order(y, l)` is true when `l` comes earlier in y_order — and
those earlier vars are themselves to_define y's that get mapped to
y_hats during the AIG→CNF transform. So y=5's formula legitimately
depends on y_hat_1, y_hat_3, y_hat_4. After `perform_repair(y=3, …)`
mutates var_to_formula[3], y_hat_3's formula-computed value shifts,
and `ctx[y_hat_5]` goes stale relative to the post-repair formulas.
The next `SLOW_DEBUG_DO(assert(ctx_y_hat_correct(ctx)))` fires.

Minimal repro (committed at `bug_real.cnf`):

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

Two XOR-3 constraints: `(1 ⊕ 2 ⊕ 3 = 1) ∧ (3 ⊕ 4 ⊕ 5 = 1)`, only var 2
in the projection. Reduced from a 90-clause fuzzer-generated CNF by
`scripts/cnf_delta.py`. Fuzz seed: `8042426018130559357`.

Fix: always call `recompute_all_y_hat_cnf(ctx)` after `perform_repair`
in the non-one-repair-per-loop path. Possible follow-up optimization:
gate on whether the formulas actually cross-reference y_hats —
const_functions never does, bve_and_substitute always does.

## Fix 3 (336ac57): persistent AIGToCNF encoder across formulas

`bve_and_substitute` used a single persistent `AIGToCNF` across all
formulas, so its node-pointer-keyed `cache` could dedup helpers for
hash-consed sub-AIGs shared across formulas (via the AIG manager's
hash-consing, especially after AIGRewriter + sat_sweep rebuild the
aigs vector).

That turned out to be unsound: a cached Lit from one formula's
encoding would be reused on a later formula's cache hit, and the
cached Lit's effective value sometimes disagreed with a direct AIG
evaluation of the same node. The surface symptom on `bug_real_big.cnf`
(a 74-clause fuzzer-reduced case, since removed from the repo):
Manthan thinks it's done (`still to define: 0`, cex_solver UNSAT
against `f.clauses+f.out`) but the exported `cnf.defs` (built from
`f.aig`) violate an original clause. The CNF encoding and AIG
encoding of the same formula denote different Boolean functions.

I could not finger the exact optimization responsible — disabling
cut_cnf / detect_ite / detect_xor / kary_fusion / normalize_inputs
individually kept the bug, but using a FRESH encoder per formula (no
cross-formula cache reuse) removed it. Likely interaction between
`fanout` recomputed per `encode()` and `cache` living across
`encode()` calls, with sat_sweep's rebuild mutating the aigs between
them in ways that invalidate assumptions made at cache-store time.

Fix: allocate `AIGToCNF` inside the per-y loop. All other encoder
optimizations stay enabled. Per-formula encoding is slightly larger
(no cross-formula helper dedup) but correct.

## Debug infrastructure

Three SLOW_DEBUG miter checks now live in Manthan, each building a
fresh `SATSolver` sharing no state with `cex_solver`:

- `check_synth_via_clauses(where)` — miter using
  `var_to_formula[y].clauses+.out`. If SAT while cex_solver was
  UNSAT, cex_solver is giving wrong answers.
- `check_synth_via_aig(where)` — same miter but Tseitin the AIG
  (`var_to_formula[y].aig`) directly. If SAT while clauses-miter is
  UNSAT, .aig and .clauses+.out disagree.
- `check_aig_matches_clauses_per_formula(where)` — pairwise miter
  between .aig and .clauses+.out per y. Pinpoints the diverging
  formula.

Wired at:
- after `bve_and_substitute`,
- after every `perform_repair` (in the inner while loop),
- at the cex_solver "finished" loop exit.

Concise failure diagnostic on hit: inputs, which y, AIG type/neg,
direct AIG eval result, Lit values under the SAT model. The full
recursive AIG structure dump is gated under `VERBOSE_DEBUG` for deep
triage. Reproducer flow:

1. Uncomment `#define SLOW_DEBUG` in `src/constants.h`,
   `cd build && make -j12`.
2. `./fuzz_synth.py --num 100` — any SLOW_DEBUG assert (including
   the three above, `check_functions_for_y_vars`,
   `ctx_y_hat_correct`, `check_stage("<name>")`) aborts with signal
   6 and the fuzzer reports the reproducing seed.
3. Copy the failing CNF out of `build/out/`, write a bash oracle
   that re-runs arjun with the same flags and greps stdout for the
   assert text, `scripts/cnf_delta.py <cnf> <out.cnf> <oracle.sh>`
   to minimise it.

Also: `SimplifiedCNF::check_synth_funs_sat()` full UNSAT-style miter
on `cnf.defs`, and `main.cpp do_synthesis()` wraps each pipeline
stage in `SLOW_DEBUG_DO(check_stage("<name>"))` so a bad def gets
attributed to the specific stage that introduced it.
