# Three serious algorithmic directions for `manthan.cpp`

## Diagnosis (from `build/data/out-synth-1570930-0`)

The death spiral on every long-tail benchmark looks the same:

```
genbuf12b4y         var  96   16264 repairs  121K AIG nodes  depth 10860
ActivityService     var 100   16300 repairs  258K AIG nodes  depth 15374
sdlx-fixpoint-7     var 1023   176 repairs   ~250 AIG nodes  depth 19
```

Every `perform_repair` call does
`compose_or(branch, old_formula)`
where `branch = AND(literals of one SAT-solver conflict)`. After K repairs the
per-variable AIG has depth ≈ K and node count ≈ K · |conflict|, and the
formula's CNF mirror grows the same way.

Three things follow:

1. **Chain blowup is the bottleneck.** On ActivityService, `recompute_y_hat`
   (`AIG::evaluate` over the chained AIG, per y, per repair) is **33.5%** of
   total time, `cex_finding` 21.6%, `find_conflict` 11.3%. All three slow
   down quadratically as the chain grows.
2. **Repairs barely generalize.** `avg rep/loop` collapses to **1.0** in the
   long tail — every CEX fixes a single corner of input space.
3. **Cost-zero ratio is huge.** ActivityService: 57,781 cost-zero "repairs"
   out of 81,377 solver calls — wasted SAT calls where the wrong y-value was
   actually fine and only the downstream y's needed updating.

The three fixes split along three orthogonal axes:
**shrink what you build**, **learn more per repair**, or
**rebuild instead of accumulating**.

---

## Option 1 — Periodic per-variable AIG compaction + lazy CNF re-encoding

### The idea

Treat the chained AIG as the source of truth and never let it grow
unboundedly. When a variable's per-formula AIG exceeds a threshold (e.g.
depth > 100 or nodes > 2000), run `AIGRewriter::rewrite_all` + `sat_sweep`
+ `rewrite_all` on it (the same passes already used in
`bve_and_substitute`), then **discard** `var_to_formula[y].clauses` /
`out` and re-Tseitin from the compacted AIG via `AIGToCNF`. Reset
`uninserted_start = 0` so `inject_formulas_into_solver` sees the new
clauses; keep the old indicator alive (or rebind via a fresh
equivalence) so `cex_solver` doesn't get confused.

### Why it should work

Most repair conflicts overlap heavily — the chained ORs accumulate
ITE-equivalent and constant-propagatable structure that the AIG rewriter
already knows how to crush. The `bve_and_substitute` log shows >40%
reduction routinely on initial AIGs; on a chain of 16k repairs the
compression is likely 10–100× because each repair conflict is a
near-duplicate of prior ones.

### Plan (~300–500 LOC)

- Add `aig_compact_threshold_depth`, `_nodes`, and
  `aig_compact_check_every` (e.g. every 100 repairs per var, or in the
  main repair loop after a CEX round) to `ManthanConf`.
- `Manthan::compact_var_formula(uint32_t y)`: take
  `var_to_formula[y].aig`, run rewriter, re-encode via a fresh
  `AIGToCNF`, replace `var_to_formula[y]` and push to `updated_y_funcs`.
- Sub-AIG dependencies: when y's AIG references other y_hats, the
  compaction is *local* — leaves are y_hat lits or input lits; that's
  already what `bve_and_substitute` does at line 979
  (`AIG::translate_leaves`).
- The compaction creates a new `f.out` (Tseitin var) — the old indicator
  (`y_hat_to_indic`) needs to be re-bound. Either drop the old indicator
  entry and call `add_not_f_x_yhat`-style fresh, or wrap with an
  equivalence clause `new_out ↔ old_out`.

### Risk

Indicator lifecycle is the only landmine — there's a `SLOW_DEBUG` check
(`check_aig_matches_clauses_per_formula`) that will catch divergence
loudly. Otherwise low: it's a representation transformation, not an
algorithm change.

### Expected impact

Directly attacks the 33%+ `recompute_y_hat` cost and the
linear-in-repairs growth. Probably wins ~10–20 of the timeout instances
where Manthan was making real progress but drowning in formula bloat
(sdlx-fixpoint-{4,5,6,7}, ActivityService, factorization).

---

## Option 2 — Craig-interpolant repair clauses

### The idea

Replace "the SAT conflict" as the repair clause with a **Craig
interpolant** computed over the input variables only.

When `find_conflict` returns UNSAT, the proof is a refutation of
`(F(x,y) ∧ y_others = ctx[y_others] ∧ y_rep = ¬ctx[y_rep])` plus
assumptions on the inputs. Partition (A, B) for the McMillan
interpolant:

- A = `F(x,y) ∧ y_others = ctx[y_others] ∧ y_rep = ¬ctx[y_rep]`
- B = `x = ctx[x]` (the input assumptions)

Shared variables = input variables. The interpolant `I(x)` satisfies:

- `A → I(x)` — captures the entire region of inputs for which flipping
  `y_rep` is feasible (i.e. where the current value is *required*).
- `I(x) ∧ B` is UNSAT — the original CEX input is excluded.

So the **repair function** to add is:

```
if ctx[y_rep] = TRUE :  y_rep_func ← y_rep_func OR  (¬I(x))
if ctx[y_rep] = FALSE:  y_rep_func ← y_rep_func AND  I(x)
```

Today we do `compose_or` with `AND(literals of one corner)`. Tomorrow we
do `compose_or` with the interpolant AIG, which typically subsumes
thousands of would-be conflict clauses.

### Why it should work

The "1 repair per loop, repeated 16k times" pattern is the textbook
symptom of conflict-clause learning vs interpolant-based learning.
IC3/PDR moved from clausal blocking to interpolant-style inductive
frames for exactly this reason. Each repair would now generalize to a
region rather than a singleton.

### Plan (~1500 LOC, harder)

There is already an `Interpolant` infrastructure in `src/interpolant.h`
/ `interpolant.cpp` that we use in `backward.cpp` for the
doubled-variable equivalence trick (Bonacina-Ghilardi). We can adapt
it: it already uses CaDiCaL with a `Tracer` (`MyTracer`) that consumes
proof antecedents on the fly and folds them into a McMillan
interpolant AIG.

- Pick interpolation backend: reuse the existing `MyTracer` /
  `Interpolant` (uses CaDiCaL's antecedent-tracking
  `connect_proof_tracer`). Lower risk than a from-scratch DRAT pass.
- Build a **mirror cadical solver** whose state matches `repair_solver`
  (same input clauses, same cumulative learned formula clauses), with
  proof tracing on. When `find_conflict` returns UNSAT, replay the same
  assumptions on the mirror, fetch the interpolant AIG.
- Pass the interpolant AIG into `perform_repair` as a precomputed
  branch; `compose_or/and` are unchanged.
- SLOW_DEBUG: check that `I(ctx[x]) = FALSE` and that the new repaired
  formula is correct via `check_aig_matches_clauses_per_formula`.
- Fallback: if the interpolation engine fails, the interpolant is huge,
  or the mirror can't be kept in sync, fall back to today's
  conflict-clause behavior.

### Risk

Interpolation engines need careful state management; bugs surface as
wrong synthesis silently. SLOW_DEBUG + `check_repair_monotonic` catch
most of these. Mirror-solver state synchronization is the biggest
operational risk.

### Expected impact

Could be transformative — the chain-of-corners pattern collapses to
chain-of-regions. On benchmarks where the function has a clean Boolean
structure (most of factorization, genbuf, amba), a handful of
interpolants may suffice where today thousands of conflicts are needed.
But: on benchmarks where the function genuinely has no clean structure,
interpolants degrade to clausal conflicts and we gain nothing.

---

## Option 3 — Trigger-based per-variable function re-synthesis

### The idea

Stop *patching* a hot variable; *rebuild* it. When a y has been
repaired more than N times (e.g. 200), the chained AIG is almost
certainly a worse representation than what we could synthesize from
scratch:

- Take all the (input, correct y) pairs we've seen via CEX history
  (these are *adversarial* — far better than random samples).
- Take y's input support from `aig_dep_list` (already cached in
  `dep_cache`).
- Train a **decision tree** on this support (the existing `ManthanLearn`
  infrastructure), or do **SAT-based exact synthesis** with templates of
  growing size (k-LUT, AND/OR with ≤ N gates).
- Verify the candidate with one cex_solver round; if it has fewer
  error CEXs than the chain, atomically replace `var_to_formula[y]`
  with the new AIG. If not, revert.
- Reset the per-var repair counter and continue.

### Why it should work

The chains we're growing are pathological encodings of relatively small
Boolean functions. A single decision tree of depth 20 over a
30-variable support can encode what 10,000 conflict-OR layers encode;
an exact-synth template of 50 gates can do the same. The existing
`--manthan_base 0` (LEARN) path does this *upfront* on random samples.
The novel piece is doing it **mid-loop, on demand, with adversarial
samples**.

### Plan (~600 LOC)

- Add `mconf.resynth_after_repairs` (e.g. 200) and
  `mconf.resynth_min_support` (e.g. 4).
- Persist a per-var `vector<sample> y_cex_history`; append every sample
  that put y in `needs_repair`. Cap at ~5k samples.
- New `Manthan::resynth_var(uint32_t y)`:
  - extract support from `dep_cache[y].dep_list`,
  - call `ManthanLearn::train_one_var(y, support, samples)` (already
    exists in `manthan_learn.cpp` as the per-var path),
  - convert decision tree to AIG (already exists),
  - encode via `AIGToCNF`,
  - run a quick *narrow* cex check: `repair_solver.solve` with
    assumptions forcing the new y to differ from the old y's correct
    outputs; if no easy CEX, swap formulas in.
- Keep the chain as a fallback if resynth's verifier fails.

### Risk

Two real ones: (1) replacing the formula breaks
indicator/dependency invariants — same lifecycle care as Option 1; (2)
we may *lose* progress (the resynthesized fn could be worse than the
chain on regions we'd already learned). Mitigate by verifying narrowly
and reverting on regression, plus boosting `prev_error_count`
monotonicity check via `check_repair_monotonic`.

### Expected impact

Targeted at the worst offenders — the `var 96` / `var 100` cases that
consume 90%+ of time on a single benchmark. If resynth succeeds on even
one such var, the rest of that benchmark often falls in seconds. If it
fails, you spend a few thousand SAT calls, give up, and continue.

---

## Ranking

- **Highest expected ROI per LOC: Option 1.** Chain growth is currently
  uncontrolled, and the AIG rewriter is right there. Probably 1–2 days;
  most work is testing the indicator lifecycle.
- **Biggest possible algorithmic win: Option 2.** This is the "real"
  generalization story. 1–2 weeks; real risk of subtle bugs; if it
  lands, the long-tail benchmarks become easy.
- **Complementary force-multiplier: Option 3.** Doesn't compete with 1
  or 2 — could be added on top of either. Best as a follow-up once
  Option 1 has tamed the bloat enough that re-synthesis sees clean
  inputs.
