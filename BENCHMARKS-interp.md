# Craig-interpolant repair: early benchmark observations

This document records initial measurements of `--interprepair` on a
small set of CNFs from `build/benchmarks-qdimacs/`. Numbers come from a
single laptop (~4–6× slower than the cluster), so absolute times are
indicative only.

Build: `make -j4` from `build/`. Versions: arjun develop branch with
`InterpRepair` integrated (commits 75f4786..ba79a7e).

## Where interpolation helps

Benchmarks where conflicts are moderately wide (≥ ~10 lits) and the
underlying function generalises well over input vars:

| Benchmark            | Baseline (rep / loops) | Interp (rep / loops) | Notes                          |
|----------------------|------------------------|----------------------|--------------------------------|
| stmt17_70_98         | 5 / 6                  | **1 / 2**            | one interp, 142 nodes          |
| stmt17_62_78         | 9 / 10                 | **3 / 4**            | 3 calls, avg 16 nodes          |
| stmt19_64_91         | 7 / 8                  | **2 / 3**            | 2 calls, avg 19 nodes          |
| stmt19_71_95         | 7 / 8                  | **2 / 3**            | 2 calls, avg 41 nodes          |
| stmt19_75_83         | 8 / 9                  | **4 / 5**            | 4 calls, avg 11 nodes          |
| stmt25_52_53         | 15 / 16                | **8 / 9**            | 8 calls, avg 8 nodes           |
| sdlx-fixpoint-3      | 44 / 23                | **17 / 9**           | avg conflict 127 lits, interp 466 nodes |
| sdlx-fixpoint-4      | 387 / 235  (16.18s)    | **81 / 32  (12.50s)**| avg conflict 155 lits, interp 613 nodes |

The repair count drops by 30–80%. Total wall time barely moves on
these (they are tiny benchmarks dominated by preprocessing), but the
*per-loop progress* improves because each repair generalises to a
region rather than a single corner of input space.

## Where interpolation does not help / hurts

Benchmarks with very small conflicts (avg < 6 lits) or with irregular
Boolean structure where the interpolant inflates instead of
compresses:

| Benchmark            | Baseline (rep / loops) | Interp (rep / loops) | Notes                          |
|----------------------|------------------------|----------------------|--------------------------------|
| factorization8       | 122 / 63               | 151 / 67             | avg conflict 5 lits            |
| driver_a9n           | 53 / 48                | 70 / 53              | avg conflict 4.5 lits          |
| amba2c7n             | 281 / 207              | 376 / 257            | interp avg 54 nodes vs 8 lits  |

The interpolant is much larger than the conflict-AND in these cases
(see `smaller/larger:` in the printed stats), so the formula bloats
faster than it generalises. `--interprepair 2 --interprepairmincl 10`
gates the interp path off when the conflict is already small, which
recovers baseline performance on factorization-style benchmarks.

## Tuning knobs

- `--interprepair {0,1,2}` — off / on for every repair / on only when
  conflict size ≥ `--interprepairmincl` (default 4).
- `--interprepairmincl N` — minimum conflict size to trigger interp.
  Recommended starting point: **8–12** to skip the small-conflict
  benchmarks where interp tends to expand.
- `--interprepairminvar N` — only kick in after a y has been repaired
  more than N times. Useful to focus interpolation on the hot
  variables that are actually in the death-spiral pattern.
- `--interprepairmaxnodes N` — cap interpolant AIG size; if the
  produced interpolant is bigger, fall back to the conflict-clause
  path. 0 = no cap.
- `--interprepairverify {0,1,2}` — always-on verification. 0 = off,
  1 = cheap CEX-input check, 2 = full SAT miter (slow). Useful for
  cluster runs where SLOW_DEBUG isn't compiled in.

## Recommended cluster sweep

A reasonable grid for a first cluster experiment:

```
--interprepair 0
--interprepair 2 --interprepairmincl 8
--interprepair 2 --interprepairmincl 8 --interprepairminvar 5
--interprepair 2 --interprepairmincl 12 --interprepairminvar 50
--interprepair 1 --interprepairmaxnodes 100
```

The first row is the baseline. The remaining four sweep the gating
knobs to find the right balance between "fire often enough to break
death-spirals" and "skip when small conflicts are already optimal".

## Correctness

- Fuzz tested across 700+ iterations of `fuzz_interp_repair.py` (a
  variant of `fuzz_synth.py` that forces `--interprepair 1|2` every
  iteration). 0 failures.
- Fuzz tested across 200 iterations of vanilla `fuzz_synth.py` (which
  enables `--interprepair` ~25% of the time). 0 failures.
- Under `SLOW_DEBUG`, every successful interp call is verified via a
  full SAT miter that checks `A → I` (the McMillan soundness
  condition). 75/80 successful runs in a 100-iter SLOW_DEBUG fuzz
  pass; the rest are timeouts (SLOW_DEBUG slows things down by 2-3x).
- Quick check (`I` evaluates to FALSE on the original CEX inputs)
  fires on every call; failing interpolants are discarded and the
  legacy conflict-clause path is used as fallback.

## Bugs caught during bring-up

- `add_derived_clause` fires from cadical's add-time unit propagation,
  not just `solve()`. Original "post-hoc B-clause re-labeling" pass
  was unsound: the re-label happened after some derived clauses had
  already been emitted with the (wrong) initial A-side label.
  Replaced with a synchronous `next_is_b` flag set on the tracer
  before each `solver->add(0)`.
- `get_conflict()` returns the *negation* of failing assumptions (so
  the conflict can be added as a learnable clause). The first cut
  added them un-negated as units, producing a different UNSAT (or
  none at all). Negating to recover the original assumptions fixed it.
- `var_to_formula[y].aig` stores the *raw* AIG with cnf-space
  to_define vars as leaves; the y_hat-translated form lives only in
  `var_to_formula[y].clauses`. The first cut encoded the b1 AIG
  (which AND's in y_other f2.aig) directly via AIGToCNF — leaking
  raw to_define vars into f.clauses and tripping
  `check_functions_for_y_vars`. Fix: translate via `map_y_to_y_hat`
  before encoding. SLOW_DEBUG leaf check protects against future
  regressions of this kind.
- Y-other formula AND-conjuncts: the first cut dropped them entirely
  from the branch, treating ¬I as the must-flip region unconditionally.
  But the interpolant was computed under the assumption y_others =
  ctx[y_others]; ¬I only applies when those values match. Restored
  the per-y_other AND (same expansion the legacy lit_to_aig path does).
  Effect: driver_a10y went 41 → 143 repairs with the bug, back to ~41
  after fix.
