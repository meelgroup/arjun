# Arjun

Minimal-independent-set calculator and CNF minimizer. Preprocessor for
[GANAK](https://github.com/meelgroup/ganak) and
[ApproxMC](https://github.com/meelgroup/ApproxMC). Also performs
Boolean-function **synthesis** (cegr-style counterexample-guided repair)
for defining relationships between variables.

## Building

ALWAYS build with `make -j12` from `build/` — otherwise it's slow.

```
cd build && ./build_norm.sh
```

Dependencies are sibling checkouts of this repo — arjun is `../arjun`, so
cryptominisat is `../cryptominisat`, cadical is `../cadical`, and likewise
`../cadiback`, `../sbva`, `../treedecomp`, `../EvalMaxSAT`, `../ganak`. To read a
dependency's source or headers, go straight there (e.g.
`../cryptominisat/src/cryptominisat.h`). NEVER search the filesystem for
them — no `find /`, no `find ~`; any hit outside `../` is an unrelated copy.

They are pointed at via the cmake configuration already present in `build/`.
If cmake needs to be re-run, use `scripts/build_norm.sh` or
`scripts/build_release.sh`.

## Running

From `build/`:

```
./arjun --verb 2 --synth --synthbve 1 --extend 1 --backward 1 --debugsynth --samples 1 out/fuzzTest_596.cnf
```

Useful top-level flags:
- `--synth` — enable synthesis (cegr)
- `--debugsynth` — emit intermediate AIGs (`*-simplified_cnf.aig`,
  `*-autarky.aig`, `*-cegr.aig`, `*-final.aig`) for debugging
- `--verb N` — verbosity (0–2)

## Quick A/B benchmarking: `scripts/run_elim_bench.sh`

One-line sanity bench for comparing simplification tweaks. Runs `arjun` on a
CNF and prints a single line with the headline counts (vars, indep, optind,
bin cls, long cls, lits, time).

Run from `build/` (where `arjun` and `count_literals.py` live):

```
../scripts/run_elim_bench.sh <cnf[.gz]> [extra arjun args...]
```

Extra args are forwarded to `arjun`. The simplified CNF is written to
`/tmp/arjun_elim_out` and the full log to `/tmp/arjun_elim.log`. Typical
workflow: run it on the same CNF before and after a change and diff the
output lines.

## After every build ALWAYS run the fuzzers, in parallel if possible

From `build/`:

```
./fuzz_synth.py --num 400
./fuzz_aig_to_cnf --num 1000
./fuzz_aig_rewrite --num 1000
```

They are independent, so with enough cores run all three at once (e.g. three
parallel tool calls in the same message) instead of sequentially.

All must pass before reporting a change as complete.

## CNF rewriting through AIG lifting (`--cnfrw`)

`src/cnf_rewrite.{h,cpp}` recovers gates (AND/OR k-ary, XOR, ITE, EQUIV,
irregular) syntactically from the clause set, lifts them into an AIG,
rewrites it with `AIGRewriter`, and
re-encodes it with `AIGToCNF` (or the cut mapper `src/aig_cnf_map.h`, see
`--cnfrwenc`). Each connected gate group is only replaced when its cost
(lits + `--cnfrwclsw`*cls + `--cnfrwvarw`*vars) drops. Sampling vars and
weighted vars are never removed. Runs inside `standalone_elim_to_file`;
`--cnfrw` is a bitmask: 1 = after the first puura pass (nearly a no-op
since puura leaves few gates), 2 = before puura (default, also ganak's
default), 4 = portfolio (first puura pass with and without the pre-rewrite,
keep the smaller). Mode 2 gives 5-25% fewer variables before puura and
smaller final CNFs on circuit-like/PG instances; note that in early paired
ganak timings (same variable permutation, pre-PG code) t3_059/095 counted
slower with it. puura's output size and ganak's time are both chaotic under
variable renaming (±30%, 3x), so only paired/median comparisons mean anything.

Plaisted-Greenbaum inputs (`--cnfrwpg`, default on): for a variable that is
not counted over (not in the sampling set, unweighted), the clauses of one
polarity, say `(¬g ∨ C_i)`, may be taken as its definition `g ↔ ∧ OR(C_i)`
without changing the projected count (∃g F is unchanged), so one-directional
Tseitin/PG encodings lift as gates too. Such outputs are re-emitted
one-directionally (`--cnfrwhalf`), and the encoder in that mode emits only the
needed implication direction per helper (polarity-aware Tseitin), flattens
fanout-1 OR conjuncts into single clauses, and duplicates small shared
sub-terms when a helper would cost more (`--cnfrwdupw`). On
mc2025_track3_103 (a pure PG circuit, 19.5k aux vars) `--cnfrw 2` removes
23% of the variables and 12% of the clauses before puura; the AIGRewriter's
cube-chain compression is off in this path (`--cnfrwchain 0`) because
sharing clause tails through helper nodes shrinks the AIG but grows the CNF.

Other knobs (defaults chosen on 5-renaming medians of 033 and 103):
`--cnfrwordistrib 1` distributes small nested ANDs into their OR clause when
the fanout-amortised helper would cost more; `--cnfrwcofactor 48` is a new
AIGRewriter rule AND(lit, f) -> AND(lit, f|lit=1) on unshared cones of at most
48 nodes (`--cnfrwcofshared 1` also duplicates shared cones); `--cnfrwconstr 1`
lifts non-gate clauses over removable gate outputs as asserted roots so the
outputs can be inlined into the constraints (off: helped 033 slightly, cost
103 its whole gain); `--cnfrwpareto N` allows N% clause/literal growth (1 =
strict). Use `--cnfrwdump <prefix>` to write the CNF before/after each pass
when debugging count changes (compare ganak counts of the two dumps).

Tooling:
- `build/cnf_gate_stats [--puura 0/1] [--backward 0/1] file.cnf` — gate and
  AIG shape statistics (fanin histograms, cone shapes, NPN classes of small
  cones, per-component rewrite table).
- `scripts/cnfrw_bench.py --configs "base:--cnfrw 0" "pre:--cnfrw 2" [--perms 3] files…`
  — A/B on output size and ganak count time; counts must agree across configs.
  puura's output size is chaotic under variable renaming (±20%), so compare
  medians over `--perms`.
- `../count_fuzzer/fuzz.py` randomizes the `--cnfrw*` flags; it is the
  count-preservation fuzzer for this module.

## Source layout (`src/`)

- `arjun.{h,cpp}` — public API, the `AIG` class, and the `SimplifiedCNF`
  container. AIG nodes are `std::shared_ptr<AIG>` (`aig_lit`). Every AIG
  node carries a monotonic `uint64_t nid` assigned at construction; use
  `nid` for ordering/hashing, never the raw pointer (ASLR makes pointers
  non-deterministic across runs).
- `cegr.{h,cpp}`, `cegr_learn.{h,cpp}` — counterexample-guided
  synthesis / repair loop. Hot path for large benchmarks.
- `aig_rewrite.{h,cpp}` — structural hashing, CSE, absorption, ITE
  flattening. Runs before cegr and between repair rounds.
- `interpolant.{h,cpp}` — definition extraction by Craig interpolation
  over a doubled CNF (used by the `--backward` and `--extend` passes),
  plus the `InterpTracerMcMillan` McMillan-interpolant tracer that
  reconstructs interpolants from a cadical proof trace. See the
  `--interprebuildevery` flag in `main.cpp`.
- `aig_to_cnf.{h,cpp}` — Tseitin encoding with fanout-based helper
  suppression, k-ary AND/OR fusion, ITE / MUX3 detection.
- `puura.{h,cpp}` — SharpSAT-td-derived simplification.
- `cnf_rewrite.{h,cpp}`, `aig_cnf_map.h` — CNF gate lifting / cut-based CNF
  mapping (see `--cnfrw` above).
- `cnf_gate_stats.cpp` — gate/AIG shape analyzer binary.
- `autarky.cpp`, `backward.cpp`, `extend.cpp`, `minimize.cpp`,
  `unate_def.cpp` — independent-set extraction passes.
- `metasolver.h`, `metasolver2.h`, `cachedsolver.h` — SAT-solver wrappers
  used by cegr.
- `test_aig_rewrite.cpp`, `test_aig_to_cnf.cpp`, `test-synth.cpp` —
  correctness checkers.
- `aig_fuzzer.cpp`, `aig_to_cnf_fuzzer.cpp` — fuzzers.

## Determinism

The same binary must produce bit-identical output across runs and machines.
Do not introduce pointer-address-dependent ordering (`operator<` on
`shared_ptr`, `std::hash<T*>`, `reinterpret_cast<uintptr_t>` of a pointer).
For AIG nodes, order/hash on `AIG::nid` via the `aig_nid_less` comparator
(in `aig_rewrite.cpp`) or `AigPtrHash` (in `aig_rewrite.h` / `aig_to_cnf.h`).

## Debug outputs

When `--debugsynth` is passed, intermediate AIGs are written next to the
input CNF with suffixes `-simplified_cnf.aig`, `-autarky.aig`,
`-minim_idep_synt.aig`, `-cegr.aig`, `-final.aig`. `test-synth` verifies
each stage's AIG against the original CNF and is invoked automatically by
`fuzz_synth.py`.

## Debugging issues

When debugging a bug (assertion, wrong answer, crash, non-determinism), use
the full toolbox — don't stop at the first technique that gives a hint.
Expected workflow:

1. **Fuzzing** — reproduce / narrow down with `fuzz_synth.py`,
   `fuzz_aig_to_cnf`, `fuzz_aig_rewrite` (see "After every build"). Fuzzers
   generate minimal failing inputs much faster than reasoning from a large
   user-supplied CNF.
2. **`scripts/cnf_delta.py`** — clause-level delta debugger for DIMACS CNFs.
   Given a failing CNF and an oracle script that exits 0 iff the bug still
   reproduces, it does plain ddmin on the clause list, preserving headers,
   comments, and the `c p show … 0` projection line. Typical use: write a
   tiny bash oracle that runs `arjun` with the bug-triggering flags and
   greps stderr for the assertion text, then run
   `./cnf_delta.py bug.cnf bug_min.cnf /tmp/oracle.sh`. Always minimize
   before filing a repro or committing a bug CNF to the repo.
3. **`SLOW_DEBUG`** (`src/constants.h:50`) — uncomment to enable expensive
   internal invariant checks (`SLOW_DEBUG_DO(...)` blocks). Turn this on
   whenever an assertion fires or an output looks wrong; it will often fail
   earlier and closer to the real cause. Add SLOW_DEBUG_DO blocks for new
   code as needed to help future debugging.
4. **`VERBOSE_DEBUG`** (`src/constants.h:51`) — uncomment to enable verbose
   trace prints guarded by `VERBOSE_DEBUG_DO(...)` / `verbose_debug_enabled`.
   Use together with a delta-debugged small CNF so the traces stay readable.
   Don't forget to add `VERBOSE_DEBUG_DO` blocks for new code as needed to help
   future debugging.
5. **valgrind** — run under `valgrind --error-exitcode=1` (and
   `--track-origins=yes` for uninitialized reads) for any suspected memory
   issue. Undefined behavior here often manifests as non-determinism on
   larger inputs.
6. **gdb** — for assertion failures and crashes, run under `gdb --args
   ./arjun ...`, `run`, then `bt` / `frame N` / `p` to inspect state at the
   failure point. Pair with `SLOW_DEBUG` so gdb stops at the invariant
   break, not downstream at a confusing symptom.

Default loop for a tricky bug: fuzz → delta-debug the failing CNF with
`cnf_delta.py` → rebuild with `SLOW_DEBUG` (and `VERBOSE_DEBUG` if needed) →
valgrind / gdb on the minimized CNF.
