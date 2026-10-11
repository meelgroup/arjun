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
./arjun --verb 2 --synth --synthbve 1 --extend 1 --backward 1 --samples 1 out/fuzzTest_596.cnf out/funs.aig
```

`--synth` needs the 2nd file: the Skolem functions, as `.aig` or `.v`. `--2qbf`
takes it too, and then keeps the functions instead of only giving the verdict.

Useful top-level flags:
- `--synth` — enable synthesis (cegr)
- `--2qbf` — solve the forall-exists 2QBF instead (see "2QBF" below)
- `--debugsynth` — emit intermediate AIGs (`*-simplified_cnf.aig`,
  `*-autarky.aig`, `*-cegr.aig`, `*-final.aig`) for debugging
- `--verb N` — verbosity (0–2)

## Experiments: small runs here, full runs on the cluster

NEVER run full benchmark sweeps on this machine -- the cluster does that. Here,
run small experiments only: ~16 instances (one per core), in parallel, each
short. Pick them from existing cluster results instead of guessing:

- `build/data/out-synth-<jobid>-<n>/` -- per-instance cluster logs.
- `build/data/data.sqlite3`, table `arjun` -- parsed results (`dirname`,
  `fname`, `timeout_call`, `arjun_time`, `cegr_time`, `start_to_define_vars`,
  `last_stage`, ...). E.g. short instances that reach CEGR:
  `select fname, arjun_time from arjun where dirname='out-synth-...' and cegr_time>0 order by arjun_time limit 16;`
- Benchmarks: `build/benchmarks-qdimacs/*.qdimacs.gz`.

## 2QBF (`--2qbf`)

`arjun --2qbf file.qdimacs` decides forall X exists Y. F, with X the `a`
block (or `c p show`). Exit code 10 = true, 20 = false plus `V` lines giving
an X that has no Y. All of it is in `do_synth_2qbf()` in `main.cpp`,
`cover.{h,cpp}` and the `*2qbf*` methods of `SimplifiedCNF`:

1. `cover()` — budgeted model covering on the orig CNF (`--cover`, 0 =
   off): a model of F settles every X that satisfies the universal parts of
   the clauses its Y leaves unsatisfied; repeat until all X are covered. Wins when its refinements are short (sortnetsort
   family), gives up quickly otherwise. The models of F it refines with
   are the decide-false ones, except that an existential that satisfies
   more clauses when true is decided true: that is what keeps them short
   (the counterexample heuristic of the AReQS paper). When it
   finishes, its models give the Skolem functions. `--synth` runs it too,
   skipping the X that have no Y instead of stopping at the first one. It
   runs twice: on the orig clauses, and again on the simplified CNF.
   `--verb 1` prints a `[cover]` stats line (rounds, refinement size,
   ticks and time per solver) at the end and every 1000 rounds.
2. The normal synthesis pipeline. Synthesis only promises F(X, f(X)) for the
   X that have a Y, so:
3. `get_2qbf_cex()` — SAT call for an X with ~F(X, f(X)). It runs on the
   simplified CNF (`get_2qbf_cls()`), which is sound because simplification
   keeps the projected solution count. A counterexample is confirmed on the
   orig clauses with `is_2qbf_cex()`.

Testing: `fuzz_synth_2qbf.py` runs `--2qbf` on half of its iterations. A true
verdict is checked with `test-synth -u -q` (the final AIG must be a total
Skolem function), a false one by checking the CNF is UNSAT under the `V`
lines. `tests/2qbf/*.qdimacs` are `lit` tests (ctest `test-2qbf`, or `lit .`
in `build/tests/2qbf`): tiny files with their `RUN:` lines in comments.
`scripts/bench_2qbf.py` compares against `../cadet/cadet`; benchmarks
are in `~/media/qbf/2qbf/qbfeval16` (QBFEVAL'16 2QBF track).

## 2QBF preprocessing (`--2qbfpre`)

`arjun --2qbfpre in.qdimacs out.qdimacs` is a 2QBF preprocessor in the place
of `../bloqqer`, with its conventions: the variable numbers are kept, a
solved instance is written as `p cnf N 0` (true) or with the empty clause
(false), and the exit code is then 10 or 20; otherwise it is 0. It is the
`--2qbf` pipeline that stops early, in `do_synth_2qbf()`:

1. `cover()` on the orig clauses, at most `--coverticks` million CaDiCaL
   ticks (20 here, no limit under `--2qbf`).
2. Puura, exactly as for counting and synthesis: NEVER trim or budget it
   for this mode. `get_2qbf_cls()` gives its clauses over the orig vars.
3. `bce_2qbf()` removes the clauses blocked on an existential literal
   (bloqqer's QBCE; `--prebce 0` turns it off). That keeps the truth and
   the X with no Y, but not the solution count, so it cannot be a Puura
   step. `--2qbf` does this too when no functions are asked for.
   Puura runs ONCE by default. `--2qbfpuurarounds N` (up to 4) runs it
   again on what step 3 left, as a new problem (`cnf_of_2qbf_cls()`): the
   2nd run as the 1st, the 3rd and 4th with BVE that may grow the CNF
   (bloqqer's variable elimination). A further run is dropped unless it
   ends up with fewer literals. `cover()` runs once more after all of
   this, if the clauses changed.
4. The `bve` cegr strategy for `--prerepairs` repairs. If that finishes,
   `get_2qbf_cex()` gets `--preconfl` conflicts to give the verdict.
5. Whatever gave up: `write_qdimacs()` writes the clauses of step 3.

What to lift from bloqqer next is found by running it on arjun's output
with one technique off at a time (`--no-bce`, `--no-ve`, `--no-exp`, ...)
and seeing which one the downstream solver cannot do without. Both parts
of step 3 came from that. With `--2qbfpuurarounds 4`, 6 more of a 64-file
sample were solved by preprocessing alone, for 2-3x the preprocessing time
on the files it did not help.

`--prewitness f.aig` writes the functions it has at that point: the
existentials gone from the output, over the variables left in it (check
with `test-synth in.qdimacs f.aig`; `-u -q` if it was solved true). It
switches step 3 off: blocked clause elimination does not keep them.

`fuzz_synth_2qbf.py` runs `--2qbfpre` on every 2QBF iteration, solves the
output with `--2qbf` and compares the verdicts. `scripts/bench_2qbfpre.py`
compares no preprocessing, bloqqer and arjun, each followed by
`../cadet/cadet` and `../rareqs-1.1/rareqs` (built with
`CFLAGS=-fpermissive`, minisat's `libr` first). More benchmarks:
`~/media/qbf/2qbf/2010-comp`, `~/media/qbf/abdst-paper/robots2d`,
`~/media/qbf/qbflib/<family>/` (one directory per QBFLIB family),
`~/media/qbf/qbfeval17/2QBF` and `~/media/qbf/qbfeval20/PCNF` (mixed
prefixes there: `~/media/qbf/qbflib/qbf_prefix.py` prints `KEEP ae` for the
forall-exists ones). All of these but the first are `.qdimacs.gz`.

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
./fuzz_synth_2qbf.py --num 400
./fuzz_aig_to_cnf --num 1000
./fuzz_aig_rewrite --num 1000
```

They are independent, so with enough cores run all three at once (e.g. three
parallel tool calls in the same message) instead of sequentially.

All must pass before reporting a change as complete.

## Source layout (`src/`)

- `arjun.{h,cpp}` — public API, the `AIG` class, and the `SimplifiedCNF`
  container. AIG nodes are `std::shared_ptr<AIG>` (`aig_lit`). Every AIG
  node carries a monotonic `uint64_t nid` assigned at construction; use
  `nid` for ordering/hashing, never the raw pointer (ASLR makes pointers
  non-deterministic across runs).
- `cegr.{h,cpp}`, `cegr_learn.{h,cpp}` — counterexample-guided
  synthesis / repair loop. Hot path for large benchmarks.
- `cover.{h,cpp}` — model covering (see "2QBF").
- `verilog.{h,cpp}` — `write_verilog()` / `read_verilog()` of AIG defs as
  one module of single-bit nets (port `xN` is var N-1). Behind
  `SimplifiedCNF::write_aig_def_to_verilog()` / `read_aig_defs_from_verilog()`.
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
`fuzz_synth_2qbf.py`.

`--debugverilog 1` writes the final one as `-final.v` instead. `test-synth`
reads a `.v` like an `.aig`, but it has the functions only, so it must be a
finished synthesis. `fuzz_synth_2qbf.py` does this on half of its iterations;
`tests/verilog/*.v` are `lit` tests of the reader (ctest `test-verilog`).

## Debugging issues

When debugging a bug (assertion, wrong answer, crash, non-determinism), use
the full toolbox — don't stop at the first technique that gives a hint.
Expected workflow:

1. **Fuzzing** — reproduce / narrow down with `fuzz_synth_2qbf.py`,
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
