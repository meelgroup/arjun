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
./arjun --verb 2 --synth --synthpuura 1 --extend 1 --backward 1 --samples 1 out/fuzzTest_596.cnf out/funs.aig
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

1. `cover()` — budgeted model covering (`--cover`, 0 = off, and
   `--coverticks`, million ticks of SAT work per run, 200 by default): a
   model of F settles every X that satisfies the universal parts of the
   clauses its Y leaves unsatisfied; repeat until all X are covered. Wins
   when its refinements are short (sortnetsort, the `query*` files), gives
   up otherwise. What keeps them short:
   - the models of F it refines with are the decide-false ones, except that
     an existential that satisfies more clauses when true is decided true
     (the counterexample heuristic of the AReQS paper);
   - `--coverminim` (a sum, 1 by default). 1: further SAT calls for a
     model of the same X whose existentials satisfy more clauses, on
     selectors, dropping the cores. 2: flip the existentials no clause
     needs, no SAT call. 4: drop a helper that another one of the
     refinement implies. 2 and 4 made no difference on small samples;
   - a clause of outer vars only gets no helper, and clauses that share no
     existential are covered apart;
   - `--synth` only: after the first X with no Y, abs gets the clauses, so
     it only picks an X that has a Y. Their cubes were most of the rounds;
   - the defs `cnf` already has are followed: a model is the values of the
     vars with no def, see `cover.h`.
   When it finishes, its models give the Skolem functions. `--synth` skips
   the X that have no Y instead of stopping at the first one. It runs on
   the simplified CNF, and again after extend/backward/unate if they
   defined something. That last run
   takes a handful of rounds when it works, so it has its own, lower limit
   (`--coverlateticks`, 100): a failing one is slow. These runs are SHORT:
   most of what covering solves takes under 100M ticks, and a failing run
   is paid by every file. The long run (`cover(ticks=5000)` in
   `--cstrategy`, on the CNF with the functions of the passes) comes before
   the last, unlimited strategy: only once the repair-limited ones did not
   finish either. NEVER make the 1st runs long instead. On the CNF as it
   was after Puura it was slower: of 55 files at 90 s, 3 more done on the
   one with the functions, none fewer. Only `--2qbf` also
   runs it on the orig clauses first, while the refinements
   are short: that is where an X with no Y is found
   (`--coverorigticks`, 2000: sortnetsort10.008 takes 1800M there).
   NEVER add that run to `--synth`: all it covered
   there is covered after Puura too, and it cost 7 s per file. NEVER build AIGs per round in it: the functions are made once,
   at the end, from the stored models.
   `--verb 1` prints a `[cover]` stats line (rounds, refinement size,
   ticks and time per solver) at the end and every 1000 rounds.
2. The normal synthesis pipeline. Synthesis only promises F(X, f(X)) for the
   X that have a Y, so:
3. `get_2qbf_cex()` — SAT call for an X with ~F(X, f(X)), on `cnf`'s
   clauses. Like cover, it works in the CNF's numbering
   (`cover_problem.h`): `OrigTranslation` turns the defs into a
   `CoverProblem` over it once, at the entrance, and the results back to orig
   vars at the exit. Nothing in between translates.

Everything works from `cnf`, never from the orig clauses (`orig_clauses` is
for debugging, e.g. `is_2qbf_cex()`). That is sound because simplification
defines a universal only by what F implies: a unit (`get_fixed_values()`) or
an equivalence with another universal. Right after each Puura run,
`get_2qbf_def_cex()` turns such a def into an X that breaks it: false, no SAT
call. With no universal defined, `cnf`'s clauses are the 2QBF and the
universals gone from them are free.

Testing: `fuzz_synth_2qbf.py` runs `--2qbf` on half of its iterations. A true
verdict is checked with `test-synth -u -q` (the final AIG must be a total
Skolem function), a false one by checking the CNF is UNSAT under the `V`
lines. It then runs `--2qbf` with no output file (the blocked clause path
below) and compares the verdicts. `tests/2qbf/*.qdimacs` are `lit` tests (ctest `test-2qbf`, or `lit .`
in `build/tests/2qbf`): tiny files with their `RUN:` lines in comments.
`scripts/bench_2qbf.py` compares against `../cadet/cadet`; benchmarks
are in `~/media/qbf/2qbf/qbfeval16` (QBFEVAL'16 2QBF track).

More 2QBF benchmarks: `~/media/qbf/2qbf/2010-comp`,
`~/media/qbf/2qbf_combo` (the `ctrl` family is there),
`~/media/qbf/abdst-paper/robots2d`, `~/media/qbf/qbflib/<family>/` (one
directory per QBFLIB family), `~/media/qbf/qbfeval17/2QBF` and
`~/media/qbf/qbfeval20/PCNF` (mixed prefixes there:
`~/media/qbf/qbflib/qbf_prefix.py` prints `KEEP ae` for the forall-exists
ones). All of these but the first are `.qdimacs.gz`.

### Blocked clauses: removed

BCE between Puura runs was removed (2026-10-25) for simplicity. On
`2qbf_combo` at 60 s: 630 solved without, 623 with. BCE is what solves `ctrl`
(7 of 29, 0 without: it unlocks BVE, 9137 -> 1736 cls) and won 2 `sdlx`; no
BCE won 16, mostly the fixpoint families. `ctrl` needs it back (git history).

## Other QBF solvers and preprocessors: `qbf_solvers/`

Sources of the tools to compare against and to lift ideas from are in
`qbf_solvers/` of this repo (untracked), one directory each: `areqs`,
`bloqqer`, `cadet`, `caqe`, `cqesto`, `depqbf`, `miniQU`, `pedant-solver`
(DQBF), `qesto`, `qfun`, `qratpreplus` (preprocessor), `quabs`, `qute`,
`rareqs`; `dl/` has the tarballs. They are built in place. All benchmarks
are described in `~/media/qbf/README.md`.

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

## After every build ALWAYS run the fuzzers, 16 wide

From `build/`, on all 16 cores, for a fixed time, NEVER one `--num 400`
process (that loads one core):

```
(echo aig_rewrite; echo aig_to_cnf; seq 1 14) | xargs -P16 -I{} bash -c 'ulimit -v 2500000;
  case {} in aig_*) ./fuzz_{} --num 1000 > fz_{}.log 2>&1;;
  *) timeout 300 ./fuzz_synth_2qbf.py --num 100000 > fz_{}.log 2>&1;; esac; echo "{} $?"'
```

The synth ones exit 124 when the time is up, anything else is a failure.
Many `fuzz_synth_2qbf.py` at once in one directory is safe: `unique_file()`
claims each name with `O_EXCL`, and every other file is named after it.
The AIG fuzzers write no files and pick a random seed each.
A killed run leaves its `out/fuzzTest_*` files behind; `unique_file()`
gives up after 2700 names, so clear `out/` now and then.
Verification loops (`test-synth` over several files) go through `xargs -P`
too.

For changes to the counting side (Puura for counting, `--coverdrop`), also
run `../count_fuzzer/fuzz.py`, 16 wide the same way, from `../count_fuzzer`
(`--proj` for projected counting, which `--coverdrop` needs). It counts
with several counters, through `../arjun/build/arjun` and
`../ganak/build/ganak` with random `--coverdrop` options, and compares. About
half of its brummayer CNFs give coverdrop components to drop or replace.

All must pass before reporting a change as complete.

## Source layout (`src/`)

- `arjun.{h,cpp}` — public API, the `AIG` class, and the `SimplifiedCNF`
  container. AIG nodes are `std::shared_ptr<AIG>` (`aig_lit`). Every AIG
  node carries a monotonic `uint64_t nid` assigned at construction; use
  `nid` for ordering/hashing, never the raw pointer (ASLR makes pointers
  non-deterministic across runs).
- `cegr.{h,cpp}`, `cegr_learn.{h,cpp}` — counterexample-guided
  synthesis / repair loop. Hot path for large benchmarks.
- `cover.{h,cpp}` — model covering (see "2QBF"). `Cover` splits the clauses
  into components by the ys they share, `CoverComponent` covers one:
  `x_solver` picks an X, `y_solver` finds a Y for it. Config:
  `Arjun::CoverConf` in `arjun.h`, like `CegrConf`.
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
