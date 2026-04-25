# Arjun

Minimal-independent-set calculator and CNF minimizer. Preprocessor for
[GANAK](https://github.com/meelgroup/ganak) and
[ApproxMC](https://github.com/meelgroup/ApproxMC). Also performs
Boolean-function **synthesis** (Manthan-style counterexample-guided repair)
for defining relationships between variables.

## Building

ALWAYS build with `make -j12` from `build/` — otherwise it's slow.

```
cd build && ./build_norm.sh
```

Dependencies (cadical, cryptominisat, sbva, treedecomp) are typically sibling
checkouts under `../` and are pointed at via the cmake configuration already
present in `build/`. If cmake needs to be re-run, use `scripts/build_norm.sh`
or `scripts/build_release.sh`.

## Running

From `build/`:

```
./arjun --verb 2 --synth --synthbve 1 --extend 1 --minimize 1 --debugsynth --samples 1 out/fuzzTest_596.cnf
```

Useful top-level flags:
- `--synth` — enable synthesis (Manthan)
- `--debugsynth` — emit intermediate AIGs (`*-simplified_cnf.aig`,
  `*-autarky.aig`, `*-manthan.aig`, `*-final.aig`) for debugging
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

## After every build ALWAYS run the fuzzers

From `build/`:

```
./fuzz_synth.py --num 50
./fuzz_aig_to_cnf --num 300
./fuzz_aig_rewrite --num 300
```

Both must pass before reporting a change as complete.

## Source layout (`src/`)

- `arjun.{h,cpp}` — public API, the `AIG` class, and the `SimplifiedCNF`
  container. AIG nodes are `std::shared_ptr<AIG>` (`aig_ptr`). Every AIG
  node carries a monotonic `uint64_t nid` assigned at construction; use
  `nid` for ordering/hashing, never the raw pointer (ASLR makes pointers
  non-deterministic across runs).
- `manthan.{h,cpp}`, `manthan_learn.{h,cpp}` — counterexample-guided
  synthesis / repair loop. Hot path for large benchmarks.
- `aig_rewrite.{h,cpp}` — structural hashing, CSE, absorption, ITE
  flattening. Runs before Manthan and between repair rounds.
- `aig_to_cnf.{h,cpp}` — Tseitin encoding with fanout-based helper
  suppression, k-ary AND/OR fusion, ITE / MUX3 detection.
- `puura.{h,cpp}` — SharpSAT-td-derived simplification.
- `autarky.cpp`, `backward.cpp`, `extend.cpp`, `minimize.cpp`,
  `unate_def.cpp` — independent-set extraction passes.
- `metasolver.h`, `metasolver2.h`, `cachedsolver.h` — SAT-solver wrappers
  used by Manthan.
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
`-minim_idep_synt.aig`, `-manthan.aig`, `-final.aig`. `test-synth` verifies
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
   earlier and closer to the real cause.
4. **`VERBOSE_DEBUG`** (`src/constants.h:51`) — uncomment to enable verbose
   trace prints guarded by `VERBOSE_DEBUG_DO(...)` / `verbose_debug_enabled`.
   Use together with a delta-debugged small CNF so the traces stay readable.
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
