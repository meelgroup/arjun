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
