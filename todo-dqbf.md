# DQBF with Arjun

DQBF: forall X exists^{D_1} y_1 ... exists^{D_n} y_n. F, each y_i may depend only
on D_i, a subset of X. Arjun assumes every y may depend on all of X and on any
other y; nearly everything below follows from dropping that.

Pedant (`qbf_solvers/pedant-solver`) is the closest relative: definitions +
interpolation + counterexample-guided repair, the strongest on true instances.

## What carries over

- The 2QBF relaxation (every D_i = X) false => the DQBF is false. So
  `get_2qbf_cex()`, cover's false verdicts and false units/equivalences on
  universals stay sound.
- Constant defs (unate, units, pure literals) are always legal.
- Dependency sets that form a chain: an ordinary QBF. All equal: a 2QBF.
  Detect both at parse time.

## What has to change

1. Data model: `SimplifiedCNF` has one `sampl_vars`. Each y needs its own
   allowed support: D_i plus the y_j with D_j subset of D_i, through every
   renumbering (`OrigTranslation`, `cover_problem.h`, defs). Parse DQDIMACS `d`
   lines.
2. A support check wherever a def is made, transitively after substitution
   (`dependency_mat` / `y_order` in `cegr.cpp`):
   - Puura BVE: the rebuilt y can pull in x not in D_i. Side condition
     (Wimmer et al., "Preprocessing for DQBF", SAT'15) or don't eliminate.
   - Equivalences: substitute y_i = y_j only if the dependency sets allow it.
     F forcing y_i = +-x with x not in D_i means false.
   - backward/extend: the shared vars of the doubled CNF must be y's own
     allowed support, not the global sampling set.
   - CEGR: learn candidates on the allowed support only, restrict repair
     cores to it. No repair there does not mean false.
3. Cover splits on full X; a Skolem function must agree on all X with the
   same projection onto D_i. Keep it only for false verdicts (relaxation) and
   the chain/equal cases.
4. False needs several X jointly: Pedant's arbiter variables (fits cegr's
   loop, complete) or HQS-style universal expansion. Without them: true /
   unknown, plus the relaxation cases.
5. Testing: `test-synth` checks each final function's support is within D_i
   (`get_dependent_vars_recursive`); fuzzer with random `d` lines, false
   checked by brute-force expansion on tiny files; `lit` tests like
   `tests/2qbf`.

## Order

1. Parse `d` lines, the 2QBF/QBF special cases, relaxation for false,
   per-y support restrictions everywhere (disallowed defs/eliminations
   skipped). Sound true / false-by-relaxation / unknown; compare with Pedant
   on the QBFEVAL DQBF track.
2. Arbiters or expansion, for false instances.

First: size up how far the single sampling set reaches into `puura.cpp`
and `interpolant.cpp`.
