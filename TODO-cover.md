# TODO: making `cover()` stronger

State at efe45e02. Ideas from reading the solvers in `qbf_solvers/` (not in
git: AReQS 2QBF beta, RAReQS 1.1, QESTO, CQESTO, QFUN, CAQE, QuAbS, CADET,
DepQBF, Qute, miniQU, Pedant, bloqqer 037, QRATPre+). Items 2-7 are from
reading code, unmeasured.

## Where cover fails now

- Too many models: each constant Y covers few X (sortnetsort synth steps,
  `nreachq_*`, `reachqu_query*`, `ctrl`, `ci`, `Q_2-3`).
- Refinements stay hundreds of helpers long and minimization removes nothing
  (`sdlx-fixpoint-8`: 1301 helpers, avg refinement 631, removed 0).
- A failing run burns its whole tick limit: 10-25 s on files that solve in
  2-3 s otherwise.

For forall-exists CNF, QESTO's selectors, CAQE's b-literals, QuAbS and
RAReQS/AReQS substitution all give the refinement clause cover already has.
The QCDCL cover sets (DepQBF `cover_by_clauses`, Qute, miniQU) are one cube:
weaker.

## To try, in order

1. **Clauses with no undefined existential get a helper that is in every
   refinement.** `mixed` gets them with an empty `exist`. Late run on
   `sdlx-fixpoint-8`: 807 outer defs, 7678 helpers, avg refinement 7637.
   Such a clause false = that X has no Y: a cex for `--2qbf`, a constraint
   on abs for `--synth`. CADET skips them: `cadet/src/casesplits.c:98-131`.
2. **One cover run per existential-connected component.** Union-find over
   the undefined vars through the clauses. Model counts then add instead of
   multiply. CAQE `caqe/src/matrix/hierarchical.rs:344`, CADET
   `cadet/src/partitions.c:25-110`. Check first how often Puura leaves more
   than one component.
3. **Shorter refinements with no SAT call.**
   - helper B is redundant in a refinement that has helper A with
     univ(A) a subset of univ(B). CAQE `caqe/src/solve/caqe.rs:1694-1750`
     (off by default there, says it does not cut iterations), RAReQS `-u`.
     Lowers the `sq_frac` cost too: recheck `--coverorig 50`.
   - flip an undefined y when every clause its true literal is in has another
     true existential literal and the flip satisfies more clauses. CAQE
     `entry_minimization`, `caqe.rs:1391-1427`; DepQBF
     `sdcl_friendly_dec_heuristic`, `depqbf/qdpll.c:10958`.
4. **Helpers decided true in abs.** QESTO `qesto/QestoGroups.nw:767`, and
   `-b` bumps them before each solve. abs then picks an X that falsifies many
   universal parts. May give more no-Y cubes in `--synth` before abs has the
   clauses.
5. **Cover only the X where candidate functions g fail.** abs gets
   ~F(X, g(X)), encoded once; the functions end with g instead of the
   default. CADET only ever runs its CEGAR like this
   (`cadet/src/cadet2.c:427-447`, at most 50 rounds, while the avg cube is
   <= 17). The other way round: on giving up, cover throws its models away;
   they are right on all covered X and could seed cegr (`set_guess`).
6. **Models that are not constants.**
   - QFUN: every 64 rounds an ID3 tree per y over X from the (X, Y) samples,
     refine with F(X, f(X)): `qfun/src/rareqs.cpp:98-146`,
     `qfun/src/dec_tree.cpp`. Sound for any f. One F-sized AIG per learning
     round, so only with a large interval.
   - CADET decisions: y is "v unless the clauses with unique consequence ~v
     force otherwise" (`cadet/src/skolem.c:1438-1464`). For a model: U = the
     unsatisfied groups whose existential part is just ~v, T = the groups
     only y=v satisfies; refine with (rest or p), (~p or U), (~p or T). No
     AIG per round, k such y make one model stand for 2^k.
7. **Fewer helpers by preprocessing.**
   - hidden/covered blocked clauses: bloqqer `hidden_tautology()`
     `bloqqer.c:3270`; QRATPre+ `qratpreplus/qbce_qrat_plus.c:142`.
   - QBCE with functions, by reconstruction in reverse removal order,
     `l := l or ~(rest of C)`: DepQBF `qdpll.c:16924`. Would let
     `bce_2qbf()` run for `--synth` and with `--prewitness`.
   - blocked universal literal elimination: bloqqer `block_lit()`
     `bloqqer.c:2812`, QRATPre+ `qbce_qrat_plus.c:263`. Does not keep the
     set of X that have a Y: `--2qbf` verdict only.
   - universal expansion of a few X: bloqqer `try_expand()`
     `bloqqer.c:4903`.

## Tried, no gain

- Minimizing the no-Y cubes by literal deletion: the cores are near-minimal.
- Selector phase preference in f.
- Dropping one of the core, or adding back, in the minimization.
- Building AIGs per round: 11 GB per process. NEVER.

## Not worth taking

Pedant's arbiters (single X points in 2QBF), CAQE's expansion and
strong-unsat refinements (never fire on forall-exists), long-distance
resolution, RAReQS's recursion, QESTO `-r` (verdict only, quadratic).

## Measuring

- `--verb 1` prints the `[cover]` line: rounds, helpers, avg refinement,
  minim calls/removed, ticks.
- Cluster reference: `build/data/out-synth-2535088-1` (404 of 593), table
  `arjun` in `build/data/data.sqlite3`. 84 of its 189 unsolved are
  `*query*_1344n`.
- Local: 16 at a time, each under `ulimit -v 2500000` and a timeout.
- Tuning run launched with efe45e02: defaults, `--coverticks 100`,
  `--coverticks 2000`, `--coverminim 0`.
