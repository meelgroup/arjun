# TODO: making `cover()` stronger

State at efe45e02. Ideas from reading the solvers in `qbf_solvers/` (not in
git: AReQS 2QBF beta, RAReQS 1.1, QESTO, CQESTO, QFUN, CAQE, QuAbS, CADET,
DepQBF, Qute, miniQU, Pedant, bloqqer 037, QRATPre+). The items to try are from
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

## From the 2QBF cluster run out-2qbf-2544900 (787 files, 900 s)

arjun --2qbf 662, VBS 728, no verdict disagreements. What arjun misses (66):

- `query*` (26): RAReQS after preprocessing gets 22, in 100-230 s median.
  Covering gives up at 500M ticks, 10-20 s in, and CEGR then runs to the
  timeout. With `--coverticks 30000`, 13 of the 26 are done in 300 s here.
  The run needs a schedule: more covering when CEGR is not getting there.
- `AR-fixpoint` (10, all false, 10k universals): CADET alone, 1-13 s. The
  orig run never ends its 1st round: 20009 of 40018 helpers in the
  refinement and one minimization call per helper, each a core of one. No
  tick check inside `minimize()`, and `--2qbf` has no tick limit there.
  Cap the calls of a round, and check the ticks in it. Even then Puura is
  too slow on them, and the interpolation of extend/backward ran out of memory.
- `small-pipeline-fixpoint` (7): the orig run takes 5867M ticks and 67 s for
  201 rounds, refinements of 4656. bloqqer + CADET: 5 s.
- `ctrl` (10): open again, BCE was removed (CLAUDE.md). bloqqer needs its
  BCE and VE for them, not expansion; BCE + a 2nd Puura run got 14 of 29 in
  200 s, all by covering.
- `ci` (6): 1 of 6 with 2 runs. bloqqer + RAReQS gets all 6. Open.

## To try, in order

1. **Helpers decided true in abs.** QESTO `qesto/QestoGroups.nw:767`, and
   `-b` bumps them before each solve. abs then picks an X that falsifies many
   universal parts. May give more no-Y cubes in `--synth` before abs has the
   clauses.
2. **Cover only the X where candidate functions g fail.** abs gets
   ~F(X, g(X)), encoded once; the functions end with g instead of the
   default. CADET only ever runs its CEGAR like this
   (`cadet/src/cadet2.c:427-447`, at most 50 rounds, while the avg cube is
   <= 17). The other way round: on giving up, cover throws its models away;
   they are right on all covered X and could seed cegr (`set_guess`).
3. **Models that are not constants.**
   - QFUN: every 64 rounds an ID3 tree per y over X from the (X, Y) samples,
     refine with F(X, f(X)): `qfun/src/rareqs.cpp:98-146`,
     `qfun/src/dec_tree.cpp`. Sound for any f. One F-sized AIG per learning
     round, so only with a large interval.
   - CADET decisions: y is "v unless the clauses with unique consequence ~v
     force otherwise" (`cadet/src/skolem.c:1438-1464`). For a model: U = the
     unsatisfied groups whose existential part is just ~v, T = the groups
     only y=v satisfies; refine with (rest or p), (~p or U), (~p or T). No
     AIG per round, k such y make one model stand for 2^k.
4. **Fewer helpers by preprocessing.**
   - hidden/covered blocked clauses: bloqqer `hidden_tautology()`
     `bloqqer.c:3270`; QRATPre+ `qratpreplus/qbce_qrat_plus.c:142`.
   - QBCE with functions, by reconstruction in reverse removal order,
     `l := l or ~(rest of C)`: DepQBF `qdpll.c:16924`.
   - blocked universal literal elimination: bloqqer `block_lit()`
     `bloqqer.c:2812`, QRATPre+ `qbce_qrat_plus.c:263`. Does not keep the
     set of X that have a Y: `--2qbf` verdict only.
   - universal expansion of a few X: bloqqer `try_expand()`
     `bloqqer.c:4903`.

## Done

- Clauses of outer vars only get no helper (1c3b013): of 83 `--synth`
  files, 90 s, 38 done, 25 by covering (36 and 22). The late run's avg
  refinement on `sdlx-fixpoint-8` went 7637 -> 22. The late run's ticks are
  now abs ticks, slower in wall time: a failing one takes 30 s, not 15.
- One run per existential-connected component (9e4dd2b). After Puura it is
  nearly always one component; the `*Service` files have 30+ of 45 clauses
  each, but only before Puura. Only `stmt17_70_90` gained.
  On giving up, the functions of the components that were covered are
  dropped: they could be kept.

## Tried, no gain
- Flipping the existentials no clause needs, no SAT call: removed
  (2026-10-26). On 32 cover-heavy files: with SAT minimization, rounds -5%,
  same time, 32 -> 31 solved; without it, same rounds, refine time x3.
- Dropping a helper of a refinement that another one in it implies: removed
  (2026-10-26). It excludes no more X, so same rounds; on 375 files of
  1-20 s, 375 -> 374 solved, same time. Shorter Skolem AIGs: aig_rewrite
  absorbs that.

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
  `--coverticks 2000`, `--coverminimsat 0`.
