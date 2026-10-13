# TODO: incremental determinization (CADET's algorithm)

Why: the `AR-fixpoint` family of the 2QBF cluster run `out-2qbf-2544900`.
10 files, all false, 10k universals, 52k-770k vars. CADET alone solves all
10 in 1-13 s. No arjun run solves any: covering needs refinements of half
the helpers (20009 of 40018), Puura takes over 100 s, `--2qbfpre` ran out
of memory in the interpolation.

A first try is on the branch `determinize-wip` (`src/determinize.{h,cpp}`,
`--determinize`). It is NOT merged: it does not solve them. What it showed
is below.

## What CADET does

A var is *determined* once, of the clauses whose other vars are all
determined (the universals are from the start), one always forces it:
whatever those vars are, some clause with it has all its other literals
false. Its value is then a function of them. Two checks per var:

- determinicity: no assignment of the others leaves it unforced;
- conflict: no assignment forces it both ways. One that does, with the
  others following their functions, is an X with no Y.

This propagates. When it stalls CADET *decides*: an undetermined var gets a
value for where nothing forces it. That is a choice of Skolem function, so a
conflict after it does not mean false. CADET analyses the conflict, learns a
clause over the determined vars, backtracks, and goes on. The learned clause
is a consequence of F, so it can force vars that F's own clauses did not.

## What the try does, on AR-fixpoint-1

Propagation only, then one SAT call for an X whose determined values falsify
a clause. The determinicity check is by enumeration over the vars of the
var's own clauses (at most 10), and by SAT call on the functions so far only
where that says no. Only a var that some assignment forces both ways has
its clauses in the final SAT call: 4 vars here, not 32512.

- 32512 of 42525 existentials determined, in 4 s. No X among them.
- The other ~10000 are real choices: 5000 pairs `z <-> x xor y` where
  neither y nor z is forced, a 2502-literal clause over the y, and
  `y -> ~w` for each.
- Giving them default values with no backtracking (the var in the most
  clauses first, the value most of them want, unless a clause forces the
  other one) gets all 42525 determined after 5010 decisions and an X that
  falsifies a clause. That X has a Y: `is_2qbf_cex()` rejects it.

CADET's log on the same file: 53753 determinicity checks, 32516 local
conflict checks, 1 global conflict check, 2 decisions, 1 conflict, "UNSAT
via Skolem conflict". So it decides once or twice, hits a conflict, and the
clause it learns from that is what lets propagation finish and find the
real X. 5010 decisions with no learning is not that.

## Why it needs conflict analysis

- A conflict under decisions only says the functions chosen so far are
  wrong for that X. Without analysis there are two bad ways on: give up, or
  flip a decision blindly (exponential).
- The learned clause is what makes it converge: it is implied by F, it is
  over determined vars, and it is forcing for the var decided last, so that
  var is now determined, with no decision. This is CDCL's unit after
  backjumping, on functions instead of values.
- False is only proven by a conflict with no decision behind it. So the
  loop has to get back to decision level 0 with learned clauses, which a
  greedy pass never does.
- True needs it as well: all vars determined and no conflict is a proof
  only if each decision was either kept without conflict or replaced by
  what was learned.

## What is needed

1. Decision levels on the determined vars and their encodings: backtracking
   takes the functions of a level away again. In the try they are permanent
   clauses of one SAT solver. CADET keeps a solver frame per level
   (`qbf_solvers/cadet/src/skolem.c`).
2. Conflict analysis over the forcing-clause graph, to a clause with one
   literal of the last level: `qbf_solvers/cadet/src/conflict_analysis.c`.
   The X of the conflict gives the values, as in CDCL.
3. Learned clauses added to the clause set, so that they count as forcing
   clauses: occurrence lists and the per-clause undetermined count have to
   take new clauses.
4. A decision heuristic (CADET: VSIDS-like activities bumped in conflict
   analysis) and restarts.
5. The functions at the end, for `--synth` and `--2qbf` with an output
   file: per var, forced true by a clause, else the decided value. CADET's
   certificates: `qbf_solvers/cadet/src/certify_SAT.c`.

Pedant's min-separator conflicts (`TODO-cover.md`) are a different cut of
the same graph, and `cegr` already does a version of the repair with
`y_order`: check whether (2) can share code with it before writing it.

## What could be kept from the try without all that

Propagation alone gives functions for three quarters of the vars of
AR-fixpoint-1 in 4 s, where Puura takes over 100 s. As a first pass that
only defines vars (no decisions, so every function is forced by F) it is
sound for `--synth` and `--2qbf`. Unmeasured: whether Puura, extend and
backward then go faster, and on which families it determines anything.

## Not this: `ci`

The 4 false `ci` files are not this problem. `--2qbfpre` already gives
what bloqqer gives without expansion (800 clauses, 63 existentials, 42
universals). Covering ran 335000 rounds on one with no X found; RAReQS
finds it in 130 s, in 8 s after bloqqer expands 2 universals. Helpers
decided true in abs found one in 17 s, and made 3 false sortnetsort files
slower (36 s -> over 60 s on one). Which X abs picks decides it: nothing
there to merge yet.
