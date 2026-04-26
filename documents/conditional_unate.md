# `unate_def`: plain unate, unate-with-def, and conditional unate

This document explains what `src/unate_def.cpp` does. It assumes you know
SAT/CNF basics but nothing about Padoa-style definability or how Arjun
splits variables into *inputs* and *to-define*.

## Background

### Variable roles in Arjun

Every CNF variable in Arjun ends up in one of three buckets (see
`SimplifiedCNF::get_var_types` in `arjun.h`):

- **input**: a variable we are NOT trying to eliminate. The independent set.
- **backward_defined**: a non-input variable that already has a known AIG
  definition `H_v(X, ...)` in terms of inputs (and possibly other defined
  vars). Stored on `SimplifiedCNF::defs`.
- **to_define**: a non-input variable we are still trying to either fix or
  define.

The goal of `unate_def` is to whittle down `to_define` — by either fixing
a variable to a constant (a unit clause) or by giving it an AIG definition
in terms of inputs.

### What "unate" means

A Boolean function `F` is **unate in variable `v`** if it is monotone in
`v`: either every model of `F` stays a model when `v` is flipped 0→1
("positive unate"), or every model stays a model when flipped 1→0
("negative unate"). In a SAT-preprocessing context, if `v` is positive
unate in `F`, we can safely add the unit clause `v` (setting it to TRUE
never loses any model), and likewise add `¬v` if negative unate.

So a **unate finding produces a unit clause**, not a definition.

### The `F ∧ ¬F` encoding

`setup_f_not_f` builds one big SAT instance over **two copies** of the
variables:

- copy `Y` of size `nVars()`: encodes `F(X, Y)` directly.
- copy `Y'` of size `nVars()` (offset by `nVars()`): encodes `¬F(X, Y')`,
  using a per-clause Tseitin variable `z_c` ("clause `c` is true on
  Y'-side") and the side constraint "at least one `z_c` is false".

Crucially, **inputs `X` are shared** between the two copies — the same
literal is reused. Only `to_define` and `backward_defined` vars are
duplicated.

So the joint solver is satisfiable iff there exist two assignments
`(X, Y)` and `(X, Y')` sharing the same `X`, such that `F(X, Y)` holds
but `F(X, Y')` does not.

### Indicator variables

For each non-input var `i`, the code adds a fresh "indicator" `ind_i`
with the meaning *`ind_i = TRUE` iff `Y_i = Y'_i`*. This lets us pin
parts of the two copies together by simply assuming `ind_i` as a literal.

---

## 1. Plain unate (`synthesis_unate`)

### The probe

For each candidate `test` ∈ `to_define`, and for each direction
`flip ∈ {0, 1}`:

```
assume:
  ind_i   = TRUE  for every other non-input i  (i.e. Y_i = Y'_i)
  Y_test  = flip
  Y'_test = !flip                               (the two copies disagree on test)
```

If the solver returns **UNSAT** for, say, `flip = 0`:

> There is no `(X, Y, Y')` with `Y_test = 0`, `Y'_test = 1`, all other Ys
> agreeing, that satisfies `F(X, Y) ∧ ¬F(X, Y')`.
>
> Equivalently: whenever `F(X, Y)` holds with `Y_test = 0`, flipping
> `Y_test` to 1 (keeping all other Y the same) **also** satisfies `F`.
>
> So `F` is positive unate in `test`. Adding the unit `test` is safe.

The code then adds `Lit(test, flip=0)` = positive `test` as a unit
clause to both the original CNF and the joint solver.

If `flip = 1` is UNSAT instead, the analogous unit `¬test` is added.

### Example — clean unate

CNF (using DIMACS-ish notation, inputs `X = {1}`, to-define `Y = {2, 3}`):

```
F = (¬1 ∨ 2) ∧ (1 ∨ 2 ∨ 3)
```

Test `var 2`:

- `flip = 0`: assume `Y_2 = 0`, `Y'_2 = 1`, `ind_3 = TRUE` (so
  `Y_3 = Y'_3`). Joint problem `F(X, Y) ∧ ¬F(X, Y')` becomes
  unsatisfiable: any `(X, Y)` with `Y_2 = 0` satisfying `F` (e.g.
  `X=0, Y_3=1`) trivially also satisfies `F` after flipping `Y_2 → 1`.
- So we add the unit clause `2`.

Variable `2` got *fixed*, not defined. We learned the value, no AIG
needed. This is the result `synthesis_unate` produces.

---

## 2. Unate with "def" (`synthesis_unate_def`)

The "def" suffix refers to two distinct things, both happening in the
same function:

1. **Reusing previously known definitions** (`backward_defined`) when
   building the joint solver, so the probes can prove more.
2. **Producing new definitions** for vars that are not pure unate but
   collapse to a single input literal under a case split — the
   *conditional* unate-def case (next section).

This subsection covers (1).

### Why backward_defined vars get special treatment

Backward-defined vars already have AIG definitions of the form
`v ↔ H_v(X, ...)`. On the *original* `Y`-side, that relationship is
already implied by `F(X, Y)`. On the **`Y'`-side we have `¬F`**, which
does *not* imply `v' ↔ H_v(X, Y'_other)`. Without help, the solver is
free to pick a `Y'` that violates the known definition, weakening every
probe we run.

So `synthesis_unate_def` walks each backward-defined var `i` and adds,
on the copy side only, the constraint

```
Y'_i ↔ H_i(X, Y'_other)
```

This is the loop at `unate_def.cpp:65`. The AIG is "transformed" into
fresh CNF clauses on the copy side via `aig_to_copy_visitor`. Inputs
inside the AIG resolve to the **shared** input literal (no copy).

Note also: `synthesis_unate_def` only allocates indicator vars for
to-define vars — backward-defined vars get no indicator (they don't
need one; the AIG def pins them already).

### Example — unate that *uses* a known def

Inputs `X = {1}`, backward_defined `{2}` with known def `2 ↔ 1`,
to-define `{3}`:

```
F = (¬1 ∨ 2) ∧ (1 ∨ ¬2) ∧ (¬2 ∨ 3) ∧ (2 ∨ 3)
```

(Rewritten using `2 = 1`, this collapses to `(¬1 ∨ 3) ∧ (1 ∨ 3)`,
i.e. `3 = TRUE`. But the solver doesn't know to do that substitution.)

Probe `var 3`, `flip = 0`:
- assume `Y_3 = 0`, `Y'_3 = 1`. No indicator on `Y_2` — instead the AIG
  def constraint pins `Y'_2 ↔ X_1` directly on the copy side.
- This forces `Y'_2 = X_1`. With `Y_3 = 0`, the clauses
  `(¬2 ∨ 3) ∧ (2 ∨ 3)` give `Y_2 = (anything)` impossible. So already
  `F(X, Y) ∧ Y_3 = 0` is unsatisfiable, the joint problem is too →
  UNSAT → unit `3` learned.

Without the explicit `Y'_2 ↔ X_1` constraint on the copy side, a
different style of probe (e.g. checking that flipping is safe under all
choices of the unconstrained `Y'_2`) might fail to be UNSAT. That's
the *def reuse* benefit.

### Example — non-def unate (just plain fixing)

Same as the §1 example, but the variable is not yet known to be
defined. The unate probe still finds it and adds a unit. The result is
recorded as `cnf.add_clause({l})` (a unit), **not** as `cnf.set_def(...)`
— because we only learned the constant value, not a functional
dependence on inputs. This is what `synthesis_unate_def` does in the
top of its inner loop, before the conditional block kicks in.

So: "non-def unate" = "plain unate within the def-aware solver" =
adds a unit, no AIG.

---

## 3. Conditional unate definition

This is the new piece. Plain unate fails when neither flip is UNSAT —
both `(Y_test = 0, Y'_test = 1)` and `(Y_test = 1, Y'_test = 0)` admit
witnesses. But the variable might still be *definable* by a single
input literal **under a case split on that input**.

### The free witnesses

When the two flips both come back SAT, the solver has handed us two
models for free:

- `M_0`: flip=0 was SAT — there is `(X, Y, Y')` with `Y_test = 0` and
  `Y'_test = 1`.
- `M_1`: flip=1 was SAT — there is `(X, Y, Y')` with `Y_test = 1` and
  `Y'_test = 0`.

The code stashes these in `model_for_flip[0]` / `model_for_flip[1]` so
we don't have to re-issue SAT calls just to find candidates.

### Picking a candidate input `L`

For each input variable `L` (sorted, deterministic), let
`v1 = M_0[L]` and `v2 = M_1[L]`.

- If `v1 == v2`, `L` had the same value in both witnesses, so it cannot
  possibly explain why `test` differs between them — skip.
- If `v1 ≠ v2`, `L` is a candidate: the witnesses already show that
  toggling `L` correlates with toggling `test`.

A budget cap (`unate_def_cond_max_per_var`) limits how many candidates
we try per `test`.

### The two probes

We want to prove: under `L = v1`, `test` is forced to 0; under
`L = v2`, `test` is forced to 1.

`M_0` already witnesses `(L = v1, test = 0)` is **possible** in `F`
(that side of the joint problem was SAT). What we need to rule out is
`(L = v1, test = 1)`. So we probe:

```
probe 1: assume L = v1, Y_test = 1, Y'_test = 0   (and same indicators as before)
         If UNSAT → under L = v1, test cannot be 1 → test = 0.

probe 2: assume L = v2, Y_test = 0, Y'_test = 1
         If UNSAT → under L = v2, test cannot be 0 → test = 1.
```

(Each probe runs with a conflict budget `unate_def_cond_max_confl` so a
hard probe doesn't blow up the whole pass.)

If both probes return UNSAT we have proven:

```
L = v1   ⟹   test = 0
L = v2   ⟹   test = 1
```

and `L` is a Boolean variable so `{v1, v2} = {0, 1}` (in some order).
Therefore `test` is a deterministic function of `L`:

- If `v1 = FALSE`: `L=0 ⟹ test=0` and `L=1 ⟹ test=1`, so `test = L`.
- Else (`v1 = TRUE`): `test = ¬L`.

This is recorded as `cnf.set_def(test_orig.var(), AIG::new_lit(...))`.
The signs are translated through the new↔orig variable map (lines
275–293), but the core relationship is just `test = L` or `test = ¬L`.

### Example — conditional unate

Inputs `X = {1, 2}`, to-define `{3}`:

```
F = (1 ∨ ¬3) ∧ (¬1 ∨ 3) ∧ (2 ∨ 3 ∨ ...) ∧ (¬2 ∨ ¬3 ∨ ...)
```

The first two clauses encode `3 ↔ 1`. Plain unate probing won't find a
direction that's safe to flip: there are clearly models where `3 = 0`
(then `1 = 0`) and others where `3 = 1` (then `1 = 1`), so neither flip
of var 3 is unconditionally safe.

But the conditional probe will:

- `M_0`: flip=0 witness has `Y_3 = 0`, `Y'_3 = 1`, and (forced)
  `X_1 = 0`. So `v1 = M_0[1] = FALSE`.
- `M_1`: flip=1 witness has `Y_3 = 1`, `Y'_3 = 0`, forced `X_1 = 1`.
  So `v2 = M_1[1] = TRUE`.
- `v1 ≠ v2`, so var 1 is a candidate.
- Probe 1: assume `X_1 = 0`, `Y_3 = 1`, `Y'_3 = 0`. The clause
  `(¬1 ∨ 3)` becomes trivially satisfied; `(1 ∨ ¬3)` with `X_1 = 0`
  forces `Y_3 = 0`, contradicting the assumption `Y_3 = 1`. UNSAT.
- Probe 2 mirrors and is UNSAT.
- `v1 = FALSE`, so the recorded def is `test = L`, i.e. `3 = 1`.

The def is added to the AIG store via `set_def`, and clauses
`Y_test ↔ L` and `Y'_test ↔ L` are added on both sides of the joint
solver to tighten subsequent probes.

### Adaptive disable

The conditional probe is expensive: up to `2 ×
unate_def_cond_max_per_var` SAT calls per test, each with a conflict
budget. To avoid burning time on hopeless inputs, the code tracks
`cond_attempts_since_last_hit`. If 64 consecutive tested vars produced
no conditional def *and* the global hit count is still zero, conditional
probing is turned off for the rest of the run (`unate_def.cpp:318`).

---

## Summary table

| Pass                          | Probe                                                    | If UNSAT, output         |
|-------------------------------|----------------------------------------------------------|--------------------------|
| Plain unate                   | `Y_test ≠ Y'_test`, all other non-input Y agree          | Unit clause for `test`   |
| Unate-def, normal probe       | Same, plus AIG def of every backward_defined var on `Y'` | Unit clause for `test`   |
| Unate-def, conditional probe  | Add `L = vk` to a flipped probe; do this for both `vk`   | AIG def `test = ±L`      |

The first two add unit clauses (i.e. fix `test` to a constant). Only
the conditional case produces a new AIG definition — and only the
single-input-literal kind. Anything richer is left to later passes
(Manthan, etc.).
