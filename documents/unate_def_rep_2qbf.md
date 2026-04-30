# Why `unate_def_rep` cost-zero is a 2QBF problem in disguise

This note explains a structural limitation of
`src/unate_def_rep.cpp`'s guess-and-refine loop: the question it is asking
is genuinely a 2QBF (∀∃) problem, and any single SAT-solver encoding can
only over- or under-approximate it. The "cost-zero" CEXes the pass keeps
hitting are not a tuning issue — they are the visible artefact of that
approximation.

## The actual question

For a single to-define variable `t`, we want to commit a Skolem function
`h(X)` (over inputs only) iff

```
∀X. (∃ y_test, y_other.  F(X, y_test, y_other))
        ⇒
    (∃ y_other'.          F(X, h(X), y_other'))
```

Read this carefully — there is an existential **inside** a universal. The
inner `∃ y_other'` says "there is *some* witness for the rest of the
to-define vars that makes `F` hold at `h(X)`." That is the precise
Skolem-validity condition.

A single SAT call can encode `∃` natively. It cannot encode `∀∃` natively
— the alternation is one quantifier deeper than SAT decides.

## What `unate_def_rep`'s miter actually checks

The current pass forms

```
F(X, Y)  ∧  ¬F(X, Y')          ← search for a CEX
y_test'  =  h(X)               ← Y'-side y_test forced to candidate
y_i'     =  y_i  for every other to-define i   ← indicator-pinning
```

and asks the SAT solver for SAT/UNSAT. UNSAT means the formula has no
assignment, which (after ¬-flipping) means

```
∀X, y_test, y_other.  F(X, y_test, y_other)  ⇒  F(X, h(X), y_other)
```

— *the same* `y_other` works on both sides. That is **strictly stronger**
than Skolem-validity: it requires the existing y_other witness to also
satisfy `F` at `h(X)`, instead of just *some* y_other witness. So the
miter is conservative — UNSAT implies Skolem-OK, but SAT does not imply
the converse.

The CEXes the miter produces are not necessarily real refutations of `h`.
The F-only call (`F(X*, y_test = h(X*))?`) is the second-stage filter
trying to recover the `∃ y_other'` semantics: if it returns SAT, it
witnesses that *some* `y_other'` makes `h(X*)` consistent, so the miter
SAT was a false alarm. We call that **cost-zero**, and it is exactly the
2QBF gap reasserting itself: the miter said "no" using `∀ y_other'`
semantics; the F-only call said "yes" using `∃ y_other'` semantics.

## "Just drop the pinning" doesn't fix it

A natural reflex is to weaken the miter: if pinning is too strong, drop
it. Without pinning the miter becomes

```
F(X, Y) ∧ ¬F(X, Y')           with both y_other and y_other' free
y_test' = h(X)
```

UNSAT here means

```
∀X, Y, Y'.  F(X, Y) ⇒ F(X, Y' with y_test' = h(X))
```

— "for *every* `y_other'`, `F` holds at `h(X)`." That is also strictly
stronger than Skolem-validity (which only needs *some* `y_other'`), just
in a different direction. SAT still does not imply a real refutation:
whenever F is bifunctional at some X* — i.e. `F` admits both `y_test = 0`
and `y_test = 1` with different y_others — the miter happily produces
a SAT witness (Y picks one branch, Y' picks the ¬F-witness on the other)
even though `h` may be perfectly fine at X*. The F-only call now confirms
`F(X*, h(X*))` is satisfiable on its own, with no pattern to extract.

So both extremes are over-approximations of Skolem-validity. There is no
choice of pinning that makes the cost-zero problem go away while keeping
SAT as the only oracle. The gap is structural.

## Off-the-shelf 2QBF backends

A real 2QBF solver can answer the question directly. The relevant tools:

- **CADET** — built specifically for 2QBF Skolem-function synthesis.
  Returns a Skolem certificate, not just SAT/UNSAT. Closest semantic
  match to what `unate_def_rep` is hand-rolling.
- **DepQBF**, **CAQE**, **Quabs**, **RAReQS** — general QBF solvers
  with CEGAR-flavoured 2QBF specialisations. Most expose a way to
  extract a Skolem function on a true answer.

Concretely, dispatching only the variables that hit `costzero_limit` to
such a solver would keep the SAT-fast path and let a sound oracle close
out the residual cases. The cost is a build-time dependency and the risk
that 2QBF solvers themselves time out on large `F`s — they are not free.

## Rolling our own 2QBF-CEGAR

The same idea without an external dependency, sketched as a per-`test`
loop:

- **Sample set `S`.** A list of witnesses
  `(X*, y_other_F*)` where `F(X*, y_test_F*, y_other_F*)` holds. Start
  empty.
- **Inner ∃-step.** Find an `h` such that for every `(X*, y_other_F*) ∈
  S`, `F(X*, h(X*), some_y_other')` is satisfiable. Concretely a SAT
  call where `h` is encoded as a small circuit template (LUT, decision
  tree, k-bounded AIG) and `y_other'_per_sample` are existentials.
- **Outer ∀-step.** With this `h`, look for a refuting `X**` via a miter
  similar to today's.
  - Treat the result as a real refutation **only after** a separate
    F-only `∃`-check `F(X**, h(X**))?`. If that's SAT, you've hit
    F-bifunctionality at X**, and `h(X**)` is genuinely free; instead
    of "refining `h`", append the new witness `(X**, y_other_F**)` to
    `S` and re-run the inner step.
  - If F-only is UNSAT, you have a real input-only conflict; either
    refine `h` directly (current path) or include the conflict in `S`
    as a hard constraint.

This is a 2QBF-CEGAR loop. It dodges the over-approximation by
maintaining `S` as ground truth and letting `h` be redrawn each time
`S` grows. Manthan does essentially this at the whole-CNF level; the
sketch above is the per-variable analogue and could plug into the same
call site `unate_def_rep` already occupies.

## Where this leaves the current pass

`unate_def_rep` is best understood as a **fast best-effort** Skolem
synthesizer: when the SAT-only approximation happens to coincide with
the real 2QBF answer, it commits cheaply; otherwise it bails on the
cost-zero budget and the variable falls through to Manthan, which has
its own holistic CEGAR loop and is not bound by the per-var miter.
Tuning `--unatedefrepmaxcz` low (3–5) and trusting the handoff is the
practical lever short of pulling in a real 2QBF backend.
