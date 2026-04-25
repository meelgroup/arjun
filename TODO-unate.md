# Research: theoretical gaps in `unate_def`

## What `unate_def` actually proves today

The current test, formalised: with the dual-rail miter `F(X, Y) ∧ ¬F(X, Y')` and indicators `ind_i ↔ (y_i = y'_i)`, for each `y_test`:

> Assume `ind_k = TRUE` for all `k ≠ test`, plus `y_test = a, y'_test = ¬a`.
> If UNSAT, declare `y_test` "unate at `a`" and pin it as a unit.

UNSAT here means: **flipping `y_test` from `a` to `¬a` (with all other `y` fixed) never breaks `F`.** I.e. `F` is monotone (non-decreasing if `a = false`, non-increasing if `a = true`) in `y_test`.

That's the **monotonicity** test. It's *not* the **definability** test. Two related but distinct properties:

| Property | Setup | Conclusion |
|---|---|---|
| **Unate at `a`** (today) | `F(X,Y) ∧ ¬F(X,Y') ∧ y=a ∧ y'=¬a ∧ rest equal` | Setting `y=¬a` is always safe → can pin to `¬a` |
| **Padoa-defined** | `F(X,Y) ∧ F(X,Y') ∧ y ≠ y' ∧ rest equal` | `y` is uniquely determined by the rest → has a definition `φ` |
| **Equivalent to z** | `F(X,Y) ∧ y ≠ z` | `y = z` in every model (special case of Padoa) |

The three are nested: **backbone ⊂ unate ⊂ Padoa-defined**. Today `unate_def` finds the middle layer. The outer layer is partly handled elsewhere (`backward.cpp` + `interpolant.cpp` extracts Padoa definitions over a *small input subset* via UNSAT-core interpolation), but several flavours fall through the cracks.

## What's missed — concretely

### 1. Equivalences with another to-define var (HIGH VALUE, EASY)

If `F → (y_i ↔ y_j)` (or `y_i ↔ ¬y_j`), neither var is unate by itself (each can take both values), and `backward.cpp` won't define `y_i` over inputs alone (its support set is `{y_j}`). Today such pairs survive into Manthan and burn repair iterations.

**Test**: on the *plain* `F(X,Y)` solver (not the dual-rail), `solve(assumps = {y_i, ¬y_j})`. If UNSAT → `F → (y_i → y_j)`. Combine the two directions to get equivalence.

**Cost**: O(pairs of survivors). Naively quadratic, but the candidate set can be pruned by simulation first (FRAIG-style): generate K random satisfying assignments via `cmsgen` (already wired), bucket vars by their value-vector signature, only SAT-test pairs in the same bucket. This is exactly what `aig_rewrite.cpp::sat_sweep` already does for AIG nodes — applied to to-define CNF vars instead.

**Extraction**: trivial AIG: `y_i = y_j` (or `¬y_j`) — a one-node AIG, no interpolation needed.

### 2. Equivalence with an input (HIGH VALUE, EASY)

Special case of the above: `y_i = x` or `y_i = ¬x`. Same SAT call. Same trivial extraction. Worth doing as a separate pass because it lets us *delete* `y_i` entirely from the to-define set.

### 3. Iterative fix-pointing (CHEAP)

The current loop walks `to_define` once. A var that fails the unate test early can become unate after later vars are pinned (because the added unit clauses propagate). The Lagniez-Marquis paper explicitly relies on this cascading effect.

**Fix**: wrap the test loop in `while (new_units > 0) { run_pass; }` until the round adds nothing. On benchmarks where one or two unit clauses unblock a chain (typical of structured circuits like the qdimacs ones), this can multiply the yield.

### 4. Padoa-defined-not-unate detection over the **Y** support (HIGH VALUE, MEDIUM EFFORT)

`backward.cpp` runs a Padoa test over the **input** support (does `y` depend only on `X`?). It does *not* do the same test over `X ∪ Y\{y}` for cases where `y` happens to be uniquely defined by the rest of the to-define set.

The `F ∧ F` miter (the Padoa setup) gives this directly: with the same indicator infrastructure that `unate_def` already builds, swap "at least one clause of `F(X,Y')` is false" for "`F(X,Y')` holds." Then `assume rest-equal ∧ y ≠ y'` UNSAT ⇒ uniquely defined.

Extraction is the harder part — needs interpolation. But arjun already has `interpolant.cpp` (it does this for `backward.cpp`). The reuse is mostly plumbing.

### 5. Conditional unate (1-step look-ahead) (MEDIUM VALUE)

`y_i` may not be unate, but become unate when `y_j = b` is added as a unit. Detection: for each pair `(y_i, y_j)`, test the unate condition with `y_j = b` *added to the assumps*. If UNSAT for some `(b, flip)` combo, define `y_i = ITE(y_j = b, c, free)` — only the `b`-branch is fixed, the other branch goes to Manthan.

Even capturing only the easy case (`y_i` becomes a constant under one polarity of `y_j`) gives a 1-bit conditional definition that takes the var out of the repair loop on the fixed side.

Cost: 4 SAT calls per pair, but bounded by `to_define ×` a small "candidate-y_j" list (e.g., recently-pinned vars).

### 6. Syntactic gate detection (CHEAP, no SAT calls)

CNF clauses that pairwise encode a gate identity:

- `(¬x ∨ a) ∧ (x ∨ ¬a)` ⇒ `x ↔ a`
- `(¬x ∨ a ∨ b) ∧ (x ∨ ¬a) ∧ (x ∨ ¬b)` ⇒ `x ↔ a ∧ b`
- analogous OR / XOR templates

Lagniez-Marquis explicitly use this as a syntactic fast-path before the SAT-based Padoa test. For arjun-style benchmarks (Tseitin-encoded circuits), gate templates are pervasive — a CNF scan over to-define vars likely catches a non-trivial fraction without ever touching the solver.

Extraction is direct: the matched template *is* the AIG.

### 7. Pure-literal pre-pass (TRIVIAL)

If a to-define `y` appears with only one polarity in `F`, it is unate at the *opposite* polarity, no SAT call needed. (CMS's preprocessing finds this for normal vars but the dual-rail solver here is fresh — the syntactic check on `F` itself is essentially free.)

## Recommended ordering by value/cost

| # | Improvement | Implementation cost | Expected yield |
|---|---|---|---|
| 7 | Pure-literal pre-pass on `F` | Trivial (CNF scan) | Small but free |
| 3 | Iterative fix-point of current pass | Trivial (outer while-loop) | Low–medium |
| 6 | Syntactic gate detection | Small (template matching) | Medium (Tseitin-heavy benchmarks) |
| 1 | Equivalence between to-define vars (sim+SAT) | Medium (port `sat_sweep` strategy) | **High** — these often dominate the survivors after `backward.cpp` |
| 2 | Equivalence with input | Medium | **High** for circuit benchmarks |
| 4 | Padoa over `X ∪ Y\{y}` + reuse interpolant | Larger | High, but overlaps with what Manthan repairs eventually find anyway |
| 5 | Conditional unate | Larger | Modest |

The **biggest theoretical win is #1**: `sat_sweep`-style equivalence detection on the to-define set. Conceptually it just lifts the same trick `aig_rewrite` already applies to AIG nodes (simulation buckets → SAT-verify candidates) onto the CNF survivors of `backward.cpp`. The literature (Lagniez-Marquis 2016, 2019) calls these out as the workhorse cases, and the extraction is degenerate (a single edge in the AIG).

The second-biggest win, conceptually, is the **Padoa-over-rest test (#4)** — that's literally what the Lagniez-Marquis "definability bipartition" paper does, and arjun already owns the interpolant machinery. The reason it's lower priority is that for arjun's pipeline, those vars eventually *do* get defined by Manthan; the savings are repair-loop time, not correctness.

## A concrete next implementation

If you want one PR that covers most of the gap with minimal disturbance, the suggested shape is:

1. **A new pass `unate_iterate(cnf)`** that wraps `synthesis_unate_def` in a fix-point loop (#3), preceded by a pure-literal scan (#7) and a small set of syntactic gate templates (#6).
2. **A new pass `equivalence_def(cnf)`** that runs *after* `unate_def`, uses `cmsgen` to bucket survivors by their value vector across K samples, and SAT-verifies in-bucket pairs. Equivalences materialise as tiny AIGs and the var moves from `to_define` to `backward_defined`.

Both passes plug into the existing `MetaSolver` / `add_clause` infrastructure and the existing `interpolant.cpp` is unchanged (no new interpolation needed for #1).

## Sources
- [Lagniez & Marquis, *Improving Model Counting by Leveraging Definability* (IJCAI 2016)](https://www.ijcai.org/Proceedings/16/Papers/112.pdf)
- [Lagniez & Marquis, *Definability for Model Counting* (Artificial Intelligence 2019)](https://www.sciencedirect.com/science/article/pii/S0004370218303928)
- [Lagniez & Marquis, *Boosting Definability Bipartition Computation Using SAT Witnesses* (JELIA 2023)](https://link.springer.com/chapter/10.1007/978-3-031-43619-2_47)
- [Golia, Roy & Meel, *Manthan: A Data-Driven Approach for Boolean Function Synthesis* (CAV 2020)](https://link.springer.com/chapter/10.1007/978-3-030-53291-8_31)
- [Akshay et al., *Engineering an Efficient Boolean Functional Synthesis Engine* (ICCAD 2021)](https://arxiv.org/abs/2108.05717)
- [Akshay et al., *Boolean functional synthesis: hardness and practical algorithms* (FMSD 2020)](https://link.springer.com/article/10.1007/s10703-020-00352-2)
