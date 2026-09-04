# Copy/paste prompt: P18 global smooth gradient witness

You are the P18 worker for the second parallel Chapter 6 batch in the
`lean_rockafellar` repository. Complete the everywhere-`C¹`, unique-global-
maximum witness clause of Rockafellar--Wets Theorem 6.11. Work only in the
assigned new Lean file, prove every declaration, and commit it.

## Starting state and branch

Use an isolated checkout and create `chapter6-p18-smooth-gradient-witness`
from exactly:

```text
9fa1c19eab36f7fc79845f679d35b87344366e0b
```

Before editing, run:

```text
git rev-parse HEAD
git status --short
```

`HEAD` must be the exact hash above and the worktree must be clean. Do not
merge, rebase, or cherry-pick another worker branch. Do not reset or overwrite
an existing branch; stop and report a blocker if the starting state differs.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/SmoothGradientWitness.lean
```

Do not edit any existing source file, `README.md`, `CHAPTER6_COVERAGE.md`, any
other ledger, `RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, lake
configuration, or anything under `parallel_tasks/`. Do not edit files owned by
P16 or P17. Place every declaration in `namespace RW`.

## Exact printed scope

Theorem 6.11 in `rockafellar_wets.pdf` (printed pp. 205--206) says that `v` is
a regular normal to `C` at `x` iff it is the gradient at `x` of a function
differentiable there and locally maximized relative to `C`. It then strengthens
the witness: the function may be chosen smooth on the whole ambient space and
its global maximum relative to `C` is achieved uniquely at `x`.

`GradientNormals.lean` already proves the local/differentiable equivalence and
constructs a globally maximizing witness differentiable only at `x`.
`SmoothMajorant.lean` already supplies the scalar `C¹` strict majorant. This
task owns the missing assembly into an everywhere-`C¹` ambient witness.

## Main theorems

Work over a real Hilbert space at the same generality as
`GradientNormals.lean`:

```lean
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} {x v : E}
```

Prove the forward construction with a stable public name and essentially this
shape:

```lean
theorem exists_contDiff_one_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone
    (hv : v ∈ regularNormalCone C x) :
    ∃ h : E → ℝ,
      ContDiff ℝ 1 h ∧
      HasGradientAt h v x ∧
      IsMaxOn h C x ∧
      ∀ y ∈ C, h y = h x → y = x
```

Conjunct order or a modestly shorter name may differ, but all four properties
must be present. Then package the exact smooth-witness characterization:

```lean
theorem mem_regularNormalCone_iff_exists_contDiff_one_unique_isMaxOn_hasGradientAt
    (hx : x ∈ C) :
    v ∈ regularNormalCone C x ↔
      ∃ h : E → ℝ,
        ContDiff ℝ 1 h ∧
        IsMaxOn h C x ∧
        (∀ y ∈ C, h y = h x → y = x) ∧
        HasGradientAt h v x
```

For the reverse implication, localize `IsMaxOn` and reuse
`mem_regularNormalCone_of_isLocalMaxOn_hasGradientAt`; do not duplicate its
epsilon proof. Do not add finite-dimensional, convexity, closedness, or
regularity hypotheses.

## Required construction

Follow the printed proof. From `hv`, build a nonnegative radial modulus
`θ₀ : ℝ → ℝ` measuring the positive part of
`⟪v, y - x⟫` over feasible points within radius `r`. A robust definition uses
`sSup` of a set containing `0`, with `max r 0` (or an explicit nonpositive
branch) so it is globally defined. Prove the reusable facts needed by
`exists_contDiff_one_strict_majorant`:

```lean
MonotoneOn θ₀ (Set.Ici 0)
θ₀ 0 = 0
Tendsto (fun r ↦ θ₀ r / r)
  (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

Also prove the domination property: for `y ∈ C`, with
`r = ‖y - x‖`, the positive part of `⟪v, y - x⟫` is at most `θ₀ r`.
The `sSup` set is nonempty because it contains zero and bounded above by
`r * ‖v‖` by Cauchy--Schwarz. The regular-normal inequality gives the
first-order decay. Keep technical modulus declarations private unless their
API is independently clean and useful.

Apply:

```lean
exists_contDiff_one_strict_majorant
```

to obtain an everywhere-`C¹` scalar function `θ` with `θ 0 = 0`,
`HasDerivAt θ 0 0`, and `θ₀ r < θ r` for `r > 0`. Define the ambient
witness exactly in the book's form:

```lean
h y := ⟪v, y - x⟫_ℝ - θ ‖y - x‖.
```

Then show:

- `h x = 0`;
- for every `y ∈ C` with `y ≠ x`, positivity of `‖y-x‖` and strict
  majorization give `h y < h x`;
- hence `IsMaxOn h C x` and equality at the maximum forces `y = x`;
- the radial penalty has derivative zero at `x`, so `HasGradientAt h v x`.

Do not replace the strict scalar majorant by the old discontinuous/max-based
witness from `GradientNormals.lean`; the point of this task is global `C¹`
smoothness.

## Required radial-composition lemma

The main analytic bridge should be a reusable theorem saying that a scalar
`C¹` function with zero derivative at the origin composes smoothly with the
norm. A suitable shape is:

```lean
theorem contDiff_one_comp_norm_sub
    {theta : ℝ → ℝ} (htheta : ContDiff ℝ 1 theta)
    (htheta0 : HasDerivAt theta 0 0) (x : E) :
    ContDiff ℝ 1 (fun y : E ↦ theta ‖y - x‖)
```

An equivalent centered-at-zero lemma plus a translated corollary is fine.
This lemma must not assume `theta` is even, polynomial, or twice
differentiable.

At points `y ≠ x`, differentiate by composing `theta` with the Hilbert-space
norm. At `x`, use `HasDerivAt theta 0 0` (equivalently the little-o estimate)
to get zero Fréchet derivative despite nondifferentiability of the norm at
zero. To prove the derivative field is continuous at `x`, use continuity of
`deriv theta`, `deriv theta 0 = 0`, and the norm-one bound for the derivative
of the norm away from zero. The following proof patterns are relevant:

- `contDiff_one_iff_hasFDerivAt` or `contDiff_one_iff_fderiv`;
- `contDiffAt_norm`/`DifferentiableAt.norm` away from zero;
- `hasGradientAt_iff_isLittleO` at the center;
- `ContDiff.continuous_fderiv`, `gradient_eq_deriv'`, and
  `norm_fderiv_norm`;
- the Hilbert formula for the derivative of the norm via `innerSL`, if an
  explicit continuous derivative field is simpler.

Handle the subsingleton ambient space cleanly if a norm-derivative theorem
requires `[Nontrivial E]`; do not add `[Nontrivial E]` to the public result
merely for convenience.

## Relevant existing APIs

- `RockafellarWets/Chapter6/GradientNormals.lean`
  - `mem_regularNormalCone_of_isLocalMaxOn_hasGradientAt`
  - `exists_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone`
  - `mem_regularNormalCone_iff_exists_isLocalMaxOn_hasGradientAt`
- `RockafellarWets/Chapter6/SmoothMajorant.lean`
  - `exists_contDiff_one_strict_majorant`
- `RockafellarWets/Chapter6/NormalCones.lean`
  - `mem_regularNormalCone`, `mem_regularNormalCone_iff`
- Mathlib:
  - `csSup_le`, `le_csSup`, `bddAbove_def`, `Real.inner_le_norm`
    (check the exact Cauchy--Schwarz lemma already used in this repository);
  - `hasGradientAt_iff_isLittleO`, `hasGradientAt_iff_hasFDerivAt`;
  - `Mathlib.Analysis.InnerProductSpace.Calculus`, including norm and inner
    derivative formulas;
  - `contDiff_one_iff_hasFDerivAt`, `contDiff_one_iff_fderiv`.

Inspect exact signatures in the pinned Mathlib checkout rather than guessing.
Small private `sSup`, tail-estimate, and radial-derivative lemmas are expected.

## Exclusions

- Do not alter or duplicate the scalar averaging construction in
  `SmoothMajorant.lean`.
- Do not settle for `DifferentiableAt h x`, local smoothness, `ContDiffAt`, or
  a non-unique maximum: the printed strengthening requires `ContDiff ℝ 1 h`
  on the whole ambient space and a unique global maximum on `C`.
- Do not assume `C` is closed, convex, nonempty beyond what `hv` entails, or
  bounded.
- Do not add finite-dimensional assumptions; the radial construction works in
  a real Hilbert space.
- Do not formalize limiting normals or Theorem 6.12.
- Do not use `sorry`, `admit`, `axiom`, linter suppression, placeholder
  declarations, or unsafe shortcuts.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/SmoothGradientWitness.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/SmoothGradientWitness.lean
git diff --check
git status --short
```

The search must have no matches and status must list only the assigned file.
Do not add an umbrella import merely to test it. Commit only that file:

```text
git add RockafellarWets/Chapter6/SmoothGradientWitness.lean
git commit -m "Complete smooth gradient witness theorem"
```

Report the commit hash, theorem inventory, exact radial-composition API,
whether any requested theorem shape needed adaptation, and all verification
commands and outcomes.
