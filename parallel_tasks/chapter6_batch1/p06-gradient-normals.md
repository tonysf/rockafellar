# P06 — Gradient characterization of regular normals (core 6.11)

You are implementing an isolated Chapter 6 work package in the
`lean_rockafellar` repository. Work only on the branch and file assigned
below. The result must be production Lean code, not a sketch.

## Git contract

- Start from the exact base commit
  `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Create and work on the branch `chapter6-p06-gradient-normals`.
- Before editing, verify that `git rev-parse HEAD` is `b2eb4ea` (the full hash
  may be shown by Git).
- Your required final commit message is:
  `Chapter 6: characterize regular normals by gradients`

## Exclusive file ownership

You may create or edit exactly one repository file:

`RockafellarWets/Chapter6/GradientNormals.lean`

Do not edit any other file. In particular, do not edit `README.md`, any
`CHAPTER*_COVERAGE.md` ledger, `RockafellarWets.lean`,
`RockafellarWets/Chapter6.lean`, any batch index or shared contract under
`parallel_tasks/`, or a Lean file assigned to another prompt. Do not add an
umbrella import. Integration will be done separately.

Place every new declaration in `namespace RW`.

## Objective

Formalize the differentiable-at-the-base-point equivalence in Theorem 6.11:
a vector is a regular normal exactly when it is the gradient at the point of
a function having a local maximum there relative to the set. Also construct
a witness with a unique global relative maximum. This task deliberately does
not own the final globally `C¹`/smooth strengthening; the scalar smoothing
infrastructure is a separate work package.

Work over a real complete inner-product space (or a finite-dimensional real
inner-product space with the needed completeness instance) so Mathlib's
`HasGradientAt` API is available.

## Required mathematical deliverables

Prove a coherent API with theorem shapes equivalent to the following. Names
may be adjusted slightly to match repository conventions.

1. The easy direction of 6.11:

   ```lean
   theorem mem_regularNormalCone_of_isLocalMaxOn_hasGradientAt
       (hx : x ∈ C) (hmax : IsLocalMaxOn h C x)
       (hh : HasGradientAt h v x) :
       v ∈ regularNormalCone C x
   ```

   Unpack the first-order remainder supplied by `HasGradientAt` and the
   eventual inequality supplied by `IsLocalMaxOn`; do not assume convexity.

2. The full pointwise equivalence, with feasibility made explicit so the
   right side cannot be vacuous off `C`:

   ```lean
   theorem mem_regularNormalCone_iff_exists_isLocalMaxOn_hasGradientAt
       (hx : x ∈ C) :
       v ∈ regularNormalCone C x ↔
         ∃ h : E → ℝ, IsLocalMaxOn h C x ∧ HasGradientAt h v x
   ```

3. A strengthened witness for the forward implication:

   ```lean
   theorem exists_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone
       (hv : v ∈ regularNormalCone C x) :
       ∃ h : E → ℝ,
         HasGradientAt h v x ∧ IsMaxOn h C x ∧
           ∀ y ∈ C, h y = h x → y = x
   ```

   Equivalent formulations of uniqueness, for example strict inequality for
   every `y ∈ C \ {x}`, are acceptable.

A direct construction avoids the hard smoothing theorem. One effective
choice is the linear functional `y ↦ ⟪v, y - x⟫_ℝ`, minus a correction that
on `C` is the positive part of this functional and is zero off `C`, and minus
`‖y - x‖²`. On `C` this is at most zero and is strictly below zero away from
`x`. The regular-normal estimate says that the correction is `o(‖y-x‖)` at
`x`, while the quadratic term is also little-o; hence the resulting function
has gradient `v` at `x`. You may use another mathematically equivalent
construction, but it must prove the stated global uniqueness and derivative.

## Existing files and APIs to use

- `RockafellarWets/Chapter6/NormalCones.lean`:
  `regularNormalCone`, `mem_regularNormalCone`, and
  `mem_regularNormalCone_iff`.
- Mathlib `Mathlib.Analysis.Calculus.Gradient.Basic`:
  `HasGradientAt`, `hasGradientAt_iff_hasFDerivAt`,
  `hasGradientAt_iff_isLittleO`, and
  `hasGradientAt_iff_isLittleO_nhds_zero`.
- Mathlib extremum APIs: `IsLocalMaxOn`, `IsMaxOn`, `isMaxOn_iff`, and
  `IsMaxOn.localize`.
- Asymptotic tools: `Asymptotics.isLittleO_iff`, closure under addition and
  negation, and `isLittleO_pow_sub_sub` / `isLittleO_norm_pow_id` for the
  quadratic term. Import `Mathlib.Analysis.Asymptotics.Lemmas` explicitly;
  the gradient module alone does not expose those named lemmas at the pinned
  base commit.
- Inner-product tools: `innerSL`, `innerSL_apply_apply`,
  `real_inner_le_norm`, and the standard linear/gradient lemmas.

Prefer `HasGradientAt h v x` in the public API rather than exposing a raw
continuous linear functional.

## Exclusions

- Do not claim that the witness is globally `ContDiff` or smooth. That final
  clause of 6.11 needs the independent smooth-majorant package and will be
  integrated later.
- Do not edit or import a file created by another batch branch.
- Do not work on limiting normal cones, change of coordinates, optimality
  theorem 6.12, or proximal normals.
- Do not add finite-dimensionality unless a proof step genuinely needs it;
  the core differentiable characterization is dimension-free in a complete
  real Hilbert space.
- Do not use `sorry`, `admit`, `axiom`, or an unsound placeholder.

## Verification and completion

From the repository root, run:

```text
lake env lean RockafellarWets/Chapter6/GradientNormals.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/GradientNormals.lean
git diff --check
git status --short
```

Resolve every error and warning that indicates a real defect. The `rg`
command must produce no matches, and `git status --short` must name only the
assigned file. Then stage only the assigned file and create the required
commit:

```text
git add RockafellarWets/Chapter6/GradientNormals.lean
git commit -m "Chapter 6: characterize regular normals by gradients"
```

Report the commit hash, the exact verification command, and a short list of
the public declarations added. State explicitly that the smooth strengthening
was left for the separate majorant task.
