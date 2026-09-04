# P07 — A reusable `C¹` strict-majorant lemma

You are implementing an isolated Chapter 6 infrastructure work package in
the `lean_rockafellar` repository. Work only on the branch and file assigned
below. The result must be production Lean code, not a sketch.

## Git contract

- Start from the exact base commit
  `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Create and work on the branch `chapter6-p07-smooth-majorant`.
- Before editing, verify that `git rev-parse HEAD` is `b2eb4ea` (the full hash
  may be shown by Git).
- Your required final commit message is:
  `Chapter 6: add smooth strict-majorant infrastructure`

## Exclusive file ownership

You may create or edit exactly one repository file:

`RockafellarWets/Chapter6/SmoothMajorant.lean`

Do not edit any other file. In particular, do not edit `README.md`, any
`CHAPTER*_COVERAGE.md` ledger, `RockafellarWets.lean`,
`RockafellarWets/Chapter6.lean`, any batch index or shared contract under
`parallel_tasks/`, or a Lean file assigned to another prompt. Do not add an
umbrella import. Integration will be done separately.

Place every new declaration in `namespace RW`.

## Objective

Extract and formalize the scalar smoothing argument in the proof of Theorem
6.11. Starting with a nondecreasing error modulus `θ₀` on `[0,∞)` satisfying
`θ₀(0)=0` and `θ₀(r)=o(r)` as `r ↓ 0`, construct an everywhere `C¹` function
that strictly majorizes `θ₀` at every positive radius while retaining zero
value and zero derivative at the origin. The lemma must be reusable and must
not mention normal cones.

The book's construction is the intended route. For `r > 0`, set

```text
θ₁(r) = (1/r) ∫ s in r..2*r, θ₀(s)
θ₂(r) = (1/r) ∫ s in r..2*r, θ₁(s)
θ₊(r) = θ₂(r) + r^2,
```

give all three value `0` at `r=0`, and use an even extension of `θ₊` if a
function on all of `ℝ` is convenient. The first averaging makes the monotone
input continuous; the second makes it continuously differentiable on the
positive half-line; the added square makes domination strict.

## Required mathematical deliverables

Provide supporting definitions/lemmas and a final public theorem with a shape
equivalent to:

```lean
theorem exists_contDiff_one_strict_majorant
    {θ₀ : ℝ → ℝ}
    (hmono : MonotoneOn θ₀ (Set.Ici 0))
    (hzero : θ₀ 0 = 0)
    (hsmall : Tendsto (fun r : ℝ => θ₀ r / r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ θ : ℝ → ℝ,
      ContDiff ℝ 1 θ ∧
      θ 0 = 0 ∧
      HasDerivAt θ 0 0 ∧
      (∀ r > 0, θ₀ r < θ r) ∧
      Tendsto (fun r : ℝ => θ r / r)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (fun r : ℝ => deriv θ r)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

If proving global `ContDiff ℝ 1 θ` directly for the even extension creates a
purely library-technical obstruction, the acceptable fallback is a theorem
whose output states all of the following explicitly: continuity on `Ici 0`,
`ContDiffOn ℝ 1 θ (Ioi 0)`, a right derivative of `0` at the origin, derivative
tending to `0` from the right, strict majorization on `Ioi 0`, and
`θ(r)/r → 0` from the right. Do not silently weaken the conclusion: document
the fallback in the module docstring and prove every property needed to make
the later even extension `C¹`.

Required intermediate facts (public or private) include:

- interval integrability of the monotone input on every compact positive
  interval;
- `θ₀(r) ≤ θ₁(r)` and `θ₁(r) ≤ θ₂(r)` for `r > 0`;
- continuity of the first average on `(0,∞)` and its convergence to `0` at
  the origin;
- differentiability/continuous differentiability of the second average on
  `(0,∞)` with derivative tending to `0` at the origin;
- preservation of the little-o ratio through both averages;
- strict domination after adding `r²`.

## Existing files and APIs to use

- Mathlib interval-integral modules, especially
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`.
- `MonotoneOn.intervalIntegrable`,
  `intervalIntegral.integral_mono_on`, the integral of a constant, and the
  fundamental-theorem lemmas such as
  `intervalIntegral.integral_hasDerivAt_right`.
- `ContDiff`, `ContDiffOn`, `HasDerivAt`, `ContinuousOn`, and the usual
  product/quotient derivative rules away from `r = 0`.
- Filter/asymptotic APIs for `nhdsWithin 0 (Ioi 0)`, including
  `Asymptotics.isLittleO_iff` if it makes the ratio estimates cleaner.

Keep the public assumptions close to the mathematical statement. Do not
replace monotonicity by global continuity: smoothing a possibly discontinuous
monotone modulus is the point of the double average.

## Exclusions

- Do not mention or prove anything about `regularNormalCone`, gradients, or
  optimization; this file is scalar analysis infrastructure only.
- Do not edit or import a file created by another batch branch.
- Do not use convolution, mollifiers, or an existence axiom unless you prove
  all required properties from an existing Mathlib theorem with matching
  hypotheses.
- Do not formalize higher smoothness than `C¹`; in this part of the book,
  “smooth” means everywhere continuously differentiable.
- Do not use `sorry`, `admit`, `axiom`, or an unsound placeholder.

## Verification and completion

From the repository root, run:

```text
lake env lean RockafellarWets/Chapter6/SmoothMajorant.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/SmoothMajorant.lean
git diff --check
git status --short
```

Resolve every error and warning that indicates a real defect. The `rg`
command must produce no matches, and `git status --short` must name only the
assigned file. Then stage only the assigned file and create the required
commit:

```text
git add RockafellarWets/Chapter6/SmoothMajorant.lean
git commit -m "Chapter 6: add smooth strict-majorant infrastructure"
```

Report the commit hash, the exact verification command, the final theorem's
actual type, and whether the global-`ContDiff` conclusion or the fully stated
one-sided fallback was achieved.
