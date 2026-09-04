# P08 — Basic first-order optimality conditions (Theorem 6.12)

You are implementing an isolated Chapter 6 work package in the
`lean_rockafellar` repository. Work only on the branch and file assigned
below. The result must be production Lean code, not a sketch.

## Git contract

- Start from the exact base commit
  `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Create and work on the branch `chapter6-p08-optimality`.
- Before editing, verify that `git rev-parse HEAD` is `b2eb4ea` (the full hash
  may be shown by Git).
- Your required final commit message is:
  `Chapter 6: prove basic first-order optimality conditions`

## Exclusive file ownership

You may create or edit exactly one repository file:

`RockafellarWets/Chapter6/Optimality.lean`

Do not edit any other file. In particular, do not edit `README.md`, any
`CHAPTER*_COVERAGE.md` ledger, `RockafellarWets.lean`,
`RockafellarWets/Chapter6.lean`, any batch index or shared contract under
`parallel_tasks/`, or a Lean file assigned to another prompt. Do not add an
umbrella import. Integration will be done separately.

Place every new declaration in `namespace RW`.

## Objective

Formalize all substantive clauses of Theorem 6.12 for a differentiable
real-valued objective on a subset of a finite-dimensional real inner-product
space. Express differentiability through `HasGradientAt f g x`, local
optimality through `IsLocalMinOn f C x`, and feasibility as the explicit
hypothesis `x ∈ C`.

The theorem says: local optimality implies nonnegativity of the gradient on
the tangent cone; this is equivalent to membership of the negative gradient
in the regular normal cone and implies membership in the limiting normal
cone. For convex `C`, it is equivalent to the global variational inequality
against all points of `C`. If `f` is also convex on `C`, these conditions are
sufficient for global optimality.

## Required mathematical deliverables

Prove a coherent API with theorem shapes equivalent to the following. Names
may be adjusted slightly to match repository conventions.

1. The local-minimum necessary tangent condition:

   ```lean
   theorem IsLocalMinOn.inner_gradient_nonneg_on_tangentCone
       (hx : x ∈ C) (hmin : IsLocalMinOn f C x)
       (hf : HasGradientAt f g x) :
       ∀ w ∈ tangentCone C x, 0 ≤ ⟪g, w⟫_ℝ
   ```

   A direct proof may apply the local inequality along the sequences in the
   definition of `tangentCone` and pass to the derivative limit.

2. Formula 6(10) as an equivalence with the regular-normal condition 6(11):

   ```lean
   theorem inner_nonneg_on_tangentCone_iff_neg_mem_regularNormalCone
       (hx : x ∈ C) :
       (∀ w ∈ tangentCone C x, 0 ≤ ⟪g, w⟫_ℝ) ↔
         -g ∈ regularNormalCone C x
   ```

   The reverse-polar implication uses finite dimensionality through
   `mem_regularNormalCone_of_forall_inner_nonpos`.

3. The normal-cone necessary condition:

   ```lean
   theorem IsLocalMinOn.neg_gradient_mem_normalCone
       (hx : x ∈ C) (hmin : IsLocalMinOn f C x)
       (hf : HasGradientAt f g x) :
       -g ∈ normalCone C x
   ```

   Also expose the stronger regular-normal membership, since that is what the
   proof actually gives.

4. For convex `C`, the equivalences with the global linearized inequality:

   ```lean
   (∀ w ∈ tangentCone C x, 0 ≤ ⟪g, w⟫_ℝ) ↔
     (∀ y ∈ C, 0 ≤ ⟪g, y - x⟫_ℝ)

   -g ∈ normalCone C x ↔
     (∀ y ∈ C, 0 ≤ ⟪g, y - x⟫_ℝ)
   ```

   Use `normalCone_eq_of_convex` and
   `tangentCone_eq_closure_radialCone`/the existing 6.9 API rather than
   reproving convex-set normal geometry.

5. The convex-objective sufficiency clause:

   ```lean
   theorem isMinOn_of_convexOn_of_firstOrder
       (hC : Convex ℝ C) (hx : x ∈ C)
       (hfconv : ConvexOn ℝ C f) (hgrad : HasGradientAt f g x)
       (hfirst : ∀ y ∈ C, 0 ≤ ⟪g, y - x⟫_ℝ) :
       IsMinOn f C x
   ```

   Only differentiability at `x` is needed. Prove the supporting inequality
   for a convex function by restricting to the segment from `x` to `y` if an
   existing theorem does not have exactly the needed boundary hypotheses.

It is useful to finish with one packaged theorem or corollary that presents
the implications/equivalences in the order of printed Theorem 6.12, but keep
the component lemmas public and reusable.

## Existing files and APIs to use

- `RockafellarWets/Chapter6/TangentCones.lean`: `tangentCone` and its
  sequence constructors/destructors.
- `RockafellarWets/Chapter6/NormalCones.lean`:
  `inner_nonpos_of_mem_regularNormalCone`,
  `mem_regularNormalCone_of_forall_inner_nonpos`, and
  `regularNormalCone_subset_normalCone`.
- `RockafellarWets/Chapter6/ConvexSets.lean`:
  `normalCone_eq_of_convex`, `regularNormalCone_eq_of_convex`,
  `tangentCone_eq_closure_radialCone`, and the radial-cone lemmas.
- Mathlib gradient/extremum APIs: `HasGradientAt`,
  `hasGradientAt_iff_isLittleO`, `IsLocalMinOn`, `IsMinOn`, and
  `isMinOn_iff`.
- Mathlib convex restriction-to-segment and one-dimensional derivative
  tools. The repository's `RockafellarWets/Chapter2/Operations.lean` contains
  `convexOn_iff_firstOrder`, but note that its public theorem assumes an open
  set, so do not apply it to an arbitrary `C` without justifying the missing
  hypothesis.

Use `[FiniteDimensional ℝ E]`; add `[CompleteSpace E]` only if instance
inference for `HasGradientAt` requires it in the chosen formulation.

## Exclusions

- Do not formalize variational inequalities/complementarity (6.13),
  constraint multipliers, or Fermat special cases beyond a trivial corollary.
- Do not depend on a gradient-characterization file or any other file created
  by a parallel batch branch; prove 6.12 directly from the base APIs.
- Do not generalize to extended-real objectives or subgradients.
- Do not use `sorry`, `admit`, `axiom`, or an unsound placeholder.

## Verification and completion

From the repository root, run:

```text
lake env lean RockafellarWets/Chapter6/Optimality.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/Optimality.lean
git diff --check
git status --short
```

Resolve every error and warning that indicates a real defect. The `rg`
command must produce no matches, and `git status --short` must name only the
assigned file. Then stage only the assigned file and create the required
commit:

```text
git add RockafellarWets/Chapter6/Optimality.lean
git commit -m "Chapter 6: prove basic first-order optimality conditions"
```

Report the commit hash, the exact verification command, and a short list of
the public declarations added.
