# Copy/paste prompt: P20 recession vectors and cones

You are the P20 worker for Chapter 6 batch 2 in the `lean_rockafellar`
repository. Formalize Definition 6.33 and every clause of Exercise 6.34,
including the finite-family uniformity statement. Prove a reusable API and
commit only the assigned module.

## Starting state and branch

Use an isolated checkout and create `chapter6-p20-recession-cones` from
exactly:

```text
9fa1c19eab36f7fc79845f679d35b87344366e0b
```

```text
git switch -c chapter6-p20-recession-cones 9fa1c19
git rev-parse HEAD
git status --short
```

Do not reset an existing branch. Stop before editing if the full hash differs
or the initial worktree is dirty.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/RecessionCones.lean
```

Do not edit existing source, either umbrella import, `README.md`,
`CHAPTER6_COVERAGE.md`, another ledger, lake configuration, anything under
`parallel_tasks/`, or another worker's file. Do not import an unmerged Batch 2
module. Place every declaration in `namespace RW`.

## Definition 6.33

Definition 6.33 and Exercise 6.34 are on book page 222 (PDF page 230). Define
the local recession cone with the printed uniform quantification over nearby
base points and short nonnegative steps. Preserve that the notion is only
defined at a feasible point, preferably by making it empty off the set:

```lean
def localRecessionCone (C : Set E) (xbar : E) : Set E :=
  {w | xbar ∈ C ∧
    ∃ V ∈ nhds xbar, ∃ ε > 0,
      ∀ x ∈ C ∩ V, ∀ τ ∈ Set.Icc (0 : ℝ) ε,
        x + τ • w ∈ C}
```

A definition using an open neighborhood with a proved equivalent filter form
is acceptable. Supply simp/membership lemmas and the off-set formula.

Define global recession vectors exactly by invariance of all rays:

```lean
def globalRecessionCone (C : Set E) : Set E :=
  {w | ∀ x ∈ C, ∀ τ : ℝ, 0 ≤ τ → x + τ • w ∈ C}
```

Supply the membership theorem and the equivalent translation inclusion
`C + τ • {w} ⊆ C` if useful. Do not identify this definition with
`horizonCone` without the printed convexity/closedness hypotheses.

## Exercise 6.34(a): local structure

At `xbar ∈ C`, prove:

- `0 ∈ localRecessionCone C xbar`;
- it is an `IsCone` and a convex set;
- `localRecessionCone C xbar ⊆ regularTangentCone C xbar` (the book's
  `T tilde`, not merely `tangentCone`);
- hence the corresponding inclusions into `derivableCone` and `tangentCone`.

Prove the stronger finite-family clause. For a finite family
`w : ι → E`, with every `w i` locally recessive, find one common neighborhood
`V` and one `ε > 0` such that every nearby `x`, every `τ ∈ [0, ε]`, and every
`z ∈ convexHull ℝ (Set.range w)` satisfy `x + τ • z ∈ C`. An equivalent
`Fin n` formulation is fine. The book writes `con{w₁,...,wᵣ}`, meaning the
convex hull; do **not** use the unbounded `conicHull`, for which a uniform
positive step size would be false.

## Exercise 6.34(b)--(c): global structure

Prove:

```lean
globalRecessionCone C = ⋂ x ∈ C, localRecessionCone C x
```

when `C` is closed. Prove directly that the global recession set is a convex
cone for arbitrary `C`, and that it is closed when `C` is closed. The empty
intersection convention must agree with the vacuous global definition.

For convex `C`, formalize the horizon comparison:

```lean
globalRecessionCone C ⊆ horizonCone C
```

under the necessary `C.Nonempty` hypothesis, and for nonempty closed convex
`C` prove equality. The nonemptiness is mathematically necessary with this
repository's convention `horizonCone ∅ = {0}` while the vacuous global
recession cone of `∅` is `univ`; mention that point in the module docstring
instead of asserting a false empty-set generalization.

## Existing APIs and proof guidance

Inspect and reuse:

- `RockafellarWets/Chapter6/RegularTangents.lean`, especially
  `mem_regularTangentCone_iff_forall_sequences` and the inclusions from regular
  tangents to derivable/ordinary tangents;
- `RockafellarWets/Chapter3/HorizonCones.lean`, especially
  `mem_horizonCone_of_forall_smul_add_mem` and
  `smul_add_mem_of_mem_horizonCone`;
- `RockafellarWets/Chapter3/FiniteConeSetOperations.lean` for finite
  nonnegative combinations and finite-product proof patterns;
- Mathlib's finite intersection of neighborhoods, `convexHull_min`, and
  continuity of `τ ↦ x + τ • w`.

For finite uniformity, intersect the finitely many witnessing neighborhoods,
take a positive minimum of the step bounds, and apply the directions
successively while shrinking the neighborhood enough to keep intermediate
points inside every witness neighborhood. Extend from the generators to their
convex hull using finite convex combinations. Do not simply invoke convexity
of `C`; clause (a) is for an arbitrary set.

For the difficult reverse inclusion in (b), use closedness and the printed
first-exit/last-contact argument on the ray. Alternatively, express global
recession as an intersection of closed preimages and separately prove the
local-to-global equality. For (c), use the existing Chapter 3 ray
characterizations rather than unfolding asymptotic neighborhoods.

## Exclusions and quality bar

Do not formalize 6.35--6.40, epigraphical recession, convexified cones, or new
versions of `horizonCone` and `regularTangentCone`. Use `x + τ • w`
consistently (rewriting commuted forms only at API boundaries). Avoid
finite-dimensional assumptions: 6.33--6.34 only require normed real spaces.

No `sorry`, `admit`, new `axiom`, linter suppression, or placeholder result is
allowed.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/RecessionCones.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/RecessionCones.lean
git diff --check
git status --short
```

The search must be empty and status must list only the assigned file. Commit:

```text
git add RockafellarWets/Chapter6/RecessionCones.lean
git commit -m "Formalize local and global recession cones"
```

Report the commit hash, theorem inventory, exact empty-set/nonemptiness
conventions, and all verification results.
