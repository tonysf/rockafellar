# Copy/paste prompt: P10 supporting halfspaces

You are the P10 worker for the first parallel Chapter 6 batch in the
`lean_rockafellar` repository. Formalize Rockafellar--Wets Theorem 6.20,
the supporting-halfspace envelope of a nonempty closed convex set. Work only
in the file assigned below, prove every declaration, and commit the result.

## Starting state and branch

Work in an isolated checkout. Create the branch
`chapter6-p10-supporting-halfspaces` based **exactly** on:

```text
b2eb4ea92faefd721b93eba48422a6c204d61fc9
```

For example:

```text
git switch -c chapter6-p10-supporting-halfspaces b2eb4ea
git rev-parse HEAD
git status --short
```

The first command must not reset or overwrite an existing branch. The printed
commit must be the full hash above, and the worktree must be clean. If either
check fails, stop and report it instead of building on a different base.

## Exclusive ownership

Create and edit exactly this one source file:

```text
RockafellarWets/Chapter6/SupportingHalfspaces.lean
```

Do not edit any existing file. In particular, do not edit `README.md`,
`CHAPTER6_COVERAGE.md`, any other ledger, `RockafellarWets/Chapter6.lean`,
`RockafellarWets.lean`, lake configuration, anything under `parallel_tasks/`,
or a file owned by another P1--P14 worker. Do not add an umbrella import.
Import only modules present at the base commit; do not import another worker's
not-yet-integrated module.

Place every new declaration in `namespace RW`.

## Objective and source

Formalize Theorem 6.20 on book pages 214--215 (PDF pages 222--223): a nonempty
closed convex subset of a finite-dimensional real inner-product space is the
intersection of its supporting closed halfspaces; conversely an intersection
of closed halfspaces is closed and convex; such a set is Clarke regular at all
of its points. Include the homogeneous supporting-halfspace specialization for
closed convex cones stated immediately after the theorem.

Use a small canonical API. Reasonable declaration shapes are shown below;
minor binder or naming changes are allowed only when Lean requires them, not to
weaken the mathematics.

```lean
def supportingHalfspace (x v : E) : Set E :=
  {y | ⟪v, y - x⟫_ℝ ≤ 0}

def IsSupportingHalfspace (C : Set E) (x v : E) : Prop :=
  x ∈ C ∧ v ≠ 0 ∧ C ⊆ supportingHalfspace x v

def supportingHalfspaces (C : Set E) : Set (Set E) :=
  {H | ∃ x v, IsSupportingHalfspace C x v ∧ H = supportingHalfspace x v}
```

Required deliverables:

- membership simp lemmas and proofs that `supportingHalfspace x v` is closed
  and convex;
- every supporting halfspace contains the supported set and has `x` on its
  boundary hyperplane;
- the exact envelope theorem, for nonempty closed convex `C`, in a convenient
  form such as
  `C = ⋂₀ supportingHalfspaces C` (or an extensionally equivalent indexed
  intersection);
- a point-separation lemma: for every `z ∉ C`, produce `x ∈ C` and
  `v ≠ 0` supporting `C` at `x` with `z ∉ supportingHalfspace x v`;
- the converse theorem that an arbitrary intersection of closed halfspaces is
  closed and convex, including the empty family whose intersection is `univ`;
- the homogeneous cone clause: if `C` is a cone, a halfspace containing `C`
  can be replaced by one with threshold zero, and the resulting intersection
  is a closed convex cone;
- the regularity clause, stated through the existing
  `IsClarkeRegularAt`: every point of a closed convex `C` is Clarke regular.

Do not merely restate Mathlib's `iInter_halfSpaces_eq`: the principal theorem
must really use halfspaces that support `C` at a point. Do not define a second
notion of normal cone or projection.

## Existing APIs and proof route

Inspect and reuse:

- `RockafellarWets/Chapter2/Separation.lean`:
  `IsSupportingHyperplane`, `separation_of_convex_open`, and
  `strict_separation_of_convex_compact`;
- `RockafellarWets/Chapter5/ProjectionMappings.lean`:
  `projMapping`, `mem_projMapping`, and `projMapping_nonempty`;
- `RockafellarWets/Chapter6/ConvexSets.lean`:
  `normalCone_eq_of_convex`, `regularNormalCone_eq_of_convex`, and
  `isClarkeRegularAt_of_convex`;
- `RockafellarWets/Chapter3/Cones.lean` and Mathlib's closed/convex
  intersection lemmas.

The intended finite-dimensional proof follows the book. For `z ∉ C`, choose
`x ∈ projMapping C z`, put `v := z - x`, prove the projection variational
inequality `⟪v, y - x⟫_ℝ ≤ 0` for `y ∈ C`, and observe
`⟪v, z - x⟫_ℝ = ‖v‖² > 0`. Search Mathlib's inner-product projection
minimality lemmas before reproving this calculation. The converse is by
closedness and convexity of arbitrary intersections. The regularity clause is
a direct application of `isClarkeRegularAt_of_convex` and
`IsClosed.isLocallyClosedAt`.

P09 owns the generic public projection-to-regular-normal theorem. Inline the
projection variational calculation here, or keep any extracted helper private
or unmistakably supporting-halfspace-specific; do not publish a competing
generic theorem.

## Exclusions

Do not formalize Exercise 6.19, polarity (6.21--6.24), proximal-normal results,
polyhedral/finitely-generated refinements, boxes, or change-of-coordinate
results. Do not modify the existing Chapter 2 supporting-hyperplane API.

## Verification and commit

The task is complete only if all of these pass:

```text
lake env lean RockafellarWets/Chapter6/SupportingHalfspaces.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/SupportingHalfspaces.lean
git diff --check
git status --short
```

The `rg` command must produce no matches. Do not use `sorry`, `admit`, new
axioms, disabled linters, or placeholder declarations. Confirm that
`git status --short` names only the assigned file, then commit it:

```text
git add RockafellarWets/Chapter6/SupportingHalfspaces.lean
git commit -m "Formalize Chapter 6 supporting halfspace representation"
```

Report the commit hash, theorem inventory, verification results, and any
statement whose Lean spelling differs from the shapes above.
