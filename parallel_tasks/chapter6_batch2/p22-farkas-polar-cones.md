# Copy/paste prompt: P22 Farkas lemma and polyhedral cone polars

You are the P22 worker for Chapter 6 batch 2 in the `lean_rockafellar`
repository. Formalize Rockafellar--Wets Lemma 6.45 exactly, both as a polar-set
identity and as the usual finite nonnegative-multiplier form of Farkas' lemma.
Reuse the integrated Chapter 3 polyhedral layer and Chapter 6 polarity API,
prove every declaration, and commit only your assigned file.

## Starting state and branch

Use an isolated checkout and create `chapter6-p22-farkas-polar-cones` from
exactly:

```text
9fa1c19eab36f7fc79845f679d35b87344366e0b
```

```text
git switch -c chapter6-p22-farkas-polar-cones 9fa1c19
git rev-parse HEAD
git status --short
```

Do not reset or overwrite an existing branch. Stop before editing if the full
hash differs or the starting worktree is dirty.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/FarkasPolarCones.lean
```

Do not edit existing source, either umbrella import, `README.md`,
`CHAPTER6_COVERAGE.md`, any ledger or lake file, anything under
`parallel_tasks/`, or another worker-owned file. Do not import an unmerged
Batch 2 module. Put all declarations in `namespace RW`.

## Book scope and canonical statement

Lemma 6.45 is on book page 230 (PDF page 238). Work in a finite-dimensional
real inner-product space and retain Chapter 6's nonpositive sign convention
for `polarCone`.

For a finite family `a : Fin m → E`, let

```lean
K := {x : E | ∀ i, ⟪a i, x⟫_ℝ ≤ 0}
```

and prove the exact equality

```lean
polarCone K = conicHull (Set.range a)
```

An equivalent right side using
`(↑(Finset.univ.image a) : Set E)` is acceptable, but expose a convenient
`Set.range` theorem as well. The theorem must handle `m = 0`, zero generators,
and duplicate generators without extra hypotheses; the book explicitly says
discarding zero vectors is only a proof convenience.

Also prove a membership form with ordinary finite multipliers:

```lean
v ∈ polarCone K ↔
  ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧
    (∑ i, y i • a i) = v
```

Orientation of the final equality may be reversed if that simplifies
rewriting. This is the copy-ready Farkas alternative: a vector pairs
nonpositively with every solution of the inequalities exactly when it is a
nonnegative linear combination of their normals. Do not stop at an abstract
`v ∈ conicHull ...` corollary.

Provide structural corollaries showing that the polar of this
H-polyhedral cone is finitely generated/closed and, conversely, that the polar
of a finitely generated cone has the displayed homogeneous finite-inequality
description. State these through existing `IsHPolyhedralCone` and
`IsFinitelyGeneratedCone` APIs where clean; do not introduce competing
polyhedral predicates.

## Existing APIs and shortest proof route

Inspect and reuse:

- `RockafellarWets/Chapter6/Polarity.lean`:
  `mem_polarCone`, `polarCone_conicHull`, `polarCone_bipolar`, and the
  closed-convex-cone bipolar corollaries;
- `RockafellarWets/Chapter3/GeneratedCones.lean`:
  `conicHull`, `mem_conicHull_iff_exists_finsupp`,
  `isClosed_conicHull_finset`, and `IsFinitelyGeneratedCone`;
- `RockafellarWets/Chapter3/MinkowskiWeyl.lean`:
  `homogeneousLinearInequalitySet`, `IsHPolyhedralCone`, and the equivalence
  between H-polyhedral and finitely generated cones;
- Mathlib's `innerSL ℝ`, `Finset.sum_inner`, and finite-sum lemmas.

Follow the printed proof. Let `J = conicHull (Set.range a)`. First prove
elementarily that

```lean
polarCone J = K
```

by checking the generators and extending across nonnegative finite
combinations. The finite conic hull is closed in finite dimensions, so
bipolarity gives `polarCone K = J`. This avoids reproving a general separation
theorem. Normalize inner-product order only with `real_inner_comm`; do not
change the sign convention or substitute Mathlib's nonnegative inner dual.

For the explicit multiplier theorem, prove or reuse the finite-index
description of `conicHull (Set.range a)`. If routing through finitely supported
coefficients, collect coefficients belonging to equal generators so duplicate
entries are handled correctly; do not assume `a` injective.

To bridge the vector inequalities to
`homogeneousLinearInequalitySet`, use `innerSL ℝ (a i)` and prove the tiny
extensional equality. Use the already integrated Minkowski--Weyl theorem for
structural corollaries rather than redoing its long induction.

## Exclusions and quality bar

Do not formalize 6.46--6.48, tangent/normal formulas for polyhedral sets,
general linear-programming duality, affine inequalities with nonzero right
sides, or an alternative polar definition. No `sorry`, `admit`, new `axiom`,
linter suppression, or placeholder theorem is allowed.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/FarkasPolarCones.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/FarkasPolarCones.lean
git diff --check
git status --short
```

The search must be empty and status must list only the assigned file. Commit:

```text
git add RockafellarWets/Chapter6/FarkasPolarCones.lean
git commit -m "Formalize Farkas lemma for polyhedral cones"
```

Report the commit hash, exact polar equality, explicit multiplier theorem,
structural corollaries, and every verification result.
