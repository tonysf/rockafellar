# Copy/paste prompt: P14 elementary cone and locality formulas

You are the P14 worker for the first parallel Chapter 6 batch in the
`lean_rockafellar` repository. Build a compact, reusable layer of locality and
elementary tangent/normal cone formulas needed by later Chapter 6 results.
Work only in the assigned new file, prove every declaration, and commit it.

## Starting state and branch

Use an isolated checkout and create `chapter6-p14-elementary-cones` from
exactly:

```text
b2eb4ea92faefd721b93eba48422a6c204d61fc9
```

```text
git switch -c chapter6-p14-elementary-cones b2eb4ea
git rev-parse HEAD
git status --short
```

Do not reset or overwrite an existing branch. Stop if the hash differs or the
starting worktree is dirty.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/ElementaryCones.lean
```

Do not edit any existing source file, `README.md`, `CHAPTER6_COVERAGE.md`, any
other ledger, `RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, lake
configuration, anything under `parallel_tasks/`, or another worker-owned file.
Do not add umbrella imports or import an unmerged P1--P14 module.

Place every new declaration in `namespace RW`.

## Objective and required locality API

Import the existing Chapter 6 tangent- and normal-cone modules and prove that
all four basic cones depend only on the germ of the set at the base point.
Required theorem shapes include:

```lean
derivableCone_inter_nhds (hU : U ∈ nhds x) :
  derivableCone (C ∩ U) x = derivableCone C x

regularNormalCone_inter_nhds (hU : U ∈ nhds x) :
  regularNormalCone (C ∩ U) x = regularNormalCone C x

normalCone_inter_nhds (hU : U ∈ nhds x) :
  normalCone (C ∩ U) x = normalCone C x
```

The base commit already has `tangentCone_inter_nhds` in
`RockafellarWets/Chapter6/ChangeOfCoordinates.lean`; reuse it rather than
duplicating it. Also provide convenient eventual-germ congruence corollaries:
if `C =ᶠ[nhds x] D` (or equivalently they agree after intersection with a
neighborhood of `x`), the corresponding cones at `x` are equal.

For the limiting normal cone, it is not enough to rewrite only the value at
`x`: show that regular-normal mappings agree throughout a sufficiently small
neighborhood, then transport the defining sequences. Preserve the convention
that normal cones are empty away from the set.

## Required elementary formulas

For a real normed inner-product space, prove simp-friendly formulas at the
appropriate member points:

```lean
tangentCone (Set.univ : Set E) x = Set.univ
derivableCone (Set.univ : Set E) x = Set.univ
regularNormalCone (Set.univ : Set E) x = {0}
normalCone (Set.univ : Set E) x = {0}

tangentCone ({x} : Set E) x = {0}
derivableCone ({x} : Set E) x = {0}
regularNormalCone ({x} : Set E) x = Set.univ
normalCone ({x} : Set E) x = Set.univ
```

Also prove the empty/off-set normal formulas if they are not already available
as simp lemmas, without duplicating existing theorems. Add geometric and Clarke
regularity corollaries for `univ` and singletons.

For every interior point `hx : x ∈ interior C`, prove:

```lean
tangentCone C x = Set.univ
derivableCone C x = Set.univ
regularNormalCone C x = {0}
normalCone C x = {0}
IsGeometricallyDerivable C x
IsClarkeRegularAt C x
```

Use locality with an open ball/neighborhood and the `univ` formulas. Do not
add finite-dimensional assumptions unless a particular limiting-normal step
genuinely needs one; keep each theorem at the weakest natural existing
typeclass level.

## Existing APIs and proof route

Inspect:

- `RockafellarWets/Chapter6/TangentCones.lean` for the sequence/path
  definitions and `IsGeometricallyDerivable`;
- `RockafellarWets/Chapter6/NormalCones.lean` for regular/limiting normals,
  empty-off-set lemmas, `IsLocallyClosedAt`, and `IsClarkeRegularAt`;
- `RockafellarWets/Chapter6/ChangeOfCoordinates.lean` for the existing
  `tangentCone_inter_nhds` proof pattern;
- `RockafellarWets/Chapter6/ConvexSets.lean` for quick convex proofs of the
  singleton/univ normal and regularity formulas;
- Chapter 5 filter and eventual-equality lemmas.

Direct definitions are usually simplest for `univ` and singleton tangents.
For normals, use the convex formulas where that avoids repeating epsilon
arguments. For locality, obtain a smaller neighborhood on which membership in
`U` is automatic and use eventual equality of the relevant filters/mappings.

## Exclusions

Do not formalize interval/ray formulas (P4), product formulas (P5), smooth
manifolds (6.8), boxes (6.10), polar or regular tangent cones, projection
formulas, or change-of-coordinate theorems. Do not change existing definitions
or retroactively add simp attributes to existing files.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/ElementaryCones.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/ElementaryCones.lean
git diff --check
git status --short
```

The search must produce no matches and status must list only the assigned
file. No `sorry`, `admit`, axiom, linter suppression, or placeholder result is
allowed. Commit:

```text
git add RockafellarWets/Chapter6/ElementaryCones.lean
git commit -m "Add elementary Chapter 6 cone formulas"
```

Report the commit hash, theorem inventory, typeclass assumptions, and all
verification results.
