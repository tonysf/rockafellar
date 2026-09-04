# Copy/paste prompt: P21 finite product cone formulas

You are the P21 worker for Chapter 6 batch 2 in the `lean_rockafellar`
repository. Complete Proposition 6.41 by adding the arbitrary finite Euclidean
product formulas, the canonical regular-tangent product equality, and the
ordinary-tangent equality under Clarke regularity. Build on the integrated
binary API without changing it, prove every declaration, and commit only your
assigned file.

## Starting state and branch

Use an isolated checkout and create `chapter6-p21-finite-product-cones` from
exactly:

```text
9fa1c19eab36f7fc79845f679d35b87344366e0b
```

```text
git switch -c chapter6-p21-finite-product-cones 9fa1c19
git rev-parse HEAD
git status --short
```

Do not reset an existing branch. Stop before editing if the full hash differs
or the starting worktree is dirty.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/FiniteProductCones.lean
```

Do not edit existing source, umbrella imports, `README.md`,
`CHAPTER6_COVERAGE.md`, any ledger or lake file, anything under
`parallel_tasks/`, or another worker-owned file. Do not import an unmerged
Batch 2 module. Put every declaration in `namespace RW`.

## Ambient finite product and scope

Proposition 6.41 is on book pages 227--228 (PDF pages 235--236). Its product
is Euclidean, so use the finite `L²` product, not the sup-normed raw Pi type.
For a finite index type and possibly heterogeneous factors, define a compact
wrapper such as

```lean
def l2PiSet {ι : Type*} {E : ι → Type*}
    (C : ∀ i, Set (E i)) : Set (PiLp 2 E) :=
  {x | ∀ i, x i ∈ C i}
```

with a simp membership theorem and a closedness theorem. Use
`[Fintype ι]`, `[∀ i, NormedAddCommGroup (E i)]`, and the appropriate
coordinatewise normed-space or inner-product-space instances. The empty finite
product should work under standard conventions; do not introduce a
`Nonempty ι` assumption unless Lean genuinely requires it.

## Required finite-family formulas

For `x ∈ l2PiSet C`, prove the full coordinatewise results corresponding to
the display in 6.41:

```lean
tangentCone (l2PiSet C) x ⊆
  l2PiSet (fun i ↦ tangentCone (C i) (x i))

regularNormalCone (l2PiSet C) x =
  l2PiSet (fun i ↦ regularNormalCone (C i) (x i))

normalCone (l2PiSet C) x =
  l2PiSet (fun i ↦ normalCone (C i) (x i))

regularTangentCone (l2PiSet C) x =
  l2PiSet (fun i ↦ regularTangentCone (C i) (x i))
```

The regular-tangent equality is required and must be proved from the canonical
Definition 6.25 object, not from a newly invented regular tangent notion.
Also provide the finite derivable-cone product equality if it is a useful
intermediate lemma; it is already part of the binary API's reusable behavior.

Under `∀ i, IsClosed (C i)` and coordinate membership, prove

```lean
IsClarkeRegularAt (l2PiSet C) x ↔
  ∀ i, IsClarkeRegularAt (C i) (x i)
```

Finally prove the printed regular-case strengthening:

```lean
(∀ i, IsClarkeRegularAt (C i) (x i)) →
  tangentCone (l2PiSet C) x =
    l2PiSet (fun i ↦ tangentCone (C i) (x i))
```

Do not silently strengthen the hypothesis to geometric derivability. If a
general bridge from Clarke regularity to equality of ordinary and regular
tangents is needed, prove the weakest reusable lemma required here (public or
private) from the integrated polarity/regular-tangent APIs, and document that
it is infrastructure for the last clause of 6.41 rather than a claimed full
formalization of 6.28--6.30.

If it follows without materially expanding the task, also record the
unnumbered equality of closed convex-conic hulls after the example, in a form
equivalent to

```text
cl (con (T_C(x))) = product_i cl (con (T_{C_i}(x_i))).
```

Use the repository's `closure (conicHull ...)` spelling and state only the
hypotheses actually needed.

## Existing APIs and proof route

Inspect and reuse:

- `RockafellarWets/Chapter6/ProductCones.lean` for the binary `WithLp 2`
  formulas and proof patterns;
- `RockafellarWets/Chapter6/RegularTangents.lean`, especially the exact
  sequential characterization of `regularTangentCone`;
- `RockafellarWets/Chapter6/Polarity.lean` for `polarCone_bipolar` and
  polarity infrastructure;
- `RockafellarWets/Chapter6/NormalCones.lean` for limiting-normal sequence
  constructors and Clarke regularity;
- `Mathlib.Analysis.InnerProductSpace.PiL2` for `PiLp.inner_apply`,
  `PiLp.continuous_apply`, coordinatewise convergence, and `L²` norm facts.

Direct coordinate proofs are preferable to a dependent induction over binary
products. Forward tangent/normal implications come from continuous coordinate
evaluation. Reverse regular-normal estimates use the finite sum formula for
the inner product and distribute `ε` over the finite coordinates. Reverse
limiting-normal and regular-tangent implications zip finitely many witness
sequences and use finite-product convergence; do not choose a different
subsequence for every coordinate. Handle zero coordinates and the empty index
type explicitly rather than dividing by `Fintype.card ι` without a case split.

For the regular-case tangent equality, do not use the existing binary theorem
`tangentCone_l2ProdSet`, whose assumptions are geometric derivability rather
than the Clarke regularity printed in 6.41.

## Exclusions and quality bar

Do not formalize intersections, images, sums, boxes, or results 6.42--6.44.
Do not replace or duplicate `l2ProdSet`, change the norm on plain products, or
edit `ProductCones.lean`. No `sorry`, `admit`, new `axiom`, linter suppression,
or placeholder declarations are allowed.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/FiniteProductCones.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/FiniteProductCones.lean
git diff --check
git status --short
```

The search must be empty and status must name only the assigned file. Commit:

```text
git add RockafellarWets/Chapter6/FiniteProductCones.lean
git commit -m "Complete finite product cone formulas"
```

Report the commit hash, theorem inventory with assumptions, the exact finite
`L²` representation, the proof used for the Clarke-regular tangent equality,
and every verification result.
