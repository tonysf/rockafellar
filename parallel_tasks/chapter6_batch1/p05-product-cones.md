# P05 — Binary product formulas for Chapter 6 cones

You are implementing an isolated Chapter 6 work package in the
`lean_rockafellar` repository. Work only on the branch and file assigned
below. The result must be production Lean code, not a sketch.

## Git contract

- Start from the exact base commit
  `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Create and work on the branch `chapter6-p05-product-cones`.
- Before editing, verify that `git rev-parse HEAD` is `b2eb4ea` (the full hash
  may be shown by Git).
- Your required final commit message is:
  `Chapter 6: add binary product cone formulas`

## Exclusive file ownership

You may create or edit exactly one repository file:

`RockafellarWets/Chapter6/ProductCones.lean`

Do not edit any other file. In particular, do not edit `README.md`, any
`CHAPTER*_COVERAGE.md` ledger, `RockafellarWets.lean`,
`RockafellarWets/Chapter6.lean`, any batch index or shared contract under
`parallel_tasks/`, or a Lean file assigned to another prompt. Do not add an
umbrella import. Integration will be done separately.

Place every new declaration in `namespace RW`.

## Objective

Build the binary-product infrastructure behind Proposition 6.41, using the
Euclidean product norm. A plain Lean product `E × F` has the sup norm and is
not an inner product space compatible with that norm. Therefore all formulas
that mention normal cones must live on `WithLp 2 (E × F)`; do not install a
local or nonstandard inner-product instance on `E × F`.

This file is the reusable binary layer that will later be folded to obtain
finite boxes and the finite-product statements surrounding 6.41. It does not
itself claim to formalize arbitrary finite products or every clause of 6.41.

Define a small public helper such as

```lean
def l2ProdSet (C : Set E) (D : Set F) : Set (WithLp 2 (E × F)) :=
  {z | z.fst ∈ C ∧ z.snd ∈ D}
```

(An extensionally equivalent definition using `WithLp.toLp 2 '' (C ×ˢ D)`
is acceptable.) Use `WithLp.toLp 2 (x, y)` for the base point.

## Required mathematical deliverables

Prove a coherent API with theorem shapes equivalent to the following. Names
may be adjusted slightly to match repository conventions, but the content
must be present.

1. Coordinate membership simp lemmas for `l2ProdSet` and its `toLp` points.

2. The always-valid tangent inclusion:

   ```lean
   tangentCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) ⊆
     l2ProdSet (tangentCone C x) (tangentCone D y)
   ```

3. The derivable-cone product formula (assuming `x ∈ C` and `y ∈ D`):

   ```lean
   derivableCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
     l2ProdSet (derivableCone C x) (derivableCone D y)
   ```

   In the reverse direction, synchronize the two paths on the minimum of
   their positive radii.

4. Exact regular-normal and limiting-normal formulas:

   ```lean
   regularNormalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
     l2ProdSet (regularNormalCone C x) (regularNormalCone D y)

   normalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
     l2ProdSet (normalCone C x) (normalCone D y)
   ```

   It is fine to state the core results with `x ∈ C` and `y ∈ D`; stronger
   versions that correctly handle the empty-off-the-set convention are also
   welcome. For the reverse limiting-normal inclusion, zip the two component
   witnessing sequences rather than appealing to an unavailable generic
   product-limit theorem.

5. A useful equality criterion for the ordinary tangent cone: if both
   factors are geometrically derivable at their base points, then

   ```lean
   tangentCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
     l2ProdSet (tangentCone C x) (tangentCone D y)
   ```

6. The binary closed-set Clarke-regularity wrapper corresponding to the
   available part of 6.41:

   ```lean
   IsClarkeRegularAt (l2ProdSet C D) (WithLp.toLp 2 (x, y)) ↔
     IsClarkeRegularAt C x ∧ IsClarkeRegularAt D y
   ```

   Here assume `IsClosed C`, `IsClosed D`, `x ∈ C`, and `y ∈ D`. Use
   `IsClosed.isLocallyClosedAt` and the two normal-cone product formulas.

Keep hypotheses minimal where doing so is straightforward. None of the cone
formulas above should require finite dimensionality.

## Existing files and APIs to use

- `RockafellarWets/Chapter6/TangentCones.lean`:
  `tangentCone`, `derivableCone`, `mem_tangentCone_of_forall`,
  `derivableCone_subset_tangentCone`, `IsGeometricallyDerivable`.
- `RockafellarWets/Chapter6/NormalCones.lean`:
  `regularNormalCone`, `normalCone`, `mem_regularNormalCone`,
  `mem_normalCone_of_forall`, `regularNormalCone_subset_normalCone`,
  `IsClarkeRegularAt`, `IsClosed.isLocallyClosedAt`.
- Mathlib's `Mathlib.Analysis.InnerProductSpace.ProdL2`:
  the inner-product instance on `WithLp 2 (E × F)`,
  `WithLp.prod_inner_apply`, `WithLp.toLp`, `WithLp.ofLp`, and the
  coordinate simp lemmas (`toLp_fst`, `toLp_snd`, add/sub/smul lemmas).
- Filter/product convergence lemmas such as `Tendsto.prodMk_nhds` and
  continuity of the two coordinate maps.

Import the narrowest existing project module(s) and the explicit Mathlib
`ProdL2` module if needed.

## Exclusions

- Do not attempt finite products indexed by a `Fintype`; binary products are
  the deliverable and can be folded later.
- Do not formalize the strict-inclusion example following 6.41.
- Do not introduce regular tangent cones from 6.25, which are not yet in the
  repository.
- Do not work on intersections, images, set addition, or the outstanding
  change-of-coordinates normal formulas.
- Do not use `sorry`, `admit`, `axiom`, or an unsound placeholder.

## Verification and completion

From the repository root, run:

```text
lake env lean RockafellarWets/Chapter6/ProductCones.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/ProductCones.lean
git diff --check
git status --short
```

Resolve every error and warning that indicates a real defect. The `rg`
command must produce no matches, and `git status --short` must name only the
assigned file. Then stage only the assigned file and create the required
commit:

```text
git add RockafellarWets/Chapter6/ProductCones.lean
git commit -m "Chapter 6: add binary product cone formulas"
```

Report the commit hash, the exact verification command, and a short list of
the public declarations added.
