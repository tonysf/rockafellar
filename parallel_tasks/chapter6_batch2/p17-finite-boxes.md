# Copy/paste prompt: P17 arbitrary finite boxes

You are the P17 worker for the second parallel Chapter 6 batch in the
`lean_rockafellar` repository. Complete the arbitrary finite-coordinate box
statement of Rockafellar--Wets Example 6.10. Work only in the assigned new Lean
file, prove every declaration, and commit it.

## Starting state and branch

Use an isolated checkout and create `chapter6-p17-finite-boxes` from exactly:

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
RockafellarWets/Chapter6/FiniteBoxes.lean
```

Do not edit any existing source file, `README.md`, `CHAPTER6_COVERAGE.md`, any
other ledger, `RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, lake
configuration, or anything under `parallel_tasks/`. Do not edit files owned by
P16 or P18. Place every declaration in `namespace RW`.

## Exact printed scope

Example 6.10 in `rockafellar_wets.pdf` (printed pp. 204--205) considers

```text
C = C₁ × ⋯ × Cₙ,
```

where every `Cⱼ` is a nonempty closed interval in `ℝ`, possibly unbounded
and possibly a singleton. It says that the box is Clarke regular and
geometrically derivable at every point, and that its tangent and normal cones
are coordinate products. The scalar tangent cases are, respectively,
`(-∞,0]`, `[0,∞)`, `ℝ`, and `{0}` at an only-right endpoint, only-left
endpoint, interior point, and singleton. The normal cases are `[0,∞)`,
`(-∞,0]`, `{0}`, and `ℝ` in the same order.

`IntervalCones.lean` already proves the bounded-interval, singleton, and two
ray formulas. `ElementaryCones.lean` supplies the missing whole-line formulas.
`ProductCones.lean` proves binary `WithLp 2` products. This task packages the
actual arbitrary finite-coordinate Euclidean box, including unbounded and
whole-line coordinates.

## Canonical representation

Use a finite index type and the genuine Euclidean normed space:

```lean
EuclideanSpace ℝ ι
```

Do not use the raw function type `ι → ℝ`, whose standard norm is the sup
norm. Define a transparent box carrier, with a simp membership theorem, along
these lines:

```lean
def finiteBox { ι : Type* } (C : ι → Set ℝ) :
    Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, x i ∈ C i}

@[simp] theorem mem_finiteBox ... : x ∈ finiteBox C ↔ ∀ i, x i ∈ C i
```

Give a concise predicate for the book's coordinate hypothesis, preferably:

```lean
def IsNonemptyClosedInterval (S : Set ℝ) : Prop :=
  S.Nonempty ∧ IsClosed S ∧ S.OrdConnected
```

An equivalent name or conjunction order is acceptable. It must include
`Set.univ`, both closed rays, bounded closed intervals (including degenerate
ones), and exclude the empty set. Do not define "box" to mean only bounded
`Icc` coordinates.

## Required reusable finite-product layer

For `[Fintype ι]`, first prove the structural facts at their weakest useful
hypotheses:

```lean
finiteBox_convex
finiteBox_isClosed

derivableCone_finiteBox
tangentCone_finiteBox
regularNormalCone_finiteBox
normalCone_finiteBox
```

The four cone theorems should have the exact coordinate-product form, e.g.

```lean
tangentCone (finiteBox C) x =
  {w | ∀ i, w i ∈ tangentCone (C i) (x i)}

regularNormalCone (finiteBox C) x =
  {v | ∀ i, v i ∈ regularNormalCone (C i) (x i)}

normalCone (finiteBox C) x =
  {v | ∀ i, v i ∈ normalCone (C i) (x i)}
```

Require `x ∈ finiteBox C` where mathematically needed. It is acceptable for
the tangent/derivable theorem to assume every coordinate is convex or
geometrically derivable; state the weakest clean reusable result you can prove.
Do not assume that binary `WithLp` associates definitionally to a finite
Euclidean product.

Recommended routes:

- prove convexity coordinatewise using `convex_pi` or directly;
- prove closedness as a finite intersection of inverse images under
  `PiLp.continuous_apply 2 _ i`;
- for derivable/tangent cones, construct coordinate paths and synchronize
  their positive radii using finiteness of `ι`; handle the empty index type
  rather than silently assuming `[Nonempty ι]`;
- alternatively prove the product box itself convex and identify its radial
  cone coordinatewise, then use the convex tangent results from
  `ConvexSets.lean`;
- for normals, use `normalCone_eq_of_convex` and
  `regularNormalCone_eq_of_convex`; isolate one coordinate with
  `EuclideanSpace.single`, and combine the reverse inequalities with
  `PiLp.inner_apply` and a finite sum.

The generic finite-product lemmas should be useful beyond intervals, but do
not turn this task into a general dependent-product library.

## Required scalar classification and final 6.10 theorem

State the four scalar cases without losing the phrase "only endpoint". One
good simp-friendly design is:

```lean
def intervalTangentDirections (S : Set ℝ) (x : ℝ) : Set ℝ :=
  if S = {x} then {0}
  else if IsGreatest S x then Set.Iic 0
  else if IsLeast S x then Set.Ici 0
  else Set.univ

def intervalNormalDirections (S : Set ℝ) (x : ℝ) : Set ℝ :=
  if S = {x} then Set.univ
  else if IsGreatest S x then Set.Ici 0
  else if IsLeast S x then Set.Iic 0
  else {0}
```

Equivalent predicates or a small interval data type are acceptable, but all
four cases must be represented and the whole-line case must reduce correctly.
Prove, for `hS : IsNonemptyClosedInterval S` and `hx : x ∈ S`, exact scalar
identities for `tangentCone`, `regularNormalCone`, and `normalCone` against
these classifiers. Reuse the existing `Icc`/`Ici`/`Iic`/`univ` theorems when
convenient; a direct proof from order-connectedness and the convex cone
formulas is also acceptable.

Finally provide clearly documented Example 6.10 theorems, with names such as:

```lean
theorem tangentCone_finiteBox_of_closedIntervals ... :
  tangentCone (finiteBox C) x =
    {w | ∀ i, w i ∈ intervalTangentDirections (C i) (x i)}

theorem regularNormalCone_finiteBox_of_closedIntervals ... : ...

theorem normalCone_finiteBox_of_closedIntervals ... :
  normalCone (finiteBox C) x =
    {v | ∀ i, v i ∈ intervalNormalDirections (C i) (x i)}

theorem isGeometricallyDerivable_finiteBox_of_closedIntervals ... :
  IsGeometricallyDerivable (finiteBox C) x

theorem isClarkeRegularAt_finiteBox_of_closedIntervals ... :
  IsClarkeRegularAt (finiteBox C) x
```

Here the hypotheses must include `[Fintype ι]`,
`∀ i, IsNonemptyClosedInterval (C i)`, and `x ∈ finiteBox C`. A single
bundled theorem in addition to the named projections is welcome, but do not
make users unpack a bespoke structure merely to access the cone equalities.

## Relevant existing APIs

- `RockafellarWets/Chapter6/IntervalCones.lean`: all `Icc`, `Ici`, and `Iic`
  tangent/regular-normal/normal formulas and regularity theorems.
- `RockafellarWets/Chapter6/ElementaryCones.lean`:
  `tangentCone_univ`, `derivableCone_univ`, `regularNormalCone_univ`,
  `normalCone_univ`, and singleton formulas.
- `RockafellarWets/Chapter6/ProductCones.lean`: binary `WithLp 2` product
  formulas; useful as a consistency check, not a required induction encoding.
- `RockafellarWets/Chapter6/ConvexSets.lean`:
  `isGeometricallyDerivable_of_convex`, `regularNormalCone_eq_of_convex`,
  `normalCone_eq_of_convex`, `isClarkeRegularAt_of_convex`.
- Mathlib: `EuclideanSpace`, `EuclideanSpace.single`,
  `EuclideanSpace.single_apply`, `PiLp.inner_apply`,
  `PiLp.continuous_apply`, `convex_pi`, `Set.convex_iff_ordConnected`,
  `isClosed_iInter`, and finite `Finset` minima/sums.

Check exact namespaces and signatures in this pinned Mathlib version. Add the
smallest explicit Mathlib imports needed by the owned file.

## Exclusions

- Do not restrict the final theorem to bounded boxes or to `Fin n`.
- Do not use raw `ι → ℝ` with its sup norm as the ambient Euclidean space.
- Do not omit rays, the whole line, singleton coordinates, or the empty index
  type.
- Do not formalize variational inequalities/complementarity (6.13).
- Do not add finite-product results for regular tangent cones or Proposition
  6.41; those belong to another task.
- Do not duplicate existing scalar interval theorems under competing generic
  names when a short wrapper suffices.
- Do not use `sorry`, `admit`, `axiom`, linter suppression, placeholder
  declarations, or unsafe shortcuts.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/FiniteBoxes.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/FiniteBoxes.lean
git diff --check
git status --short
```

The search must have no matches and status must list only the assigned file.
Do not add an umbrella import merely to test it. Commit only that file:

```text
git add RockafellarWets/Chapter6/FiniteBoxes.lean
git commit -m "Complete finite box cone formulas"
```

Report the commit hash, theorem inventory, exact representation of closed
intervals and endpoint cases, all verification commands and outcomes, and any
exact adaptation of the requested theorem shapes.
