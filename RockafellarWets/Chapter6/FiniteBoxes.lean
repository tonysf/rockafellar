/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Cones to a finite box (Example 6.10)

Example 6.10 takes a *box*

```text
C = C₁ × ⋯ × Cₙ ⊆ IRⁿ,
```

each `Cⱼ` a nonempty closed interval of `IR` -- bounded or not, degenerate or
not -- and asserts that `C` is Clarke regular and geometrically derivable at
each of its points, with

```text
T_C(x̄) = T_{C₁}(x̄₁) × ⋯ × T_{Cₙ}(x̄ₙ),
N_C(x̄) = N_{C₁}(x̄₁) × ⋯ × N_{Cₙ}(x̄ₙ),
```

the scalar factors being `(-∞,0]`, `[0,∞)`, `IR`, `{0}` for the tangents and
`[0,∞)`, `(-∞,0]`, `{0}`, `IR` for the normals, according as `x̄ⱼ` is the only
right endpoint of `Cⱼ`, the only left endpoint, an interior point, or the
single point of a degenerate `Cⱼ`.

Three design points.

* The ambient space is `EuclideanSpace ℝ ι` for a finite index type `ι`, that
  is `PiLp 2 fun _ ↦ ℝ`, and *not* the raw function type `ι → ℝ`, whose
  standard norm is the sup norm.  Nothing below would be false for the sup
  norm -- the tangent and normal cone definitions only see the topology, and
  the normal cones see the inner product -- but only the `L²` type carries the
  Euclidean inner product that 6(4) is written against.
* The book's coordinate hypothesis is recorded as
  `IsNonemptyClosedInterval`: nonempty, closed, and order connected.  Order
  connectedness is exactly convexity in `ℝ`, so this admits `Set.univ`, both
  closed rays, and every `Icc a b` with `a ≤ b` including the degenerate ones,
  while excluding `∅`.  It never asks for endpoints to exist.
* Rather than case on which of the four printed shapes `Cⱼ` has, the four
  cases are packaged by the two order predicates `IsGreatest` and `IsLeast`:
  `intervalTangentDirections S x` is cut out by `IsGreatest S x → w ≤ 0` and
  `IsLeast S x → 0 ≤ w`, which yields `{0}`, `Iic 0`, `Ici 0`, `univ`
  according as both, only the first, only the second, or neither holds.
  Since `IsGreatest S x ∧ IsLeast S x ↔ S = {x}`
  (`isGreatest_and_isLeast_iff_eq_singleton`), "both" is exactly the
  degenerate case and "only the first" is exactly the book's *only right
  endpoint*.  `intervalNormalDirections` is the mirrored predicate and gives
  `univ`, `Ici 0`, `Iic 0`, `{0}` in the same order.

The finite-product layer -- `finiteBox_convex`, `finiteBox_isClosed`,
`derivableCone_finiteBox`, `tangentCone_finiteBox`,
`regularNormalCone_finiteBox`, `normalCone_finiteBox` -- is proved for
arbitrary coordinate sets (convex ones where convexity is genuinely used), so
it is reusable away from intervals.  The empty index type is not excluded
anywhere: there `EuclideanSpace ℝ ι` is the zero space, `finiteBox C` is all
of it, and every product statement reads as a statement about `univ`.

The binary `WithLp 2` formulas of
[`ProductCones.lean`](RockafellarWets/Chapter6/ProductCones.lean) are a
consistency check on what follows, not an ingredient: `WithLp 2 (E × F)` does
not associate definitionally to `EuclideanSpace ℝ ι`, so the finite products
below are proved directly, synchronizing the coordinate data with
`Finite.exists_min` on the finite index type.
-/

import RockafellarWets.Chapter6.IntervalCones
import RockafellarWets.Chapter6.ElementaryCones
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section BoxDefinition

variable {ι : Type*}

/-- The box `C₁ × ⋯ × Cₙ` of Example 6.10, as a subset of the *Euclidean*
space on the index type `ι`. -/
def finiteBox (C : ι → Set ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, x i ∈ C i}

@[simp]
theorem mem_finiteBox {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ finiteBox C ↔ ∀ i, x i ∈ C i :=
  Iff.rfl

@[simp]
theorem finiteBox_univ : finiteBox (fun _ : ι ↦ (univ : Set ℝ)) = univ := by
  ext x
  simp

end BoxDefinition

section BoxStructure

variable {ι : Type*} [Fintype ι]

/-- A box of convex coordinate sets is convex, the convex combination being
formed coordinate by coordinate. -/
theorem finiteBox_convex {C : ι → Set ℝ} (hC : ∀ i, Convex ℝ (C i)) :
    Convex ℝ (finiteBox C) := by
  intro y hy z hz a b ha hb hab i
  simpa using hC i (hy i) (hz i) ha hb hab

omit [Fintype ι] in
/-- A box of closed coordinate sets is closed, being the intersection of the
preimages of the `C i` under the (continuous) coordinate projections. -/
theorem finiteBox_isClosed {C : ι → Set ℝ} (hC : ∀ i, IsClosed (C i)) :
    IsClosed (finiteBox C) := by
  have hinter : finiteBox C = ⋂ i, (fun z : EuclideanSpace ℝ ι ↦ z i) ⁻¹' C i := by
    ext z
    simp [finiteBox]
  rw [hinter]
  exact isClosed_iInter fun i ↦
    (hC i).preimage (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i)

omit [Fintype ι] in
/-- Convergence in `EuclideanSpace ℝ ι` is coordinatewise convergence: the
`L²` topology on a finite product is the product topology. -/
private theorem tendsto_euclidean_iff {α : Type*} {l : Filter α}
    {f : α → EuclideanSpace ℝ ι} {y : EuclideanSpace ℝ ι} :
    Tendsto f l (nhds y) ↔ ∀ i, Tendsto (fun a ↦ f a i) l (nhds (y i)) := by
  constructor
  · intro h i
    exact ((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).tendsto y).comp h
  · intro h
    have h1 : Tendsto (fun a ↦ (f a).ofLp) l (nhds y.ofLp) := tendsto_pi_nhds.2 h
    have h2 := ((EuclideanSpace.equiv ι ℝ).symm.continuous.tendsto y.ofLp).comp h1
    simpa using h2

/-- Finitely many positive reals have a common positive lower bound.  This is
what synchronizes the coordinate paths of `derivableCone_finiteBox`; the empty
index type is covered by the arbitrary choice `1`. -/
private theorem exists_pos_forall_le {ι : Type*} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i ↦ (hι.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

end BoxStructure

section BoxTangents

variable {ι : Type*} [Fintype ι]

/-- Derivable tangent vectors to a finite box are exactly the vectors whose
coordinates are derivable tangent vectors to the coordinate sets.  No
hypothesis at all is needed: forwards the coordinates of a path are paths,
and backwards the finitely many coordinate paths are restricted to a common
positive radius. -/
theorem derivableCone_finiteBox (C : ι → Set ℝ) (x : EuclideanSpace ℝ ι) :
    derivableCone (finiteBox C) x = {w | ∀ i, w i ∈ derivableCone (C i) (x i)} := by
  ext w
  constructor
  · rintro ⟨ε, hε, ξ, hξ0, hξC, hξt⟩ i
    refine ⟨ε, hε, fun t ↦ ξ t i, by simp [hξ0], fun t ht ↦ hξC t ht i, ?_⟩
    simpa using ((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).tendsto w).comp hξt
  · intro hw
    choose ε hε ξ hξ0 hξC hξt using hw
    obtain ⟨c, hc, hcle⟩ := exists_pos_forall_le ε hε
    refine ⟨c, hc, fun t ↦ (WithLp.toLp 2 fun i ↦ ξ i t : EuclideanSpace ℝ ι), ?_, ?_, ?_⟩
    · ext i
      simpa using hξ0 i
    · intro t ht i
      simpa using hξC i t ⟨ht.1, ht.2.trans (hcle i)⟩
    · refine tendsto_euclidean_iff.2 fun i ↦ ?_
      simpa using hξt i

/-- A tangent vector to a finite box has tangent coordinates.  This half needs
no hypothesis either. -/
theorem tangentCone_finiteBox_subset (C : ι → Set ℝ) (x : EuclideanSpace ℝ ι) :
    tangentCone (finiteBox C) x ⊆ {w | ∀ i, w i ∈ tangentCone (C i) (x i)} := by
  rintro w ⟨xs, τs, hxC, -, hτpos, hτ0, hq⟩ i
  refine mem_tangentCone_of_forall (xs := fun n ↦ xs n i) (fun n ↦ hxC n i) hτpos hτ0 ?_
  simpa using ((PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).tendsto w).comp hq

/-- A box of geometrically derivable coordinate sets is geometrically
derivable: a tangent vector to the box has tangent, hence derivable,
coordinates, and derivable coordinates assemble to a derivable vector. -/
theorem isGeometricallyDerivable_finiteBox {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι}
    (hC : ∀ i, IsGeometricallyDerivable (C i) (x i)) :
    IsGeometricallyDerivable (finiteBox C) x := by
  intro w hw
  rw [derivableCone_finiteBox]
  exact fun i ↦ hC i (tangentCone_finiteBox_subset C x hw i)

/-- **Example 6.10**, the tangent half in product form: at a point of a finite
box whose coordinate sets are geometrically derivable, the tangent cone is the
coordinate product of the tangent cones. -/
theorem tangentCone_finiteBox {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι}
    (hx : x ∈ finiteBox C) (hC : ∀ i, IsGeometricallyDerivable (C i) (x i)) :
    tangentCone (finiteBox C) x = {w | ∀ i, w i ∈ tangentCone (C i) (x i)} := by
  refine Subset.antisymm (tangentCone_finiteBox_subset C x) fun w hw ↦ ?_
  refine derivableCone_subset_tangentCone hx ?_
  rw [derivableCone_finiteBox]
  exact fun i ↦ hC i (hw i)

end BoxTangents

section BoxNormals

variable {ι : Type*} [Fintype ι]

/-- The Euclidean inner product read off coordinatewise. -/
private theorem inner_eq_sum (v y : EuclideanSpace ℝ ι) : ⟪v, y⟫_ℝ = ∑ i, v i * y i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- Testing a vector against a single coordinate direction. -/
private theorem inner_single_right [DecidableEq ι] (v : EuclideanSpace ℝ ι) (i : ι) (c : ℝ) :
    ⟪v, (EuclideanSpace.single i c : EuclideanSpace ℝ ι)⟫_ℝ = v i * c := by
  rw [inner_eq_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Moving a single coordinate of a point of the box to another admissible
value stays in the box. -/
private theorem add_single_mem_finiteBox [DecidableEq ι] {C : ι → Set ℝ}
    {x : EuclideanSpace ℝ ι} (hx : x ∈ finiteBox C) (i : ι) {y : ℝ} (hy : y ∈ C i) :
    x + (EuclideanSpace.single i (y - x i) : EuclideanSpace ℝ ι) ∈ finiteBox C := by
  intro j
  by_cases hj : j = i
  · subst hj
    simpa using hy
  · simpa [hj] using hx j

/-- **Example 6.10**, the regular-normal half in product form.  Both cones are
computed by Theorem 6.9; one inclusion isolates a coordinate by perturbing the
base point along `EuclideanSpace.single`, the other sums the coordinate
inequalities. -/
theorem regularNormalCone_finiteBox {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι}
    (hC : ∀ i, Convex ℝ (C i)) (hx : x ∈ finiteBox C) :
    regularNormalCone (finiteBox C) x = {v | ∀ i, v i ∈ regularNormalCone (C i) (x i)} := by
  classical
  ext v
  rw [regularNormalCone_eq_of_convex (finiteBox_convex hC) hx]
  simp only [mem_setOf_eq]
  constructor
  · intro hv i
    rw [regularNormalCone_eq_of_convex (hC i) (hx i)]
    intro y hy
    have h := hv _ (add_single_mem_finiteBox hx i hy)
    rw [add_sub_cancel_left, inner_single_right] at h
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using h
  · intro hv y hy
    rw [inner_eq_sum]
    refine Finset.sum_nonpos fun i _ ↦ ?_
    have hi := hv i
    rw [regularNormalCone_eq_of_convex (hC i) (hx i)] at hi
    have h := hi (y i) (hy i)
    simp only [RCLike.inner_apply, conj_trivial] at h
    have hsub : (y - x) i = y i - x i := by simp
    rw [hsub, mul_comm]
    exact h

/-- **Example 6.10**, the limiting-normal half in product form.  For convex
coordinate sets the box is convex, so both sides collapse onto the regular
normal cones by Theorem 6.9. -/
theorem normalCone_finiteBox {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι}
    (hC : ∀ i, Convex ℝ (C i)) (hx : x ∈ finiteBox C) :
    normalCone (finiteBox C) x = {v | ∀ i, v i ∈ normalCone (C i) (x i)} := by
  rw [normalCone_eq_regularNormalCone_of_convex (finiteBox_convex hC) hx,
    regularNormalCone_finiteBox hC hx]
  ext v
  simp only [mem_setOf_eq]
  refine forall_congr' fun i ↦ ?_
  rw [normalCone_eq_regularNormalCone_of_convex (hC i) (hx i)]

end BoxNormals

section ScalarIntervals

/-- The book's coordinate hypothesis in Example 6.10: a nonempty closed
interval of `ℝ`, possibly unbounded and possibly a single point.  Order
connectedness is convexity in `ℝ`, so this is precisely the class
`{univ, Ici a, Iic b, Icc a b (a ≤ b)}` -- with `Icc a a = {a}` -- and it
excludes `∅`. -/
def IsNonemptyClosedInterval (S : Set ℝ) : Prop :=
  S.Nonempty ∧ IsClosed S ∧ S.OrdConnected

theorem IsNonemptyClosedInterval.nonempty {S : Set ℝ} (h : IsNonemptyClosedInterval S) :
    S.Nonempty := h.1

theorem IsNonemptyClosedInterval.isClosed {S : Set ℝ} (h : IsNonemptyClosedInterval S) :
    IsClosed S := h.2.1

theorem IsNonemptyClosedInterval.ordConnected {S : Set ℝ} (h : IsNonemptyClosedInterval S) :
    S.OrdConnected := h.2.2

theorem IsNonemptyClosedInterval.convex {S : Set ℝ} (h : IsNonemptyClosedInterval S) :
    Convex ℝ S := convex_iff_ordConnected.mpr h.2.2

theorem isNonemptyClosedInterval_univ : IsNonemptyClosedInterval (univ : Set ℝ) :=
  ⟨⟨0, mem_univ 0⟩, isClosed_univ, ordConnected_univ⟩

theorem isNonemptyClosedInterval_Ici (a : ℝ) : IsNonemptyClosedInterval (Ici a) :=
  ⟨⟨a, self_mem_Ici⟩, isClosed_Ici, ordConnected_Ici⟩

theorem isNonemptyClosedInterval_Iic (b : ℝ) : IsNonemptyClosedInterval (Iic b) :=
  ⟨⟨b, self_mem_Iic⟩, isClosed_Iic, ordConnected_Iic⟩

theorem isNonemptyClosedInterval_Icc {a b : ℝ} (hab : a ≤ b) :
    IsNonemptyClosedInterval (Icc a b) :=
  ⟨nonempty_Icc.2 hab, isClosed_Icc, ordConnected_Icc⟩

theorem isNonemptyClosedInterval_singleton (a : ℝ) : IsNonemptyClosedInterval ({a} : Set ℝ) :=
  ⟨singleton_nonempty a, isClosed_singleton, ordConnected_singleton⟩

/-- The two order predicates hold together exactly at a degenerate interval,
which is what makes "only right endpoint" and "only left endpoint" below
faithful readings of Example 6.10. -/
theorem isGreatest_and_isLeast_iff_eq_singleton {S : Set ℝ} {x : ℝ} :
    (IsGreatest S x ∧ IsLeast S x) ↔ S = {x} := by
  constructor
  · rintro ⟨⟨hxS, hub⟩, ⟨-, hlb⟩⟩
    exact Subset.antisymm (fun y hy ↦ mem_singleton_iff.2 (le_antisymm (hub hy) (hlb hy)))
      (singleton_subset_iff.2 hxS)
  · rintro rfl
    exact ⟨isGreatest_singleton, isLeast_singleton⟩

private theorem not_isGreatest_of_lt {S : Set ℝ} {x y : ℝ} (hy : y ∈ S) (h : x < y) :
    ¬ IsGreatest S x := fun hg ↦ absurd (hg.2 hy) (not_le.2 h)

private theorem not_isLeast_of_lt {S : Set ℝ} {x y : ℝ} (hy : y ∈ S) (h : y < x) :
    ¬ IsLeast S x := fun hl ↦ absurd (hl.2 hy) (not_le.2 h)

private theorem exists_gt_of_not_isGreatest {S : Set ℝ} {x : ℝ} (hx : x ∈ S)
    (h : ¬ IsGreatest S x) : ∃ y ∈ S, x < y := by
  by_contra hcon
  push_neg at hcon
  exact h ⟨hx, fun y hy ↦ hcon y hy⟩

private theorem exists_lt_of_not_isLeast {S : Set ℝ} {x : ℝ} (hx : x ∈ S)
    (h : ¬ IsLeast S x) : ∃ y ∈ S, y < x := by
  by_contra hcon
  push_neg at hcon
  exact h ⟨hx, fun y hy ↦ hcon y hy⟩

/-- The scaling that carries `x` along a direction `w ≠ 0` exactly onto a
prescribed second point `y` of the set. -/
private theorem add_div_mul_cancel {x y w : ℝ} (hw : w ≠ 0) : x + (y - x) / w * w = y := by
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hw, mul_one]
  ring

/-- The scalar tangent directions of Example 6.10 at `x` in `S`: `{0}` when
`x` is both endpoint, that is `S = {x}`; `Iic 0` when `x` is the only right
endpoint; `Ici 0` when `x` is the only left endpoint; and `univ` -- the whole
line -- otherwise. -/
def intervalTangentDirections (S : Set ℝ) (x : ℝ) : Set ℝ :=
  {w | (IsGreatest S x → w ≤ 0) ∧ (IsLeast S x → 0 ≤ w)}

/-- The scalar normal directions of Example 6.10 at `x` in `S`: `univ` when
`S = {x}`; `Ici 0` at an only right endpoint; `Iic 0` at an only left
endpoint; and `{0}` at an interior point.  This is the polar pattern of
`intervalTangentDirections`. -/
def intervalNormalDirections (S : Set ℝ) (x : ℝ) : Set ℝ :=
  {v | (¬ IsGreatest S x → v ≤ 0) ∧ (¬ IsLeast S x → 0 ≤ v)}

@[simp]
theorem mem_intervalTangentDirections {S : Set ℝ} {x w : ℝ} :
    w ∈ intervalTangentDirections S x ↔
      (IsGreatest S x → w ≤ 0) ∧ (IsLeast S x → 0 ≤ w) := Iff.rfl

@[simp]
theorem mem_intervalNormalDirections {S : Set ℝ} {x v : ℝ} :
    v ∈ intervalNormalDirections S x ↔
      (¬ IsGreatest S x → v ≤ 0) ∧ (¬ IsLeast S x → 0 ≤ v) := Iff.rfl

/-- Degenerate interval: the tangent directions are `{0}`. -/
theorem intervalTangentDirections_of_isGreatest_of_isLeast {S : Set ℝ} {x : ℝ}
    (hg : IsGreatest S x) (hl : IsLeast S x) : intervalTangentDirections S x = {0} := by
  ext w
  simp only [mem_intervalTangentDirections, mem_singleton_iff]
  exact ⟨fun h ↦ le_antisymm (h.1 hg) (h.2 hl), fun h ↦ ⟨fun _ ↦ h.le, fun _ ↦ h.ge⟩⟩

/-- Only right endpoint: the tangent directions are `(-∞, 0]`. -/
theorem intervalTangentDirections_of_isGreatest {S : Set ℝ} {x : ℝ}
    (hg : IsGreatest S x) (hl : ¬ IsLeast S x) : intervalTangentDirections S x = Iic 0 := by
  ext w
  simp [hg, hl]

/-- Only left endpoint: the tangent directions are `[0, ∞)`. -/
theorem intervalTangentDirections_of_isLeast {S : Set ℝ} {x : ℝ}
    (hg : ¬ IsGreatest S x) (hl : IsLeast S x) : intervalTangentDirections S x = Ici 0 := by
  ext w
  simp [hg, hl]

/-- Interior point: the tangent directions are the whole line. -/
theorem intervalTangentDirections_of_not_isGreatest_of_not_isLeast {S : Set ℝ} {x : ℝ}
    (hg : ¬ IsGreatest S x) (hl : ¬ IsLeast S x) : intervalTangentDirections S x = univ := by
  ext w
  simp [hg, hl]

/-- Degenerate interval: every direction is normal. -/
theorem intervalNormalDirections_of_isGreatest_of_isLeast {S : Set ℝ} {x : ℝ}
    (hg : IsGreatest S x) (hl : IsLeast S x) : intervalNormalDirections S x = univ := by
  ext v
  simp [hg, hl]

/-- Only right endpoint: the normal directions are `[0, ∞)`. -/
theorem intervalNormalDirections_of_isGreatest {S : Set ℝ} {x : ℝ}
    (hg : IsGreatest S x) (hl : ¬ IsLeast S x) : intervalNormalDirections S x = Ici 0 := by
  ext v
  simp [hg, hl]

/-- Only left endpoint: the normal directions are `(-∞, 0]`. -/
theorem intervalNormalDirections_of_isLeast {S : Set ℝ} {x : ℝ}
    (hg : ¬ IsGreatest S x) (hl : IsLeast S x) : intervalNormalDirections S x = Iic 0 := by
  ext v
  simp [hg, hl]

/-- Interior point: the only normal direction is `0`. -/
theorem intervalNormalDirections_of_not_isGreatest_of_not_isLeast {S : Set ℝ} {x : ℝ}
    (hg : ¬ IsGreatest S x) (hl : ¬ IsLeast S x) : intervalNormalDirections S x = {0} := by
  ext v
  simp only [mem_intervalNormalDirections, mem_singleton_iff]
  exact ⟨fun h ↦ le_antisymm (h.1 hg) (h.2 hl), fun h ↦ ⟨fun _ ↦ h.le, fun _ ↦ h.ge⟩⟩

theorem intervalTangentDirections_singleton (x : ℝ) :
    intervalTangentDirections ({x} : Set ℝ) x = {0} :=
  intervalTangentDirections_of_isGreatest_of_isLeast isGreatest_singleton isLeast_singleton

theorem intervalNormalDirections_singleton (x : ℝ) :
    intervalNormalDirections ({x} : Set ℝ) x = univ :=
  intervalNormalDirections_of_isGreatest_of_isLeast isGreatest_singleton isLeast_singleton

/-- The whole line reduces correctly on the tangent side. -/
theorem intervalTangentDirections_univ (x : ℝ) :
    intervalTangentDirections (univ : Set ℝ) x = univ :=
  intervalTangentDirections_of_not_isGreatest_of_not_isLeast
    (not_isGreatest_of_lt (mem_univ (x + 1)) (by linarith))
    (not_isLeast_of_lt (mem_univ (x - 1)) (by linarith))

/-- The whole line reduces correctly on the normal side. -/
theorem intervalNormalDirections_univ (x : ℝ) :
    intervalNormalDirections (univ : Set ℝ) x = {0} :=
  intervalNormalDirections_of_not_isGreatest_of_not_isLeast
    (not_isGreatest_of_lt (mem_univ (x + 1)) (by linarith))
    (not_isLeast_of_lt (mem_univ (x - 1)) (by linarith))

theorem intervalTangentDirections_Ici_self (a : ℝ) :
    intervalTangentDirections (Ici a) a = Ici 0 :=
  intervalTangentDirections_of_isLeast
    (not_isGreatest_of_lt (y := a + 1) (mem_Ici.2 (by linarith)) (by linarith)) isLeast_Ici

theorem intervalNormalDirections_Ici_self (a : ℝ) :
    intervalNormalDirections (Ici a) a = Iic 0 :=
  intervalNormalDirections_of_isLeast
    (not_isGreatest_of_lt (y := a + 1) (mem_Ici.2 (by linarith)) (by linarith)) isLeast_Ici

theorem intervalTangentDirections_Iic_self (b : ℝ) :
    intervalTangentDirections (Iic b) b = Iic 0 :=
  intervalTangentDirections_of_isGreatest isGreatest_Iic
    (not_isLeast_of_lt (y := b - 1) (mem_Iic.2 (by linarith)) (by linarith))

theorem intervalNormalDirections_Iic_self (b : ℝ) :
    intervalNormalDirections (Iic b) b = Ici 0 :=
  intervalNormalDirections_of_isGreatest isGreatest_Iic
    (not_isLeast_of_lt (y := b - 1) (mem_Iic.2 (by linarith)) (by linarith))

theorem intervalTangentDirections_Icc_left {a b : ℝ} (hab : a < b) :
    intervalTangentDirections (Icc a b) a = Ici 0 :=
  intervalTangentDirections_of_isLeast
    (not_isGreatest_of_lt (right_mem_Icc.2 hab.le) hab) (isLeast_Icc hab.le)

theorem intervalTangentDirections_Icc_right {a b : ℝ} (hab : a < b) :
    intervalTangentDirections (Icc a b) b = Iic 0 :=
  intervalTangentDirections_of_isGreatest (isGreatest_Icc hab.le)
    (not_isLeast_of_lt (left_mem_Icc.2 hab.le) hab)

theorem intervalTangentDirections_Icc_interior {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    intervalTangentDirections (Icc a b) x = univ :=
  intervalTangentDirections_of_not_isGreatest_of_not_isLeast
    (not_isGreatest_of_lt (right_mem_Icc.2 (hax.trans hxb).le) hxb)
    (not_isLeast_of_lt (left_mem_Icc.2 (hax.trans hxb).le) hax)

theorem intervalNormalDirections_Icc_left {a b : ℝ} (hab : a < b) :
    intervalNormalDirections (Icc a b) a = Iic 0 :=
  intervalNormalDirections_of_isLeast
    (not_isGreatest_of_lt (right_mem_Icc.2 hab.le) hab) (isLeast_Icc hab.le)

theorem intervalNormalDirections_Icc_right {a b : ℝ} (hab : a < b) :
    intervalNormalDirections (Icc a b) b = Ici 0 :=
  intervalNormalDirections_of_isGreatest (isGreatest_Icc hab.le)
    (not_isLeast_of_lt (left_mem_Icc.2 hab.le) hab)

theorem intervalNormalDirections_Icc_interior {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    intervalNormalDirections (Icc a b) x = {0} :=
  intervalNormalDirections_of_not_isGreatest_of_not_isLeast
    (not_isGreatest_of_lt (right_mem_Icc.2 (hax.trans hxb).le) hxb)
    (not_isLeast_of_lt (left_mem_Icc.2 (hax.trans hxb).le) hax)

/-- Each of the four cases is a closed set. -/
theorem isClosed_intervalTangentDirections (S : Set ℝ) (x : ℝ) :
    IsClosed (intervalTangentDirections S x) := by
  by_cases hg : IsGreatest S x <;> by_cases hl : IsLeast S x
  · rw [intervalTangentDirections_of_isGreatest_of_isLeast hg hl]
    exact isClosed_singleton
  · rw [intervalTangentDirections_of_isGreatest hg hl]
    exact isClosed_Iic
  · rw [intervalTangentDirections_of_isLeast hg hl]
    exact isClosed_Ici
  · rw [intervalTangentDirections_of_not_isGreatest_of_not_isLeast hg hl]
    exact isClosed_univ

/-- The radial cone of *any* subset of `ℝ` at one of its points is already
the four-case set: no closedness or convexity enters, because when `w` points
strictly into the set the scaling `λ = (y - x)/w` lands exactly on a witness
`y`. -/
theorem radialCone_eq_intervalTangentDirections {S : Set ℝ} {x : ℝ} (hx : x ∈ S) :
    radialCone S x = intervalTangentDirections S x := by
  ext w
  simp only [mem_radialCone, mem_intervalTangentDirections, smul_eq_mul]
  constructor
  · rintro ⟨lam, hlam, hmem⟩
    refine ⟨fun hg ↦ ?_, fun hl ↦ ?_⟩
    · nlinarith [hg.2 hmem]
    · nlinarith [hl.2 hmem]
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy w 0 with hw | rfl | hw
    · obtain ⟨y, hy, hyx⟩ := exists_lt_of_not_isLeast hx (fun hl ↦ absurd (h2 hl) (by linarith))
      refine ⟨(y - x) / w, div_pos_of_neg_of_neg (by linarith) hw, ?_⟩
      rw [add_div_mul_cancel (ne_of_lt hw)]
      exact hy
    · exact ⟨1, one_pos, by simpa using hx⟩
    · obtain ⟨y, hy, hxy⟩ :=
        exists_gt_of_not_isGreatest hx (fun hg ↦ absurd (h1 hg) (by linarith))
      refine ⟨(y - x) / w, div_pos (by linarith) hw, ?_⟩
      rw [add_div_mul_cancel (ne_of_gt hw)]
      exact hy

/-- **Example 6.10**, scalar tangent cone.  Every point of a nonempty closed
interval has the four-case tangent cone; only order connectedness is used. -/
theorem tangentCone_eq_intervalTangentDirections {S : Set ℝ} (hS : S.OrdConnected) {x : ℝ}
    (hx : x ∈ S) : tangentCone S x = intervalTangentDirections S x := by
  rw [tangentCone_eq_closure_radialCone (convex_iff_ordConnected.mpr hS) hx,
    radialCone_eq_intervalTangentDirections hx,
    (isClosed_intervalTangentDirections S x).closure_eq]

/-- **Example 6.10**, scalar derivable cone: the same four cases, so every
point of an order-connected set is geometrically derivable. -/
theorem derivableCone_eq_intervalTangentDirections {S : Set ℝ} (hS : S.OrdConnected) {x : ℝ}
    (hx : x ∈ S) : derivableCone S x = intervalTangentDirections S x := by
  rw [derivableCone_eq_closure_radialCone (convex_iff_ordConnected.mpr hS) hx,
    radialCone_eq_intervalTangentDirections hx,
    (isClosed_intervalTangentDirections S x).closure_eq]

/-- **Example 6.10**, scalar regular normal cone. -/
theorem regularNormalCone_eq_intervalNormalDirections {S : Set ℝ} (hS : S.OrdConnected) {x : ℝ}
    (hx : x ∈ S) : regularNormalCone S x = intervalNormalDirections S x := by
  rw [regularNormalCone_eq_of_convex (convex_iff_ordConnected.mpr hS) hx]
  ext v
  simp only [mem_setOf_eq, mem_intervalNormalDirections, RCLike.inner_apply, conj_trivial]
  constructor
  · intro h
    refine ⟨fun hg ↦ ?_, fun hl ↦ ?_⟩
    · obtain ⟨y, hy, hxy⟩ := exists_gt_of_not_isGreatest hx hg
      nlinarith [h y hy]
    · obtain ⟨y, hy, hyx⟩ := exists_lt_of_not_isLeast hx hl
      nlinarith [h y hy]
  · rintro ⟨h1, h2⟩ y hy
    rcases lt_trichotomy y x with hlt | rfl | hgt
    · nlinarith [h2 (not_isLeast_of_lt hy hlt)]
    · simp
    · nlinarith [h1 (not_isGreatest_of_lt hy hgt)]

/-- **Example 6.10**, scalar limiting normal cone: the same four cases, the
two normal cones coinciding by Theorem 6.9. -/
theorem normalCone_eq_intervalNormalDirections {S : Set ℝ} (hS : S.OrdConnected) {x : ℝ}
    (hx : x ∈ S) : normalCone S x = intervalNormalDirections S x := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_iff_ordConnected.mpr hS) hx,
    regularNormalCone_eq_intervalNormalDirections hS hx]

/-- Every point of an order-connected subset of `ℝ` is geometrically
derivable. -/
theorem isGeometricallyDerivable_of_ordConnected {S : Set ℝ} (hS : S.OrdConnected) {x : ℝ}
    (hx : x ∈ S) : IsGeometricallyDerivable S x :=
  isGeometricallyDerivable_of_convex (convex_iff_ordConnected.mpr hS) hx

end ScalarIntervals

section Example610

variable {ι : Type*} [Fintype ι]

/-- **Example 6.10**: the tangent cone to a box of nonempty closed intervals
is the coordinate product of the four-case scalar tangent cones. -/
theorem tangentCone_finiteBox_of_closedIntervals {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι}
    (hC : ∀ i, IsNonemptyClosedInterval (C i)) (hx : x ∈ finiteBox C) :
    tangentCone (finiteBox C) x =
      {w | ∀ i, w i ∈ intervalTangentDirections (C i) (x i)} := by
  rw [tangentCone_finiteBox hx fun i ↦
    isGeometricallyDerivable_of_ordConnected (hC i).ordConnected (hx i)]
  ext w
  simp only [mem_setOf_eq]
  exact forall_congr' fun i ↦ by
    rw [tangentCone_eq_intervalTangentDirections (hC i).ordConnected (hx i)]

/-- **Example 6.10**: the derivable tangent vectors to a box of nonempty
closed intervals are the same coordinate product, the box being geometrically
derivable. -/
theorem derivableCone_finiteBox_of_closedIntervals {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι}
    (hC : ∀ i, IsNonemptyClosedInterval (C i)) (hx : x ∈ finiteBox C) :
    derivableCone (finiteBox C) x =
      {w | ∀ i, w i ∈ intervalTangentDirections (C i) (x i)} := by
  rw [derivableCone_finiteBox]
  ext w
  simp only [mem_setOf_eq]
  exact forall_congr' fun i ↦ by
    rw [derivableCone_eq_intervalTangentDirections (hC i).ordConnected (hx i)]

/-- **Example 6.10**: the regular normal cone to a box of nonempty closed
intervals is the coordinate product of the four-case scalar regular normal
cones. -/
theorem regularNormalCone_finiteBox_of_closedIntervals {C : ι → Set ℝ}
    {x : EuclideanSpace ℝ ι} (hC : ∀ i, IsNonemptyClosedInterval (C i))
    (hx : x ∈ finiteBox C) :
    regularNormalCone (finiteBox C) x =
      {v | ∀ i, v i ∈ intervalNormalDirections (C i) (x i)} := by
  rw [regularNormalCone_finiteBox (fun i ↦ (hC i).convex) hx]
  ext v
  simp only [mem_setOf_eq]
  exact forall_congr' fun i ↦ by
    rw [regularNormalCone_eq_intervalNormalDirections (hC i).ordConnected (hx i)]

/-- **Example 6.10**: the limiting normal cone to a box of nonempty closed
intervals is the coordinate product of the four-case scalar normal cones. -/
theorem normalCone_finiteBox_of_closedIntervals {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι}
    (hC : ∀ i, IsNonemptyClosedInterval (C i)) (hx : x ∈ finiteBox C) :
    normalCone (finiteBox C) x =
      {v | ∀ i, v i ∈ intervalNormalDirections (C i) (x i)} := by
  rw [normalCone_finiteBox (fun i ↦ (hC i).convex) hx]
  ext v
  simp only [mem_setOf_eq]
  exact forall_congr' fun i ↦ by
    rw [normalCone_eq_intervalNormalDirections (hC i).ordConnected (hx i)]

/-- **Example 6.10**: a box of nonempty closed intervals is geometrically
derivable at each of its points. -/
theorem isGeometricallyDerivable_finiteBox_of_closedIntervals {C : ι → Set ℝ}
    {x : EuclideanSpace ℝ ι} (hC : ∀ i, IsNonemptyClosedInterval (C i))
    (hx : x ∈ finiteBox C) : IsGeometricallyDerivable (finiteBox C) x :=
  isGeometricallyDerivable_finiteBox fun i ↦
    isGeometricallyDerivable_of_ordConnected (hC i).ordConnected (hx i)

/-- **Example 6.10**: a box of nonempty closed intervals is Clarke regular at
each of its points. -/
theorem isClarkeRegularAt_finiteBox_of_closedIntervals {C : ι → Set ℝ}
    {x : EuclideanSpace ℝ ι} (hC : ∀ i, IsNonemptyClosedInterval (C i))
    (hx : x ∈ finiteBox C) : IsClarkeRegularAt (finiteBox C) x :=
  isClarkeRegularAt_of_convex (finiteBox_convex fun i ↦ (hC i).convex) hx
    (RW.IsClosed.isLocallyClosedAt (finiteBox_isClosed fun i ↦ (hC i).isClosed) x)

/-- **Example 6.10** in full: a box of nonempty closed intervals is closed,
convex, geometrically derivable and Clarke regular at each of its points, and
its four cones are the coordinate products of the scalar four-case sets. -/
theorem variationalGeometry_finiteBox_of_closedIntervals {C : ι → Set ℝ}
    {x : EuclideanSpace ℝ ι}
    (hC : ∀ i, IsNonemptyClosedInterval (C i)) (hx : x ∈ finiteBox C) :
    IsClosed (finiteBox C) ∧ Convex ℝ (finiteBox C) ∧
      IsGeometricallyDerivable (finiteBox C) x ∧ IsClarkeRegularAt (finiteBox C) x ∧
      tangentCone (finiteBox C) x =
        {w | ∀ i, w i ∈ intervalTangentDirections (C i) (x i)} ∧
      derivableCone (finiteBox C) x =
        {w | ∀ i, w i ∈ intervalTangentDirections (C i) (x i)} ∧
      regularNormalCone (finiteBox C) x =
        {v | ∀ i, v i ∈ intervalNormalDirections (C i) (x i)} ∧
      normalCone (finiteBox C) x =
        {v | ∀ i, v i ∈ intervalNormalDirections (C i) (x i)} :=
  ⟨finiteBox_isClosed fun i ↦ (hC i).isClosed, finiteBox_convex fun i ↦ (hC i).convex,
    isGeometricallyDerivable_finiteBox_of_closedIntervals hC hx,
    isClarkeRegularAt_finiteBox_of_closedIntervals hC hx,
    tangentCone_finiteBox_of_closedIntervals hC hx,
    derivableCone_finiteBox_of_closedIntervals hC hx,
    regularNormalCone_finiteBox_of_closedIntervals hC hx,
    normalCone_finiteBox_of_closedIntervals hC hx⟩

end Example610

section Consistency

/-! Sanity checks against the one-dimensional formulas already available in
[`IntervalCones.lean`](RockafellarWets/Chapter6/IntervalCones.lean) and
[`ElementaryCones.lean`](RockafellarWets/Chapter6/ElementaryCones.lean), and
against the degenerate index type. -/

example {a b : ℝ} (hab : a < b) : tangentCone (Icc a b) a = Ici 0 := by
  rw [tangentCone_eq_intervalTangentDirections ordConnected_Icc (left_mem_Icc.2 hab.le),
    intervalTangentDirections_Icc_left hab]

example {a b : ℝ} (hab : a < b) : tangentCone (Icc a b) b = Iic 0 := by
  rw [tangentCone_eq_intervalTangentDirections ordConnected_Icc (right_mem_Icc.2 hab.le),
    intervalTangentDirections_Icc_right hab]

example {a b : ℝ} (hab : a < b) : normalCone (Icc a b) b = Ici 0 := by
  rw [normalCone_eq_intervalNormalDirections ordConnected_Icc (right_mem_Icc.2 hab.le),
    intervalNormalDirections_Icc_right hab]

example (a : ℝ) : tangentCone (Ici a) a = Ici 0 := by
  rw [tangentCone_eq_intervalTangentDirections ordConnected_Ici self_mem_Ici,
    intervalTangentDirections_Ici_self]

example (b : ℝ) : regularNormalCone (Iic b) b = Ici 0 := by
  rw [regularNormalCone_eq_intervalNormalDirections ordConnected_Iic self_mem_Iic,
    intervalNormalDirections_Iic_self]

example (x : ℝ) : tangentCone ({x} : Set ℝ) x = {0} := by
  rw [tangentCone_eq_intervalTangentDirections ordConnected_singleton rfl,
    intervalTangentDirections_singleton]

/-- The whole-line coordinate case: `intervalTangentDirections` and
`intervalNormalDirections` agree with `tangentCone_univ` and
`normalCone_univ`. -/
example (x : ℝ) : tangentCone (univ : Set ℝ) x = univ := by
  rw [tangentCone_eq_intervalTangentDirections ordConnected_univ (mem_univ x),
    intervalTangentDirections_univ]

example (x : ℝ) : normalCone (univ : Set ℝ) x = {0} := by
  rw [normalCone_eq_intervalNormalDirections ordConnected_univ (mem_univ x),
    intervalNormalDirections_univ]

/-- A box all of whose coordinates are the whole line is the whole space, and
Example 6.10 returns the expected `{0}` normal cone there. -/
example {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    normalCone (finiteBox fun _ : ι ↦ (univ : Set ℝ)) x =
      {v | ∀ i, v i ∈ intervalNormalDirections (univ : Set ℝ) (x i)} :=
  normalCone_finiteBox_of_closedIntervals (fun _ ↦ isNonemptyClosedInterval_univ) (by simp)

example {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    {v : EuclideanSpace ℝ ι | ∀ i, v i ∈ intervalNormalDirections (univ : Set ℝ) (x i)}
      = {0} := by
  ext v
  simp only [intervalNormalDirections_univ, mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro h
    ext i
    simpa using h i
  · rintro rfl i
    simp

example {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    normalCone (finiteBox fun _ : ι ↦ (univ : Set ℝ)) x = {0} := by
  rw [finiteBox_univ, normalCone_univ]

/-- The empty index type is not excluded: the box is then all of the zero
dimensional space `EuclideanSpace ℝ Empty`. -/
example (C : Empty → Set ℝ) (x : EuclideanSpace ℝ Empty) :
    tangentCone (finiteBox C) x = univ := by
  rw [tangentCone_finiteBox (fun i ↦ i.elim) (fun i ↦ i.elim)]
  ext w
  simp

end Consistency

end RW
