/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Variational inequalities and complementarity (Example 6.13)

For any set `C ⊆ IRⁿ` and any mapping `F : C → IRⁿ`, Example 6.13 calls the
relation

```text
F(x̄) + N_C(x̄) ∋ 0
```

the *variational condition* for `C` and `F`, a vector `x̄ ∈ C` satisfying it
being a *solution*.  When `C` is convex it is also called the *variational
inequality* for `C` and `F`, because it can then be written equivalently as

```text
x̄ ∈ C,   ⟨F(x̄), x - x̄⟩ ≥ 0  for all x ∈ C,
```

and interpreted as saying that the linear function `l(x) = ⟨F(x̄), x⟩`
achieves its minimum over `C` at `x̄`.  In the special case `C = IRⁿ₊` it is
the *complementarity condition* for `F`, coming out as

```text
x̄ⱼ ≥ 0,  v̄ⱼ ≥ 0,  x̄ⱼ v̄ⱼ = 0  for j = 1, …, n,  where v̄ = F(x̄),
```

summarized vectorially by `0 ≤ x̄ ⟂ F(x̄) ≥ 0`.

Four design points.

* **`F` is arbitrary.**  The printed statement asks for *any* mapping, and
  nothing below assumes continuity, monotonicity, or that `F` is a gradient;
  only the single vector `F(x̄)` ever enters.  `F` is carried as a total map
  `E → E` rather than a partial map on `C`, which changes nothing since the
  condition is only ever read at a point of `C`.
* **The feasibility conjunct is redundant.**  `IsVariationalSolution` records
  `x̄ ∈ C` alongside `-F(x̄) ∈ N_C(x̄)`, as the book writes `x̄ ∈ C` next to the
  inequality, but `isVariationalSolution_iff_neg_mem_normalCone` shows the
  first conjunct is implied by the second: normal cones are empty off `C`.
  `isVariationalSolution_iff_zero_mem_singleton_add` is the printed form
  `F(x̄) + N_C(x̄) ∋ 0`, with `{F(x̄)} + N_C(x̄)` the pointwise sum of sets.
* **The general equivalences need no finite-dimensionality.**  They rest on
  Theorem 6.9 through `neg_mem_normalCone_iff_forall_inner_nonneg_of_convex`
  of [`Optimality.lean`](RockafellarWets/Chapter6/Optimality.lean), which is
  dimension-free, so the ambient space is an arbitrary real inner product
  space for everything up to the complementarity section.
* **The orthant is a genuine Euclidean product.**  `IRⁿ₊` is the finite box
  `finiteBox (fun _ ↦ [0, ∞))` of Example 6.10 inside `EuclideanSpace ℝ ι`,
  that is `PiLp 2 fun _ ↦ ℝ`, and *not* the raw function type `ι → ℝ`, whose
  standard norm is the sup norm and which therefore carries no Euclidean
  inner product.  The book's coordinate reduction is then exactly the `Ici`
  case of the interval classification of Example 6.10: at `x̄ⱼ = 0` the set
  `[0, ∞)` has a least element and no greatest one, so its normal directions
  are `(-∞, 0]` and only `v̄ⱼ ≥ 0` is required, whereas at `x̄ⱼ > 0` it has
  neither, so the only normal direction is `0` and `v̄ⱼ = 0` is forced.  That
  is the book's *"this requires `v̄ⱼ = 0` when `x̄ⱼ > 0` but merely `v̄ⱼ ≥ 0`
  when `x̄ⱼ = 0`"*.  The empty index type is not excluded: there the orthant
  is the whole zero dimensional space and every point is a solution.
-/

import RockafellarWets.Chapter6.FiniteBoxes
import RockafellarWets.Chapter6.Optimality
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Order.Filter.Extr

open Filter Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

section VariationalCondition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Example 6.13**: `x̄` is a *solution of the variational condition* for
`C` and `F` when `x̄ ∈ C` and `F(x̄) + N_C(x̄) ∋ 0`, that is
`-F(x̄) ∈ N_C(x̄)`. -/
def IsVariationalSolution (C : Set E) (F : E → E) (x : E) : Prop :=
  x ∈ C ∧ -F x ∈ normalCone C x

variable {C : Set E} {F : E → E} {x : E}

/-- A solution is feasible. -/
theorem IsVariationalSolution.mem (h : IsVariationalSolution C F x) : x ∈ C := h.1

theorem IsVariationalSolution.neg_mem_normalCone (h : IsVariationalSolution C F x) :
    -F x ∈ normalCone C x := h.2

/-- The feasibility conjunct is redundant, `N_C(x̄)` being empty when
`x̄ ∉ C`.  This is the form `-F(x̄) ∈ N_C(x̄)` of the variational
condition. -/
theorem isVariationalSolution_iff_neg_mem_normalCone :
    IsVariationalSolution C F x ↔ -F x ∈ normalCone C x :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨h.1, h⟩⟩

theorem not_isVariationalSolution_of_notMem (hx : x ∉ C) :
    ¬ IsVariationalSolution C F x := fun h ↦ hx h.mem

/-- **Example 6.13** exactly as printed: the variational condition is
`F(x̄) + N_C(x̄) ∋ 0`, the sum being the pointwise sum of the singleton
`{F(x̄)}` with the normal cone. -/
theorem isVariationalSolution_iff_zero_mem_singleton_add :
    IsVariationalSolution C F x ↔ (0 : E) ∈ ({F x} : Set E) + normalCone C x := by
  rw [isVariationalSolution_iff_neg_mem_normalCone]
  constructor
  · intro h
    exact ⟨F x, rfl, -F x, h, by simp⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    rw [mem_singleton_iff] at hu
    subst hu
    rwa [neg_eq_iff_add_eq_zero.2 huv]

/-- **Example 6.13**, the convex case: the variational condition is the
*variational inequality* `⟨F(x̄), x - x̄⟩ ≥ 0` for all `x ∈ C`.  Only
Theorem 6.9 is used, so no finite-dimensionality is needed. -/
theorem isVariationalSolution_iff_forall_inner_nonneg_of_convex (hC : Convex ℝ C) :
    IsVariationalSolution C F x ↔
      x ∈ C ∧ ∀ y ∈ C, 0 ≤ ⟪F x, y - x⟫_ℝ := by
  constructor
  · intro h
    exact ⟨h.mem, (neg_mem_normalCone_iff_forall_inner_nonneg_of_convex hC h.mem).1 h.2⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (neg_mem_normalCone_iff_forall_inner_nonneg_of_convex hC hx).2 h⟩

/-- **Example 6.13**, the interpretation of the variational inequality: the
linear function `l(x) = ⟨F(x̄), x⟩` achieves its minimum over `C` at `x̄`. -/
theorem isVariationalSolution_iff_isMinOn_linear_of_convex (hC : Convex ℝ C) :
    IsVariationalSolution C F x ↔
      x ∈ C ∧ IsMinOn (fun y ↦ ⟪F x, y⟫_ℝ) C x := by
  rw [isVariationalSolution_iff_forall_inner_nonneg_of_convex hC]
  refine and_congr_right fun _ ↦ ?_
  rw [isMinOn_iff]
  refine forall_congr' fun y ↦ imp_congr_right fun _ ↦ ?_
  change 0 ≤ ⟪F x, y - x⟫_ℝ ↔ ⟪F x, x⟫_ℝ ≤ ⟪F x, y⟫_ℝ
  rw [inner_sub_right]
  exact sub_nonneg

/-- **Example 6.13** for a convex set, in one statement: the printed set
inclusion, the variational inequality, and the linear minimization property
are all equivalent to the variational condition. -/
theorem variationalCondition_equivalences_of_convex (hC : Convex ℝ C) :
    (IsVariationalSolution C F x ↔ (0 : E) ∈ ({F x} : Set E) + normalCone C x) ∧
    (IsVariationalSolution C F x ↔ -F x ∈ normalCone C x) ∧
    (IsVariationalSolution C F x ↔ x ∈ C ∧ ∀ y ∈ C, 0 ≤ ⟪F x, y - x⟫_ℝ) ∧
    (IsVariationalSolution C F x ↔ x ∈ C ∧ IsMinOn (fun y ↦ ⟪F x, y⟫_ℝ) C x) :=
  ⟨isVariationalSolution_iff_zero_mem_singleton_add,
    isVariationalSolution_iff_neg_mem_normalCone,
    isVariationalSolution_iff_forall_inner_nonneg_of_convex hC,
    isVariationalSolution_iff_isMinOn_linear_of_convex hC⟩

/-- A constant mapping turns the variational condition into plain
minimization of a linear function over `C`, which is the reading of 6.13
supplied by Theorem 6.12. -/
theorem isVariationalSolution_const_iff_isMinOn_of_convex {c : E} (hC : Convex ℝ C) :
    IsVariationalSolution C (fun _ ↦ c) x ↔ x ∈ C ∧ IsMinOn (fun y ↦ ⟪c, y⟫_ℝ) C x :=
  isVariationalSolution_iff_isMinOn_linear_of_convex hC

end VariationalCondition

section OrthantDefinition

variable {ι : Type*}

/-- The nonnegative orthant `IRⁿ₊` of Example 6.13, as the finite box of
Example 6.10 whose coordinate sets are all `[0, ∞)`, inside the *Euclidean*
space on the index type `ι`. -/
def euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι) :=
  finiteBox fun _ ↦ Ici 0

theorem euclideanNonnegativeOrthant_eq_finiteBox :
    (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) =
      finiteBox fun _ ↦ Ici 0 := rfl

@[simp]
theorem mem_euclideanNonnegativeOrthant {x : EuclideanSpace ℝ ι} :
    x ∈ (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) ↔ ∀ i, 0 ≤ x i :=
  Iff.rfl

theorem zero_mem_euclideanNonnegativeOrthant :
    (0 : EuclideanSpace ℝ ι) ∈ (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) := by
  simp

end OrthantDefinition

section OrthantStructure

variable {ι : Type*} [Fintype ι]

theorem convex_euclideanNonnegativeOrthant :
    Convex ℝ (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) :=
  finiteBox_convex fun _ ↦ convex_Ici 0

omit [Fintype ι] in
theorem isClosed_euclideanNonnegativeOrthant :
    IsClosed (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) :=
  finiteBox_isClosed fun _ ↦ isClosed_Ici

/-- At a *positive* point the ray `[0, ∞)` is neither greatest nor least, so
by Example 6.10 the only normal direction there is `0`. -/
theorem intervalNormalDirections_Ici_zero_of_pos {t : ℝ} (ht : 0 < t) :
    intervalNormalDirections (Ici (0 : ℝ)) t = {0} :=
  intervalNormalDirections_of_not_isGreatest_of_not_isLeast
    (fun hg ↦ absurd (hg.2 (mem_Ici.2 (by linarith : (0 : ℝ) ≤ t + 1)))
      (not_le.2 (by linarith)))
    (fun hl ↦ absurd (hl.2 (mem_Ici.2 (le_refl (0 : ℝ)))) (not_le.2 ht))

/-- The scalar complementarity step.  For `t ≥ 0`, the direction `-s` is
normal to `[0, ∞)` at `t` exactly when `s ≥ 0` and `t s = 0`: at `t = 0` the
normal directions are `(-∞, 0]`, which asks only `s ≥ 0`, while at `t > 0`
they are `{0}`, which forces `s = 0`. -/
theorem neg_mem_intervalNormalDirections_Ici_zero_iff {t s : ℝ} (ht : 0 ≤ t) :
    -s ∈ intervalNormalDirections (Ici (0 : ℝ)) t ↔ 0 ≤ s ∧ t * s = 0 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [intervalNormalDirections_Ici_self]
    simp
  · rw [intervalNormalDirections_Ici_zero_of_pos hpos]
    simp only [mem_singleton_iff, neg_eq_zero]
    refine ⟨fun h ↦ ?_, fun h ↦ (mul_eq_zero.1 h.2).resolve_left hpos.ne'⟩
    subst h
    simp

/-- **Example 6.10** specialized to the orthant: the normal cone to `IRⁿ₊` is
the coordinate product of the scalar normal directions of `[0, ∞)`. -/
theorem normalCone_euclideanNonnegativeOrthant {x : EuclideanSpace ℝ ι}
    (hx : x ∈ (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι))) :
    normalCone (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) x =
      {v | ∀ i, v i ∈ intervalNormalDirections (Ici (0 : ℝ)) (x i)} :=
  normalCone_finiteBox_of_closedIntervals (fun _ ↦ isNonemptyClosedInterval_Ici 0) hx

/-- The Euclidean inner product read off coordinatewise. -/
theorem inner_euclideanSpace_eq_sum (v y : EuclideanSpace ℝ ι) :
    ⟪v, y⟫_ℝ = ∑ i, v i * y i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial]

end OrthantStructure

section Complementarity

variable {ι : Type*} [Fintype ι]

/-- **Example 6.13**, the complementarity condition.  For the nonnegative
orthant the variational condition for an arbitrary mapping `F` is the
coordinatewise system

```text
x̄ⱼ ≥ 0,  F(x̄)ⱼ ≥ 0,  x̄ⱼ F(x̄)ⱼ = 0.
```
-/
theorem isVariationalSolution_nonnegativeOrthant_iff
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {x : EuclideanSpace ℝ ι} :
    IsVariationalSolution euclideanNonnegativeOrthant F x ↔
      ∀ i, 0 ≤ x i ∧ 0 ≤ F x i ∧ x i * F x i = 0 := by
  constructor
  · intro h
    have hx : ∀ i, 0 ≤ x i := mem_euclideanNonnegativeOrthant.1 h.mem
    have hv := h.neg_mem_normalCone
    rw [normalCone_euclideanNonnegativeOrthant h.mem] at hv
    intro i
    have hvi : -F x i ∈ intervalNormalDirections (Ici (0 : ℝ)) (x i) := by
      simpa using hv i
    obtain ⟨h1, h2⟩ := (neg_mem_intervalNormalDirections_Ici_zero_iff (hx i)).1 hvi
    exact ⟨hx i, h1, h2⟩
  · intro h
    have hx : x ∈ (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) :=
      mem_euclideanNonnegativeOrthant.2 fun i ↦ (h i).1
    refine ⟨hx, ?_⟩
    rw [normalCone_euclideanNonnegativeOrthant hx]
    intro i
    have hi : (-F x) i = -F x i := by simp
    rw [hi]
    exact (neg_mem_intervalNormalDirections_Ici_zero_iff (h i).1).2 ⟨(h i).2.1, (h i).2.2⟩

/-- **Example 6.13**, the vectorial summary `0 ≤ x̄ ⟂ F(x̄) ≥ 0`: both vectors
lie in the orthant and are orthogonal.  The reverse direction uses that each
coordinate product is nonnegative, so a vanishing sum forces every term to
vanish; the empty index type and zero coordinates need no separate
treatment. -/
theorem isVariationalSolution_nonnegativeOrthant_iff_inner_eq_zero
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {x : EuclideanSpace ℝ ι} :
    IsVariationalSolution euclideanNonnegativeOrthant F x ↔
      x ∈ (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) ∧
        F x ∈ (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) ∧
        ⟪x, F x⟫_ℝ = 0 := by
  rw [isVariationalSolution_nonnegativeOrthant_iff]
  constructor
  · intro h
    refine ⟨mem_euclideanNonnegativeOrthant.2 fun i ↦ (h i).1,
      mem_euclideanNonnegativeOrthant.2 fun i ↦ (h i).2.1, ?_⟩
    rw [inner_euclideanSpace_eq_sum]
    exact Finset.sum_eq_zero fun i _ ↦ (h i).2.2
  · rintro ⟨hx, hF, hinner⟩
    rw [mem_euclideanNonnegativeOrthant] at hx hF
    rw [inner_euclideanSpace_eq_sum] at hinner
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      fun i _ ↦ mul_nonneg (hx i) (hF i)).1 hinner
    exact fun i ↦ ⟨hx i, hF i, hzero i (Finset.mem_univ i)⟩

/-- The complementarity condition for the identity mapping: the origin is its
only solution. -/
theorem isVariationalSolution_nonnegativeOrthant_id_iff {x : EuclideanSpace ℝ ι} :
    IsVariationalSolution euclideanNonnegativeOrthant (fun y ↦ y) x ↔ x = 0 := by
  rw [isVariationalSolution_nonnegativeOrthant_iff]
  constructor
  · intro h
    ext i
    have hi : x i * x i = 0 := (h i).2.2
    simpa using mul_self_eq_zero.1 hi
  · rintro rfl
    intro i
    simp

end Complementarity

section Consistency

/-! Sanity checks: the degenerate mapping, the degenerate index type, and the
normal cone at the corner of the orthant. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For `F = 0` the variational condition says nothing beyond feasibility,
the zero vector being normal at every point of `C`. -/
example {C : Set E} {x : E} :
    IsVariationalSolution C (fun _ ↦ (0 : E)) x ↔ x ∈ C :=
  ⟨fun h ↦ h.mem, fun hx ↦ ⟨hx, by simpa using (isCone_normalCone hx).1⟩⟩

/-- The empty index type is not excluded: `EuclideanSpace ℝ Empty` is the
zero space, the orthant is all of it, and every point solves every
variational condition. -/
example (F : EuclideanSpace ℝ Empty → EuclideanSpace ℝ Empty)
    (x : EuclideanSpace ℝ Empty) :
    IsVariationalSolution euclideanNonnegativeOrthant F x :=
  isVariationalSolution_nonnegativeOrthant_iff.2 fun i ↦ i.elim

/-- At the corner of the orthant every nonpositive vector is normal; this is
the polar cone of `IRⁿ₊`. -/
example {ι : Type*} [Fintype ι] :
    normalCone (euclideanNonnegativeOrthant : Set (EuclideanSpace ℝ ι)) 0 =
      {v : EuclideanSpace ℝ ι | ∀ i, v i ≤ 0} := by
  rw [normalCone_euclideanNonnegativeOrthant zero_mem_euclideanNonnegativeOrthant]
  ext v
  simp only [mem_setOf_eq]
  refine forall_congr' fun i ↦ ?_
  have h0 : (0 : EuclideanSpace ℝ ι) i = 0 := by simp
  rw [h0, intervalNormalDirections_Ici_self]
  exact mem_Iic

end Consistency

end RW
