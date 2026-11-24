/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2B: Level sets, intersections, polyhedral and affine sets

This file formalizes Section B of Chapter 2 of Rockafellar–Wets for
extended-real-valued functions, with the convexity notion
`IsConvexRelative` of `ConvexFunctions` (inequality 2(3) with inf-addition).

* Proposition 2.7: convexity of the level sets `lev≤α f` and `lev<α f`.
* Example 2.8: affine functions, half-spaces and hyperplanes.
* Proposition 2.9: intersections, pointwise suprema (also strict, for finite
  families) and pointwise upper limits.
* Example 2.10: polyhedral and affine sets, in the book's sense of finite
  intersections of closed half-spaces and hyperplanes, with the equivalent
  linear-constraint description and the comparison with the Chapter 3
  generator definition `IsPolyhedral` (Minkowski–Weyl).
* Exercise 2.11: the four characterizations of nonempty affine sets.
-/

import RockafellarWets.Chapter2.ConvexFunctions
import RockafellarWets.Chapter3.MinkowskiWeyl
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RW

section General

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## Proposition 2.7 -/

/-- **Proposition 2.7**: for a convex `f : E → EReal`, all level sets
`lev≤α f` and `lev<α f` are convex. -/
theorem IsConvexRelative.convex_levelSet_and_strictLevelSet {f : E → EReal}
    (hf : IsConvexRelative univ f) (α : EReal) :
    Convex ℝ (levelSet f α) ∧ Convex ℝ (strictLevelSet f α) :=
  ⟨hf.convex_levelSet α, hf.convex_strictLevelSet α⟩

/-! ## Proposition 2.9 -/

/-- **Proposition 2.9(a)**: an arbitrary intersection of convex sets is
convex. -/
theorem convex_iInter_of_forall_convex {ι : Sort*} {C : ι → Set E}
    (hC : ∀ i, Convex ℝ (C i)) : Convex ℝ (⋂ i, C i) :=
  _root_.convex_iInter hC

omit [AddCommGroup E] [Module ℝ E] in
/-- The epigraph of a pointwise supremum is the intersection of the epigraphs. -/
theorem epigraph_iSup_eq_iInter_epigraph {ι : Sort*} (f : ι → E → EReal) :
    epigraph (fun x ↦ ⨆ i, f i x) = ⋂ i, epigraph (f i) := by
  ext ⟨x, a⟩
  simp [mem_epigraph_iff, iSup_le_iff]

/-- **Proposition 2.9(b)**: the pointwise supremum of an arbitrary family of
convex functions is convex. -/
theorem IsConvexRelative.iSup {ι : Sort*} {f : ι → E → EReal}
    (hf : ∀ i, IsConvexRelative univ (f i)) :
    IsConvexRelative univ (fun x ↦ ⨆ i, f i x) := by
  rw [isConvexRelative_univ_iff, epigraph_iSup_eq_iInter_epigraph]
  exact _root_.convex_iInter fun i ↦ (isConvexRelative_univ_iff _).mp (hf i)

/-- Monotonicity of the right side of 2(3) below `∞`. -/
theorem infAddition_convexCombination_mono {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {a b c d : EReal} (hac : a ≤ c) (hbd : b ≤ d) (hc : c < ⊤) (hd : d < ⊤) :
    infAddition (((1 - τ : ℝ) : EReal) * a) ((τ : EReal) * b) ≤
      infAddition (((1 - τ : ℝ) : EReal) * c) ((τ : EReal) * d) := by
  rw [infAddition_convexCombination_of_lt_top hτ0 hτ1 (hac.trans_lt hc) (hbd.trans_lt hd),
    infAddition_convexCombination_of_lt_top hτ0 hτ1 hc hd]
  exact add_le_add (mul_le_mul_of_nonneg_left hac (EReal.coe_nonneg.mpr (by linarith)))
    (mul_le_mul_of_nonneg_left hbd (EReal.coe_nonneg.mpr hτ0))

/-- The right side of 2(3) is `-∞` when one value is `-∞` and the other is
below `∞`. -/
theorem infAddition_convexCombination_eq_bot {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {a b : EReal} (ha : a < ⊤) (hb : b < ⊤) (hab : a = ⊥ ∨ b = ⊥) :
    infAddition (((1 - τ : ℝ) : EReal) * a) ((τ : EReal) * b) = ⊥ := by
  rw [infAddition_convexCombination_of_lt_top hτ0.le hτ1.le ha hb]
  rcases hab with rfl | rfl
  · rw [EReal.coe_mul_bot_of_pos (by linarith), EReal.bot_add]
  · rw [EReal.coe_mul_bot_of_pos hτ0, EReal.add_bot]

/-- **Proposition 2.9(c)**: the pointwise supremum of a finite family of
strictly convex functions is strictly convex. -/
theorem IsStrictlyConvexRelative.iSup_of_finite {ι : Type*} [Finite ι] {f : ι → E → EReal}
    (hf : ∀ i, IsStrictlyConvexRelative univ (f i)) :
    IsStrictlyConvexRelative univ (fun x ↦ ⨆ i, f i x) := by
  refine ⟨IsConvexRelative.iSup fun i ↦ (hf i).1, ?_⟩
  intro x₀ _ x₁ _ hne h₀t h₀b h₁t h₁b τ hτ0 hτ1
  set F : E → EReal := fun x ↦ ⨆ i, f i x with hF
  lift F x₀ to ℝ using ⟨h₀t, h₀b⟩ with a₀ ha₀
  lift F x₁ to ℝ using ⟨h₁t, h₁b⟩ with a₁ ha₁
  set R := infAddition (((1 - τ : ℝ) : EReal) * (a₀ : EReal)) ((τ : EReal) * (a₁ : EReal))
  have hR : R = (((1 - τ) * a₀ + τ * a₁ : ℝ) : EReal) := by
    simp only [R]
    rw [← EReal.coe_mul, ← EReal.coe_mul,
      infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _), ← EReal.coe_add]
  have hle₀ : ∀ i, f i x₀ ≤ (a₀ : EReal) := fun i ↦ ha₀ ▸ le_iSup (fun j ↦ f j x₀) i
  have hle₁ : ∀ i, f i x₁ ≤ (a₁ : EReal) := fun i ↦ ha₁ ▸ le_iSup (fun j ↦ f j x₁) i
  have hlt : ∀ i, f i ((1 - τ) • x₀ + τ • x₁) < R := by
    intro i
    have ht₀ : f i x₀ < ⊤ := (hle₀ i).trans_lt (EReal.coe_lt_top _)
    have ht₁ : f i x₁ < ⊤ := (hle₁ i).trans_lt (EReal.coe_lt_top _)
    by_cases hbot : f i x₀ = ⊥ ∨ f i x₁ = ⊥
    · have h := (hf i).1 (mem_univ x₀) (mem_univ x₁) hτ0 hτ1
      rw [infAddition_convexCombination_eq_bot hτ0 hτ1 ht₀ ht₁ hbot, le_bot_iff] at h
      rw [h, hR]
      exact EReal.bot_lt_coe _
    · push_neg at hbot
      have h := (hf i).2 (mem_univ x₀) (mem_univ x₁) hne ht₀.ne hbot.1 ht₁.ne hbot.2 hτ0 hτ1
      exact h.trans_le (infAddition_convexCombination_mono hτ0.le hτ1.le (hle₀ i) (hle₁ i)
        (EReal.coe_lt_top _) (EReal.coe_lt_top _))
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [hR]
    change (⨆ i, f i ((1 - τ) • x₀ + τ • x₁)) < _
    rw [iSup_of_empty]
    exact EReal.bot_lt_coe _
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i ↦ f i ((1 - τ) • x₀ + τ • x₁))
    exact (iSup_le hi₀).trans_lt (hlt i₀)

/-- **Proposition 2.9(d)**: a pointwise upper limit of convex functions is
convex. -/
theorem IsConvexRelative.limsup {f : ℕ → E → EReal}
    (hf : ∀ ν, IsConvexRelative univ (f ν)) :
    IsConvexRelative univ (fun x ↦ limsup (fun ν ↦ f ν x) atTop) := by
  rw [isConvexRelative_iff_lt convex_univ]
  intro x₀ _ x₁ _ α₀ α₁ h₀ h₁ τ hτ0 hτ1
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_lt_of_limsup_lt h₀, eventually_lt_of_limsup_lt h₁] with ν hν₀ hν₁
  exact (isConvexRelative_iff_lt convex_univ (f ν)).mp (hf ν) (mem_univ x₀) (mem_univ x₁)
    hν₀ hν₁ hτ0 hτ1

end General

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Example 2.8 -/

/-- **Example 2.8**: an affine function `x ↦ ⟪a, x⟫ + β` is convex. -/
theorem isConvexRelative_affine (a : E) (β : ℝ) :
    IsConvexRelative univ (fun x ↦ ((⟪a, x⟫_ℝ + β : ℝ) : EReal)) := by
  rw [isConvexRelative_coe_iff convex_univ]
  exact ((innerₗ E a).convexOn convex_univ).add (convexOn_const β convex_univ)

/-- **Example 2.8**: an affine function `x ↦ ⟪a, x⟫ + β` is concave. -/
theorem isConcaveRelative_affine (a : E) (β : ℝ) :
    IsConcaveRelative univ (fun x ↦ ((⟪a, x⟫_ℝ + β : ℝ) : EReal)) := by
  have h := isConvexRelative_affine (-a) (-β)
  refine h.congr convex_univ fun x _ ↦ ?_
  rw [inner_neg_left, ← EReal.coe_neg]
  congr 1
  ring

/-- In finite dimensions every function differing from a linear function by a
constant has the form `x ↦ ⟪a, x⟫ + β`. -/
theorem exists_inner_add_eq_of_linear [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] ℝ) (β : ℝ) :
    ∃ a : E, ∀ x, L x + β = ⟪a, x⟫_ℝ + β := by
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap L),
    fun x ↦ ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

/-- **Example 2.8**: the level sets `{⟪a, x⟫ ≤ α}`, `{⟪a, x⟫ ≥ α}`,
`{⟪a, x⟫ < α}`, `{⟪a, x⟫ > α}` and `{⟪a, x⟫ = α}` of an affine function are
convex. -/
theorem convex_inner_levelSets (a : E) (α : ℝ) :
    Convex ℝ {x | ⟪a, x⟫_ℝ ≤ α} ∧ Convex ℝ {x | α ≤ ⟪a, x⟫_ℝ} ∧
      Convex ℝ {x | ⟪a, x⟫_ℝ < α} ∧ Convex ℝ {x | α < ⟪a, x⟫_ℝ} ∧
        Convex ℝ {x | ⟪a, x⟫_ℝ = α} := by
  have hl : IsLinearMap ℝ (fun x : E ↦ ⟪a, x⟫_ℝ) := (innerₗ E a).isLinear
  exact ⟨convex_halfSpace_le hl α, convex_halfSpace_ge hl α, convex_halfSpace_lt hl α,
    convex_halfSpace_gt hl α, convex_hyperplane hl α⟩

/-- A hyperplane `{x | ⟪a, x⟫ = α}` with `a ≠ 0` (Example 2.8). -/
def IsHyperplane (H : Set E) : Prop :=
  ∃ a : E, a ≠ 0 ∧ ∃ α : ℝ, H = {x | ⟪a, x⟫_ℝ = α}

/-- A closed half-space `{x | ⟪a, x⟫ ≤ α}` with `a ≠ 0` (Example 2.8). -/
def IsClosedHalfSpace (H : Set E) : Prop :=
  ∃ a : E, a ≠ 0 ∧ ∃ α : ℝ, H = {x | ⟪a, x⟫_ℝ ≤ α}

/-- An open half-space `{x | ⟪a, x⟫ < α}` with `a ≠ 0` (Example 2.8). -/
def IsOpenHalfSpace (H : Set E) : Prop :=
  ∃ a : E, a ≠ 0 ∧ ∃ α : ℝ, H = {x | ⟪a, x⟫_ℝ < α}

/-- The sets `{⟪a, x⟫ ≥ α}` with `a ≠ 0` are closed half-spaces as well. -/
theorem isClosedHalfSpace_ge {a : E} (ha : a ≠ 0) (α : ℝ) :
    IsClosedHalfSpace {x | α ≤ ⟪a, x⟫_ℝ} :=
  ⟨-a, neg_ne_zero.mpr ha, -α, by ext x; simp [inner_neg_left]⟩

/-- The sets `{⟪a, x⟫ > α}` with `a ≠ 0` are open half-spaces as well. -/
theorem isOpenHalfSpace_gt {a : E} (ha : a ≠ 0) (α : ℝ) :
    IsOpenHalfSpace {x | α < ⟪a, x⟫_ℝ} :=
  ⟨-a, neg_ne_zero.mpr ha, -α, by ext x; simp [inner_neg_left]⟩

theorem IsHyperplane.convex {H : Set E} (hH : IsHyperplane H) : Convex ℝ H := by
  obtain ⟨a, -, α, rfl⟩ := hH
  exact (convex_inner_levelSets a α).2.2.2.2

theorem IsHyperplane.isClosed {H : Set E} (hH : IsHyperplane H) : IsClosed H := by
  obtain ⟨a, -, α, rfl⟩ := hH
  exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

theorem IsClosedHalfSpace.convex {H : Set E} (hH : IsClosedHalfSpace H) : Convex ℝ H := by
  obtain ⟨a, -, α, rfl⟩ := hH
  exact (convex_inner_levelSets a α).1

theorem IsClosedHalfSpace.isClosed {H : Set E} (hH : IsClosedHalfSpace H) : IsClosed H := by
  obtain ⟨a, -, α, rfl⟩ := hH
  exact isClosed_le (continuous_const.inner continuous_id) continuous_const

theorem IsOpenHalfSpace.convex {H : Set E} (hH : IsOpenHalfSpace H) : Convex ℝ H := by
  obtain ⟨a, -, α, rfl⟩ := hH
  exact (convex_inner_levelSets a α).2.2.1

theorem IsOpenHalfSpace.isOpen {H : Set E} (hH : IsOpenHalfSpace H) : IsOpen H := by
  obtain ⟨a, -, α, rfl⟩ := hH
  exact isOpen_lt (continuous_const.inner continuous_id) continuous_const

/-! ## Example 2.10 -/

/-- **Example 2.10**: a polyhedral set is the intersection of a finite family
of closed half-spaces or hyperplanes. -/
def IsPolyhedralSet (C : Set E) : Prop :=
  ∃ S : Set (Set E), S.Finite ∧ (∀ H ∈ S, IsClosedHalfSpace H ∨ IsHyperplane H) ∧ C = ⋂₀ S

/-- **Example 2.10**: an affine set is the intersection of a finite family of
hyperplanes. -/
def IsAffineSet (C : Set E) : Prop :=
  ∃ S : Set (Set E), S.Finite ∧ (∀ H ∈ S, IsHyperplane H) ∧ C = ⋂₀ S

/-- The solution set of finitely many affine constraints `⟪a, x⟫ ≤ α` for
`(a, α) ∈ I` and `⟪b, x⟫ = β` for `(b, β) ∈ J`; degenerate constraints with
zero coefficient vectors are allowed. -/
def affineConstraintSet (I J : Finset (E × ℝ)) : Set E :=
  {x | (∀ p ∈ I, ⟪p.1, x⟫_ℝ ≤ p.2) ∧ ∀ p ∈ J, ⟪p.1, x⟫_ℝ = p.2}

theorem IsAffineSet.isPolyhedralSet {C : Set E} (hC : IsAffineSet C) : IsPolyhedralSet C := by
  obtain ⟨S, hS, hH, rfl⟩ := hC
  exact ⟨S, hS, fun H hHS ↦ Or.inr (hH H hHS), rfl⟩

/-- **Example 2.10**: polyhedral sets are closed. -/
theorem IsPolyhedralSet.isClosed {C : Set E} (hC : IsPolyhedralSet C) : IsClosed C := by
  obtain ⟨S, -, hH, rfl⟩ := hC
  exact isClosed_sInter fun H hHS ↦ (hH H hHS).elim IsClosedHalfSpace.isClosed
    IsHyperplane.isClosed

/-- **Example 2.10**: polyhedral sets are convex. -/
theorem IsPolyhedralSet.convex {C : Set E} (hC : IsPolyhedralSet C) : Convex ℝ C := by
  obtain ⟨S, -, hH, rfl⟩ := hC
  exact convex_sInter fun H hHS ↦ (hH H hHS).elim IsClosedHalfSpace.convex IsHyperplane.convex

/-- **Example 2.10**: the whole space is affine, as the intersection of the
empty family of hyperplanes. -/
theorem isAffineSet_univ : IsAffineSet (univ : Set E) :=
  ⟨∅, finite_empty, by simp, by simp⟩

/-- **Example 2.10**: the empty set is affine, as the intersection of two
parallel hyperplanes.  This needs a nonzero vector, i.e. `n ≥ 1`. -/
theorem isAffineSet_empty [Nontrivial E] : IsAffineSet (∅ : Set E) := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  refine ⟨{{x | ⟪e, x⟫_ℝ = 0}, {x | ⟪e, x⟫_ℝ = 1}}, toFinite _, ?_, ?_⟩
  · rintro H (rfl | rfl)
    · exact ⟨e, he, 0, rfl⟩
    · exact ⟨e, he, 1, rfl⟩
  · ext x
    simp only [mem_empty_iff_false, sInter_insert, sInter_singleton, mem_inter_iff,
      mem_setOf_eq, false_iff, not_and]
    intro h0 h1
    rw [h0] at h1
    exact zero_ne_one h1

theorem IsPolyhedralSet.inter {C D : Set E} (hC : IsPolyhedralSet C) (hD : IsPolyhedralSet D) :
    IsPolyhedralSet (C ∩ D) := by
  obtain ⟨S, hS, hH, rfl⟩ := hC
  obtain ⟨T, hT, hK, rfl⟩ := hD
  refine ⟨S ∪ T, hS.union hT, fun H hHST ↦ hHST.elim (hH H) (hK H), ?_⟩
  rw [sInter_union]

theorem IsAffineSet.inter {C D : Set E} (hC : IsAffineSet C) (hD : IsAffineSet D) :
    IsAffineSet (C ∩ D) := by
  obtain ⟨S, hS, hH, rfl⟩ := hC
  obtain ⟨T, hT, hK, rfl⟩ := hD
  refine ⟨S ∪ T, hS.union hT, fun H hHST ↦ hHST.elim (hH H) (hK H), ?_⟩
  rw [sInter_union]

theorem isPolyhedralSet_univ : IsPolyhedralSet (univ : Set E) :=
  isAffineSet_univ.isPolyhedralSet

theorem isPolyhedralSet_biInter_finset {ι : Type*} (s : Finset ι) {C : ι → Set E}
    (hC : ∀ i ∈ s, IsPolyhedralSet (C i)) : IsPolyhedralSet (⋂ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolyhedralSet_univ
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact (hC i (Finset.mem_insert_self i s)).inter
      (ih fun j hj ↦ hC j (Finset.mem_insert_of_mem hj))

theorem isAffineSet_biInter_finset {ι : Type*} (s : Finset ι) {C : ι → Set E}
    (hC : ∀ i ∈ s, IsAffineSet (C i)) : IsAffineSet (⋂ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isAffineSet_univ
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact (hC i (Finset.mem_insert_self i s)).inter
      (ih fun j hj ↦ hC j (Finset.mem_insert_of_mem hj))

/-- A single affine equation defines an affine set, possibly degenerate. -/
theorem isAffineSet_inner_eq [Nontrivial E] (a : E) (α : ℝ) :
    IsAffineSet {x | ⟪a, x⟫_ℝ = α} := by
  by_cases ha : a = 0
  · subst ha
    by_cases hα : (0 : ℝ) = α
    · simpa [hα] using (isAffineSet_univ (E := E))
    · simpa [hα] using (isAffineSet_empty (E := E))
  · exact ⟨{{x | ⟪a, x⟫_ℝ = α}}, finite_singleton _, by
      simp only [mem_singleton_iff, forall_eq]; exact ⟨a, ha, α, rfl⟩, by simp⟩

/-- A single affine inequality defines a polyhedral set, possibly degenerate. -/
theorem isPolyhedralSet_inner_le [Nontrivial E] (a : E) (α : ℝ) :
    IsPolyhedralSet {x | ⟪a, x⟫_ℝ ≤ α} := by
  by_cases ha : a = 0
  · subst ha
    by_cases hα : (0 : ℝ) ≤ α
    · simpa [hα] using (isPolyhedralSet_univ (E := E))
    · simpa [hα] using (isAffineSet_empty (E := E)).isPolyhedralSet
  · exact ⟨{{x | ⟪a, x⟫_ℝ ≤ α}}, finite_singleton _, by
      simp only [mem_singleton_iff, forall_eq]; exact Or.inl ⟨a, ha, α, rfl⟩, by simp⟩

theorem affineConstraintSet_eq (I J : Finset (E × ℝ)) :
    affineConstraintSet I J =
      (⋂ p ∈ I, {x | ⟪p.1, x⟫_ℝ ≤ p.2}) ∩ ⋂ p ∈ J, {x | ⟪p.1, x⟫_ℝ = p.2} := by
  ext x
  simp [affineConstraintSet]

/-- **Example 2.10**: in the linear-constraint description, a set is polyhedral
if and only if it is the solution set of finitely many affine constraints
`fᵢ(x) ≤ 0` or `fᵢ(x) = 0` (for `n ≥ 1`). -/
theorem isPolyhedralSet_iff_affineConstraintSet [Nontrivial E] {C : Set E} :
    IsPolyhedralSet C ↔ ∃ I J : Finset (E × ℝ), C = affineConstraintSet I J := by
  classical
  constructor
  · rintro ⟨S, hS, hH, rfl⟩
    induction S, hS using Set.Finite.induction_on with
    | empty => exact ⟨∅, ∅, by ext x; simp [affineConstraintSet]⟩
    | @insert H S hHS hS ih =>
      obtain ⟨I, J, hIJ⟩ := ih fun K hK ↦ hH K (mem_insert_of_mem H hK)
      rw [sInter_insert, hIJ]
      rcases hH H (mem_insert H S) with ⟨a, -, α, rfl⟩ | ⟨a, -, α, rfl⟩
      · refine ⟨insert (a, α) I, J, ?_⟩
        ext x
        simp [affineConstraintSet, and_assoc]
      · refine ⟨I, insert (a, α) J, ?_⟩
        ext x
        simp only [affineConstraintSet, mem_inter_iff, mem_setOf_eq, Finset.mem_insert,
          forall_eq_or_imp]
        tauto
  · rintro ⟨I, J, rfl⟩
    rw [affineConstraintSet_eq]
    exact (isPolyhedralSet_biInter_finset I fun p _ ↦ isPolyhedralSet_inner_le p.1 p.2).inter
      (isPolyhedralSet_biInter_finset J fun p _ ↦
        (isAffineSet_inner_eq p.1 p.2).isPolyhedralSet)

/-- **Example 2.10**: a set is affine if and only if it is the solution set of
finitely many affine equations `fᵢ(x) = 0` (for `n ≥ 1`). -/
theorem isAffineSet_iff_affineConstraintSet [Nontrivial E] {C : Set E} :
    IsAffineSet C ↔ ∃ J : Finset (E × ℝ), C = affineConstraintSet ∅ J := by
  classical
  constructor
  · rintro ⟨S, hS, hH, rfl⟩
    induction S, hS using Set.Finite.induction_on with
    | empty => exact ⟨∅, by ext x; simp [affineConstraintSet]⟩
    | @insert H S hHS hS ih =>
      obtain ⟨J, hJ⟩ := ih fun K hK ↦ hH K (mem_insert_of_mem H hK)
      rw [sInter_insert, hJ]
      obtain ⟨a, -, α, rfl⟩ := hH H (mem_insert H S)
      refine ⟨insert (a, α) J, ?_⟩
      ext x
      simp [affineConstraintSet]
  · rintro ⟨J, rfl⟩
    rw [affineConstraintSet_eq]
    simpa using isAffineSet_biInter_finset J fun p _ ↦ isAffineSet_inner_eq p.1 p.2

/-- In finite dimensions, the book's polyhedral sets (finite intersections of
closed half-spaces and hyperplanes) are exactly the Chapter 3 polyhedral sets
`IsPolyhedral`, given by finite generators (Minkowski–Weyl, Theorem 3.52). -/
theorem isPolyhedralSet_iff_isPolyhedral [FiniteDimensional ℝ E] [Nontrivial E] {C : Set E} :
    IsPolyhedralSet C ↔ IsPolyhedral C := by
  classical
  rw [isPolyhedralSet_iff_affineConstraintSet, ← isHPolyhedral_iff_isPolyhedral]
  constructor
  · rintro ⟨I, J, rfl⟩
    rw [affineConstraintSet_eq]
    refine (IsHPolyhedral.iInter_finset I _ fun p _ ↦ ?_).inter
      (IsHPolyhedral.iInter_finset J _ fun p _ ↦ ?_)
    · simpa [innerSL_apply_apply] using IsHPolyhedral.halfspace (innerSL ℝ p.1) p.2
    · have h := (IsHPolyhedral.halfspace (innerSL ℝ p.1) p.2).inter
        (IsHPolyhedral.halfspace (innerSL ℝ (-p.1)) (-p.2))
      convert h using 1
      ext x
      simp only [mem_setOf_eq, mem_inter_iff, innerSL_apply_apply, inner_neg_left, neg_le_neg_iff]
      exact ⟨fun h ↦ ⟨h.le, h.ge⟩, fun h ↦ le_antisymm h.1 h.2⟩
  · rintro ⟨m, A, b, rfl⟩
    refine ⟨Finset.univ.image fun i ↦ ((InnerProductSpace.toDual ℝ E).symm (A i), b i), ∅, ?_⟩
    ext x
    simp [affineConstraintSet, linearInequalitySet, InnerProductSpace.toDual_symm_apply]

/-! ## Exercise 2.11 -/

/-- Characterization 2.11(d): an affine set contains the whole line through any
two of its points. -/
theorem IsAffineSet.combo_mem {C : Set E} (hC : IsAffineSet C) {x₀ x₁ : E} (h₀ : x₀ ∈ C)
    (h₁ : x₁ ∈ C) (τ : ℝ) : (1 - τ) • x₀ + τ • x₁ ∈ C := by
  obtain ⟨S, -, hH, rfl⟩ := hC
  rw [mem_sInter] at h₀ h₁ ⊢
  intro H hHS
  obtain ⟨a, -, α, rfl⟩ := hH H hHS
  have e₀ : ⟪a, x₀⟫_ℝ = α := h₀ _ hHS
  have e₁ : ⟪a, x₁⟫_ℝ = α := h₁ _ hHS
  change ⟪a, (1 - τ) • x₀ + τ • x₁⟫_ℝ = α
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, e₀, e₁]
  ring

/-- A set containing all lines through its points is a translate of a linear
subspace (2.11(d) ⇒ (b)). -/
theorem exists_submodule_of_combo_mem {C : Set E} {p : E} (hp : p ∈ C)
    (hC : ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → ∀ τ : ℝ, (1 - τ) • x₀ + τ • x₁ ∈ C) :
    ∃ M : Submodule ℝ E, C = (fun v ↦ v + p) '' (M : Set E) := by
  let M : Submodule ℝ E :=
    { carrier := {v | v + p ∈ C}
      add_mem' := by
        intro u v hu hv
        have hm := hC hu hv (1 / 2)
        have h := hC hp hm 2
        change (u + v) + p ∈ C
        convert h using 1
        module
      zero_mem' := by
        change (0 : E) + p ∈ C
        simpa using hp
      smul_mem' := by
        intro c v hv
        have h := hC hp hv c
        change c • v + p ∈ C
        convert h using 1
        module }
  refine ⟨M, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨x - p, ?_, by simp⟩
    change x - p + p ∈ C
    simpa using hx
  · rintro ⟨v, hv, rfl⟩
    exact hv

/-- A translate of a linear subspace is the solution set of a linear system
`Ax = b` (2.11(b) ⇒ (c)). -/
theorem exists_linearMap_eq_of_submodule [FiniteDimensional ℝ E] (M : Submodule ℝ E) (p : E) :
    ∃ (m : ℕ) (A : E →ₗ[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ),
      (fun v ↦ v + p) '' (M : Set E) = {x | A x = b} := by
  let B := Module.finBasis ℝ (E ⧸ M)
  let A : E →ₗ[ℝ] (Fin (Module.finrank ℝ (E ⧸ M)) → ℝ) := B.equivFun.toLinearMap ∘ₗ M.mkQ
  have hA : ∀ y, A y = 0 ↔ y ∈ M := by
    intro y
    constructor
    · intro h
      have h' : B.equivFun (M.mkQ y) = B.equivFun 0 := by rw [map_zero]; exact h
      have := B.equivFun.injective h'
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    · intro h
      change B.equivFun (M.mkQ y) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero M).mpr h, map_zero]
  refine ⟨_, A, A p, ?_⟩
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change A (v + p) = A p
    rw [map_add, (hA v).mpr hv, zero_add]
  · intro hx
    have hker : x - p ∈ M := by
      rw [← hA, map_sub]
      exact sub_eq_zero.mpr hx
    exact ⟨x - p, hker, by simp⟩

/-- A nonempty solution set of a linear system is an affine set
(2.11(c) ⇒ (a)). -/
theorem isAffineSet_of_linearMap_eq [FiniteDimensional ℝ E] {m : ℕ} (A : E →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (hne : {x | A x = b}.Nonempty) : IsAffineSet {x | A x = b} := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : {x | A x = b} = univ := by
      obtain ⟨y, hy⟩ := hne
      ext x
      simp only [mem_univ, iff_true]
      rw [Subsingleton.elim x y]
      exact hy
    rw [this]
    exact isAffineSet_univ
  · rw [isAffineSet_iff_affineConstraintSet]
    let a : Fin m → E := fun i ↦ (InnerProductSpace.toDual ℝ E).symm
      (LinearMap.toContinuousLinearMap ((LinearMap.proj i).comp A))
    have ha : ∀ i x, ⟪a i, x⟫_ℝ = A x i := by
      intro i x
      simp only [a, InnerProductSpace.toDual_symm_apply]
      rfl
    refine ⟨Finset.univ.image fun i ↦ (a i, b i), ?_⟩
    ext x
    simp only [mem_setOf_eq, affineConstraintSet, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, ha]
    exact funext_iff

/-- **Exercise 2.11 (characterization of affine sets)**: for a nonempty set `C`
in a finite-dimensional space the following are equivalent: (a) `C` is affine;
(b) `C` is a translate `M + p` of a linear subspace `M`; (c) `C = {x | Ax = b}`
for a linear map `A` into some `ℝᵐ` and `b ∈ ℝᵐ`; (d) `C` contains the entire
line through any two of its points. -/
theorem isAffineSet_tfae [FiniteDimensional ℝ E] {C : Set E} (hC : C.Nonempty) :
    List.TFAE [IsAffineSet C,
      ∃ (M : Submodule ℝ E) (p : E), C = (fun v ↦ v + p) '' (M : Set E),
      ∃ (m : ℕ) (A : E →ₗ[ℝ] (Fin m → ℝ)) (b : Fin m → ℝ), C = {x | A x = b},
      ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → ∀ τ : ℝ, (1 - τ) • x₀ + τ • x₁ ∈ C] := by
  tfae_have 1 → 4 := fun h x₀ h₀ x₁ h₁ τ ↦ h.combo_mem h₀ h₁ τ
  tfae_have 4 → 2 := by
    intro h
    obtain ⟨p, hp⟩ := hC
    obtain ⟨M, hM⟩ := exists_submodule_of_combo_mem hp h
    exact ⟨M, p, hM⟩
  tfae_have 2 → 3 := by
    rintro ⟨M, p, rfl⟩
    obtain ⟨m, A, b, h⟩ := exists_linearMap_eq_of_submodule M p
    exact ⟨m, A, b, h⟩
  tfae_have 3 → 1 := by
    rintro ⟨m, A, b, rfl⟩
    exact isAffineSet_of_linearMap_eq A b hC
  tfae_finish

end InnerProduct

end RW
