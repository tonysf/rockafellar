/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2G: Separation of convex sets

This file formalizes the separation concepts of Section G of Chapter 2 of
Rockafellar–Wets and Theorem 2.39 in a finite-dimensional Euclidean space.

A hyperplane `{x | ⟪a, x⟫ = α}` (`a ≠ 0`) separates `C₁` and `C₂` when they lie
in the two opposite closed half-spaces; the separation is proper when the
hyperplane does not contain both sets; strong separation uses half-spaces
`⟪a, x⟫ ≤ α₁` and `⟪a, x⟫ ≥ α₂` with `α₁ < α₂`.  The Chapter 4 predicate
`CannotBeSeparated A B := 0 ∈ int(A - B)` is the negation of `CanBeSeparated`
for nonempty convex sets (`canBeSeparated_iff`).
-/

import RockafellarWets.Chapter2.LevelSetsAffine
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

open Set Filter Topology
open scoped InnerProductSpace Pointwise

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The hyperplane `{x | ⟪a, x⟫ = α}` with `a ≠ 0` separates `C₁` and `C₂`. -/
def HyperplaneSeparates (a : E) (α : ℝ) (C₁ C₂ : Set E) : Prop :=
  a ≠ 0 ∧ (((∀ x ∈ C₁, ⟪a, x⟫_ℝ ≤ α) ∧ ∀ x ∈ C₂, α ≤ ⟪a, x⟫_ℝ) ∨
    ((∀ x ∈ C₂, ⟪a, x⟫_ℝ ≤ α) ∧ ∀ x ∈ C₁, α ≤ ⟪a, x⟫_ℝ))

/-- Proper separation: the separating hyperplane does not contain both sets. -/
def HyperplaneSeparatesProperly (a : E) (α : ℝ) (C₁ C₂ : Set E) : Prop :=
  HyperplaneSeparates a α C₁ C₂ ∧ ¬(C₁ ⊆ {x | ⟪a, x⟫_ℝ = α} ∧ C₂ ⊆ {x | ⟪a, x⟫_ℝ = α})

/-- `C₁` and `C₂` can be separated by a hyperplane. -/
def CanBeSeparated (C₁ C₂ : Set E) : Prop :=
  ∃ a α, HyperplaneSeparates a α C₁ C₂

/-- `C₁` and `C₂` can be separated properly. -/
def CanBeSeparatedProperly (C₁ C₂ : Set E) : Prop :=
  ∃ a α, HyperplaneSeparatesProperly a α C₁ C₂

/-- Strong separation: `C₁ ⊆ {⟪a, x⟫ ≤ α₁}` and `C₂ ⊆ {⟪a, x⟫ ≥ α₂}` with
`α₁ < α₂` (or with the roles of the sets exchanged). -/
def CanBeStronglySeparated (C₁ C₂ : Set E) : Prop :=
  ∃ (a : E) (α₁ α₂ : ℝ), a ≠ 0 ∧ α₁ < α₂ ∧
    (((∀ x ∈ C₁, ⟪a, x⟫_ℝ ≤ α₁) ∧ ∀ x ∈ C₂, α₂ ≤ ⟪a, x⟫_ℝ) ∨
      ((∀ x ∈ C₂, ⟪a, x⟫_ℝ ≤ α₁) ∧ ∀ x ∈ C₁, α₂ ≤ ⟪a, x⟫_ℝ))

/-- A nonzero `a` with `⟪a, ·⟫ ≤ 0` on a convex set `D` with `0 ∉ int D`. -/
theorem exists_inner_nonpos_of_zero_not_mem_interior {D : Set E} (hD : Convex ℝ D)
    (hne : D.Nonempty) (h0 : (0 : E) ∉ interior D) : ∃ a : E, a ≠ 0 ∧ ∀ x ∈ D, ⟪a, x⟫_ℝ ≤ 0 := by
  by_cases hint : (interior D).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hD.interior isOpen_interior h0
    have hfD : ∀ x ∈ D, f x ≤ 0 := by
      intro x hx
      have hcl : x ∈ closure (interior D) := by
        rw [hD.closure_interior_eq_closure_of_nonempty_interior hint]
        exact subset_closure hx
      have hle : ∀ y ∈ interior D, f y ≤ 0 := fun y hy ↦ by
        have := hf y hy
        rw [map_zero] at this
        exact this.le
      exact (isClosed_le f.continuous continuous_const).closure_subset_iff.mpr hle hcl
    refine ⟨(InnerProductSpace.toDual ℝ E).symm f, ?_, fun x hx ↦ ?_⟩
    · intro h0'
      obtain ⟨y, hy⟩ := hint
      have := hf y hy
      rw [(InnerProductSpace.toDual ℝ E).symm_apply_eq.mp h0', map_zero] at this
      simp at this
    · rw [InnerProductSpace.toDual_symm_apply]
      exact hfD x hx
  · have hspan : affineSpan ℝ D ≠ ⊤ := fun h ↦
      hint ((hD.interior_nonempty_iff_affineSpan_eq_top).mpr h)
    obtain ⟨p, hp⟩ := hne
    have hdir : (affineSpan ℝ D).direction ≠ ⊤ := fun h ↦
      hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ⟨p, subset_affineSpan ℝ D hp⟩).mp h)
    have hperp : (affineSpan ℝ D).directionᗮ ≠ ⊥ := fun h ↦
      hdir (Submodule.orthogonal_eq_bot_iff.mp h)
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
    have hconst : ∀ x ∈ D, ⟪b, x⟫_ℝ = ⟪b, p⟫_ℝ := by
      intro x hx
      have hmem : x - p ∈ (affineSpan ℝ D).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ D hx) (subset_affineSpan ℝ D hp)
      have := (Submodule.mem_orthogonal' _ b).mp hb (x - p) hmem
      rw [inner_sub_right] at this
      linarith
    by_cases hsign : ⟪b, p⟫_ℝ ≤ 0
    · exact ⟨b, hb0, fun x hx ↦ (hconst x hx).trans_le hsign⟩
    · refine ⟨-b, neg_ne_zero.mpr hb0, fun x hx ↦ ?_⟩
      rw [inner_neg_left, hconst x hx]
      linarith

omit [FiniteDimensional ℝ E] in
/-- Separation from a nonpositive functional on `C₁ - C₂`. -/
theorem hyperplaneSeparates_of_inner_nonpos {C₁ C₂ : Set E} (hne₁ : C₁.Nonempty)
    (hne₂ : C₂.Nonempty) {a : E} (ha : a ≠ 0) (h : ∀ x ∈ C₁ - C₂, ⟪a, x⟫_ℝ ≤ 0) :
    ∃ α, HyperplaneSeparates a α C₁ C₂ := by
  have h' : ∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, ⟪a, x₁⟫_ℝ ≤ ⟪a, x₂⟫_ℝ := by
    intro x₁ h₁ x₂ h₂
    have := h (x₁ - x₂) (sub_mem_sub h₁ h₂)
    rw [inner_sub_right] at this
    linarith
  obtain ⟨y₂, hy₂⟩ := hne₂
  have hbdd : BddAbove ((fun x ↦ ⟪a, x⟫_ℝ) '' C₁) :=
    ⟨⟪a, y₂⟫_ℝ, by rintro _ ⟨x, hx, rfl⟩; exact h' x hx y₂ hy₂⟩
  refine ⟨sSup ((fun x ↦ ⟪a, x⟫_ℝ) '' C₁), ha, Or.inl ⟨fun x hx ↦ le_csSup hbdd ⟨x, hx, rfl⟩,
    fun x hx ↦ csSup_le (hne₁.image _) ?_⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact h' y hy x hx

omit [FiniteDimensional ℝ E] in
theorem inner_sub_nonpos_of_hyperplaneSeparates {C₁ C₂ : Set E} {a : E} {α : ℝ}
    (h : HyperplaneSeparates a α C₁ C₂) :
    ∃ b : E, b ≠ 0 ∧ (b = a ∨ b = -a) ∧ ∀ x ∈ C₁ - C₂, ⟪b, x⟫_ℝ ≤ 0 := by
  obtain ⟨ha, (⟨h₁, h₂⟩ | ⟨h₂, h₁⟩)⟩ := h
  · refine ⟨a, ha, Or.inl rfl, ?_⟩
    rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    rw [inner_sub_right]
    linarith [h₁ x₁ hx₁, h₂ x₂ hx₂]
  · refine ⟨-a, neg_ne_zero.mpr ha, Or.inr rfl, ?_⟩
    rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    rw [inner_neg_left, inner_sub_right]
    linarith [h₁ x₁ hx₁, h₂ x₂ hx₂]

omit [FiniteDimensional ℝ E] in
/-- A set on which a nonzero linear functional is `≤ 0` has `0` outside its
interior. -/
theorem zero_not_mem_interior_of_inner_nonpos {D : Set E} {b : E} (hb : b ≠ 0)
    (h : ∀ x ∈ D, ⟪b, x⟫_ℝ ≤ 0) : (0 : E) ∉ interior D := by
  intro h0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  have hpos : 0 < ε / (2 * ‖b‖) := div_pos hε (by positivity)
  have hmem : (ε / (2 * ‖b‖)) • b ∈ D := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hpos.le]
    have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
    calc ε / (2 * ‖b‖) * ‖b‖ = ε / 2 := by field_simp
      _ < ε := by linarith
  have := h _ hmem
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at this
  have hb2 : 0 < ‖b‖ ^ 2 := by positivity
  nlinarith

/-- **Theorem 2.39**: two nonempty convex sets can be separated by a hyperplane
if and only if `0 ∉ int(C₁ - C₂)`. -/
theorem canBeSeparated_iff {C₁ C₂ : Set E} (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    CanBeSeparated C₁ C₂ ↔ (0 : E) ∉ interior (C₁ - C₂) := by
  constructor
  · rintro ⟨a, α, h⟩
    obtain ⟨b, hb, -, hbD⟩ := inner_sub_nonpos_of_hyperplaneSeparates h
    exact zero_not_mem_interior_of_inner_nonpos hb hbD
  · intro h0
    obtain ⟨a, ha, haD⟩ :=
      exists_inner_nonpos_of_zero_not_mem_interior (hC₁.sub hC₂) (hne₁.sub hne₂) h0
    obtain ⟨α, hα⟩ := hyperplaneSeparates_of_inner_nonpos hne₁ hne₂ ha haD
    exact ⟨a, α, hα⟩

omit [FiniteDimensional ℝ E] in
/-- A hyperplane through the origin has empty interior. -/
theorem interior_inner_eq_zero_eq_empty {a : E} (ha : a ≠ 0) :
    interior {x : E | ⟪a, x⟫_ℝ = 0} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  have hzmem : z ∈ {x : E | ⟪a, x⟫_ℝ = 0} := interior_subset hz
  have hz0 : ⟪a, z⟫_ℝ = 0 := hzmem
  have hpos : 0 < ε / (2 * ‖a‖) := div_pos hε (by positivity)
  have hmem : z + (ε / (2 * ‖a‖)) • a ∈ {x : E | ⟪a, x⟫_ℝ = 0} := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hpos.le]
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    calc ε / (2 * ‖a‖) * ‖a‖ = ε / 2 := by field_simp
      _ < ε := by linarith
  have := hmem
  simp only [mem_setOf_eq, inner_add_right, hz0, zero_add, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at this
  have ha2 : 0 < ‖a‖ ^ 2 := by positivity
  have := mul_pos hpos ha2
  linarith

omit [FiniteDimensional ℝ E] in
/-- **Theorem 2.39**: when `int(C₁ - C₂) ≠ ∅`, every separating hyperplane
separates properly. -/
theorem HyperplaneSeparates.properly_of_interior_nonempty {C₁ C₂ : Set E} {a : E} {α : ℝ}
    (h : HyperplaneSeparates a α C₁ C₂) (hint : (interior (C₁ - C₂)).Nonempty) :
    HyperplaneSeparatesProperly a α C₁ C₂ := by
  refine ⟨h, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  have hD : C₁ - C₂ ⊆ {x | ⟪a, x⟫_ℝ = 0} := by
    rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    have e₁ : ⟪a, x₁⟫_ℝ = α := h₁ hx₁
    have e₂ : ⟪a, x₂⟫_ℝ = α := h₂ hx₂
    change ⟪a, x₁ - x₂⟫_ℝ = 0
    rw [inner_sub_right, e₁, e₂, sub_self]
  obtain ⟨z, hz⟩ := hint
  have := interior_mono hD hz
  rw [interior_inner_eq_zero_eq_empty h.1] at this
  exact this

omit [FiniteDimensional ℝ E] in
/-- **Theorem 2.39**: if `int C₁ ≠ ∅` and `C₂ ∩ int C₁ = ∅`, then
`0 ∉ int(C₁ - C₂)` and `int(C₁ - C₂) ≠ ∅`. -/
theorem zero_not_mem_interior_sub_of_disjoint_interior {C₁ C₂ : Set E} (hC₁ : Convex ℝ C₁)
    (hC₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) (hint : (interior C₁).Nonempty)
    (hdisj : Disjoint C₂ (interior C₁)) :
    (0 : E) ∉ interior (C₁ - C₂) ∧ (interior (C₁ - C₂)).Nonempty := by
  have hU : IsOpen (interior C₁ - C₂) := isOpen_interior.sub_right
  have hUc : Convex ℝ (interior C₁ - C₂) := hC₁.interior.sub hC₂
  have hUsub : interior C₁ - C₂ ⊆ C₁ - C₂ := sub_subset_sub_right interior_subset
  have hUne : (interior C₁ - C₂).Nonempty := hint.sub hne₂
  have hsubcl : C₁ - C₂ ⊆ closure (interior C₁ - C₂) := by
    rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    have hx₁' : x₁ ∈ closure (interior C₁) := by
      rw [hC₁.closure_interior_eq_closure_of_nonempty_interior hint]
      exact subset_closure hx₁
    have hcont : Continuous (fun y : E ↦ y - x₂) := by fun_prop
    have hmaps : MapsTo (fun y : E ↦ y - x₂) (interior C₁) (interior C₁ - C₂) :=
      fun y hy ↦ ⟨y, hy, x₂, hx₂, rfl⟩
    have hmem := map_mem_closure hcont hx₁' hmaps
    exact hmem
  have hint_eq : interior (C₁ - C₂) = interior C₁ - C₂ := by
    apply Subset.antisymm
    · calc interior (C₁ - C₂) ⊆ interior (closure (interior C₁ - C₂)) := interior_mono hsubcl
        _ = interior C₁ - C₂ := by
            rw [hUc.interior_closure_eq_interior_of_nonempty_interior
              (by rwa [hU.interior_eq]), hU.interior_eq]
    · exact interior_maximal hUsub hU
  refine ⟨?_, hint_eq ▸ hUne⟩
  rw [hint_eq]
  rintro ⟨x₁, hx₁, x₂, hx₂, h0⟩
  rw [sub_eq_zero] at h0
  subst h0
  exact Set.disjoint_left.mp hdisj hx₂ hx₁

omit [FiniteDimensional ℝ E] in
/-- **Theorem 2.39**: the symmetric condition, `int C₂ ≠ ∅` and `C₁ ∩ int C₂ = ∅`. -/
theorem zero_not_mem_interior_sub_of_disjoint_interior' {C₁ C₂ : Set E} (hC₁ : Convex ℝ C₁)
    (hC₂ : Convex ℝ C₂) (hne₁ : C₁.Nonempty) (hint : (interior C₂).Nonempty)
    (hdisj : Disjoint C₁ (interior C₂)) :
    (0 : E) ∉ interior (C₁ - C₂) ∧ (interior (C₁ - C₂)).Nonempty := by
  obtain ⟨h0, hne⟩ := zero_not_mem_interior_sub_of_disjoint_interior hC₂ hC₁ hne₁ hint hdisj
  have hneg : C₁ - C₂ = -(C₂ - C₁) := by rw [neg_sub]
  have hint' : interior (C₁ - C₂) = -interior (C₂ - C₁) := by
    rw [hneg]
    exact ((Homeomorph.neg E).preimage_interior (C₂ - C₁)).symm
  rw [hint']
  refine ⟨fun h ↦ h0 (by simpa using h), ?_⟩
  obtain ⟨y, hy⟩ := hne
  exact ⟨-y, by simpa using hy⟩

/-- **Theorem 2.39**: strong separation is possible if and only if
`0 ∉ cl(C₁ - C₂)`. -/
theorem canBeStronglySeparated_iff {C₁ C₂ : Set E} (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    CanBeStronglySeparated C₁ C₂ ↔ (0 : E) ∉ closure (C₁ - C₂) := by
  constructor
  · rintro ⟨a, α₁, α₂, ha, hlt, h⟩
    obtain ⟨b, γ, hγ, hbD⟩ : ∃ (b : E) (γ : ℝ), γ < 0 ∧ ∀ x ∈ C₁ - C₂, ⟪b, x⟫_ℝ ≤ γ := by
      rcases h with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
      · refine ⟨a, α₁ - α₂, by linarith, ?_⟩
        rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
        rw [inner_sub_right]
        linarith [h₁ x₁ hx₁, h₂ x₂ hx₂]
      · refine ⟨-a, α₁ - α₂, by linarith, ?_⟩
        rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
        rw [inner_neg_left, inner_sub_right]
        linarith [h₁ x₁ hx₁, h₂ x₂ hx₂]
    intro h0
    have hcl : closure (C₁ - C₂) ⊆ {x | ⟪b, x⟫_ℝ ≤ γ} :=
      closure_minimal hbD (isClosed_le (continuous_const.inner continuous_id) continuous_const)
    have := hcl h0
    simp only [mem_setOf_eq, inner_zero_right] at this
    linarith
  · intro h0
    obtain ⟨f, u, hfD, hu⟩ := geometric_hahn_banach_closed_point (hC₁.sub hC₂).closure
      isClosed_closure h0
    rw [map_zero] at hu
    set a := (InnerProductSpace.toDual ℝ E).symm f
    have ha : ∀ x, ⟪a, x⟫_ℝ = f x := fun x ↦ InnerProductSpace.toDual_symm_apply
    have hgap : ∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, ⟪a, x₁⟫_ℝ < ⟪a, x₂⟫_ℝ + u := by
      intro x₁ hx₁ x₂ hx₂
      have := hfD (x₁ - x₂) (subset_closure (sub_mem_sub hx₁ hx₂))
      rw [← ha, inner_sub_right] at this
      linarith
    obtain ⟨y₂, hy₂⟩ := hne₂
    have hbdd : BddAbove ((fun x ↦ ⟪a, x⟫_ℝ) '' C₁) :=
      ⟨⟪a, y₂⟫_ℝ + u, by rintro _ ⟨x, hx, rfl⟩; exact (hgap x hx y₂ hy₂).le⟩
    set α₁ := sSup ((fun x ↦ ⟪a, x⟫_ℝ) '' C₁)
    have ha0 : a ≠ 0 := by
      intro ha0
      obtain ⟨x₁, hx₁⟩ := hne₁
      have := hgap x₁ hx₁ y₂ hy₂
      rw [ha0, inner_zero_left, inner_zero_left] at this
      linarith
    refine ⟨a, α₁, α₁ - u, ha0, by linarith, Or.inl ⟨fun x hx ↦ le_csSup hbdd ⟨x, hx, rfl⟩,
      fun x hx ↦ ?_⟩⟩
    have : α₁ ≤ ⟪a, x⟫_ℝ + u := csSup_le (hne₁.image _) (by
      rintro _ ⟨y, hy, rfl⟩
      exact (hgap y hy x hx).le)
    linarith

/-- **Theorem 2.39**: disjoint closed convex sets, one of them bounded, can be
strongly separated. -/
theorem canBeStronglySeparated_of_disjoint {C₁ C₂ : Set E} (hC₁ : Convex ℝ C₁)
    (hC₂ : Convex ℝ C₂) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) (hcl₁ : IsClosed C₁)
    (hcl₂ : IsClosed C₂) (hb : Bornology.IsBounded C₁ ∨ Bornology.IsBounded C₂)
    (hdisj : Disjoint C₁ C₂) : CanBeStronglySeparated C₁ C₂ := by
  rw [canBeStronglySeparated_iff hC₁ hC₂ hne₁ hne₂]
  have hclosed : IsClosed (C₁ - C₂) := by
    rw [sub_eq_add_neg]
    rcases hb with hb | hb
    · exact hcl₂.neg.add_left_of_isCompact (Metric.isCompact_of_isClosed_isBounded hcl₁ hb)
    · exact hcl₁.add_right_of_isCompact (Metric.isCompact_of_isClosed_isBounded hcl₂ hb).neg
  rw [hclosed.closure_eq]
  rintro ⟨x₁, hx₁, x₂, hx₂, h0⟩
  rw [sub_eq_zero] at h0
  subst h0
  exact Set.disjoint_left.mp hdisj hx₁ hx₂

end RW
