/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Interior tests in terms of support functions
-/

import RockafellarWets.Chapter8.SupportFunctions
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem inner_lt_support_of_mem_interior {C : Set E} {x : E} (hx : x ∈ interior C)
    {v : E} (hv : v ≠ 0) : (⟪x,v⟫_ℝ : EReal) < supportFunction C v := by
  have hs : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝[>] 0) (𝓝 x) := by
    simpa using ((continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ) :
      Tendsto (fun t : ℝ ↦ x+t • v) _ _).mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,htC⟩ := (hpos.and (hs.eventually (mem_interior_iff_mem_nhds.1 hx))).exists
  apply lt_of_lt_of_le _ (inner_le_supportFunction htC v)
  rw [EReal.coe_lt_coe_iff, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact lt_add_of_pos_right _ (mul_pos ht (sq_pos_of_pos (norm_pos_iff.2 hv)))

private theorem supportFunction_eq_of_constant_inner {C : Set E} (hne : C.Nonempty) {v : E} {c : ℝ}
    (h : ∀ x ∈ C, ⟪x,v⟫_ℝ = c) : supportFunction C v = (c : EReal) := by
  obtain ⟨x,hx⟩ := hne
  exact le_antisymm ((supportFunction_le_iff _ _ _).2 (fun y hy ↦ by rw [h y hy]))
    (by simpa [h x hx] using inner_le_supportFunction hx v)

variable [FiniteDimensional ℝ E]

private theorem exists_constant_inner_of_empty_interior {C : Set E} (hc : Convex ℝ C) (hne : C.Nonempty)
    (hint : ¬(interior C).Nonempty) : ∃ v : E, v ≠ 0 ∧ ∃ c : ℝ, ∀ x ∈ C, ⟪x,v⟫_ℝ = c := by
  let A := affineSpan ℝ C
  have hA : A ≠ ⊤ := fun h ↦ hint (hc.interior_nonempty_iff_affineSpan_eq_top.mpr h)
  obtain ⟨x,hx⟩ := hne
  have hxA : x ∈ A := subset_affineSpan ℝ C hx
  have hK : A.direction ≠ ⊤ := fun h ↦ hA ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x,hxA⟩).mp h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ hK (Submodule.orthogonal_eq_bot_iff.mp h))
  refine ⟨v,hv0,⟪x,v⟫_ℝ, fun y hy ↦ ?_⟩
  have hsub : y-x ∈ A.direction := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hy) hxA
  exact sub_eq_zero.1 (by simpa [inner_sub_left] using Submodule.inner_right_of_mem_orthogonal hsub hv)

/-- **Proposition 8.29(a).** A nonempty convex set has interior exactly when
no nonzero direction has zero width. The nonemptiness assumption accounts
for the value `⊥` of the support function of the empty set. -/
theorem interior_nonempty_iff_supportFunction_ne_neg {C : Set E} (hc : Convex ℝ C) (hne : C.Nonempty) :
    (interior C).Nonempty ↔ ∀ v : E, v ≠ 0 → supportFunction C v ≠ -supportFunction C (-v) := by
  constructor
  · rintro ⟨x,hx⟩ v hv heq
    have h₁ := inner_lt_support_of_mem_interior hx hv
    have h₂ := inner_lt_support_of_mem_interior hx (neg_ne_zero.2 hv)
    rw [inner_neg_right, EReal.coe_neg] at h₂
    rw [heq] at h₁
    exact h₁.not_ge (by simpa only [neg_neg] using EReal.neg_le_neg_iff.2 h₂.le)
  · intro h
    by_contra hn
    obtain ⟨v,hv,c,he⟩ := exists_constant_inner_of_empty_interior hc hne hn
    apply h v hv
    rw [supportFunction_eq_of_constant_inner hne he, supportFunction_eq_of_constant_inner (c := -c) hne
      (fun x hx ↦ by simp [inner_neg_right, he x hx])]
    simp

omit [FiniteDimensional ℝ E] in
/-- The empty set violates the unrestricted zero-width test in 8.29(a). -/
theorem empty_supportFunction_interior_obstruction :
    ¬(interior (∅ : Set E)).Nonempty ∧ ∀ v : E, v ≠ 0 →
      supportFunction (∅ : Set E) v ≠ -supportFunction (∅ : Set E) (-v) := by simp

/-- The pointwise interior test in 8.29(a), on every nonempty convex set. -/
theorem mem_interior_iff_inner_lt_supportFunction {C : Set E} (hc : Convex ℝ C)
    (hne : C.Nonempty) (x : E) :
    x ∈ interior C ↔ ∀ v : E, v ≠ 0 → (⟪x,v⟫_ℝ : EReal) < supportFunction C v := by
  refine ⟨fun hx _ hv ↦ inner_lt_support_of_mem_interior hx hv, fun h ↦ ?_⟩
  letI := FiniteDimensional.complete ℝ E
  have hi : (interior C).Nonempty := by
    by_contra hn
    obtain ⟨v,hv,c,he⟩ := exists_constant_inner_of_empty_interior hc hne hn
    have h₁ := h v hv
    have h₂ := h (-v) (neg_ne_zero.2 hv)
    rw [supportFunction_eq_of_constant_inner hne he, EReal.coe_lt_coe_iff] at h₁
    rw [supportFunction_eq_of_constant_inner (c := -c) hne (fun y hy ↦ by simp [inner_neg_right, he y hy]),
      inner_neg_right, EReal.coe_lt_coe_iff] at h₂
    linarith
  by_contra hx
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point hc.interior isOpen_interior hx
  let v := (InnerProductSpace.toDual ℝ E).symm f
  have hfv (y : E) : ⟪y,v⟫_ℝ = f y := by rw [real_inner_comm]; simp [v]
  have hv : v ≠ 0 := by
    intro he
    obtain ⟨p,hp⟩ := hi
    have := hf p hp
    rw [← hfv p, ← hfv x, he] at this
    simp at this
  have hbound : supportFunction C v ≤ (⟪x,v⟫_ℝ : EReal) := by
    apply (supportFunction_le_iff _ _ _).2
    intro y hy
    rw [EReal.coe_le_coe_iff, hfv, hfv]
    have hycl : y ∈ closure (interior C) := by rw [hc.closure_interior_eq_closure_of_nonempty_interior hi]; exact subset_closure hy
    exact closure_minimal (fun z hz ↦ (hf z hz).le) (isClosed_le f.continuous continuous_const) hycl
  exact (h v hv).not_ge hbound

omit [FiniteDimensional ℝ E] in
private theorem supportFunction_sub_nonpos_iff (C D : Set E) (v : E) :
    supportFunction (C-D) v ≤ 0 ↔ supportFunction C v ≤ -supportFunction D (-v) := by
  rw [supportFunction_le_iff, supportFunction_le_iff]
  constructor
  · intro h x hx
    rw [EReal.le_neg, supportFunction_le_iff]
    intro y hy
    have hval := h (x-y) (sub_mem_sub hx hy)
    simpa [inner_sub_left, inner_neg_right, ← EReal.coe_neg, sub_nonpos] using
      (show ⟪x-y,v⟫_ℝ ≤ 0 from EReal.coe_le_coe_iff.1 hval)
  · rintro h _ ⟨x,hx,y,hy,rfl⟩
    have hval := ((supportFunction_le_iff _ _ _).1 (EReal.le_neg.1 (h x hx))) y hy
    change (⟪x-y,v⟫_ℝ : EReal) ≤ ((0:ℝ) : EReal)
    apply EReal.coe_le_coe_iff.2
    simpa [inner_sub_left, inner_neg_right, ← EReal.coe_neg, sub_nonpos] using hval

/-- In positive dimension the strict support inequalities also test membership
for the empty convex set. -/
theorem mem_interior_iff_inner_lt_supportFunction_of_nontrivial [Nontrivial E] {C : Set E}
    (hc : Convex ℝ C) (x : E) :
    x ∈ interior C ↔ ∀ v : E, v ≠ 0 → (⟪x,v⟫_ℝ : EReal) < supportFunction C v := by
  rcases C.eq_empty_or_nonempty with rfl | hn
  · obtain ⟨v,hv⟩ := exists_ne (0 : E)
    constructor
    · simp
    · intro h
      exact ((not_lt_bot) (by simpa only [supportFunction_empty] using h v hv)).elim
  · exact mem_interior_iff_inner_lt_supportFunction hc hn x

/-- **Proposition 8.29(b).** Interior overlap of a difference of two nonempty
convex sets is characterized by their support functions. -/
theorem zero_mem_interior_sub_iff_supportFunction {C D : Set E} (hc : Convex ℝ C) (hd : Convex ℝ D)
    (hC : C.Nonempty) (hD : D.Nonempty) :
    (0 : E) ∈ interior (C-D) ↔ ∀ v : E, v ≠ 0 → ¬supportFunction C v ≤ -supportFunction D (-v) := by
  rw [mem_interior_iff_inner_lt_supportFunction (hc.sub hd) (hC.sub hD)]
  simp only [inner_zero_left, EReal.coe_zero, lt_iff_not_ge, supportFunction_sub_nonpos_iff]

end RW
