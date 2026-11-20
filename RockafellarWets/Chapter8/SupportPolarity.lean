/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Horizon cones and finite support values
-/

import RockafellarWets.Chapter8.SupportFunctions
import RockafellarWets.Chapter3.HorizonCones
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Bornology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The final polarity assertion of Theorem 8.24, in both directions. -/
theorem horizonCone_polar_effectiveDomain_supportFunction {D : Set E} (hD : IsClosed D)
    (hc : Convex ℝ D) (hne : D.Nonempty) :
    horizonCone D = polarCone (effectiveDomain (supportFunction D)) ∧
      polarCone (horizonCone D) = closure (effectiveDomain (supportFunction D)) := by
  obtain ⟨x,hx⟩ := hne
  have heq : linearMinorantSet (supportFunction D) = D := by
    rw [linearMinorantSet_supportFunction, hc.convexHull_eq, hD.closure_eq]
  have hfirst : horizonCone D = polarCone (effectiveDomain (supportFunction D)) := by
    ext v
    constructor
    · intro hv w hw
      obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real (show supportFunction D w < ⊤ from hw)
      by_contra! hpos
      let t := (|r-⟪x,w⟫_ℝ|+1)/⟪v,w⟫_ℝ
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have h := EReal.coe_lt_coe_iff.1
        ((inner_le_supportFunction (smul_add_mem_of_mem_horizonCone hc hD hx hv ht) w).trans_lt hr)
      rw [inner_add_left, real_inner_smul_left,
        show t*⟪v,w⟫_ℝ = |r-⟪x,w⟫_ℝ|+1 by dsimp [t]; field_simp] at h
      linarith [le_abs_self (r-⟪x,w⟫_ℝ)]
    · intro hv
      apply mem_horizonCone_of_forall_smul_add_mem (x := x)
      intro t ht
      rw [← heq]
      intro w
      by_cases hw : supportFunction D w = ⊤
      · simp [hw]
      have hi := hv w (show w ∈ effectiveDomain (supportFunction D) from lt_top_iff_ne_top.2 hw)
      apply le_trans _ (inner_le_supportFunction hx w)
      rw [EReal.coe_le_coe_iff, inner_add_left, real_inner_smul_left]
      linarith only [mul_nonpos_of_nonneg_of_nonpos ht hi]
  refine ⟨hfirst, ?_⟩
  let S := effectiveDomain (supportFunction D)
  have hcone : IsCone S := by
    refine ⟨(sublinear_supportFunction D).1.1, fun {w} hw {t} ht ↦ ?_⟩
    change supportFunction D (t • w) < ⊤
    have hfin := EReal.coe_toReal (show supportFunction D w < ⊤ from hw).ne
      ((isProper_supportFunction ⟨x,hx⟩).2 w).ne'
    rw [(sublinear_supportFunction D).1.2 ht, ← hfin, ← EReal.coe_mul]
    exact EReal.coe_lt_top _
  have hconv : Convex ℝ S := by
    intro u hu v hv a b ha hb hab
    obtain ⟨s, hus, _⟩ := EReal.exists_between_coe_real (show supportFunction D u < ⊤ from hu)
    obtain ⟨t, hvt, _⟩ := EReal.exists_between_coe_real (show supportFunction D v < ⊤ from hv)
    change supportFunction D (a • u + b • v) < ⊤
    apply lt_of_le_of_lt _ (EReal.coe_lt_top (a*s + b*t))
    apply (supportFunction_le_iff _ _ _).2
    intro z hz
    have hzu := EReal.coe_lt_coe_iff.1 ((inner_le_supportFunction hz u).trans_lt hus)
    have hzv := EReal.coe_lt_coe_iff.1 ((inner_le_supportFunction hz v).trans_lt hvt)
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, EReal.coe_le_coe_iff]
    exact add_le_add (mul_le_mul_of_nonneg_left hzu.le ha) (mul_le_mul_of_nonneg_left hzv.le hb)
  rw [hfirst, polarCone_bipolar, conicHull_eq_self_of_convex_isCone hconv hcone]

/-- **Proposition 8.29(d).** Nonempty bounded sets are exactly those whose
support function is finite in every direction. -/
theorem nonempty_bounded_iff_supportFunction_finite (C : Set E) :
    C.Nonempty ∧ IsBounded C ↔ ∀ w, ∃ r : ℝ, supportFunction C w = (r : EReal) := by
  constructor
  · rintro ⟨hne,hb⟩ w
    obtain ⟨R,hR⟩ := hb.exists_norm_le
    have hupper := (supportFunction_le_iff C w ((R*‖w‖ : ℝ) : EReal)).2 fun v hv ↦
      EReal.coe_le_coe_iff.2 (((le_abs_self _).trans (abs_real_inner_le_norm v w)).trans
        (mul_le_mul_of_nonneg_right (hR v hv) (norm_nonneg w)))
    exact ⟨_, (EReal.coe_toReal (hupper.trans_lt (EReal.coe_lt_top _)).ne
      ((isProper_supportFunction hne).2 w).ne').symm⟩
  · intro h
    have hn : C.Nonempty := by
      by_contra! hempty
      obtain ⟨r,hr⟩ := h 0
      simp [hempty] at hr
    refine ⟨hn, isBounded_iff_forall_norm_le.2 ?_⟩
    letI := FiniteDimensional.complete ℝ E
    obtain ⟨R,hR⟩ := banach_steinhaus (g := fun v : C ↦ innerSL ℝ (v:E)) (by
      intro w
      obtain ⟨p,hp⟩ := h w
      obtain ⟨q,hq⟩ := h (-w)
      refine ⟨max p q, fun v ↦ ?_⟩
      have h₁ := EReal.coe_le_coe_iff.1 ((inner_le_supportFunction v.2 w).trans_eq hp)
      have h₂ := EReal.coe_le_coe_iff.1 ((inner_le_supportFunction v.2 (-w)).trans_eq hq)
      rw [inner_neg_right] at h₂
      rw [innerSL_apply_apply, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [le_max_right p q], h₁.trans (le_max_left _ _)⟩)
    exact ⟨R, fun v hv ↦ by simpa only [innerSL_apply_norm] using hR ⟨v,hv⟩⟩

end RW
