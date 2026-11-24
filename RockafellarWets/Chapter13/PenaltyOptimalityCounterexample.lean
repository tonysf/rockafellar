/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: the critical cones of Exercise 13.26 depend on the multiplier

Exercise 13.26 asserts that the cones `X'(x̄) = T_X(x̄) ∩ ∇ₓL(x̄, ŷ)^⊥` and
`Y'(x̄) = T_Y(ŷ) ∩ ∇_yL(x̄, ŷ)^⊥` do not depend on the choice of `ŷ ∈ Y(x̄)`; its guide only claims
this for the function `δ_{X'(x̄)} + 2θ_{Y'(x̄),B}(∇F(x̄)·)`, which is what
`second_order_optimality_with_penalties` proves.  In one dimension take `X = Y = [0, ∞)`, `B = 0`,
`f₀(x) = x`, `F(x) = -x` and `x̄ = 0`: then `Y(x̄) = [0, 1]`, and both cones change between
`ŷ = 0` and `ŷ = 1`.
-/

import RockafellarWets.Chapter13.PenaltyOptimality

open Filter Set Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace RW
namespace PenaltyOptimalityCounterexample

/-- `f₀(x) = x`. -/
def f₀ : ℝ → ℝ := fun x ↦ x

/-- `F(x) = -x`. -/
def F : ℝ → ℝ := fun x ↦ -x

theorem gradient_f₀ : gradient f₀ 0 = 1 := by
  rw [gradient_eq_deriv']
  exact congrFun deriv_id'' 0

theorem adjoint_fderiv_F (y : ℝ) : (fderiv ℝ F 0).adjoint y = -y := by
  have hF : fderiv ℝ F 0 = -ContinuousLinearMap.id ℝ ℝ := ((hasFDerivAt_id (0 : ℝ)).neg).fderiv
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, hF]
  simp

theorem normalCone_Ici_zero_zero : normalCone (Ici (0 : ℝ)) 0 = Iic 0 := by
  rw [normalCone_eq_of_convex (convex_Ici 0) (by simp)]
  ext v
  simp only [mem_setOf_eq, mem_Ici, sub_zero, mem_Iic]
  constructor
  · intro h
    have := h 1 zero_le_one
    simpa using this
  · intro hv z hz
    simp only [RCLike.inner_apply, conj_trivial]
    nlinarith

theorem zero_mem_normalCone_Ici_zero {x : ℝ} (hx : 0 ≤ x) : (0 : ℝ) ∈ normalCone (Ici (0 : ℝ)) x := by
  rw [normalCone_eq_of_convex (convex_Ici 0) hx]
  intro z _
  simp

theorem mem_tangentCone_of_forall_add_inv_smul {C : Set ℝ} {x w : ℝ}
    (h : ∀ n : ℕ, x + ((n : ℝ) + 1)⁻¹ * w ∈ C) : w ∈ tangentCone C x := by
  refine mem_tangentCone_of_forall (xs := fun n : ℕ ↦ x + ((n : ℝ) + 1)⁻¹ * w)
    (τs := fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) h (fun n ↦ by positivity)
    (by simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_
  refine tendsto_const_nhds.congr fun n ↦ ?_
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [add_sub_cancel_left, inv_inv, smul_eq_mul]
  field_simp

theorem one_mem_tangentCone : (1 : ℝ) ∈ tangentCone (Ici (0 : ℝ)) 0 :=
  mem_tangentCone_of_forall_add_inv_smul fun n ↦ by simp only [mem_Ici]; positivity

theorem neg_one_mem_tangentCone : (-1 : ℝ) ∈ tangentCone (Ici (0 : ℝ)) 1 := by
  refine mem_tangentCone_of_forall_add_inv_smul fun n ↦ ?_
  have h : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
  simp only [mem_Ici]
  linarith

/-- **Exercise 13.26**, the cones `X'(x̄)` and `Y'(x̄)` themselves depend on `ŷ ∈ Y(x̄)`.  For
`n = m = 1`, `X = Y = [0, ∞)`, `B = 0`, `f₀(x) = x`, `F(x) = -x` and `x̄ = 0`, all hypotheses of
13.26 hold (`B = 0` is symmetric and positive-semidefinite), and `Y(x̄) = [0, 1]` contains
`ŷ = 0` and `ŷ = 1`.  But `1 ∈ X'(x̄)` for `ŷ = 1`, where `∇ₓL(x̄, 1) = 0`, while `1 ∉ X'(x̄)`
for `ŷ = 0`, where `∇ₓL(x̄, 0) = 1`; likewise `-1 ∈ Y'(x̄) = T_Y(1)` for `ŷ = 1` while
`Y'(x̄) = T_Y(0) = [0, ∞)` for `ŷ = 0`.  The functions `δ_{X'(x̄)} + 2θ_{Y'(x̄),B}(∇F(x̄)·)` agree, as
in `second_order_optimality_with_penalties`. -/
theorem penalty_critical_cones_depend_on_multiplier :
    IsPolyhedral (Ici (0 : ℝ)) ∧ (Ici (0 : ℝ)).Nonempty ∧ ContDiff ℝ 2 f₀ ∧ ContDiff ℝ 2 F ∧
      (0 : ℝ) ∈ Ici (0 : ℝ) ∧ F 0 ∈ effectiveDomain (plqPenalty (Ici (0 : ℝ)) 0) ∧
      (∀ y ∈ horizonCone (Ici (0 : ℝ)), (0 : ℝ →L[ℝ] ℝ) y = 0 →
        -((fderiv ℝ F 0).adjoint y) ∈ normalCone (Ici (0 : ℝ)) 0 → y = 0) ∧
      (0 : ℝ) ∈ penaltyMultiplierSet f₀ F (Ici 0) (Ici 0) 0 0 ∧
      (1 : ℝ) ∈ penaltyMultiplierSet f₀ F (Ici 0) (Ici 0) 0 0 ∧
      (1 : ℝ) ∈ penaltyPrimalCriticalCone f₀ F (Ici 0) 0 1 ∧
      (1 : ℝ) ∉ penaltyPrimalCriticalCone f₀ F (Ici 0) 0 0 ∧
      (-1 : ℝ) ∈ penaltyCriticalCone (Ici 0) 0 (F 0) 1 ∧
      (-1 : ℝ) ∉ penaltyCriticalCone (Ici 0) 0 (F 0) 0 := by
  have hF0 : F 0 = 0 := by simp [F]
  refine ⟨IsPolyhedral.Ici_zero, ⟨0, mem_Ici.2 le_rfl⟩, contDiff_id, contDiff_id.neg,
    mem_Ici.2 le_rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · change plqPenalty (Ici (0 : ℝ)) 0 (F 0) < ⊤
    refine lt_of_le_of_lt (iSup₂_le fun y _ ↦ ?_) (EReal.coe_lt_top 0)
    simp [hF0]
  · intro y hy _ hN
    rw [horizonCone_Ici_zero, mem_Ici] at hy
    rw [adjoint_fderiv_F, neg_neg, normalCone_Ici_zero_zero, mem_Iic] at hN
    linarith
  · refine ⟨?_, ?_⟩
    · rw [gradient_f₀, adjoint_fderiv_F, normalCone_Ici_zero_zero, mem_Iic]
      norm_num
    · rw [hF0]
      simpa using zero_mem_normalCone_Ici_zero le_rfl
  · refine ⟨?_, ?_⟩
    · rw [gradient_f₀, adjoint_fderiv_F, normalCone_Ici_zero_zero, mem_Iic]
      norm_num
    · rw [hF0]
      simpa using zero_mem_normalCone_Ici_zero zero_le_one
  · refine ⟨one_mem_tangentCone, ?_⟩
    rw [gradient_f₀, adjoint_fderiv_F]
    simp
  · rintro ⟨-, h⟩
    rw [gradient_f₀, adjoint_fderiv_F] at h
    simp at h
  · refine ⟨?_, ?_⟩
    · exact neg_one_mem_tangentCone
    · simp [hF0]
  · rintro ⟨h, -⟩
    have hN : (-1 : ℝ) ∈ normalCone (Ici (0 : ℝ)) 0 := by
      rw [normalCone_Ici_zero_zero, mem_Iic]; norm_num
    rw [normalCone_eq_regularNormalCone_of_convex (convex_Ici 0) (by simp),
      regularNormalCone_eq_polarCone_tangentCone (by simp)] at hN
    have := hN _ h
    simp at this
    linarith

end PenaltyOptimalityCounterexample
end RW
