/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Subgradients of the vector maximum and the Euclidean norm
-/

import RockafellarWets.Chapter8.SupportExamples
import RockafellarWets.Chapter8.SupportSubgradients

open Classical Metric Set
open scoped InnerProductSpace

namespace RW

section Max

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Example 8.26.** Precisely the probability weights supported on the
maximum coordinates are subgradients of the vector maximum. -/
theorem mem_subdifferential_vecMax_iff (v w : EuclideanSpace ℝ ι) :
    v ∈ subdifferential (fun z ↦ (vecMax z : EReal)) w ↔
      (∀ i, w i = vecMax w → 0 ≤ v i) ∧ (∀ i, w i ≠ vecMax w → v i = 0) ∧ ∑ i, v i = 1 := by
  have heq := funext (fun z : EuclideanSpace ℝ ι ↦ (supportFunction_canonicalSimplex z).1)
  rw [← heq, subdifferential_supportFunction convex_canonicalSimplex isClosed_canonicalSimplex
    canonicalSimplex_nonempty (by exact (supportFunction_canonicalSimplex w).1.trans_lt (EReal.coe_lt_top _))]
  simp only [mem_setOf_eq, (supportFunction_canonicalSimplex w).1, EReal.coe_eq_coe_iff]
  constructor
  · rintro ⟨hv,he⟩
    exact ⟨fun i _ ↦ hv.1 i, (simplex_inner_eq_vecMax_iff hv).1 he, hv.2⟩
  · rintro ⟨hpos,hzero,hsum⟩
    have hv : v ∈ canonicalSimplex := ⟨fun i ↦ by
      by_cases he : w i = vecMax w
      · exact hpos i he
      · rw [hzero i he], hsum⟩
    exact ⟨hv, (simplex_inner_eq_vecMax_iff hv).2 hzero⟩

theorem horizonSubdifferential_vecMax (w : EuclideanSpace ℝ ι) :
    horizonSubdifferential (fun z ↦ (vecMax z : EReal)) w = {0} := by
  apply horizonSubdifferential_eq_zero_of_convex_finite _ (fun z ↦ ⟨_, rfl⟩)
  rw [← funext (fun z : EuclideanSpace ℝ ι ↦ (supportFunction_canonicalSimplex z).1)]
  exact convex_epigraph_of_sublinear (sublinear_supportFunction _)

end Max

section Norm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 8.27.** At the origin the norm has the closed unit ball as
its subdifferential. Elsewhere its subgradient is the unit radial vector. -/
theorem subdifferential_norm (w : E) : subdifferential (fun z : E ↦ (‖z‖ : EReal)) w =
    if w = 0 then closedBall 0 1 else {‖w‖⁻¹ • w} := by
  classical
  have heq := funext (fun z : E ↦ (supportFunction_unitBall z).1)
  rw [← heq, subdifferential_supportFunction (convex_closedBall _ _) isClosed_closedBall
    (nonempty_closedBall.2 zero_le_one) (by exact (supportFunction_unitBall w).1.trans_lt (EReal.coe_lt_top _))]
  rw [(supportFunction_unitBall w).1]
  ext v
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [if_neg hw, mem_singleton_iff]
    change (v ∈ closedBall (0:E) 1 ∧ (⟪v,w⟫_ℝ : EReal) = (‖w‖ : EReal)) ↔ _
    simp only [EReal.coe_eq_coe_iff]
    refine ⟨fun ⟨hv,he⟩ ↦ (unitBall_inner_eq_norm_iff hw hv).1 he, fun he ↦ ?_⟩
    have hv : v ∈ closedBall (0:E) 1 := by
      rw [he, mem_closedBall_zero_iff]
      simp [norm_smul, norm_ne_zero_iff.2 hw]
    exact ⟨hv,(unitBall_inner_eq_norm_iff hw hv).2 he⟩

theorem horizonSubdifferential_norm (w : E) :
    horizonSubdifferential (fun z : E ↦ (‖z‖ : EReal)) w = {0} := by
  apply horizonSubdifferential_eq_zero_of_convex_finite _ (fun z ↦ ⟨_,rfl⟩)
  rw [← funext (fun z : E ↦ (supportFunction_unitBall z).1)]
  exact convex_epigraph_of_sublinear (sublinear_supportFunction _)

end Norm

end RW
