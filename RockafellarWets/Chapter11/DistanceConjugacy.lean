/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The conjugate of distance to a convex set
-/

import RockafellarWets.Chapter11.MoreauConjugacy
import RockafellarWets.Chapter11.SupportDualOperations
import RockafellarWets.Chapter8.DistanceSubderivatives
import RockafellarWets.Chapter8.SupportExamples

open Metric Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Distance is the infimal convolution of the norm and the indicator. -/
theorem distanceVA_eq_epiSum {C : Set E} (hcl : IsClosed C) (hne : C.Nonempty) :
    distanceVA C = epiSum (fun x : E ↦ (‖x‖ : EReal)) (indicatorVA C) := by
  funext x
  rw [epiSum_apply]
  refine le_antisymm (le_iInf fun w ↦ ?_) ?_
  · by_cases hw : w ∈ C
    · rw [indicatorVA_apply_mem hw,add_zero]
      exact EReal.coe_le_coe_iff.mpr (by simpa [dist_eq_norm] using (infDist_le_dist_of_mem (x := x) hw))
    · simp [indicatorVA_apply_not_mem hw]
  · obtain ⟨w,hw,he⟩ := hcl.exists_infDist_eq_dist hne x
    apply iInf_le_of_le w
    simp only [indicatorVA_apply_mem hw,add_zero,distanceVA,he,dist_eq_norm,le_rfl]

/-- **11.26(a)**, both directions of the distance/support conjugacy. -/
theorem distance_conjugacy {C : Set E} (hc : Convex ℝ C) (hcl : IsClosed C) (hne : C.Nonempty) :
    fenchelConjugate (distanceVA C) = (fun v ↦ supportFunction C v + indicatorVA (closedBall 0 1) v) ∧
    fenchelConjugate (fun v ↦ supportFunction C v + indicatorVA (closedBall 0 1) v) = distanceVA C := by
  let B := closedBall (0 : E) 1
  have hnorm : supportFunction B = fun x ↦ (‖x‖ : EReal) := funext fun x ↦ (supportFunction_unitBall x).1
  have hBC : Convex ℝ B := convex_closedBall _ _
  have hBcl : IsClosed B := isClosed_closedBall
  have hB₀ : (0 : E) ∈ interior B :=
    Metric.ball_subset_interior_closedBall (mem_ball_self zero_lt_one)
  have hhp : IsProper (fun x : E ↦ (‖x‖ : EReal)) :=
    ⟨⟨0,EReal.coe_lt_top _⟩,fun x ↦ EReal.bot_lt_coe _⟩
  have hind := (indicatorVA_isProper_iff C).mpr hne
  have hB := (indicatorVA_isProper_iff B).mpr ⟨0,interior_subset hB₀⟩
  have he : fenchelConjugate (fun x : E ↦ (‖x‖ : EReal)) = indicatorVA B := by
    rw [← hnorm,fenchelConjugate_supportFunction_of_closed_convex hBC hBcl]
  have hsc : Convex ℝ (epigraph (supportFunction C)) := by
    rw [← fenchelConjugate_indicatorVA]
    exact convex_epigraph_fenchelConjugate _
  have hbc : Convex ℝ (epigraph (indicatorVA B)) := by rw [epigraph_indicatorVA]; exact hBC.prod (convex_Ici 0)
  have hq : (0 : E) ∈ interior (effectiveDomain (supportFunction C) - effectiveDomain (indicatorVA B)) := by
    apply zero_mem_interior_sub_of_meets_interior
    rw [effectiveDomain_indicatorVA]
    exact Or.inl ⟨0,by simpa only [mem_effectiveDomain_iff,supportFunction_zero hne] using (EReal.coe_lt_top 0),hB₀⟩
  rw [distanceVA_eq_epiSum hcl hne]
  constructor
  · rw [epiSum_comm,fenchelConjugate_epiSum hind hhp,fenchelConjugate_indicatorVA,he]
  · rw [fenchelConjugate_add_of_interior (isProper_supportFunction hne) hB (lowerSemicontinuous_supportFunction _)
      (lowerSemicontinuous_indicatorVA hBcl) hsc hbc hq,
      fenchelConjugate_supportFunction_of_closed_convex hc hcl,fenchelConjugate_indicatorVA,← hnorm,epiSum_comm]

end RW
