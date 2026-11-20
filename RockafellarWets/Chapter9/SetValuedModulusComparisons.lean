/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Comparing the two finite-radius set-valued moduli
-/

import RockafellarWets.Chapter9.AubinAbsoluteLocalization

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {X : Set E} {x : E} {r s : ℝ≥0}

/-- The first comparison in formula 9(14), with only eventual nonempty fibers. -/
theorem svRhoHatModulusWithin_le_svLipschitzModulusWithin
    (hne : ∀ᶠ a in 𝓝[X] x, (S a).Nonempty) :
    svRhoHatLipschitzModulusWithin S X r x ≤ svLipschitzModulusWithin S X r x := by
  refine le_iInf fun k ↦ ?_
  obtain ⟨U,hU,H⟩ := k.property
  apply localPairModulusWithin_le (inter_mem hU hne)
  intro a ha b hb
  calc
    _ = ENNReal.ofReal (rhoHatDistance r (S a) (S b)) := (ofReal_rhoHatDistance r ha.2 hb.2).symm
    _ ≤ ENNReal.ofReal (rhoDistance r (S a) (S b)) :=
      ENNReal.ofReal_le_ofReal (rhoHatDistance_le_rhoDistance r ha.2 hb.2)
    _ ≤ (k.val:ℝ≥0∞)*edist a b := by
      simpa only [edist_dist,rhoDistance] using H ha.1 hb.1

/-- The upper comparison in formula 9(14) with the necessary strict radius
margin. Upper semicontinuity of the zero-distance controls nearby fibers. -/
theorem svLipschitzModulusWithin_le_svRhoHatModulusWithin_of_lt
    (hS : ∀ᶠ a in 𝓝[X] x, (S a).Nonempty ∧ IsClosed (S a))
    (husc : UpperSemicontinuousWithinAt (fun a ↦ infDist 0 (S a)) X x)
    (hrs : 2*(r:ℝ)+infDist 0 (S x) < (s:ℝ)) :
    svLipschitzModulusWithin S X r x ≤ svRhoHatLipschitzModulusWithin S X s x := by
  have hsmall := husc ((s:ℝ)-2*(r:ℝ)) (by linarith)
  refine le_iInf fun k ↦ ?_
  obtain ⟨U,hU,H⟩ := k.property
  apply lipschitzModulusWithin_le (inter_mem (inter_mem hU hS) hsmall)
  intro a ha b hb
  have hrad : 2*(r:ℝ)+max (infDist 0 (S a)) (infDist 0 (S b)) ≤ (s:ℝ) := by
    have ha' : infDist 0 (S a) < (s:ℝ)-2*(r:ℝ) := ha.2
    have hb' : infDist 0 (S b) < (s:ℝ)-2*(r:ℝ) := hb.2
    have hm := max_le ha'.le hb'.le
    linarith
  calc
    _ = ENNReal.ofReal (rhoDistance r (S a) (S b)) := edist_dist _ _
    _ ≤ ENNReal.ofReal (rhoHatDistance s (S a) (S b)) := ENNReal.ofReal_le_ofReal
      (rhoDistance_le_rhoHatDistance_of_two_mul ha.1.2.2 hb.1.2.2 ha.1.2.1 hb.1.2.1 hrad)
    _ = rhoHatEDistance s (S a) (S b) := ofReal_rhoHatDistance s ha.1.2.1 hb.1.2.1
    _ ≤ (k.val:ℝ≥0∞)*edist a b := H a ha.1.1 b hb.1.1

/-- Each fixed-center distance function is continuous at a point of strict
set-valued continuity, with no global fiber hypotheses. -/
theorem SvStrictlyContinuousWithinAt.continuousWithinAt_infDist
    (h : SvStrictlyContinuousWithinAt S X x) (v : F) :
    ContinuousWithinAt (fun a ↦ infDist v (S a)) X x := by
  let r := ‖v‖₊
  obtain ⟨k,U,hU,H⟩ := (strictlyContinuousWithinAt_iff.mp ⟨h.1,h.2.2 r⟩).2
  have Hv := (svRhoLipschitzOnWith_iff_distance_functions.mp H) v (by simp [r])
  exact (Hv.continuousOn.continuousWithinAt (mem_of_mem_nhdsWithin h.1 hU)).mono_of_mem_nhdsWithin hU

/-- Formula 9(14) at a point of strict continuity, with a strict radius margin.
The weak boundary condition requires an additional hypothesis and is not asserted. -/
theorem SvStrictlyContinuousWithinAt.modulus_comparisons
    (h : SvStrictlyContinuousWithinAt S X x) (hrs : 2*(r:ℝ)+infDist 0 (S x) < (s:ℝ)) :
    svRhoHatLipschitzModulusWithin S X r x ≤ svLipschitzModulusWithin S X r x ∧
      svLipschitzModulusWithin S X r x ≤ svRhoHatLipschitzModulusWithin S X s x :=
  ⟨svRhoHatModulusWithin_le_svLipschitzModulusWithin (h.2.1.mono fun _ ha ↦ ha.1),
    svLipschitzModulusWithin_le_svRhoHatModulusWithin_of_lt h.2.1
      (h.continuousWithinAt_infDist 0).upperSemicontinuousWithinAt hrs⟩

end RW
