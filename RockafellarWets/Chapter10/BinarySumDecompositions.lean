/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Binary decompositions and the finite-family counterexample to 10.42
-/
import RockafellarWets.Chapter10.BoundedFiniteSums
import RockafellarWets.Chapter10.CoderivativeAddition
import RockafellarWets.Chapter10.SumClosednessCounterexample

open Bornology Filter Metric Set Topology

namespace RW

/-- The binary decomposition mapping from Chapter 5 stores just the first
summand. Bounding it locally also bounds both components of the finite-family
decomposition, since the sum stays near the specified output. -/
theorem finiteSumMappingAux_fin_two_of_svAddAux {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {S T : E → Set F} {x : E} {b : F}
    (hb : SvLocallyBoundedAt (svAddAux S T) (x,b)) :
    SvLocallyBoundedAt (finiteSumMappingAux (![S,T] : Fin 2 → E → Set F)) (x,b) := by
  obtain ⟨U,hU,hB⟩ := hb
  obtain ⟨V,hV,W,hW,hVW⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨r,hr,hball⟩ := hB.subset_closedBall_lt 0 (0:F)
  apply finiteSumMappingAux_locallyBounded_iff.mpr
  refine ⟨V,hV,W ∩ ball b 1,inter_mem hW (ball_mem_nhds b one_pos),r+‖b‖+2,by positivity,?_⟩
  intro a ha q hq hs i
  rw [Fin.sum_univ_two] at hs
  have hmem : q 0 ∈ svImage (svAddAux S T) U := by
    refine mem_svImage.mpr ⟨(a,q 0+q 1),hVW ⟨ha,hs.1⟩,mem_svAddAux.mpr ⟨hq 0,?_⟩⟩
    change q 0+q 1-q 0 ∈ T a
    simpa using (show q 1 ∈ T a from hq 1)
  have hq0 : ‖q 0‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hball hmem
  have hsum := norm_le_norm_add_norm_sub' (q 0+q 1) b
  have hdist := mem_ball.mp hs.2
  rw [dist_eq_norm] at hdist
  fin_cases i
  · change ‖q 0‖ < r+‖b‖+2
    linarith [norm_nonneg b]
  · change ‖q 1‖ < r+‖b‖+2
    have hq1 := norm_sub_le (q 0+q 1) (q 0)
    rw [add_sub_cancel_left] at hq1
    linarith

/-- The counterexample to 10.42 in the very same finite-family notation
used by its Aubin and Hausdorff modulus estimates. -/
theorem finite_sum_strict_continuity_counterexample :
    ∃ S : Fin 2 → ℝ → Set (WithLp 2 (ℝ × ℝ)),
      (∀ i, SvOsc (S i) ∧ SvStrictlyContinuousAt (S i) 0) ∧
      (∀ b ∈ svFiniteSum S 0, SvLocallyBoundedAt (finiteSumMappingAux S) (0,b)) ∧
      ¬ SvStrictlyContinuousAt (svFiniteSum S) 0 := by
  obtain ⟨hA,hB,hsA,hsB,hb,hn⟩ := strict_continuity_sum_counterexample
  let S : ℝ → Set (WithLp 2 (ℝ × ℝ)) := fun _ ↦ exponentialGraphSet
  let T : ℝ → Set (WithLp 2 (ℝ × ℝ)) := fun _ ↦ horizontalAxisSet
  refine ⟨![S,T],?_,?_,?_⟩
  · intro i; fin_cases i
    · exact ⟨hA,hsA⟩
    · exact ⟨hB,hsB⟩
  · rw [svFiniteSum_fin_two]
    exact fun b h ↦ finiteSumMappingAux_fin_two_of_svAddAux (hb b h)
  · rw [svFiniteSum_fin_two]
    exact hn

end RW
