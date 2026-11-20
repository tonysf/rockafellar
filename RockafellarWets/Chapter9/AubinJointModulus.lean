/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The joint scalar-modulus formula for the Aubin property
-/

import RockafellarWets.Chapter9.AubinDistanceCriteria
import RockafellarWets.Chapter9.BoundedLipschitzModulus

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace F]
  {S : E → Set F} {x : E} {u : F}

/-- **Exercise 9.37**, the joint limsup of the local scalar distance moduli.
The explicit nonemptiness condition preserves the book's point-to-set distance
convention when using Mathlib's real-valued `infDist`. -/
theorem graphicalLipschitzModulus_eq_limsup_distance_moduli (hu : u ∈ S x)
    (hne : ∀ᶠ a in 𝓝 x, (S a).Nonempty) :
    graphicalLipschitzModulus S x u =
      limsup (fun p : E × F ↦ lipschitzModulus (fun a ↦ infDist p.2 (S a)) p.1) (𝓝 (x,u)) := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨k,hk,hk'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have hb := eventually_lt_of_limsup_lt hk
    obtain ⟨V,hV,W,hW,hVW⟩ := mem_nhds_prod_iff.mp hb
    obtain ⟨d,hd,hD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hV hne)
    have hprofile : AubinProfileEstimate S univ x u k := by
      refine ⟨ball x d,ball_mem_nhds _ hd,W,hW,fun a ha ↦ (hD (ball_subset_closedBall ha.2)).2,
        fun v hv ↦ ?_⟩
      rw [univ_inter]
      apply lipschitzOnWith_of_modulus_le_of_convex (convex_ball x d)
      intro a ha
      exact (hVW (a := (a,v)) ⟨(hD (ball_subset_closedBall ha)).1,hv⟩).le
    apply hk'.not_ge
    change graphicalLipschitzModulusWithin S univ x u ≤ (k:ℝ≥0∞)
    rw [graphicalLipschitzModulusWithin_eq_iInf_profiles (mem_univ x) hu]
    exact iInf_le (fun c : {c : ℝ≥0 // AubinProfileEstimate S univ x u c} ↦ ((c:ℝ≥0):ℝ≥0∞)) ⟨k,hprofile⟩
  · refine le_iInf fun k ↦ ?_
    obtain ⟨V,hV,W,hW,_,H⟩ := k.property.profileEstimate (mem_univ x) hu
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [prod_mem_nhds (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hV)) hW]
      with p hp
    apply lipschitzModulus_le (mem_interior_iff_mem_nhds.mp hp.1)
    simpa only [univ_inter] using H p.2 hp.2

end RW
