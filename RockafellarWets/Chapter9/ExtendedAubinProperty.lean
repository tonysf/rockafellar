/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: The extended Aubin estimate
-/

import RockafellarWets.Chapter9.AubinProperty

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {S : E → Set F} {X : Set E} {x : E} {u : F} {k : ℝ≥0}

/-- The extended inclusion of Lemma 9.39(b). Its source input can be anywhere
in the reference set, while the target input stays near the base point. -/
def ExtendedAubinEstimate (S : E → Set F) (X : Set E) (x : E) (u : F) (k : ℝ≥0) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 u, ∀ a ∈ X, ∀ b ∈ X ∩ V, ∀ v ∈ S a ∩ W, ∃ z ∈ S b, dist v z ≤ k * dist a b

theorem ExtendedAubinEstimate.toAubinEstimate (h : ExtendedAubinEstimate S X x u k) :
    AubinEstimate S X x u k := by
  obtain ⟨V,hV,W,hW,h⟩ := h
  exact ⟨V,hV,W,hW,fun a ha ↦ h a ha.1⟩

/-- **Lemma 9.39.** Any strictly positive Aubin constant admits the extended
formulation. The positive radius in the output variable requires positivity
of the constant, as the counterexample below shows. -/
theorem extendedAubinEstimate_iff_of_pos (hx : x ∈ X) (hu : u ∈ S x) (hk : 0 < k) :
    ExtendedAubinEstimate S X x u k ↔ AubinEstimate S X x u k := by
  refine ⟨ExtendedAubinEstimate.toAubinEstimate,?_⟩
  rintro ⟨V,hV,W,hW,H⟩
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hV
  have hk' : 0 < (k:ℝ) := hk
  refine ⟨ball x (δ/4),ball_mem_nhds _ (by positivity),W ∩ ball u (k*(δ/4)),
    inter_mem hW (ball_mem_nhds _ (by positivity)),?_⟩
  intro a ha b hb v hv
  have hb' : dist b x < δ/4 := hb.2
  have hbV : b ∈ X ∩ V := ⟨hb.1,hsub (show dist b x < δ by linarith)⟩
  by_cases haV : a ∈ ball x δ
  · exact H a ⟨ha,hsub haV⟩ b hbV v ⟨hv.1,hv.2.1⟩
  · obtain ⟨z,hz,hd⟩ := H x ⟨hx,mem_of_mem_nhds hV⟩ b hbV u ⟨hu,mem_of_mem_nhds hW⟩
    have hfar : δ ≤ dist a x := le_of_not_gt haV
    have hv' : dist v u < k*(δ/4) := hv.2.2
    rw [dist_comm x b] at hd
    have h₁ := dist_triangle a b x
    have h₂ := mul_le_mul_of_nonneg_left (show δ/4 + dist b x ≤ dist a b by linarith) hk'.le
    exact ⟨z,hz,(dist_triangle v u z).trans (by nlinarith)⟩

/-- Even at zero modulus, taking the infimum of the extended constants gives
the original graphical Lipschitz modulus. -/
theorem graphicalLipschitzModulusWithin_eq_iInf_extended (hx : x ∈ X) (hu : u ∈ S x) :
    graphicalLipschitzModulusWithin S X x u =
      ⨅ k : {k : ℝ≥0 // ExtendedAubinEstimate S X x u k}, ((k : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm (le_iInf fun k ↦ k.2.toAubinEstimate.modulus_le)
  by_contra! h
  obtain ⟨k,hk,hk'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hkpos : 0 < k := ENNReal.coe_pos.mp (lt_of_le_of_lt bot_le hk)
  have H := (extendedAubinEstimate_iff_of_pos hx hu hkpos).mpr (aubinEstimate_of_modulus_lt hk)
  exact hk'.not_ge (iInf_le (fun a : {l : ℝ≥0 // ExtendedAubinEstimate S X x u l} ↦ ((a : ℝ≥0) : ℝ≥0∞)) ⟨k,H⟩)

theorem hasAubinPropertyWithinAt_iff_extended :
    HasAubinPropertyWithinAt S X x u ↔ x ∈ X ∧ u ∈ S x ∧ IsLocallyClosedAt (svGraph S) (x,u) ∧
      ∃ k, ExtendedAubinEstimate S X x u k := by
  constructor
  · rintro ⟨hx,hu,hl,k,hk⟩
    exact ⟨hx,hu,hl,k+1,(extendedAubinEstimate_iff_of_pos hx hu (by positivity)).mpr
      (hk.mono (by simp))⟩
  · rintro ⟨hx,hu,hl,k,hk⟩
    exact ⟨hx,hu,hl,k,hk.toAubinEstimate⟩

private def remoteFiber (a : ℝ) : Set ℝ := if a = 2 then Ioi 0 else {0}

/-- At constant zero the printed equivalence in 9.39 fails. The graph is
locally the zero function, but the distant fiber contains arbitrarily small
strictly positive values. -/
theorem zero_aubinEstimate_counterexample :
    ∃ S : ℝ → Set ℝ, 0 ∈ S 0 ∧ IsLocallyClosedAt (svGraph S) (0,0) ∧
      AubinEstimate S univ 0 0 0 ∧ ¬ ExtendedAubinEstimate S univ 0 0 0 := by
  have hf {a : ℝ} (ha : a ∈ closedBall 0 1) : remoteFiber a = {0} := by
    have hn : a ≠ 2 := by rintro rfl; norm_num [mem_closedBall,Real.dist_eq] at ha
    simp [remoteFiber,hn]
  have hU : closedBall (0:ℝ) 1 ∈ 𝓝 0 := closedBall_mem_nhds _ zero_lt_one
  have hz : 0 ∈ remoteFiber 0 := by norm_num [remoteFiber]
  refine ⟨remoteFiber,hz,?_,?_,?_⟩
  · let U := closedBall (0:ℝ) 1 ×ˢ (univ : Set ℝ)
    have he : svGraph remoteFiber ∩ U = closedBall (0:ℝ) 1 ×ˢ {0} := by
      ext p
      change (p.2 ∈ remoteFiber p.1 ∧ p.1 ∈ closedBall 0 1 ∧ p.2 ∈ univ) ↔ _
      constructor
      · rintro ⟨h,ha,_⟩
        exact ⟨ha,hf ha ▸ h⟩
      · rintro ⟨ha,hb⟩
        exact ⟨hf ha ▸ hb,ha,trivial⟩
    exact ⟨U,prod_mem_nhds hU univ_mem,isClosed_closedBall.prod isClosed_univ,
      he ▸ isClosed_closedBall.prod isClosed_singleton⟩
  · refine ⟨closedBall 0 1,hU,univ,univ_mem,?_⟩
    intro a ha b hb v hv
    have he : v = 0 := by have hm := hv.1; rwa [hf ha.2,mem_singleton_iff] at hm
    exact ⟨0,hf hb.2 ▸ mem_singleton _,by simp [he]⟩
  · rintro ⟨V,hV,W,hW,H⟩
    obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp hW
    have hr' : r/2 ∈ remoteFiber 2 := by simp [remoteFiber,hr]
    have hball : r/2 ∈ ball (0:ℝ) r := by
      rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    obtain ⟨z,hz',hd⟩ := H 2 trivial 0 ⟨trivial,mem_of_mem_nhds hV⟩ (r/2) ⟨hr',hrW hball⟩
    have hz₀ : z = 0 := by simpa [remoteFiber] using hz'
    simp [hz₀,abs_of_pos hr] at hd
    linarith

end RW
