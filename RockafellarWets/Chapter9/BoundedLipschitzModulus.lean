/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Lipschitz continuity from bounded modulus
-/

import RockafellarWets.Chapter9.LipschitzModulus
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.Order.IntermediateValue

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace F]

/-- A common local Lipschitz constant along a convex set bounds all pairs
of points of the set. Continuous induction propagates the bound along each segment. -/
theorem lipschitzOnWith_of_local_of_convex {f : E → F} {X : Set E} {K : ℝ≥0} (hc : Convex ℝ X)
    (h : ∀ z ∈ X, ∃ U ∈ 𝓝 z, LipschitzOnWith K f U) : LipschitzOnWith K f X := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  let γ := AffineMap.lineMap x y (k := ℝ)
  have hmap : MapsTo γ (Icc 0 1) X := fun t ht ↦ hc.lineMap_mem hx hy ht
  have hcont : ContinuousOn (f ∘ γ) (Icc 0 1) := by
    intro t ht
    obtain ⟨U, hU, hf⟩ := h _ (hmap ht)
    exact ((hf.continuousOn.continuousAt hU).comp AffineMap.lineMap_continuous.continuousAt).continuousWithinAt
  let S := {t : ℝ | dist (f x) (f (γ t)) ≤ K * t * dist x y}
  have hS : IsClosed (S ∩ Icc 0 1) := by
    rw [inter_comm]
    exact ((continuous_dist.comp_continuousOn (continuousOn_const.prodMk hcont)).prodMk ((continuousOn_const.mul continuousOn_id).mul continuousOn_const)
      ).preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  have h0 : 0 ∈ S := by simp [S, γ]
  have hseg := hS.Icc_subset_of_forall_mem_nhdsWithin h0 (fun t ht ↦ ?_)
  · simpa [S, γ] using hseg (a := 1) (right_mem_Icc.mpr zero_le_one)
  · obtain ⟨U, hU, hf⟩ := h _ (hmap (Ico_subset_Icc_self ht.2))
    have he : U ∈ 𝓝 (γ t) := hU
    have hev : ∀ᶠ s : ℝ in 𝓝[>] t, γ s ∈ U :=
      (AffineMap.lineMap_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually he
    filter_upwards [hev, (show ∀ᶠ s in 𝓝[>] t, t < s from self_mem_nhdsWithin)] with s hs hts
    have hp := hf.dist_le_mul _ (mem_of_mem_nhds he) _ hs
    change dist (f (AffineMap.lineMap x y t)) (f (AffineMap.lineMap x y s)) ≤
      K * dist (AffineMap.lineMap x y t) (AffineMap.lineMap x y s) at hp
    rw [dist_lineMap_lineMap, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hts.le)] at hp
    have ht' : dist (f x) (f (γ t)) ≤ K * t * dist x y := ht.1
    change dist (f x) (f (γ s)) ≤ K * s * dist x y
    calc
      _ ≤ dist (f x) (f (γ t)) + dist (f (γ t)) (f (γ s)) := dist_triangle ..
      _ ≤ K * t * dist x y + K * (-(t - s) * dist x y) := add_le_add ht' hp
      _ = _ := by ring

/-- **Theorem 9.2.** A bound on the exact modulus over a convex set is a
Lipschitz constant on the whole set, even when it is attained only as an infimum. -/
theorem lipschitzOnWith_of_modulus_le_of_convex {f : E → F} {X : Set E} {K : ℝ≥0} (hc : Convex ℝ X)
    (h : ∀ z ∈ X, lipschitzModulus f z ≤ (K : ℝ≥0∞)) : LipschitzOnWith K f X := by
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · simp
  apply (ENNReal.div_le_iff (edist_eq_zero.not.mpr hxy) (edist_ne_top x y)).mp
  by_contra! hn
  obtain ⟨k, hk, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hn
  have hl := lipschitzOnWith_of_local_of_convex hc (fun z hz ↦ exists_lipschitzOnWith_of_modulus_lt ((h z hz).trans_lt hk))
  exact hr.not_ge (ENNReal.div_le_of_le_mul (hl hx hy))

/-- On a nonempty compact convex set of strict continuity, the maximum
of the modulus is finite and gives a Lipschitz constant on that set. -/
theorem exists_max_modulus_of_compact_convex {f : E → F} {X : Set E} (hc : Convex ℝ X) (hX : IsCompact X)
    (hne : X.Nonempty) (hf : ∀ z ∈ X, StrictlyContinuousAt f z) :
    ∃ z ∈ X, ∃ k : ℝ≥0, lipschitzModulus f z = k ∧ (⨆ y : X, lipschitzModulus f y) = k ∧ LipschitzOnWith k f X := by
  obtain ⟨z, hz, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne hX
    ((upperSemicontinuous_lipschitzModulusWithin f univ).upperSemicontinuousOn X)
  let k := (lipschitzModulus f z).toNNReal
  have he : lipschitzModulus f z = k := (ENNReal.coe_toNNReal (hf z hz).ne).symm
  have hall : ∀ y ∈ X, lipschitzModulus f y ≤ (k : ℝ≥0∞) := fun y hy ↦ (hmax hy).trans he.le
  exact ⟨z, hz, k, he, le_antisymm (iSup_le fun y ↦ hall _ y.property)
    (he ▸ le_iSup (fun y : X ↦ lipschitzModulus f y) ⟨z,hz⟩), lipschitzOnWith_of_modulus_le_of_convex hc hall⟩

end RW
