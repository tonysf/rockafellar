/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: The exact local modulus of distance
-/

import RockafellarWets.Chapter9.LipschitzModulus
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {C : Set E} {x : E}

private theorem one_le_modulus_infDist_of_not_mem (hC : IsClosed C) (hne : C.Nonempty) (hx : x ∉ C) :
    1 ≤ lipschitzModulus (infDist · C) x := by
  obtain ⟨p, hp, hd⟩ := hC.exists_infDist_eq_dist hne x
  have hpos := (hC.notMem_iff_infDist_pos hne).mp hx
  rw [hd] at hpos
  refine le_iInf fun k ↦ ?_
  obtain ⟨U, hU, h⟩ := k.property
  rw [nhdsWithin_univ] at hU
  let γ := AffineMap.lineMap x p (k := ℝ)
  have hlim : Tendsto γ (𝓝[>] 0) (𝓝 x) := by
    simpa only [γ, AffineMap.lineMap_apply_zero] using
      (AffineMap.lineMap_continuous (p := x) (q := p)).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  obtain ⟨t, htU, ht⟩ := ((hlim.eventually hU).and (show ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 1 from
    Ioo_mem_nhdsGT one_pos)).exists
  have hz := h.dist_le_mul x (mem_of_mem_nhds hU) (γ t) htU
  rw [Real.dist_eq, hd] at hz
  have hxt : dist x (γ t) = t * dist x p := by simp [γ, dist_left_lineMap, Real.norm_eq_abs, abs_of_pos ht.1]
  have htp : dist (γ t) p = (1-t) * dist x p := by
    simp [γ, dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2.le)]
  have htval := infDist_le_dist_of_mem (x := γ t) hp
  rw [hxt] at hz
  rw [htp] at htval
  apply (ENNReal.coe_le_coe (r := (1 : ℝ≥0))).mpr
  show (1 : ℝ) ≤ (k.val : ℝ)
  have hh : t * dist x p ≤ k.val * (t * dist x p) := by
    calc
      _ ≤ dist x p - infDist (γ t) C := by linarith
      _ ≤ _ := (le_abs_self _).trans hz
  exact (le_of_mul_le_mul_right (by simpa only [one_mul] using hh : 1 * (t * dist x p) ≤ _) (mul_pos ht.1 hpos))

/-- **Example 9.6.** The distance to a nonempty closed set is globally
one-Lipschitz; its modulus is zero in the interior and one everywhere else. -/
theorem lipschitzModulus_infDist (hC : IsClosed C) (hne : C.Nonempty) (x : E) :
    LipschitzWith 1 (infDist · C) ∧
      (x ∈ interior C → lipschitzModulus (infDist · C) x = 0) ∧
      (x ∉ interior C → lipschitzModulus (infDist · C) x = 1) := by
  have h := lipschitz_infDist_pt C
  refine ⟨h, ?_, ?_⟩
  · intro hx
    apply bot_unique
    apply lipschitzModulus_le (k := 0) (mem_interior_iff_mem_nhds.mp hx)
    exact (LipschitzOnWith.zero_iff _).mpr fun y hy z hz ↦ (infDist_zero_of_mem hy).trans (infDist_zero_of_mem hz).symm
  · intro hx
    apply le_antisymm (lipschitzModulus_le (k := 1) univ_mem (lipschitzOnWith_univ.mpr h))
    by_contra! hlt
    have hev := upperSemicontinuous_lipschitzModulusWithin (infDist · C) univ x 1 hlt
    exact hx (mem_interior_iff_mem_nhds.mpr (hev.mono fun y hy ↦ by
      by_contra hneg
      exact hy.not_ge (one_le_modulus_infDist_of_not_mem hC hne hneg)))

end RW
