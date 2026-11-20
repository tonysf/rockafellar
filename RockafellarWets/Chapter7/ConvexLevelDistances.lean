/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Distances between convex level sets
-/

import RockafellarWets.Chapter1.Semicontinuity
import RockafellarWets.Chapter4.LocalSetDistances

open Metric Set Topology

open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Interpolation toward a lower reference point takes a point from height
`b` to height `a`, at a distance proportional to the drop in height. -/
theorem exists_levelSet_dist_le_of_convex_epigraph {f : E → EReal}
    (hf : Convex ℝ (epigraph f)) {m a b : ℝ} (hma : m ≤ a) (hab : a ≤ b) (hmb : m < b)
    {z x : E} (hz : z ∈ levelSet f m) (hx : x ∈ levelSet f b) :
    ∃ y ∈ levelSet f a, dist x y ≤ ((b - a) / (b - m)) * dist x z := by
  let t := (b - a) / (b - m)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hmb.le)
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hmb)).mpr (by linarith)
  have heq : (1 - t) * b + t * m = a := by
    have h := div_mul_cancel₀ (b - a) (sub_ne_zero.mpr hmb.ne')
    dsimp [t]
    nlinarith
  have hxy := hf (x := (x, b)) hx (y := (z, m)) hz (sub_nonneg.mpr ht1) ht (by ring)
  refine ⟨(1 - t) • x + t • z, ?_, ?_⟩
  · change f _ ≤ (a : EReal)
    change f _ ≤ (((1 - t) * b + t * m : ℝ) : EReal) at hxy
    rwa [heq] at hxy
  · have hsub : x - ((1 - t) • x + t • z) = t • (x - z) := by module
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, dist_eq_norm]

/-- **Proposition 7.68.** The truncated distance between nested convex
level sets, in terms of the distance to the nearest minimizer. -/
theorem rhoHatDistance_levelSets_le_of_convex_epigraph [FiniteDimensional ℝ E]
    {f : E → EReal} (hprop : IsProper f) (hlsc : LowerSemicontinuous f)
    (hconv : Convex ℝ (epigraph f)) (hmin : (argmin f).Nonempty)
    {m a b : ℝ} (hm : (⨅ x, f x) = (m : EReal)) (hma : m < a) (hab : a < b)
    (ρ : ℝ≥0) :
    rhoHatDistance ρ (levelSet f b) (levelSet f a) ≤
      ((b - a) / (b - m)) * ((ρ : ℝ) + infDist 0 (argmin f)) := by
  have hclosed : IsClosed (argmin f) := by
    have hset : argmin f = {x | f x ≤ (m : EReal)} := by
      ext x
      rw [mem_argmin_iff_eq_iInf_of_isProper hprop, hm]
      exact ⟨Eq.le, fun h ↦ le_antisymm h (hm ▸ iInf_le f x)⟩
    rw [hset]
    exact (lowerSemicontinuous_iff_isClosed_preimage.mp hlsc) _
  obtain ⟨z, hz, hdist⟩ := hclosed.exists_infDist_eq_dist hmin 0
  have hzm : f z = (m : EReal) := ((mem_argmin_iff_eq_iInf_of_isProper hprop _).mp hz).trans hm
  have hza : z ∈ levelSet f a := hzm.le.trans (EReal.coe_le_coe_iff.mpr hma.le)
  have hlevels : levelSet f a ⊆ levelSet f b := fun _ h ↦ h.trans (EReal.coe_le_coe_iff.mpr hab.le)
  have ht : 0 ≤ (b - a) / (b - m) := div_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr (hma.trans hab).le)
  have hnonneg : 0 ≤ (b - a) / (b - m) * ((ρ : ℝ) + infDist 0 (argmin f)) :=
    mul_nonneg ht (add_nonneg ρ.coe_nonneg infDist_nonneg)
  apply (rhoHatDistance_le_iff ρ ⟨z, hlevels hza⟩ ⟨z, hza⟩ hnonneg).mpr
  constructor
  · rintro x ⟨hx, hxρ⟩
    obtain ⟨y, hy, hxy⟩ := exists_levelSet_dist_le_of_convex_epigraph hconv hma.le hab.le
      (hma.trans hab) (z := z) hzm.le hx
    apply mem_cthickening_of_dist_le x y _ _ hy (hxy.trans ?_)
    apply mul_le_mul_of_nonneg_left _ ht
    exact (dist_triangle x 0 z).trans (add_le_add hxρ hdist.ge)
  · rintro x ⟨hx, _⟩
    exact mem_cthickening_of_dist_le x x _ _ (hlevels hx) (by simpa using hnonneg)

end RW
