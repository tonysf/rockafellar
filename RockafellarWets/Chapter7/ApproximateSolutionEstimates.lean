/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Distances between approximate solution sets
-/

import RockafellarWets.Chapter7.ApproximateMinimizers
import RockafellarWets.Chapter7.AuxEpiDistance
import RockafellarWets.Chapter7.ConvexLevelDistances

open Metric Set Topology

open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem min_le_of_auxEpiComparison {f g : E → EReal} {ρ : ℝ≥0} {η m k : ℝ}
    {z : E} (hz : z ∈ closedBall (0 : E) (ρ : ℝ)) (hf : f z = (m : EReal))
    (hk : (⨅ x, g x) = (k : EReal)) (hm : -(ρ : ℝ) ≤ m)
    (h : auxEpiComparison ρ f g η) : k ≤ m + η := by
  obtain ⟨y, _, hy⟩ := h z hz
  rw [hf, max_eq_left (EReal.coe_le_coe_iff.mpr hm), ← EReal.coe_add] at hy
  exact EReal.coe_le_coe_iff.mp ((hk ▸ iInf_le g y).trans hy)

/-- Interpolate a nearby trial point toward the reference minimizer. The
distance is estimated directly from the original point so that the trial
point need not belong to the truncation ball. -/
private theorem approxArgmin_subset_of_auxEpiComparison {f g : E → EReal}
    {ρ : ℝ≥0} {ε η m k : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hconv : Convex ℝ (epigraph g)) {z : E} (hz : z ∈ closedBall (0 : E) (ρ : ℝ))
    (hgz : g z = (k : EReal)) (hf : (⨅ x, f x) = (m : EReal)) (hg : (⨅ x, g x) = (k : EReal))
    (hm : -(ρ : ℝ) ≤ m) (hmk : m ≤ k + η) (h : auxEpiComparison ρ f g η) :
    approxArgmin f ε ∩ closedBall (0 : E) (ρ : ℝ) ⊆
      cthickening (η * (1 + 2 * (ρ : ℝ) / (η + ε / 2))) (approxArgmin g ε) := by
  rintro x ⟨hx, hxρ⟩
  obtain ⟨u, hxu, hu⟩ := h x hxρ
  change f x ≤ (⨅ y, f y) + (ε : EReal) at hx
  rw [hf, ← EReal.coe_add] at hx
  have hmfx : (m : EReal) ≤ f x := hf ▸ iInf_le f x
  rw [max_eq_left ((EReal.coe_le_coe_iff.mpr hm).trans hmfx)] at hu
  let b := k + ε + 2 * η
  have hub : g u ≤ (b : EReal) := by
    refine hu.trans ((add_le_add_left hx _).trans ?_)
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (by dsimp [b]; linarith)
  let t := η / (η + ε / 2)
  have hden : 0 < η + ε / 2 := by linarith
  have ht : 0 ≤ t := div_nonneg hη hden.le
  have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith)
  have htden : t * (η + ε / 2) = η := div_mul_cancel₀ _ hden.ne'
  let v := (1 - t) • u + t • z
  have hv : g v ≤ ((k + ε : ℝ) : EReal) := by
    have hv' := hconv (x := (u, b)) hub (y := (z, k)) hgz.le (sub_nonneg.mpr ht1) ht (by ring)
    change g v ≤ (((1-t)*b+t*k : ℝ) : EReal) at hv'
    have hmix : (1-t)*b+t*k = k+ε := by dsimp [b]; nlinarith [htden]
    rwa [hmix] at hv'
  apply mem_cthickening_of_dist_le x v _ _
  · change g v ≤ (⨅ y, g y) + (ε : EReal)
    rwa [hg, ← EReal.coe_add]
  · have hsub : x - v = (1-t) • (x-u) + t • (x-z) := by dsimp [v]; module
    have hxz : dist x z ≤ 2 * (ρ : ℝ) := by
      have hzρ : dist 0 z ≤ (ρ : ℝ) := by simpa only [dist_comm 0 z] using hz
      linarith [dist_triangle x 0 z, show dist x 0 ≤ (ρ : ℝ) from hxρ]
    calc
      dist x v ≤ (1-t) * dist x u + t * dist x z := by
        rw [dist_eq_norm, hsub, dist_eq_norm, dist_eq_norm]
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht1)]
          using norm_add_le ((1-t) • (x-u)) (t • (x-z))
      _ ≤ (1-t) * η + t * (2 * ρ) := add_le_add
        (mul_le_mul_of_nonneg_left hxu (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hxz ht)
      _ ≤ η + t * (2 * ρ) := by nlinarith [mul_nonneg ht hη]
      _ = _ := by dsimp [t]; ring

/-- **Theorem 7.69.** Both the rational estimate and its linear upper bound
for the distance between ε-minimizer sets. The two optimal values are given
as real numbers, as follows from properness and attainment. -/
theorem rhoHatDistance_approxArgmin_le_of_convex [FiniteDimensional ℝ E]
    {f g : E → EReal} (hf : IsProper f) (hg : IsProper g)
    (hfc : Convex ℝ (epigraph f)) (hgc : Convex ℝ (epigraph g))
    {m k : ℝ} (hm : (⨅ x, f x) = (m : EReal)) (hk : (⨅ x, g x) = (k : EReal))
    {ρ₀ ρ : ℝ≥0} (hρ : ρ₀ ≤ ρ)
    (hfmin : (argmin f ∩ closedBall (0 : E) (ρ₀ : ℝ)).Nonempty)
    (hgmin : (argmin g ∩ closedBall (0 : E) (ρ₀ : ℝ)).Nonempty)
    (hm₀ : -(ρ₀ : ℝ) ≤ m) (hk₀ : -(ρ₀ : ℝ) ≤ k) {ε : ℝ} (hε : 0 < ε) :
    let η := auxEpiDistance ρ f g
    rhoHatDistance ρ (approxArgmin f ε) (approxArgmin g ε) ≤
        η * (1 + 2 * (ρ : ℝ) / (η + ε / 2)) ∧
      η * (1 + 2 * (ρ : ℝ) / (η + ε / 2)) ≤ (1 + 4 * (ρ : ℝ) / ε) * η := by
  let η := auxEpiDistance ρ f g
  have hη : 0 ≤ η := auxEpiDistance_nonneg hf.1 hg.1
  obtain ⟨z, hzf, hz₀⟩ := hfmin
  obtain ⟨w, hwg, hw₀⟩ := hgmin
  have hρ' : (ρ₀ : ℝ) ≤ ρ := hρ
  have hz := closedBall_subset_closedBall (x := (0 : E)) hρ' hz₀
  have hw := closedBall_subset_closedBall (x := (0 : E)) hρ' hw₀
  have hfz : f z = (m : EReal) := ((mem_argmin_iff_eq_iInf_of_isProper hf _).mp hzf).trans hm
  have hgw : g w = (k : EReal) := ((mem_argmin_iff_eq_iInf_of_isProper hg _).mp hwg).trans hk
  have hmf : -(ρ : ℝ) ≤ m := (neg_le_neg hρ').trans hm₀
  have hkg : -(ρ : ℝ) ≤ k := (neg_le_neg hρ').trans hk₀
  have hne {u : E → EReal} {j : ℝ} {v : E} (hj : (⨅ x, u x) = (j : EReal))
      (hv : u v = (j : EReal)) : (approxArgmin u ε).Nonempty := by
    refine ⟨v, ?_⟩
    change u v ≤ (⨅ x, u x) + (ε : EReal)
    rw [hj, hv, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  let B (e : ℝ) := e * (1 + 2 * (ρ : ℝ) / (e + ε / 2))
  have hbound (e : ℝ) (he : η < e) :
      rhoHatDistance ρ (approxArgmin f ε) (approxArgmin g ε) ≤ B e := by
    obtain ⟨he₀, hfg, hgf⟩ := auxEpiAdmissible_of_lt hf.1 hg.1 he
    have hmk := min_le_of_auxEpiComparison hw hgw hm hkg hgf
    have hkm := min_le_of_auxEpiComparison hz hfz hk hmf hfg
    have hB₀ : 0 ≤ B e := by dsimp [B]; positivity
    exact (rhoHatDistance_le_iff ρ (hne hm hfz) (hne hk hgw) hB₀).mpr
      ⟨approxArgmin_subset_of_auxEpiComparison hε he₀ hgc hw hgw hm hk hmf hmk hfg,
        approxArgmin_subset_of_auxEpiComparison hε he₀ hfc hz hfz hk hm hkg hkm hgf⟩
  have hd : 0 < η + ε / 2 := by linarith
  have hc : ContinuousAt B η := by dsimp [B]; fun_prop (disch := positivity)
  refine ⟨ge_of_tendsto (hc.continuousWithinAt (s := Ioi η)) ?_, ?_⟩
  · exact Filter.mem_of_superset self_mem_nhdsWithin fun e he ↦ hbound e he
  · rw [mul_comm (1 + 4 * (ρ : ℝ) / ε)]
    apply mul_le_mul_of_nonneg_left _ hη
    apply add_le_add_right
    rw [div_le_div_iff₀ hd hε]
    nlinarith [mul_nonneg ρ.coe_nonneg hη]

end RW
