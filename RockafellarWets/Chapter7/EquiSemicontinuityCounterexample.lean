/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A qualification to Exercise 7.9

The epigraphical formulation in 5.38 only tests bounded heights. When the
values at the base point tend to −∞, the scalar estimate printed in 7.9(a)
can distinguish values far below every fixed test interval. For example,
take the finite continuous functions `fₙ(y) = −n − n|y|` at the origin.
-/
import RockafellarWets.Chapter5.Equicontinuity
import RockafellarWets.Chapter5.ProfileMappings

open Filter Metric Set Topology

namespace RW

/-- Each function is Lipschitz, with slope magnitude growing with its index. -/
def fallingProfileExample (n : ℕ) (y : ℝ) : EReal := ((-(n : ℝ) - n * |y| : ℝ) : EReal)

theorem continuous_fallingProfileExample (n : ℕ) : Continuous (fallingProfileExample n) :=
  continuous_coe_real_ereal.comp (continuous_const.sub (continuous_const.mul continuous_abs))

/-- The profiles satisfy even the all-indices version of equi-osc. Once
`n ≥ ρ`, every height tested by the cutoff already lies in the base profile. -/
theorem svEquiOscWithinAt_fallingProfileExample :
    SvEquiOscWithinAt (fun n ↦ epiProfile (fallingProfileExample n)) univ 0 := by
  intro ε hε ρ hρ
  let δ := ε / (ρ + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  refine ⟨ball 0 δ, ball_mem_nhds _ hδ, ?_⟩
  intro n y hy t ht
  have hfy : -(n : ℝ) - n * |y| ≤ t := EReal.coe_le_coe_iff.1 ht.1
  have hty : |t| ≤ ρ := by simpa [mem_closedBall, Real.dist_eq] using ht.2
  have hyδ : |y| < δ := by simpa [mem_ball, Real.dist_eq] using hy.1
  by_cases hbase : -(n : ℝ) ≤ t
  · exact mem_thickening_iff.2 ⟨t, by
      simpa [fallingProfileExample] using EReal.coe_le_coe_iff.2 hbase,
      by simpa using hε⟩
  · have hnρ : (n : ℝ) < ρ := by linarith [(abs_le.1 hty).1]
    have hstep : (n : ℝ) * |y| < ε := calc
      (n : ℝ) * |y| ≤ (ρ + 1) * |y| := by gcongr; linarith
      _ < (ρ + 1) * δ := mul_lt_mul_of_pos_left hyδ (by linarith)
      _ = ε := by dsimp [δ]; field_simp
    refine mem_thickening_iff.2 ⟨-(n : ℝ), by simp [fallingProfileExample], ?_⟩
    rw [Real.dist_eq, abs_of_neg (by linarith : t - -(n : ℝ) < 0)]
    linarith

/-- Even the eventual version of the scalar estimate fails for
`ρ = ε = 1`, on every positive-radius closed ball about the origin. -/
theorem not_eventually_lower_estimate_fallingProfileExample (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ᶠ n : ℕ in atTop, min (fallingProfileExample n 0 - 1) 1 ≤
      ⨅ y ∈ closedBall (0 : ℝ) δ, fallingProfileExample n y := by
  intro h
  obtain ⟨n, hn, hbound⟩ := (h.and (tendsto_natCast_atTop_atTop.eventually_gt_atTop
    (1 / δ))).exists
  have hlarge : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδ).1 hbound
  have hy : δ ∈ closedBall (0 : ℝ) δ := by simp [mem_closedBall, abs_of_pos hδ]
  have hn' := hn.trans (iInf₂_le δ hy)
  have hmin : (-(n : ℝ) - 1 : ℝ) ≤ 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hzero : fallingProfileExample n 0 = ((-(n : ℝ) : ℝ) : EReal) := by
    simp [fallingProfileExample]
  rw [hzero, ← EReal.coe_one, ← EReal.coe_sub, min_eq_left (EReal.coe_le_coe_iff.2 hmin)] at hn'
  have hcoef : ((-(n : ℝ) - 1 : ℝ) : EReal) ≤ ((-(n : ℝ) - n * δ : ℝ) : EReal) := by
    simpa only [fallingProfileExample, abs_of_pos hδ] using hn'
  linarith [EReal.coe_le_coe_iff.1 hcoef]

/-- Negating the same example gives equi-osc hypo profiles. -/
theorem svEquiOscWithinAt_neg_fallingProfileExample :
    SvEquiOscWithinAt (fun n ↦ hypoProfile (fun y ↦ -fallingProfileExample n y)) univ 0 := by
  intro ε hε ρ hρ
  obtain ⟨V, hV, hnear⟩ := svEquiOscWithinAt_fallingProfileExample ε hε ρ hρ
  refine ⟨V, hV, ?_⟩
  intro n y hy t ht
  have hm : -t ∈ epiProfile (fallingProfileExample n) y := by
    rw [mem_epiProfile, EReal.coe_neg]
    exact EReal.le_neg.1 ht.1
  have hb : -t ∈ closedBall (0 : ℝ) ρ := by
    simpa only [mem_closedBall_zero_iff, norm_neg] using ht.2
  obtain ⟨s, hs, hdist⟩ := mem_thickening_iff.1 (hnear n y hy ⟨hm, hb⟩)
  refine mem_thickening_iff.2 ⟨-s, ?_, ?_⟩
  · rw [mem_hypoProfile, EReal.coe_neg, EReal.neg_le_neg_iff]
    exact hs
  · rw [Real.dist_eq, abs_lt] at hdist ⊢
    constructor <;> linarith

/-- The printed upper estimate from 7.9(b) fails on every ball as well. -/
theorem not_eventually_upper_estimate_neg_fallingProfileExample (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ᶠ n : ℕ in atTop, (⨆ y ∈ closedBall (0 : ℝ) δ, -fallingProfileExample n y) ≤
      max (-fallingProfileExample n 0 + 1) (-1) := by
  intro h
  obtain ⟨n, hn, hbound⟩ := (h.and (tendsto_natCast_atTop_atTop.eventually_gt_atTop
    (1 / δ))).exists
  have hlarge : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδ).1 hbound
  have hy : δ ∈ closedBall (0 : ℝ) δ := by simp [mem_closedBall, abs_of_pos hδ]
  have hn' := (le_iSup₂ δ hy).trans hn
  have hmax : (-(1 : ℝ)) ≤ -(-(n : ℝ)) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hzero : fallingProfileExample n 0 = ((-(n : ℝ) : ℝ) : EReal) := by
    simp [fallingProfileExample]
  have hsum : -fallingProfileExample n 0 + 1 = ((-(-(n : ℝ)) + 1 : ℝ) : EReal) := by
    simp [hzero, EReal.coe_add]
  have hmax' : (-1 : EReal) ≤ ((-(-(n : ℝ)) + 1 : ℝ) : EReal) := by
    simpa only [EReal.coe_neg, EReal.coe_one] using EReal.coe_le_coe_iff.2 hmax
  rw [hsum, max_eq_left hmax'] at hn'
  have hcoef : ((-(-(n : ℝ) - n * δ) : ℝ) : EReal) ≤ ((-(-(n : ℝ)) + 1 : ℝ) : EReal) := by
    simpa only [fallingProfileExample, abs_of_pos hδ, EReal.coe_neg] using hn'
  linarith [EReal.coe_le_coe_iff.1 hcoef]

end RW
