/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Strict smooth minorants for regular subgradients
-/

import RockafellarWets.Chapter6.SmoothGradientWitness
import RockafellarWets.Chapter8.SubderivativeFormulas

open Asymptotics Filter Function Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- A radial modulus of the error in a differentiable affine approximation.
Truncation at the distance gives a global finite bound and agrees with the
untruncated error near the base point. -/
private theorem radial_majorant_of_isLittleO {e : E → ℝ} {x : E}
    (he : e =o[𝓝 x] fun y ↦ y - x) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ 1 θ ∧ θ 0 = 0 ∧ HasDerivAt θ 0 0 ∧
      ∀ᶠ y in 𝓝 x, y ≠ x → ‖e y‖ < θ ‖y - x‖ := by
  let m := fun y ↦ min ‖e y‖ ‖y-x‖
  let S := fun r : ℝ ↦ m '' closedBall x (max r 0)
  let M := fun r ↦ sSup (S r)
  have hne (r : ℝ) : (S r).Nonempty := ⟨m x, x, mem_closedBall_self (le_max_right r 0), rfl⟩
  have hub (r : ℝ) : BddAbove (S r) := by
    refine ⟨max r 0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (min_le_right ..).trans (show ‖y-x‖ ≤ max r 0 by simpa only [mem_closedBall, dist_eq_norm] using hy)
  have hM (r : ℝ) : 0 ≤ M r := by
    have h0 : m x = 0 := by simp [m]
    exact h0 ▸ le_csSup (hub r) (show m x ∈ S r from ⟨x, mem_closedBall_self (le_max_right r 0), rfl⟩)
  have hmono : Monotone M := by
    intro r s hrs
    exact csSup_le_csSup (hub s) (hne r) (image_mono (closedBall_subset_closedBall (max_le_max hrs le_rfl)))
  have hzero : M 0 = 0 := by simp [M, S, m]
  have hsmall : Tendsto (fun r : ℝ ↦ M r / r) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨d, hd, hdsub⟩ := Metric.mem_nhds_iff.mp (he.bound (half_pos hε))
    refine ⟨d, hd, fun r (hr : 0 < r) hrd ↦ ?_⟩
    have hrd' : r < d := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using hrd
    have hsup : M r ≤ (ε/2)*r := by
      apply csSup_le (hne r)
      rintro _ ⟨y, hy, rfl⟩
      have hyr : ‖y-x‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm, max_eq_left hr.le] using hy
      have hye : ‖e y‖ ≤ (ε/2)*‖y-x‖ := hdsub (mem_ball.mpr (dist_eq_norm y x ▸ hyr.trans_lt hrd'))
      exact (min_le_left ..).trans (hye.trans (mul_le_mul_of_nonneg_left hyr (half_pos hε).le))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hM r) hr.le)]
    exact ((div_le_iff₀ hr).mpr hsup).trans_lt (half_lt_self hε)
  obtain ⟨θ, hc, hz, hd, hstrict, -, -⟩ := exists_contDiff_one_strict_majorant (hmono.monotoneOn _) hzero hsmall
  refine ⟨θ, hc, hz, hd, ?_⟩
  filter_upwards [he.bound one_pos] with y hy hyx
  have hle := le_csSup (hub ‖y-x‖) (show m y ∈ S ‖y-x‖ from ⟨y, by simp [mem_closedBall, dist_eq_norm], rfl⟩)
  have hmy : m y = ‖e y‖ := min_eq_left (by simpa only [one_mul] using hy)
  exact hmy ▸ hle.trans_lt (hstrict _ (norm_pos_iff.mpr (sub_ne_zero.mpr hyx)))

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Proposition 8.5**, strict smooth form. The minorant can be chosen
globally continuously differentiable and strictly below the function at
every other point of a neighborhood. -/
theorem mem_regularSubdifferential_iff_exists_strict_smooth_minorant {f : E → EReal} {x v : E}
    {c : ℝ} (hx : f x = c) :
    v ∈ regularSubdifferential f x ↔
      ∃ h : E → ℝ, ContDiff ℝ 1 h ∧ h x = c ∧ HasGradientAt h v x ∧
        ∀ᶠ y in 𝓝 x, y ≠ x → (h y : EReal) < f y := by
  rw [mem_regularSubdifferential_iff_exists_hasGradientAt hx]
  constructor
  · rintro ⟨g, hle, hg, hgrad⟩
    let e := fun y ↦ g y - g x - ⟪v, y-x⟫_ℝ
    have he : e =o[𝓝 x] fun y ↦ y-x := hasGradientAt_iff_isLittleO.mp hgrad
    obtain ⟨θ, hc, hz, hd, hstrict⟩ := radial_majorant_of_isLittleO he
    let h := fun y ↦ c + ⟪v, y-x⟫_ℝ - θ ‖y-x‖
    have hh : h x = c := by simp [h, hz]
    refine ⟨h, (contDiff_const.add (ContDiff.inner ℝ contDiff_const (contDiff_id.sub contDiff_const))
      ).sub (contDiff_one_comp_norm_sub hc hd x), hh, ?_, ?_⟩
    · rw [hasGradientAt_iff_isLittleO]
      have ht : (fun t : ℝ ↦ θ t) =o[𝓝 0] fun t : ℝ ↦ t := by simpa [hz] using hasDerivAt_iff_isLittleO.mp hd
      have hn : Tendsto (fun y : E ↦ ‖y-x‖) (𝓝 x) (𝓝 0) := by
        simpa using ((continuous_id.sub (continuous_const (y := x))).norm.tendsto x)
      have hcomp : (fun y ↦ θ ‖y-x‖) =o[𝓝 x] fun y ↦ ‖y-x‖ := ht.comp_tendsto hn
      apply (isLittleO_norm_right.mp hcomp).neg_left.congr_left
      intro y
      rw [hh]
      dsimp [h]
      ring
    · filter_upwards [hstrict, hle] with y hy hf hyx
      have herr := hy hyx
      rw [Real.norm_eq_abs] at herr
      have hlow := neg_abs_le (e y)
      apply (EReal.coe_lt_coe_iff.mpr ?_).trans_le hf
      dsimp [h, e] at *
      linarith
  · rintro ⟨h, -, he, hg, hstrict⟩
    refine ⟨h, ?_, he, hg⟩
    filter_upwards [hstrict] with y hy
    rcases eq_or_ne y x with rfl | hyx
    · rw [he, hx]
    · exact (hy hyx).le

end RW
