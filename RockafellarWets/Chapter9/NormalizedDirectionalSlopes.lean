/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: The normalized secant criterion in Exercise 9.42
-/

import RockafellarWets.Chapter9.DirectionalLipschitzFunctions

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → EReal} {x w : E} {c : ℝ}

/-- The secant quotient with denominator the length of the displacement.
For positive `t` and nonzero `v`, this is
`[f(y+t • v)-f(y)] / ‖t • v‖`. -/
noncomputable def normalizedSecantQuotient (f : E → EReal) (y : E) (t : ℝ) (v : E) : EReal :=
  differenceQuotient f y (t*‖v‖) (‖v‖⁻¹ • v)

theorem normalizedSecantQuotient_le_coe_iff {y v : E} {t a d : ℝ}
    (hy : f y = d) (ht : 0 < t) (hv : v ≠ 0) :
    normalizedSecantQuotient f y t v ≤ (a:EReal) ↔
      f (y+t • v) ≤ ((d+t*‖v‖*a:ℝ):EReal) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have he : (t*‖v‖) • (‖v‖⁻¹ • v) = t • v := by
    rw [smul_smul,mul_assoc,mul_inv_cancel₀ hn,mul_one]
  simpa only [normalizedSecantQuotient,he] using
    (differenceQuotient_le_coe_iff (w := ‖v‖⁻¹ • v) hy (mul_pos ht (norm_pos_iff.mpr hv)))

/-- The directional upper limit of normalized secant quotients. The base
point converges attentively and the nonzero displacement tends to zero
in the direction of `w`, through `t → 0+` and `v → w`. -/
noncomputable def normalizedDirectionalSlope (f : E → EReal) (x w : E) : EReal :=
  limsup (fun q : (E × ℝ) × E ↦ normalizedSecantQuotient f q.1.1 q.1.2 q.2)
    ((attentiveNhds f x ×ˢ 𝓝[>] (0:ℝ)) ×ˢ 𝓝 w)

/-- Normalizing by the displacement length preserves finiteness of the
upper directional slope in every nonzero direction. -/
theorem normalizedDirectionalSlope_lt_top_iff (hx : f x = c) (hw : w ≠ 0) :
    normalizedDirectionalSlope f x w < ⊤ ↔ upperDirectionalSlope f x w < ⊤ := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hnorm : ∀ᶠ v : E in 𝓝 w, ‖w‖/2 < ‖v‖ ∧ ‖v‖ < 2*‖w‖ :=
    continuous_norm.continuousAt.eventually
      (Ioo_mem_nhds (by linarith : ‖w‖/2 < ‖w‖) (by linarith : ‖w‖ < 2*‖w‖))
  have ht : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
  have hfin := eventually_finite_attentiveNhds hx
  constructor
  · intro h
    obtain ⟨a,ha,-⟩ := EReal.exists_between_coe_real h
    have hev := eventually_lt_of_limsup_lt ha
    have hbound : upperDirectionalSlope f x w ≤ ((2*‖w‖*max a 0:ℝ):EReal) := by
      apply limsup_le_of_le (by isBoundedDefault)
      filter_upwards [hev,(tendsto_fst.comp tendsto_fst).eventually hfin,
        (tendsto_snd.comp tendsto_fst).eventually ht,tendsto_snd.eventually hnorm] with q hq hqfin hqt hqn
      have hqnpos : 0 < ‖q.2‖ := by linarith
      have hval := (normalizedSecantQuotient_le_coe_iff hqfin hqt (norm_pos_iff.mp hqnpos)).mp hq.le
      apply (differenceQuotient_le_coe_iff hqfin hqt).mpr
      apply hval.trans (EReal.coe_le_coe_iff.mpr ?_)
      have hna : ‖q.2‖*a ≤ 2*‖w‖*max a 0 := by
        calc
          ‖q.2‖*a ≤ ‖q.2‖*max a 0 := mul_le_mul_of_nonneg_left (le_max_left ..) hqnpos.le
          _ ≤ 2*‖w‖*max a 0 := mul_le_mul_of_nonneg_right hqn.2.le (le_max_right ..)
      nlinarith [mul_le_mul_of_nonneg_left hna hqt.le]
    exact hbound.trans_lt (EReal.coe_lt_top _)
  · intro h
    obtain ⟨a,ha,-⟩ := EReal.exists_between_coe_real h
    have hev := eventually_lt_of_limsup_lt ha
    let B := max a 0 / (‖w‖/2)
    have hB : 0 ≤ B := div_nonneg (le_max_right ..) (by positivity)
    have hBeq : ‖w‖/2*B = max a 0 := by dsimp [B]; field_simp
    have hbound : normalizedDirectionalSlope f x w ≤ (B:EReal) := by
      apply limsup_le_of_le (by isBoundedDefault)
      filter_upwards [hev,(tendsto_fst.comp tendsto_fst).eventually hfin,
        (tendsto_snd.comp tendsto_fst).eventually ht,tendsto_snd.eventually hnorm] with q hq hqfin hqt hqn
      have hqnpos : 0 < ‖q.2‖ := by linarith
      have hval := (differenceQuotient_le_coe_iff hqfin hqt).mp hq.le
      apply (normalizedSecantQuotient_le_coe_iff hqfin hqt (norm_pos_iff.mp hqnpos)).mpr
      apply hval.trans (EReal.coe_le_coe_iff.mpr ?_)
      have hna : a ≤ ‖q.2‖*B := by nlinarith [le_max_left a 0]
      nlinarith [mul_le_mul_of_nonneg_left hna hqt.le]
    exact hbound.trans_lt (EReal.coe_lt_top _)

variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- **Exercise 9.42(b)** in the printed normalized-secant formulation. -/
theorem isDirectionallyLipschitzAt_iff_exists_normalizedSlope (hx : f x = c)
    (hl : IsLocallyLscAt f x) :
    IsDirectionallyLipschitzAt f x ↔ ∃ w ≠ 0, normalizedDirectionalSlope f x w < ⊤ := by
  rw [isDirectionallyLipschitzAt_iff_exists_nonzero_upperSlope hx hl]
  exact exists_congr (fun w ↦ and_congr_right (fun hw ↦ (normalizedDirectionalSlope_lt_top_iff hx hw).symm))

end RW
