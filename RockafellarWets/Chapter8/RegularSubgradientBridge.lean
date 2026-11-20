/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Regular subgradients from subderivatives

Exercise 8.4, formula 8(7):
`∂̂f(x̄) = {v | ⟪v, w⟫ ≤ df(x̄)(w) for all w}` at every point where `f(x̄)` is
finite.  Here `df(x̄)` is the subderivative of Definition 8.1, which is the
function `subderivative` of formula 7(21).

The inclusion `⊆` passes the regular subgradient inequality 8(3) through the
difference quotients.  The inclusion `⊇` is the compactness argument of the
book's guide: the strict inequalities `⟪v, w⟫ - ε < df(x̄)(w)` persist on
neighborhoods in `(τ, w)`, finitely many of which cover the unit sphere, and
this bounds the difference quotients uniformly in the direction.
-/

import RockafellarWets.Chapter8.Subgradients
import RockafellarWets.Chapter7.EpiDerivatives

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Exercise 8.4**, the inclusion `⊆` of 8(7): a regular subgradient pairs
with every direction below the subderivative. -/
theorem inner_le_subderivative_of_mem_regularSubdifferential {f : E → EReal} {x v : E}
    (hv : v ∈ regularSubdifferential f x) (w : E) :
    ((⟪v, w⟫_ℝ : ℝ) : EReal) ≤ subderivative f x w := by
  obtain ⟨c, hxc, hreg⟩ := hv
  by_contra hlt
  push_neg at hlt
  obtain ⟨b, hb1, hb2⟩ := EReal.exists_between_coe_real hlt
  have hbw : b < ⟪v, w⟫_ℝ := EReal.coe_lt_coe_iff.1 hb2
  set η : ℝ := ⟪v, w⟫_ℝ - b with hη_def
  have hη : 0 < η := sub_pos.2 hbw
  have hM : 0 < ‖w‖ + 1 := by positivity
  set ε : ℝ := η / (2 * (‖w‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hεw : ε * (‖w‖ + 1) = η / 2 := by
    rw [hε_def, div_mul_eq_mul_div, mul_div_mul_right η 2 hM.ne']
  have hpath := tendsto_add_smul_nhds x w
  have h1 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      ((c + ⟪v, x + p.1 • p.2 - x⟫_ℝ - ε * ‖x + p.1 • p.2 - x‖ : ℝ) : EReal) ≤
        f (x + p.1 • p.2) :=
    hpath.eventually (hreg ε hε)
  have h2 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, p.2 ∈ ball w 1 :=
    tendsto_snd.eventually (ball_mem_nhds w one_pos)
  have h3' : ∀ᶠ u in 𝓝 w, ⟪v, u⟫_ℝ ∈ ball ⟪v, w⟫_ℝ (η / 2) :=
    ((continuous_const.inner continuous_id).tendsto w) (ball_mem_nhds _ (half_pos hη))
  have h3 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, ⟪v, p.2⟫_ℝ ∈ ball ⟪v, w⟫_ℝ (η / 2) :=
    tendsto_snd.eventually h3'
  have h4 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) ≤ differenceQuotient f x p.1 p.2 := by
    filter_upwards [h1, h2, h3, h4] with p hp1 hp2 hp3 hp4
    obtain ⟨τ, u⟩ := p
    simp only [add_sub_cancel_left] at hp1
    simp only [mem_ball, dist_eq_norm] at hp2
    simp only [mem_ball, Real.dist_eq] at hp3
    change 0 < τ at hp4
    by_contra hcon
    push_neg at hcon
    have hle := (differenceQuotient_le_coe_iff hxc hp4).1 hcon.le
    have hreal := EReal.coe_le_coe_iff.1 (hp1.trans hle)
    rw [real_inner_smul_right, norm_smul, Real.norm_of_nonneg hp4.le] at hreal
    have hu : ‖u‖ < ‖w‖ + 1 := by linarith [norm_sub_norm_le u w]
    rw [abs_lt] at hp3
    have hεu : ε * ‖u‖ ≤ η / 2 := by
      rw [← hεw]
      exact mul_le_mul_of_nonneg_left hu.le hε.le
    have key : τ * (⟪v, u⟫_ℝ - ε * ‖u‖) ≤ τ * b := by linarith
    have key2 : ⟪v, u⟫_ℝ - ε * ‖u‖ ≤ b := le_of_mul_le_mul_left key hp4
    linarith [hp3.1]
  have hle : (b : EReal) ≤ subderivative f x w := le_liminf_of_le (h := hev)
  exact lt_irrefl _ (hb1.trans_le hle)

/-- **Exercise 8.4**, the inclusion `⊇` of 8(7), by the compactness argument
of the book's guide. -/
theorem mem_regularSubdifferential_of_inner_le_subderivative [FiniteDimensional ℝ E]
    {f : E → EReal} {x v : E} {c : ℝ} (hxc : f x = c)
    (h : ∀ w, ((⟪v, w⟫_ℝ : ℝ) : EReal) ≤ subderivative f x w) :
    v ∈ regularSubdifferential f x := by
  refine ⟨c, hxc, fun ε hε ↦ ?_⟩
  have hS : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝ˢ (sphere (0 : E) 1),
      ((⟪v, p.2⟫_ℝ - ε : ℝ) : EReal) < differenceQuotient f x p.1 p.2 := by
    refine (isCompact_sphere (0 : E) 1).mem_prod_nhdsSet_of_forall fun w _ ↦ ?_
    have hlt : ((⟪v, w⟫_ℝ - ε / 2 : ℝ) : EReal) < subderivative f x w :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) (h w)
    have h1 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
        ((⟪v, w⟫_ℝ - ε / 2 : ℝ) : EReal) < differenceQuotient f x p.1 p.2 :=
      eventually_lt_of_lt_liminf hlt
    have h2' : ∀ᶠ u in 𝓝 w, ⟪v, u⟫_ℝ ∈ ball ⟪v, w⟫_ℝ (ε / 2) :=
      ((continuous_const.inner continuous_id).tendsto w) (ball_mem_nhds _ (half_pos hε))
    filter_upwards [h1, tendsto_snd.eventually h2'] with p hp1 hp2
    rw [mem_ball, Real.dist_eq, abs_lt] at hp2
    exact lt_trans (EReal.coe_lt_coe_iff.2 (by linarith [hp2.2])) hp1
  have hU : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ w ∈ sphere (0 : E) 1,
      ((⟪v, w⟫_ℝ - ε : ℝ) : EReal) < differenceQuotient f x τ w := by
    filter_upwards [hS.curry] with τ hτ w hw
    exact hτ.self_of_nhdsSet w hw
  obtain ⟨δ, hδ, hδU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  filter_upwards [ball_mem_nhds x hδ] with y hy
  rcases eq_or_ne y x with rfl | hyx
  · rw [hxc]
    simp
  · have hτ : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
    rw [mem_ball, dist_eq_norm] at hy
    set τ := ‖y - x‖ with hτ_def
    set z : E := τ⁻¹ • (y - x) with hz_def
    have hz : z ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, hz_def, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 hτ.le), ← hτ_def, inv_mul_cancel₀ hτ.ne']
    have hτz : τ • z = y - x := by
      rw [hz_def, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
    have hmem := hδU ⟨hτ, hy⟩ z hz
    rw [← not_le, differenceQuotient_le_coe_iff hxc hτ, hτz, add_sub_cancel] at hmem
    have hinner : ⟪v, y - x⟫_ℝ = τ * ⟪v, z⟫_ℝ := by
      rw [← hτz, real_inner_smul_right]
    have heq : c + τ * (⟪v, z⟫_ℝ - ε) = c + ⟪v, y - x⟫_ℝ - ε * τ := by
      rw [hinner]
      ring
    rw [heq] at hmem
    exact (not_le.1 hmem).le

/-- **Exercise 8.4**, formula 8(7): at a point where `f` is finite, the
regular subgradients are exactly the vectors `v` with `⟪v, w⟫ ≤ df(x̄)(w)` for
all `w`. -/
theorem regularSubdifferential_eq_setOf_inner_le_subderivative [FiniteDimensional ℝ E]
    {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    regularSubdifferential f x = {v | ∀ w, ((⟪v, w⟫_ℝ : ℝ) : EReal) ≤ subderivative f x w} := by
  ext v
  exact ⟨fun hv w ↦ inner_le_subderivative_of_mem_regularSubdifferential hv w,
    mem_regularSubdifferential_of_inner_le_subderivative hxc⟩

/-- **Exercise 8.4**, membership form of 8(7). -/
theorem mem_regularSubdifferential_iff_inner_le_subderivative [FiniteDimensional ℝ E]
    {f : E → EReal} {x v : E} {c : ℝ} (hxc : f x = c) :
    v ∈ regularSubdifferential f x ↔ ∀ w, ((⟪v, w⟫_ℝ : ℝ) : EReal) ≤ subderivative f x w := by
  rw [regularSubdifferential_eq_setOf_inner_le_subderivative hxc]
  rfl

end RW
