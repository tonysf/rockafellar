/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Approximation of subgradients by proximal subgradients

Corollary 8.47(a), first statement: for `f` lsc and finite at `x̄` and
`v̄ ∈ ∂f(x̄)`, for every `δ > 0` there are `x ∈ IB(x̄, δ) ∩ dom f` with
`|f(x) - f(x̄)| ≤ δ` and a proximal subgradient `v` of `f` at `x` with
`v ∈ IB(v̄, δ)`.  As in the book, `(v̄, -1)` is a normal to `epi f` (8.9),
it is approximated by proximal normals (6.18(a)), these have negative
vertical component and are rescaled to height `-1`, and 8.46(a) turns them
into proximal subgradients.  Properness of `f` is not needed.

The remaining clauses are proved in ProximalSubgradientLimits and
MonotoneProximalRecovery by first approximating horizontal normals with
negative-height normals.
-/

import RockafellarWets.Chapter8.ProximalSubgradientEpigraphs
import RockafellarWets.Chapter8.EpigraphNormals
import RockafellarWets.Chapter6.NormalApproximation

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean epigraph of Definition 7.25 is the one used for 8.9. -/
theorem l2Epigraph_eq_euclideanEpigraph (f : E → EReal) :
    l2Epigraph f = euclideanEpigraph f := rfl

omit [InnerProductSpace ℝ E] in
theorem norm_fst_le_norm_l2 (q : WithLp 2 (E × ℝ)) : ‖q.fst‖ ≤ ‖q‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [WithLp.prod_norm_sq_eq_of_L2 q]
  nlinarith [sq_nonneg ‖q.snd‖]

omit [InnerProductSpace ℝ E] in
theorem abs_snd_le_norm_l2 (q : WithLp 2 (E × ℝ)) : |q.snd| ≤ ‖q‖ := by
  rw [← Real.norm_eq_abs]
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [WithLp.prod_norm_sq_eq_of_L2 q]
  nlinarith [sq_nonneg ‖q.fst‖]

variable [FiniteDimensional ℝ E]

/-- **Corollary 8.47(a)**, first statement: subgradients of an lsc function are
approximated by proximal subgradients at nearby points with nearby values. -/
theorem exists_mem_proximalSubdifferential_close {f : E → EReal} (hf : LowerSemicontinuous f)
    {x v : E} {c : ℝ} (hxc : f x = c) (hv : v ∈ subdifferential f x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x' v' : E, ∃ c' : ℝ, f x' = c' ∧ ‖x' - x‖ ≤ δ ∧ |c' - c| ≤ δ ∧
      v' ∈ proximalSubdifferential f x' ∧ ‖v' - v‖ ≤ δ := by
  have hclosed : IsClosed (euclideanEpigraph f) :=
    (isClosed_epigraph_of_lsc_ereal f hf).preimage (l2ProdEquiv E).continuous
  have hN : WithLp.toLp 2 (v, (-1 : ℝ)) ∈
      normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) :=
    (mem_subdifferential_iff_epigraph_normal hxc).1 hv
  set ε : ℝ := min (1 / 2) (δ / (2 * ‖v‖ + 3)) with hε_def
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε2 : ε ≤ 1 / 2 := min_le_left _ _
  have hεδ : ε * (2 * ‖v‖ + 3) ≤ δ := by
    have := min_le_right (1 / 2 : ℝ) (δ / (2 * ‖v‖ + 3))
    rw [← hε_def] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hεδ' : ε ≤ δ := by nlinarith [mul_nonneg hε.le (norm_nonneg v)]
  obtain ⟨z, u, hzE, hu, hz, hu'⟩ :=
    exists_mem_proximalNormalCone_close_of_mem_normalCone hclosed hN hε
  obtain ⟨⟨y, α⟩, rfl⟩ : ∃ p : E × ℝ, WithLp.toLp 2 p = z := ⟨WithLp.ofLp z, by simp⟩
  obtain ⟨⟨u₁, u₂⟩, rfl⟩ : ∃ p : E × ℝ, WithLp.toLp 2 p = u := ⟨WithLp.ofLp u, by simp⟩
  -- coordinate estimates
  have hyx : ‖y - x‖ < ε := by
    have h1 := norm_fst_le_norm_l2 (WithLp.toLp 2 (y, α) - WithLp.toLp 2 (x, c))
    have h2 : (WithLp.toLp 2 (y, α) - WithLp.toLp 2 (x, c)).fst = y - x := rfl
    rw [h2] at h1
    linarith
  have hαc : |α - c| < ε := by
    have h1 := abs_snd_le_norm_l2 (WithLp.toLp 2 (y, α) - WithLp.toLp 2 (x, c))
    have h2 : (WithLp.toLp 2 (y, α) - WithLp.toLp 2 (x, c)).snd = α - c := rfl
    rw [h2] at h1
    linarith
  have hu1 : ‖u₁ - v‖ < ε := by
    have h1 := norm_fst_le_norm_l2 (WithLp.toLp 2 (u₁, u₂) - WithLp.toLp 2 (v, (-1 : ℝ)))
    have h2 : (WithLp.toLp 2 (u₁, u₂) - WithLp.toLp 2 (v, (-1 : ℝ))).fst = u₁ - v := rfl
    rw [h2] at h1
    linarith
  have hu2 : |u₂ - -1| < ε := by
    have h1 := abs_snd_le_norm_l2 (WithLp.toLp 2 (u₁, u₂) - WithLp.toLp 2 (v, (-1 : ℝ)))
    have h2 : (WithLp.toLp 2 (u₁, u₂) - WithLp.toLp 2 (v, (-1 : ℝ))).snd = u₂ - -1 := rfl
    rw [h2] at h1
    linarith
  rw [sub_neg_eq_add, abs_lt] at hu2
  set t : ℝ := -u₂ with ht_def
  have ht : 1 / 2 ≤ t := by linarith [hu2.2]
  have htpos : 0 < t := by linarith
  -- rescale the proximal normal to height `-1`
  have hscaled : WithLp.toLp 2 (t⁻¹ • u₁, (-1 : ℝ)) ∈
      proximalNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (y, α)) := by
    have hs := (isCone_proximalNormalCone hzE).2 hu (inv_pos.2 htpos)
    convert hs using 1
    rw [← WithLp.toLp_smul, Prod.smul_mk, smul_eq_mul, ht_def]
    congr 2
    have hu₂ne : u₂ ≠ 0 := ne_of_lt (by linarith)
    field_simp
  have hfy : f y = α :=
    value_eq_of_mem_regularNormalCone_epigraph_of_neg
      (proximalNormalCone_subset_regularNormalCone hscaled) (by norm_num)
  have hprox : t⁻¹ • u₁ ∈ proximalSubdifferential f y :=
    (mem_proximalSubdifferential_iff_mem_proximalNormalCone_l2Epigraph hfy).2 hscaled
  refine ⟨y, t⁻¹ • u₁, α, hfy, by linarith, by linarith, hprox, ?_⟩
  -- the rescaled vector stays close to `v`
  have hs1 : |t⁻¹ - 1| ≤ 2 * ε := by
    have hrw : t⁻¹ - 1 = (1 - t) / t := by field_simp
    rw [hrw, abs_div, abs_of_pos htpos, div_le_iff₀ htpos, abs_le]
    constructor <;> nlinarith [hu2.1, hu2.2]
  have hnu1 : ‖u₁‖ ≤ ‖v‖ + ε := by
    have := norm_sub_norm_le u₁ v
    linarith
  calc ‖t⁻¹ • u₁ - v‖ = ‖(t⁻¹ - 1) • u₁ + (u₁ - v)‖ := by
        congr 1
        rw [sub_smul, one_smul]
        abel
    _ ≤ ‖(t⁻¹ - 1) • u₁‖ + ‖u₁ - v‖ := norm_add_le _ _
    _ ≤ 2 * ε * (‖v‖ + ε) + ε := by
        rw [norm_smul, Real.norm_eq_abs]
        have := mul_le_mul hs1 hnu1 (norm_nonneg _) (by positivity)
        linarith
    _ ≤ δ := by nlinarith [norm_nonneg v]

end RW
