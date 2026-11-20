/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Proximal subgradients and proximal normals to epigraphs

Proposition 8.46(a): `v` is a proximal subgradient of `f` at `x̄` if and only if
`(v, -1)` is a proximal normal to `epi f` at `(x̄, f(x̄))`.  Proximal normals are
Euclidean notions, so the epigraph is taken in `WithLp 2 (E × ℝ)`
(`l2Epigraph`, as in Definition 7.25).

Both directions are proved from the global quadratic-support description of
proximal normals (`mem_proximalNormalCone_iff_quadratic_support`):
* a local quadratic minorant 8(30) gives the support inequality near `x̄`
  directly, and far from `x̄` the linear terms are dominated by quadratic
  ones (the same device as in the proof of 8.46(b));
* conversely, a point `(y, α)` of the epigraph with `α` below the quadratic
  minorant `f(x̄) + ⟪v, y - x̄⟫ - K|y - x̄|²` would violate the support
  inequality once `K` is large and `y` is close to `x̄`.  This replaces the
  book's appeal to the upper surface of the supporting ball and to (c).
-/

import RockafellarWets.Chapter8.ProximalSubgradientMinorants
import RockafellarWets.Chapter7.SubdifferentialRegularity

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_toLp_neg_one_sub (v x y : E) (c α : ℝ) :
    ⟪WithLp.toLp 2 (v, (-1 : ℝ)), WithLp.toLp 2 (y, α) - WithLp.toLp 2 (x, c)⟫_ℝ =
      ⟪v, y - x⟫_ℝ - (α - c) := by
  rw [← WithLp.toLp_sub, Prod.mk_sub_mk, WithLp.prod_inner_apply]
  have h1 : ⟪(-1 : ℝ), α - c⟫_ℝ = -(α - c) := by simp
  simp only [h1]
  ring

omit [InnerProductSpace ℝ E] in
theorem norm_toLp_sub_sq (x y : E) (c α : ℝ) :
    ‖WithLp.toLp 2 (y, α) - WithLp.toLp 2 (x, c)‖ ^ 2 = ‖y - x‖ ^ 2 + (α - c) ^ 2 := by
  rw [← WithLp.toLp_sub, Prod.mk_sub_mk, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs]

/-- **Proposition 8.46(a)**: `v` is a proximal subgradient of `f` at `x̄` if and
only if `(v, -1)` is a proximal normal to `epi f` at `(x̄, f(x̄))`. -/
theorem mem_proximalSubdifferential_iff_mem_proximalNormalCone_l2Epigraph {f : E → EReal}
    {x v : E} {c : ℝ} (hxc : f x = c) :
    v ∈ proximalSubdifferential f x ↔
      WithLp.toLp 2 (v, (-1 : ℝ)) ∈ proximalNormalCone (l2Epigraph f) (WithLp.toLp 2 (x, c)) := by
  have hmemE : ∀ (y : E) (α : ℝ), WithLp.toLp 2 (y, α) ∈ l2Epigraph f ↔ f y ≤ α :=
    fun y α ↦ Iff.rfl
  have hz : WithLp.toLp 2 (x, c) ∈ l2Epigraph f := (hmemE x c).2 (le_of_eq hxc)
  rw [mem_proximalNormalCone_iff_quadratic_support]
  constructor
  · rintro ⟨c', hc', ρ, hρ, δ, hδ, hle⟩
    have hcc : c' = c := by
      rw [hxc] at hc'
      exact (EReal.coe_injective hc').symm
    subst hcc
    refine ⟨hz, max (ρ / 2) ((‖v‖ + 1) / δ), lt_max_of_lt_left (by positivity), ?_⟩
    intro z hzE
    obtain ⟨⟨y, α⟩, rfl⟩ : ∃ p : E × ℝ, WithLp.toLp 2 p = z := ⟨WithLp.ofLp z, by simp⟩
    have hyα : f y ≤ α := (hmemE y α).1 hzE
    rw [inner_toLp_neg_one_sub, norm_toLp_sub_sq]
    have hq1 : 0 ≤ ‖y - x‖ ^ 2 := by positivity
    have hq2 : 0 ≤ (α - c') ^ 2 := by positivity
    have hε0 : 0 ≤ max (ρ / 2) ((‖v‖ + 1) / δ) := le_trans (by positivity) (le_max_left _ _)
    rcases le_or_gt ‖y - x‖ δ with hyδ | hyδ
    · have h1 := EReal.coe_le_coe_iff.1 (le_trans (hle y hyδ) hyα)
      have h2 : ρ / 2 * ‖y - x‖ ^ 2 ≤ max (ρ / 2) ((‖v‖ + 1) / δ) * ‖y - x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hq1
      have h3 : 0 ≤ max (ρ / 2) ((‖v‖ + 1) / δ) * (α - c') ^ 2 := mul_nonneg hε0 hq2
      nlinarith
    · have hr : 0 < ‖y - x‖ := lt_trans hδ hyδ
      have k0 : ⟪v, y - x⟫_ℝ ≤ ‖v‖ * ‖y - x‖ := real_inner_le_norm v (y - x)
      have k1 : δ * ⟪v, y - x⟫_ℝ ≤ ‖v‖ * ‖y - x‖ ^ 2 := by
        have h1 : δ * ⟪v, y - x⟫_ℝ ≤ δ * (‖v‖ * ‖y - x‖) := mul_le_mul_of_nonneg_left k0 hδ.le
        have h2 : δ * (‖v‖ * ‖y - x‖) ≤ ‖y - x‖ * (‖v‖ * ‖y - x‖) :=
          mul_le_mul_of_nonneg_right hyδ.le (by positivity)
        nlinarith
      have k2 : -(δ * (α - c')) ≤ ((α - c') ^ 2 + δ ^ 2) / 2 := by
        nlinarith [sq_nonneg (α - c' + δ)]
      have k3 : δ ^ 2 ≤ ‖y - x‖ ^ 2 := by nlinarith
      have k4 : ‖v‖ + 1 ≤ max (ρ / 2) ((‖v‖ + 1) / δ) * δ := by
        rw [← div_le_iff₀ hδ]
        exact le_max_right _ _
      have k5 : δ * (⟪v, y - x⟫_ℝ - (α - c')) ≤
          δ * (max (ρ / 2) ((‖v‖ + 1) / δ) * (‖y - x‖ ^ 2 + (α - c') ^ 2)) := by
        have hv := norm_nonneg v
        nlinarith [mul_le_mul_of_nonneg_right k4 (add_nonneg hq1 hq2)]
      exact le_of_mul_le_mul_left k5 hδ
  · rintro ⟨-, ε, hε, hquad⟩
    set K : ℝ := 2 * ε + 2 * ε * ‖v‖ ^ 2 with hK_def
    have hK : 0 < K := by positivity
    refine ⟨c, hxc, 2 * K, by positivity, 1 / (2 * K), by positivity, fun y hy ↦ ?_⟩
    by_contra hlt
    push_neg at hlt
    rcases eq_or_ne y x with rfl | hyx
    · simp [hxc] at hlt
    · have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
      have hmem := (hmemE y (c + ⟪v, y - x⟫_ℝ - 2 * K / 2 * ‖y - x‖ ^ 2)).2 hlt.le
      have hineq := hquad _ hmem
      rw [inner_toLp_neg_one_sub, norm_toLp_sub_sq] at hineq
      set a := ⟪v, y - x⟫_ℝ with ha_def
      set d := ‖y - x‖ ^ 2 with hd_def
      have hdpos : 0 < d := by positivity
      have hcs : a ^ 2 ≤ ‖v‖ ^ 2 * d := by
        have h1 := abs_real_inner_le_norm v (y - x)
        have h2 : |a| ^ 2 ≤ (‖v‖ * ‖y - x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [sq_abs, mul_pow] at h2
        exact h2
      have hsmall : K ^ 2 * d ≤ 1 / 4 := by
        have h1 : ‖y - x‖ * (2 * K) ≤ 1 := by
          have := hy
          rw [le_div_iff₀ (by positivity)] at this
          linarith
        have h2 : (‖y - x‖ * (2 * K)) ^ 2 ≤ 1 := by
          have h0 : 0 ≤ ‖y - x‖ * (2 * K) := by positivity
          nlinarith
        rw [hd_def]
        nlinarith
      have s1 : (a - K * d) ^ 2 ≤ 2 * a ^ 2 + 2 * (K * d) ^ 2 := by
        nlinarith [sq_nonneg (a + K * d)]
      have s2 : K * d ≤ ε * d + ε * (a - K * d) ^ 2 := by
        have : a - (c + a - 2 * K / 2 * d - c) = K * d := by ring
        have h' : c + a - 2 * K / 2 * d - c = a - K * d := by ring
        rw [this, h'] at hineq
        linarith
      have s3 : ε * (a - K * d) ^ 2 ≤ ε * (2 * a ^ 2 + 2 * (K * d) ^ 2) :=
        mul_le_mul_of_nonneg_left s1 hε.le
      have s4 : ε * a ^ 2 ≤ ε * (‖v‖ ^ 2 * d) := mul_le_mul_of_nonneg_left hcs hε.le
      have s5 : ε * d * (K ^ 2 * d) ≤ ε * d * (1 / 4) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      have s6 : 0 < ε * d := by positivity
      nlinarith [s2, s3, s4, s5, s6]

end RW
