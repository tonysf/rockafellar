/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order expansions of twice differentiable functions

Auxiliary facts used throughout Chapter 13.

* A function differentiable near `x̄` whose derivative is differentiable at
  `x̄` (twice differentiable in the classical sense of 13.1(a)) has the
  quadratic expansion `f(x̄ + h) = f(x̄) + f'(x̄)h + ½ f''(x̄)(h)(h) + o(‖h‖²)`.
  The proof applies the one-dimensional mean value inequality to
  `t ↦ f(x̄ + th) - t f'(x̄)h - (t²/2) f''(x̄)(h)(h)` on `[0, 1]`.
* Consequently the second-order quotients `Δ²_τ f(x̄ | ∇f(x̄))` converge
  continuously to the quadratic form `w ↦ f''(x̄)(w)(w)` as `τ ↓ 0`.
* Lower limits and lower epi-limits of sums with a family that converges
  continuously to a finite limit.
-/

import RockafellarWets.Chapter13.SecondSubderivatives
import Mathlib.Analysis.Calculus.MeanValue

open Filter Set Topology Metric Asymptotics
open scoped InnerProductSpace

namespace RW

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quadratic expansion of a function that is twice differentiable at `x` in the
classical sense: `f(x + h) - f(x) - f'(x)h - ½ f''(h)(h) = o(‖h‖²)`. -/
theorem isLittleO_secondOrder {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {f'' : E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hf' : HasFDerivAt f' f'' x) :
    (fun h : E ↦ f (x + h) - f x - f' x h - (1 / 2) * f'' h h) =o[𝓝 0] (fun h ↦ ‖h‖ ^ 2) := by
  rw [isLittleO_iff]
  intro ε hε
  have ho := (hasFDerivAtFilter_iff_isLittleO.1 hf').def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hf.and ho)
  filter_upwards [ball_mem_nhds (0 : E) hδ] with h hh
  rw [mem_ball, dist_zero_right] at hh
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ ball x δ := by
    intro t ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    calc t * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg h)
      _ < δ := by rw [one_mul]; exact hh
  set χ : ℝ → ℝ := fun t ↦ f (x + t • h) - t * f' x h - t ^ 2 / 2 * f'' h h with hχ
  set χ' : ℝ → ℝ := fun t ↦ f' (x + t • h) h - f' x h - t * f'' h h with hχ'
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt χ (χ' t) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hfd : HasFDerivAt f (f' (x + t • h)) (x + t • h) := (hball (hseg t ht)).1
    have hline : HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h1 : HasDerivAt (fun s : ℝ ↦ f (x + s • h)) (f' (x + t • h) h) t :=
      hfd.comp_hasDerivAt t hline
    have h2 : HasDerivAt (fun s : ℝ ↦ s * f' x h) (f' x h) t := by
      simpa using (hasDerivAt_id t).mul_const (f' x h)
    have h3 : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2 * f'' h h) (t * f'' h h) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).mul_const (f'' h h)
      convert this using 1
      push_cast
      ring
    exact ((h1.sub h2).sub h3).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖χ' t‖ ≤ ε * ‖h‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have hest := (hball (hseg t ht')).2
    simp only [add_sub_cancel_left] at hest
    have heq : χ' t = (f' (x + t • h) - f' x - f'' (t • h)) h := by
      simp [hχ', map_smul, smul_eq_mul]
    rw [heq]
    calc ‖(f' (x + t • h) - f' x - f'' (t • h)) h‖
        ≤ ‖f' (x + t • h) - f' x - f'' (t • h)‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖t • h‖ * ‖h‖ := mul_le_mul_of_nonneg_right hest (norm_nonneg h)
      _ ≤ ε * ‖h‖ * ‖h‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hε.le) (norm_nonneg h)
        rw [norm_smul, Real.norm_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg h) ht.2.le
      _ = ε * ‖h‖ ^ 2 := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  have h1 : χ 1 - χ 0 = f (x + h) - f x - f' x h - 1 / 2 * f'' h h := by
    simp [hχ]
    ring
  rw [h1] at hmvt
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)]
  rwa [Real.norm_eq_abs] at hmvt

/-- The quadratic expansion in `ε`–`δ` form. -/
theorem exists_secondOrder_bound {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {f'' : E →L[ℝ] E →L[ℝ] ℝ}
    {x : E} (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hf' : HasFDerivAt f' f'' x) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ h : E, ‖h‖ < δ →
      |f (x + h) - f x - f' x h - (1 / 2) * f'' h h| ≤ ε * ‖h‖ ^ 2 := by
  have ho := (isLittleO_iff.1 (isLittleO_secondOrder hf hf')) hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ho
  refine ⟨δ, hδ, fun h hh ↦ ?_⟩
  have := hball (show h ∈ ball (0 : E) δ by rwa [mem_ball, dist_zero_right])
  simp only [mem_setOf_eq, Real.norm_eq_abs] at this
  rwa [abs_of_nonneg (sq_nonneg ‖h‖)] at this

end Expansion

section Quotients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The second-order quotient 13(5) of a real-valued function, as a real number. -/
theorem secondDifferenceQuotient_coe (f : E → ℝ) (x v : E) (τ : ℝ) (w : E) :
    secondDifferenceQuotient (fun y ↦ (f y : EReal)) x v τ w =
      ((2 / τ ^ 2 * (f (x + τ • w) - f x - τ * ⟪v, w⟫_ℝ) : ℝ) : EReal) :=
  secondDifferenceQuotient_of_coe rfl rfl

/-- For a function twice differentiable at `x̄` in the classical sense with gradient `v`,
the quotients `Δ²_τ f(x̄ | v)` converge continuously to `w ↦ f''(x̄)(w)(w)`. -/
theorem tendsto_secondDifferenceQuotient_of_hasFDerivAt {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E →L[ℝ] E →L[ℝ] ℝ} {x v : E} (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hf' : HasFDerivAt f' f'' x) (hv : ∀ w, f' x w = ⟪v, w⟫_ℝ) (w : E) :
    Tendsto (fun p : ℝ × E ↦ 2 / p.1 ^ 2 * (f (x + p.1 • p.2) - f x - p.1 * ⟪v, p.2⟫_ℝ))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (f'' w w)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hM : 0 < (‖w‖ + 1) ^ 2 := by positivity
  set ε : ℝ := η / (4 * (‖w‖ + 1) ^ 2) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hbound⟩ := exists_secondOrder_bound hf hf' hε
  have hq : Continuous fun u : E ↦ f'' u u :=
    f''.continuous₂.comp (continuous_id.prodMk continuous_id)
  have e1 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, ‖p.2‖ < ‖w‖ + 1 :=
    tendsto_snd.eventually ((continuous_norm.tendsto w).eventually (gt_mem_nhds (by linarith)))
  have e2 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, dist (f'' p.2 p.2) (f'' w w) < η / 2 :=
    tendsto_snd.eventually ((hq.tendsto w).eventually (ball_mem_nhds _ (half_pos hη)))
  have e3 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, ‖p.1 • p.2‖ < δ := by
    have h0 : Tendsto (fun p : ℝ × E ↦ p.1 • p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 0) := by
      have := (continuous_fst.smul continuous_snd).tendsto ((0 : ℝ), w)
      rw [zero_smul, nhds_prod_eq] at this
      exact this.mono_left (Filter.prod_mono nhdsWithin_le_nhds le_rfl)
    exact h0.eventually ((continuous_norm.tendsto (0 : E)).eventually
      (gt_mem_nhds (by rw [norm_zero]; exact hδ)))
  have e4 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 := tendsto_fst.eventually self_mem_nhdsWithin
  filter_upwards [e1, e2, e3, e4] with p hp1 hp2 hp3 hp4
  obtain ⟨τ, u⟩ := p
  simp only at hp1 hp2 hp3 hp4 ⊢
  have hb := hbound (τ • u) hp3
  have hlin : f' x (τ • u) = τ * ⟪v, u⟫_ℝ := by rw [map_smul, hv, smul_eq_mul]
  have hquad : f'' (τ • u) (τ • u) = τ ^ 2 * f'' u u := by
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [hlin, hquad, norm_smul, Real.norm_of_nonneg hp4.le] at hb
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hkey : |2 / τ ^ 2 * (f (x + τ • u) - f x - τ * ⟪v, u⟫_ℝ) - f'' u u| ≤ 2 * ε * ‖u‖ ^ 2 := by
    have heq : 2 / τ ^ 2 * (f (x + τ • u) - f x - τ * ⟪v, u⟫_ℝ) - f'' u u =
        2 / τ ^ 2 * (f (x + τ • u) - f x - τ * ⟪v, u⟫_ℝ - 1 / 2 * (τ ^ 2 * f'' u u)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / τ ^ 2)]
    calc 2 / τ ^ 2 * |f (x + τ • u) - f x - τ * ⟪v, u⟫_ℝ - 1 / 2 * (τ ^ 2 * f'' u u)|
        ≤ 2 / τ ^ 2 * (ε * (τ * ‖u‖) ^ 2) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 * ε * ‖u‖ ^ 2 := by field_simp
  have hu2 : ‖u‖ ^ 2 ≤ (‖w‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hp1.le 2
  have h2ε : 2 * ε * ‖u‖ ^ 2 ≤ η / 2 := by
    calc 2 * ε * ‖u‖ ^ 2 ≤ 2 * ε * (‖w‖ + 1) ^ 2 := mul_le_mul_of_nonneg_left hu2 (by positivity)
      _ = η / 2 := by rw [hεdef]; field_simp; ring
  rw [Real.dist_eq] at hp2 ⊢
  calc |2 / τ ^ 2 * (f (x + τ • u) - f x - τ * ⟪v, u⟫_ℝ) - f'' w w|
      ≤ |2 / τ ^ 2 * (f (x + τ • u) - f x - τ * ⟪v, u⟫_ℝ) - f'' u u| + |f'' u u - f'' w w| :=
        abs_sub_le _ _ _
    _ < η / 2 + η / 2 := by linarith
    _ = η := by ring

/-- The `EReal` form: `Δ²_τ f(x̄ | ∇f(x̄))` converges continuously to `f''(x̄)(w)(w)`. -/
theorem tendsto_secondDifferenceQuotient_coe_of_hasFDerivAt {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E →L[ℝ] E →L[ℝ] ℝ} {x v : E} (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hf' : HasFDerivAt f' f'' x) (hv : ∀ w, f' x w = ⟪v, w⟫_ℝ) (w : E) :
    Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotient (fun y ↦ (f y : EReal)) x v p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((f'' w w : ℝ) : EReal)) := by
  simp_rw [secondDifferenceQuotient_coe]
  exact EReal.tendsto_coe.2 (tendsto_secondDifferenceQuotient_of_hasFDerivAt hf hf' hv w)

end Quotients

section Sums

variable {ι E : Type*} [TopologicalSpace E]

/-- `liminf (u + v) = liminf u + b` when `v` converges to a real number `b`. -/
theorem liminf_add_of_tendsto_coe {l : Filter ι} [l.NeBot] {u v : ι → EReal} {b : ℝ}
    (hv : Tendsto v l (𝓝 (b : EReal))) :
    liminf (fun i ↦ u i + v i) l = liminf u l + b := by
  apply le_antisymm
  · have h := EReal.liminf_add_le (u := v) (v := u) (f := l)
      (Or.inl (hv.limsup_eq ▸ EReal.coe_ne_bot b))
      (Or.inl (hv.limsup_eq ▸ EReal.coe_ne_top b))
    rw [hv.limsup_eq] at h
    calc liminf (fun i ↦ u i + v i) l = liminf (v + u) l := by
          congr 1
          funext i
          exact add_comm _ _
      _ ≤ (b : EReal) + liminf u l := h
      _ = liminf u l + b := add_comm _ _
  · have h := EReal.le_liminf_add (u := u) (v := v) (f := l)
    rwa [hv.liminf_eq] at h

/-- Adding a family that converges continuously to a real-valued limit preserves the
inclusion of an epigraph in the inner limit of epigraphs (the upper half of
epi-convergence). -/
theorem epigraph_add_subset_innerSetLimitAlong {l : Filter ι} {g : ι → E → EReal}
    {h : ι → E → ℝ} {G : E → EReal} {H : E → ℝ}
    (hG : epigraph G ⊆ innerSetLimitAlong l (fun i ↦ epigraph (g i)))
    (hH : ∀ w, Tendsto (fun p : ι × E ↦ h p.1 p.2) (l ×ˢ 𝓝 w) (𝓝 (H w))) :
    epigraph (fun w ↦ G w + H w) ⊆
      innerSetLimitAlong l (fun i ↦ epigraph (fun w ↦ g i w + h i w)) := by
  rintro ⟨w, α⟩ hwα N hN
  change G w + (H w : EReal) ≤ (α : EReal) at hwα
  have hGw : G w ≤ ((α - H w : ℝ) : EReal) := by
    rw [EReal.coe_sub]
    exact EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
      |>.2 hwα
  obtain ⟨V, hV, I, hI, hVI⟩ := mem_nhds_prod_iff.1 hN
  obtain ⟨ε, hε, hballI⟩ := Metric.mem_nhds_iff.1 hI
  obtain ⟨U₁, hU₁, V₁, hV₁, hUV₁⟩ := mem_prod_iff.1
    ((hH w).eventually (ball_mem_nhds (H w) (half_pos hε)))
  have hmem := hG (show (w, α - H w) ∈ epigraph G from hGw)
    ((V ∩ V₁) ×ˢ ball (α - H w) (ε / 2))
    (prod_mem_nhds (inter_mem hV hV₁) (ball_mem_nhds _ (half_pos hε)))
  filter_upwards [hmem, hU₁] with i hi hiU
  obtain ⟨⟨w', β⟩, hβ, ⟨hw'V, hw'V₁⟩, hβball⟩ := hi
  refine ⟨(w', β + h i w'), ?_, hVI ⟨hw'V, hballI ?_⟩⟩
  · change g i w' + (h i w' : EReal) ≤ ((β + h i w' : ℝ) : EReal)
    rw [EReal.coe_add]
    exact add_le_add (show g i w' ≤ (β : EReal) from hβ) le_rfl
  · have hh : dist (h i w') (H w) < ε / 2 :=
      hUV₁ (show (i, w') ∈ U₁ ×ˢ V₁ from ⟨hiU, hw'V₁⟩)
    rw [mem_ball, Real.dist_eq] at hβball ⊢
    rw [Real.dist_eq] at hh
    calc |β + h i w' - α| = |(β - (α - H w)) + (h i w' - H w)| := by ring_nf
      _ ≤ |β - (α - H w)| + |h i w' - H w| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring

end Sums

end RW
