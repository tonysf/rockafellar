/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Perturbations of prox-regularity

Exercise 13.35.  A function `g` of class `C¹⁺` around `x̄` is described by a
gradient map `G` on a ball `IB(x̄, δ)` that is Lipschitz there.
-/

import RockafellarWets.Chapter13.ProxRegularity

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Local lower semicontinuity survives the addition of a real function continuous on a
neighborhood of `x̄`. -/
theorem IsLocallyLscAt.add_continuousOn {f : E → EReal} {g : E → ℝ} {x : E} {δ : ℝ}
    (hf : IsLocallyLscAt f x) (hδ : 0 < δ) (hg : ∀ y ∈ ball x δ, ContinuousAt g y) :
    IsLocallyLscAt (fun y ↦ f y + (g y : EReal)) x := by
  obtain ⟨h1, h2, ε, hε, hcl⟩ := hf
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal h2 h1).symm
  set c := (f x).toReal
  obtain ⟨η, hη, hηg⟩ := Metric.continuousAt_iff.1 (hg x (mem_ball_self hδ)) (ε / 3)
    (by positivity)
  set r : ℝ := min (min (ε / 3) (η / 2)) (δ / 2) with hr
  have hrpos : 0 < r := lt_min (lt_min (by positivity) (half_pos hη)) (half_pos hδ)
  have hrε : r ≤ ε / 3 := (min_le_left _ _).trans (min_le_left _ _)
  have hrη : r < η := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self hη)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
  have hsum : f x + (g x : EReal) = ((c + g x : ℝ) : EReal) := by
    rw [hxc, EReal.coe_add]
  refine ⟨show f x + (g x : EReal) ≠ ⊥ by rw [hsum]; exact EReal.coe_ne_bot _,
    show f x + (g x : EReal) ≠ ⊤ by rw [hsum]; exact EReal.coe_ne_top _, r, hrpos, fun α hα ↦ ?_⟩
  change α ≤ (f x + (g x : EReal)).toReal + r at hα
  rw [hsum, EReal.toReal_coe] at hα
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  obtain ⟨ys, hys, hlim⟩ := mem_closure_iff_seq_limit.1 hy
  have hyball : y ∈ closedBall x r :=
    isClosed_closedBall.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ (hys n).1)
  refine ⟨hyball, ?_⟩
  change f y + (g y : EReal) ≤ (α : EReal)
  have hyx : dist y x ≤ r := mem_closedBall.1 hyball
  have hgy : |g y - g x| < ε / 3 := by
    have := hηg (show dist y x < η from lt_of_le_of_lt hyx hrη)
    rwa [Real.dist_eq] at this
  have hcont : ContinuousAt g y := hg y (by rw [mem_ball]; linarith)
  have hgylim : Tendsto (fun n ↦ g (ys n)) atTop (𝓝 (g y)) := hcont.tendsto.comp hlim
  -- `f y ≤ α - g y + t` for every `t ∈ (0, ε/3]`
  have hkey : ∀ t : ℝ, 0 < t → t ≤ ε / 3 → f y ≤ ((α - g y + t : ℝ) : EReal) := by
    intro t ht htε
    have hclosed := hcl (α - g y + t) (by
      rw [abs_lt] at hgy
      linarith)
    refine (hclosed.mem_of_tendsto hlim ?_).2
    filter_upwards [hgylim.eventually (lt_mem_nhds (show g y - t < g y by linarith))] with n hn
    refine ⟨(closedBall_subset_closedBall (hrε.trans (by linarith))) (hys n).1, ?_⟩
    change f (ys n) ≤ ((α - g y + t : ℝ) : EReal)
    have hn' : f (ys n) + (g (ys n) : EReal) ≤ (α : EReal) := (hys n).2
    have hle : f (ys n) ≤ ((α - g (ys n) : ℝ) : EReal) := by
      rw [EReal.coe_sub]
      exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).2 hn'
    exact hle.trans (EReal.coe_le_coe_iff.2 (by linarith))
  have hfy : f y ≤ ((α - g y : ℝ) : EReal) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs1, hs2⟩ := EReal.exists_between_coe_real hcon
    have hs1' : α - g y < s := EReal.coe_lt_coe_iff.1 hs1
    have ht : 0 < min (ε / 3) (s - (α - g y)) := lt_min (by positivity) (by linarith)
    have := hkey _ ht (min_le_left _ _)
    have h3 : ((α - g y + min (ε / 3) (s - (α - g y)) : ℝ) : EReal) ≤ (s : EReal) :=
      EReal.coe_le_coe_iff.2 (by linarith [min_le_right (ε / 3) (s - (α - g y))])
    exact absurd (this.trans h3) (not_le.2 hs2)
  rw [EReal.coe_sub] at hfy
  exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).1 hfy

section Lipschitz

variable {g : E → ℝ} {G : E → E} {x : E} {δ L : ℝ}

omit [InnerProductSpace ℝ E] in
/-- A gradient map that is Lipschitz on a ball is continuous there. -/
theorem continuousOn_of_lipschitz_gradient (hL0 : 0 ≤ L)
    (hL : ∀ y ∈ ball x δ, ∀ z ∈ ball x δ, ‖G y - G z‖ ≤ L * ‖y - z‖) :
    ContinuousOn G (ball x δ) := by
  have : LipschitzOnWith ⟨L, hL0⟩ G (ball x δ) := LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ by
    rw [dist_eq_norm, dist_eq_norm]
    exact hL y hy z hz
  exact this.continuousOn

variable [CompleteSpace E]

/-- A function with `L`-Lipschitz gradient on a ball satisfies
`g(x') ≥ g(y) + ⟪∇g(y), x' - y⟫ - L‖x' - y‖²` there. -/
theorem quadratic_lower_bound_of_lipschitz_gradient (hL0 : 0 ≤ L)
    (hg : ∀ y ∈ ball x δ, HasGradientAt g (G y) y)
    (hL : ∀ y ∈ ball x δ, ∀ z ∈ ball x δ, ‖G y - G z‖ ≤ L * ‖y - z‖)
    {y x' : E} (hy : y ∈ ball x δ) (hx' : x' ∈ ball x δ) :
    g y + ⟪G y, x' - y⟫_ℝ - L * ‖x' - y‖ ^ 2 ≤ g x' := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x' - y) ∈ ball x δ :=
    fun t ht ↦ (convex_ball x δ).add_smul_sub_mem hy hx' ht
  set χ : ℝ → ℝ := fun t ↦ g (y + t • (x' - y)) - t * ⟪G y, x' - y⟫_ℝ with hχ
  set χ' : ℝ → ℝ := fun t ↦ ⟪G (y + t • (x' - y)) - G y, x' - y⟫_ℝ with hχ'
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt χ (χ' t) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hline : HasDerivAt (fun s : ℝ ↦ y + s • (x' - y)) (x' - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x' - y)).const_add y
    have h1 := (hg _ (hseg t ht)).hasFDerivAt.comp_hasDerivAt t hline
    have h2 : HasDerivAt (fun s : ℝ ↦ s * ⟪G y, x' - y⟫_ℝ) ⟪G y, x' - y⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G y, x' - y⟫_ℝ
    have h3 := (h1.sub h2).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
    convert h3 using 1
    simp only [hχ', InnerProductSpace.toDual_apply_apply, inner_sub_left]
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖χ' t‖ ≤ L * ‖x' - y‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have hLip := hL _ (hseg t ht') y hy
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1] at hLip
    calc ‖χ' t‖ ≤ ‖G (y + t • (x' - y)) - G y‖ * ‖x' - y‖ := by
          rw [Real.norm_eq_abs]
          exact abs_real_inner_le_norm _ _
      _ ≤ L * (t * ‖x' - y‖) * ‖x' - y‖ := mul_le_mul_of_nonneg_right hLip (norm_nonneg _)
      _ ≤ L * ‖x' - y‖ ^ 2 := by
        have := mul_nonneg (mul_nonneg hL0 (sub_nonneg.2 ht.2.le)) (sq_nonneg ‖x' - y‖)
        nlinarith [this]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  simp only [hχ, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, add_sub_cancel] at hmvt
  rw [Real.norm_eq_abs, abs_le] at hmvt
  linarith [hmvt.1]

/-- Near `x̄`, subgradients of `f + g` are subgradients of `f` shifted by `∇g`. -/
theorem subdifferential_add_lipschitz_gradient [FiniteDimensional ℝ E] {f : E → EReal}
    (hL0 : 0 ≤ L) (hg : ∀ y ∈ ball x δ, HasGradientAt g (G y) y)
    (hL : ∀ y ∈ ball x δ, ∀ z ∈ ball x δ, ‖G y - G z‖ ≤ L * ‖y - z‖) {y : E}
    (hy : y ∈ ball x δ) {c : ℝ} (hfy : f y = c) :
    subdifferential (fun z ↦ f z + (g z : EReal)) y = (fun u ↦ u + G y) '' subdifferential f y := by
  have hcont := continuousOn_of_lipschitz_gradient hL0 hL
  have hC1 : ContDiffAt ℝ 1 g y := by
    rw [contDiffAt_one_iff]
    refine ⟨fun z ↦ InnerProductSpace.toDual ℝ E (G z), ball x δ, isOpen_ball.mem_nhds hy,
      ?_, fun z hz ↦ (hg z hz).hasFDerivAt⟩
    exact (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.continuous.comp_continuousOn hcont
  have h := (subdifferentials_add_smooth hfy hC1).2.1
  rwa [(hg y hy).gradient] at h

end Lipschitz

/-! ### Exercise 13.35 -/

section Exercise1335

variable [FiniteDimensional ℝ E] {f : E → EReal} {g : E → ℝ} {G : E → E} {x v : E} {δ L : ℝ}

/-- **Exercise 13.35**: if `f` is prox-regular at `x̄` for `v̄` and `g` is `C¹⁺` around `x̄`
(gradient `G`, `L`-Lipschitz on `IB(x̄, δ)`), then `f + g` is prox-regular at `x̄` for
`v̄ + ∇g(x̄)`. -/
theorem IsProxRegularAt.add_lipschitz_gradient (hf : IsProxRegularAt f x v) (hδ : 0 < δ)
    (hL0 : 0 ≤ L) (hg : ∀ y ∈ ball x δ, HasGradientAt g (G y) y)
    (hL : ∀ y ∈ ball x δ, ∀ z ∈ ball x δ, ‖G y - G z‖ ≤ L * ‖y - z‖) :
    IsProxRegularAt (fun y ↦ f y + (g y : EReal)) x (v + G x) := by
  obtain ⟨hlsc, hv, ε, hε, ρ, hρ, hprox⟩ := hf
  have hxδ : x ∈ ball x δ := mem_ball_self hδ
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hlsc.2.1 hlsc.1).symm
  have hcontg : ∀ y ∈ ball x δ, ContinuousAt g y :=
    fun y hy ↦ (hg y hy).differentiableAt.continuousAt
  obtain ⟨η, hη, hηg⟩ := Metric.continuousAt_iff.1 (hcontg x hxδ) (ε / 2) (half_pos hε)
  set ε' : ℝ := min (min (δ / 2) (ε / 2)) (min (ε / (2 * (L + 1))) (η / 2)) with hε'
  have hε'pos : 0 < ε' := lt_min (lt_min (half_pos hδ) (half_pos hε))
    (lt_min (by positivity) (half_pos hη))
  have hε'δ : ε' < δ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _))
    (half_lt_self hδ)
  have hε'ε : ε' ≤ ε / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε'L : ε' * (1 + L) ≤ ε / 2 := by
    have h1 : ε' ≤ ε / (2 * (L + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    calc ε' * (1 + L) ≤ ε / (2 * (L + 1)) * (1 + L) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = ε / 2 := by field_simp; ring
  have hε'η : ε' < η := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
    (half_lt_self hη)
  refine ⟨hlsc.add_continuousOn hδ hcontg, ?_, ε', hε'pos, ρ + 2 * L, by positivity, ?_⟩
  · rw [subdifferential_add_lipschitz_gradient hL0 hg hL hxδ hxc]
    exact ⟨v, hv, rfl⟩
  intro y v' hv' hvv hyx hfy x' hx'
  have hyδ : y ∈ ball x δ := by rw [mem_ball, dist_eq_norm]; linarith
  have hx'δ : x' ∈ ball x δ := by
    rw [mem_ball]
    exact lt_of_le_of_lt (mem_closedBall.1 hx') hε'δ
  -- `f y` is finite
  obtain ⟨cy, hcy⟩ := hv'.1
  have hfy1 : f y ≠ ⊤ := fun h ↦ by
    change f y + (g y : EReal) = cy at hcy
    rw [h, EReal.top_add_coe] at hcy
    exact EReal.coe_ne_top cy hcy.symm
  have hfy2 : f y ≠ ⊥ := fun h ↦ by
    change f y + (g y : EReal) = cy at hcy
    rw [h, EReal.bot_add] at hcy
    exact EReal.coe_ne_bot cy hcy.symm
  have hyc : f y = (((f y).toReal : ℝ) : EReal) := (EReal.coe_toReal hfy1 hfy2).symm
  rw [subdifferential_add_lipschitz_gradient hL0 hg hL hyδ hyc] at hv'
  obtain ⟨u, hu, rfl⟩ := hv'
  have huv : ‖u - v‖ < ε := by
    have h1 : u - v = (u + G y - (v + G x)) + (G x - G y) := by abel
    have h2 := hL x hxδ y hyδ
    rw [norm_sub_rev x y] at h2
    calc ‖u - v‖ ≤ ‖u + G y - (v + G x)‖ + ‖G x - G y‖ := by rw [h1]; exact norm_add_le _ _
      _ < ε' + L * ε' := by
        refine add_lt_add_of_lt_of_le hvv (h2.trans (mul_le_mul_of_nonneg_left hyx.le hL0))
      _ = ε' * (1 + L) := by ring
      _ ≤ ε / 2 := hε'L
      _ < ε := half_lt_self hε
  have hgxy : |g y - g x| < ε / 2 := by
    have := hηg (show dist y x < η by rw [dist_eq_norm]; linarith)
    rwa [Real.dist_eq] at this
  have hfy' : f y < f x + ε := by
    change f y + (g y : EReal) < f x + (g x : EReal) + ε' at hfy
    rw [hyc, hxc, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hfy
    rw [hyc, hxc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    rw [abs_lt] at hgxy
    linarith
  have hprox' := hprox y u hu huv (by linarith) hfy' x'
    (closedBall_subset_closedBall (hε'ε.trans (half_le_self hε.le)) hx')
  have hquad := quadratic_lower_bound_of_lipschitz_gradient hL0 hg hL hyδ hx'δ
  change f y + (g y : EReal) + ((⟪u + G y, x' - y⟫_ℝ - (ρ + 2 * L) / 2 * ‖x' - y‖ ^ 2 : ℝ) :
    EReal) ≤ f x' + (g x' : EReal)
  rcases ereal_trichotomy (f x') with h | h | ⟨b, h⟩
  · rw [h] at hprox'
    rw [hyc] at hprox'
    exact absurd (le_bot_iff.1 hprox') (by rw [← EReal.coe_add]; exact EReal.coe_ne_bot _)
  · rw [h, EReal.top_add_coe]
    exact le_top
  · rw [h, hyc] at hprox' ⊢
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hprox'
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_add_left]
    linarith

/-- **Exercise 13.35**: subdifferential continuity is preserved as well. -/
theorem IsSubdifferentiallyContinuousAt.add_lipschitz_gradient
    (hf : IsSubdifferentiallyContinuousAt f x v) (hδ : 0 < δ) (hL0 : 0 ≤ L)
    (hg : ∀ y ∈ ball x δ, HasGradientAt g (G y) y)
    (hL : ∀ y ∈ ball x δ, ∀ z ∈ ball x δ, ‖G y - G z‖ ≤ L * ‖y - z‖) :
    IsSubdifferentiallyContinuousAt (fun y ↦ f y + (g y : EReal)) x (v + G x) := by
  obtain ⟨hv, hcont⟩ := hf
  have hxδ : x ∈ ball x δ := mem_ball_self hδ
  obtain ⟨c, hxc⟩ := hv.1
  have hsubx := subdifferential_add_lipschitz_gradient hL0 hg hL hxδ hxc
  have hGc : ContinuousAt G x :=
    (continuousOn_of_lipschitz_gradient hL0 hL).continuousAt (isOpen_ball.mem_nhds hxδ)
  have hgc : ContinuousAt g x := (hg x hxδ).differentiableAt.continuousAt
  refine ⟨by rw [hsubx]; exact ⟨v, hv, rfl⟩, fun xs vs hxs hvs hsub ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (isOpen_ball.mem_nhds hxδ))
  -- shift past `N` so that all points lie in the ball
  have hmem : ∀ n, vs (n + N) - G (xs (n + N)) ∈ subdifferential f (xs (n + N)) := by
    intro n
    have hyδ := hN (n + N) (Nat.le_add_left N n)
    obtain ⟨cy, hcy⟩ := (hsub (n + N)).1
    have hfy1 : f (xs (n + N)) ≠ ⊤ := fun h ↦ by
      change f (xs (n + N)) + (g (xs (n + N)) : EReal) = cy at hcy
      rw [h, EReal.top_add_coe] at hcy
      exact EReal.coe_ne_top cy hcy.symm
    have hfy2 : f (xs (n + N)) ≠ ⊥ := fun h ↦ by
      change f (xs (n + N)) + (g (xs (n + N)) : EReal) = cy at hcy
      rw [h, EReal.bot_add] at hcy
      exact EReal.coe_ne_bot cy hcy.symm
    have h := hsub (n + N)
    rw [subdifferential_add_lipschitz_gradient hL0 hg hL hyδ
      (EReal.coe_toReal hfy1 hfy2).symm] at h
    obtain ⟨u, hu, hueq⟩ := h
    rwa [← hueq, add_sub_cancel_right]
  have hxs' : Tendsto (fun n ↦ xs (n + N)) atTop (𝓝 x) := hxs.comp (tendsto_add_atTop_nat N)
  have hus : Tendsto (fun n ↦ vs (n + N) - G (xs (n + N))) atTop (𝓝 v) := by
    have := ((hvs.comp (tendsto_add_atTop_nat N)).sub (hGc.tendsto.comp hxs'))
    simpa using this
  have hf' := hcont _ _ hxs' hus hmem
  have hsum := ((EReal.continuousAt_add (p := (f x, ((g x : ℝ) : EReal)))
    (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto).comp
    (hf'.prodMk_nhds (EReal.tendsto_coe.2 (hgc.tendsto.comp hxs')))
  exact (tendsto_add_atTop_iff_nat N).1 hsum

/-- **Exercise 13.35**: `f₀(x) = f(x) - ⟪v̄, x⟫` is prox-regular at `x̄` for `0`, with
subdifferential continuity preserved. -/
theorem IsProxRegularAt.sub_inner (hf : IsProxRegularAt f x v) :
    IsProxRegularAt (fun y ↦ f y + ((-⟪v, y⟫_ℝ : ℝ) : EReal)) x 0 := by
  have hg : ∀ y ∈ ball x 1, HasGradientAt (fun y ↦ -⟪v, y⟫_ℝ) (-v) y := by
    intro y _
    rw [hasGradientAt_iff_hasFDerivAt]
    have := ((InnerProductSpace.toDual ℝ E v : E →L[ℝ] ℝ).hasFDerivAt (x := y)).neg
    convert this using 1
    ext z
    simp [InnerProductSpace.toDual_apply_apply]
  have := hf.add_lipschitz_gradient one_pos le_rfl hg (fun _ _ _ _ ↦ by simp)
  simpa using this

/-- **Exercise 13.35** for `g` of class `C²`: its gradient is Lipschitz near `x̄`. -/
theorem exists_lipschitz_gradient_of_contDiff_two {g : E → ℝ} (hg : ContDiff ℝ 2 g) (x : E) :
    ∃ δ > 0, ∃ L ≥ 0, (∀ y ∈ ball x δ, HasGradientAt g (gradient g y) y) ∧
      ∀ y ∈ ball x δ, ∀ z ∈ ball x δ, ‖gradient g y - gradient g z‖ ≤ L * ‖y - z‖ := by
  have hgrad : ContDiff ℝ 1 (gradient g) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
    have : gradient g = fun y ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g y) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp h1
  obtain ⟨K, t, ht, hK⟩ := hgrad.contDiffAt.exists_lipschitzOnWith (x := x)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨δ, hδ, K, K.2, fun y _ ↦ ((hg.differentiable (by norm_num)) y).hasGradientAt,
    fun y hy z hz ↦ ?_⟩
  have := hK.dist_le_mul y (hball hy) z (hball hz)
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- **Exercise 13.35** for `g` of class `C²`: prox-regularity and subdifferential continuity of
`f` at `x̄` for `v̄` pass to `f + g` at `x̄` for `v̄ + ∇g(x̄)`. -/
theorem perturbations_of_prox_regularity {g : E → ℝ} (hg : ContDiff ℝ 2 g) :
    (IsProxRegularAt f x v →
      IsProxRegularAt (fun y ↦ f y + (g y : EReal)) x (v + gradient g x)) ∧
    (IsSubdifferentiallyContinuousAt f x v →
      IsSubdifferentiallyContinuousAt (fun y ↦ f y + (g y : EReal)) x (v + gradient g x)) := by
  obtain ⟨δ, hδ, L, hL0, hgrad, hL⟩ := exists_lipschitz_gradient_of_contDiff_two hg x
  exact ⟨fun h ↦ h.add_lipschitz_gradient hδ hL0 hgrad hL,
    fun h ↦ h.add_lipschitz_gradient hδ hL0 hgrad hL⟩

end Exercise1335

end RW
