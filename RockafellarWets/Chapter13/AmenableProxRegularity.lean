/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Prox-regularity from amenability

Proposition 13.32.  For a strongly amenable function, represented near `x̄` as `g ∘ F` with `g`
proper, lsc and convex and `F` of class `C²` (Definition 10.23), the multipliers
`y ∈ ∂g(F(x))` with `∇F(x)* y = v` stay bounded for `(x, v)` near `(x̄, v̄)` because of the
constraint qualification, and the second-order Taylor bound for `F` then turns the convex
subgradient inequality for `g` into the uniform prox-regularity inequality
`f(x') ≥ f(x) + ⟪v, x' - x⟫ - (ρ/2)‖x' - x‖²`.  Applied in both directions this inequality also
yields subdifferential continuity.  Persistence of strong amenability (10.25) extends both
properties to all nearby points of `dom f`.
-/

import RockafellarWets.Chapter13.ProxRegularity
import RockafellarWets.Chapter10.AmenableSubgradientGraphs
import RockafellarWets.Chapter10.AmenabilityPersistence
import RockafellarWets.Chapter10.AmenableCompositionNeighborhoods
import RockafellarWets.Chapter10.AmenableRegularity
import RockafellarWets.Chapter10.AmenableFunctionCalculus

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

section Multipliers

variable {E T G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Under the kernel qualification, convex subgradient multipliers `y ∈ ∂g(F(x))` whose images
`A(x) y` stay near a fixed `u` are bounded for `x` near `x̄`. -/
theorem exists_multiplier_bound_of_convex {g : T → EReal} (hp : IsProper g)
    (hl : LowerSemicontinuous g) (hc : Convex ℝ (epigraph g)) {F : E → T} {A : E → T →L[ℝ] G}
    {x : E} (hF : ContinuousAt F x) (hA : ContinuousAt A x)
    (hQ : ∀ v ∈ normalCone (closure (effectiveDomain g)) (F x), A x v = 0 → v = 0) (u : G) :
    ∃ ε > 0, ∃ η : ℝ, ∀ y, dist y x < ε → ∀ v ∈ subdifferential g (F y),
      ‖A y v - u‖ < ε → ‖v‖ ≤ η := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ y, dist y x < 1 / ((n : ℝ) + 1) ∧ ∃ v ∈ subdifferential g (F y),
      ‖A y v - u‖ < 1 / ((n : ℝ) + 1) ∧ (n : ℝ) < ‖v‖ := fun n ↦ hcon _ (by positivity) n
  choose ys hys vs hvs hAv hvn using hseq
  have hy : Tendsto ys atTop (𝓝 x) := tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hys n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have hu : Tendsto (fun n ↦ A (ys n) (vs n)) atTop (𝓝 u) := tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (hAv n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  choose c hcv using fun n ↦ (hvs n).1
  obtain ⟨a, z, φ, hφ, -, hsum, hat, hzt⟩ :=
    exists_normalized_multiplier_subsequence (fun _ ↦ 1) vs (fun _ ↦ by norm_num)
  have ha0 : a = 0 := by
    have hlim : Tendsto (fun n ↦ (1 : ℝ) / (1 + ‖vs (φ n)‖)) atTop (𝓝 0) := by
      refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
      have h1 := hvn (φ n)
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact tendsto_nhds_unique hat hlim
  have hyφ := hy.comp hφ.tendsto_atTop
  have hFφ := hF.tendsto.comp hyφ
  have hAt : Tendsto (fun n ↦ A (ys (φ n)) ((1 + ‖vs (φ n)‖)⁻¹ • vs (φ n))) atTop
      (𝓝 (A x z)) :=
    ((continuous_fst.clm_apply continuous_snd :
      Continuous (fun p : (T →L[ℝ] G) × T ↦ p.1 p.2)).tendsto (A x, z)).comp
      ((hA.tendsto.comp hyφ).prodMk_nhds hzt)
  have hright : Tendsto (fun n ↦ (1 / (1 + ‖vs (φ n)‖)) • A (ys (φ n)) (vs (φ n))) atTop
      (𝓝 (a • u)) := hat.smul (hu.comp hφ.tendsto_atTop)
  have hAz : A x z = a • u :=
    tendsto_nhds_unique hAt (hright.congr fun n ↦ by simp only [map_smul, one_div])
  rw [ha0, zero_smul] at hAz
  have hxD : F x ∈ closure (effectiveDomain g) := isClosed_closure.mem_of_tendsto hFφ
    (.of_forall fun n ↦ subset_closure ((hcv (φ n)).trans_lt (EReal.coe_lt_top _)))
  obtain ⟨b, _, hbg⟩ := EReal.exists_between_coe_real (hp.2 (F x))
  have hlow : ∀ᶠ n in atTop, b ≤ c (φ n) := by
    filter_upwards [hFφ.eventually (hl (F x) (b : EReal) hbg)] with n hn
    dsimp only [Function.comp_def] at hn
    rw [hcv (φ n)] at hn
    exact (EReal.coe_lt_coe_iff.mp hn).le
  have hsupport : ∀ w ∈ effectiveDomain g, ⟪z, w - F x⟫_ℝ ≤ 0 := by
    intro w hw
    have hwval := (EReal.coe_toReal hw.ne (hp.2 w).ne').symm
    have ht := (hat.mul_const b).add (hzt.inner ((tendsto_const_nhds (x := w)).sub hFφ))
    have hright := hat.mul_const (g w).toReal
    have hh : a * b + ⟪z, w - F x⟫_ℝ ≤ a * (g w).toReal := by
      apply le_of_tendsto_of_tendsto ht hright
      filter_upwards [hlow] with n hn
      have hs := (mem_subdifferential_iff_of_convex hc hp (hcv (φ n))).mp (hvs (φ n)) w
      rw [hwval, EReal.coe_le_coe_iff] at hs
      have hnpos : 0 ≤ 1 / (1 + ‖vs (φ n)‖) := by positivity
      have hm1 := mul_le_mul_of_nonneg_left hs hnpos
      have hm2 := mul_le_mul_of_nonneg_left hn hnpos
      rw [mul_add] at hm1
      have hh := (add_le_add hm2 (le_rfl :
        (1 / (1 + ‖vs (φ n)‖)) * ⟪vs (φ n), w - F (ys (φ n))⟫_ℝ ≤
        (1 / (1 + ‖vs (φ n)‖)) * ⟪vs (φ n), w - F (ys (φ n))⟫_ℝ)).trans hm1
      simpa only [one_div, real_inner_smul_left] using hh
    simpa only [ha0, zero_mul, zero_add] using hh
  have hzN : z ∈ normalCone (closure (effectiveDomain g)) (F x) := by
    rw [normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hc).closure hxD]
    have hsub : effectiveDomain g ⊆ {w | ⟪z, w - F x⟫_ℝ ≤ 0} := fun w hw ↦ hsupport w hw
    have hclosed : IsClosed {w : T | ⟪z, w - F x⟫_ℝ ≤ 0} :=
      isClosed_le (by fun_prop) continuous_const
    exact closure_minimal hsub hclosed
  have hz0 := hQ z hzN hAz
  rw [ha0, hz0, norm_zero, add_zero] at hsum
  exact zero_ne_one hsum

end Multipliers

section Taylor

variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- A `C²` mapping has a uniform second-order Taylor bound on a small closed ball. -/
theorem exists_quadratic_bound_of_contDiffOn {F : E → T} {V : Set E} (hV : IsOpen V) {x : E}
    (hx : x ∈ V) {r : ℕ} (hr : 2 ≤ r) (hF : ContDiffOn ℝ r F V) :
    ∃ δ > 0, ∃ L : ℝ, 0 ≤ L ∧ closedBall x δ ⊆ V ∧ ∀ y ∈ closedBall x δ, ∀ y' ∈ closedBall x δ,
      ‖F y' - F y - fderiv ℝ F y (y' - y)‖ ≤ L * ‖y' - y‖ ^ 2 := by
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hV x hx
  have hδ : 0 < δ₀ / 2 := half_pos hδ₀
  have hsub : closedBall x (δ₀ / 2) ⊆ V := (closedBall_subset_ball (half_lt_self hδ₀)).trans hball
  have h12 : (1 : WithTop ℕ∞) + 1 ≤ (r : WithTop ℕ∞) := by
    have : ((2 : ℕ) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hr
    simpa [one_add_one_eq_two] using this
  have hF' : ContDiffOn ℝ 1 (fderiv ℝ F) V := hF.fderiv_of_isOpen hV h12
  obtain ⟨K, hK⟩ := (hF'.mono hsub).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall x (δ₀ / 2)) (isCompact_closedBall x (δ₀ / 2))
  have hdiffV : ∀ z ∈ V, HasFDerivAt F (fderiv ℝ F z) z := fun z hz ↦
    ((hF.differentiableOn (by norm_cast; omega)) z hz).differentiableAt
      (hV.mem_nhds hz) |>.hasFDerivAt
  refine ⟨δ₀ / 2, hδ, K, K.coe_nonneg, hsub, fun y hy y' hy' ↦ ?_⟩
  have hseg : segment ℝ y y' ⊆ closedBall x (δ₀ / 2) :=
    (convex_closedBall x _).segment_subset hy hy'
  have hdiff : ∀ z ∈ segment ℝ y y', HasFDerivWithinAt (fun z ↦ F z - fderiv ℝ F y z)
      (fderiv ℝ F z - fderiv ℝ F y) (segment ℝ y y') z := fun z hz ↦
    ((hdiffV z (hsub (hseg hz))).sub (fderiv ℝ F y).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ segment ℝ y y', ‖fderiv ℝ F z - fderiv ℝ F y‖ ≤ K * ‖y' - y‖ := by
    intro z hz
    calc ‖fderiv ℝ F z - fderiv ℝ F y‖ ≤ K * ‖z - y‖ := hK.norm_sub_le (hseg hz) hy
      _ ≤ K * ‖y' - y‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg
  have h := (convex_segment y y').norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff hbound
    (left_mem_segment ℝ y y') (right_mem_segment ℝ y y')
  calc ‖F y' - F y - fderiv ℝ F y (y' - y)‖
      = ‖(F y' - fderiv ℝ F y y') - (F y - fderiv ℝ F y y)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ K * ‖y' - y‖ * ‖y' - y‖ := h
    _ = K * ‖y' - y‖ ^ 2 := by ring

end Taylor

section Proposition1332

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The uniform inequality behind Proposition 13.32 yields prox-regularity. -/
theorem isProxRegularAt_of_uniform {f : E → EReal} {x v : E} (hl : IsLocallyLscAt f x)
    (hv : v ∈ subdifferential f x) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (h : ∀ y v', v' ∈ subdifferential f y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ closedBall x ε, f y + ((⟪v', x' - y⟫_ℝ - ρ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x') :
    IsProxRegularAt f x v :=
  ⟨hl, hv, ε, hε, ρ, hρ, fun y v' hv' h1 h2 _ x' hx' ↦ h y v' hv' h1 h2 x' hx'⟩

/-- The uniform inequality behind Proposition 13.32, used in both directions, yields
subdifferential continuity. -/
theorem isSubdifferentiallyContinuousAt_of_uniform {f : E → EReal} {x v : E}
    (hv : v ∈ subdifferential f x) {ε ρ : ℝ} (hε : 0 < ε)
    (h : ∀ y v', v' ∈ subdifferential f y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ closedBall x ε, f y + ((⟪v', x' - y⟫_ℝ - ρ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x') :
    IsSubdifferentiallyContinuousAt f x v := by
  refine ⟨hv, fun xs vs hxs hvs hmem ↦ ?_⟩
  obtain ⟨c, hc⟩ := hv.1
  choose d hd using fun n ↦ (hmem n).1
  have hx0 : Tendsto (fun n ↦ xs n - x) atTop (𝓝 0) := by simpa using hxs.sub_const x
  have hv0 : Tendsto (fun n ↦ vs n - v) atTop (𝓝 0) := by simpa using hvs.sub_const v
  have hev : ∀ᶠ n in atTop, ‖xs n - x‖ < ε ∧ ‖vs n - v‖ < ε :=
    (hx0.norm.eventually (gt_mem_nhds (by simpa using hε))).and
      (hv0.norm.eventually (gt_mem_nhds (by simpa using hε)))
  have hlowT : Tendsto (fun n ↦ c + ⟪v, xs n - x⟫_ℝ - ρ / 2 * ‖xs n - x‖ ^ 2) atTop (𝓝 c) := by
    have h1 := ((tendsto_const_nhds (x := v)).inner hx0).const_add c
    have h2 := ((hx0.norm.pow 2).const_mul (ρ / 2))
    simpa using h1.sub h2
  have hupT : Tendsto (fun n ↦ c - ⟪vs n, x - xs n⟫_ℝ + ρ / 2 * ‖x - xs n‖ ^ 2) atTop (𝓝 c) := by
    have hx0' : Tendsto (fun n ↦ x - xs n) atTop (𝓝 0) := by simpa using (hxs.const_sub x)
    have h1 := (hvs.inner hx0').const_sub c
    have h2 := ((hx0'.norm.pow 2).const_mul (ρ / 2))
    simpa using h1.add h2
  rw [hc]
  refine (EReal.tendsto_coe.2 (tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowT hupT ?_ ?_)).congr'
    (.of_forall fun n ↦ (hd n).symm)
  · filter_upwards [hev] with n ⟨hn1, _⟩
    have h1 := h x v hv (by simpa using hε) (by simpa using hε) (xs n)
      (by rw [mem_closedBall, dist_eq_norm]; exact hn1.le)
    rw [hc, hd n, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    linarith
  · filter_upwards [hev] with n ⟨hn1, hn2⟩
    have h1 := h (xs n) (vs n) (hmem n) hn2 hn1 x (mem_closedBall_self hε.le)
    rw [hc, hd n, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    linarith

variable [FiniteDimensional ℝ E]

/-- The uniform prox-regularity inequality at the base point of a `C²` amenable model. -/
theorem AmenableFunctionModel.exists_uniform_prox {f : E → EReal} {x v : E} {full : Bool}
    (M : AmenableFunctionModel f x 2 full) :
    ∃ ε > 0, ∃ ρ ≥ 0, ∀ y v', v' ∈ subdifferential f y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ closedBall x ε, f y + ((⟪v', x' - y⟫_ℝ - ρ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤
        f x' := by
  have hcont : ContinuousAt M.inner x :=
    M.smooth.continuousOn.continuousAt (M.isOpen.mem_nhds M.mem)
  have hder : ContinuousAt (fderiv ℝ M.inner) x :=
    (M.smooth.continuousOn_fderiv_of_isOpen M.isOpen
      (by exact_mod_cast (by norm_num : 1 ≤ 2))).continuousAt (M.isOpen.mem_nhds M.mem)
  have hA : ContinuousAt (fun y ↦ (fderiv ℝ M.inner y).adjoint) x :=
    ContinuousLinearMap.adjoint.continuous.continuousAt.comp hder
  obtain ⟨ε₁, hε₁, η, hη⟩ := exists_multiplier_bound_of_convex M.proper M.lsc M.convex hcont hA
    M.qualification v
  obtain ⟨δ, hδ, L, hL0, hδV, hquad⟩ :=
    exists_quadratic_bound_of_contDiffOn M.isOpen M.mem le_rfl M.smooth
  obtain ⟨ε₂, hε₂, hε₂Q⟩ := Metric.mem_nhds_iff.1 (M.qualification_eventually (by norm_num))
  set ε := min (min ε₁ δ) ε₂ with hε_def
  have hε : 0 < ε := lt_min (lt_min hε₁ hδ) hε₂
  have hεδ : ε ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  set η' := max η 0
  refine ⟨ε, hε, 2 * η' * L, by positivity, ?_⟩
  intro y v' hv' hvv hyx x' hx'
  have hyb : y ∈ closedBall x δ := by rw [mem_closedBall, dist_eq_norm]; linarith
  have hx'b : x' ∈ closedBall x δ := closedBall_subset_closedBall hεδ hx'
  have hyV := hδV hyb
  have hx'V := hδV hx'b
  have hyQ : y ∈ ball x ε₂ := by
    rw [mem_ball, dist_eq_norm]
    exact hyx.trans_le (min_le_right _ _)
  have hfin : f y ≠ ⊥ ∧ f y ≠ ⊤ := by
    obtain ⟨a, ha⟩ := hv'.1
    exact ⟨by rw [ha]; exact EReal.coe_ne_bot a, by rw [ha]; exact EReal.coe_ne_top a⟩
  let My : AmenableFunctionModel f y 2 full :=
    { M with mem := hyV, finite := hfin, qualification := hε₂Q hyQ }
  have hform : subdifferential f y =
      (fderiv ℝ M.inner y).adjoint '' subdifferential M.outer (M.inner y) :=
    (My.derivatives (by norm_num)).1
  rw [hform] at hv'
  obtain ⟨u, hu, rfl⟩ := hv'
  have hεε₁ : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hyε₁ : dist y x < ε₁ := by
    rw [dist_eq_norm]
    exact hyx.trans_le hεε₁
  have hun : ‖u‖ ≤ η := hη y hyε₁ u hu (hvv.trans_le hεε₁)
  obtain ⟨c, hc⟩ := hu.1
  have hsg := (mem_subdifferential_iff_of_convex M.convex M.proper hc).mp hu (M.inner x')
  rw [M.eqOn y hyV, M.eqOn x' hx'V, hc]
  refine le_trans ?_ hsg
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have h1 := hquad y hyb x' hx'b
  have h3 : ‖u‖ * ‖M.inner x' - M.inner y - fderiv ℝ M.inner y (x' - y)‖ ≤
      η' * (L * ‖x' - y‖ ^ 2) :=
    mul_le_mul (hun.trans (le_max_left _ _)) h1 (norm_nonneg _) (le_max_right _ _)
  have h4 := (abs_le.1 (abs_real_inner_le_norm u
    (M.inner x' - M.inner y - fderiv ℝ M.inner y (x' - y)))).1
  rw [ContinuousLinearMap.adjoint_inner_left, inner_sub_right]
  rw [inner_sub_right, inner_sub_right] at h4
  nlinarith

/-- **Proposition 13.32** at `x̄`: a strongly amenable function is prox-regular and
subdifferentially continuous at `x̄` for every `v̄ ∈ ∂f(x̄)`. -/
theorem StronglyAmenableAt.isProxRegularAt {f : E → EReal} {x v : E} (h : StronglyAmenableAt f x)
    (hv : v ∈ subdifferential f x) :
    IsProxRegularAt f x v ∧ IsSubdifferentiallyContinuousAt f x v := by
  obtain ⟨M⟩ := h
  have hl : IsLocallyLscAt f x :=
    (StronglyAmenableAt.amenableAt ⟨M⟩).isSubdifferentiallyRegularAt.isLocallyLscAt
  obtain ⟨ε, hε, ρ, hρ, hu⟩ := M.exists_uniform_prox (v := v)
  exact ⟨isProxRegularAt_of_uniform hl hv hε hρ hu,
    isSubdifferentiallyContinuousAt_of_uniform hv hε hu⟩

/-- **Proposition 13.32** (prox-regularity from amenability): a function strongly amenable at
`x̄` is prox-regular and subdifferentially continuous at `x̄`, and at all points of `dom f` near
`x̄`. -/
theorem prox_regularity_from_amenability {f : E → EReal} {x : E} (h : StronglyAmenableAt f x) :
    (IsProxRegularAtPoint f x ∧ IsSubdifferentiallyContinuousAtPoint f x) ∧
      ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain f →
        IsProxRegularAtPoint f y ∧ IsSubdifferentiallyContinuousAtPoint f y := by
  have key : ∀ y, StronglyAmenableAt f y →
      IsProxRegularAtPoint f y ∧ IsSubdifferentiallyContinuousAtPoint f y := fun y hy ↦
    ⟨fun v hv ↦ (hy.isProxRegularAt hv).1, fun v hv ↦ (hy.isProxRegularAt hv).2⟩
  exact ⟨key x h, h.eventually.mono fun y hy hyd ↦ key y (hy hyd)⟩

end Proposition1332

end RW
