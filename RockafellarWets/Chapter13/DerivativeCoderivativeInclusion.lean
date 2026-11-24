/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Derivative-coderivative inclusion

Theorem 13.57 and Corollary 13.58.  In the proof of Theorem 13.40 (`ProxCore`), twice epi-differentiability gives the
graph of `H = D(∂f)(x̄ | v̄)` as `{(u - λG₀(u), G₀(u))}` for the positively homogeneous Lipschitz
limit `G₀` of the difference quotients of `∇e_λ f`; `G₀` is the gradient of a `C¹` potential, so its
Jacobians are symmetric where they exist.  At such points `u` (dense, by Rademacher's theorem),
`(z̄, -w̄)` and `(-z̄, w̄)` are regular normals to `gph H` at `(w̄, z̄) = (u - λG₀(u), G₀(u))`, as in the
proof of the book; 8.44(a) and the closedness of `gph D*(∂f)(x̄ | v̄)` give 13(37).  For 13.58,
full amenability persists near `x̄` and the coderivative graphs are outer semicontinuous (6.6).
-/

import RockafellarWets.Chapter13.SecondSubderivativeConvexity
import RockafellarWets.Chapter13.GeneralizedHessians
import RockafellarWets.Chapter8.DerivativesOfDerivatives
import Mathlib.Analysis.Calculus.Rademacher

open Filter Set Topology Metric MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The potential `u ↦ ∫₀¹ ⟪G(su), u⟫ ds` of a mapping `G`. -/
noncomputable def linePotential (G : E → E) (u : E) : ℝ := ∫ s in (0 : ℝ)..1, ⟪G (s • u), u⟫_ℝ

namespace ProxCore

variable {f : E → EReal} {x : E} {ε : ℝ} (K : ProxCore f x ε) {G₀ : E → E}

omit [FiniteDimensional ℝ E] in
theorem Gs_smul {τ t : ℝ} (ht : 0 < t) (u : E) : K.Gs τ (t • u) = t • K.Gs (τ * t) u := by
  simp only [Gs, smul_smul]
  congr 1
  field_simp

omit [FiniteDimensional ℝ E] in
theorem G₀_smul (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) {t : ℝ}
    (ht : 0 < t) (u : E) : G₀ (t • u) = t • G₀ u := by
  have hmap : Tendsto (fun τ : ℝ ↦ τ * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun τ : ℝ ↦ τ * t) (𝓝 0) (𝓝 (0 * t)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact mul_pos hτ ht
  have h2 : Tendsto (fun τ ↦ t • K.Gs (τ * t) u) (𝓝[>] 0) (𝓝 (t • G₀ u)) :=
    ((hG₀ u).comp hmap).const_smul t
  exact tendsto_nhds_unique (hG₀ (t • u)) (h2.congr fun τ ↦ (K.Gs_smul ht u).symm)

omit [FiniteDimensional ℝ E] in
theorem G₀_lip (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (a b : E) :
    ‖G₀ a - G₀ b‖ ≤ 3 / K.lam * ‖a - b‖ := by
  refine le_of_tendsto ((hG₀ a).sub (hG₀ b)).norm ?_
  filter_upwards [self_mem_nhdsWithin, K.eventually_mem_U (max ‖a‖ ‖b‖)] with τ hτ hU
  exact K.Gs_lip hτ (hU a (le_max_left _ _)) (hU b (le_max_right _ _))

omit [FiniteDimensional ℝ E] in
theorem continuous_G₀ (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    Continuous G₀ := by
  have hlam := K.hlam
  refine (LipschitzWith.of_dist_le_mul (K := ⟨3 / K.lam, by positivity⟩) fun a b ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk]
  exact K.G₀_lip hG₀ a b

omit [FiniteDimensional ℝ E] in
theorem ks_sub_eq_integral {τ : ℝ} (hτ : 0 < τ) {u v : E}
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + τ • (u + s • v) ∈ proxRange f x ε K.lam) :
    K.ks τ (u + v) - K.ks τ u = ∫ s in (0 : ℝ)..1, ⟪K.Gs τ (u + s • v), v⟫_ℝ := by
  have hlam := K.hlam
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ K.ks τ (u + s • v)) ⟪K.Gs τ (u + s • v), v⟫_ℝ s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 := K.ks_hasFDerivAt hτ (hseg s hs)
    have h2 : HasDerivAt (fun s : ℝ ↦ u + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add u
    have h3 := h1.comp_hasDerivAt s h2
    simpa using h3
  have hcont : ContinuousOn (fun s : ℝ ↦ ⟪K.Gs τ (u + s • v), v⟫_ℝ) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine (LipschitzOnWith.of_dist_le_mul
      (K := ⟨3 / K.lam * ‖v‖ ^ 2, by positivity⟩) fun a ha b hb ↦ ?_).continuousOn
    rw [Real.dist_eq, ← inner_sub_left, NNReal.coe_mk, Real.dist_eq]
    have h1 := K.Gs_lip hτ (hseg a ha) (hseg b hb)
    rw [show u + a • v - (u + b • v) = (a - b) • v by rw [sub_smul]; abel, norm_smul,
      Real.norm_eq_abs] at h1
    calc |⟪K.Gs τ (u + a • v) - K.Gs τ (u + b • v), v⟫_ℝ| ≤
          ‖K.Gs τ (u + a • v) - K.Gs τ (u + b • v)‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ 3 / K.lam * (|a - b| * ‖v‖) * ‖v‖ := by gcongr
      _ = 3 / K.lam * ‖v‖ ^ 2 * |a - b| := by ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp

omit [FiniteDimensional ℝ E] in
/-- The potential of `G₀` is the limit of the `kτ`: its increments are line integrals of `G₀`. -/
theorem linePotential_sub (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u v : E) :
    linePotential G₀ (u + v) - linePotential G₀ u = ∫ s in (0 : ℝ)..1, ⟪G₀ (u + s • v), v⟫_ℝ := by
  have hlam := K.hlam
  have h1 := (K.tendsto_ks hG₀ (u + v)).sub (K.tendsto_ks hG₀ u)
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, x + τ • (u + s • v) ∈ proxRange f x ε K.lam := by
    filter_upwards [self_mem_nhdsWithin, K.eventually_mem_U (‖u‖ + ‖v‖)] with τ hτ hU
    refine ⟨hτ, fun s hs ↦ hU _ ?_⟩
    calc ‖u + s • v‖ ≤ ‖u‖ + ‖s • v‖ := norm_add_le _ _
      _ ≤ ‖u‖ + ‖v‖ := by
          rw [norm_smul, Real.norm_of_nonneg hs.1]
          linarith [mul_le_of_le_one_left (norm_nonneg v) hs.2]
  have h2 : Tendsto (fun τ ↦ ∫ s in (0 : ℝ)..1, ⟪K.Gs τ (u + s • v), v⟫_ℝ) (𝓝[>] 0)
      (𝓝 (∫ s in (0 : ℝ)..1, ⟪G₀ (u + s • v), v⟫_ℝ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ 3 / K.lam * (‖u‖ + ‖v‖) * ‖v‖) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hev] with τ ⟨hτ, hU⟩
      rw [uIoc_of_le zero_le_one]
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine (LipschitzOnWith.of_dist_le_mul
        (K := ⟨3 / K.lam * ‖v‖ ^ 2, by positivity⟩) fun a ha b hb ↦ ?_).continuousOn
      rw [Real.dist_eq, ← inner_sub_left, NNReal.coe_mk, Real.dist_eq]
      have h1 := K.Gs_lip hτ (hU a (Ioc_subset_Icc_self ha)) (hU b (Ioc_subset_Icc_self hb))
      rw [show u + a • v - (u + b • v) = (a - b) • v by rw [sub_smul]; abel, norm_smul,
        Real.norm_eq_abs] at h1
      calc |⟪K.Gs τ (u + a • v) - K.Gs τ (u + b • v), v⟫_ℝ| ≤
            ‖K.Gs τ (u + a • v) - K.Gs τ (u + b • v)‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ 3 / K.lam * (|a - b| * ‖v‖) * ‖v‖ := by gcongr
        _ = 3 / K.lam * ‖v‖ ^ 2 * |a - b| := by ring
    · filter_upwards [hev] with τ ⟨hτ, hU⟩
      refine Eventually.of_forall fun s hs ↦ ?_
      rw [uIoc_of_le zero_le_one] at hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
      have hn : ‖u + s • v‖ ≤ ‖u‖ + ‖v‖ := by
        calc ‖u + s • v‖ ≤ ‖u‖ + ‖s • v‖ := norm_add_le _ _
          _ ≤ ‖u‖ + ‖v‖ := by
              rw [norm_smul, Real.norm_of_nonneg hs'.1]
              linarith [mul_le_of_le_one_left (norm_nonneg v) hs'.2]
      rw [Real.norm_eq_abs]
      calc |⟪K.Gs τ (u + s • v), v⟫_ℝ| ≤ ‖K.Gs τ (u + s • v)‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ 3 / K.lam * ‖u + s • v‖ * ‖v‖ := by gcongr; exact K.norm_Gs_le hτ (hU s hs')
        _ ≤ 3 / K.lam * (‖u‖ + ‖v‖) * ‖v‖ := by gcongr
    · exact Eventually.of_forall fun s _ ↦ (hG₀ (u + s • v)).inner tendsto_const_nhds
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [hev] with τ ⟨hτ, hU⟩
  exact (K.ks_sub_eq_integral hτ hU).symm

omit [FiniteDimensional ℝ E] in
/-- The potential of `G₀` is differentiable with gradient `G₀`. -/
theorem hasFDerivAt_linePotential (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u)))
    (u : E) :
    HasFDerivAt (linePotential G₀) (innerSL ℝ (G₀ u)) u := by
  have hlam := K.hlam
  have hcont := K.continuous_G₀ hG₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbound : ∀ v : E, ‖linePotential G₀ (u + v) - linePotential G₀ u - innerSL ℝ (G₀ u) v‖ ≤
      3 / K.lam * ‖v‖ ^ 2 := by
    intro v
    have hint1 : IntervalIntegrable (fun s : ℝ ↦ ⟪G₀ (u + s • v), v⟫_ℝ) volume 0 1 :=
      ((hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).inner
        continuous_const).intervalIntegrable 0 1
    rw [K.linePotential_sub hG₀, innerSL_apply_apply]
    have hconst : ⟪G₀ u, v⟫_ℝ = ∫ s in (0 : ℝ)..1, ⟪G₀ u, v⟫_ℝ := by simp
    rw [hconst, ← intervalIntegral.integral_sub hint1 intervalIntegrable_const]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun s : ℝ ↦ ⟪G₀ (u + s • v), v⟫_ℝ - ⟪G₀ u, v⟫_ℝ) (C := 3 / K.lam * ‖v‖ ^ 2)
      (fun s hs ↦ ?_)
    · simpa using h
    rw [uIoc_of_le zero_le_one] at hs
    change ‖⟪G₀ (u + s • v), v⟫_ℝ - ⟪G₀ u, v⟫_ℝ‖ ≤ _
    rw [← inner_sub_left, Real.norm_eq_abs]
    calc |⟪G₀ (u + s • v) - G₀ u, v⟫_ℝ| ≤ ‖G₀ (u + s • v) - G₀ u‖ * ‖v‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ 3 / K.lam * ‖u + s • v - u‖ * ‖v‖ := by gcongr; exact K.G₀_lip hG₀ _ _
      _ ≤ 3 / K.lam * ‖v‖ * ‖v‖ := by
          gcongr
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1.le]
          exact mul_le_of_le_one_left (norm_nonneg v) hs.2
      _ = 3 / K.lam * ‖v‖ ^ 2 := by ring
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun v : E ↦ ‖v‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (3 / K.lam) (Eventually.of_forall fun v ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg ‖v‖)]
  exact hbound v

theorem gradient_linePotential (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    gradient (linePotential G₀) = G₀ := by
  funext u
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  convert K.hasFDerivAt_linePotential hG₀ u using 1

/-- The Jacobians of `G₀` are symmetric where they exist. -/
theorem fderiv_G₀_inner_comm (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u)))
    {u : E} (hu : DifferentiableAt ℝ G₀ u) (a b : E) :
    ⟪fderiv ℝ G₀ u a, b⟫_ℝ = ⟪a, fderiv ℝ G₀ u b⟫_ℝ := by
  have hgrad := K.gradient_linePotential hG₀
  have h := hessian_inner_comm (f := linePotential G₀)
    (Eventually.of_forall fun y ↦ (K.hasFDerivAt_linePotential hG₀ y).differentiableAt)
    (by rw [hgrad]; exact hu) a b
  rwa [hgrad] at h

omit [FiniteDimensional ℝ E] in
/-- Euler's identity for the positively homogeneous `G₀`. -/
theorem fderiv_G₀_self (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) {u : E}
    (hu : DifferentiableAt ℝ G₀ u) : fderiv ℝ G₀ u u = G₀ u := by
  have h1 : HasDerivAt (fun t : ℝ ↦ G₀ (t • u)) (fderiv ℝ G₀ u u) 1 := by
    have hp : HasDerivAt (fun t : ℝ ↦ t • u) u 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const u
    have hu' : HasFDerivAt G₀ (fderiv ℝ G₀ u) ((1 : ℝ) • u) := by
      rw [one_smul]; exact hu.hasFDerivAt
    exact hu'.comp_hasDerivAt (1 : ℝ) hp
  have h2 : HasDerivAt (fun t : ℝ ↦ G₀ (t • u)) (G₀ u) 1 := by
    have h3 : HasDerivAt (fun t : ℝ ↦ t • G₀ u) (G₀ u) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const (G₀ u)
    apply h3.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds one_pos] with t ht
    exact K.G₀_smul hG₀ ht u
  exact h1.unique h2

omit [FiniteDimensional ℝ E] in
theorem w0_add (u : E) : K.w0 G₀ u + K.lam • G₀ u = u := by simp [w0]

/-- At a point `u` where `G₀` is differentiable, with `(w̄, z̄) = (w₀(u), G₀(u))`, the vector
`σ(z̄, -w̄)` (`|σ| ≤ 1`) is a regular normal to `{(w, z) ∣ G₀(w + λz) = z}` at `(w̄, z̄)`. -/
theorem regularNormal_of_differentiableAt
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) {u : E}
    (hu : DifferentiableAt ℝ G₀ u) {σ : ℝ} (hσ : |σ| ≤ 1) :
    WithLp.toLp 2 (σ • G₀ u, -(σ • K.w0 G₀ u)) ∈
      regularNormalCone {p : WithLp 2 (E × E) | G₀ (p.fst + K.lam • p.snd) = p.snd}
        (WithLp.toLp 2 (K.w0 G₀ u, G₀ u)) := by
  have hlam := K.hlam
  set A := fderiv ℝ G₀ u
  have hsym := K.fderiv_G₀_inner_comm hG₀ hu
  have heul := K.fderiv_G₀_self hG₀ hu
  rw [mem_regularNormalCone]
  refine ⟨by simp [K.w0_add], fun η hη ↦ ?_⟩
  set c := (‖u‖ + 1) * (1 + K.lam) with hc
  have hcpos : 0 < c := by positivity
  have ho := hu.hasFDerivAt.isLittleO.def (show 0 < η / c by positivity)
  have hcont : Tendsto (fun p : WithLp 2 (E × E) ↦ p.fst + K.lam • p.snd)
      (𝓝 (WithLp.toLp 2 (K.w0 G₀ u, G₀ u))) (𝓝 u) := by
    have h : Continuous fun p : WithLp 2 (E × E) ↦ p.fst + K.lam • p.snd :=
      (WithLp.fstL 2 ℝ E E).continuous.add ((WithLp.sndL 2 ℝ E E).continuous.const_smul K.lam)
    have h2 := h.tendsto (WithLp.toLp 2 (K.w0 G₀ u, G₀ u))
    simpa [K.w0_add] using h2
  filter_upwards [nhdsWithin_le_nhds (hcont.eventually ho), self_mem_nhdsWithin] with p hp hpC
  set u' := p.fst + K.lam • p.snd with hu'
  set a := p.fst - K.w0 G₀ u
  set b := p.snd - G₀ u
  have hb : b = G₀ u' - G₀ u := by simp only [b, hpC]
  have hua : u' - u = a + K.lam • b := by
    simp only [hu', a, b, w0, smul_sub]
    abel
  have hinner : ⟪WithLp.toLp 2 (σ • G₀ u, -(σ • K.w0 G₀ u)),
      p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u)⟫_ℝ =
      -(σ * ⟪u, G₀ u' - G₀ u - A (u' - u)⟫_ℝ) := by
    rw [WithLp.prod_inner_apply]
    change ⟪σ • G₀ u, a⟫_ℝ + ⟪-(σ • K.w0 G₀ u), b⟫_ℝ = _
    have ha : a = u' - u - K.lam • b := by rw [hua]; abel
    rw [ha, hb]
    have hw0 : K.w0 G₀ u = u - K.lam • G₀ u := rfl
    have hAu : ⟪G₀ u, u' - u⟫_ℝ = ⟪u, A (u' - u)⟫_ℝ := by
      rw [← heul]; exact hsym u (u' - u)
    have e1 : ⟪σ • G₀ u, u' - u - K.lam • (G₀ u' - G₀ u)⟫_ℝ =
        σ * ⟪G₀ u, u' - u⟫_ℝ - σ * K.lam * ⟪G₀ u, G₀ u' - G₀ u⟫_ℝ := by
      rw [real_inner_smul_left, inner_sub_right, real_inner_smul_right]; ring
    have e2 : ⟪-(σ • K.w0 G₀ u), G₀ u' - G₀ u⟫_ℝ =
        -(σ * ⟪u, G₀ u' - G₀ u⟫_ℝ) + σ * K.lam * ⟪G₀ u, G₀ u' - G₀ u⟫_ℝ := by
      rw [hw0, inner_neg_left, real_inner_smul_left, inner_sub_left, real_inner_smul_left]; ring
    have e3 : ⟪u, G₀ u' - G₀ u - A (u' - u)⟫_ℝ = ⟪u, G₀ u' - G₀ u⟫_ℝ - ⟪u, A (u' - u)⟫_ℝ :=
      inner_sub_right _ _ _
    rw [e1, e2, e3, hAu]
    ring
  rw [hinner]
  have hnorm : ‖u' - u‖ ≤ (1 + K.lam) * ‖p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u)‖ := by
    rw [hua]
    have h1 : ‖a‖ ≤ ‖p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u)‖ := by
      have := WithLp.norm_fst_le (x := p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u))
      simpa [a, WithLp.sub_fst] using this
    have h2 : ‖b‖ ≤ ‖p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u)‖ := by
      have := WithLp.norm_snd_le (x := p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u))
      simpa [b, WithLp.sub_snd] using this
    calc ‖a + K.lam • b‖ ≤ ‖a‖ + K.lam * ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hlam.le]
      _ ≤ (1 + K.lam) * ‖p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u)‖ := by nlinarith
  have hR : ‖G₀ u' - G₀ u - A (u' - u)‖ ≤ η / c * ‖u' - u‖ := hp
  calc -(σ * ⟪u, G₀ u' - G₀ u - A (u' - u)⟫_ℝ) ≤ |σ * ⟪u, G₀ u' - G₀ u - A (u' - u)⟫_ℝ| :=
        neg_le_abs _
    _ = |σ| * |⟪u, G₀ u' - G₀ u - A (u' - u)⟫_ℝ| := abs_mul _ _
    _ ≤ 1 * (‖u‖ * ‖G₀ u' - G₀ u - A (u' - u)‖) :=
        mul_le_mul hσ (abs_real_inner_le_norm _ _) (abs_nonneg _) zero_le_one
    _ ≤ 1 * (‖u‖ * (η / c * ((1 + K.lam) * ‖p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u)‖))) := by
        gcongr
        exact hR.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
    _ ≤ η * ‖p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u)‖ := by
        rw [one_mul, hc]
        have h1 : ‖u‖ * (η / ((‖u‖ + 1) * (1 + K.lam)) * (1 + K.lam)) ≤ η := by
          rw [show ‖u‖ * (η / ((‖u‖ + 1) * (1 + K.lam)) * (1 + K.lam)) = η * (‖u‖ / (‖u‖ + 1)) by
            field_simp]
          exact mul_le_of_le_one_right hη.le ((div_le_one (by positivity)).2 (by linarith))
        nlinarith [norm_nonneg (p - WithLp.toLp 2 (K.w0 G₀ u, G₀ u))]

end ProxCore

/-- **Theorem 13.57** (derivative-coderivative inclusion).  If `f` is prox-regular,
subdifferentially continuous and twice epi-differentiable at `x̄` for `v̄`, then
`D(∂f)(x̄ | v̄) ⊂ D*(∂f)(x̄ | v̄)`, and more precisely, for all `w`,
`D(∂f)(x̄ | v̄)(w) ∪ [-D(∂f)(x̄ | v̄)(-w)] ⊂ D*(∂f)(x̄ | v̄)(w) ∩ [-D*(∂f)(x̄ | v̄)(-w)]`
(13(37)). -/
theorem derivative_coderivative_inclusion {f : E → EReal} {x v : E} (hf : IsProxRegularAt f x v)
    (hsc : IsSubdifferentiallyContinuousAt f x v) (hte : TwiceEpiDifferentiableAt f x v) :
    (∀ w, graphicalDerivative (subdifferential f) x v w ⊆
      coderivative (subdifferential f) x v w) ∧
    ∀ w, graphicalDerivative (subdifferential f) x v w ∪
        -graphicalDerivative (subdifferential f) x v (-w) ⊆
      coderivative (subdifferential f) x v w ∩ -coderivative (subdifferential f) x v (-w) := by
  obtain ⟨f₁, ε, K, -, hte₁, hsc_agree, -⟩ := hf.exists_proxCore
  have hagree := hsc_agree hsc
  choose G₀ hG₀ using K.tendsto_Gs_of_twiceEpi (hte₁.2 hte)
  have hlam := K.hlam
  set S := subdifferential f with hS
  have hD : graphicalDerivative S x v = graphicalDerivative (proxLocalization f₁ x ε) x 0 :=
    (isProtoDifferentiableAt_iff_of_eventually hagree).2
  have hgraphD : euclideanSvGraph (graphicalDerivative S x v) =
      {p : WithLp 2 (E × E) | G₀ (p.fst + K.lam • p.snd) = p.snd} := by
    ext p
    rw [hD]
    exact Set.ext_iff.1 (K.svGraph_graphicalDerivative hG₀) (p.fst, p.snd)
  have hmemD : ∀ w z, z ∈ graphicalDerivative S x v w ↔ G₀ (w + K.lam • z) = z := by
    intro w z
    have := Set.ext_iff.1 hgraphD (WithLp.toLp 2 (w, z))
    simpa using this
  -- local closedness of `gph ∂f` at `(x̄, v̄)`
  have hlc : IsLocallyClosedAt (euclideanSvGraph S) (WithLp.toLp 2 (x, v)) := by
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 hagree
    have hδ := K.hδ₀
    set r := min (r₁ / 2) (K.δ₀ / (2 * (1 + K.lam))) with hr_def
    have hr : 0 < r := by positivity
    have hrr₁ : r < r₁ := by have := min_le_left (r₁ / 2) (K.δ₀ / (2 * (1 + K.lam))); linarith
    have hrδ : (1 + K.lam) * r < K.δ₀ := by
      have h1 := min_le_right (r₁ / 2) (K.δ₀ / (2 * (1 + K.lam)))
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    set B : Set (E × E) := closedBall (x, v) r
    have hBU : ∀ q ∈ B, q.1 + K.lam • (q.2 - v) ∈ ball x K.δ₀ := by
      intro q hq
      rw [mem_closedBall, Prod.dist_eq, max_le_iff, dist_eq_norm, dist_eq_norm] at hq
      rw [mem_ball, dist_eq_norm]
      calc ‖q.1 + K.lam • (q.2 - v) - x‖ = ‖(q.1 - x) + K.lam • (q.2 - v)‖ := by congr 1; abel
        _ ≤ ‖q.1 - x‖ + K.lam * ‖q.2 - v‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, Real.norm_of_nonneg hlam.le]
        _ ≤ r + K.lam * r := by nlinarith [hq.1, hq.2]
        _ < K.δ₀ := by linarith
    have hB : ∀ q ∈ B, (q.2 ∈ S q.1 ↔ K.G (q.1 + K.lam • (q.2 - v)) - (q.2 - v) = 0) := by
      intro q hq
      have h1 : q ∈ {p : E × E | p.2 ∈ subdifferential f p.1 ↔
          p.2 - v ∈ proxLocalization f₁ x ε p.1} := hball₁ (closedBall_subset_ball hrr₁ hq)
      simp only [mem_setOf_eq] at h1
      rw [hS, h1, K.hgraph, sub_eq_zero]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨K.hball (hBU q hq), h⟩⟩
    have hGcont : ContinuousOn K.G (proxRange f₁ x ε K.lam) :=
      (LipschitzOnWith.of_dist_le_mul (K := ⟨3 / K.lam, by positivity⟩) fun a ha b hb ↦ by
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk]
        exact K.hGLip b hb a ha).continuousOn
    have hBcl : IsClosed (svGraph S ∩ B) := by
      have heq : svGraph S ∩ B =
          B ∩ (fun q : E × E ↦ K.G (q.1 + K.lam • (q.2 - v)) - (q.2 - v)) ⁻¹' {0} := by
        ext q
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h2, (hB q h2).1 h1⟩
        · rintro ⟨h2, h1⟩
          exact ⟨(hB q h2).2 h1, h2⟩
      rw [heq]
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_ isClosed_closedBall isClosed_singleton
      refine ContinuousOn.sub (hGcont.comp (Continuous.continuousOn (by fun_prop)) ?_)
        (by fun_prop)
      exact fun q hq ↦ K.hball (hBU q hq)
    set L := WithLp.prodContinuousLinearEquiv 2 ℝ E E
    refine ⟨L ⁻¹' B, L.continuous.continuousAt.preimage_mem_nhds (closedBall_mem_nhds _ hr),
      isClosed_closedBall.preimage L.continuous, ?_⟩
    exact hBcl.preimage L.continuous
  have hv : v ∈ S x := hf.2.1
  -- the inclusion at differentiability points of `G₀`
  have key : ∀ u, DifferentiableAt ℝ G₀ u →
      G₀ u ∈ coderivative S x v (K.w0 G₀ u) ∧ -G₀ u ∈ coderivative S x v (-K.w0 G₀ u) := by
    intro u hu
    have hsub := fun y ↦ coderivative_graphicalDerivative_subset hv hlc (K.w0 G₀ u) (G₀ u) y
    have hN : ∀ σ : ℝ, |σ| ≤ 1 → WithLp.toLp 2 (σ • G₀ u, -(σ • K.w0 G₀ u)) ∈
        normalCone (euclideanSvGraph (graphicalDerivative S x v))
          (WithLp.toLp 2 (K.w0 G₀ u, G₀ u)) := by
      intro σ hσ
      rw [hgraphD]
      exact regularNormalCone_subset_normalCone _ _ (K.regularNormal_of_differentiableAt hG₀ hu hσ)
    constructor
    · refine (hsub (K.w0 G₀ u)).2 ((hsub (K.w0 G₀ u)).1 ?_)
      have h := hN 1 (by simp)
      simpa using h
    · refine (hsub (-K.w0 G₀ u)).2 ((hsub (-K.w0 G₀ u)).1 ?_)
      have h := hN (-1) (by simp)
      change WithLp.toLp 2 (-G₀ u, -(-K.w0 G₀ u)) ∈ normalCone
        (euclideanSvGraph (graphicalDerivative S x v)) (WithLp.toLp 2 (K.w0 G₀ u, G₀ u))
      rw [neg_neg]
      simpa using h
  -- closedness of the target and density of differentiability points
  have hclosed : IsClosed {q : E × E | q.2 ∈ coderivative S x v q.1 ∧
      -q.2 ∈ coderivative S x v (-q.1)} := by
    have hN := isClosed_normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x, v))
    have hc1 : Continuous fun q : E × E ↦ WithLp.toLp 2 (q.2, -q.1) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous.comp (by fun_prop)
    have hc2 : Continuous fun q : E × E ↦ WithLp.toLp 2 (-q.2, -(-q.1)) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous.comp (by fun_prop)
    exact (hN.preimage hc1).inter (hN.preimage hc2)
  have hdense : Dense {u : E | DifferentiableAt ℝ G₀ u} := by
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    have hLip : LipschitzWith ⟨3 / K.lam, by positivity⟩ G₀ :=
      LipschitzWith.of_dist_le_mul fun a b ↦ by
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk]; exact K.G₀_lip hG₀ a b
    have hae := hLip.ae_differentiableAt (μ := MeasureTheory.Measure.addHaar)
    rw [dense_iff_inter_open]
    intro U hU hne
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have hsub : U ⊆ {u | ¬DifferentiableAt ℝ G₀ u} := fun u hu hd ↦
      (eq_empty_iff_forall_notMem.1 hcon) u ⟨hu, hd⟩
    have h0 : MeasureTheory.Measure.addHaar {u : E | ¬DifferentiableAt ℝ G₀ u} = 0 :=
      MeasureTheory.ae_iff.1 hae
    have hpos := hU.measure_pos (MeasureTheory.Measure.addHaar : MeasureTheory.Measure E) hne
    exact hpos.ne' (MeasureTheory.measure_mono_null hsub h0)
  have hφ : Continuous fun u : E ↦ (K.w0 G₀ u, G₀ u) :=
    (continuous_id.sub ((K.continuous_G₀ hG₀).const_smul K.lam)).prodMk (K.continuous_G₀ hG₀)
  have hall : ∀ u, G₀ u ∈ coderivative S x v (K.w0 G₀ u) ∧
      -G₀ u ∈ coderivative S x v (-K.w0 G₀ u) := by
    intro u
    have h1 : (fun u : E ↦ (K.w0 G₀ u, G₀ u)) '' {u | DifferentiableAt ℝ G₀ u} ⊆
        {q : E × E | q.2 ∈ coderivative S x v q.1 ∧ -q.2 ∈ coderivative S x v (-q.1)} := by
      rintro _ ⟨u, hu, rfl⟩
      exact key u hu
    have h2 := (image_closure_subset_closure_image hφ).trans
      (closure_minimal h1 hclosed)
    rw [hdense.closure_eq] at h2
    exact h2 ⟨u, mem_univ u, rfl⟩
  have hmain : ∀ w z, z ∈ graphicalDerivative S x v w →
      z ∈ coderivative S x v w ∧ -z ∈ coderivative S x v (-w) := by
    intro w z hz
    rw [hmemD] at hz
    have h := hall (w + K.lam • z)
    have hw : K.w0 G₀ (w + K.lam • z) = w := by simp [ProxCore.w0, hz]
    rw [hw, hz] at h
    exact h
  refine ⟨fun w z hz ↦ (hmain w z hz).1, fun w z hz ↦ ?_⟩
  rcases hz with hz | hz
  · exact ⟨(hmain w z hz).1, by simpa using (hmain w z hz).2⟩
  · have hz' : -z ∈ graphicalDerivative S x v (-w) := hz
    obtain ⟨h1, h2⟩ := hmain (-w) (-z) hz'
    rw [neg_neg, neg_neg] at h2
    exact ⟨h2, by simpa using h1⟩

/-- **Corollary 13.58** (subgradient coderivatives of fully amenable functions).  If `f` is fully
amenable at `x̄`, then for every `v̄ ∈ ∂f(x̄)` the graphical outer limit of the proto-derivatives
`D(∂f)(x | v)` as `(x, v) → (x̄, v̄)` in `gph ∂f` is contained in `D*(∂f)(x̄ | v̄)`. -/
theorem subgradient_coderivatives_of_fully_amenable {f : E → EReal} {x v : E}
    (hf : FullyAmenableAt f x) (hv : v ∈ subdifferential f x) :
    outerSetLimitAlong (𝓝[svGraph (subdifferential f)] (x, v))
        (fun p : E × E ↦ svGraph (graphicalDerivative (subdifferential f) p.1 p.2)) ⊆
      svGraph (coderivative (subdifferential f) x v) := by
  intro q hq
  obtain ⟨ps, qs, hps, hqs, hqto⟩ := mem_outerSetLimitAlong_iff_exists_seq.1 hq
  obtain ⟨hps1, hps2⟩ := tendsto_nhdsWithin_iff.1 hps
  -- full amenability at the nearby points, then Theorem 13.57 there
  have hfa : ∀ᶠ n in atTop, FullyAmenableAt f (ps n).1 :=
    (((continuous_fst.tendsto (x, v)).comp hps1).eventually hf.eventually).mp
      (hps2.mono fun n hn hdom ↦ hdom (by
        obtain ⟨⟨c, hc⟩, -⟩ := mem_subdifferential_iff_exists_seq.1 hn
        change f (ps n).1 < ⊤
        rw [hc]; exact EReal.coe_lt_top _))
  have hcod : ∀ᶠ n in atTop,
      (qs n).2 ∈ coderivative (subdifferential f) (ps n).1 (ps n).2 (qs n).1 := by
    filter_upwards [hfa, hps2] with n hn hmem
    have hmem' : (ps n).2 ∈ subdifferential f (ps n).1 := hmem
    obtain ⟨hpr, hsc⟩ := hn.stronglyAmenableAt.isProxRegularAt hmem'
    exact (derivative_coderivative_inclusion hpr hsc
      (hn.properlyTwiceEpiDifferentiableAt hmem').1).1 _ (hqs n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hcod.and hps2)
  set L := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  have hL : Continuous fun p : E × E ↦ WithLp.toLp 2 p := L.symm.continuous
  have hxs : Tendsto (fun n ↦ WithLp.toLp 2 (ps (n + N))) atTop (𝓝 (WithLp.toLp 2 (x, v))) :=
    (hL.tendsto _).comp (hps1.comp (tendsto_add_atTop_nat N))
  have hvs : Tendsto (fun n ↦ WithLp.toLp 2 ((qs (n + N)).2, -(qs (n + N)).1)) atTop
      (𝓝 (WithLp.toLp 2 (q.2, -q.1))) := by
    have hc : Continuous fun r : E × E ↦ WithLp.toLp 2 (r.2, -r.1) :=
      hL.comp (continuous_snd.prodMk continuous_fst.neg)
    exact (hc.tendsto _).comp (hqto.comp (tendsto_add_atTop_nat N))
  exact mem_normalCone_of_tendsto (C := euclideanSvGraph (subdifferential f)) hv
    (fun n ↦ (hN (n + N) (Nat.le_add_left N n)).2) hxs
    (fun n ↦ (hN (n + N) (Nat.le_add_left N n)).1) hvs

end RW
