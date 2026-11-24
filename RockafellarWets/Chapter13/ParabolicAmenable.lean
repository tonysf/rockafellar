/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Parabolic aspects of fully amenable functions

Theorem 13.67 and Corollary 13.68.  As in the proof of 13.67, we work with a representation
`f = g ∘ F` with `g` convex piecewise linear-quadratic and `F` of class `C²`: parabolic
epi-differentiability and formula 13(40) come from 13.63 and 13.61, parabolic regularity from the
linear-programming duality of 13.14 applied to `dg(F(x̄))`, and the conjugacy of
`h = d²f(x̄)(w ∣ ·)` and `k` from parabolic regularity together with a separation argument.  A fully
amenable function agrees near `x̄` with such a composition, and all these notions only depend on
the function near `x̄`.
-/

import RockafellarWets.Chapter13.ParabolicChainRule
import RockafellarWets.Chapter13.PiecewiseLinearQuadraticParabolic
import RockafellarWets.Chapter13.SecondOrderChainRuleAmenable
import RockafellarWets.Chapter12.MonotoneRangesGrowth
import RockafellarWets.Chapter11.ProximalTransform
import RockafellarWets.Chapter11.PiecewiseLinearConjugacy
import RockafellarWets.Chapter10.AmenableExamples
import RockafellarWets.Chapter10.AmenableIndicatorEquivalence
import RockafellarWets.Chapter10.AmenableRegularity
import RockafellarWets.Chapter11.SupportConjugates

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Localization of parabolic notions -/

omit [FiniteDimensional ℝ E] in
/-- Along `τ ↓ 0`, `z' → z`, the points `x̄ + τw + ½τ²z'` eventually lie in any neighborhood of
`x̄`. -/
theorem eventually_parabolic_mem_of_mem_nhds {x : E} {U : Set E} (hU : U ∈ 𝓝 x) (w z : E) :
    ∀ᶠ p : ℝ × E in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 z, x + p.1 • w + (p.1 ^ 2 / 2) • p.2 ∈ U := by
  have h1 : Tendsto (fun p : ℝ × E ↦ p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 0) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).comp tendsto_fst
  have h : Tendsto (fun p : ℝ × E ↦ x + p.1 • w + (p.1 ^ 2 / 2) • p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z)
      (𝓝 (x + (0 : ℝ) • w + ((0 : ℝ) ^ 2 / 2) • z)) :=
    (tendsto_const_nhds.add (h1.smul tendsto_const_nhds)).add
      (((h1.pow 2).div_const 2).smul tendsto_snd)
  simp only [zero_smul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div] at h
  exact h.eventually hU

omit [FiniteDimensional ℝ E] in
/-- Parabolic subderivatives only depend on the function near `x̄`. -/
theorem parabolicSubderivative_congr_nhds {f₁ f₂ : E → EReal} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂)
    (w z : E) : parabolicSubderivative f₁ x w z = parabolicSubderivative f₂ x w z := by
  refine liminf_congr ?_
  filter_upwards [eventually_parabolic_mem_of_mem_nhds h w z] with p hp
  have hp' : f₁ (x + p.1 • w + (p.1 ^ 2 / 2) • p.2) = f₂ (x + p.1 • w + (p.1 ^ 2 / 2) • p.2) := hp
  simp only [parabolicDifferenceQuotient, hp', h.self_of_nhds, subderivative_congr_nhds h w]

omit [FiniteDimensional ℝ E] in
/-- Parabolic epi-differentiability only depends on the function near `x̄`. -/
theorem IsParabolicallyEpiDifferentiableAt.congr_nhds {f₁ f₂ : E → EReal} {x w : E}
    (h : f₁ =ᶠ[𝓝 x] f₂) (h₂ : IsParabolicallyEpiDifferentiableAt f₂ x w) :
    IsParabolicallyEpiDifferentiableAt f₁ x w := by
  obtain ⟨h1, h2, h3, h4, ⟨z₀, hz₀⟩, hinner, -⟩ := h₂
  have hx : f₁ x = f₂ x := h.self_of_nhds
  have hd : subderivative f₁ x w = subderivative f₂ x w := subderivative_congr_nhds h w
  have hpar : parabolicSubderivative f₁ x w = parabolicSubderivative f₂ x w :=
    funext fun z ↦ parabolicSubderivative_congr_nhds h w z
  refine ⟨hx ▸ h1, hx ▸ h2, hd ▸ h3, hd ▸ h4, ⟨z₀, by rw [hpar]; exact hz₀⟩, ?_,
    (epigraph_parabolicSubderivative f₁ x w).symm⟩
  apply le_antisymm
  · exact (innerSetLimitAlong_subset_outerSetLimitAlong _).trans
      (epigraph_parabolicSubderivative f₁ x w).symm.le
  · rw [hpar, ← hinner]
    intro q hq N hN
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (h : {y | f₁ y = f₂ y} ∈ 𝓝 x)
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
    have hpos : 0 < δ / (‖w‖ + ‖q.1‖ + r + 1) := by positivity
    filter_upwards [hq (ball q r) (ball_mem_nhds q hr), self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hpos one_pos))] with τ ⟨p, hp, hpq⟩ hτ hτδ
    have hτ' : (0 : ℝ) < τ := hτ
    have hτ1 : τ < 1 := lt_of_lt_of_le hτδ (min_le_right _ _)
    have hτ2 : τ < δ / (‖w‖ + ‖q.1‖ + r + 1) := lt_of_lt_of_le hτδ (min_le_left _ _)
    refine ⟨p, ?_, hrN hpq⟩
    have hp1 : ‖p.1‖ < ‖q.1‖ + r := by
      have h1 : dist p.1 q.1 < r :=
        lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) (mem_ball.1 hpq)
      have h2 := norm_le_norm_add_norm_sub' p.1 q.1
      rw [dist_eq_norm] at h1
      linarith
    have hmem : x + τ • w + (τ ^ 2 / 2) • p.1 ∈ {y | f₁ y = f₂ y} := by
      refine hball ?_
      rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
      have hτδ' : τ * (‖w‖ + ‖q.1‖ + r + 1) < δ := by
        rw [lt_div_iff₀ (by positivity)] at hτ2; exact hτ2
      calc ‖τ • w + (τ ^ 2 / 2) • p.1‖ ≤ ‖τ • w‖ + ‖(τ ^ 2 / 2) • p.1‖ := norm_add_le _ _
        _ = τ * ‖w‖ + τ ^ 2 / 2 * ‖p.1‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hτ'.le,
            Real.norm_of_nonneg (by positivity)]
        _ ≤ τ * (‖w‖ + ‖q.1‖ + r + 1) := by
          have : τ ^ 2 / 2 * ‖p.1‖ ≤ τ * ‖p.1‖ := by
            have : τ ^ 2 / 2 ≤ τ := by nlinarith
            exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
          nlinarith [norm_nonneg p.1, norm_nonneg w]
        _ < δ := hτδ'
    change (p.2 : EReal) ≥ parabolicDifferenceQuotient f₁ x w τ p.1
    have heq : parabolicDifferenceQuotient f₁ x w τ p.1 =
        parabolicDifferenceQuotient f₂ x w τ p.1 := by
      have hm : f₁ (x + τ • w + (τ ^ 2 / 2) • p.1) = f₂ (x + τ • w + (τ ^ 2 / 2) • p.1) := hmem
      simp only [parabolicDifferenceQuotient, hx, hd, hm]
    rw [heq]
    exact hp

omit [FiniteDimensional ℝ E] in
/-- Parabolic regularity only depends on the function near `x̄`. -/
theorem IsParabolicallyRegularAt.congr_nhds {f₁ f₂ : E → EReal} {x v : E}
    (h : f₁ =ᶠ[𝓝 x] f₂) (h₂ : IsParabolicallyRegularAt f₂ x v) :
    IsParabolicallyRegularAt f₁ x v := by
  obtain ⟨⟨c, hc⟩, hreg⟩ := h₂
  refine ⟨⟨c, h.self_of_nhds.trans hc⟩, fun w hw ↦ ?_⟩
  rw [subderivative_congr_nhds h] at hw
  simp only [parabolicSubderivative_congr_nhds h, secondSubderivative_congr_nhds h]
  exact hreg w hw

/-! ### Compositions with convex piecewise linear-quadratic functions -/

/-- `(γ + (a + c)) - c = γ + a` in `EReal` for real `a`, `c`. -/
theorem ereal_add_coe_add_sub_coe (γ : EReal) (a c : ℝ) :
    γ + ((a + c : ℝ) : EReal) - (c : EReal) = γ + (a : EReal) := by
  induction γ using EReal.rec <;> simp [← EReal.coe_add, ← EReal.coe_sub]
  ring

/-- **Theorem 13.67** for a composition `f = g ∘ F`, `g` convex piecewise linear-quadratic and `F`
of class `C²`, under the qualification of 13.14: for every `w ∈ dom df(x̄)`, `f` is parabolically
epi-differentiable at `x̄` for `w` and formula 13(40) holds,
`d²f(x̄)(w ∣ z) = d²g(F(x̄))(∇F(x̄)w ∣ ∇²F(x̄)(w, w) + ∇F(x̄)z)
  = d²g(F(x̄))(∇F(x̄)w) + σ_{Y(x̄ ∣ w)}(∇²F(x̄)(w, w) + ∇F(x̄)z)` with
`Y(x̄ ∣ w) = argmax_{y ∈ ∂g(F(x̄))} ⟪y, ∇F(x̄)w⟫`; and `f` is parabolically regular at `x̄` for
every `v ∈ ∂f(x̄)`. -/
theorem parabolic_aspects_comp_plq {G : E → F} (hG : ContDiff ℝ 2 G) {g : F → EReal}
    (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    (∀ w ∈ effectiveDomain (subderivative (g ∘ G) x),
      IsParabolicallyEpiDifferentiableAt (g ∘ G) x w ∧
      ∀ z, parabolicSubderivative (g ∘ G) x w z =
          parabolicSubderivative g (G x) (fderiv ℝ G x w)
            (fderiv ℝ (fderiv ℝ G) x w w + fderiv ℝ G x z) ∧
        parabolicSubderivative (g ∘ G) x w z = secondSubderivativeAt g (G x) (fderiv ℝ G x w) +
          supportFunction {y ∈ subdifferential g (G x) | ∀ y' ∈ subdifferential g (G x),
            ⟪y', fderiv ℝ G x w⟫_ℝ ≤ ⟪y, fderiv ℝ G x w⟫_ℝ}
            (fderiv ℝ (fderiv ℝ G) x w w + fderiv ℝ G x z)) ∧
    ∀ v ∈ subdifferential (g ∘ G) x, IsParabolicallyRegularAt (g ∘ G) x v := by
  set u := G x with hu
  set A := fderiv ℝ G x with hA
  have hfin : g u = ((g u).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (hg.ne_bot u)).symm
  have hl : LowerSemicontinuous g := hg.lowerSemicontinuous
  obtain ⟨hT1, hT2, hT3⟩ := chain_rule_for_parabolic_subderivatives hG hl hfin hQ
  have hlsc : IsLocallyLscAt g u := isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal g hl) _)
  have hr : IsSubdifferentiallyRegularAt g u := (isSubdifferentiallyRegularAt_of_convex hgc hlsc).1
  obtain ⟨hPne, hPpoly, -⟩ := hg.convex_subgradient_properties hgc hx
  have hsupp : subderivative g u = supportFunction (subdifferential g u) :=
    hg.subderivative_eq_support hgc hx
  have hdne : ∀ ζ, subderivative g u ζ ≠ ⊥ := fun ζ ↦ by
    rw [hsupp]; exact ((isProper_supportFunction hPne).2 ζ).ne'
  -- the parabolic formula
  have hpar : ∀ w ∈ effectiveDomain (subderivative (g ∘ G) x),
      IsParabolicallyEpiDifferentiableAt (g ∘ G) x w ∧
      ∀ z, parabolicSubderivative (g ∘ G) x w z =
          parabolicSubderivative g u (A w) (fderiv ℝ (fderiv ℝ G) x w w + A z) ∧
        parabolicSubderivative (g ∘ G) x w z = secondSubderivativeAt g u (A w) +
          supportFunction {y ∈ subdifferential g u | ∀ y' ∈ subdifferential g u,
            ⟪y', A w⟫_ℝ ≤ ⟪y, A w⟫_ℝ} (fderiv ℝ (fderiv ℝ G) x w w + A z) := by
    intro w hw
    have hfw : subderivative (g ∘ G) x w ≠ ⊤ := ne_of_lt hw
    have hfwb : subderivative (g ∘ G) x w ≠ ⊥ := by rw [hT1]; exact hdne _
    have hAw : A w ∈ effectiveDomain (subderivative g u) := by
      change subderivative g u (A w) < ⊤; rw [← hT1]; exact hw
    obtain ⟨hpe, hform, hargmax, -⟩ := parabolic_aspects_of_piecewise_linear_quadratic hg hgc hx hAw
    refine ⟨hT3 w hfwb hfw hr hpe, fun z ↦ ⟨hT2 w hfwb hfw z, ?_⟩⟩
    rw [hT2 w hfwb hfw z, hform, hargmax]
  refine ⟨hpar, fun v hv ↦ ?_⟩
  -- parabolic regularity
  have hfx : (g ∘ G) x = (((g u).toReal : ℝ) : EReal) := hfin
  refine ⟨⟨_, hfx⟩, fun w hw ↦ ?_⟩
  refine le_antisymm ?_ (secondSubderivative_le_iInf_parabolicSubderivative hfx hw)
  have hwd : w ∈ effectiveDomain (subderivative (g ∘ G) x) := by
    change subderivative (g ∘ G) x w < ⊤; rw [hw]; exact EReal.coe_lt_top _
  obtain ⟨-, h1319, -, hif, -, -⟩ := chain_rule_second_subderivatives_plq hG hg hgc hx hQ hv
  obtain ⟨y₀, hy₀, hmax₀, hd2⟩ := h1319 w
  have hdgw : subderivative g u (A w) = ((⟪v, w⟫_ℝ : ℝ) : EReal) := by rw [← hT1]; exact hw
  rw [hif w, if_pos hdgw] at hd2
  -- linear programming for `g' = dg(ū)` at `∇F(x̄)w`
  have hg' : IsPiecewiseLinearQuadratic (subderivative g u) :=
    (hg.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic
  have hg'c : Convex ℝ (epigraph (subderivative g u)) := by
    rw [hsupp]; exact convex_epigraph_of_sublinear (sublinear_supportFunction _)
  have hAw : A w ∈ effectiveDomain (subderivative g u) := by
    change subderivative g u (A w) < ⊤; rw [hdgw]; exact EReal.coe_lt_top _
  have hsub' : subdifferential (subderivative g u) (A w) = {y ∈ subdifferential g u |
      ∀ y' ∈ subdifferential g u, ⟪y', A w⟫_ℝ ≤ ⟪y, A w⟫_ℝ} := by
    rw [hsupp]
    exact subdifferential_supportFunction_eq_argmax hPpoly.isClosed hPpoly.convex hPne (A w)
  have hMS : {y | y ∈ subdifferential (subderivative g u) (A w) ∧ A.adjoint y = v} =
      multiplierSet G g x v := by
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      rw [hsub'] at hy1
      exact ⟨hy1.1, hy2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, hy2⟩
      rw [hsub']
      refine ⟨hy1, fun y' hy' ↦ ?_⟩
      have hle := (hr.subdifferential_eq_regularSubdifferential ▸ hy') |>
        fun h ↦ inner_le_subderivative_of_mem_regularSubdifferential h (A w)
      rw [hdgw, ← hy2, ContinuousLinearMap.adjoint_inner_left] at hle
      exact EReal.coe_le_coe_iff.1 hle
  obtain ⟨hMSne, -, hMScpt⟩ := multiplierSet_properties hG hl hr hQ hv
  obtain ⟨z₁, y₁, hy₁, hmax₁, hLP⟩ := exists_subderivative_eq_max_multiplier hg' hg'c hAw A v
    (fderiv ℝ (fderiv ℝ G) x w w) (by rw [hMS]; exact hMSne) (by rw [hMS]; exact hMScpt)
  rw [hMS] at hy₁ hmax₁
  have hyeq : ⟪y₁, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ = ⟪y₀, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ :=
    le_antisymm (hmax₀ y₁ hy₁) (hmax₁ y₀ hy₀)
  have hσ : subderivative (subderivative g u) (A w) = supportFunction {y ∈ subdifferential g u |
      ∀ y' ∈ subdifferential g u, ⟪y', A w⟫_ℝ ≤ ⟪y, A w⟫_ℝ} := by
    rw [hg'.subderivative_eq_support hg'c hAw, hsub']
  refine iInf_le_of_le z₁ (le_of_eq ?_)
  rw [((hpar w hwd).2 z₁).2, ← hσ, hLP, ereal_add_coe_add_sub_coe, hyeq, hd2]

/-! ### Conjugacy of the parabolic subderivatives -/

/-- Affine precomposition and a real shift preserve piecewise linearity. -/
theorem IsPiecewiseLinear.compAffine_add_const {φ : F → EReal} (hφ : IsPiecewiseLinear φ)
    (A : E →L[ℝ] F) (b : F) (γ : ℝ) :
    IsPiecewiseLinear (fun z ↦ φ (A z + b) + (γ : EReal)) := by
  obtain ⟨m, C, a, c, hC, hdom, hφ⟩ := hφ
  refine ⟨m, fun i ↦ (fun z ↦ A z + b) ⁻¹' C i, fun i ↦ A.adjoint (a i),
    fun i ↦ ⟪a i, b⟫_ℝ + c i + γ, fun i ↦ (hC i).affine_preimage A b, ?_, ?_⟩
  · ext z
    simp only [mem_effectiveDomain_iff, mem_iUnion, mem_preimage]
    have hiff : φ (A z + b) + (γ : EReal) < ⊤ ↔ φ (A z + b) < ⊤ := by
      constructor
      · intro h
        by_contra hne
        rw [not_lt, top_le_iff] at hne
        rw [hne, EReal.top_add_coe] at h
        exact lt_irrefl _ h
      · intro h
        exact EReal.add_lt_top h.ne (EReal.coe_ne_top γ)
    rw [hiff, ← mem_effectiveDomain_iff, hdom, mem_iUnion]
  · intro i z hz
    change φ (A z + b) + (γ : EReal) =
      ((⟪A.adjoint (a i), z⟫_ℝ + (⟪a i, b⟫_ℝ + c i + γ) : ℝ) : EReal)
    rw [hφ i (A z + b) hz, ← EReal.coe_add]
    congr 1
    rw [inner_add_right, ContinuousLinearMap.adjoint_inner_left]
    ring

/-- A proper lsc convex piecewise linear function and its conjugate form a conjugate pair of
proper lsc convex piecewise linear functions (11.1, 11.14). -/
theorem conjugate_pair_of_piecewiseLinear {h k : E → EReal} (hp : IsProper h)
    (hl : LowerSemicontinuous h) (hc : Convex ℝ (epigraph h)) (hpl : IsPiecewiseLinear h)
    (hk : fenchelConjugate h = k) :
    LowerSemicontinuous k ∧ IsProper k ∧ Convex ℝ (epigraph k) ∧ IsPiecewiseLinear k ∧
      fenchelConjugate k = h := by
  subst hk
  exact ⟨lowerSemicontinuous_fenchelConjugate h, isProper_fenchelConjugate hp hl hc,
    convex_epigraph_fenchelConjugate h, (isPiecewiseLinear_fenchelConjugate_iff hp hl hc).2 hpl,
    fenchelConjugate_fenchelConjugate_eq hp hl hc⟩

open Classical in
/-- **Theorem 13.67**, the conjugacy, for a composition `f = g ∘ F` as in
`parabolic_aspects_comp_plq`: for `w ∈ dom df(x̄)`, `h = d²f(x̄)(w ∣ ·)` is lsc, proper, convex and
piecewise linear, and its conjugate is `k(v) = -d²f(x̄ ∣ v)(w)` for
`v ∈ ∂f(x̄ ∣ w) = argmax_{v ∈ ∂f(x̄)} ⟪v, w⟫`, `k(v) = ∞` otherwise. -/
theorem parabolic_conjugacy_comp_plq {G : E → F} (hG : ContDiff ℝ 2 G) {g : F → EReal}
    (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {w : E} (hw : w ∈ effectiveDomain (subderivative (g ∘ G) x)) :
    LowerSemicontinuous (parabolicSubderivative (g ∘ G) x w) ∧
    IsProper (parabolicSubderivative (g ∘ G) x w) ∧
    Convex ℝ (epigraph (parabolicSubderivative (g ∘ G) x w)) ∧
    IsPiecewiseLinear (parabolicSubderivative (g ∘ G) x w) ∧
    fenchelConjugate (parabolicSubderivative (g ∘ G) x w) = fun v ↦
      if v ∈ {v ∈ subdifferential (g ∘ G) x | ∀ v' ∈ subdifferential (g ∘ G) x,
        ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} then -secondSubderivative (g ∘ G) x v w else ⊤ := by
  classical
  set u := G x with hu
  set A := fderiv ℝ G x with hA
  set b := fderiv ℝ (fderiv ℝ G) x w w with hb
  set P := subdifferential g u with hP
  set Yw := {y ∈ P | ∀ y' ∈ P, ⟪y', A w⟫_ℝ ≤ ⟪y, A w⟫_ℝ} with hYw
  obtain ⟨hpar, hreg⟩ := parabolic_aspects_comp_plq hG hg hgc hx hQ
  obtain ⟨hpe, hform⟩ := hpar w hw
  have hform' : ∀ z, parabolicSubderivative (g ∘ G) x w z =
      secondSubderivativeAt g u (A w) + supportFunction Yw (b + A z) := fun z ↦ (hform z).2
  have hfin : g u = ((g u).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (hg.ne_bot u)).symm
  have hl : LowerSemicontinuous g := hg.lowerSemicontinuous
  have hlsc : IsLocallyLscAt g u := isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal g hl) _)
  have hr : IsSubdifferentiallyRegularAt g u := (isSubdifferentiallyRegularAt_of_convex hgc hlsc).1
  obtain ⟨hPne, hPpoly, -⟩ := hg.convex_subgradient_properties hgc hx
  have hsupp : subderivative g u = supportFunction P := hg.subderivative_eq_support hgc hx
  obtain ⟨hT1, -, -⟩ := chain_rule_for_parabolic_subderivatives hG hl hfin hQ
  have hsubC : subdifferential (g ∘ G) x = A.adjoint '' P :=
    subdifferential_comp_eq_of_regular (hG.of_le (by norm_num)) hl hr hQ
  have hdgw : A w ∈ effectiveDomain (subderivative g u) := by
    change subderivative g u (A w) < ⊤; rw [← hT1]; exact hw
  have hg' : IsPiecewiseLinearQuadratic (subderivative g u) :=
    (hg.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic
  have hg'c : Convex ℝ (epigraph (subderivative g u)) := by
    rw [hsupp]; exact convex_epigraph_of_sublinear (sublinear_supportFunction _)
  have hsub' : subdifferential (subderivative g u) (A w) = Yw := by
    rw [hsupp]
    exact subdifferential_supportFunction_eq_argmax hPpoly.isClosed hPpoly.convex hPne (A w)
  obtain ⟨hYne, hYpoly, -⟩ := hg'.convex_subgradient_properties hg'c hdgw
  rw [hsub'] at hYne hYpoly
  have hσpl : IsPiecewiseLinear (supportFunction Yw) := by
    rw [← hsub', ← hg'.subderivative_eq_support hg'c hdgw]
    exact (hg'.subderivative_piecewiseLinear hdgw).1
  have hσne : ∀ ζ, supportFunction Yw ζ ≠ ⊥ := fun ζ ↦ ((isProper_supportFunction hYne).2 ζ).ne'
  -- the constant `γ = d²g(F(x̄))(∇F(x̄)w)` is finite
  have hγnn : 0 ≤ secondSubderivativeAt g u (A w) :=
    ((piecewise_linear_quadratic_second_order hg hgc hx).1.2.2 (A w)).1
  obtain ⟨z₀, hz₀⟩ := hpe.2.2.2.2.1
  have hγtop : secondSubderivativeAt g u (A w) ≠ ⊤ := by
    intro hγ
    rw [hform' z₀, hγ, EReal.top_add_of_ne_bot (hσne _)] at hz₀
    exact lt_irrefl _ hz₀
  set γr := (secondSubderivativeAt g u (A w)).toReal with hγr
  have hγ : secondSubderivativeAt g u (A w) = (γr : EReal) :=
    (EReal.coe_toReal hγtop (ne_bot_of_le_ne_bot EReal.zero_ne_bot hγnn)).symm
  have hfun : parabolicSubderivative (g ∘ G) x w = fun z ↦ supportFunction Yw (A z + b) +
      (γr : EReal) := by
    funext z
    rw [hform' z, hγ, add_comm (γr : EReal), add_comm b]
  -- properties of `h`
  have hlsc_h := lowerSemicontinuous_parabolicSubderivative (g ∘ G) x w
  have hconv_h : Convex ℝ (epigraph (parabolicSubderivative (g ∘ G) x w)) := by
    rw [hfun]
    exact convex_epigraph_add_const_ereal (convex_epigraph_compAffine
      (convex_epigraph_of_sublinear (sublinear_supportFunction Yw)) A b) γr
  have hbot_h : ∀ z, ⊥ < parabolicSubderivative (g ∘ G) x w z := by
    intro z
    rw [hfun]
    exact bot_lt_iff_ne_bot.2 (EReal.add_ne_bot_iff.2 ⟨hσne _, EReal.coe_ne_bot _⟩)
  have hprop_h : IsProper (parabolicSubderivative (g ∘ G) x w) := ⟨⟨z₀, hz₀⟩, hbot_h⟩
  have hpl_h : IsPiecewiseLinear (parabolicSubderivative (g ∘ G) x w) := by
    rw [hfun]; exact hσpl.compAffine_add_const A b γr
  refine ⟨hlsc_h, hprop_h, hconv_h, hpl_h, ?_⟩
  funext v
  by_cases hvD : v ∈ {v ∈ subdifferential (g ∘ G) x | ∀ v' ∈ subdifferential (g ∘ G) x,
      ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ}
  · rw [if_pos hvD]
    -- `df(x̄)(w) = ⟪v, w⟫`
    have hdfw : subderivative (g ∘ G) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) := by
      obtain ⟨hv1, hv2⟩ := hvD
      have hv1' := hv1
      rw [hsubC] at hv1'
      obtain ⟨y₀, hy₀, hvy₀⟩ := hv1'
      rw [hT1, hsupp]
      apply le_antisymm
      · refine iSup_le fun y ↦ ?_
        have := hv2 (A.adjoint y) (by rw [hsubC]; exact ⟨y, y.2, rfl⟩)
        rw [ContinuousLinearMap.adjoint_inner_left] at this
        exact EReal.coe_le_coe_iff.2 this
      · rw [← hvy₀, ContinuousLinearMap.adjoint_inner_left]
        exact le_iSup (fun y : P ↦ ((⟪(y : F), A w⟫_ℝ : ℝ) : EReal)) ⟨y₀, hy₀⟩
    have hregv := (hreg v hvD.1).2 w hdfw
    rw [← hregv, ereal_neg_iInf]
    unfold fenchelConjugate
    congr 1
    funext z
    rw [EReal.neg_sub (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)), sub_eq_add_neg,
      add_comm]
  · rw [if_neg hvD]
    -- separate `v` from `∇F(x̄)* Y(x̄ ∣ w)`
    have hvS : v ∉ (A.adjoint.toLinearMap) '' Yw := by
      rintro ⟨y, hy, hyv⟩
      apply hvD
      refine ⟨by rw [hsubC]; exact ⟨y, hy.1, hyv⟩, fun v' hv' ↦ ?_⟩
      rw [hsubC] at hv'
      obtain ⟨y', hy', rfl⟩ := hv'
      rw [← hyv]
      change ⟪A.adjoint y', w⟫_ℝ ≤ ⟪A.adjoint y, w⟫_ℝ
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
      exact hy.2 y' hy'
    have hSpoly := hYpoly.linear_image A.adjoint.toLinearMap
    obtain ⟨φ, c, hφv, hφS⟩ := geometric_hahn_banach_point_closed hSpoly.convex hSpoly.isClosed hvS
    set ζ := (InnerProductSpace.toDual ℝ E).symm φ with hζ
    have hφ : ∀ p, φ p = ⟪ζ, p⟫_ℝ := fun p ↦ by rw [hζ, InnerProductSpace.toDual_symm_apply]
    set η := -ζ with hη
    have hση : ∀ y ∈ Yw, ⟪y, A η⟫_ℝ ≤ -c := by
      intro y hy
      have h1 := hφS (A.adjoint y) ⟨y, hy, rfl⟩
      rw [hφ, real_inner_comm, ContinuousLinearMap.adjoint_inner_left] at h1
      rw [hη, map_neg, inner_neg_right]
      linarith
    have hvη : -c < ⟪v, η⟫_ℝ := by
      rw [hφ, real_inner_comm] at hφv
      rw [hη, inner_neg_right]
      linarith
    -- growth of `⟪v, z⟫ - h(z)` along `z₀ + tη`
    set r₀ := (parabolicSubderivative (g ∘ G) x w z₀).toReal with hr₀
    have hz₀r : parabolicSubderivative (g ∘ G) x w z₀ = (r₀ : EReal) :=
      (EReal.coe_toReal hz₀.ne (hbot_h z₀).ne').symm
    have hbound : ∀ t : ℝ, 0 < t →
        parabolicSubderivative (g ∘ G) x w (z₀ + t • η) ≤ ((r₀ - t * c : ℝ) : EReal) := by
      intro t ht
      have hsplit : A (z₀ + t • η) + b = (A z₀ + b) + t • A η := by
        rw [map_add, map_smul]; abel
      have hσle : supportFunction Yw ((A z₀ + b) + t • A η) ≤
          supportFunction Yw (A z₀ + b) + ((t * -c : ℝ) : EReal) := by
        refine iSup_le fun y ↦ ?_
        rw [inner_add_right, real_inner_smul_right, EReal.coe_add]
        exact add_le_add (le_iSup (fun y : Yw ↦ ((⟪(y : F), A z₀ + b⟫_ℝ : ℝ) : EReal)) y)
          (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left (hση y y.2) ht.le))
      have hz₀' : supportFunction Yw (A z₀ + b) + (γr : EReal) = (r₀ : EReal) := by
        rw [← hz₀r, hfun]
      rw [hfun]
      dsimp only
      rw [hsplit]
      calc supportFunction Yw ((A z₀ + b) + t • A η) + (γr : EReal)
          ≤ supportFunction Yw (A z₀ + b) + ((t * -c : ℝ) : EReal) + (γr : EReal) :=
            add_le_add hσle le_rfl
        _ = supportFunction Yw (A z₀ + b) + (γr : EReal) + ((t * -c : ℝ) : EReal) := by
            rw [add_right_comm]
        _ = ((r₀ - t * c : ℝ) : EReal) := by
            rw [hz₀', ← EReal.coe_add]; congr 1; ring
    rw [EReal.eq_top_iff_forall_lt]
    intro M
    set κ := ⟪v, η⟫_ℝ + c with hκ
    have hκpos : 0 < κ := by linarith
    set t := max 1 ((M - (⟪v, z₀⟫_ℝ - r₀)) / κ + 1) with ht
    have ht1 : 0 < t := lt_of_lt_of_le one_pos (le_max_left _ _)
    have htM : M < ⟪v, z₀⟫_ℝ - r₀ + t * κ := by
      have h1 : (M - (⟪v, z₀⟫_ℝ - r₀)) / κ < t := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
      rw [div_lt_iff₀ hκpos] at h1
      linarith
    calc (M : EReal) < ((⟪v, z₀ + t • η⟫_ℝ - (r₀ - t * c) : ℝ) : EReal) := by
          apply EReal.coe_lt_coe_iff.2
          rw [inner_add_right, real_inner_smul_right]
          linarith
      _ = ((⟪v, z₀ + t • η⟫_ℝ : ℝ) : EReal) - ((r₀ - t * c : ℝ) : EReal) := EReal.coe_sub _ _
      _ ≤ ((⟪v, z₀ + t • η⟫_ℝ : ℝ) : EReal) - parabolicSubderivative (g ∘ G) x w (z₀ + t • η) :=
          EReal.sub_le_sub le_rfl (hbound t ht1)
      _ ≤ fenchelConjugate (parabolicSubderivative (g ∘ G) x w) v :=
          le_iSup (fun z ↦ ((⟪v, z⟫_ℝ : ℝ) : EReal) - parabolicSubderivative (g ∘ G) x w z)
            (z₀ + t • η)

/-! ### Fully amenable functions -/

open Classical in
/-- The function `k` of Theorem 13.67: `k(v) = -d²f(x̄ ∣ v)(w)` for
`v ∈ ∂f(x̄ ∣ w) = argmax_{v ∈ ∂f(x̄)} ⟪v, w⟫`, and `k(v) = ∞` otherwise. -/
noncomputable def parabolicDualFunction (f : E → EReal) (x w : E) (v : E) : EReal :=
  if v ∈ {v ∈ subdifferential f x | ∀ v' ∈ subdifferential f x, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} then
    -secondSubderivative f x v w else ⊤

theorem parabolicDualFunction_congr_nhds {f₁ f₂ : E → EReal} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂)
    (w : E) : parabolicDualFunction f₁ x w = parabolicDualFunction f₂ x w := by
  funext v
  simp only [parabolicDualFunction, secondSubderivative_congr_nhds h]
  rw [subdifferential_eq_of_eventuallyEq h]

section Amenable

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A model of full amenability yields a global representation `f = g ∘ G₀` near `x̄`, with `g`
convex piecewise linear-quadratic, `G₀` of class `C²` agreeing with the inner mapping near `x̄`,
and the qualification of 13.14. -/
theorem AmenableFunctionModel.exists_global_representation {f : E → EReal} {x : E}
    (M : AmenableFunctionModel f x 2 true) :
    ∃ G₀ : E → M.Target, ContDiff ℝ 2 G₀ ∧ G₀ =ᶠ[𝓝 x] M.inner ∧ f =ᶠ[𝓝 x] M.outer ∘ G₀ ∧
      G₀ x ∈ effectiveDomain M.outer ∧
      ∀ y ∈ horizonSubdifferential M.outer (G₀ x), (fderiv ℝ G₀ x).adjoint y = 0 → y = 0 := by
  obtain ⟨G₀, hG₀, hG₀eq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn M.isOpen M.mem M.smooth
  have hval : M.outer (G₀ x) = ((f x).toReal : EReal) := by
    rw [hG₀eq.self_of_nhds, ← M.eqOn x M.mem]
    exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
  refine ⟨G₀, hG₀, hG₀eq, ?_, ?_, ?_⟩
  · filter_upwards [M.isOpen.mem_nhds M.mem, hG₀eq] with y hy hy'
    rw [Function.comp_apply, hy', M.eqOn y hy]
  · rw [mem_effectiveDomain_iff, hval]; exact EReal.coe_lt_top _
  · intro y hy h0
    rw [horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex hval,
      hG₀eq.self_of_nhds] at hy
    rw [hG₀eq.fderiv_eq] at h0
    exact M.qualification y hy h0

/-- **Theorem 13.67** (parabolic aspects of fully amenable functions).  If `f` is fully amenable at
`x̄`, then `f` is parabolically epi-differentiable at `x̄` for every `w ∈ dom df(x̄)` and
parabolically regular at `x̄` for every `v ∈ ∂f(x̄)`.  For every `w ∈ dom df(x̄)` the function
`h = d²f(x̄)(w ∣ ·)` is lsc, proper, convex and piecewise linear, and so is the function
`k = parabolicDualFunction f x̄ w`, `k(v) = -d²f(x̄ ∣ v)(w)` for `v ∈ ∂f(x̄ ∣ w)` and `∞` otherwise;
`h` and `k` are conjugate to each other.  For every local representation `f = g ∘ F` as in the
definition of full amenability (an `AmenableFunctionModel`), formula 13(40) holds:
`d²f(x̄)(w ∣ z) = d²g(F(x̄))(∇F(x̄)w ∣ ∇²F(x̄)(w, w) + ∇F(x̄)z)
  = d²g(F(x̄))(∇F(x̄)w) + σ_{Y(x̄ ∣ w)}(∇²F(x̄)(w, w) + ∇F(x̄)z)`,
`Y(x̄ ∣ w) = argmax_{y ∈ ∂g(F(x̄))} ⟪y, ∇F(x̄)w⟫`, the support function being the maximum in the
book. -/
theorem parabolic_aspects_of_fully_amenable_functions {f : E → EReal} {x : E}
    (hf : FullyAmenableAt f x) :
    (∀ w ∈ effectiveDomain (subderivative f x), IsParabolicallyEpiDifferentiableAt f x w) ∧
    (∀ v ∈ subdifferential f x, IsParabolicallyRegularAt f x v) ∧
    (∀ w ∈ effectiveDomain (subderivative f x),
      LowerSemicontinuous (parabolicSubderivative f x w) ∧
      IsProper (parabolicSubderivative f x w) ∧
      Convex ℝ (epigraph (parabolicSubderivative f x w)) ∧
      IsPiecewiseLinear (parabolicSubderivative f x w) ∧
      LowerSemicontinuous (parabolicDualFunction f x w) ∧ IsProper (parabolicDualFunction f x w) ∧
      Convex ℝ (epigraph (parabolicDualFunction f x w)) ∧
      IsPiecewiseLinear (parabolicDualFunction f x w) ∧
      fenchelConjugate (parabolicSubderivative f x w) = parabolicDualFunction f x w ∧
      fenchelConjugate (parabolicDualFunction f x w) = parabolicSubderivative f x w) ∧
    (∀ M : AmenableFunctionModel f x 2 true, ∀ w ∈ effectiveDomain (subderivative f x), ∀ z,
      parabolicSubderivative f x w z = parabolicSubderivative M.outer (M.inner x)
          (fderiv ℝ M.inner x w) (fderiv ℝ (fderiv ℝ M.inner) x w w + fderiv ℝ M.inner x z) ∧
      parabolicSubderivative f x w z = secondSubderivativeAt M.outer (M.inner x)
          (fderiv ℝ M.inner x w) +
        supportFunction {y ∈ subdifferential M.outer (M.inner x) |
          ∀ y' ∈ subdifferential M.outer (M.inner x),
            ⟪y', fderiv ℝ M.inner x w⟫_ℝ ≤ ⟪y, fderiv ℝ M.inner x w⟫_ℝ}
          (fderiv ℝ (fderiv ℝ M.inner) x w w + fderiv ℝ M.inner x z)) := by
  -- the composite statements, transported along a local representation
  have hrep : ∀ M : AmenableFunctionModel f x 2 true,
      (∀ w ∈ effectiveDomain (subderivative f x), IsParabolicallyEpiDifferentiableAt f x w ∧
        ∀ z, parabolicSubderivative f x w z = parabolicSubderivative M.outer (M.inner x)
            (fderiv ℝ M.inner x w) (fderiv ℝ (fderiv ℝ M.inner) x w w + fderiv ℝ M.inner x z) ∧
          parabolicSubderivative f x w z = secondSubderivativeAt M.outer (M.inner x)
              (fderiv ℝ M.inner x w) +
            supportFunction {y ∈ subdifferential M.outer (M.inner x) |
              ∀ y' ∈ subdifferential M.outer (M.inner x),
                ⟪y', fderiv ℝ M.inner x w⟫_ℝ ≤ ⟪y, fderiv ℝ M.inner x w⟫_ℝ}
              (fderiv ℝ (fderiv ℝ M.inner) x w w + fderiv ℝ M.inner x z)) ∧
      (∀ v ∈ subdifferential f x, IsParabolicallyRegularAt f x v) ∧
      (∀ w ∈ effectiveDomain (subderivative f x),
        LowerSemicontinuous (parabolicSubderivative f x w) ∧
        IsProper (parabolicSubderivative f x w) ∧
        Convex ℝ (epigraph (parabolicSubderivative f x w)) ∧
        IsPiecewiseLinear (parabolicSubderivative f x w) ∧
        fenchelConjugate (parabolicSubderivative f x w) = parabolicDualFunction f x w) := by
    intro M
    obtain ⟨G₀, hG₀, hG₀eq, hloc, hdom₀, hQ₀⟩ := M.exists_global_representation
    have hg := M.plq rfl
    obtain ⟨hpar, hreg⟩ := parabolic_aspects_comp_plq hG₀ hg M.convex hdom₀ hQ₀
    have hx₀ : G₀ x = M.inner x := hG₀eq.self_of_nhds
    have hd₀ : fderiv ℝ G₀ x = fderiv ℝ M.inner x := hG₀eq.fderiv_eq
    have hdd₀ : fderiv ℝ (fderiv ℝ G₀) x = fderiv ℝ (fderiv ℝ M.inner) x := hG₀eq.fderiv.fderiv_eq
    have hdomw : ∀ w, w ∈ effectiveDomain (subderivative f x) →
        w ∈ effectiveDomain (M.outer ∘ G₀ |> subderivative <| x) := by
      intro w hw
      change subderivative (M.outer ∘ G₀) x w < ⊤
      rw [← subderivative_congr_nhds hloc w]
      exact hw
    have hpf : ∀ w, parabolicSubderivative f x w = parabolicSubderivative (M.outer ∘ G₀) x w :=
      fun w ↦ funext fun z ↦ parabolicSubderivative_congr_nhds hloc w z
    refine ⟨fun w hw ↦ ⟨((hpar w (hdomw w hw)).1).congr_nhds hloc, fun z ↦ ?_⟩,
      fun v hv ↦ (hreg v (by rw [← subdifferential_eq_of_eventuallyEq hloc]; exact hv)).congr_nhds
        hloc, fun w hw ↦ ?_⟩
    · obtain ⟨h1, h2⟩ := (hpar w (hdomw w hw)).2 z
      rw [hpf w, h1, hx₀, hd₀, hdd₀]
      refine ⟨rfl, ?_⟩
      rw [← hx₀, ← hd₀, ← hdd₀, ← h1, h2]
    · obtain ⟨h1, h2, h3, h4, h5⟩ := parabolic_conjugacy_comp_plq hG₀ hg M.convex hdom₀ hQ₀
        (hdomw w hw)
      rw [hpf w, parabolicDualFunction_congr_nhds hloc w]
      exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨M⟩ := hf
  obtain ⟨hpar, hreg, hconj⟩ := hrep M
  refine ⟨fun w hw ↦ (hpar w hw).1, hreg, fun w hw ↦ ?_, fun M' w hw z ↦ ((hrep M').1 w hw).2 z⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hconj w hw
  obtain ⟨k1, k2, k3, k4, k5⟩ := conjugate_pair_of_piecewiseLinear h2 h1 h3 h4 h5
  exact ⟨h1, h2, h3, h4, k1, k2, k3, k4, h5, k5⟩

end Amenable

section AmenableSets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- **Corollary 13.68** (parabolic aspects of fully amenable sets).  If `C` is fully amenable at
`x̄`, then `C` is parabolically derivable at `x̄` for every `w ∈ T_C(x̄)` and parabolically regular
at `x̄` for every `v ∈ N_C(x̄)` (that is, `δ_C` is); for every `w ∈ T_C(x̄)` the second-order
tangent set `T²_C(x̄ ∣ w)` is nonempty and polyhedral, with support function
`σ_{T²_C(x̄ ∣ w)}(v) = -d²δ_C(x̄ ∣ v)(w)` if `v ∈ N_C(x̄)` and `v ⊥ w`, and `∞` otherwise.  As in
the book, this is 13.67 for `f = δ_C`. -/
theorem parabolic_aspects_of_fully_amenable_sets {C : Set E} {x : E}
    (hC : SetFullyAmenableAt C x) :
    (∀ w ∈ tangentCone C x, IsParabolicallyDerivable C x w) ∧
    (∀ v ∈ normalCone C x, IsParabolicallyRegularAt (indicatorVA C) x v) ∧
    ∀ w ∈ tangentCone C x, (secondOrderTangentSet C x w).Nonempty ∧
      IsPolyhedral (secondOrderTangentSet C x w) ∧
      ∀ v, supportFunction (secondOrderTangentSet C x w) v =
        if v ∈ normalCone C x ∧ ⟪v, w⟫_ℝ = 0 then -secondSubderivative (indicatorVA C) x v w
        else ⊤ := by
  have hf : FullyAmenableAt (indicatorVA C) x := setFullyAmenableAt_iff_indicator.1 hC
  have hxC : x ∈ C := by obtain ⟨M⟩ := hC; exact M.base
  obtain ⟨hpe, hreg, hconj, -⟩ := parabolic_aspects_of_fully_amenable_functions hf
  have hdom : effectiveDomain (subderivative (indicatorVA C) x) = tangentCone C x := by
    rw [subderivative_indicatorVA hxC, effectiveDomain_indicatorVA]
  have hr : IsSubdifferentiallyRegularAt (indicatorVA C) x :=
    hf.amenableAt.isSubdifferentiallyRegularAt
  -- normals are polar to tangents
  have hpolar : ∀ v ∈ normalCone C x, ∀ w ∈ tangentCone C x, ⟪v, w⟫_ℝ ≤ 0 := by
    intro v hv w hw
    have hv' : v ∈ regularSubdifferential (indicatorVA C) x := by
      rw [← hr.subdifferential_eq_regularSubdifferential, subdifferential_indicatorVA]; exact hv
    have h := inner_le_subderivative_of_mem_regularSubdifferential hv' w
    rw [subderivative_indicatorVA hxC, indicatorVA_apply_mem hw] at h
    exact_mod_cast h
  have hzero : (0 : E) ∈ normalCone C x := by
    refine regularNormalCone_subset_normalCone C x ?_
    rw [regularNormalCone_eq_polarCone_tangentCone hxC]
    intro w _
    rw [inner_zero_left]
  refine ⟨fun w hw ↦ (isParabolicallyEpiDifferentiableAt_indicatorVA_iff hxC hw).1
      (hpe w (by rw [hdom]; exact hw)),
    fun v hv ↦ hreg v (by rw [subdifferential_indicatorVA]; exact hv), fun w hw ↦ ?_⟩
  obtain ⟨-, hprop, hconv, hpl, -, -, -, -, hhk, -⟩ := hconj w (by rw [hdom]; exact hw)
  have hT2 := parabolicSubderivative_indicatorVA hxC hw
  rw [hT2] at hprop hconv hpl hhk
  refine ⟨?_, ?_, fun v ↦ ?_⟩
  · obtain ⟨z, hz⟩ := hprop.1
    refine ⟨z, ?_⟩
    by_contra hzT
    rw [indicatorVA_apply_not_mem hzT] at hz
    exact lt_irrefl _ hz
  · have h := (hpl.hasPolyhedralEpigraph hconv).effectiveDomain_isPolyhedral
    rwa [effectiveDomain_indicatorVA] at h
  · rw [← fenchelConjugate_indicatorVA, hhk, parabolicDualFunction]
    have hcond : v ∈ {v ∈ subdifferential (indicatorVA C) x |
        ∀ v' ∈ subdifferential (indicatorVA C) x, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} ↔
        v ∈ normalCone C x ∧ ⟪v, w⟫_ℝ = 0 := by
      simp only [mem_setOf_eq, subdifferential_indicatorVA]
      constructor
      · rintro ⟨hv, hmax⟩
        refine ⟨hv, le_antisymm (hpolar v hv w hw) ?_⟩
        have := hmax 0 hzero
        rwa [inner_zero_left] at this
      · rintro ⟨hv, h0⟩
        refine ⟨hv, fun v' hv' ↦ ?_⟩
        rw [h0]
        exact hpolar v' hv' w hw
    by_cases hv : v ∈ normalCone C x ∧ ⟪v, w⟫_ℝ = 0
    · rw [if_pos (hcond.2 hv), if_pos hv]
    · rw [if_neg (fun h ↦ hv (hcond.1 h)), if_neg hv]

end AmenableSets

end RW
