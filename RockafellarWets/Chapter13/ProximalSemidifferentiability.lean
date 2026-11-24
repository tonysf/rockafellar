/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Semidifferentiability of proximal mappings

Exercise 13.45 (`semidifferentiability_of_proximal_mappings`).
-/

import RockafellarWets.Chapter13.QuadraticExpansionCharacterization
import RockafellarWets.Chapter13.NormalConeProjections

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Construction

omit [FiniteDimensional ℝ E] in
/-- The data of `ProxCore` exist for every sufficiently small `λ`, with `P_λ f = {P}` and `e_λ f`
finite on `U = rge(I + λT)`. -/
theorem ProxCore.exists_of_lam {f : E → EReal} {x : E} (hpr : IsProxRegularAt f x 0)
    (hpb : IsProxBounded f) {ε lam₀ : ℝ} (hlam₀ : 0 < lam₀) (H : ProxEnvelopeModel f x ε lam₀) :
    ∃ lam₁ > 0, ∀ lam, 0 < lam → lam < lam₁ → ∃ K : ProxCore f x ε, K.lam = lam ∧
      (∀ u ∈ proxRange f x ε lam, proximalMappingEReal f lam u = {K.P u}) ∧
      (∀ u ∈ proxRange f x ε lam, moreauEnvelopeEReal f lam u = ((K.e u : ℝ) : EReal)) := by
  obtain ⟨ε₂, hε₂, μ, hμ, hglob⟩ := hpr.exists_global_inequality hpb
  obtain ⟨⟨hx1, hx2, -⟩, h0, -⟩ := hpr
  refine ⟨min lam₀ (1 / (2 * μ)), lt_min hlam₀ (by positivity), fun lam hlam hlam₁ ↦ ?_⟩
  have hlamlt : lam < lam₀ := lt_of_lt_of_le hlam₁ (min_le_left _ _)
  have hlammu : lam * μ ≤ 1 / 2 := by
    have h2 : lam ≤ 1 / (2 * μ) := (lt_of_lt_of_le hlam₁ (min_le_right _ _)).le
    calc lam * μ ≤ 1 / (2 * μ) * μ := mul_le_mul_of_nonneg_right h2 hμ.le
      _ = 1 / 2 := by field_simp
  obtain ⟨P, hUo, hxU, hPx, hPsingle, hPmono, hdiff, hGLip, hgr⟩ := H lam hlam hlamlt
  set U := proxRange f x ε lam with hU
  set c := (f x).toReal with hc_def
  have hc : f x = (c : EReal) := (EReal.coe_toReal hx2 hx1).symm
  set G : E → E := fun u ↦ lam⁻¹ • (u - P u) with hG
  -- values of `f` along the graph
  have hval : ∀ u ∈ U, f (P u) =
      (((moreauEnvelopeEReal f lam u).toReal - lam / 2 * ‖G u‖ ^ 2 : ℝ) : EReal) := by
    intro u hu
    have hmem : P u ∈ proximalMappingEReal f lam u := by rw [hPsingle u hu]; exact mem_singleton _
    obtain ⟨hobj, -⟩ := mem_proximalMappingEReal_iff.1 hmem
    obtain ⟨he1, he2, -⟩ := hdiff u hu
    have he : moreauEnvelopeEReal f lam u = ((moreauEnvelopeEReal f lam u).toReal : EReal) :=
      (EReal.coe_toReal he2 he1).symm
    have hnorm : lam / 2 * ‖G u‖ ^ 2 = 1 / (2 * lam) * ‖P u - u‖ ^ 2 := by
      simp only [hG, norm_smul, norm_inv, Real.norm_of_nonneg hlam.le, norm_sub_rev u (P u)]
      field_simp
    rw [proximalObjectiveEReal, he] at hobj
    rw [hnorm]
    rcases ereal_trichotomy (f (P u)) with h' | h' | ⟨r, hr⟩
    · rw [h', EReal.bot_add] at hobj; exact absurd hobj.symm (EReal.coe_ne_bot _)
    · rw [h', EReal.top_add_coe] at hobj; exact absurd hobj (EReal.coe_ne_top _).symm
    · rw [hr] at hobj ⊢
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at hobj
      rw [EReal.coe_eq_coe_iff]
      linarith
  have he : (moreauEnvelopeEReal f lam x).toReal = c := by
    have h := hval x hxU
    rw [hPx, hc, EReal.coe_eq_coe_iff] at h
    simp only [hG, hPx, sub_self, smul_zero, norm_zero] at h
    linarith
  -- the graph of `T`
  have hgraph : ∀ y w, w ∈ proxLocalization f x ε y ↔ y + lam • w ∈ U ∧ G (y + lam • w) = w := by
    intro y w
    constructor
    · intro hw
      have hu : y + lam • w ∈ U := ⟨y, w, hw, rfl⟩
      exact ⟨hu, (hgr _ hu w).2 ⟨y, hw, rfl⟩⟩
    · rintro ⟨hu, hGw⟩
      obtain ⟨y', hy', hyy⟩ := (hgr _ hu w).1 hGw
      rw [add_left_inj] at hyy
      rw [hyy]; exact hy'
  have hPG : ∀ u, P u + lam • G u = u := fun u ↦ by
    simp only [hG, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]; abel
  have hGsub : ∀ u ∈ U, G u ∈ subdifferential f (P u) := by
    intro u hu
    have h := (hgraph (P u) (G u)).2 ⟨by rw [hPG]; exact hu, by rw [hPG]⟩
    exact h.1
  -- continuity of the envelope at `x̄`
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hUo x hxU
  have hecont : ContinuousAt (fun z ↦ (moreauEnvelopeEReal f lam z).toReal) x :=
    (hdiff x hxU).2.2.continuousAt
  obtain ⟨r₁, hr₁, hr₁e⟩ := Metric.continuousAt_iff.1 hecont ε₂ hε₂
  set δ₀ := min r₀ (min r₁ (min (ε₂ / 2) (lam * ε₂ / 3))) with hδ₀_def
  have hδ₀ : 0 < δ₀ := by positivity
  have hδr₀ : δ₀ ≤ r₀ := min_le_left _ _
  have hδr₁ : δ₀ ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ₀ ≤ ε₂ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδl : δ₀ ≤ lam * ε₂ / 3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hballU : ball x δ₀ ⊆ U := (ball_subset_ball hδr₀).trans hr₀U
  have hGx : G x = 0 := by simp [hG, hPx]
  have hineq : ∀ u ∈ ball x δ₀, ∀ x', f (P u) +
      ((⟪G u, x' - P u⟫_ℝ - μ / 2 * ‖x' - P u‖ ^ 2 : ℝ) : EReal) ≤ f x' := by
    intro u hu x'
    have huU := hballU hu
    rw [mem_ball, dist_eq_norm] at hu
    have hPu : ‖P u - x‖ < ε₂ := by
      have := (hPmono x hxU u huU).2
      rw [hPx] at this
      linarith
    have hGu : ‖G u - 0‖ < ε₂ := by
      have h1 := hGLip x hxU u huU
      rw [sub_zero]
      have h2 : ‖G u‖ ≤ 3 / lam * ‖u - x‖ := by
        simp only [hPx, sub_self, smul_zero, sub_zero] at h1
        exact h1
      calc ‖G u‖ ≤ 3 / lam * ‖u - x‖ := h2
        _ < 3 / lam * (lam * ε₂ / 3) := by
            apply mul_lt_mul_of_pos_left (lt_of_lt_of_le hu hδl) (by positivity)
        _ = ε₂ := by field_simp
    have hfu : f (P u) < f x + ε₂ := by
      rw [hval u huU, hc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      have h1 := hr₁e (show dist u x < r₁ by rw [dist_eq_norm]; linarith)
      rw [Real.dist_eq, he] at h1
      have h2 : 0 ≤ lam / 2 * ‖G u‖ ^ 2 := by positivity
      linarith [abs_lt.1 h1]
    exact hglob (P u) (G u) (hGsub u huU) hGu hPu hfu x'
  have hlow : ∀ x', ((c - μ / 2 * ‖x' - x‖ ^ 2 : ℝ) : EReal) ≤ f x' := by
    intro x'
    have h := hglob x 0 h0 (by simpa using hε₂) (by simpa using hε₂)
      (by rw [hc, ← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith)) x'
    rw [hc, inner_zero_left, zero_sub, ← EReal.coe_add] at h
    convert h using 2
  refine ⟨⟨lam, μ, c, δ₀, P, hlam, hμ, hlammu, hδ₀, hc, hUo, hballU, hPx,
    fun u hu u' hu' ↦ (hPmono u hu u' hu').2, hGLip, fun u hu ↦ (hdiff u hu).2.2, he, hval,
    hgraph, hineq, hlow⟩, rfl, hPsingle, fun u hu ↦ ?_⟩
  obtain ⟨he1, he2, -⟩ := hdiff u hu
  exact (EReal.coe_toReal he2 he1).symm


end Construction

/-! ### The proximal mapping -/

namespace ProxCore

variable {f : E → EReal} {x : E} {ε : ℝ} (K : ProxCore f x ε)

omit [FiniteDimensional ℝ E] in
theorem Ps_lip {τ : ℝ} (hτ : 0 < τ) {u u' : E} (hu : x + τ • u ∈ proxRange f x ε K.lam)
    (hu' : x + τ • u' ∈ proxRange f x ε K.lam) : ‖K.Ps τ u - K.Ps τ u'‖ ≤ 2 * ‖u - u'‖ := by
  have h := K.hPLip _ hu' _ hu
  have e1 : x + τ • u - (x + τ • u') = τ • (u - u') := by rw [smul_sub]; abel
  rw [e1, norm_smul, Real.norm_of_nonneg hτ.le] at h
  have e2 : K.Ps τ u - K.Ps τ u' = τ⁻¹ • (K.P (x + τ • u) - K.P (x + τ • u')) := by
    simp only [Ps, smul_sub]; abel
  rw [e2, norm_smul, norm_inv, Real.norm_of_nonneg hτ.le]
  calc τ⁻¹ * ‖K.P (x + τ • u) - K.P (x + τ • u')‖ ≤ τ⁻¹ * (2 * (τ * ‖u - u'‖)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * ‖u - u'‖ := by field_simp

omit [FiniteDimensional ℝ E] in
theorem Ps_zero (τ : ℝ) : K.Ps τ 0 = 0 := by simp [Ps, K.hPx]

omit [FiniteDimensional ℝ E] in
/-- The graphs of the difference quotients of `P_λ f` at `x̄` agree on balls, eventually, with the
graphs of the rescaled mappings `Pτ`. -/
theorem svGraph_quotient_prox_inter_ball
    (hP : ∀ u ∈ proxRange f x ε K.lam, proximalMappingEReal f K.lam u = {K.P u}) (R : ℝ) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      svGraph (mappingDifferenceQuotient (proximalMappingEReal f K.lam) x x τ) ∩ ball 0 R =
        lipschitzParamGraph (fun τ ↦ {u | x + τ • u ∈ proxRange f x ε K.lam}) K.Ps 0 τ ∩
          ball 0 R := by
  filter_upwards [self_mem_nhdsWithin, K.eventually_mem_U R] with τ hτ hU
  ext ⟨u, z⟩
  simp only [mem_inter_iff, and_congr_left_iff]
  intro hp
  rw [mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff] at hp
  have hu := hU u hp.1.le
  change z ∈ mappingDifferenceQuotient (proximalMappingEReal f K.lam) x x τ u ↔
    u + (0 : ℝ) • z ∈ {u | x + τ • u ∈ proxRange f x ε K.lam} ∧ K.Ps τ (u + (0 : ℝ) • z) = z
  rw [mem_mappingDifferenceQuotient_iff (ne_of_gt hτ), zero_smul, add_zero, hP _ hu,
    mem_singleton_iff]
  refine ⟨fun h ↦ ⟨hu, ?_⟩, fun h ↦ ?_⟩
  · rw [← K.add_smul_Ps (ne_of_gt hτ) u] at h
    exact (smul_right_injective E (ne_of_gt hτ)) (add_left_cancel h) |>.symm
  · rw [← h.2, K.add_smul_Ps (ne_of_gt hτ) u]

/-- `P_λ f` is proto-differentiable at `x̄` for `x̄` exactly when the rescaled mappings `Pτ`
converge pointwise. -/
theorem isProtoDifferentiableAt_prox_iff
    (hP : ∀ u ∈ proxRange f x ε K.lam, proximalMappingEReal f K.lam u = {K.P u}) :
    IsProtoDifferentiableAt (proximalMappingEReal f K.lam) x x ↔
      ∀ u, ∃ z, Tendsto (fun τ ↦ K.Ps τ u) (𝓝[>] 0) (𝓝 z) := by
  have hlip : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ u ∈ {u | x + τ • u ∈ proxRange f x ε K.lam},
      ∀ u' ∈ {u | x + τ • u ∈ proxRange f x ε K.lam}, ‖K.Ps τ u - K.Ps τ u'‖ ≤ 2 * ‖u - u'‖ :=
    Filter.mem_of_superset (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
      fun _ hτ _ hu _ hu' ↦ K.Ps_lip hτ hu hu'
  obtain ⟨hin, hout⟩ := setLimits_congr_of_eventually_inter_ball (0 : E × E)
    (fun R _ ↦ K.svGraph_quotient_prox_inter_ball hP R)
  constructor
  · intro h u
    have hK : PKConvergesAlong (𝓝[>] (0 : ℝ))
        (lipschitzParamGraph (fun τ ↦ {u | x + τ • u ∈ proxRange f x ε K.lam}) K.Ps 0)
        (svGraph (graphicalDerivative (proximalMappingEReal f K.lam) x x)) :=
      ⟨hin.symm.trans h.1, hout.symm.trans h.2⟩
    exact tendsto_of_pkConvergesAlong_lipschitzParamGraph (by norm_num)
      K.eventually_closedBall_subset hlip (Eventually.of_forall K.Ps_zero) hK u
  · intro h
    choose P₀ hP₀ using h
    have hK := pkConvergesAlong_lipschitzParamGraph_of_tendsto (lam := 0) (by norm_num)
      K.eventually_closedBall_subset hlip hP₀
    have hD : svGraph (graphicalDerivative (proximalMappingEReal f K.lam) x x) =
        {p : E × E | P₀ (p.1 + (0 : ℝ) • p.2) = p.2} := by
      rw [svGraph_graphicalDerivative_eq_outerLimit, hout, hK.2]
    rw [IsProtoDifferentiableAt, hD]
    exact ⟨hin.trans hK.1, hout.trans hK.2⟩

omit [FiniteDimensional ℝ E] in
theorem exists_tendsto_Ps_iff (u : E) :
    (∃ z, Tendsto (fun τ ↦ K.Ps τ u) (𝓝[>] 0) (𝓝 z)) ↔
      ∃ z, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 z) := by
  have hlam := K.hlam
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨K.lam⁻¹ • (u - z), ?_⟩
    have h := (tendsto_const_nhds (x := u)).sub hz |>.const_smul K.lam⁻¹
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [K.Ps_eq (ne_of_gt hτ), sub_sub_cancel, inv_smul_smul₀ hlam.ne']
  · rintro ⟨z, hz⟩
    refine ⟨u - K.lam • z, ?_⟩
    refine ((tendsto_const_nhds (x := u)).sub (hz.const_smul K.lam)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [K.Ps_eq (ne_of_gt hτ)]

/-- **Exercise 13.45**, (b): `P_λ f` is proto-differentiable at `x̄` exactly when `f` is twice
epi-differentiable at `x̄` for `0`. -/
theorem isProtoDifferentiableAt_prox_iff_twiceEpi
    (hP : ∀ u ∈ proxRange f x ε K.lam, proximalMappingEReal f K.lam u = {K.P u}) :
    IsProtoDifferentiableAt (proximalMappingEReal f K.lam) x x ↔
      TwiceEpiDifferentiableAt f x 0 := by
  rw [K.isProtoDifferentiableAt_prox_iff hP, ← K.core_equivalence.1, K.isProtoDifferentiableAt_iff]
  exact forall_congr' fun u ↦ K.exists_tendsto_Ps_iff u

omit [FiniteDimensional ℝ E] in
/-- Under convergence of `Gτ` to `G₀`, `D[P_λ f](x̄)(u) = {u - λG₀(u)}`. -/
theorem graphicalDerivative_prox {G₀ : E → E}
    (hP : ∀ u ∈ proxRange f x ε K.lam, proximalMappingEReal f K.lam u = {K.P u})
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u : E) :
    graphicalDerivative (proximalMappingEReal f K.lam) x x u = {K.w0 G₀ u} := by
  have hlip : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ u ∈ {u | x + τ • u ∈ proxRange f x ε K.lam},
      ∀ u' ∈ {u | x + τ • u ∈ proxRange f x ε K.lam}, ‖K.Ps τ u - K.Ps τ u'‖ ≤ 2 * ‖u - u'‖ :=
    Filter.mem_of_superset (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
      fun _ hτ _ hu _ hu' ↦ K.Ps_lip hτ hu hu'
  obtain ⟨-, hout⟩ := setLimits_congr_of_eventually_inter_ball (0 : E × E)
    (fun R _ ↦ K.svGraph_quotient_prox_inter_ball hP R)
  have hK := pkConvergesAlong_lipschitzParamGraph_of_tendsto (lam := 0) (by norm_num)
    K.eventually_closedBall_subset hlip (K.tendsto_Ps hG₀)
  have hD : svGraph (graphicalDerivative (proximalMappingEReal f K.lam) x x) =
      {p : E × E | K.w0 G₀ (p.1 + (0 : ℝ) • p.2) = p.2} := by
    rw [svGraph_graphicalDerivative_eq_outerLimit, hout, hK.2]
  ext z
  have := Set.ext_iff.1 hD (u, z)
  simp only [zero_smul, add_zero, mem_setOf_eq] at this
  rw [mem_singleton_iff]
  exact this.trans eq_comm

omit [FiniteDimensional ℝ E] in
/-- The proximal mapping and envelope of `h = ½d²f(x̄ ∣ 0)`: under convergence of `Gτ` to `G₀`,
`P_λ h(u) = {u - λG₀(u)}` and `e_λ h(u) = ∫₀¹ ⟪G₀(su), u⟫ ds`, by the exact quadratic minorants of
`d²f(x̄ ∣ 0)` at `w₀(u)` (`λμ ≤ ½`). -/
theorem prox_half_secondSubderivative {G₀ : E → E}
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u : E) :
    proximalMappingEReal (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w) K.lam u =
        {K.w0 G₀ u} ∧
      moreauEnvelopeEReal (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w) K.lam u =
        ((∫ s in (0 : ℝ)..1, ⟪G₀ (s • u), u⟫_ℝ : ℝ) : EReal) := by
  have hlam := K.hlam
  have hmu := K.hmu
  have hlm := K.hlammu
  set h : E → EReal := fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w with hh
  set w₀ := K.w0 G₀ u with hw₀
  set val : ℝ := ∫ s in (0 : ℝ)..1, ⟪G₀ (s • u), u⟫_ℝ with hval
  set c : ℝ := 1 / (2 * K.lam) - K.mu / 2 with hc
  have hc0 : 0 < c := by
    rw [hc]
    have : K.mu ≤ 1 / (2 * K.lam) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : 1 / (2 * K.lam) - 1 / (4 * K.lam) = 1 / (4 * K.lam) := by field_simp; ring
    have h3 : K.mu / 2 ≤ 1 / (4 * K.lam) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith [show (0 : ℝ) < 1 / (4 * K.lam) by positivity]
  have huw : u - w₀ = K.lam • G₀ u := by rw [hw₀, w0]; abel
  -- the objective at `w₀` and below
  have hobj₀ : proximalObjectiveEReal h K.lam u w₀ = (val : EReal) := by
    rw [proximalObjectiveEReal, hh]
    simp only
    rw [K.secondSubderivative_w0 hG₀, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff,
      norm_sub_rev, huw, norm_smul, Real.norm_of_nonneg hlam.le, eta, hval]
    field_simp
    ring
  have hbound : ∀ w', ((val + c * ‖w' - w₀‖ ^ 2 : ℝ) : EReal) ≤ proximalObjectiveEReal h K.lam u w' := by
    intro w'
    have h1 := K.le_secondSubderivative_of_tendsto hG₀ u w'
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) by
      exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2))
    rw [proximalObjectiveEReal, hh]
    refine le_trans (le_of_eq ?_) (add_le_add h2 le_rfl)
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    have e1 : w' - u = (w' - w₀) - K.lam • G₀ u := by rw [← huw]; abel
    have e2 : w' - K.w0 G₀ u = w' - w₀ := by rw [hw₀]
    rw [e1, e2]
    have hn := norm_sub_sq_real (w' - w₀) (K.lam • G₀ u)
    rw [inner_smul_right, norm_smul, Real.norm_of_nonneg hlam.le] at hn
    rw [hn, eta, ← hval, hc, real_inner_comm (w' - w₀) (G₀ u)]
    field_simp
    ring
  have henv : moreauEnvelopeEReal h K.lam u = (val : EReal) := by
    refine le_antisymm ?_ ?_
    · rw [moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal, ← hobj₀]
      exact iInf_le _ w₀
    · rw [moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal]
      refine le_iInf fun w' ↦ le_trans ?_ (hbound w')
      exact EReal.coe_le_coe_iff.2 (by nlinarith [sq_nonneg ‖w' - w₀‖])
  refine ⟨Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun w' hw' ↦ ?_⟩, henv⟩
  · rw [mem_proximalMappingEReal_iff, hobj₀, henv]
    exact ⟨rfl, EReal.coe_lt_top _⟩
  · rw [mem_proximalMappingEReal_iff, henv] at hw'
    have h1 := hbound w'
    rw [hw'.1, EReal.coe_le_coe_iff] at h1
    have h2 : ‖w' - w₀‖ ^ 2 ≤ 0 := by nlinarith
    have h3 : ‖w' - w₀‖ = 0 := by nlinarith [norm_nonneg (w' - w₀)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h3)

omit [FiniteDimensional ℝ E] in
/-- `P_λ f` has the Aubin property at `x̄` for `x̄`. -/
theorem hasAubinPropertyAt_prox
    (hP : ∀ u ∈ proxRange f x ε K.lam, proximalMappingEReal f K.lam u = {K.P u}) :
    HasAubinPropertyAt (proximalMappingEReal f K.lam) x x := by
  have hxU : x ∈ proxRange f x ε K.lam := K.hball (mem_ball_self K.hδ₀)
  have hPx : x ∈ proximalMappingEReal f K.lam x := by
    rw [hP x hxU, mem_singleton_iff, K.hPx]
  have hball' : ∀ u ∈ ball x K.δ₀, proximalMappingEReal f K.lam u = {K.P u} :=
    fun u hu ↦ hP u (K.hball hu)
  have hPcont : ContinuousOn K.P (ball x K.δ₀) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := 2) fun u hu u' hu' ↦ ?_).continuousOn
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
    exact K.hPLip _ (K.hball hu') _ (K.hball hu)
  refine ⟨mem_univ _, hPx, ⟨closedBall (x, x) (K.δ₀ / 2),
    closedBall_mem_nhds _ (by have := K.hδ₀; positivity), isClosed_closedBall, ?_⟩, 2,
    ball x K.δ₀, ball_mem_nhds x K.hδ₀, univ, univ_mem, fun u₁ hu₁ u₂ hu₂ y₁ hy₁ ↦ ?_⟩
  · have hsub : ∀ p ∈ closedBall (x, x) (K.δ₀ / 2), p.1 ∈ ball x K.δ₀ := by
      intro p hp
      rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hp
      rw [mem_ball]; linarith [hp.1, K.hδ₀]
    have hcont : ContinuousOn (fun p : E × E ↦ (p.2, K.P p.1)) (closedBall (x, x) (K.δ₀ / 2)) :=
      continuous_snd.continuousOn.prodMk
        (hPcont.comp continuous_fst.continuousOn fun p hp ↦ hsub p hp)
    have hcl := hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_diagonal
    convert hcl using 1
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_diagonal_iff]
    constructor
    · rintro ⟨hp, hpb⟩
      refine ⟨hpb, ?_⟩
      have : p.2 ∈ proximalMappingEReal f K.lam p.1 := hp
      rw [hball' p.1 (hsub p hpb), mem_singleton_iff] at this
      exact this
    · rintro ⟨hpb, hp⟩
      refine ⟨?_, hpb⟩
      change p.2 ∈ proximalMappingEReal f K.lam p.1
      rw [hball' p.1 (hsub p hpb), mem_singleton_iff]
      exact hp
  · rw [mem_inter_iff] at hu₁ hu₂
    refine ⟨K.P u₂, by rw [hball' u₂ hu₂.2]; exact mem_singleton _, ?_⟩
    have hy : y₁ = K.P u₁ := by
      have := hy₁.1
      rwa [hball' u₁ hu₁.2, mem_singleton_iff] at this
    rw [hy, dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat, norm_sub_rev u₁ u₂]
    exact K.hPLip _ (K.hball hu₂.2) _ (K.hball hu₁.2) |>.trans_eq (by rw [norm_sub_rev])

/-! ### The envelope -/

omit [FiniteDimensional ℝ E] in
/-- The mean value estimate for `kτ` along a segment: if `Gτ` stays within `C` of `c` there, then
`|kτ(u + v) - kτ(u) - ⟪c, v⟫| ≤ C‖v‖`. -/
theorem abs_ks_add_sub_le {τ : ℝ} (hτ : 0 < τ) {u v c : E} {C : ℝ}
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + τ • (u + s • v) ∈ proxRange f x ε K.lam)
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, ‖K.Gs τ (u + s • v) - c‖ ≤ C) :
    |K.ks τ (u + v) - K.ks τ u - ⟪c, v⟫_ℝ| ≤ C * ‖v‖ := by
  set φ : ℝ → ℝ := fun s ↦ K.ks τ (u + s • v) - s * ⟪c, v⟫_ℝ with hφ
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ (⟪K.Gs τ (u + s • v) - c, v⟫_ℝ) (Icc 0 1) s := by
    intro s hs
    have h1 := K.ks_hasFDerivAt hτ (hseg s hs)
    have hp : HasDerivAt (fun s : ℝ ↦ u + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add u
    have h2 := h1.comp_hasDerivAt s hp
    have h3 : HasDerivAt φ (⟪K.Gs τ (u + s • v), v⟫_ℝ - ⟪c, v⟫_ℝ) s := by
      have := h2.sub ((hasDerivAt_id s).mul_const ⟪c, v⟫_ℝ)
      simp only [innerSL_apply_apply, one_mul] at this
      exact this
    rw [inner_sub_left]
    exact h3.hasDerivWithinAt
  have hb : ∀ s ∈ Ico (0 : ℝ) 1, ‖⟪K.Gs τ (u + s • v) - c, v⟫_ℝ‖ ≤ C * ‖v‖ := fun s hs ↦
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hC s (Ico_subset_Icc_self hs))
      (norm_nonneg _))
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb 1 (by simp)
  simp only [hφ, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, mul_one,
    Real.norm_eq_abs] at h
  rw [show K.ks τ (u + v) - K.ks τ u - ⟪c, v⟫_ℝ = K.ks τ (u + v) - ⟪c, v⟫_ℝ - K.ks τ u by ring]
  exact h

omit [FiniteDimensional ℝ E] in
/-- Eventually, `kτ` is Lipschitz with constant `3R/λ` on `IB(0, R)`, bounded there by `3R²/λ`,
and satisfies the descent estimate `|kτ(u + v) - kτ(u) - ⟪Gτ(u), v⟫| ≤ 3‖v‖²/λ`. -/
theorem eventually_ks_estimates (R : ℝ) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), (∀ u u', ‖u‖ ≤ R → ‖u'‖ ≤ R →
        |K.ks τ u' - K.ks τ u| ≤ 3 / K.lam * R * ‖u' - u‖) ∧
      (∀ u v, ‖u‖ ≤ R → ‖u + v‖ ≤ R →
        |K.ks τ (u + v) - K.ks τ u - ⟪K.Gs τ u, v⟫_ℝ| ≤ 3 / K.lam * ‖v‖ ^ 2) := by
  have hlam := K.hlam
  filter_upwards [self_mem_nhdsWithin, K.eventually_mem_U R] with τ hτ hU
  have hseg : ∀ u v : E, ‖u‖ ≤ R → ‖u + v‖ ≤ R → ∀ s ∈ Icc (0 : ℝ) 1,
      ‖u + s • v‖ ≤ R := by
    intro u v hu huv s hs
    have : u + s • v = (1 - s) • u + s • (u + v) := by
      rw [smul_add, sub_smul, one_smul]; abel
    rw [this]
    calc ‖(1 - s) • u + s • (u + v)‖ ≤ (1 - s) * ‖u‖ + s * ‖u + v‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hs.2]),
            Real.norm_of_nonneg hs.1]
      _ ≤ (1 - s) * R + s * R := by gcongr; linarith [hs.2]; exact hs.1
      _ = R := by ring
  refine ⟨fun u u' hu hu' ↦ ?_, fun u v hu huv ↦ ?_⟩
  · have h := K.abs_ks_add_sub_le (u := u) (v := u' - u) (c := 0) (C := 3 / K.lam * R) hτ
      (fun s hs ↦ hU _ (hseg u (u' - u) hu (by rwa [add_sub_cancel]) s hs)) (fun s hs ↦ ?_)
    · rw [add_sub_cancel, inner_zero_left, sub_zero] at h
      exact h
    · rw [sub_zero]
      have hs' := hseg u (u' - u) hu (by rwa [add_sub_cancel]) s hs
      calc ‖K.Gs τ (u + s • (u' - u))‖ ≤ 3 / K.lam * ‖u + s • (u' - u)‖ :=
            K.norm_Gs_le hτ (hU _ hs')
        _ ≤ 3 / K.lam * R := by gcongr
  · have h := K.abs_ks_add_sub_le (u := u) (v := v) (c := K.Gs τ u) (C := 3 / K.lam * ‖v‖) hτ
      (fun s hs ↦ hU _ (hseg u v hu huv s hs)) (fun s hs ↦ ?_)
    · calc _ ≤ 3 / K.lam * ‖v‖ * ‖v‖ := h
        _ = 3 / K.lam * ‖v‖ ^ 2 := by ring
    · have h1 := K.Gs_lip hτ (hU _ (hseg u v hu huv s hs)) (hU u hu)
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1] at h1
      calc ‖K.Gs τ (u + s • v) - K.Gs τ u‖ ≤ 3 / K.lam * (s * ‖v‖) := h1
        _ ≤ 3 / K.lam * ‖v‖ := by
            gcongr; exact mul_le_of_le_one_left (norm_nonneg v) hs.2

omit [FiniteDimensional ℝ E] in
/-- The quotients of `e_λ f` at `x̄` for `0` are `2kτ` on `U`. -/
theorem secondDifferenceQuotient_env
    (he : ∀ u ∈ proxRange f x ε K.lam, moreauEnvelopeEReal f K.lam u = ((K.e u : ℝ) : EReal))
    {τ : ℝ} {u : E} (hu : x + τ • u ∈ proxRange f x ε K.lam) :
    secondDifferenceQuotient (moreauEnvelopeEReal f K.lam) x 0 τ u =
      ((2 * K.ks τ u : ℝ) : EReal) := by
  have hxU : x ∈ proxRange f x ε K.lam := K.hball (mem_ball_self K.hδ₀)
  rw [secondDifferenceQuotient, he _ hu, he x hxU, K.e_x, inner_zero_left, mul_zero,
    ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_eq_coe_iff, sub_zero, ks]
  ring

omit [FiniteDimensional ℝ E] in
theorem eventually_secondDifferenceQuotient_env
    (he : ∀ u ∈ proxRange f x ε K.lam, moreauEnvelopeEReal f K.lam u = ((K.e u : ℝ) : EReal))
    (w : E) :
    ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      secondDifferenceQuotient (moreauEnvelopeEReal f K.lam) x 0 p.1 p.2 =
        ((2 * K.ks p.1 p.2 : ℝ) : EReal) ∧ ‖p.2‖ ≤ ‖w‖ + 1 := by
  filter_upwards [prod_mem_prod (K.eventually_mem_U (‖w‖ + 1))
    (Metric.closedBall_mem_nhds w one_pos)] with p ⟨hp1, hp2⟩
  have hn : ‖p.2‖ ≤ ‖w‖ + 1 := by
    rw [mem_closedBall, dist_eq_norm] at hp2
    calc ‖p.2‖ = ‖(p.2 - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖p.2 - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + 1 := by linarith
  exact ⟨K.secondDifferenceQuotient_env he (hp1 p.2 hn), hn⟩

omit [FiniteDimensional ℝ E] in
/-- Under convergence of `Gτ` to `G₀`, the quotients `kτ` converge continuously. -/
theorem tendsto_ks_continuous {G₀ : E → E}
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (w : E) :
    Tendsto (fun p : ℝ × E ↦ K.ks p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 (∫ s in (0 : ℝ)..1, ⟪G₀ (s • w), w⟫_ℝ)) := by
  have h1 : Tendsto (fun p : ℝ × E ↦ K.ks p.1 w) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 (∫ s in (0 : ℝ)..1, ⟪G₀ (s • w), w⟫_ℝ)) := (K.tendsto_ks hG₀ w).comp tendsto_fst
  have h2 : Tendsto (fun p : ℝ × E ↦ K.ks p.1 p.2 - K.ks p.1 w) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun p ↦ 3 / K.lam * (‖w‖ + 1) * ‖p.2 - w‖) ?_ ?_
    · filter_upwards [(K.eventually_ks_estimates (‖w‖ + 1)).prod_inl (𝓝 w),
        tendsto_snd.eventually (Metric.closedBall_mem_nhds w one_pos)] with p hp hp2
      rw [dist_eq_norm] at hp2
      have hn : ‖p.2‖ ≤ ‖w‖ + 1 := by
        calc ‖p.2‖ = ‖(p.2 - w) + w‖ := by rw [sub_add_cancel]
          _ ≤ ‖p.2 - w‖ + ‖w‖ := norm_add_le _ _
          _ ≤ ‖w‖ + 1 := by linarith
      rw [Real.norm_eq_abs]
      exact hp.1 w p.2 (by linarith) hn
    · have hc : Continuous (fun p : ℝ × E ↦ 3 / K.lam * (‖w‖ + 1) * ‖p.2 - w‖) := by fun_prop
      have := hc.tendsto (0, w)
      simp only [sub_self, norm_zero, mul_zero] at this
      exact this.mono_left (by
        rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds le_rfl)
  have := h1.add h2
  simpa using this

omit [FiniteDimensional ℝ E] in
/-- Under convergence of `Gτ` to `G₀`, `e_λ f` is twice semidifferentiable at `x̄`, twice
epi-differentiable at `x̄` for `0`, with `d²(e_λ f)(x̄ ∣ 0)(w) = 2∫₀¹ ⟪G₀(sw), w⟫ ds`. -/
theorem env_of_tendsto
    (he : ∀ u ∈ proxRange f x ε K.lam, moreauEnvelopeEReal f K.lam u = ((K.e u : ℝ) : EReal))
    {G₀ : E → E} (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    TwiceSemidifferentiableAt (moreauEnvelopeEReal f K.lam) x ∧
      TwiceEpiDifferentiableAt (moreauEnvelopeEReal f K.lam) x 0 ∧
      ∀ w, secondSubderivative (moreauEnvelopeEReal f K.lam) x 0 w =
        ((2 * ∫ s in (0 : ℝ)..1, ⟪G₀ (s • w), w⟫_ℝ : ℝ) : EReal) := by
  set e' := moreauEnvelopeEReal f K.lam with he'
  have hxU : x ∈ proxRange f x ε K.lam := K.hball (mem_ball_self K.hδ₀)
  have hfd : HasFDerivAt (fun z ↦ (e' z).toReal) (innerSL ℝ (0 : E)) x := by
    have h := K.hderiv x hxU
    rw [K.hPx, sub_self, smul_zero] at h
    exact h
  have hgrad : HasERealGradientAt e' x (innerSL ℝ (0 : E)) := by
    refine ⟨by rw [he x hxU]; exact EReal.coe_ne_bot _, by rw [he x hxU]; exact EReal.coe_ne_top _,
      ?_, HasFDerivAtFilter.isLittleO hfd⟩
    filter_upwards [K.hUo.mem_nhds hxU] with y hy
    rw [he y hy]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  have hsub : ∀ w, subderivative e' x w = ((⟪(0 : E), w⟫_ℝ : ℝ) : EReal) := fun w ↦ by
    rw [(hgrad.hasSemiderivative w).subderivative_eq, innerSL_apply_apply]
  have hlim : ∀ w, Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotient e' x 0 p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((2 * ∫ s in (0 : ℝ)..1, ⟪G₀ (s • w), w⟫_ℝ : ℝ) : EReal)) := by
    intro w
    have := (continuous_coe_real_ereal.tendsto _).comp ((K.tendsto_ks_continuous hG₀ w).const_mul 2)
    refine this.congr' ?_
    filter_upwards [K.eventually_secondDifferenceQuotient_env he w] with p hp
    exact hp.1.symm
  have hd2 : ∀ w, secondSubderivative e' x 0 w =
      ((2 * ∫ s in (0 : ℝ)..1, ⟪G₀ (s • w), w⟫_ℝ : ℝ) : EReal) := fun w ↦ (hlim w).liminf_eq
  have heq : secondSubderivativeAt e' x = secondSubderivative e' x 0 :=
    secondSubderivativeAt_eq_secondSubderivative_of_hasERealGradientAt hgrad
  refine ⟨⟨fun w ↦ ⟨_, hgrad.hasSemiderivative w⟩, fun w ↦ ?_⟩, ?_, hd2⟩
  · rw [heq, hd2 w]
    exact (hlim w).congr fun p ↦ (secondDifferenceQuotientAt_eq_of_subderivative_eq (hsub p.2)).symm
  · refine twiceEpiDifferentiableAt_iff_subset.2 ⟨hgrad.1, hgrad.2.1, ?_⟩
    rw [show secondSubderivative e' x 0 = fun w ↦
      ((2 * ∫ s in (0 : ℝ)..1, ⟪G₀ (s • w), w⟫_ℝ : ℝ) : EReal) from funext hd2]
    exact epigraph_subset_innerSetLimitAlong_of_tendsto fun w ↦ by
      have h2 := (hlim w).comp (tendsto_pair_const w)
      exact h2

omit [FiniteDimensional ℝ E] in
/-- Under twice epi-differentiability of `e_λ f` at `x̄` for `0`, the quotients `2kτ(w)` converge
to the finite value `d²(e_λ f)(x̄ ∣ 0)(w)`. -/
theorem tendsto_ks_of_twiceEpi_env
    (he : ∀ u ∈ proxRange f x ε K.lam, moreauEnvelopeEReal f K.lam u = ((K.e u : ℝ) : EReal))
    (hte : TwiceEpiDifferentiableAt (moreauEnvelopeEReal f K.lam) x 0) (w : E) :
    ∃ d : ℝ, secondSubderivative (moreauEnvelopeEReal f K.lam) x 0 w = d ∧
      Tendsto (fun τ ↦ 2 * K.ks τ w) (𝓝[>] 0) (𝓝 d) := by
  have hlam := K.hlam
  set e' := moreauEnvelopeEReal f K.lam with he'
  set R := ‖w‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  set L := 3 / K.lam * R with hL
  have hL0 : 0 ≤ L := by positivity
  set D := secondSubderivative e' x 0 w with hD
  -- the quotients along `w` are `2kτ(w)`
  have hqw : ∀ᶠ τ in 𝓝[>] (0 : ℝ), secondDifferenceQuotient e' x 0 τ w = ((2 * K.ks τ w : ℝ) : EReal) := by
    filter_upwards [K.eventually_mem_U R] with τ hU
    exact K.secondDifferenceQuotient_env he (hU w (by linarith))
  have hbnd : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ u, ‖u‖ ≤ R → |K.ks τ u| ≤ L * R := by
    filter_upwards [K.eventually_ks_estimates R] with τ hτ u hu
    have := hτ.1 0 u (by simp; linarith) hu
    rw [K.ks_zero, sub_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hu hL0)
  have hliminf : D ≤ liminf (fun τ ↦ ((2 * K.ks τ w : ℝ) : EReal)) (𝓝[>] 0) := by
    have hg : Tendsto (fun τ : ℝ ↦ ((τ, w) : ℝ × E)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
      tendsto_id.prodMk tendsto_const_nhds
    refine (secondSubderivative_le_liminf hg).trans (le_of_eq (liminf_congr ?_))
    filter_upwards [hqw] with τ hτ
    exact hτ
  -- bounds
  have hlow : ((-(2 * (L * R)) : ℝ) : EReal) ≤ D := by
    refine coe_le_secondSubderivative_of_eventually (ψ := fun _ ↦ -(2 * (L * R))) ?_
      tendsto_const_nhds
    filter_upwards [K.eventually_secondDifferenceQuotient_env he w, hbnd.prod_inl (𝓝 w)] with p hp hb
    rw [hp.1, EReal.coe_le_coe_iff]
    have := hb p.2 hp.2
    linarith [(abs_le.1 this).1]
  have hup : D ≤ ((2 * (L * R)) : ℝ) := by
    refine hliminf.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    filter_upwards [hbnd] with τ hb
    rw [EReal.coe_le_coe_iff]
    have := hb w (by linarith)
    linarith [(abs_le.1 this).2]
  obtain ⟨d, hd⟩ : ∃ d : ℝ, D = d :=
    ⟨D.toReal, (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hup)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow)).symm⟩
  refine ⟨d, hd, tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩⟩
  · have hl' := hliminf
    rw [hd] at hl'
    have h1 : ((a : ℝ) : EReal) < liminf (fun τ ↦ ((2 * K.ks τ w : ℝ) : EReal)) (𝓝[>] 0) :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 ha) hl'
    filter_upwards [eventually_lt_of_lt_liminf h1] with τ hτ
    exact EReal.coe_lt_coe_iff.1 hτ
  · -- the inner limit of the epigraphs
    set η := (b - d) / 3 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    have hp₀ : ((w, d + η) : E × ℝ) ∈ epigraph (secondSubderivative e' x 0) := by
      change (((d + η : ℝ)) : EReal) ≥ secondSubderivative e' x 0 w
      rw [← hD, hd]; exact EReal.coe_le_coe_iff.2 (by linarith)
    have hin := (twiceEpiDifferentiableAt_iff_subset.1 hte).2.2 hp₀
    set δ := min 1 (η / (1 + 2 * L)) with hδ
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδη : δ * (1 + 2 * L) ≤ η := by
      have : δ ≤ η / (1 + 2 * L) := min_le_right _ _
      rwa [le_div_iff₀ (by positivity)] at this
    filter_upwards [hin (ball (w, d + η) δ) (ball_mem_nhds _ hδ0), K.eventually_mem_U R,
      K.eventually_ks_estimates R] with τ hne hU hest
    obtain ⟨⟨u', α⟩, hepi, hball⟩ := hne
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, Real.dist_eq] at hball
    have hu'R : ‖u'‖ ≤ R := by
      calc ‖u'‖ = ‖(u' - w) + w‖ := by rw [sub_add_cancel]
        _ ≤ ‖u' - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    have hq : secondDifferenceQuotient e' x 0 τ u' = ((2 * K.ks τ u' : ℝ) : EReal) :=
      K.secondDifferenceQuotient_env he (hU u' hu'R)
    have hα : 2 * K.ks τ u' ≤ α := by
      have : secondDifferenceQuotient e' x 0 τ u' ≤ ((α : ℝ) : EReal) := hepi
      rwa [hq, EReal.coe_le_coe_iff] at this
    have hLip := hest.1 u' w hu'R (by linarith)
    rw [norm_sub_rev] at hLip
    have h1 : K.ks τ w ≤ K.ks τ u' + L * δ := by
      have := (abs_le.1 hLip).2
      nlinarith [hball.1]
    have h2 : α < d + η + δ := by linarith [(abs_lt.1 hball.2).2]
    nlinarith

/-- **Exercise 13.45**, (c) ⇒ convergence of `Gτ`: twice epi-differentiability of `e_λ f` at `x̄`
for `0` makes the rescaled gradients converge (`kτ` converge, and their gradients `Gτ` are
determined in the limit by the descent estimates). -/
theorem tendsto_Gs_of_twiceEpi_env
    (he : ∀ u ∈ proxRange f x ε K.lam, moreauEnvelopeEReal f K.lam u = ((K.e u : ℝ) : EReal))
    (hte : TwiceEpiDifferentiableAt (moreauEnvelopeEReal f K.lam) x 0) (u : E) :
    ∃ z, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 z) := by
  have hlam := K.hlam
  choose d hd hdlim using K.tendsto_ks_of_twiceEpi_env he hte
  have hk : ∀ w, Tendsto (fun τ ↦ K.ks τ w) (𝓝[>] 0) (𝓝 (d w / 2)) := fun w ↦ by
    have := (hdlim w).div_const 2
    simpa [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] using this
  set P : E → Prop := fun g ↦ ∀ v, |d (u + v) / 2 - d u / 2 - ⟪g, v⟫_ℝ| ≤ 3 / K.lam * ‖v‖ ^ 2
    with hPdef
  have hP : ∀ {τs : ℕ → ℝ}, Tendsto τs atTop (𝓝[>] 0) → ∀ {g : E},
      Tendsto (fun n ↦ K.Gs (τs n) u) atTop (𝓝 g) → P g := by
    intro τs hτs g hg v
    have hev := hτs.eventually (K.eventually_ks_estimates (‖u‖ + ‖v‖))
    have hlim : Tendsto (fun n ↦ |K.ks (τs n) (u + v) - K.ks (τs n) u - ⟪K.Gs (τs n) u, v⟫_ℝ|)
        atTop (𝓝 |d (u + v) / 2 - d u / 2 - ⟪g, v⟫_ℝ|) :=
      ((((hk (u + v)).comp hτs).sub ((hk u).comp hτs)).sub (hg.inner tendsto_const_nhds)).abs
    exact le_of_tendsto hlim (hev.mono fun n hn ↦ hn.2 u v (by linarith [norm_nonneg v])
      (norm_add_le u v))
  have huniq : ∀ g₁ g₂, P g₁ → P g₂ → g₁ = g₂ := by
    intro g₁ g₂ h1 h2
    by_contra hne
    have hD : 0 < ‖g₁ - g₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    set t := K.lam / 12 with ht
    have ht0 : 0 < t := by positivity
    have e1 := h1 (t • (g₁ - g₂))
    have e2 := h2 (t • (g₁ - g₂))
    rw [norm_smul, Real.norm_of_nonneg ht0.le, mul_pow] at e1 e2
    rw [real_inner_smul_right] at e1 e2
    have hdiff : ⟪g₁, g₁ - g₂⟫_ℝ - ⟪g₂, g₁ - g₂⟫_ℝ = ‖g₁ - g₂‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have h3 : t * ‖g₁ - g₂‖ ^ 2 ≤ 6 / K.lam * (t ^ 2 * ‖g₁ - g₂‖ ^ 2) := by
      set A := d (u + t • (g₁ - g₂)) / 2 - d u / 2 with hA
      have h4 : (A - t * ⟪g₂, g₁ - g₂⟫_ℝ) - (A - t * ⟪g₁, g₁ - g₂⟫_ℝ) = t * ‖g₁ - g₂‖ ^ 2 := by
        rw [← hdiff]; ring
      have h7 : 3 / K.lam * (t ^ 2 * ‖g₁ - g₂‖ ^ 2) + 3 / K.lam * (t ^ 2 * ‖g₁ - g₂‖ ^ 2) =
          6 / K.lam * (t ^ 2 * ‖g₁ - g₂‖ ^ 2) := by ring
      calc t * ‖g₁ - g₂‖ ^ 2 = |(A - t * ⟪g₂, g₁ - g₂⟫_ℝ) - (A - t * ⟪g₁, g₁ - g₂⟫_ℝ)| := by
            rw [h4, abs_of_pos (mul_pos ht0 (pow_pos hD 2))]
        _ ≤ |A - t * ⟪g₂, g₁ - g₂⟫_ℝ| + |A - t * ⟪g₁, g₁ - g₂⟫_ℝ| := abs_sub _ _
        _ ≤ 3 / K.lam * (t ^ 2 * ‖g₁ - g₂‖ ^ 2) + 3 / K.lam * (t ^ 2 * ‖g₁ - g₂‖ ^ 2) :=
            add_le_add e2 e1
        _ = 6 / K.lam * (t ^ 2 * ‖g₁ - g₂‖ ^ 2) := h7
    have h6 : 6 / K.lam * (t ^ 2 * ‖g₁ - g₂‖ ^ 2) = 1 / 2 * (t * ‖g₁ - g₂‖ ^ 2) := by
      rw [ht]; field_simp; ring
    rw [h6] at h3
    have : 0 < t * ‖g₁ - g₂‖ ^ 2 := mul_pos ht0 (pow_pos hD 2)
    linarith
  have hbd : ∀ {τ : ℕ → ℝ}, Tendsto τ atTop (𝓝[>] 0) →
      ∀ᶠ n in atTop, K.Gs (τ n) u ∈ closedBall (0 : E) (3 / K.lam * ‖u‖) := by
    intro τ hτ
    filter_upwards [hτ.eventually self_mem_nhdsWithin, hτ.eventually (K.eventually_mem_U ‖u‖)]
      with n hn hnU
    have h := K.Gs_lip hn (hnU u le_rfl) (hnU 0 (by simp))
    rw [K.Gs_zero, sub_zero, sub_zero] at h
    rwa [mem_closedBall, dist_zero_right]
  have hseq : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n ↦ mem_Ioi.2 (by positivity)⟩
  obtain ⟨z, -, φ, hφ, hφz⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall
    (hbd hseq).frequently
  have hz : P z := hP (hseq.comp hφ.tendsto_atTop) hφz
  refine ⟨z, tendsto_of_subseq_tendsto fun ns hns ↦ ?_⟩
  obtain ⟨z', -, ψ, hψ, hψz⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall
    (hbd hns).frequently
  have hz' : P z' := hP (hns.comp hψ.tendsto_atTop) hψz
  rw [huniq z z' hz hz'] at *
  exact ⟨ψ, hψz⟩

end ProxCore

/-! ### Exercise 13.45 -/

/-- **Exercise 13.45** (semidifferentiability of proximal mappings).  Let `f` be prox-regular at
`x̄` for `v̄ = 0` and prox-bounded.  For all sufficiently small `λ > 0`, each of
(a) `P_λ f` is semidifferentiable at `x̄` (for `x̄`), (b) `P_λ f` is proto-differentiable at `x̄`
(for `x̄`), (c) `e_λ f` is twice epi-differentiable at `x̄` (for `∇e_λ f(x̄) = 0`) and (d) `e_λ f`
is twice semidifferentiable at `x̄` is equivalent to the twice epi-differentiability of `f` at `x̄`
for `0`, and then, with `h = ½d²f(x̄ ∣ 0)`, `½d²(e_λ f)(x̄ ∣ 0) = e_λ h` and `D[P_λ f](x̄) = P_λ h`.
-/
theorem semidifferentiability_of_proximal_mappings {f : E → EReal} {x : E}
    (hpr : IsProxRegularAt f x 0) (hpb : IsProxBounded f) :
    ∃ lam₁ > (0 : ℝ), ∀ lam : ℝ, 0 < lam → lam < lam₁ →
      ((∃ H, HasMappingSemiderivative (proximalMappingEReal f lam) x x H) ↔
        TwiceEpiDifferentiableAt f x 0) ∧
      (IsProtoDifferentiableAt (proximalMappingEReal f lam) x x ↔
        TwiceEpiDifferentiableAt f x 0) ∧
      (TwiceEpiDifferentiableAt (moreauEnvelopeEReal f lam) x 0 ↔
        TwiceEpiDifferentiableAt f x 0) ∧
      (TwiceSemidifferentiableAt (moreauEnvelopeEReal f lam) x ↔
        TwiceEpiDifferentiableAt f x 0) ∧
      (TwiceEpiDifferentiableAt f x 0 →
        (∀ w, ((1 / 2 : ℝ) : EReal) * secondSubderivative (moreauEnvelopeEReal f lam) x 0 w =
          moreauEnvelopeEReal (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w) lam w) ∧
        graphicalDerivative (proximalMappingEReal f lam) x x =
          proximalMappingEReal (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w) lam)
    := by
  obtain ⟨ε, hε, lam₀, hlam₀, H⟩ := hpr.exists_proxEnvelopeModel hpb
  obtain ⟨lam₁, hlam₁, hK⟩ := ProxCore.exists_of_lam hpr hpb hlam₀ H
  refine ⟨lam₁, hlam₁, fun lam hlam hlt ↦ ?_⟩
  obtain ⟨K, hKlam, hP, he⟩ := hK lam hlam hlt
  subst hKlam
  have hb := K.isProtoDifferentiableAt_prox_iff_twiceEpi hP
  have haub := K.hasAubinPropertyAt_prox hP
  have hGs_of : TwiceEpiDifferentiableAt f x 0 →
      ∃ G₀ : E → E, ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u)) := fun h ↦ by
    choose G₀ hG₀ using K.tendsto_Gs_of_twiceEpi h
    exact ⟨G₀, hG₀⟩
  have hc_to : TwiceEpiDifferentiableAt (moreauEnvelopeEReal f K.lam) x 0 →
      TwiceEpiDifferentiableAt f x 0 := fun h ↦
    K.core_equivalence.1.1 (K.isProtoDifferentiableAt_iff.2 (K.tendsto_Gs_of_twiceEpi_env he h))
  refine ⟨⟨fun ⟨H, hH⟩ ↦ hb.1 hH.protoDerivative.1,
      fun h ↦ ⟨_, (hasMappingSemiderivative_iff_proto_of_aubin haub).2 (hb.2 h)⟩⟩, hb,
    ⟨hc_to, fun h ↦ ?_⟩, ⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun h ↦ ?_⟩
  · obtain ⟨G₀, hG₀⟩ := hGs_of h
    exact (K.env_of_tendsto he hG₀).2.1
  · -- (d) ⇒ (c)
    refine hc_to (twiceEpiDifferentiableAt_iff_subset.2 ⟨?_, ?_, ?_⟩)
    · have hxU : x ∈ proxRange f x ε K.lam := K.hball (mem_ball_self K.hδ₀)
      rw [he x hxU]; exact EReal.coe_ne_bot _
    · have hxU : x ∈ proxRange f x ε K.lam := K.hball (mem_ball_self K.hδ₀)
      rw [he x hxU]; exact EReal.coe_ne_top _
    · obtain ⟨hs, hlim⟩ := h
      have hxU : x ∈ proxRange f x ε K.lam := K.hball (mem_ball_self K.hδ₀)
      have hfd : HasFDerivAt (fun z ↦ (moreauEnvelopeEReal f K.lam z).toReal)
          (innerSL ℝ (0 : E)) x := by
        have h := K.hderiv x hxU
        rw [K.hPx, sub_self, smul_zero] at h
        exact h
      have hgrad : HasERealGradientAt (moreauEnvelopeEReal f K.lam) x (innerSL ℝ (0 : E)) := by
        refine ⟨by rw [he x hxU]; exact EReal.coe_ne_bot _,
          by rw [he x hxU]; exact EReal.coe_ne_top _, ?_, HasFDerivAtFilter.isLittleO hfd⟩
        filter_upwards [K.hUo.mem_nhds hxU] with y hy
        rw [he y hy]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
      have hsub : ∀ w, subderivative (moreauEnvelopeEReal f K.lam) x w =
          ((⟪(0 : E), w⟫_ℝ : ℝ) : EReal) := fun w ↦ by
        rw [(hgrad.hasSemiderivative w).subderivative_eq, innerSL_apply_apply]
      have heq := secondSubderivativeAt_eq_secondSubderivative_of_hasERealGradientAt hgrad
      rw [← heq]
      exact epigraph_subset_innerSetLimitAlong_of_tendsto fun w ↦ by
        have h2 := ((hlim w).congr fun p ↦
          secondDifferenceQuotientAt_eq_of_subderivative_eq (hsub p.2)).comp (tendsto_pair_const w)
        exact h2
  · obtain ⟨G₀, hG₀⟩ := hGs_of h
    exact (K.env_of_tendsto he hG₀).1
  · -- the formulas
    obtain ⟨G₀, hG₀⟩ := hGs_of h
    obtain ⟨-, -, hd2⟩ := K.env_of_tendsto he hG₀
    refine ⟨fun w ↦ ?_, funext fun u ↦ ?_⟩
    · rw [hd2 w, (K.prox_half_secondSubderivative hG₀ w).2, ← EReal.coe_mul]
      congr 1; ring
    · rw [K.graphicalDerivative_prox hP hG₀ u, (K.prox_half_secondSubderivative hG₀ u).1]

end RW
