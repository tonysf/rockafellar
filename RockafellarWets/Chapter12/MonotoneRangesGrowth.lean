/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Ranges and growth of maximal monotone mappings

Corollary 12.42.

For maximal monotone `T`, `R = cl(rge T)` and any `x̄`, the rescaled mappings
`Tτ(w) = T(x̄ + τw)` converge graphically to `∂σ_R = N_R⁻¹` as `τ → ∞`.  The
book obtains this from 12.37 applied to `T⁻¹`, through the identity
`Tτ⁻¹ = τ⁻¹(T⁻¹ - x̄)`.  Here the inner limit is produced by the resolvents of
`T⁻¹`, which converge to the projection on `R` by 12.37, and the outer limit is
a continuity argument with the monotonicity inequality.  The identity
`N_R⁻¹ = ∂σ_R`, with `∂σ_R(w)` the set of maximizers of `⟪·, w⟫` over `R`, comes
from 8.25.

The sequential reformulations follow: the union over `wν → w` of the outer
limits of `T(x̄ + τν wν)` is `∂σ_R(w)` for every `τν → ∞`, and the outer limit of
`T(x)` as `x → dir w` (Definition 3.1: `λν xν → w` for some `λν ↘ 0`) is
`argmax_{v ∈ R} ⟪v, w⟫`.  When `⟪·, w⟫` has no maximizer on `R`, the sets `T(xν)`
therefore escape to the horizon along every `xν → dir w`.
-/

import RockafellarWets.Chapter12.MonotoneDomains
import RockafellarWets.Chapter8.SupportSubgradients
import RockafellarWets.Chapter4.EscapeToHorizon
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- `N_R⁻¹(w)` is the set of maximizers of `⟪·, w⟫` over a convex set `R`. -/
theorem mem_svInv_normalCone_iff {R : Set E} (hR : Convex ℝ R) {w v : E} :
    v ∈ svInv (normalCone R) w ↔ v ∈ R ∧ ∀ v' ∈ R, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ := by
  rw [mem_svInv]
  constructor
  · intro h
    have hv : v ∈ R := h.1
    rw [normalCone_eq_of_convex hR hv] at h
    refine ⟨hv, fun v' hv' ↦ ?_⟩
    have h' := h v' hv'
    rw [inner_sub_right, real_inner_comm v' w, real_inner_comm v w] at h'
    linarith
  · rintro ⟨hv, h⟩
    rw [normalCone_eq_of_convex hR hv]
    intro v' hv'
    rw [inner_sub_right, real_inner_comm v' w, real_inner_comm v w]
    linarith [h v' hv']

/-- `N_R⁻¹ = ∂σ_R` for a nonempty closed convex set `R` (8.25, 11.4). -/
theorem svInv_normalCone_eq_subdifferential_supportFunction {R : Set E} (hRc : IsClosed R)
    (hR : Convex ℝ R) (hne : R.Nonempty) :
    svInv (normalCone R) = subdifferential (supportFunction R) := by
  funext w
  ext v
  by_cases hw : w ∈ effectiveDomain (supportFunction R)
  · rw [subdifferential_supportFunction_eq_normal_face hR hRc hne hw, mem_svInv]
    exact ⟨fun h ↦ ⟨h.1, h⟩, fun h ↦ h.2⟩
  · have htop : supportFunction R w = ⊤ := by
      simpa [effectiveDomain] using hw
    rw [subdifferential_eq_empty_of_eq_top htop]
    simp only [mem_empty_iff_false, iff_false]
    intro hv
    rw [mem_svInv_normalCone_iff hR] at hv
    apply hw
    refine lt_of_le_of_lt ((supportFunction_le_iff R w _).2 fun v' hv' ↦ ?_)
      (EReal.coe_lt_top ⟪v, w⟫_ℝ)
    exact EReal.coe_le_coe_iff.2 (hv.2 v' hv')

/-- `∂σ_R(w) = argmax_{v ∈ R} ⟪v, w⟫` for a nonempty closed convex set `R`. -/
theorem subdifferential_supportFunction_eq_argmax {R : Set E} (hRc : IsClosed R)
    (hR : Convex ℝ R) (hne : R.Nonempty) (w : E) :
    subdifferential (supportFunction R) w = {v | v ∈ R ∧ ∀ v' ∈ R, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} := by
  rw [← svInv_normalCone_eq_subdifferential_supportFunction hRc hR hne]
  ext v
  exact mem_svInv_normalCone_iff hR

omit [FiniteDimensional ℝ E] in
/-- A maximal monotone mapping has a nonempty range. -/
theorem SvMaximalMonotone.svRange_nonempty {T : E → Set E} (hT : SvMaximalMonotone T) :
    (svRange T).Nonempty := by
  obtain ⟨x, v, hv⟩ := hT.svDom_nonempty
  exact ⟨v, x, hv⟩

/-- **Corollary 12.42**, the graphical limit in the form `N_R⁻¹`: the mappings
`Tτ(w) = T(x̄ + τw)` converge graphically to `N_R⁻¹` as `τ → ∞`. -/
theorem SvMaximalMonotone.pkConvergesAlong_atTop_svInv_normalCone {T : E → Set E}
    (hT : SvMaximalMonotone T) (xbar : E) :
    PKConvergesAlong atTop (fun τ : ℝ ↦ svGraph (fun w ↦ T (xbar + τ • w)))
      (svGraph (svInv (normalCone (closure (svRange T))))) := by
  set R := closure (svRange T) with hRdef
  have hS : SvMaximalMonotone (svInv T) := hT.inv
  have hRconv : Convex ℝ R := hS.convex_closure_svDom
  have hN : SvMaximalMonotone (normalCone R) := hS.svMaximalMonotone_normalCone_closure_svDom
  have hin : svGraph (svInv (normalCone R)) ⊆
      innerSetLimitAlong atTop (fun τ : ℝ ↦ svGraph (fun w ↦ T (xbar + τ • w))) := by
    rintro ⟨w, v⟩ hwv V hV
    have hwv' : w ∈ normalCone R v := hwv
    have hP : resolventMap (normalCone R) 1 (v + w) = v :=
      (hN.resolventMap_eq_iff one_pos).2 ⟨w, hwv', by rw [one_smul]⟩
    have ht := hS.tendsto_resolventMap_nhdsWithin_zero (v + w)
    rw [svDom_svInv, ← hRdef, hP] at ht
    have ht' : Tendsto (fun τ : ℝ ↦ resolventMap (svInv T) τ⁻¹ (v + w)) atTop (𝓝 v) :=
      ht.comp tendsto_inv_atTop_nhdsGT_zero
    have hw' : Tendsto (fun τ : ℝ ↦ (v + w - resolventMap (svInv T) τ⁻¹ (v + w)) - τ⁻¹ • xbar)
        atTop (𝓝 w) := by
      have h1 := ((tendsto_const_nhds (x := v + w)).sub ht').sub
        (tendsto_inv_atTop_zero.smul_const xbar)
      rwa [zero_smul, sub_zero, add_sub_cancel_left] at h1
    filter_upwards [(hw'.prodMk_nhds ht') hV, eventually_gt_atTop (0 : ℝ)] with τ h1 hτ
    refine ⟨_, ?_, h1⟩
    change resolventMap (svInv T) τ⁻¹ (v + w) ∈
      T (xbar + τ • ((v + w - resolventMap (svInv T) τ⁻¹ (v + w)) - τ⁻¹ • xbar))
    have hm := hS.inv_smul_sub_resolventMap_mem (inv_pos.2 hτ) (v + w)
    rw [inv_inv] at hm
    have e : xbar + τ • ((v + w - resolventMap (svInv T) τ⁻¹ (v + w)) - τ⁻¹ • xbar) =
        τ • (v + w - resolventMap (svInv T) τ⁻¹ (v + w)) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
      abel
    rw [e]
    exact hm
  have hout : outerSetLimitAlong atTop (fun τ : ℝ ↦ svGraph (fun w ↦ T (xbar + τ • w))) ⊆
      svGraph (svInv (normalCone R)) := by
    rintro ⟨w, v⟩ hwv
    have hvR : v ∈ R := by
      by_contra hv
      have hV : ((univ : Set E) ×ˢ Rᶜ) ∈ 𝓝 (w, v) :=
        prod_mem_nhds univ_mem (isClosed_closure.isOpen_compl.mem_nhds hv)
      obtain ⟨_, p, hp, hpV⟩ := (hwv _ hV).exists
      exact hpV.2 (subset_closure ⟨_, hp⟩)
    change w ∈ normalCone R v
    rw [normalCone_eq_of_convex hRconv hvR]
    have hrge : svRange T ⊆ {u : E | ⟪w, u - v⟫_ℝ ≤ 0} := by
      rintro u ⟨a, hu⟩
      simp only [mem_setOf_eq]
      by_contra hpos
      push_neg at hpos
      have hg : Continuous (fun q : ℝ × (E × E) ↦ ⟪q.2.2 - u, q.1 • (xbar - a) + q.2.1⟫_ℝ) := by
        fun_prop
      have h0 : ⟪v - u, (0 : ℝ) • (xbar - a) + w⟫_ℝ < 0 := by
        rw [zero_smul, zero_add, ← neg_sub u v, inner_neg_left, real_inner_comm]
        linarith
      have hmem : {q : ℝ × (E × E) | ⟪q.2.2 - u, q.1 • (xbar - a) + q.2.1⟫_ℝ < 0} ∈
          𝓝 ((0 : ℝ), (w, v)) :=
        (isOpen_lt hg continuous_const).mem_nhds h0
      obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.1 hmem
      have hU' : ∀ᶠ τ : ℝ in atTop, τ⁻¹ ∈ U := tendsto_inv_atTop_zero hU
      obtain ⟨τ, ⟨hτU, hτ⟩, p, hp, hpW⟩ :=
        ((hU'.and (eventually_gt_atTop 0)).and_frequently (hwv W hW)).exists
      have hlt : ⟪p.2 - u, τ⁻¹ • (xbar - a) + p.1⟫_ℝ < 0 := hUW (Set.mk_mem_prod hτU hpW)
      have hm := hT.1 hu hp
      have e : xbar + τ • p.1 - a = τ • (τ⁻¹ • (xbar - a) + p.1) := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
        abel
      rw [e, real_inner_smul_right] at hm
      nlinarith
    intro u hu
    exact closure_minimal hrge (isClosed_le (by fun_prop) continuous_const) hu
  have hio := innerSetLimitAlong_subset_outerSetLimitAlong (l := (atTop : Filter ℝ))
    (fun τ : ℝ ↦ svGraph (fun w ↦ T (xbar + τ • w)))
  exact ⟨Subset.antisymm (hio.trans hout) hin, Subset.antisymm hout (hin.trans hio)⟩

/-- **Corollary 12.42**: `g-lim_{τ → ∞} Tτ = ∂σ_R` for `Tτ(w) = T(x̄ + τw)` and
`R = cl(rge T)`. -/
theorem SvMaximalMonotone.pkConvergesAlong_atTop_subdifferential_supportFunction
    {T : E → Set E} (hT : SvMaximalMonotone T) (xbar : E) :
    PKConvergesAlong atTop (fun τ : ℝ ↦ svGraph (fun w ↦ T (xbar + τ • w)))
      (svGraph (subdifferential (supportFunction (closure (svRange T))))) := by
  rw [← svInv_normalCone_eq_subdifferential_supportFunction (R := closure (svRange T))
    isClosed_closure (hT.inv.convex_closure_svDom : Convex ℝ (closure (svRange T)))
    hT.svRange_nonempty.closure]
  exact hT.pkConvergesAlong_atTop_svInv_normalCone xbar

/-- **Corollary 12.42**, along any sequence `τν → ∞`. -/
theorem SvMaximalMonotone.graphicalConverges_growth {T : E → Set E} (hT : SvMaximalMonotone T)
    (xbar : E) {tau : ℕ → ℝ} (htau : Tendsto tau atTop atTop) :
    GraphicalConverges (fun n w ↦ T (xbar + tau n • w))
      (subdifferential (supportFunction (closure (svRange T)))) :=
  (hT.pkConvergesAlong_atTop_subdifferential_supportFunction xbar).pkConverges_comp htau

/-- **Corollary 12.42**, the sequential form: for every `τν → ∞`, the union over
`wν → w` of `lim sup_ν T(x̄ + τν wν)` is `∂σ_R(w)`. -/
theorem SvMaximalMonotone.iUnion_outerSetLimit_growth {T : E → Set E}
    (hT : SvMaximalMonotone T) (xbar : E) {tau : ℕ → ℝ} (htau : Tendsto tau atTop atTop)
    (w : E) :
    {v | ∃ ws : ℕ → E, Tendsto ws atTop (𝓝 w) ∧
        v ∈ outerSetLimit (fun n ↦ T (xbar + tau n • ws n))} =
      subdifferential (supportFunction (closure (svRange T))) w := by
  have hg := hT.graphicalConverges_growth xbar htau
  ext v
  constructor
  · rintro ⟨ws, hws, hv⟩
    have hmem : (w, v) ∈ outerSetLimit (fun n ↦ svGraph (fun w' ↦ T (xbar + tau n • w'))) := by
      intro V hV
      obtain ⟨U₁, hU₁, U₂, hU₂, hUV⟩ := mem_nhds_prod_iff.1 hV
      refine ((hv U₂ hU₂).and_eventually (hws hU₁)).mono fun n hn ↦ ?_
      obtain ⟨⟨u, hu, huU⟩, hnU⟩ := hn
      exact ⟨(ws n, u), hu, hUV (Set.mk_mem_prod hnU huU)⟩
    rw [hg.outer_eq] at hmem
    exact hmem
  · intro hv
    have hmem : (w, v) ∈ innerSetLimit (fun n ↦ svGraph (fun w' ↦ T (xbar + tau n • w'))) := by
      rw [hg.inner_eq]
      exact hv
    obtain ⟨ws, vs, hev, hws, hvs⟩ :=
      mem_graphicalInnerLimit_iff.1 (show v ∈ graphicalInnerLimit _ w from hmem)
    refine ⟨ws, hws, fun V hV ↦ ?_⟩
    exact (hev.and (hvs hV)).frequently.mono fun n hn ↦ ⟨vs n, hn.1, hn.2⟩

/-- **Corollary 12.42**, the direction form: the outer limit of `T(x)` as
`x → dir w`, that is along sequences with `λν xν → w` for some `λν ↘ 0`
(Definition 3.1), is `argmax_{v ∈ R} ⟪v, w⟫`. -/
theorem SvMaximalMonotone.outerLimit_dir_eq_argmax {T : E → Set E} (hT : SvMaximalMonotone T)
    (w : E) :
    {v | ∃ (x vs : ℕ → E) (lam : ℕ → ℝ), (∀ n, 0 < lam n) ∧ Tendsto lam atTop (𝓝 0) ∧
        Tendsto (fun n ↦ lam n • x n) atTop (𝓝 w) ∧ (∀ n, vs n ∈ T (x n)) ∧
        Tendsto vs atTop (𝓝 v)} =
      {v | v ∈ closure (svRange T) ∧ ∀ v' ∈ closure (svRange T), ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} := by
  have hRconv : Convex ℝ (closure (svRange T)) := hT.inv.convex_closure_svDom
  ext v
  simp only [mem_setOf_eq]
  rw [← mem_svInv_normalCone_iff hRconv]
  constructor
  · rintro ⟨x, vs, lam, hpos, hlam, hx, hvs, hv⟩
    have htau : Tendsto (fun n ↦ (lam n)⁻¹) atTop atTop :=
      tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hlam, Eventually.of_forall hpos⟩)
    have hg := (hT.pkConvergesAlong_atTop_svInv_normalCone 0).pkConverges_comp htau
    have hmem : (w, v) ∈ outerSetLimit
        (fun n ↦ svGraph (fun w' ↦ T (0 + (lam n)⁻¹ • w'))) := by
      intro V hV
      refine (((hx.prodMk_nhds hv).eventually hV).mono fun n hn ↦ ?_).frequently
      refine ⟨(lam n • x n, vs n), ?_, hn⟩
      change vs n ∈ T (0 + (lam n)⁻¹ • (lam n • x n))
      rw [zero_add, smul_smul, inv_mul_cancel₀ (hpos n).ne', one_smul]
      exact hvs n
    rw [hg.outer_eq] at hmem
    exact hmem
  · intro hv
    have htau : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hg := (hT.pkConvergesAlong_atTop_svInv_normalCone 0).pkConverges_comp htau
    have hmem : (w, v) ∈ innerSetLimit
        (fun n ↦ svGraph (fun w' ↦ T (0 + ((n : ℝ) + 1) • w'))) := by
      rw [hg.inner_eq]
      exact hv
    obtain ⟨ws, vs, hev, hws, hvs⟩ :=
      mem_graphicalInnerLimit_iff.1 (show v ∈ graphicalInnerLimit _ w from hmem)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨fun n ↦ (((n + N : ℕ) : ℝ) + 1) • ws (n + N), fun n ↦ vs (n + N),
      fun n ↦ 1 / (((n + N : ℕ) : ℝ) + 1), fun n ↦ by positivity, ?_, ?_, fun n ↦ ?_,
      hvs.comp (tendsto_add_atTop_nat N)⟩
    · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat N)
    · refine (hws.comp (tendsto_add_atTop_nat N)).congr fun n ↦ ?_
      have hpos : (0 : ℝ) < ((n + N : ℕ) : ℝ) + 1 := by positivity
      simp only [Function.comp_apply, smul_smul, one_div, inv_mul_cancel₀ hpos.ne', one_smul]
    · have h := hN (n + N) (Nat.le_add_left N n)
      simpa only [zero_add] using h

/-- **Corollary 12.42**, the final assertion: when `⟪·, w⟫` has no maximizer on
`R = cl(rge T)`, because it is unbounded above on `R` or does not attain its
supremum, the sets `T(xν)` escape to the horizon along every `xν → dir w`. -/
theorem SvMaximalMonotone.pkConverges_empty_of_forall_lt {T : E → Set E}
    (hT : SvMaximalMonotone T) {w : E}
    (hw : ∀ v ∈ closure (svRange T), ∃ v' ∈ closure (svRange T), ⟪v, w⟫_ℝ < ⟪v', w⟫_ℝ)
    {x : ℕ → E} {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n) (hlam : Tendsto lam atTop (𝓝 0))
    (hx : Tendsto (fun n ↦ lam n • x n) atTop (𝓝 w)) :
    PKConverges (fun n ↦ T (x n)) ∅ := by
  rw [pkConverges_empty_iff_outerSetLimit_eq_empty]
  refine eq_empty_of_forall_notMem fun v hv ↦ ?_
  obtain ⟨φ, vs, hφ, hvs, hvlim⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hv
  have hmem : v ∈ {v | ∃ (x vs : ℕ → E) (lam : ℕ → ℝ), (∀ n, 0 < lam n) ∧
      Tendsto lam atTop (𝓝 0) ∧ Tendsto (fun n ↦ lam n • x n) atTop (𝓝 w) ∧
      (∀ n, vs n ∈ T (x n)) ∧ Tendsto vs atTop (𝓝 v)} :=
    ⟨x ∘ φ, vs, lam ∘ φ, fun n ↦ hpos (φ n), hlam.comp hφ.tendsto_atTop,
      hx.comp hφ.tendsto_atTop, hvs, hvlim⟩
  rw [hT.outerLimit_dir_eq_argmax] at hmem
  obtain ⟨v', hv', hlt⟩ := hw v hmem.1
  exact absurd (hmem.2 v' hv') (not_le.2 hlt)

/-- **Corollary 12.42 (ranges and growth)**, collected.  For maximal monotone
`T`, `R = cl(rge T)` and any `x̄`: `Tτ(w) = T(x̄ + τw)` converges graphically to
`∂σ_R` as `τ → ∞`; for every `τν → ∞` the union over `wν → w` of the outer limits
of `T(x̄ + τν wν)` is `∂σ_R(w)`; `∂σ_R(w) = argmax_{v ∈ R} ⟪v, w⟫`; and the outer
limit of `T(x)` as `x → dir w` is that argmax. -/
theorem ranges_and_growth {T : E → Set E} (hT : SvMaximalMonotone T) (xbar : E) :
    PKConvergesAlong atTop (fun τ : ℝ ↦ svGraph (fun w ↦ T (xbar + τ • w)))
        (svGraph (subdifferential (supportFunction (closure (svRange T))))) ∧
      (∀ tau : ℕ → ℝ, Tendsto tau atTop atTop → ∀ w,
        {v | ∃ ws : ℕ → E, Tendsto ws atTop (𝓝 w) ∧
            v ∈ outerSetLimit (fun n ↦ T (xbar + tau n • ws n))} =
          subdifferential (supportFunction (closure (svRange T))) w) ∧
      (∀ w, subdifferential (supportFunction (closure (svRange T))) w =
        {v | v ∈ closure (svRange T) ∧ ∀ v' ∈ closure (svRange T), ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ}) ∧
      ∀ w, {v | ∃ (x vs : ℕ → E) (lam : ℕ → ℝ), (∀ n, 0 < lam n) ∧ Tendsto lam atTop (𝓝 0) ∧
          Tendsto (fun n ↦ lam n • x n) atTop (𝓝 w) ∧ (∀ n, vs n ∈ T (x n)) ∧
          Tendsto vs atTop (𝓝 v)} =
        {v | v ∈ closure (svRange T) ∧ ∀ v' ∈ closure (svRange T), ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} :=
  ⟨hT.pkConvergesAlong_atTop_subdifferential_supportFunction xbar,
    fun _ htau w ↦ hT.iUnion_outerSetLimit_growth xbar htau w,
    subdifferential_supportFunction_eq_argmax isClosed_closure
      (hT.inv.convex_closure_svDom : Convex ℝ (closure (svRange T))) hT.svRange_nonempty.closure,
    hT.outerLimit_dir_eq_argmax⟩

end RW
