/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Projections on prox-regular sets

Exercise 13.38.  For a closed set `C` and `x̄ ∈ C`:

* prox-regularity of `C` at `x̄` for `v̄ = 0` is equivalent to the existence of a hypomonotone
  localization of `N_C` around `(x̄, 0)`, by Theorem 13.36 applied to `δ_C`
  (`proxRegularSetAt_zero_iff_hasHypomonotoneNormalLocalization`);
* it holds when `C` is fully amenable at `x̄`, by Proposition 13.32;
* it yields, by Proposition 13.37 applied to `δ_C` (for which `P_λ δ_C = P_C` and
  `e_λ δ_C = d_C² / (2λ)`), an open neighborhood `V` of `x̄` on which `P_C` is single-valued,
  monotone and Lipschitz, with `P_C = (I + T)⁻¹` for the localization
  `gph T = gph N_C ∩ (int 𝔹(x̄, ε) × int 𝔹(0, δ))` of `N_C` around `(x̄, 0)`, while `d_C` is
  differentiable at every point of `V \ C` with `∇d_C = (I - P_C) / d_C`.
-/

import RockafellarWets.Chapter13.ProxRegularEnvelopes
import RockafellarWets.Chapter13.AmenableProxRegularity
import RockafellarWets.Chapter10.AmenableIndicatorEquivalence
import RockafellarWets.Chapter8.DistanceSubgradients
import RockafellarWets.Chapter12.ProjectionMonotonicity

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Exercise1338

/-! ### Proximal mappings and envelopes of indicators -/

omit [InnerProductSpace ℝ E] in
theorem proximalObjectiveEReal_indicatorVA_of_mem {C : Set E} {lam : ℝ} {u w : E} (hw : w ∈ C) :
    proximalObjectiveEReal (indicatorVA C) lam u w =
      ((1 / (2 * lam) * ‖w - u‖ ^ 2 : ℝ) : EReal) := by
  rw [proximalObjectiveEReal, indicatorVA_apply_mem hw, zero_add]

omit [InnerProductSpace ℝ E] in
theorem proximalObjectiveEReal_indicatorVA_of_not_mem {C : Set E} {lam : ℝ} {u w : E}
    (hw : w ∉ C) : proximalObjectiveEReal (indicatorVA C) lam u w = ⊤ := by
  rw [proximalObjectiveEReal, indicatorVA_apply_not_mem hw, EReal.top_add_coe]

/-- For a closed nonempty set in finite dimensions, `e_λ δ_C = d_C² / (2λ)`. -/
theorem moreauEnvelopeEReal_indicatorVA [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C)
    (hne : C.Nonempty) {lam : ℝ} (hlam : 0 < lam) (u : E) :
    moreauEnvelopeEReal (indicatorVA C) lam u =
      ((1 / (2 * lam) * infDist u C ^ 2 : ℝ) : EReal) := by
  have hc : 0 < 1 / (2 * lam) := by positivity
  obtain ⟨p, hp⟩ := projMapping_nonempty hC hne u
  rw [moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal]
  refine le_antisymm ?_ (le_iInf fun w ↦ ?_)
  · refine (iInf_le _ p).trans_eq ?_
    rw [proximalObjectiveEReal_indicatorVA_of_mem hp.1, norm_sub_rev, norm_sub_eq_infDist hp]
  · by_cases hw : w ∈ C
    · rw [proximalObjectiveEReal_indicatorVA_of_mem hw, EReal.coe_le_coe_iff]
      have h1 : infDist u C ≤ ‖w - u‖ := by
        rw [norm_sub_rev, ← dist_eq_norm]
        exact infDist_le_dist_of_mem hw
      have h2 : infDist u C ^ 2 ≤ ‖w - u‖ ^ 2 := pow_le_pow_left₀ infDist_nonneg h1 2
      exact mul_le_mul_of_nonneg_left h2 hc.le
    · rw [proximalObjectiveEReal_indicatorVA_of_not_mem hw]
      exact le_top

omit [InnerProductSpace ℝ E] in
/-- Indicators are prox-bounded. -/
theorem isProxBounded_indicatorVA (C : Set E) : IsProxBounded (indicatorVA C) := by
  refine ⟨1, one_pos, 0, ?_⟩
  have h0 : (0 : EReal) ≤ ⨅ w : E, indicatorVA C w + ((1 / (2 * 1)) * ‖w - 0‖ ^ 2 : ℝ) := by
    refine le_iInf fun w ↦ ?_
    by_cases hw : w ∈ C
    · rw [indicatorVA_apply_mem hw, zero_add, ← EReal.coe_zero, EReal.coe_le_coe_iff]
      positivity
    · rw [indicatorVA_apply_not_mem hw, EReal.top_add_coe]
      exact le_top
  exact lt_of_lt_of_le EReal.bot_lt_zero h0

/-- `0` is a proximal normal at every point of `C`. -/
theorem zero_mem_proximalSubdifferential_indicatorVA {C : Set E} {x : E} (hx : x ∈ C) :
    (0 : E) ∈ proximalSubdifferential (indicatorVA C) x := by
  refine ⟨0, by rw [indicatorVA_apply_mem hx]; rfl, 1, one_pos, 1, one_pos, fun y _ ↦ ?_⟩
  by_cases hy : y ∈ C
  · rw [indicatorVA_apply_mem hy, ← EReal.coe_zero, EReal.coe_le_coe_iff, inner_zero_left]
    nlinarith [sq_nonneg ‖y - x‖]
  · rw [indicatorVA_apply_not_mem hy]
    exact le_top

/-! ### Hypomonotone localizations of normal cone mappings -/

/-- **Exercise 13.38(b)**: `N_C` has a hypomonotone localization around `(x̄, 0)`: for some
`ε > 0` and `ρ ≥ 0`, the mapping `T` with `gph T = gph N_C ∩ (int 𝔹(x̄, ε) × int 𝔹(0, ε))`
makes `T + ρI` monotone. -/
def HasHypomonotoneNormalLocalization (C : Set E) (x : E) : Prop :=
  ∃ ε > 0, ∃ ρ ≥ 0, ∀ x₀ v₀ x₁ v₁, v₀ ∈ normalCone C x₀ → v₁ ∈ normalCone C x₁ →
    ‖x₀ - x‖ < ε → ‖x₁ - x‖ < ε → ‖v₀‖ < ε → ‖v₁‖ < ε →
    -ρ * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- For `δ_C` the attentiveness requirement is void: the hypomonotone `f`-attentive
localizations of `∂δ_C = N_C` around `(x̄, 0)` are those of `N_C`. -/
theorem hasHypomonotoneAttentiveLocalization_indicatorVA_iff [FiniteDimensional ℝ E] {C : Set E}
    {x : E} (hx : x ∈ C) :
    HasHypomonotoneAttentiveLocalization (indicatorVA C) x 0 ↔
      HasHypomonotoneNormalLocalization C x := by
  simp only [HasHypomonotoneAttentiveLocalization, HasHypomonotoneNormalLocalization, sub_zero]
  simp_rw [subdifferential_indicatorVA]
  constructor
  · rintro ⟨ε, hε, ρ, hρ, h⟩
    refine ⟨ε, hε, ρ, hρ, fun x₀ v₀ x₁ v₁ hv₀ hv₁ hx₀ hx₁ hv₀' hv₁' ↦ ?_⟩
    have hεE : (0 : EReal) < (ε : EReal) := by exact_mod_cast hε
    have hlo : (0 : EReal) - ε < 0 := by
      rw [zero_sub]
      exact EReal.neg_lt_zero.2 hεE
    have hhi : (0 : EReal) < 0 + ε := by rwa [zero_add]
    refine h x₀ v₀ x₁ v₁ hv₀ hv₁ hx₀ hx₁ hv₀' hv₁' ?_ ?_ ?_ ?_ <;>
      simp only [indicatorVA_apply_mem hx, indicatorVA_apply_mem hv₀.1,
        indicatorVA_apply_mem hv₁.1] <;> assumption
  · rintro ⟨ε, hε, ρ, hρ, h⟩
    exact ⟨ε, hε, ρ, hρ, fun x₀ v₀ x₁ v₁ hv₀ hv₁ hx₀ hx₁ hv₀' hv₁' _ _ _ _ ↦
      h x₀ v₀ x₁ v₁ hv₀ hv₁ hx₀ hx₁ hv₀' hv₁'⟩

/-- **Exercise 13.38**, `(a) ⇔ (b)`: for closed `C ∋ x̄`, prox-regularity at `x̄` for `v̄ = 0`
is the existence of a hypomonotone localization of `N_C` around `(x̄, 0)`. -/
theorem isProxRegularSetAt_zero_iff_hasHypomonotoneNormalLocalization [FiniteDimensional ℝ E]
    {C : Set E} (hC : IsClosed C) {x : E} (hx : x ∈ C) :
    IsProxRegularSetAt C x 0 ↔ HasHypomonotoneNormalLocalization C x := by
  rw [← isProxRegularAt_indicatorVA_iff hx,
    ← hasHypomonotoneAttentiveLocalization_indicatorVA_iff hx]
  exact subdifferential_characterization_of_prox_regularity
    ((isLocallyLscAt_indicatorVA_iff hx).2 (RW.IsClosed.isLocallyClosedAt hC x))
    (zero_mem_proximalSubdifferential_indicatorVA hx)

/-! ### Projections and the distance function -/

/-- The derivative of `d_C` off `C` from that of `d_C²`. -/
theorem hasFDerivAt_infDist_of_sq {C : Set E} {u p : E} (hC : IsClosed C) (hne : C.Nonempty)
    (hu : u ∉ C) (h : HasFDerivAt (fun z ↦ infDist z C ^ 2) (innerSL ℝ ((2 : ℝ) • (u - p))) u) :
    HasFDerivAt (fun z ↦ infDist z C) (innerSL ℝ ((infDist u C)⁻¹ • (u - p))) u := by
  have hpos : 0 < infDist u C := (hC.notMem_iff_infDist_pos hne).1 hu
  have hne : infDist u C ^ 2 ≠ 0 := by positivity
  have hs := h.sqrt hne
  have heq : (fun z ↦ √(infDist z C ^ 2)) = fun z ↦ infDist z C := by
    funext z
    exact Real.sqrt_sq infDist_nonneg
  rw [heq, Real.sqrt_sq infDist_nonneg] at hs
  convert hs using 1
  ext w
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]
  field_simp

/-- **Exercise 13.38**, `(c)`, `(d)` and the formulas: if `C` is closed and prox-regular at
`x̄ ∈ C` for `v̄ = 0`, there are an open neighborhood `V` of `x̄`, a single-valued `P` and
`ε, δ > 0` such that on `V`, `P_C = {P}` is monotone and Lipschitz with `P_C = (I + T)⁻¹` for the
localization `gph T = gph N_C ∩ (int 𝔹(x̄, ε) × int 𝔹(0, δ))` of `N_C` around `(x̄, 0)`, and at each
point of `V \ C` the distance `d_C` is differentiable with `∇d_C = (I - P_C)/d_C`. -/
theorem IsProxRegularSetAt.projection [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C)
    {x : E} (hx : x ∈ C) (h : IsProxRegularSetAt C x 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∃ P : E → E, ∃ ε > 0, ∃ δ > 0, P x = x ∧
      (∀ u ∈ V, projMapping C u = {P u}) ∧
      (∀ u ∈ V, ∀ u' ∈ V, 0 ≤ ⟪P u' - P u, u' - u⟫_ℝ ∧ ‖P u' - P u‖ ≤ 2 * ‖u' - u‖) ∧
      (∀ u ∈ V, ∀ y, P u = y ↔ u - y ∈ normalCone C y ∧ ‖y - x‖ < ε ∧ ‖u - y‖ < δ) ∧
      (∀ u ∈ V, u ∉ C →
        HasFDerivAt (fun z ↦ infDist z C) (innerSL ℝ ((infDist u C)⁻¹ • (u - P u))) u) := by
  have hpr : IsProxRegularAt (indicatorVA C) x 0 := (isProxRegularAt_indicatorVA_iff hx).2 h
  obtain ⟨ε, hε, lam₀, hlam₀, hmain⟩ :=
    proximal_mappings_and_moreau_envelopes hpr (isProxBounded_indicatorVA C)
  set lam := lam₀ / 2 with hlam_def
  have hlam : 0 < lam := by positivity
  obtain ⟨P, hopen, hxU, hPx, hsingle, hmono, henv, -, hloc⟩ :=
    hmain lam hlam (by rw [hlam_def]; linarith)
  refine ⟨proxRange (indicatorVA C) x ε lam, hopen, hxU, P, ε, hε, lam * ε, by positivity, hPx,
    fun u hu ↦ ?_, hmono, fun u hu y ↦ ?_, fun u hu huC ↦ ?_⟩
  · rw [← proximalMappingEReal_indicatorVA C hlam]
    exact hsingle u hu
  · constructor
    · intro hPy
      have hw := (hloc u hu (lam⁻¹ • (u - P u))).1 rfl
      obtain ⟨y', ⟨hN, hy'x, -, hnorm⟩, hu'⟩ := hw
      have hy' : y' = P u := by
        rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] at hu'
        calc y' = (y' + (u - P u)) - (u - P u) := by abel
          _ = u - (u - P u) := by rw [← hu']
          _ = P u := by abel
      rw [← hPy, ← hy']
      rw [subdifferential_indicatorVA] at hN
      have hu_eq : u - y' = lam • (lam⁻¹ • (u - P u)) := by
        rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, hy']
      refine ⟨?_, hy'x, ?_⟩
      · rw [hu_eq]
        exact (isCone_normalCone hN.1).2 hN hlam
      · rw [hu_eq, norm_smul, Real.norm_of_nonneg hlam.le]
        exact mul_lt_mul_of_pos_left hnorm hlam
    · rintro ⟨hN, hyx, hnorm⟩
      have hyC : y ∈ C := hN.1
      have hw : lam⁻¹ • (u - y) ∈ proxLocalization (indicatorVA C) x ε y := by
        refine ⟨?_, hyx, ?_, ?_⟩
        · rw [subdifferential_indicatorVA]
          exact (isCone_normalCone hyC).2 hN (inv_pos.2 hlam)
        · rw [indicatorVA_apply_mem hyC, indicatorVA_apply_mem hx, zero_add]
          exact_mod_cast hε
        · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le), inv_mul_lt_iff₀ hlam]
          exact hnorm
      have hu' : u = y + lam • (lam⁻¹ • (u - y)) := by
        rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]; abel
      have := (hloc u hu (lam⁻¹ • (u - y))).2 ⟨y, hw, hu'⟩
      have h2 := congrArg (fun z ↦ lam • z) this
      simp only [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] at h2
      have : P u = y := by
        have h3 : u - P u - (u - y) = 0 := by rw [h2, sub_self]
        have h4 : y - P u = 0 := by rw [← h3]; abel
        exact (sub_eq_zero.1 h4).symm
      exact this
  · obtain ⟨-, -, hd⟩ := henv u hu
    have hfun : (fun z ↦ (moreauEnvelopeEReal (indicatorVA C) lam z).toReal) =
        fun z ↦ 1 / (2 * lam) * infDist z C ^ 2 := by
      funext z
      rw [moreauEnvelopeEReal_indicatorVA hC ⟨x, hx⟩ hlam, EReal.toReal_coe]
    rw [hfun] at hd
    have hd2 := hd.const_mul (2 * lam)
    have hfun2 : (fun z ↦ 2 * lam * (1 / (2 * lam) * infDist z C ^ 2)) =
        fun z ↦ infDist z C ^ 2 := by
      funext z
      field_simp
    rw [hfun2] at hd2
    refine hasFDerivAt_infDist_of_sq hC ⟨x, hx⟩ huC (hd2.congr_fderiv ?_)
    ext w
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, real_inner_smul_left,
      smul_eq_mul]
    field_simp

end Exercise1338

section Exercise1338Amenable

variable [FiniteDimensional ℝ E]

/-- **Exercise 13.38**: fully amenable sets are prox-regular for `v̄ = 0` (Proposition 13.32). -/
theorem SetFullyAmenableAt.isProxRegularSetAt_zero {C : Set E} {x : E}
    (h : SetFullyAmenableAt C x) (hx : x ∈ C) : IsProxRegularSetAt C x 0 := by
  have hf : StronglyAmenableAt (indicatorVA C) x :=
    (setFullyAmenableAt_iff_indicator.1 h).stronglyAmenableAt
  have h0 : (0 : E) ∈ subdifferential (indicatorVA C) x := by
    rw [subdifferential_indicatorVA]
    exact (isCone_normalCone hx).1
  exact (isProxRegularAt_indicatorVA_iff hx).1 ((prox_regularity_from_amenability hf).1.1 0 h0)

/-- **Exercise 13.38** (projections on prox-regular sets). For a closed set `C` and `x̄ ∈ C`,
(a) prox-regularity of `C` at `x̄` for `v̄ = 0` is equivalent to (b) the existence of a
hypomonotone localization of `N_C` around `(x̄, 0)`; these hold when `C` is fully amenable at
`x̄`, and they imply (c) `P_C` is single-valued around `x̄` and (d) `d_C` is differentiable at the
points outside `C` near `x̄`. More precisely there is an open neighborhood `V` of `x̄` on which
`P_C` is monotone and Lipschitz with `P_C = (I + T)⁻¹` for a localization `T` of `N_C` around
`(x̄, 0)`, and `∇d_C = (I - P_C)/d_C` on `V \ C`. -/
theorem projections_on_prox_regular_sets {C : Set E} (hC : IsClosed C)
    {x : E} (hx : x ∈ C) :
    (IsProxRegularSetAt C x 0 ↔ HasHypomonotoneNormalLocalization C x) ∧
    (SetFullyAmenableAt C x → IsProxRegularSetAt C x 0) ∧
    (IsProxRegularSetAt C x 0 →
      (∀ᶠ u in 𝓝 x, ∃ p, projMapping C u = {p}) ∧
      (∀ᶠ u in 𝓝 x, u ∉ C → DifferentiableAt ℝ (fun z ↦ infDist z C) u) ∧
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∃ P : E → E, ∃ ε > 0, ∃ δ > 0, P x = x ∧
        (∀ u ∈ V, projMapping C u = {P u}) ∧
        (∀ u ∈ V, ∀ u' ∈ V, 0 ≤ ⟪P u' - P u, u' - u⟫_ℝ ∧ ‖P u' - P u‖ ≤ 2 * ‖u' - u‖) ∧
        (∀ u ∈ V, ∀ y, P u = y ↔ u - y ∈ normalCone C y ∧ ‖y - x‖ < ε ∧ ‖u - y‖ < δ) ∧
        (∀ u ∈ V, u ∉ C →
          HasFDerivAt (fun z ↦ infDist z C) (innerSL ℝ ((infDist u C)⁻¹ • (u - P u))) u)) := by
  refine ⟨isProxRegularSetAt_zero_iff_hasHypomonotoneNormalLocalization hC hx,
    fun h ↦ h.isProxRegularSetAt_zero hx, fun h ↦ ?_⟩
  obtain ⟨V, hV, hxV, P, ε, hε, δ, hδ, hPx, hsingle, hmono, hres, hdiff⟩ := h.projection hC hx
  refine ⟨?_, ?_, V, hV, hxV, P, ε, hε, δ, hδ, hPx, hsingle, hmono, hres, hdiff⟩
  · filter_upwards [hV.mem_nhds hxV] with u hu
    exact ⟨P u, hsingle u hu⟩
  · filter_upwards [hV.mem_nhds hxV] with u hu huC
    exact (hdiff u hu huC).differentiableAt

end Exercise1338Amenable

end RW
