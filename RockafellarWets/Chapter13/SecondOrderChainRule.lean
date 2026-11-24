/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: The chain rule for second subderivatives

Theorem 13.14, general part.  For `f = g ∘ G` with `G` of class `C²` and `g(G(x̄))` finite, every
`y` with `∇G(x̄)* y = v` gives the identity of quotients

  `Δ²_τ f(x̄ | v)(w') = Δ²_τ g(G(x̄) | y)(Δ_τ G(x̄)(w')) + Δ²_τ (yG)(x̄ | v)(w')`,

where `Δ_τ G(x̄)(w') = [G(x̄ + τw') - G(x̄)]/τ → ∇G(x̄)w` and the last quotient converges to
`⟪y, ∇²G(x̄)(w, w)⟫`.  Passing to lower limits gives the inequality
`d²f(x̄ | v)(w) ≥ d²g(G(x̄) | y)(∇G(x̄)w) + ⟪w, ∇²(yG)(x̄)w⟫`
(`secondSubderivative_comp_ge`).  Under regularity of `g` and the horizon qualification, the set
`Y(x̄, v) = {y ∈ ∂g(G(x̄)) | ∇G(x̄)* y = v}` is nonempty, convex and compact
(`multiplierSet_properties`).
-/

import RockafellarWets.Chapter13.SecondOrderTangentChainRule
import RockafellarWets.Chapter13.PiecewiseLinearQuadraticParabolic
import RockafellarWets.Chapter10.SemiderivativeCalculus
import RockafellarWets.Chapter10.BasicChainRule
import RockafellarWets.Chapter8.SubgradientRelationships
import RockafellarWets.Chapter8.SubdifferentialRegularityCriterion
import RockafellarWets.Chapter3.HorizonAddition
import RockafellarWets.Chapter11.PiecewiseLinearQuadraticProgramming
import RockafellarWets.Chapter10.AmenableComposition
import RockafellarWets.Chapter10.SmoothLocalExtension
import RockafellarWets.Chapter10.FiniteInfimumSubderivatives
import RockafellarWets.Chapter12.Hypomonotonicity

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### The general inequality -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The quotient identity in the proof of Theorem 13.14. -/
theorem secondDifferenceQuotient_comp_eq {G : E → F} {g : F → EReal} {x : E} {c : ℝ}
    (hc : g (G x) = c) {y : F} {v : E} {τ : ℝ} (hτ : 0 < τ) (w : E) :
    secondDifferenceQuotient (g ∘ G) x v τ w =
      secondDifferenceQuotient g (G x) y τ (τ⁻¹ • (G (x + τ • w) - G x)) +
        ((2 / τ ^ 2 * (⟪y, G (x + τ • w)⟫_ℝ - ⟪y, G x⟫_ℝ - τ * ⟪v, w⟫_ℝ) : ℝ) : EReal) := by
  have hu : G x + τ • (τ⁻¹ • (G (x + τ • w) - G x)) = G (x + τ • w) := by
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
  have hc' : (g ∘ G) x = c := hc
  rcases ereal_trichotomy (g (G (x + τ • w))) with h | h | ⟨r, h⟩
  · rw [secondDifferenceQuotient_of_bot hτ.ne' hc' h,
      secondDifferenceQuotient_of_bot hτ.ne' hc (by rw [hu]; exact h), EReal.bot_add]
  · rw [secondDifferenceQuotient_of_top hτ.ne' hc' h,
      secondDifferenceQuotient_of_top hτ.ne' hc (by rw [hu]; exact h), EReal.top_add_coe]
  · rw [secondDifferenceQuotient_of_coe hc' h,
      secondDifferenceQuotient_of_coe hc (by rw [hu]; exact h),
      ← EReal.coe_add, EReal.coe_eq_coe_iff, real_inner_smul_right, inner_sub_right]
    field_simp
    ring

/-- **Theorem 13.14**, the inequality: for `G` of class `C²`, `g(G(x̄))` finite and any `y` with
`∇G(x̄)* y = v`,
`d²(g ∘ G)(x̄ | v)(w) ≥ d²g(G(x̄) | y)(∇G(x̄)w) + ⟪y, ∇²G(x̄)(w, w)⟫`. -/
theorem secondSubderivative_comp_ge {G : E → F} (hG : ContDiff ℝ 2 G) {g : F → EReal} {x : E}
    {c : ℝ} (hc : g (G x) = c) {y : F} {v : E} (hv : (fderiv ℝ G x).adjoint y = v) (w : E) :
    secondSubderivative g (G x) y (fderiv ℝ G x w) +
        ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal) ≤
      secondSubderivative (g ∘ G) x v w := by
  set L : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.compL ℝ E F ℝ (innerSL ℝ y)
  have hd1 : ∀ z, HasFDerivAt G (fderiv ℝ G z) z := fun z ↦
    (hG.differentiable (by norm_num) z).hasFDerivAt
  have hd2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have hφ : ∀ᶠ z in 𝓝 x, HasFDerivAt (fun z ↦ ⟪y, G z⟫_ℝ) (L (fderiv ℝ G z)) z :=
    .of_forall fun z ↦ (innerSL ℝ y).hasFDerivAt.comp z (hd1 z)
  have hφ' : HasFDerivAt (fun z ↦ L (fderiv ℝ G z)) (L.comp (fderiv ℝ (fderiv ℝ G) x)) x :=
    L.hasFDerivAt.comp x hd2
  have hvL : ∀ w', L (fderiv ℝ G x) w' = ⟪v, w'⟫_ℝ := fun w' ↦ by
    simp [L, ← hv, ContinuousLinearMap.adjoint_inner_left]
  have hR := tendsto_secondDifferenceQuotient_of_hasFDerivAt hφ hφ' hvL w
  have hRval : (L.comp (fderiv ℝ (fderiv ℝ G) x)) w w = ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ := by
    simp [L]
  rw [hRval] at hR
  have hR' : Tendsto (fun p : ℝ × E ↦ ((2 / p.1 ^ 2 * (⟪y, G (x + p.1 • p.2)⟫_ℝ - ⟪y, G x⟫_ℝ -
      p.1 * ⟪v, p.2⟫_ℝ) : ℝ) : EReal)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hR
  have hpath : Tendsto (fun p : ℝ × E ↦ (p.1, p.1⁻¹ • (G (x + p.1 • p.2) - G x)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (fderiv ℝ G x w)) :=
    tendsto_fst.prodMk ((hd1 x).hasDirectionalSemiderivative w)
  have hid : (fun p : ℝ × E ↦ secondDifferenceQuotient (g ∘ G) x v p.1 p.2) =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 w]
      fun p ↦ secondDifferenceQuotient g (G x) y p.1 (p.1⁻¹ • (G (x + p.1 • p.2) - G x)) +
        ((2 / p.1 ^ 2 * (⟪y, G (x + p.1 • p.2)⟫_ℝ - ⟪y, G x⟫_ℝ - p.1 * ⟪v, p.2⟫_ℝ) : ℝ) :
          EReal) := by
    filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
    exact secondDifferenceQuotient_comp_eq hc hp p.2
  have h1 : secondSubderivative (g ∘ G) x v w = liminf (fun p : ℝ × E ↦
      secondDifferenceQuotient g (G x) y p.1 (p.1⁻¹ • (G (x + p.1 • p.2) - G x)) +
        ((2 / p.1 ^ 2 * (⟪y, G (x + p.1 • p.2)⟫_ℝ - ⟪y, G x⟫_ℝ - p.1 * ⟪v, p.2⟫_ℝ) : ℝ) :
          EReal)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
    liminf_congr hid
  rw [h1, liminf_add_of_tendsto_coe (u := fun p : ℝ × E ↦
    secondDifferenceQuotient g (G x) y p.1 (p.1⁻¹ • (G (x + p.1 • p.2) - G x))) hR']
  gcongr
  change _ ≤ liminf ((fun q : ℝ × F ↦ secondDifferenceQuotient g (G x) y q.1 q.2) ∘
    fun p : ℝ × E ↦ (p.1, p.1⁻¹ • (G (x + p.1 • p.2) - G x))) _
  rw [liminf_comp]
  exact liminf_le_liminf_of_le hpath

/-! ### The multiplier set `Y(x̄, v)` -/

/-- The multiplier set `Y(x̄, v) = {y ∈ ∂g(G(x̄)) | ∇G(x̄)* y = v}` of Theorem 13.14. -/
def multiplierSet (G : E → F) (g : F → EReal) (x v : E) : Set F :=
  {y | y ∈ subdifferential g (G x) ∧ (fderiv ℝ G x).adjoint y = v}

/-- **Theorem 13.14**: when `g` is regular at `G(x̄)` and the horizon qualification holds, for every
`v ∈ ∂(g ∘ G)(x̄)` the multiplier set `Y(x̄, v)` is nonempty, convex and compact. -/
theorem multiplierSet_properties {G : E → F} (hG : ContDiff ℝ 2 G) {g : F → EReal} {x : E}
    (hl : LowerSemicontinuous g) (hr : IsSubdifferentiallyRegularAt g (G x))
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} (hv : v ∈ subdifferential (g ∘ G) x) :
    (multiplierSet G g x v).Nonempty ∧ Convex ℝ (multiplierSet G g x v) ∧
      IsCompact (multiplierSet G g x v) := by
  have hc : g (G x) = ((g (G x)).toReal : EReal) := (EReal.coe_toReal hr.2.1 hr.1).symm
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hsub := subdifferential_comp_eq_of_regular hG1 hl hr hQ
  have hreg : subdifferential g (G x) = regularSubdifferential g (G x) :=
    hr.subdifferential_eq_regularSubdifferential
  obtain ⟨hRcl, hRconv, -⟩ := subdifferential_properties hc
  set A := (fderiv ℝ G x).adjoint with hA
  have hY : multiplierSet G g x v = regularSubdifferential g (G x) ∩ (A : F →ₗ[ℝ] E) ⁻¹' {v} := by
    ext y
    simp only [multiplierSet, hreg, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    rfl
  have hne : (multiplierSet G g x v).Nonempty := by
    rw [hsub] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨y, hy, rfl⟩
  have hLconv : Convex ℝ ((A : F →ₗ[ℝ] E) ⁻¹' {v}) := (convex_singleton v).linear_preimage _
  have hLcl : IsClosed ((A : F →ₗ[ℝ] E) ⁻¹' {v}) :=
    isClosed_singleton.preimage A.continuous
  refine ⟨hne, ?_, ?_⟩
  · rw [hY]; exact hRconv.inter hLconv
  · rw [hY]
    refine Metric.isCompact_of_isClosed_isBounded (hRcl.inter hLcl) ?_
    rw [isBounded_iff_horizonCone_eq_singleton_zero]
    have hne' : (regularSubdifferential g (G x) ∩ (A : F →ₗ[ℝ] E) ⁻¹' {v}).Nonempty := hY ▸ hne
    rw [horizonCone_inter_eq_inter_horizonCone hRconv hLconv hRcl hLcl hne',
      horizonCone_preimage_linearMap_eq (A : F →ₗ[ℝ] E) (convex_singleton v) isClosed_singleton
        (hne'.mono inter_subset_right)]
    have hsing : horizonCone ({v} : Set E) = {0} :=
      isBounded_iff_horizonCone_eq_singleton_zero.1 Bornology.isBounded_singleton
    rw [hsing]
    refine Subset.antisymm (fun y ⟨hy1, hy2⟩ ↦ ?_) ?_
    · exact hQ y (horizonCone_regularSubdifferential_subset hc hy1) hy2
    · rintro y rfl
      exact ⟨zero_mem_horizonCone _, by simp⟩

/-! ### The duality 13(20)–13(21) -/

omit [FiniteDimensional ℝ F] in
theorem fenchelConjugate_zero_fun : fenchelConjugate (fun _ : E ↦ (0 : EReal)) =
    indicatorVA ({0} : Set E) := by
  have h : (fun _ : E ↦ (0 : EReal)) = indicatorVA ((⊤ : Submodule ℝ E) : Set E) := by
    funext z
    rw [indicatorVA_apply_mem (by simp)]
  rw [h, fenchelConjugate_indicatorVA_submodule, Submodule.top_orthogonal_eq_bot,
    Submodule.bot_coe]

/-- The linear-programming duality of 13(20)–13(21): for convex piecewise linear-quadratic `g`
with `ū ∈ dom g`, a continuous linear `A`, and `Y = {y ∈ ∂g(ū) | A* y = v}` nonempty and compact,
there are `z̄` and a maximizer `y₀` of `⟪·, b⟫` on `Y` with `dg(ū)(b + Az̄) = ⟪y₀, b⟫ + ⟪v, z̄⟫`. -/
theorem exists_subderivative_eq_max_multiplier {g : F → EReal} (hg : IsPiecewiseLinearQuadratic g)
    (hgc : Convex ℝ (epigraph g)) {u : F} (hu : u ∈ effectiveDomain g) (A : E →L[ℝ] F) (v : E)
    (b : F) (hne : {y | y ∈ subdifferential g u ∧ A.adjoint y = v}.Nonempty)
    (hcpt : IsCompact {y | y ∈ subdifferential g u ∧ A.adjoint y = v}) :
    ∃ z : E, ∃ y₀ ∈ {y | y ∈ subdifferential g u ∧ A.adjoint y = v},
      (∀ y ∈ {y | y ∈ subdifferential g u ∧ A.adjoint y = v}, ⟪y, b⟫_ℝ ≤ ⟪y₀, b⟫_ℝ) ∧
      subderivative g u (b + A z) = ((⟪y₀, b⟫_ℝ + ⟪v, z⟫_ℝ : ℝ) : EReal) := by
  classical
  set Y := {y | y ∈ subdifferential g u ∧ A.adjoint y = v} with hY
  set P := subdifferential g u with hP
  obtain ⟨hPne, hPpoly, -⟩ := hg.convex_subgradient_properties hgc hu
  have hsupp : subderivative g u = supportFunction P := hg.subderivative_eq_support hgc hu
  have hh : IsPiecewiseLinearQuadratic (subderivative g u) :=
    (hg.subderivative_piecewiseLinear hu).1.isPiecewiseLinearQuadratic
  have hhp : IsProper (subderivative g u) := by
    rw [hsupp]; exact isProper_supportFunction hPne
  have hhc : Convex ℝ (epigraph (subderivative g u)) := by
    rw [hsupp]; exact convex_epigraph_of_sublinear (sublinear_supportFunction P)
  have hk : IsPiecewiseLinearQuadratic (fun _ : E ↦ (0 : EReal)) := by
    have h := isPiecewiseLinearQuadratic_inner (0 : E)
    simpa using h
  have hkp : IsProper (fun _ : E ↦ (0 : EReal)) :=
    ⟨⟨0, EReal.zero_lt_top⟩, fun _ ↦ EReal.bot_lt_zero⟩
  have hkc : Convex ℝ (epigraph (fun _ : E ↦ (0 : EReal))) := by
    have : epigraph (fun _ : E ↦ (0 : EReal)) = univ ×ˢ Ici 0 := by
      ext ⟨z, r⟩
      simp [epigraph]
    rw [this]
    exact convex_univ.prod (convex_Ici 0)
  -- a maximizer of `⟪·, b⟫` on `Y`
  obtain ⟨y₀, hy₀, hmax⟩ := hcpt.exists_isMaxOn hne
    (show ContinuousOn (fun y : F ↦ ⟪y, b⟫_ℝ) Y from
      (continuous_id.inner continuous_const).continuousOn)
  have hmax' : ∀ y ∈ Y, ⟪y, b⟫_ℝ ≤ ⟪y₀, b⟫_ℝ := fun y hy ↦ hmax hy
  -- the dual objective
  have hhconj : fenchelConjugate (subderivative g u) = indicatorVA P := by
    rw [hsupp]; exact fenchelConjugate_supportFunction_of_closed_convex hPpoly.convex
      hPpoly.isClosed
  have hdual : ∀ y, fenchelDual (fun _ : E ↦ (0 : EReal)) (subderivative g u) (-A) b (-v) y =
      if y ∈ Y then ((⟪b, y⟫_ℝ : ℝ) : EReal) else ⊥ := by
    intro y
    simp only [fenchelDual, hhconj, fenchelConjugate_zero_fun]
    have hadj : (-A).adjoint y - -v = v - A.adjoint y := by
      rw [map_neg, ContinuousLinearMap.neg_apply]; abel
    rw [hadj]
    by_cases hyP : y ∈ P
    · by_cases hyA : A.adjoint y = v
      · have hyY : y ∈ Y := ⟨hyP, hyA⟩
        rw [if_pos hyY, indicatorVA_apply_mem hyP,
          indicatorVA_apply_mem (show v - A.adjoint y ∈ ({0} : Set E) by simp [hyA])]
        simp
      · have hyY : y ∉ Y := fun h ↦ hyA h.2
        rw [if_neg hyY, indicatorVA_apply_mem hyP,
          indicatorVA_apply_not_mem (show v - A.adjoint y ∉ ({0} : Set E) by
            simp [sub_eq_zero, Ne.symm hyA])]
        simp
    · have hyY : y ∉ Y := fun h ↦ hyP h.1
      rw [if_neg hyY, indicatorVA_apply_not_mem hyP]
      simp
  have hsup : (⨆ y, fenchelDual (fun _ : E ↦ (0 : EReal)) (subderivative g u) (-A) b (-v) y) =
      ((⟪y₀, b⟫_ℝ : ℝ) : EReal) := by
    refine le_antisymm (iSup_le fun y ↦ ?_) ?_
    · rw [hdual]
      split_ifs with hy
      · rw [real_inner_comm]; exact EReal.coe_le_coe_iff.2 (hmax' y hy)
      · exact bot_le
    · refine le_trans (le_of_eq ?_) (le_iSup _ y₀)
      rw [hdual, if_pos hy₀, real_inner_comm]
  obtain ⟨⟨a, ha₁, ha₂⟩, ⟨z, hz⟩, -, -⟩ := piecewiseLinearQuadratic_fenchel_duality (-A) b (-v)
    hk hkp hkc hh hhp hhc (Or.inr ⟨_, hsup⟩)
  have ha : a = ⟪y₀, b⟫_ℝ := by
    rw [hsup] at ha₂; exact_mod_cast ha₂.symm
  have hzval : fenchelPrimal (fun _ : E ↦ (0 : EReal)) (subderivative g u) (-A) b (-v) z = a := by
    rw [hz.1, ha₁]
  refine ⟨z, y₀, hy₀, hmax', ?_⟩
  simp only [fenchelPrimal, ContinuousLinearMap.neg_apply, sub_neg_eq_add, inner_neg_left,
    add_zero] at hzval
  rw [ha] at hzval
  rcases ereal_trichotomy (subderivative g u (b + A z)) with h' | h' | ⟨r, h'⟩
  · exact absurd h' (hh.ne_bot _)
  · rw [h', EReal.coe_add_top] at hzval
    exact absurd hzval (EReal.coe_ne_top _).symm
  · rw [h', ← EReal.coe_add, EReal.coe_eq_coe_iff] at hzval
    rw [h', EReal.coe_eq_coe_iff]
    linarith

/-! ### Composition with an affine mapping -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Epigraphs of limits along paths lie in the inner limits of the epigraphs. -/
theorem epigraph_subset_innerSetLimitAlong_of_paths {g : ℝ → E → EReal} {Φ : E → EReal}
    (h : ∀ w, Φ w < ⊤ → ∃ p : ℝ → E, Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
      Tendsto (fun τ ↦ g τ (p τ)) (𝓝[>] (0 : ℝ)) (𝓝 (Φ w))) :
    epigraph Φ ⊆ innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (g τ)) := by
  rintro ⟨w, α⟩ hwα N hN
  change Φ w ≤ (α : EReal) at hwα
  obtain ⟨p, hp, hlim⟩ := h w (lt_of_le_of_lt hwα (EReal.coe_lt_top α))
  obtain ⟨V, hV, I, hI, hVI⟩ := mem_nhds_prod_iff.1 hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hI
  have hlt : Φ w < ((α + ε / 2 : ℝ) : EReal) :=
    lt_of_le_of_lt hwα (EReal.coe_lt_coe_iff.2 (by linarith))
  filter_upwards [hlim.eventually (Iio_mem_nhds hlt), hp.eventually hV] with τ hτ hτV
  refine ⟨(p τ, α + ε / 2), le_of_lt hτ, hVI ⟨hτV, hball ?_⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
  linarith

/-- For `g` convex and piecewise linear-quadratic with `ū ∈ dom g`, `y ∈ ∂g(ū)` and `A* y = v`, the
composition `ḡ(z) = g(ū + A(z - x̄))` has `d²ḡ(x̄ | v)(w) = d²g(ū | y)(Aw)`. -/
theorem secondSubderivative_comp_affine {g : F → EReal} (hg : IsPiecewiseLinearQuadratic g)
    (hgc : Convex ℝ (epigraph g)) {u : F} (hu : u ∈ effectiveDomain g) (A : E →L[ℝ] F)
    {x v : E} {y : F} (hy : y ∈ subdifferential g u) (hyv : A.adjoint y = v) (w : E) :
    secondSubderivative (fun z ↦ g (u + A (z - x))) x v w = secondSubderivative g u y (A w) := by
  have hfin : g u = ((g u).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hu) (hg.ne_bot u)).symm
  have hp : IsProper g := ⟨⟨u, hu⟩, fun z ↦ lt_of_le_of_ne bot_le (hg.ne_bot z).symm⟩
  have hq : ∀ τ w', secondDifferenceQuotient (fun z ↦ g (u + A (z - x))) x v τ w' =
      secondDifferenceQuotient g u y τ (A w') := by
    intro τ w'
    simp only [secondDifferenceQuotient, add_sub_cancel_left, sub_self, map_zero, add_zero,
      map_smul, ← hyv, ContinuousLinearMap.adjoint_inner_left]
  have hv : ∀ u', ((⟪y, u'⟫_ℝ : ℝ) : EReal) ≤ subderivative g u u' :=
    inner_le_subderivative_of_convex hp hgc hfin hy
  obtain ⟨M⟩ := hg.nonempty_localModel u
  have hlim := M.tendsto_secondDifferenceQuotient hg hu hv (A w)
  refine le_antisymm ?_ ?_
  · have ht : Tendsto (fun τ : ℝ ↦ (τ, w)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
      tendsto_id.prodMk tendsto_const_nhds
    calc secondSubderivative (fun z ↦ g (u + A (z - x))) x v w
        ≤ liminf ((fun p : ℝ × E ↦ secondDifferenceQuotient (fun z ↦ g (u + A (z - x))) x v
            p.1 p.2) ∘ fun τ : ℝ ↦ (τ, w)) (𝓝[>] (0 : ℝ)) := by
          rw [secondSubderivative, liminf_comp]
          exact liminf_le_liminf_of_le ht
      _ = secondSubderivative g u y (A w) := by
          simp only [Function.comp_def, hq]
          exact hlim.liminf_eq
  · have hpath : Tendsto (fun p : ℝ × E ↦ (p.1, A p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (A w)) :=
      tendsto_fst.prodMk ((A.continuous.tendsto w).comp tendsto_snd)
    rw [secondSubderivative, secondSubderivative]
    simp only [hq]
    change _ ≤ liminf ((fun q : ℝ × F ↦ secondDifferenceQuotient g u y q.1 q.2) ∘
      fun p : ℝ × E ↦ (p.1, A p.2)) _
    rw [liminf_comp]
    exact liminf_le_liminf_of_le hpath

/-! ### The upper estimate for convex piecewise linear-quadratic `g` -/

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A polyhedral convex cone is contained in its tangent cone at any of its points. -/
theorem IsPolyhedral.subset_tangentCone_of_isCone {K : Set E} (hK : IsPolyhedral K)
    (hc : IsCone K) {a : E} (ha : a ∈ K) : K ⊆ tangentCone K a := by
  intro k hk
  have hadd : ∀ t : ℝ, 0 < t → a + t • k ∈ K := by
    intro t ht
    have h1 : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • (t • k) ∈ K :=
      hK.convex ha (hc.2 hk ht) (by norm_num) (by norm_num) (by norm_num)
    have h2 := hc.2 h1 (show (0 : ℝ) < 2 by norm_num)
    rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
      one_smul] at h2
  obtain ⟨t, hiff, ht⟩ := ((hK.eventually_ray_mem_iff ha k).and self_mem_nhdsWithin).exists
  exact hiff.1 (hadd t ht)

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- For a sublinear `h` finite at `a`, `dh(a)(ζ) ≤ h(ζ)`. -/
theorem subderivative_le_of_sublinear {h : E → EReal} (hh : Sublinear h) {a : E} {c : ℝ}
    (ha : h a = c) (ζ : E) : subderivative h a ζ ≤ h ζ := by
  have ht : Tendsto (fun τ : ℝ ↦ (τ, ζ)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 ζ) :=
    tendsto_id.prodMk tendsto_const_nhds
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), differenceQuotient h a τ ζ ≤ h ζ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : (0 : ℝ) < τ := hτ
    have hsub := hh.2 a (τ • ζ)
    rw [hh.1.2 hτ', ha] at hsub
    rcases ereal_trichotomy (h (a + τ • ζ)) with h1 | h1 | ⟨r, h1⟩
    · rw [differenceQuotient_eq_bot hτ' ha h1]; exact bot_le
    · rw [h1, top_le_iff] at hsub
      have hζ : h ζ = ⊤ := by
        rcases ereal_trichotomy (h ζ) with h2 | h2 | ⟨s, h2⟩
        · rw [h2, EReal.coe_mul_bot_of_pos hτ', EReal.add_bot] at hsub
          exact absurd hsub (by simp)
        · exact h2
        · rw [h2, ← EReal.coe_mul, ← EReal.coe_add] at hsub
          exact absurd hsub (EReal.coe_ne_top _)
      rw [hζ]; exact le_top
    · rw [differenceQuotient_eq_coe ha h1]
      rcases ereal_trichotomy (h ζ) with h2 | h2 | ⟨s, h2⟩
      · rw [h1, h2, EReal.coe_mul_bot_of_pos hτ', EReal.add_bot] at hsub
        exact absurd hsub (by simp)
      · rw [h2]; exact le_top
      · rw [h1, h2, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hsub
        rw [h2, EReal.coe_le_coe_iff, inv_mul_le_iff₀ hτ']
        linarith
  calc subderivative h a ζ
      ≤ liminf (fun p : ℝ × E ↦ differenceQuotient h a p.1 p.2) (map (fun τ : ℝ ↦ (τ, ζ))
          (𝓝[>] (0 : ℝ))) := liminf_le_liminf_of_le ht
    _ = liminf (fun τ ↦ differenceQuotient h a τ ζ) (𝓝[>] (0 : ℝ)) :=
        (liminf_comp (fun p : ℝ × E ↦ differenceQuotient h a p.1 p.2) _ _).symm
    _ ≤ h ζ := liminf_le_of_frequently_le' hev.frequently

/-- The upper estimate in the proof of Theorem 13.14 for convex piecewise linear-quadratic `g`:
for `w` with `dg(ū)(∇G(x̄)w) = ⟪v, w⟫` there are a maximizer `y₀` of `⟪·, ∇²G(x̄)(w, w)⟫` on
`Y(x̄, v)` and a path `w_τ → w` along which `Δ²_τ f(x̄ | v)(w_τ)` converges to a value at most
`d²g(ū)(∇G(x̄)w) + ⟪y₀, ∇²G(x̄)(w, w)⟫`.  The path comes from a parabolic arc of
`C = G⁻¹(dom g)` (13.13, polyhedral case) whose second-order direction `z̄` solves the dual
problem 13(21). -/
theorem exists_path_secondDifferenceQuotient_comp {G : E → F} (hG : ContDiff ℝ 2 G)
    {g : F → EReal} (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} (hv : v ∈ subdifferential (g ∘ G) x) {w : E}
    (hw : subderivative g (G x) (fderiv ℝ G x w) = ((⟪v, w⟫_ℝ : ℝ) : EReal)) :
    ∃ y₀ ∈ multiplierSet G g x v,
      (∀ y ∈ multiplierSet G g x v, ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ ≤
        ⟪y₀, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ) ∧
      ∃ p : ℝ → E, ∃ L : EReal, Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
        Tendsto (fun τ ↦ secondDifferenceQuotient (g ∘ G) x v τ (p τ)) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
        L ≤ secondSubderivativeAt g (G x) (fderiv ℝ G x w) +
          ((⟪y₀, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal) := by
  set u := G x with hu_def
  set A := fderiv ℝ G x with hA
  set B := fderiv ℝ (fderiv ℝ G) x w w with hB
  have hfin : g u = ((g u).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (hg.ne_bot u)).symm
  have hp : IsProper g := ⟨⟨u, hx⟩, fun z ↦ lt_of_le_of_ne bot_le (hg.ne_bot z).symm⟩
  have hl : LowerSemicontinuous g := hg.lowerSemicontinuous
  have hlsc : IsLocallyLscAt g u := isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal g hl) _)
  have hr : IsSubdifferentiallyRegularAt g u := (isSubdifferentiallyRegularAt_of_convex hgc hlsc).1
  obtain ⟨hYne, -, hYcpt⟩ := multiplierSet_properties hG hl hr hQ hv
  obtain ⟨z₀, y₀, hy₀, hmax, hz₀⟩ :=
    exists_subderivative_eq_max_multiplier hg hgc hx A v B hYne hYcpt
  refine ⟨y₀, hy₀, hmax, ?_⟩
  -- second-order tangents to `C = G⁻¹(dom g)` and a parabolic arc
  set D := effectiveDomain g with hD
  have hDpoly : IsPolyhedral D := hg.isPolyhedral_effectiveDomain hgc
  have hQD : ∀ y ∈ normalCone D u, A.adjoint y = 0 → y = 0 := by
    rw [← horizonSubdifferential_eq_normalCone_domain_of_locallyLsc hgc hp hlsc hfin]
    exact hQ
  obtain ⟨hT1, hT2, -, hT4⟩ := chain_rule_for_second_order_tangents hG hDpoly.isClosed hx hQD
  have hdomh : effectiveDomain (subderivative g u) = tangentCone D u :=
    (hg.subderivative_piecewiseLinear hx).2
  have hAw : A w ∈ tangentCone D u := by
    rw [← hdomh, mem_effectiveDomain_iff, hw]; exact EReal.coe_lt_top _
  have hwC : w ∈ tangentCone (G ⁻¹' D) x := (hT1 w).2 hAw
  obtain ⟨hderiv, hT2eq⟩ := hT4 hDpoly w hwC
  have hζ₀ : A z₀ + B ∈ tangentCone D u := by
    rw [← hdomh, mem_effectiveDomain_iff, add_comm, hz₀]; exact EReal.coe_lt_top _
  have hz₀T : z₀ ∈ secondOrderTangentSet (G ⁻¹' D) x w := by
    rw [hT2, hT2eq]
    exact (hDpoly.isPolyhedral_tangentCone hx).subset_tangentCone_of_isCone
      (isCone_tangentCone hx) hAw hζ₀
  have hinner : z₀ ∈ innerSetLimitAlong (𝓝[>] (0 : ℝ)) (parabolicBlowUp (G ⁻¹' D) x w) := by
    rw [hderiv.2.1]; exact hz₀T
  obtain ⟨ε, hε, ξ, hξC, -, hξ1, hξ2⟩ :=
    (mem_innerSetLimitAlong_parabolicBlowUp_iff (show x ∈ G ⁻¹' D from hx)).1 hinner
  set z : ℝ → E := fun τ ↦ (2 / τ ^ 2) • (ξ τ - x - τ • w) with hz_def
  set p : ℝ → E := fun τ ↦ τ⁻¹ • (ξ τ - x) with hp_def
  have hξeq : ∀ τ : ℝ, τ ≠ 0 → ξ τ = x + τ • w + (τ ^ 2 / 2) • z τ := by
    intro τ hτ
    simp only [hz_def, smul_smul]
    rw [show τ ^ 2 / 2 * (2 / τ ^ 2) = 1 by field_simp, one_smul]
    abel
  have hxp : ∀ τ : ℝ, τ ≠ 0 → x + τ • p τ = ξ τ := by
    intro τ hτ
    simp only [hp_def, smul_smul, mul_inv_cancel₀ hτ, one_smul]
    abel
  have hpz : ∀ τ : ℝ, τ ≠ 0 → p τ = w + ((1 / 2 : ℝ) * τ) • z τ := by
    intro τ hτ
    simp only [hp_def]
    rw [hξeq τ hτ, show x + τ • w + (τ ^ 2 / 2) • z τ - x = τ • w + (τ ^ 2 / 2) • z τ by abel,
      smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hτ, one_smul]
    congr 2
    field_simp
  clear_value p z
  -- the map quotients `ζ_τ = Δ²_τ G(x̄)(w | z_τ) → ∇G(x̄)z̄ + ∇²G(x̄)(w, w)`
  have hζlim' := (tendsto_mapSecondDifferenceQuotient hG x w z₀).comp
    (tendsto_id.prodMk hξ2)
  obtain ⟨ζ, hζ_def⟩ : ∃ ζ : ℝ → F, ζ = fun τ ↦ mapSecondDifferenceQuotient G x w τ (z τ) :=
    ⟨_, rfl⟩
  have hζlim : Tendsto ζ (𝓝[>] (0 : ℝ)) (𝓝 (A z₀ + B)) := by
    rw [hζ_def]; exact hζlim'
  obtain ⟨U, hU_def⟩ : ∃ U : ℝ → F, U = fun τ ↦ A w + ((1 / 2 : ℝ) * τ) • ζ τ := ⟨_, rfl⟩
  have hGξ : ∀ τ : ℝ, τ ≠ 0 → G (ξ τ) = u + τ • U τ := by
    intro τ hτ
    have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
    simp only [hU_def, hζ_def, mapSecondDifferenceQuotient, smul_add, smul_smul]
    rw [show τ * (1 / 2 * τ * (2 / τ ^ 2)) = 1 by field_simp, one_smul, ← hξeq τ hτ, hu_def, hA]
    abel
  have hs : Tendsto (fun τ : ℝ ↦ (1 / 2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_const_mul_nhdsGT_zero (by norm_num)
  have hs0 : Tendsto (fun τ : ℝ ↦ (1 / 2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hs.mono_right nhdsWithin_le_nhds
  have hUlim : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 (A w)) := by
    have := tendsto_const_nhds (x := A w) |>.add (hs0.smul hζlim)
    rw [zero_smul, add_zero] at this
    rw [hU_def]; exact this
  -- the local model of `g` at `ū`
  obtain ⟨M⟩ := hg.nonempty_localModel u
  have hτU : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ * ‖U τ‖ < M.radius := by
    have h1 : Tendsto (fun τ : ℝ ↦ τ * ‖U τ‖) (𝓝[>] (0 : ℝ)) (𝓝 (0 * ‖A w‖)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul ((continuous_norm.tendsto _).comp hUlim)
    rw [zero_mul] at h1
    exact h1.eventually (gt_mem_nhds M.radius_pos)
  have hinD : ∀ᶠ τ in 𝓝[>] (0 : ℝ), G (ξ τ) ∈ D := by
    filter_upwards [Ioo_mem_nhdsGT hε] with τ hτ
    exact hξC τ ⟨hτ.1.le, hτ.2.le⟩
  have hUdom : ∀ᶠ τ in 𝓝[>] (0 : ℝ), U τ ∈ M.coneUnion := by
    filter_upwards [hτU, hinD, self_mem_nhdsWithin] with τ h1 h2 hτ'
    have hτ : (0 : ℝ) < τ := hτ'
    rw [hGξ τ (ne_of_gt hτ)] at h2
    obtain ⟨i, hi⟩ := (M.dom_iff _ (M.norm_smul_lt hτ h1)).1 h2
    exact M.mem_coneUnion.2 ⟨i, M.mem_cone_of_smul_mem hτ hi⟩
  have hAwU : A w ∈ M.coneUnion := by
    rw [← M.effectiveDomain_subderivative hg hx, hdomh]; exact hAw
  obtain ⟨j, hj⟩ := M.mem_coneUnion.1 hAwU
  have hdj := M.subderivative_eq hg hx hj
  have hvw : ⟪M.grad j, A w⟫_ℝ = ⟪v, w⟫_ℝ := by
    rw [hdj] at hw; exact_mod_cast hw
  -- the three limits
  have hd₁ : IsPiecewiseLinearQuadratic (subderivative g u) :=
    (hg.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic
  have hAw₁ : A w ∈ effectiveDomain (subderivative g u) := by rw [hdomh]; exact hAw
  obtain ⟨M₁⟩ := hd₁.nonempty_localModel (A w)
  have L₁ := M₁.tendsto_differenceQuotient_of_mem_dom hd₁ hAw₁ hs hζlim (by
    filter_upwards [hUdom] with τ hτ
    rw [hU_def] at hτ
    rw [M.effectiveDomain_subderivative hg hx]; exact hτ)
  have hq := M.isPiecewiseLinearQuadratic_secondForm hg hx
  have hdomq : effectiveDomain M.secondForm = M.coneUnion := M.effectiveDomain_secondForm hg hx
  have L₂ : Tendsto (fun τ ↦ M.secondForm (U τ)) (𝓝[>] (0 : ℝ)) (𝓝 (M.secondForm (A w))) :=
    (hq.continuousOn (A w) (by rw [hdomq]; exact hAwU)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hUlim, by rw [hdomq]; exact hUdom⟩)
  have L₃ : Tendsto (fun τ ↦ ((⟪v, z τ⟫_ℝ : ℝ) : EReal)) (𝓝[>] (0 : ℝ))
      (𝓝 ((⟪v, z₀⟫_ℝ : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp ((continuous_const.inner continuous_id).tendsto
      z₀ |>.comp hξ2)
  have hq₀ := M.secondForm_eq hg hx hj
  have hne : M.secondForm (A w) ≠ ⊥ ∧ M.secondForm (A w) ≠ ⊤ := by
    rw [hq₀]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  have hsum := (EReal.continuousAt_add (Or.inr hne.1) (Or.inr hne.2)).tendsto.comp
    (L₁.prodMk_nhds L₂)
  have hsub := (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (-⟪v, z₀⟫_ℝ)))
    (Or.inr (EReal.coe_ne_top (-⟪v, z₀⟫_ℝ)))).tendsto.comp (hsum.prodMk_nhds
      ((continuous_coe_real_ereal.tendsto _).comp ((continuous_const.inner continuous_id).tendsto
        z₀ |>.comp hξ2 |>.neg)))
  have hsub' : Tendsto (fun τ ↦ differenceQuotient (subderivative g u) (A w) ((1 / 2 : ℝ) * τ)
      (ζ τ) + M.secondForm (U τ) + ((-⟪v, z τ⟫_ℝ : ℝ) : EReal)) (𝓝[>] (0 : ℝ))
      (𝓝 (subderivative (subderivative g u) (A w) (A z₀ + B) + M.secondForm (A w) +
        ((-⟪v, z₀⟫_ℝ : ℝ) : EReal))) := by
    simpa only [Function.comp_def, id] using hsub
  refine ⟨p, _, hξ1, hsub'.congr' ?_, ?_⟩
  · -- the eventual identity of quotients
    filter_upwards [hτU, hUdom, self_mem_nhdsWithin] with τ h1 h2 hτ
    have hτ' : (0 : ℝ) < τ := hτ
    obtain ⟨i, hi⟩ := M.mem_coneUnion.1 h2
    have hexp := M.eq_expansion hi hτ' h1
    have hbase : (M.piece i).eval u = (M.piece j).eval u := by
      have := (M.eq_eval_base ⟨_, hi⟩).symm.trans (M.eq_eval_base ⟨_, hj⟩)
      exact_mod_cast this
    have hfx : (g ∘ G) x = (((M.piece j).eval u : ℝ) : EReal) := M.eq_eval_base ⟨_, hj⟩
    have hfp : (g ∘ G) (x + τ • p τ) = (((M.piece i).eval u + τ * ⟪M.grad i, U τ⟫_ℝ +
        τ ^ 2 / 2 * ⟪U τ, (M.piece i).matrix (U τ)⟫_ℝ : ℝ) : EReal) := by
      simp only [Function.comp_apply]
      rw [hxp τ (ne_of_gt hτ'), hGξ τ (ne_of_gt hτ')]
      exact hexp
    have hdU : subderivative g u (A w + ((1 / 2 : ℝ) * τ) • ζ τ) =
        ((⟪M.grad i, U τ⟫_ℝ : ℝ) : EReal) := by
      rw [show A w + ((1 / 2 : ℝ) * τ) • ζ τ = U τ by rw [hU_def]]
      exact M.subderivative_eq hg hx hi
    rw [secondDifferenceQuotient_of_coe hfx hfp, differenceQuotient_eq_coe hdj hdU,
      M.secondForm_eq hg hx hi]
    norm_cast
    rw [hpz τ (ne_of_gt hτ'), inner_add_right, real_inner_smul_right, hbase, hvw]
    generalize ⟪M.grad i, U τ⟫_ℝ = a₁
    generalize ⟪U τ, (M.piece i).matrix (U τ)⟫_ℝ = q₁
    field_simp
    ring
  · -- the bound through `dh₁(∇G(x̄)w)(ζ̄) ≤ h₁(ζ̄) = ⟪y₀, B⟫ + ⟪v, z̄⟫`
    have hsl : Sublinear (subderivative g u) := by
      rw [hg.subderivative_eq_support hgc hx]; exact sublinear_supportFunction _
    have hle := subderivative_le_of_sublinear hsl hdj (A z₀ + B)
    have hz₀' : subderivative g u (A z₀ + B) = ((⟪y₀, B⟫_ℝ + ⟪v, z₀⟫_ℝ : ℝ) : EReal) := by
      rw [add_comm]; exact hz₀
    rw [hz₀'] at hle
    rw [M.secondSubderivativeAt_eq hg hx, hq₀]
    rcases ereal_trichotomy (subderivative (subderivative g u) (A w) (A z₀ + B)) with
      h' | h' | ⟨r, h'⟩
    · rw [h', EReal.bot_add, EReal.bot_add]; exact bot_le
    · rw [h'] at hle; exact absurd hle (not_le.2 (EReal.coe_lt_top _))
    · rw [h'] at hle ⊢
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      rw [EReal.coe_le_coe_iff] at hle
      linarith

/-! ### Theorem 13.14 for convex piecewise linear-quadratic `g` -/

/-- **Theorem 13.14** for convex piecewise linear-quadratic `g`: with `ū = G(x̄)`,
`f̄(z) = g(ū + ∇G(x̄)(z - x̄))` and `v ∈ ∂f(x̄)` for `f = g ∘ G`,

* `d²f(x̄ | v)(w) = sup_{y ∈ Y(x̄,v)} [d²g(ū | y)(∇G(x̄)w) + ⟪w, ∇²(yG)(x̄)w⟫]`, and this is formula
  13(19): `d²f(x̄ | v)(w) = d²f̄(x̄ | v)(w) + max_{y ∈ Y(x̄,v)} ⟪y, ∇²G(x̄)(w, w)⟫`, the maximum
  being attained;
* `d²f̄(x̄ | v)(w) = d²g(ū | y)(∇G(x̄)w)` for every `y ∈ Y(x̄, v)`, which is `d²g(ū)(∇G(x̄)w)` when
  `dg(ū)(∇G(x̄)w) = ⟪v, w⟫` and `∞` otherwise;
* `f` is properly twice epi-differentiable at `x̄` for `v`, with
  `dom d²f(x̄ | v) = {w | df(x̄)(w) = ⟪v, w⟫}`. -/
theorem chain_rule_second_subderivatives_plq {G : E → F} (hG : ContDiff ℝ 2 G) {g : F → EReal}
    (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} (hv : v ∈ subdifferential (g ∘ G) x) :
    (∀ w, secondSubderivative (g ∘ G) x v w = ⨆ y ∈ multiplierSet G g x v,
        (secondSubderivative g (G x) y (fderiv ℝ G x w) +
          ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal))) ∧
    (∀ w, ∃ y₀ ∈ multiplierSet G g x v,
      (∀ y ∈ multiplierSet G g x v, ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ ≤
        ⟪y₀, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ) ∧
      secondSubderivative (g ∘ G) x v w =
        secondSubderivative (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x v w +
          ((⟪y₀, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal)) ∧
    (∀ w, ∀ y ∈ multiplierSet G g x v,
      secondSubderivative (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x v w =
        secondSubderivative g (G x) y (fderiv ℝ G x w)) ∧
    (∀ w, secondSubderivative (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x v w =
      if subderivative g (G x) (fderiv ℝ G x w) = ((⟪v, w⟫_ℝ : ℝ) : EReal) then
        secondSubderivativeAt g (G x) (fderiv ℝ G x w) else ⊤) ∧
    ProperlyTwiceEpiDifferentiableAt (g ∘ G) x v ∧
    effectiveDomain (secondSubderivative (g ∘ G) x v) =
      {w | subderivative (g ∘ G) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} := by
  set u := G x with hu_def
  set A := fderiv ℝ G x with hA
  have hfin : g u = ((g u).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (hg.ne_bot u)).symm
  have hp : IsProper g := ⟨⟨u, hx⟩, fun z ↦ lt_of_le_of_ne bot_le (hg.ne_bot z).symm⟩
  have hl : LowerSemicontinuous g := hg.lowerSemicontinuous
  have hlsc : IsLocallyLscAt g u := isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal g hl) _)
  have hr : IsSubdifferentiallyRegularAt g u := (isSubdifferentiallyRegularAt_of_convex hgc hlsc).1
  obtain ⟨hYne, -, hYcpt⟩ := multiplierSet_properties hG hl hr hQ hv
  obtain ⟨M⟩ := hg.nonempty_localModel u
  set fbar : E → EReal := fun z ↦ g (u + A (z - x)) with hfbar
  -- `d²f̄(x̄ | v)(w) = d²g(ū | y)(Aw)`
  have hbar : ∀ w, ∀ y ∈ multiplierSet G g x v,
      secondSubderivative fbar x v w = secondSubderivative g u y (A w) :=
    fun w y hy ↦ secondSubderivative_comp_affine hg hgc hx A hy.1 hy.2 w
  obtain ⟨y₀, hy₀⟩ := hYne
  have hbar2 : ∀ w, secondSubderivative fbar x v w =
      if subderivative g u (A w) = ((⟪v, w⟫_ℝ : ℝ) : EReal) then secondSubderivativeAt g u (A w)
      else ⊤ := by
    intro w
    have hv₀ := inner_le_subderivative_of_convex hp hgc hfin hy₀.1
    have hinner : ⟪y₀, A w⟫_ℝ = ⟪v, w⟫_ℝ := by
      rw [← hy₀.2, ContinuousLinearMap.adjoint_inner_left]
    rw [hbar w y₀ hy₀, M.secondSubderivative_eq hg hx hv₀, hinner, M.secondSubderivativeAt_eq hg hx]
  have hbar_ne_bot : ∀ w, secondSubderivative fbar x v w ≠ ⊥ := by
    intro w
    rw [hbar2]
    split_ifs
    · rw [M.secondSubderivativeAt_eq hg hx]; exact M.secondForm_ne_bot _
    · exact top_ne_bot
  -- the maximizers of `⟪·, ∇²G(x̄)(w, w)⟫` on `Y`
  have hmaxex : ∀ w, ∃ y₁ ∈ multiplierSet G g x v, ∀ y ∈ multiplierSet G g x v,
      ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ ≤ ⟪y₁, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ := by
    intro w
    obtain ⟨y₁, hy₁, hmax⟩ := hYcpt.exists_isMaxOn ⟨y₀, hy₀⟩
      (show ContinuousOn (fun y : F ↦ ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ) _ from
        (continuous_id.inner continuous_const).continuousOn)
    exact ⟨y₁, hy₁, fun y hy ↦ hmax hy⟩
  -- the main equality, with the attaining path when finite
  have hmain : ∀ w, ∀ y₁ ∈ multiplierSet G g x v, (∀ y ∈ multiplierSet G g x v,
      ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ ≤ ⟪y₁, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ) →
      secondSubderivative (g ∘ G) x v w = secondSubderivative fbar x v w +
        ((⟪y₁, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal) ∧
      (secondSubderivative (g ∘ G) x v w < ⊤ → ∃ p : ℝ → E, Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
        Tendsto (fun τ ↦ secondDifferenceQuotient (g ∘ G) x v τ (p τ)) (𝓝[>] (0 : ℝ))
          (𝓝 (secondSubderivative (g ∘ G) x v w))) := by
    intro w y₁ hy₁ hmax₁
    have hge : secondSubderivative fbar x v w + ((⟪y₁, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) :
        EReal) ≤ secondSubderivative (g ∘ G) x v w := by
      rw [hbar w y₁ hy₁]
      exact secondSubderivative_comp_ge hG hfin hy₁.2 w
    by_cases hK : subderivative g u (A w) = ((⟪v, w⟫_ℝ : ℝ) : EReal)
    · obtain ⟨y₂, hy₂, -, p, L, hp, hL, hLle⟩ :=
        exists_path_secondDifferenceQuotient_comp hG hg hgc hx hQ hv hK
      have hy₂₁ : ⟪y₂, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ ≤ ⟪y₁, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ :=
        hmax₁ y₂ hy₂
      have hLle' : L ≤ secondSubderivative fbar x v w +
          ((⟪y₁, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal) := by
        rw [hbar2, if_pos hK]
        exact hLle.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 hy₂₁))
      have hpath : Tendsto (fun τ : ℝ ↦ (τ, p τ)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
        tendsto_id.prodMk hp
      have hleL : secondSubderivative (g ∘ G) x v w ≤ L := by
        calc secondSubderivative (g ∘ G) x v w
            ≤ liminf ((fun q : ℝ × E ↦ secondDifferenceQuotient (g ∘ G) x v q.1 q.2) ∘
                fun τ : ℝ ↦ (τ, p τ)) (𝓝[>] (0 : ℝ)) := by
              rw [secondSubderivative, liminf_comp]
              exact liminf_le_liminf_of_le hpath
          _ = L := hL.liminf_eq
      have heq : secondSubderivative (g ∘ G) x v w = secondSubderivative fbar x v w +
          ((⟪y₁, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal) :=
        le_antisymm (hleL.trans hLle') hge
      refine ⟨heq, fun _ ↦ ⟨p, hp, ?_⟩⟩
      have hLeq : L = secondSubderivative (g ∘ G) x v w :=
        le_antisymm (hLle'.trans_eq heq.symm) hleL
      rwa [← hLeq]
    · have htop : secondSubderivative fbar x v w = ⊤ := by rw [hbar2, if_neg hK]
      rw [htop, EReal.top_add_coe, top_le_iff] at hge
      refine ⟨by rw [htop, EReal.top_add_coe, hge], fun h ↦ absurd hge (ne_of_lt h)⟩
  have hsup : ∀ w, secondSubderivative (g ∘ G) x v w = ⨆ y ∈ multiplierSet G g x v,
      (secondSubderivative g u y (A w) + ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal)) := by
    intro w
    obtain ⟨y₁, hy₁, hmax₁⟩ := hmaxex w
    rw [(hmain w y₁ hy₁ hmax₁).1]
    refine le_antisymm ?_ (iSup₂_le fun y hy ↦ ?_)
    · refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun y _ ↦ secondSubderivative g u y (A w) +
        ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal)) y₁ hy₁)
      rw [hbar w y₁ hy₁]
    · rw [← hbar w y hy]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (hmax₁ y hy))
  have hdf : ∀ w, subderivative (g ∘ G) x w = subderivative g u (A w) :=
    subderivative_comp_eq_of_regular (hG.of_le (by norm_num)) hl hr hQ
  refine ⟨hsup, fun w ↦ ?_, hbar, hbar2, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨y₁, hy₁, hmax₁⟩ := hmaxex w
    exact ⟨y₁, hy₁, hmax₁, (hmain w y₁ hy₁ hmax₁).1⟩
  · -- twice epi-differentiability
    rw [twiceEpiDifferentiableAt_iff_subset]
    refine ⟨by simp only [Function.comp_apply]; rw [hfin]; exact EReal.coe_ne_bot _,
      by simp only [Function.comp_apply]; rw [hfin]; exact EReal.coe_ne_top _, ?_⟩
    refine epigraph_subset_innerSetLimitAlong_of_paths fun w hw ↦ ?_
    obtain ⟨y₁, hy₁, hmax₁⟩ := hmaxex w
    exact (hmain w y₁ hy₁ hmax₁).2 hw
  · -- properness
    have hd0 : subderivative g u 0 = 0 := by
      rcases subderivative_zero_eq_zero_or_bot hfin with h | h
      · exact h
      · exact absurd h ((hg.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic.ne_bot 0)
    obtain ⟨y₁, hy₁, hmax₁⟩ := hmaxex 0
    have h0 := (hmain 0 y₁ hy₁ hmax₁).1
    have hF0 : secondSubderivative fbar x v 0 = 0 := by
      rw [hbar2, map_zero, hd0, inner_zero_right, EReal.coe_zero, if_pos rfl,
        M.secondSubderivativeAt_eq hg hx, M.secondForm_zero hg hx]
    have hB0 : fderiv ℝ (fderiv ℝ G) x 0 0 = 0 := by simp
    rw [hF0, hB0, inner_zero_right, EReal.coe_zero, add_zero] at h0
    rw [isProper_iff]
    refine ⟨⟨0, by rw [mem_effectiveDomain_iff, h0]; exact EReal.zero_lt_top⟩, fun w ↦ ?_⟩
    obtain ⟨y₁, hy₁, hmax₁⟩ := hmaxex w
    rw [(hmain w y₁ hy₁ hmax₁).1]
    rcases ereal_trichotomy (secondSubderivative fbar x v w) with h | h | ⟨r, h⟩
    · exact absurd h (hbar_ne_bot w)
    · rw [h, EReal.top_add_coe]; exact bot_lt_top
    · rw [h, ← EReal.coe_add]; exact EReal.bot_lt_coe _
  · -- the domain
    ext w
    rw [mem_effectiveDomain_iff, mem_setOf_eq, hdf]
    obtain ⟨y₁, hy₁, hmax₁⟩ := hmaxex w
    rw [(hmain w y₁ hy₁ hmax₁).1, hbar2]
    split_ifs with hK
    · simp only [hK, iff_true]
      rw [M.secondSubderivativeAt_eq hg hx]
      have hAw : A w ∈ M.coneUnion := by
        by_contra hn
        rw [M.subderivative_eq_top hg hx hn] at hK
        exact absurd hK.symm (EReal.coe_ne_top _)
      obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hAw
      rw [M.secondForm_eq hg hx hi, ← EReal.coe_add]
      exact EReal.coe_lt_top _
    · simp only [EReal.top_add_coe, lt_irrefl, hK]

/-! ### Localization and second-order chain identities -/

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- Along `τ ↓ 0` with bounded directions, the points `x̄ + τw'` eventually lie in any
neighborhood of `x̄`. -/
theorem eventually_add_smul_mem_of_mem_nhds {x : E} {U : Set E} (hU : U ∈ 𝓝 x) (w : E) :
    ∀ᶠ p : ℝ × E in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, x + p.1 • p.2 ∈ U := by
  have h : Tendsto (fun p : ℝ × E ↦ x + p.1 • p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (x + (0 : ℝ) • w)) :=
    tendsto_const_nhds.add (((tendsto_id.mono_left nhdsWithin_le_nhds).comp tendsto_fst).smul
      tendsto_snd)
  rw [zero_smul, add_zero] at h
  exact h.eventually hU

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- Second subderivatives only depend on the function near `x̄`. -/
theorem secondSubderivative_congr_nhds {f₁ f₂ : E → EReal} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂)
    (v w : E) : secondSubderivative f₁ x v w = secondSubderivative f₂ x v w := by
  refine liminf_congr ?_
  filter_upwards [eventually_add_smul_mem_of_mem_nhds h w] with p hp
  simp only [secondDifferenceQuotient, hp, h.self_of_nhds]

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- Twice epi-differentiability only depends on the function near `x̄`. -/
theorem TwiceEpiDifferentiableAt.congr_nhds {f₁ f₂ : E → EReal} {x v : E} (h : f₁ =ᶠ[𝓝 x] f₂)
    (h₂ : TwiceEpiDifferentiableAt f₂ x v) : TwiceEpiDifferentiableAt f₁ x v := by
  rw [twiceEpiDifferentiableAt_iff_subset] at h₂ ⊢
  obtain ⟨h1, h2, hsub⟩ := h₂
  have hx : f₁ x = f₂ x := h.self_of_nhds
  refine ⟨hx ▸ h1, hx ▸ h2, ?_⟩
  have hd : secondSubderivative f₁ x v = secondSubderivative f₂ x v :=
    funext fun w ↦ secondSubderivative_congr_nhds h v w
  rw [hd]
  intro q hq N hN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (h : {y | f₁ y = f₂ y} ∈ 𝓝 x)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
  have hpos : 0 < δ / (‖q.1‖ + r + 1) := by positivity
  filter_upwards [hsub hq (ball q r) (ball_mem_nhds q hr), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hpos)] with τ ⟨p, hp, hpq⟩ hτ hτδ
  have hτ' : (0 : ℝ) < τ := hτ
  refine ⟨p, ?_, hrN hpq⟩
  have hp1 : ‖p.1‖ < ‖q.1‖ + r := by
    have h1 : dist p.1 q.1 < r :=
      lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) (mem_ball.1 hpq)
    have h2 := norm_le_norm_add_norm_sub' p.1 q.1
    rw [dist_eq_norm] at h1
    linarith
  have hmem : x + τ • p.1 ∈ {y | f₁ y = f₂ y} := by
    refine hball ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ'.le]
    have hτδ' : τ * (‖q.1‖ + r + 1) < δ := by
      rw [mem_Iio, lt_div_iff₀ (by positivity)] at hτδ; exact hτδ
    nlinarith [norm_nonneg p.1]
  show (p.2 : EReal) ≥ secondDifferenceQuotient f₁ x v τ p.1
  have heq : secondDifferenceQuotient f₁ x v τ p.1 = secondDifferenceQuotient f₂ x v τ p.1 := by
    simp only [secondDifferenceQuotient, hx, show f₁ (x + τ • p.1) = f₂ (x + τ • p.1) from hmem]
  rw [heq]
  exact hp

/-- The second-order chain identity
`∇²(H ∘ G)(x̄)(w, w) = ∇H(ū)(∇²G(x̄)(w, w)) + ∇²H(ū)(∇G(x̄)w, ∇G(x̄)w)` for `C²` mappings, obtained by
uniqueness of the limits of the second-order quotients. -/
theorem fderiv_fderiv_comp_apply {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] {H : F → P} {G : E → F} (hH : ContDiff ℝ 2 H) (hG : ContDiff ℝ 2 G)
    (x w : E) :
    fderiv ℝ (fderiv ℝ (H ∘ G)) x w w = fderiv ℝ H (G x) (fderiv ℝ (fderiv ℝ G) x w w) +
      fderiv ℝ (fderiv ℝ H) (G x) (fderiv ℝ G x w) (fderiv ℝ G x w) := by
  have hHG : ContDiff ℝ 2 (H ∘ G) := hH.comp hG
  have hdH : DifferentiableAt ℝ H (G x) := hH.differentiable (by norm_num) _
  have hdG : DifferentiableAt ℝ G x := hG.differentiable (by norm_num) _
  have hchain : fderiv ℝ (H ∘ G) x = (fderiv ℝ H (G x)).comp (fderiv ℝ G x) :=
    fderiv_comp x hdH hdG
  -- the quotients of `H ∘ G` along the ray `w`
  have hray : Tendsto (fun τ : ℝ ↦ (τ, (0 : E))) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) :=
    tendsto_id.prodMk tendsto_const_nhds
  have h1 := (tendsto_mapSecondDifferenceQuotient hHG x w 0).comp hray
  rw [map_zero, zero_add] at h1
  -- the quotients of `G` along the ray `w` and those of `H` along the induced parabolas
  have h2 := (tendsto_mapSecondDifferenceQuotient hG x w 0).comp hray
  rw [map_zero, zero_add] at h2
  have h3 := (tendsto_mapSecondDifferenceQuotient hH (G x) (fderiv ℝ G x w)
    (fderiv ℝ (fderiv ℝ G) x w w)).comp (tendsto_id.prodMk h2)
  refine tendsto_nhds_unique h1 (h3.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ' : τ ≠ 0 := ne_of_gt hτ
  have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ'
  simp only [Function.comp_apply, id, mapSecondDifferenceQuotient, smul_zero, add_zero]
  have hG' : G x + τ • fderiv ℝ G x w + (τ ^ 2 / 2) • ((2 / τ ^ 2) • (G (x + τ • w) - G x -
      τ • fderiv ℝ G x w)) = G (x + τ • w) := by
    rw [smul_smul, show τ ^ 2 / 2 * (2 / τ ^ 2) = 1 by field_simp, one_smul]
    abel
  rw [hG', hchain, ContinuousLinearMap.comp_apply]

end RW
