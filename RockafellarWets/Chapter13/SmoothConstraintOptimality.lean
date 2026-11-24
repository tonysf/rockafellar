/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order optimality with smooth constraints

Example 13.25.  We minimize `f₀` over `C = {x ∈ X | F(x) ∈ D}` with `f₀`, `F` of class `C²` and
`X`, `D` polyhedral.  As in the detail, Theorem 13.24 is applied to `f = δ_C + f₀`, whose second
subderivatives come from Exercise 13.17 (`indicators_and_geometry`) with the help of 13.18.  The
quadratic form `⟪w, ∇²ₓₓ[f₀ + yF](x̄)w⟫` is the second derivative of the Lagrangian
`x ↦ f₀(x) + ⟪y, F(x)⟫` at `x̄` in the direction `w`, which is
`∇²f₀(x̄)(w, w) + ⟪y, ∇²F(x̄)(w, w)⟫` (`fderiv_fderiv_lagrangian_apply`).
-/

import RockafellarWets.Chapter13.IndicatorSecondOrder
import RockafellarWets.Chapter13.SmoothAddition
import RockafellarWets.Chapter13.SecondOrderOptimality

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The second derivative of the Lagrangian `x ↦ f₀(x) + ⟪y, F(x)⟫`:
`⟪w, ∇²ₓₓ[f₀ + yF](x̄)w⟫ = ∇²f₀(x̄)(w, w) + ⟪y, ∇²F(x̄)(w, w)⟫`. -/
theorem fderiv_fderiv_lagrangian_apply {f₀ : E → ℝ} (hf₀ : ContDiff ℝ 2 f₀) {F : E → P}
    (hF : ContDiff ℝ 2 F) (y : P) (x w : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ)) x w w =
      fderiv ℝ (fderiv ℝ f₀) x w w + ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ := by
  set H : P → ℝ := ⇑(innerSL ℝ y) with hHdef
  have hH : ContDiff ℝ 2 H := (innerSL ℝ y).contDiff
  have hg : ContDiff ℝ 2 (H ∘ F) := hH.comp hF
  have hfun : (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ) = fun z ↦ f₀ z + (H ∘ F) z := by
    funext z
    simp [hHdef]
  have h1 : fderiv ℝ (fun z ↦ f₀ z + (H ∘ F) z) =
      fun z ↦ fderiv ℝ f₀ z + fderiv ℝ (H ∘ F) z := by
    funext z
    exact fderiv_add (hf₀.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hd₀ : DifferentiableAt ℝ (fderiv ℝ f₀) x :=
    (hf₀.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hdg : DifferentiableAt ℝ (fderiv ℝ (H ∘ F)) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hHd : fderiv ℝ H = fun _ ↦ innerSL ℝ y := funext fun u ↦ (innerSL ℝ y).fderiv
  have hHdd : fderiv ℝ (fderiv ℝ H) (F x) = 0 := by
    rw [hHd]
    exact fderiv_const_apply _
  have h2 : fderiv ℝ (fun z ↦ fderiv ℝ f₀ z + fderiv ℝ (H ∘ F) z) x =
      fderiv ℝ (fderiv ℝ f₀) x + fderiv ℝ (fderiv ℝ (H ∘ F)) x := fderiv_add hd₀ hdg
  rw [hfun, h1, h2, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    fderiv_fderiv_comp_apply hH hF, hHdd, hHd]
  simp

/-- **Example 13.25** (second-order optimality with smooth constraints).  Let `f₀ : ℝⁿ → ℝ` and
`F : ℝⁿ → ℝᵐ` be of class `C²`, `X`, `D` polyhedral, and `x̄ ∈ C = {x ∈ X | F(x) ∈ D}` with the
qualification `y ∈ N_D(F(x̄)), -∇F(x̄)* y ∈ N_X(x̄) ⇒ y = 0`.  With
`Y(x̄) = {y ∈ N_D(F(x̄)) | -[∇f₀(x̄) + ∇F(x̄)* y] ∈ N_X(x̄)}` and
`K(x̄) = {w ∈ T_X(x̄) | ∇F(x̄)w ∈ T_D(F(x̄)), w ⊥ ∇f₀(x̄)}`: `Y(x̄)` is polyhedral and compact,
`K(x̄)` is a polyhedral cone, and
(a) if `x̄` is locally optimal, then `Y(x̄) ≠ ∅` and for every `w ∈ K(x̄)` the maximum over
`y ∈ Y(x̄)` of `⟪w, ∇²ₓₓ[f₀ + yF](x̄)w⟫` is attained and nonnegative;
(b) conversely, if `Y(x̄) ≠ ∅` and the maximum is positive for every `w ∈ K(x̄) \ {0}`, then
`x̄` is locally optimal, with `f₀(x) ≥ f₀(x̄) + ε‖x - x̄‖²` for `x ∈ C`, `‖x - x̄‖ ≤ δ`. -/
theorem second_order_optimality_with_smooth_constraints {X : Set E} {D : Set P}
    (hX : IsPolyhedral X) (hD : IsPolyhedral D) {f₀ : E → ℝ} (hf₀ : ContDiff ℝ 2 f₀)
    {F : E → P} (hF : ContDiff ℝ 2 F) {x : E} (hxX : x ∈ X) (hFx : F x ∈ D)
    (hQ : ∀ y ∈ normalCone D (F x), -((fderiv ℝ F x).adjoint y) ∈ normalCone X x → y = 0) :
    IsPolyhedral {y | y ∈ normalCone D (F x) ∧
        -(gradient f₀ x + (fderiv ℝ F x).adjoint y) ∈ normalCone X x} ∧
    IsCompact {y | y ∈ normalCone D (F x) ∧
        -(gradient f₀ x + (fderiv ℝ F x).adjoint y) ∈ normalCone X x} ∧
    IsPolyhedral {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧
        ⟪w, gradient f₀ x⟫_ℝ = 0} ∧
    IsCone {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧
        ⟪w, gradient f₀ x⟫_ℝ = 0} ∧
    (IsLocalMinOn f₀ {z | z ∈ X ∧ F z ∈ D} x →
      {y | y ∈ normalCone D (F x) ∧
        -(gradient f₀ x + (fderiv ℝ F x).adjoint y) ∈ normalCone X x}.Nonempty ∧
      ∀ w ∈ {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧
          ⟪w, gradient f₀ x⟫_ℝ = 0},
        ∃ y₀ ∈ {y | y ∈ normalCone D (F x) ∧
            -(gradient f₀ x + (fderiv ℝ F x).adjoint y) ∈ normalCone X x},
          (∀ y ∈ {y | y ∈ normalCone D (F x) ∧
              -(gradient f₀ x + (fderiv ℝ F x).adjoint y) ∈ normalCone X x},
            fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ)) x w w ≤
              fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y₀, F z⟫_ℝ)) x w w) ∧
          0 ≤ fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y₀, F z⟫_ℝ)) x w w) ∧
    ({y | y ∈ normalCone D (F x) ∧
        -(gradient f₀ x + (fderiv ℝ F x).adjoint y) ∈ normalCone X x}.Nonempty →
      (∀ w ∈ {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧
          ⟪w, gradient f₀ x⟫_ℝ = 0}, w ≠ 0 →
        ∃ y ∈ {y | y ∈ normalCone D (F x) ∧
            -(gradient f₀ x + (fderiv ℝ F x).adjoint y) ∈ normalCone X x},
          0 < fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ)) x w w) →
      IsLocalMinOn f₀ {z | z ∈ X ∧ F z ∈ D} x ∧
      ∃ ε > 0, ∃ δ > 0, ∀ z ∈ {z | z ∈ X ∧ F z ∈ D}, ‖z - x‖ ≤ δ →
        f₀ x + ε * ‖z - x‖ ^ 2 ≤ f₀ z) := by
  set C := {z | z ∈ X ∧ F z ∈ D} with hC
  set g := gradient f₀ x with hg
  set Y := {y | y ∈ normalCone D (F x) ∧
    -(g + (fderiv ℝ F x).adjoint y) ∈ normalCone X x} with hY
  set K := {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧
    ⟪w, g⟫_ℝ = 0} with hK
  obtain ⟨hchar, hsec⟩ := indicators_and_geometry hX hD hF hxX hFx hQ
  have hxC : x ∈ C := ⟨hxX, hFx⟩
  have hYeq : Y = {y | y ∈ normalCone D (F x) ∧
      -g - (fderiv ℝ F x).adjoint y ∈ normalCone X x} := by
    ext y
    simp only [hY, mem_setOf_eq, neg_add']
  have hKeq : K = {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧
      ⟪w, -g⟫_ℝ = 0} := by
    ext w
    simp only [hK, mem_setOf_eq, inner_neg_right, neg_eq_zero]
  have hmemY : ∀ y ∈ Y, -g ∈ normalCone C x := fun y hy ↦
    (hchar (-g)).2 ⟨y, hy.1, by rw [← neg_add']; exact hy.2⟩
  -- the Hessian of the Lagrangian
  have hlag : ∀ y w, fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ)) x w w =
      fderiv ℝ (fderiv ℝ f₀) x w w + ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ :=
    fun y w ↦ fderiv_fderiv_lagrangian_apply hf₀ hF y x w
  -- the objective `f = δ_C + f₀`
  set f : E → EReal := fun z ↦ indicatorVA C z + (f₀ z : EReal) with hf
  have hδx : indicatorVA C x = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem hxC, EReal.coe_zero]
  have hfx : f x = ((f₀ x : ℝ) : EReal) := by
    simp only [hf, hδx, EReal.coe_zero, zero_add]
  have hd2 : -g ∈ normalCone C x → ∀ w, secondSubderivative f x 0 w =
      indicatorVA K w + (⨆ y ∈ Y, ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) +
        ((fderiv ℝ (fderiv ℝ f₀) x w w : ℝ) : EReal) := by
    intro hv w
    have h : secondSubderivative f x (-g + g) w = secondSubderivative (indicatorVA C) x (-g) w +
        ((fderiv ℝ (fderiv ℝ f₀) x w w : ℝ) : EReal) :=
      secondSubderivative_add_smooth
        (Eventually.of_forall (hasFDerivAt_fderiv_of_contDiff_two hf₀))
        (hasFDerivAt_fderiv_fderiv_of_contDiff_two hf₀ x) (fderiv_apply_eq_inner_gradient f₀ x)
        hδx w
    rw [neg_add_cancel] at h
    rw [h, (hsec (-g) hv).2.1 w, ← hKeq, ← hYeq]
  have hmax : -g ∈ normalCone C x → ∀ w, ∃ y₀ ∈ Y, ∀ y ∈ Y,
      ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ ≤ ⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ := by
    intro hv w
    rw [hYeq]
    exact (hsec (-g) hv).2.2.1 w
  have hsup_eq : ∀ w, ∀ y₀ ∈ Y, (∀ y ∈ Y,
      ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ ≤ ⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ) →
      (⨆ y ∈ Y, ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) =
        ((⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal) := fun w y₀ hy₀ hm ↦
    le_antisymm (iSup₂_le fun y hy ↦ EReal.coe_le_coe_iff.2 (hm y hy))
      (le_iSup₂ (f := fun y _ ↦ ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) y₀ hy₀)
  -- polyhedrality and compactness of `Y(x̄)`, and the cone `K(x̄)`
  have hYpoly : IsPolyhedral Y := by
    have hNX := hX.isPolyhedral_normalCone hxX
    have hND := hD.isPolyhedral_normalCone hFx
    let φ : E →ᵃ[ℝ] E := ⟨fun n ↦ -n - g, -LinearMap.id, fun p v ↦ by
      simp only [vadd_eq_add, LinearMap.neg_apply, LinearMap.id_apply]
      abel⟩
    have hφ : φ '' normalCone X x = {u | -(g + u) ∈ normalCone X x} := by
      ext u
      constructor
      · rintro ⟨n, hn, rfl⟩
        have : -(g + (-n - g)) = n := by abel
        change -(g + (-n - g)) ∈ normalCone X x
        rw [this]
        exact hn
      · intro hu
        refine ⟨-(g + u), hu, ?_⟩
        change -(-(g + u)) - g = u
        abel
    have h2 : IsPolyhedral ((fderiv ℝ F x).adjoint ⁻¹' (φ '' normalCone X x)) :=
      (hNX.affine_image φ).continuousLinear_preimage _
    rw [hφ] at h2
    exact hND.inter h2
  have hYcpt : IsCompact Y := by
    by_cases hv : -g ∈ normalCone C x
    · rw [hYeq]
      exact (hsec (-g) hv).2.2.2.2.2
    · rw [Set.eq_empty_of_forall_notMem fun y hy ↦ hv (hmemY y hy)]
      exact isCompact_empty
  refine ⟨hYpoly, hYcpt,
    isPolyhedral_setOf_tangentCone_inner_eq_zero hX hD hxX hFx (fderiv ℝ F x) g,
    isCone_setOf_tangentCone_inner_eq_zero hxX hFx (fderiv ℝ F x) g, ?_, ?_⟩
  · -- (a) necessity
    intro hmin
    have hlm : IsLocalMin f x := by
      have h := hmin
      rw [IsLocalMinOn, IsMinFilter, eventually_nhdsWithin_iff] at h
      filter_upwards [h] with z hz
      rw [hfx]
      by_cases hzC : z ∈ C
      · simp only [hf, indicatorVA_apply_mem hzC, zero_add]
        exact EReal.coe_le_coe_iff.2 (hz hzC)
      · simp only [hf, indicatorVA_apply_not_mem hzC, EReal.top_add_coe]
        exact le_top
    obtain ⟨h0, h2⟩ := RW.IsLocalMin.secondOrder_necessary hlm hfx
    have hv : -g ∈ normalCone C x := by
      have h0' := (zero_mem_subdifferential_add_smooth_iff hδx
        (hf₀.contDiffAt.of_le (by norm_num))).1
        (regularSubdifferential_subset_subdifferential f x h0)
      rw [subdifferential_indicatorVA] at h0'
      exact h0'
    obtain ⟨y, hy, hxy⟩ := (hchar (-g)).1 hv
    refine ⟨⟨y, hy, by rw [neg_add']; exact hxy⟩, fun w hw ↦ ?_⟩
    obtain ⟨y₀, hy₀, hm⟩ := hmax hv w
    refine ⟨y₀, hy₀, fun y' hy' ↦ ?_, ?_⟩
    · rw [hlag, hlag]
      linarith [hm y' hy']
    · have h2w := h2 w
      rw [hd2 hv w, indicatorVA_apply_mem hw, zero_add, hsup_eq w y₀ hy₀ hm,
        ← EReal.coe_add] at h2w
      rw [hlag]
      have := EReal.coe_nonneg.1 h2w
      linarith
  · -- (b) sufficiency
    intro hne hpos
    obtain ⟨y₁, hy₁⟩ := hne
    have hv : -g ∈ normalCone C x := hmemY y₁ hy₁
    have hpos' : ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w := by
      intro w hw0
      rw [hd2 hv w]
      obtain ⟨y₀, hy₀, hm⟩ := hmax hv w
      rw [hsup_eq w y₀ hy₀ hm]
      by_cases hw : w ∈ K
      · rw [indicatorVA_apply_mem hw, zero_add, ← EReal.coe_add]
        obtain ⟨y, hy, hlt⟩ := hpos w hw hw0
        rw [hlag] at hlt
        exact EReal.coe_pos.2 (by linarith [hm y hy])
      · rw [indicatorVA_apply_not_mem hw, EReal.top_add_coe, EReal.top_add_coe]
        exact EReal.zero_lt_top
    obtain ⟨ε, hε, δ, hδ, hgr⟩ := exists_growth_of_secondSubderivative_pos hfx hpos'
    have hgrowth : ∀ z ∈ C, ‖z - x‖ ≤ δ → f₀ x + ε * ‖z - x‖ ^ 2 ≤ f₀ z := by
      intro z hz hzx
      have h := hgr z hzx
      simp only [hf, indicatorVA_apply_mem hz, zero_add] at h
      exact EReal.coe_le_coe_iff.1 h
    refine ⟨?_, ε, hε, δ, hδ, hgrowth⟩
    filter_upwards [nhdsWithin_le_nhds (closedBall_mem_nhds x hδ), self_mem_nhdsWithin]
      with z hz hzC
    rw [mem_closedBall, dist_eq_norm] at hz
    exact le_trans (le_add_of_nonneg_right (by positivity)) (hgrowth z hzC hz)

end RW
