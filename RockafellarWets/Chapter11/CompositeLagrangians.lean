/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The multiplier rule in Lagrangian form

Example 11.46.
-/
import RockafellarWets.Chapter11.FenchelLagrangians
import RockafellarWets.Chapter11.MinimaxProblems
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter10.CompositeMultipliers

open Set Filter Topology Classical
open scoped InnerProductSpace
namespace RW
noncomputable section

/-- Adding a constant other than `-∞` keeps an epigraph convex. -/
theorem convex_epigraph_const_add {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {g : F → EReal} (hg : Convex ℝ (epigraph g)) (hgb : ∀ u, g u ≠ ⊥) (c : EReal) :
    Convex ℝ (epigraph (fun u ↦ c + g u)) := by
  induction c using EReal.rec with
  | bot =>
    have he : epigraph (fun u ↦ (⊥ : EReal) + g u) = univ := by
      ext p
      simp [epigraph]
    rw [he]
    exact convex_univ
  | top =>
    have he : epigraph (fun u ↦ (⊤ : EReal) + g u) = ∅ := by
      ext p
      simp [epigraph, EReal.top_add_of_ne_bot (hgb _)]
    rw [he]
    exact convex_empty
  | coe r =>
    have hr : Convex ℝ (epigraph (fun _ : F ↦ (r : EReal))) := by
      rintro ⟨u₁, a₁⟩ h₁ ⟨u₂, a₂⟩ h₂ t s ht hs hts
      change (r : EReal) ≤ a₁ at h₁
      change (r : EReal) ≤ a₂ at h₂
      change (r : EReal) ≤ ((t * a₁ + s * a₂ : ℝ) : EReal)
      rw [EReal.coe_le_coe_iff] at h₁ h₂ ⊢
      have hc : t * r + s * r = r := by rw [← add_mul, hts, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left h₁ ht, mul_le_mul_of_nonneg_left h₂ hs]
    exact convex_epigraph_add_of_ne_bot hr hg (fun _ ↦ EReal.coe_ne_bot _) hgb

theorem ereal_neg_coe_sub (a : ℝ) {H : EReal} (hH : H ≠ ⊥) :
    -((a : EReal) - H) = H + ((-a : ℝ) : EReal) := by
  induction H using EReal.rec with
  | bot => exact absurd rfl hH
  | top => simp
  | coe H =>
    norm_cast
    ring

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The parameterization `f(x,u) = δ_X(x) + f₀(x) + θ(F(x) + u)` of **11.46**. -/
def compositeIntegrand (X : Set E) (f₀ : E → ℝ) (F : E → P) (θ : P → EReal) :
    WithLp 2 (E × P) → EReal :=
  fun q ↦ indicatorVA X q.fst + (f₀ q.fst : EReal) + θ (F q.fst + q.snd)

/-- The Lagrangian of **11.46**, `l(x,y) = δ_X(x) + f₀(x) + ⟨y,F(x)⟩ - θ*(y)` with
the convention `∞ - ∞ = ∞`. -/
def compositeLagrangian (X : Set E) (f₀ : E → ℝ) (F : E → P) (θ : P → EReal)
    (x : E) (y : P) : EReal :=
  if x ∈ X then ((f₀ x + ⟪y, F x⟫_ℝ : ℝ) : EReal) - fenchelConjugate θ y else ⊤

variable {X : Set E} {f₀ : E → ℝ} {F : E → P} {θ : P → EReal}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] in
theorem primalObjective_compositeIntegrand :
    primalObjective (compositeIntegrand X f₀ F θ) = compositeObjective X f₀ F θ := by
  funext x
  change indicatorVA X x + (f₀ x : EReal) + θ (F x + 0) = _
  rw [add_zero, add_right_comm]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Example 11.46**: `f` is a dualizing parameterization of minimizing
`δ_X + f₀ + θ ∘ F`. -/
theorem isDualizingParameterization_composite (hX : X.Nonempty) (hθp : IsProper θ)
    (hθl : LowerSemicontinuous θ) (hθc : Convex ℝ (epigraph θ)) :
    IsDualizingParameterization (compositeObjective X f₀ F θ) (compositeIntegrand X f₀ F θ) := by
  have hθb : ∀ w, θ w ≠ ⊥ := fun w ↦ (hθp.2 w).ne'
  have hcb (x : E) : indicatorVA X x + (f₀ x : EReal) ≠ ⊥ := by
    unfold indicatorVA
    split_ifs <;> simp
  refine ⟨primalObjective_compositeIntegrand.symm, ⟨?_, fun q ↦ ?_⟩, fun x ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨x₀, hx₀⟩ := hX
    obtain ⟨w₀, hw₀⟩ := hθp.1
    refine ⟨WithLp.toLp 2 (x₀, w₀ - F x₀), ?_⟩
    change indicatorVA X x₀ + (f₀ x₀ : EReal) + θ (F x₀ + (w₀ - F x₀)) < ⊤
    rw [show F x₀ + (w₀ - F x₀) = w₀ by abel]
    simp only [indicatorVA, hx₀, if_true, zero_add]
    exact EReal.add_lt_top (EReal.coe_ne_top _) hw₀.ne
  · exact bot_lt_iff_ne_bot.mpr (by simp [compositeIntegrand, EReal.add_eq_bot_iff, hcb, hθb])
  · have hs : parameterSlice (compositeIntegrand X f₀ F θ) x =
        fun u ↦ (indicatorVA X x + (f₀ x : EReal)) + θ (F x + u) := rfl
    have hl : LowerSemicontinuous (fun u : P ↦ θ (F x + u)) :=
      hθl.comp (continuous_const.add continuous_id)
    rw [hs]
    exact lowerSemicontinuous_const.add' hl
      fun u ↦ EReal.continuousAt_add (.inr (hθb _)) (.inl (hcb x))
  · have hs : parameterSlice (compositeIntegrand X f₀ F θ) x =
        fun u ↦ (indicatorVA X x + (f₀ x : EReal)) + θ (F x + u) := rfl
    have hcv : Convex ℝ (epigraph (fun u : P ↦ θ (F x + u))) := by
      have := convex_epigraph_compAffine hθc (ContinuousLinearMap.id ℝ P) (F x)
      simpa [add_comm] using this
    rw [hs]
    exact convex_epigraph_const_add hcv (fun _ ↦ hθb _) _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- **Example 11.46**: the Lagrangian of the parameterization. -/
theorem lagrangian_compositeIntegrand (hθb : ∀ w, θ w ≠ ⊥) :
    lagrangian (compositeIntegrand X f₀ F θ) = compositeLagrangian X f₀ F θ := by
  funext x y
  unfold lagrangian compositeLagrangian
  by_cases hx : x ∈ X
  · rw [if_pos hx]
    have hshift : (⨅ u : P, compositeIntegrand X f₀ F θ (WithLp.toLp 2 (x, u)) -
          (⟪y, u⟫_ℝ : EReal)) =
        ⨅ w : P, (((0 : ℝ) + f₀ x + ⟪y, F x⟫_ℝ : ℝ) : EReal) + (θ w - (⟪y, w⟫_ℝ : EReal)) := by
      refine (Equiv.subRight (F x)).iInf_comp.symm.trans (iInf_congr fun w ↦ ?_)
      change indicatorVA X x + (f₀ x : EReal) + θ (F x + (w - F x)) -
        (⟪y, w - F x⟫_ℝ : EReal) = _
      rw [show F x + (w - F x) = w by abel, inner_sub_right]
      simp only [indicatorVA, hx, if_true]
      rw [← EReal.coe_zero]
      exact ereal_coe_add_coe_add_sub_coe _ _ _ _ _
    rw [hshift, ← coe_add_iInf, iInf_sub_inner_eq_neg_fenchelConjugate, zero_add, ← sub_eq_add_neg]
  · rw [if_neg hx]
    refine iInf_eq_top.mpr fun u ↦ ?_
    change indicatorVA X x + (f₀ x : EReal) + θ (F x + u) - (⟪y, u⟫_ℝ : EReal) = ⊤
    simp only [indicatorVA, hx, if_false, EReal.top_add_coe, EReal.top_add_of_ne_bot (hθb _),
      EReal.top_sub_coe]

theorem hasGradientAt_add_inner_comp {x₀ : E} (hf₀ : DifferentiableAt ℝ f₀ x₀)
    (hF : DifferentiableAt ℝ F x₀) (y : P) :
    HasGradientAt (fun x ↦ f₀ x + ⟪y, F x⟫_ℝ)
      (gradient f₀ x₀ + (fderiv ℝ F x₀).adjoint y) x₀ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h₁ := hf₀.hasGradientAt.hasFDerivAt
  have h₂ : HasFDerivAt (fun x ↦ ⟪y, F x⟫_ℝ) ((innerSL ℝ y).comp (fderiv ℝ F x₀)) x₀ :=
    (innerSL ℝ y).hasFDerivAt.comp x₀ hF.hasFDerivAt
  refine (h₁.add h₂).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left]

/-- **Example 11.46**: the multiplier rule of **10.8**,
`-(∇f₀(x̄) + ∇F(x̄)*ȳ) ∈ N_X(x̄)` with `ȳ ∈ ∂θ(F(x̄))`, is the Lagrangian condition
`0 ∈ ∂ₓl(x̄,ȳ)`, `0 ∈ ∂_y[-l](x̄,ȳ)`. -/
theorem composite_multiplier_rule_iff_lagrangian (hθp : IsProper θ) (hθl : LowerSemicontinuous θ)
    (hθc : Convex ℝ (epigraph θ)) {x₀ : E} (hf₀ : ContDiffAt ℝ 1 f₀ x₀)
    (hF : ContDiffAt ℝ 1 F x₀) (y₀ : P) :
    (-(gradient f₀ x₀ + (fderiv ℝ F x₀).adjoint y₀) ∈ normalCone X x₀ ∧
        y₀ ∈ subdifferential θ (F x₀)) ↔
      ((0 : E) ∈ subdifferential (fun x ↦ compositeLagrangian X f₀ F θ x y₀) x₀ ∧
        (0 : P) ∈ subdifferential (fun y ↦ -compositeLagrangian X f₀ F θ x₀ y) y₀) := by
  have hθcp := isProper_fenchelConjugate hθp hθl hθc
  by_cases hx₀ : x₀ ∈ X
  swap
  · rw [normalCone_eq_empty hx₀]
    simp only [mem_empty_iff_false, false_and, false_iff, not_and]
    intro _ h
    obtain ⟨a, ha⟩ := h.1
    simp [compositeLagrangian, hx₀] at ha
  by_cases hct : fenchelConjugate θ y₀ = ⊤
  · constructor
    · rintro ⟨-, hy⟩
      have he := (mem_subdifferential_iff_fenchel_equality hθp hθc (F x₀) y₀).mp hy
      rw [hct, EReal.add_top_of_ne_bot (hθp.2 _).ne'] at he
      exact absurd he (EReal.coe_ne_top _).symm
    · rintro ⟨-, h⟩
      obtain ⟨a, ha⟩ := h.1
      simp [compositeLagrangian, hx₀, hct] at ha
  obtain ⟨c, hc⟩ : ∃ c : ℝ, fenchelConjugate θ y₀ = c :=
    ⟨_, (EReal.coe_toReal hct (hθcp.2 y₀).ne').symm⟩
  have hk : ContDiffAt ℝ 1 (fun x ↦ f₀ x + ⟪y₀, F x⟫_ℝ) x₀ :=
    hf₀.add ((contDiffAt_const (c := y₀)).inner ℝ hF)
  have hgk := hasGradientAt_add_inner_comp (F := F) (hf₀.differentiableAt one_ne_zero)
    (hF.differentiableAt one_ne_zero) y₀
  -- the primal part
  have hlx : (fun x ↦ compositeLagrangian X f₀ F θ x y₀) =
      fun x ↦ indicatorVA X x + (((f₀ x + ⟪y₀, F x⟫_ℝ) + (-c) : ℝ) : EReal) := by
    funext x
    unfold compositeLagrangian indicatorVA
    rw [hc]
    split_ifs
    · rw [zero_add, ← EReal.coe_sub, sub_eq_add_neg]
    · rw [EReal.top_add_coe]
  have hval : indicatorVA X x₀ = ((0 : ℝ) : EReal) := by simp [indicatorVA, hx₀]
  have hsx := (subdifferentials_add_smooth hval (hk.add (contDiffAt_const (c := -c)))).2.1
  have hgx : gradient (fun x ↦ (f₀ x + ⟪y₀, F x⟫_ℝ) + (-c)) x₀ =
      gradient f₀ x₀ + (fderiv ℝ F x₀).adjoint y₀ := by
    have hg : HasGradientAt (fun x ↦ (f₀ x + ⟪y₀, F x⟫_ℝ) + (-c))
        (gradient f₀ x₀ + (fderiv ℝ F x₀).adjoint y₀) x₀ :=
      hasGradientAt_iff_hasFDerivAt.mpr (hgk.hasFDerivAt.add_const (-c))
    exact hg.gradient
  -- the dual part
  have hly : (fun y ↦ -compositeLagrangian X f₀ F θ x₀ y) =
      fun y ↦ fenchelConjugate θ y + ((-(f₀ x₀ + ⟪y, F x₀⟫_ℝ) : ℝ) : EReal) := by
    funext y
    simp only [compositeLagrangian, hx₀, if_true]
    exact ereal_neg_coe_sub _ (hθcp.2 y).ne'
  have hm : ContDiffAt ℝ 1 (fun y : P ↦ -(f₀ x₀ + ⟪y, F x₀⟫_ℝ)) y₀ :=
    ((contDiffAt_const (c := f₀ x₀)).add (contDiffAt_id.inner ℝ (contDiffAt_const (c := F x₀)))).neg
  have hsy := (subdifferentials_add_smooth hc hm).2.1
  have hgm : HasGradientAt (fun y : P ↦ -(f₀ x₀ + ⟪y, F x₀⟫_ℝ)) (-F x₀) y₀ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hi : HasFDerivAt (fun y : P ↦ ⟪y, F x₀⟫_ℝ) (innerSL ℝ (F x₀)) y₀ := by
      have he : (fun y : P ↦ ⟪y, F x₀⟫_ℝ) = fun y ↦ innerSL ℝ (F x₀) y := by
        funext y
        rw [innerSL_apply_apply, real_inner_comm]
      rw [he]
      exact (innerSL ℝ (F x₀)).hasFDerivAt
    refine (hi.const_add (f₀ x₀)).neg.congr_fderiv ?_
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  rw [hlx, hly]
  change _ ↔ (0 : E) ∈ subdifferential (fun x ↦ indicatorVA X x +
      ((fun x ↦ (f₀ x + ⟪y₀, F x⟫_ℝ) + (-c)) x : EReal)) x₀ ∧
    (0 : P) ∈ subdifferential (fun y ↦ fenchelConjugate θ y +
      ((fun y : P ↦ -(f₀ x₀ + ⟪y, F x₀⟫_ℝ)) y : EReal)) y₀
  rw [hsx, hsy, hgx, hgm.gradient, subdifferential_indicatorVA,
    ← mem_subdifferential_fenchelConjugate_iff hθp hθl hθc]
  constructor
  · rintro ⟨hn, hy⟩
    exact ⟨⟨_, hn, by abel⟩, ⟨F x₀, hy, by abel⟩⟩
  · rintro ⟨⟨v, hv, hv0⟩, ⟨w, hw, hw0⟩⟩
    have hv' : v = -(gradient f₀ x₀ + (fderiv ℝ F x₀).adjoint y₀) := eq_neg_of_add_eq_zero_left hv0
    have hw' : w = F x₀ := by
      have := eq_neg_of_add_eq_zero_left hw0
      rwa [neg_neg] at this
    exact ⟨hv' ▸ hv, hw' ▸ hw⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **11.46** for `θ = θ_{Y,B}`: the Lagrangian is `δ_X + L - δ_Y` with
`L(x,y) = f₀(x) + ⟨y,F(x)⟩ - ½⟨y,By⟩`. -/
theorem compositeLagrangian_quadraticSupport {Y : Set P} {B : P →L[ℝ] P} (hYn : Y.Nonempty)
    (hYc : IsClosed Y) (hYcv : Convex ℝ Y) (hBs : ∀ y z, ⟪B y, z⟫_ℝ = ⟪y, B z⟫_ℝ)
    (hBp : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) :
    compositeLagrangian X f₀ F (quadraticSupport Y B) =
      minimaxLagrangian (fun x y ↦ f₀ x + ⟪y, F x⟫_ℝ - halfQuadratic B y) X Y := by
  have hθ : fenchelConjugate (quadraticSupport Y B) = indicatorQuadratic Y B := by
    rw [quadraticSupport_eq_fenchelConjugate]
    exact fenchelConjugate_fenchelConjugate_eq (isProper_indicatorQuadratic hYn)
      (lowerSemicontinuous_indicatorQuadratic hYc)
      (convex_epigraph_indicatorQuadratic hYcv hBs hBp)
  funext x y
  unfold compositeLagrangian minimaxLagrangian
  rw [hθ]
  by_cases hx : x ∈ X
  · rw [if_pos hx, if_pos hx]
    by_cases hy : y ∈ Y
    · simp only [indicatorQuadratic, indicatorVA, hy, if_true, zero_add]
      norm_cast
    · simp [indicatorQuadratic, indicatorVA, hy]
  · rw [if_neg hx, if_neg hx]

/-- **11.46** for `θ = θ_{Y,B}`: the multiplier rule becomes
`-∇ₓL(x̄,ȳ) ∈ N_X(x̄)` and `∇_yL(x̄,ȳ) ∈ N_Y(ȳ)`. -/
theorem composite_multiplier_rule_quadraticSupport {Y : Set P} {B : P →L[ℝ] P}
    (hYn : Y.Nonempty) (hYc : IsClosed Y) (hYcv : Convex ℝ Y)
    (hBs : ∀ y z, ⟪B y, z⟫_ℝ = ⟪y, B z⟫_ℝ) (hBp : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) {x₀ : E}
    (hf₀ : ContDiffAt ℝ 1 f₀ x₀) (hF : ContDiffAt ℝ 1 F x₀) (y₀ : P) :
    (-(gradient f₀ x₀ + (fderiv ℝ F x₀).adjoint y₀) ∈ normalCone X x₀ ∧
        y₀ ∈ subdifferential (quadraticSupport Y B) (F x₀)) ↔
      (-gradient (fun x ↦ f₀ x + ⟪y₀, F x⟫_ℝ - halfQuadratic B y₀) x₀ ∈ normalCone X x₀ ∧
        gradient (fun y ↦ f₀ x₀ + ⟪y, F x₀⟫_ℝ - halfQuadratic B y) y₀ ∈ normalCone Y y₀) := by
  have hjp : IsProper (indicatorQuadratic Y B) := isProper_indicatorQuadratic hYn
  have hjl : LowerSemicontinuous (indicatorQuadratic Y B) :=
    lowerSemicontinuous_indicatorQuadratic hYc
  have hjc := convex_epigraph_indicatorQuadratic hYcv hBs hBp
  have hθ : quadraticSupport Y B = fenchelConjugate (indicatorQuadratic Y B) :=
    quadraticSupport_eq_fenchelConjugate Y
  have hθp : IsProper (quadraticSupport Y B) := hθ ▸ isProper_fenchelConjugate hjp hjl hjc
  have hθl : LowerSemicontinuous (quadraticSupport Y B) :=
    hθ ▸ lowerSemicontinuous_fenchelConjugate _
  have hθc : Convex ℝ (epigraph (quadraticSupport Y B)) := hθ ▸ convex_epigraph_fenchelConjugate _
  have hθθ : fenchelConjugate (quadraticSupport Y B) = indicatorQuadratic Y B := by
    rw [hθ]
    exact fenchelConjugate_fenchelConjugate_eq hjp hjl hjc
  have hgx : gradient (fun x ↦ f₀ x + ⟪y₀, F x⟫_ℝ - halfQuadratic B y₀) x₀ =
      gradient f₀ x₀ + (fderiv ℝ F x₀).adjoint y₀ := by
    have hg : HasGradientAt (fun x ↦ f₀ x + ⟪y₀, F x⟫_ℝ - halfQuadratic B y₀)
        (gradient f₀ x₀ + (fderiv ℝ F x₀).adjoint y₀) x₀ :=
      hasGradientAt_iff_hasFDerivAt.mpr ((hasGradientAt_add_inner_comp
        (hf₀.differentiableAt one_ne_zero) (hF.differentiableAt one_ne_zero) y₀).hasFDerivAt.sub_const _)
    exact hg.gradient
  have hgy : gradient (fun y ↦ f₀ x₀ + ⟪y, F x₀⟫_ℝ - halfQuadratic B y) y₀ = F x₀ - B y₀ := by
    have hi : HasGradientAt (fun y : P ↦ ⟪y, F x₀⟫_ℝ) (F x₀) y₀ := by
      rw [hasGradientAt_iff_hasFDerivAt]
      have he : (fun y : P ↦ ⟪y, F x₀⟫_ℝ) = fun y ↦ innerSL ℝ (F x₀) y := by
        funext y
        rw [innerSL_apply_apply, real_inner_comm]
      rw [he]
      exact (innerSL ℝ (F x₀)).hasFDerivAt
    have hg : HasGradientAt (fun y ↦ f₀ x₀ + ⟪y, F x₀⟫_ℝ - halfQuadratic B y) (F x₀ - B y₀) y₀ := by
      rw [hasGradientAt_iff_hasFDerivAt, map_sub]
      exact (hi.hasFDerivAt.const_add (f₀ x₀)).sub (hasGradientAt_halfQuadratic hBs y₀).hasFDerivAt
    exact hg.gradient
  rw [hgx, hgy, ← mem_subdifferential_fenchelConjugate_iff hθp hθl hθc, hθθ,
    mem_subdifferential_indicatorQuadratic hBs]

/-- **11.46**: `θ = δ_K` for a closed convex cone `K` is the case `B = 0`, `Y = K*`. -/
theorem quadraticSupport_polarCone_zero {K : Set P} (hKc : IsClosed K) (hKv : Convex ℝ K)
    (hKk : IsCone K) : quadraticSupport (polarCone K) 0 = indicatorVA K := by
  have hj : indicatorQuadratic (polarCone K) (0 : P →L[ℝ] P) = indicatorVA (polarCone K) := by
    funext y
    simp [indicatorQuadratic, halfQuadratic]
  rw [quadraticSupport_eq_fenchelConjugate, hj, fenchelConjugate_indicatorVA_cone
    (isCone_polarCone K), polarCone_bipolar_eq_self hKc hKv hKk]

end
end RW
