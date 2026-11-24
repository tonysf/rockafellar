/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Almost everywhere second-order differentiability

Theorem 13.51.  As in the proof, around each point of `O` a lower-`C²` function `f` agrees on a
ball with `g - ρ‖·‖²` for a finite convex `g` (10.33); restricted to a smaller closed ball, `g`
becomes a proper lsc convex function whose subgradient mapping is maximal monotone (12.17), hence
differentiable almost everywhere on the interior of its domain (12.66).  There `∂f = ∂g - 2ρI`,
so `∂f` is differentiable at almost every point near `x̄`, which is twice differentiability in the
extended sense by 13.2(c).  The symmetry of `∇²f(x)` comes from prox-regularity (13.33) through
`HasExtendedHessianAt.inner_map_comm_of_isProxRegularAt`, in place of the book's appeal to 13.42.
-/

import RockafellarWets.Chapter13.HessianSymmetry
import RockafellarWets.Chapter13.LowerC2ProxRegularity
import RockafellarWets.Chapter12.GenericSingleValuedness
import RockafellarWets.Chapter12.ConvexSubgradientMappings
import RockafellarWets.Chapter10.SubsmoothQuadratic
import RockafellarWets.Chapter10.SubsmoothCalculus
import RockafellarWets.Chapter10.SubsmoothRepresentations
import RockafellarWets.Chapter9.SubgradientModulus
import RockafellarWets.Chapter12.Hypomonotonicity

open Filter Set Topology Metric MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Shifting a set-valued mapping by a continuous linear map preserves differentiability. -/
theorem SvDifferentiableAt.of_shift {S T : E → Set E} {y : E} (L : E →L[ℝ] E)
    (hST : ∀ᶠ z in 𝓝 y, ∀ w, w ∈ S z ↔ w + L z ∈ T z) (hT : SvDifferentiableAt T y) :
    SvDifferentiableAt S y := by
  obtain ⟨u, B, hB⟩ := hT
  refine ⟨u - L y, B - L, fun ε hε ↦ ?_⟩
  filter_upwards [hB ε hε, hST] with z ⟨⟨w', hw'⟩, hall⟩ hz
  refine ⟨⟨w' - L z, (hz _).2 (by rw [sub_add_cancel]; exact hw')⟩, fun w hw ↦ ?_⟩
  have h := hall (w + L z) ((hz w).1 hw)
  calc ‖w - (u - L y) - (B - L) (z - y)‖ = ‖w + L z - u - B (z - y)‖ := by
        congr 1
        simp only [ContinuousLinearMap.sub_apply, map_sub]
        abel
    _ ≤ ε * ‖z - y‖ := h

/-- The gradient of `ρ‖·‖²` is `2ρ·`. -/
theorem gradient_const_mul_norm_sq (ρ : ℝ) (z : E) :
    HasGradientAt (fun y ↦ ρ * ‖y‖ ^ 2) ((2 * ρ) • z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_mul ρ
  convert h using 1
  ext w
  simp [InnerProductSpace.toDual_apply_apply]
  ring

/-- For `f` finite at `z`, the subgradients of `f + ρ‖·‖²` at `z` are those of `f` shifted by
`2ρz`. -/
theorem mem_subdifferential_add_norm_sq_iff {f : E → EReal} {z : E} {c : ℝ} (hz : f z = c)
    (ρ : ℝ) (w : E) :
    w + (2 * ρ) • z ∈ subdifferential (fun y ↦ f y + ((ρ * ‖y‖ ^ 2 : ℝ) : EReal)) z ↔
      w ∈ subdifferential f z := by
  have hk : ContDiffAt ℝ 1 (fun y : E ↦ ρ * ‖y‖ ^ 2) z :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt
  rw [(subdifferentials_add_smooth hz hk).2.1, (gradient_const_mul_norm_sq ρ z).gradient]
  constructor
  · rintro ⟨w', hw', hww⟩
    rw [add_left_inj] at hww
    rw [← hww]; exact hw'
  · intro hw; exact ⟨w, hw, rfl⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- **Theorem 13.51** (almost everywhere second-order differentiability).  A lower-`C²` function
`f` on an open set `O` is twice differentiable in the extended sense at all points of `O` outside
a set that is negligible for any additive Haar measure (Lebesgue measure in particular), and the
Hessians `∇²f(x)` are symmetric wherever they exist. -/
theorem almost_everywhere_second_order_differentiability {f : E → EReal} {O : Set E}
    (hO : IsOpen O) (hfin : ∀ y ∈ O, f y ≠ ⊥ ∧ f y ≠ ⊤)
    (hlow : IsLowerCOn 2 (fun y ↦ (f y).toReal) O) (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ {x ∈ O | ¬ ∃ A, HasExtendedHessianAt f x A} = 0 ∧
    ∀ x ∈ O, ∀ A, HasExtendedHessianAt f x A → ∀ u w, ⟪A u, w⟫_ℝ = ⟪u, A w⟫_ℝ := by
  classical
  have hval : ∀ y ∈ O, f y = (((f y).toReal : ℝ) : EReal) := fun y hy ↦
    (EReal.coe_toReal (hfin y hy).2 (hfin y hy).1).symm
  have hcont : ContinuousOn (fun y ↦ (f y).toReal) O := hlow.continuousOn (by norm_num)
  have hpts := fun y (hy : y ∈ O) ↦ isProxRegular_of_isLowerCOn_two hO hfin hlow hy
  refine ⟨?_, fun x hxO A hA u w ↦ ?_⟩
  · apply measure_null_of_locally_null
    rintro x ⟨hxO, -⟩
    obtain ⟨δ, hδ, hball, ρ, -, hconv⟩ := hlow.exists_convex_sub_quadratic x hxO
    set h : E → ℝ := fun y ↦ (f y).toReal + ρ * ‖y‖ ^ 2 with hh
    set B := closedBall x (δ / 2) with hB
    have hBδ : B ⊆ ball x δ := closedBall_subset_ball (by linarith)
    set H : E → EReal := fun y ↦ if y ∈ B then (h y : EReal) else ⊤ with hH
    -- `H` is proper, lsc and convex
    have hHconv : Convex ℝ (epigraph H) := by
      rintro ⟨y₁, α₁⟩ hy₁ ⟨y₂, α₂⟩ hy₂ a b ha hb hab
      change (α₁ : EReal) ≥ H y₁ at hy₁
      change (α₂ : EReal) ≥ H y₂ at hy₂
      by_cases h₁ : y₁ ∈ B
      · by_cases h₂ : y₂ ∈ B
        · simp only [hH, if_pos h₁, if_pos h₂, ge_iff_le, EReal.coe_le_coe_iff] at hy₁ hy₂
          have hmem : a • y₁ + b • y₂ ∈ B := (convex_closedBall x (δ / 2)) h₁ h₂ ha hb hab
          change ((a * α₁ + b * α₂ : ℝ) : EReal) ≥ H (a • y₁ + b • y₂)
          simp only [hH, if_pos hmem, ge_iff_le, EReal.coe_le_coe_iff]
          calc h (a • y₁ + b • y₂) ≤ a * h y₁ + b * h y₂ :=
                hconv.2 (hBδ h₁) (hBδ h₂) ha hb hab
            _ ≤ a * α₁ + b * α₂ := by gcongr
        · simp only [hH, if_neg h₂] at hy₂
          exact absurd hy₂ (not_le.2 (EReal.coe_lt_top α₂))
      · simp only [hH, if_neg h₁] at hy₁
        exact absurd hy₁ (not_le.2 (EReal.coe_lt_top α₁))
    have hxB : x ∈ B := mem_closedBall_self (by positivity)
    have hHx : H x = (h x : EReal) := by simp only [hH, if_pos hxB]
    have hHprop : IsProper H := by
      refine ⟨⟨x, by rw [hHx]; exact EReal.coe_lt_top _⟩, fun y ↦ ?_⟩
      by_cases hy : y ∈ B
      · simp only [hH, if_pos hy]; exact EReal.bot_lt_coe _
      · simp only [hH, if_neg hy]; exact bot_lt_top
    have hhcont : ∀ y ∈ ball x δ, ContinuousAt h y := fun y hy ↦
      ((hcont.continuousAt (hO.mem_nhds (hball hy))).add
        (continuousAt_const.mul (continuous_norm.continuousAt.pow 2)))
    have hHlsc : LowerSemicontinuous H := by
      intro y a hay
      by_cases hy : y ∈ B
      · simp only [hH, if_pos hy] at hay
        rcases ereal_trichotomy a with ha | ha | ⟨a', ha⟩
        · subst ha
          refine Eventually.of_forall fun z ↦ ?_
          by_cases hz : z ∈ B
          · simp only [hH, if_pos hz]; exact EReal.bot_lt_coe _
          · simp only [hH, if_neg hz]; exact bot_lt_top
        · subst ha; exact absurd hay (not_lt.2 le_top)
        · subst ha
          have hay' : a' < h y := EReal.coe_lt_coe_iff.1 hay
          filter_upwards [(hhcont y (hBδ hy)).eventually (lt_mem_nhds hay')] with z hz
          by_cases hzB : z ∈ B
          · simp only [hH, if_pos hzB]; exact EReal.coe_lt_coe_iff.2 hz
          · simp only [hH, if_neg hzB]; exact EReal.coe_lt_top _
      · have hev : ∀ᶠ z in 𝓝 y, z ∉ B := isClosed_closedBall.isOpen_compl.mem_nhds hy
        filter_upwards [hev] with z hz
        simp only [hH, if_neg hz]
        simp only [hH, if_neg hy] at hay
        exact hay
    have hmax := svMaximalMonotone_subdifferential_of_convex hHprop hHlsc hHconv
    have hnull := (hmax.generic_differentiability μ).1
    -- near `x̄`, `∂H` is `∂f` shifted by `2ρI`
    have hloc : ∀ z ∈ ball x (δ / 2),
        H =ᶠ[𝓝 z] fun y ↦ f y + ((ρ * ‖y‖ ^ 2 : ℝ) : EReal) := by
      intro z hz
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      have hyB : y ∈ B := ball_subset_closedBall hy
      have hyO : y ∈ O := hball (hBδ hyB)
      simp only [hH, if_pos hyB, hh]
      rw [EReal.coe_add, ← hval y hyO]
    have hshift : ∀ z ∈ ball x (δ / 2), ∀ w,
        w ∈ subdifferential f z ↔ w + (2 * ρ) • z ∈ subdifferential H z := by
      intro z hz w
      rw [subdifferential_eq_of_eventuallyEq (hloc z hz)]
      have hzO : z ∈ O := hball (hBδ (ball_subset_closedBall hz))
      exact (mem_subdifferential_add_norm_sq_iff (hval z hzO) ρ w).symm
    refine ⟨{y ∈ O | ¬ ∃ A, HasExtendedHessianAt f y A} ∩ ball x (δ / 2),
      inter_mem_nhdsWithin _ (ball_mem_nhds x (by positivity)), measure_mono_null ?_ hnull⟩
    rintro y ⟨⟨hyO, hyA⟩, hyb⟩
    refine ⟨?_, fun hd ↦ hyA ?_⟩
    · -- `y` is interior to the domain of `∂H`
      have hsub : ball x (δ / 2) ⊆ svDom (subdifferential H) := by
        intro z hz
        have hzO : z ∈ O := hball (hBδ (ball_subset_closedBall hz))
        obtain ⟨w, hw⟩ := ((hpts z hzO).2.2.subdifferential_nonempty_compact).1
        exact ⟨w + (2 * ρ) • z, (hshift z hz w).1 hw⟩
      have hint : y ∈ interior (ball x (δ / 2)) := by
        rw [isOpen_ball.interior_eq]; exact hyb
      exact interior_mono hsub hint
    · -- differentiability of `∂f`, hence an extended Hessian
      have hdf : SvDifferentiableAt (subdifferential f) y := by
        refine SvDifferentiableAt.of_shift ((2 * ρ) • ContinuousLinearMap.id ℝ E) ?_ hd
        filter_upwards [isOpen_ball.mem_nhds hyb] with z hz w
        exact hshift z hz w
      obtain ⟨v, hv⟩ := ((hpts y hyO).2.2.subdifferential_nonempty_compact).1
      exact exists_hasExtendedHessianAt_iff.2
        ⟨⟨_, hval y hyO⟩, ((hpts y hyO).1 v hv).1, hdf⟩
  · -- symmetry from prox-regularity
    have hgrad : gradient (fun z ↦ (f z).toReal) x ∈ subdifferential f x := by
      obtain ⟨⟨w', hw'⟩, hall⟩ := (hA.hasMappingFirstOrderExpansion 1 one_pos).self_of_nhds
      have h1 := hall w' hw'
      simp only [sub_self, map_zero, sub_zero, norm_zero, mul_zero, norm_le_zero_iff,
        sub_eq_zero] at h1
      rw [← h1]; exact hw'
    exact hA.inner_map_comm_of_isProxRegularAt ((hpts x hxO).1 _ hgrad) u w

/-- **Theorem 13.51**, the convex case: a finite convex function on an open convex set is twice
differentiable in the extended sense almost everywhere there, with symmetric Hessians. -/
theorem almost_everywhere_second_order_differentiability_of_convex {f : E → EReal} {O : Set E}
    (hO : IsOpen O) (hfin : ∀ y ∈ O, f y ≠ ⊥ ∧ f y ≠ ⊤)
    (hconv : ConvexOn ℝ O (fun y ↦ (f y).toReal)) (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ {x ∈ O | ¬ ∃ A, HasExtendedHessianAt f x A} = 0 ∧
    ∀ x ∈ O, ∀ A, HasExtendedHessianAt f x A → ∀ u w, ⟪A u, w⟫_ℝ = ⟪u, A w⟫_ℝ :=
  almost_everywhere_second_order_differentiability hO hfin
    ((ConvexOn.isLowerCOn hO hconv).mono le_top) μ

end RW
