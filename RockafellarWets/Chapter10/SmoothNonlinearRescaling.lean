/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nonlinear rescaling with a locally smooth inner function

Proposition 10.19(a). Smoothness is required only on a neighborhood of the
base point; a bump extension supplies a global representative for the chain
rule, and locality transports the result back.
-/

import RockafellarWets.Chapter10.BasicChainRule
import RockafellarWets.Chapter10.SmoothLocalExtension
import RockafellarWets.Chapter10.SubgradientGerms

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem adjoint_fderiv_real_apply {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x) (r : ℝ) :
    (fderiv ℝ F x).adjoint r = r • gradient F x := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left,real_inner_smul_left,inner_gradient_left hF]
  simp [real_inner_comm,mul_comm]

private theorem scalar_chain_qualification {F : E → ℝ} {θ : ℝ → EReal} {x : E}
    (hF : DifferentiableAt ℝ F x)
    (hQ : gradient F x ≠ 0 ∨ horizonSubdifferential θ (F x) = {0}) :
    ∀ r ∈ horizonSubdifferential θ (F x), (fderiv ℝ F x).adjoint r = 0 → r = 0 := by
  intro r hr he
  rcases hQ with hgrad | hhor
  · rw [adjoint_fderiv_real_apply hF] at he
    exact (smul_eq_zero.mp he).resolve_right hgrad
  · exact mem_singleton_iff.mp (hhor ▸ hr)

/-- **Proposition 10.19(a)**, both inclusions with local smoothness. -/
theorem nonlinearRescaling_smooth_local {F : E → ℝ} {θ : ℝ → EReal} {x : E} {a : ℝ}
    {V : Set E} (hV : IsOpen V) (hxV : x ∈ V) (hF : ContDiffOn ℝ 1 F V)
    (hθ : LowerSemicontinuous θ) (hx : θ (F x) = a)
    (hQ : gradient F x ≠ 0 ∨ horizonSubdifferential θ (F x) = {0}) :
    subdifferential (θ ∘ F) x ⊆ (fun r : ℝ ↦ r • gradient F x) '' subdifferential θ (F x) ∧
      horizonSubdifferential (θ ∘ F) x ⊆
        (fun r : ℝ ↦ r • gradient F x) '' horizonSubdifferential θ (F x) := by
  obtain ⟨G,hG,he⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hV hxV hF
  have hGx := he.eq_of_nhds
  have hgrad := he.gradient_eq (𝕜 := ℝ)
  have hQG : gradient G x ≠ 0 ∨ horizonSubdifferential θ (G x) = {0} := by
    simpa only [hGx,hgrad] using hQ
  have hdx := hG.differentiable (by norm_num) x
  have hxG : θ (G x) = a := hGx ▸ hx
  have hcomp : θ ∘ G =ᶠ[𝓝 x] θ ∘ F := he.fun_comp θ
  have hlG := locallyLscAt_of_lowerSemicontinuous_finite (hθ.comp hG.continuous) hxG
  have hlF := hlG.congr_nhds hcomp
  constructor
  · rw [← subdifferential_congr_nhds_of_finite (f := θ ∘ G) (x := x) hxG hcomp]
    have h := subdifferential_comp_subset hG hθ hxG (scalar_chain_qualification hdx hQG)
    simpa only [adjoint_fderiv_real_apply hdx,hGx,hgrad] using h
  · rw [← horizonSubdifferential_congr_nhds_of_locallyLsc (f := θ ∘ G) (x := x) hxG hlG hlF hcomp]
    have h := horizonSubdifferential_comp_subset hG hθ hxG (scalar_chain_qualification hdx hQG)
    simpa only [adjoint_fderiv_real_apply hdx,hGx,hgrad] using h

/-- **Proposition 10.19(a)**, equality and regularity when the outer scalar
function is regular. -/
theorem nonlinearRescaling_smooth_local_of_regular {F : E → ℝ} {θ : ℝ → EReal} {x : E}
    {V : Set E} (hV : IsOpen V) (hxV : x ∈ V) (hF : ContDiffOn ℝ 1 F V)
    (hθ : LowerSemicontinuous θ) (hr : IsSubdifferentiallyRegularAt θ (F x))
    (hQ : gradient F x ≠ 0 ∨ horizonSubdifferential θ (F x) = {0}) :
    subdifferential (θ ∘ F) x = (fun r : ℝ ↦ r • gradient F x) '' subdifferential θ (F x) ∧
      horizonSubdifferential (θ ∘ F) x =
        (fun r : ℝ ↦ r • gradient F x) '' horizonSubdifferential θ (F x) ∧
      IsSubdifferentiallyRegularAt (θ ∘ F) x := by
  obtain ⟨G,hG,he⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hV hxV hF
  have hGx := he.eq_of_nhds
  have hgrad := he.gradient_eq (𝕜 := ℝ)
  have hQG : gradient G x ≠ 0 ∨ horizonSubdifferential θ (G x) = {0} := by
    simpa only [hGx,hgrad] using hQ
  have hrG : IsSubdifferentiallyRegularAt θ (G x) := hGx ▸ hr
  have hdx := hG.differentiable (by norm_num) x
  have hxG : θ (G x) = ((θ (G x)).toReal : EReal) := (EReal.coe_toReal hrG.2.1 hrG.1).symm
  have hcomp : θ ∘ G =ᶠ[𝓝 x] θ ∘ F := he.fun_comp θ
  have hqual := scalar_chain_qualification hdx hQG
  have hregG := hrG.comp_of_horizon_qualification hG hθ hqual
  have hregF := hregG.congr_nhds hcomp
  refine ⟨?_,?_,hregF⟩
  · rw [← subdifferential_congr_nhds_of_finite (f := θ ∘ G) (x := x) hxG hcomp]
    have h := subdifferential_comp_eq_of_regular hG hθ hrG hqual
    simpa only [adjoint_fderiv_real_apply hdx,hGx,hgrad] using h
  · rw [← horizonSubdifferential_congr_nhds_of_locallyLsc (f := θ ∘ G) (x := x) hxG hregG.isLocallyLscAt hregF.isLocallyLscAt hcomp]
    have h := horizonSubdifferential_comp_eq_of_regular hG hθ hrG hqual
    simpa only [adjoint_fderiv_real_apply hdx,hGx,hgrad] using h

end RW
