/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Moreau envelopes and Yosida regularizations

This file formalizes Exercise 12.23: for a proper lsc convex `f` and `λ > 0`,
the Moreau envelope `eλf` is finite and differentiable with
`∇eλf = (λI + (∂f)⁻¹)⁻¹`, the Yosida regularization of `∂f` (Example 12.13).
This mapping is maximal monotone, single-valued and Lipschitz continuous with
constant `λ⁻¹`, so `eλf` is of class `C¹⁺`.

The gradient formula `∇eλf = λ⁻¹(I - Pλf)` of 2.26 is proved directly here.
With `p = Pλf(x)`, `p' = Pλf(x')` and `d = x' - x`, comparing the envelope
values through the competitors `p` and `p'` gives

`⟪g, d⟫ - (2λ)⁻¹‖d‖² ≤ eλf(x') - eλf(x) ≤ ⟪g, d⟫ + (2λ)⁻¹‖d‖²`,

for `g = λ⁻¹(x - p)`, where the lower bound uses `‖p' - p‖ ≤ ‖d‖` from the
nonexpansivity of `Pλf` (12.19).  Lemma 12.14 identifies `g` with the Yosida
map of `∂f`, and Example 12.13 supplies maximality and the Lipschitz constant.
-/

import RockafellarWets.Chapter12.ProximalMappingMonotonicity
import RockafellarWets.Chapter12.YosidaRegularization

open Set Filter Topology Asymptotics
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A quadratic bound on the first-order remainder gives a gradient. -/
theorem hasGradientAt_of_abs_sub_inner_le [CompleteSpace E] {F : E → ℝ} {g x : E} {C : ℝ}
    (h : ∀ x', |F x' - F x - ⟪g, x' - x⟫_ℝ| ≤ C * ‖x' - x‖ ^ 2) : HasGradientAt F g x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun d : E ↦ F (x + d) - F x - (InnerProductSpace.toDual ℝ E g) d) =O[𝓝 0]
      fun d ↦ ‖d‖ ^ 2 := by
    refine IsBigO.of_bound C (Eventually.of_forall fun d ↦ ?_)
    have hd := h (x + d)
    rw [add_sub_cancel_left] at hd
    rw [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs, norm_pow, norm_norm]
    exact hd
  exact hO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

variable [FiniteDimensional ℝ E]

/-- The envelope at a point is given by the proximal point there. -/
theorem moreauEnvelopeReal_eq_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam)
    (x : E) :
    moreauEnvelopeEReal f lam x = (moreauEnvelopeReal f lam x : EReal) ∧
      moreauEnvelopeReal f lam x = (f (resolventMap (subdifferential f) lam x)).toReal +
        1 / (2 * lam) * ‖resolventMap (subdifferential f) lam x - x‖ ^ 2 := by
  have hx : resolventMap (subdifferential f) lam x ∈ proximalMappingEReal f lam x := by
    rw [proximalMappingEReal_eq_singleton_of_convex hp hl hc hlam]
    exact mem_singleton _
  obtain ⟨-, he⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp hx
  refine ⟨?_, ?_⟩ <;> rw [moreauEnvelopeReal, he, EReal.toReal_coe]

/-- The two-sided quadratic estimate for the Moreau envelope of a convex
function, with `g = λ⁻¹(x - Pλf(x))`. -/
theorem abs_moreauEnvelopeReal_sub_le {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam)
    (x x' : E) :
    |moreauEnvelopeReal f lam x' - moreauEnvelopeReal f lam x -
        ⟪lam⁻¹ • (x - resolventMap (subdifferential f) lam x), x' - x⟫_ℝ| ≤
      1 / (2 * lam) * ‖x' - x‖ ^ 2 := by
  set P := resolventMap (subdifferential f) lam with hPdef
  have hT := svMaximalMonotone_subdifferential_of_convex hp hl hc
  have hmem : ∀ z, P z ∈ proximalMappingEReal f lam z := fun z ↦ by
    rw [proximalMappingEReal_eq_singleton_of_convex hp hl hc hlam]
    exact mem_singleton _
  have hfP : ∀ z, f (P z) = ((f (P z)).toReal : EReal) := fun z ↦
    (moreauEnvelope_eq_of_mem_proximalMapping hp (hmem z)).1
  obtain ⟨hx₁, hx₂⟩ := moreauEnvelopeReal_eq_of_convex hp hl hc hlam x
  obtain ⟨hx₁', hx₂'⟩ := moreauEnvelopeReal_eq_of_convex hp hl hc hlam x'
  have hup := moreauEnvelope_le (f := f) (lam := lam) x' (P x)
  have hlo := moreauEnvelope_le (f := f) (lam := lam) x (P x')
  rw [hx₁', hfP x, ← EReal.coe_add, EReal.coe_le_coe_iff] at hup
  rw [hx₁, hfP x', ← EReal.coe_add, EReal.coe_le_coe_iff] at hlo
  rw [← hPdef] at hx₂ hx₂'
  have hlip : ‖P x' - P x‖ ≤ ‖x' - x‖ := by
    have := (hT.lipschitzWith_resolventMap hlam).dist_le_mul x' x
    simpa [dist_eq_norm] using this
  have e1 : ‖P x - x'‖ ^ 2 = ‖P x - x‖ ^ 2 - 2 * ⟪P x - x, x' - x⟫_ℝ + ‖x' - x‖ ^ 2 := by
    rw [show P x - x' = (P x - x) - (x' - x) by abel, norm_sub_sq_real]
  have e2 : ‖P x' - x'‖ ^ 2 = ‖P x' - x‖ ^ 2 - 2 * ⟪P x' - x, x' - x⟫_ℝ + ‖x' - x‖ ^ 2 := by
    rw [show P x' - x' = (P x' - x) - (x' - x) by abel, norm_sub_sq_real]
  have e3 : ⟪P x' - x, x' - x⟫_ℝ = ⟪P x' - P x, x' - x⟫_ℝ + ⟪P x - x, x' - x⟫_ℝ := by
    rw [← inner_add_left]
    congr 1
    abel
  have e4 : ⟪lam⁻¹ • (x - P x), x' - x⟫_ℝ = -(lam⁻¹ * ⟪P x - x, x' - x⟫_ℝ) := by
    rw [real_inner_smul_left, ← neg_sub (P x) x, inner_neg_left]
    ring
  have hcs : ⟪P x' - P x, x' - x⟫_ℝ ≤ ‖x' - x‖ ^ 2 := by
    have := real_inner_le_norm (P x' - P x) (x' - x)
    nlinarith [norm_nonneg (x' - x)]
  have hc2 : lam⁻¹ = 2 * (1 / (2 * lam)) := by
    field_simp
  have hcpos : 0 < 1 / (2 * lam) := by positivity
  rw [e4, hx₂, hx₂', hc2, e2, e3]
  rw [e1] at hup
  set c := 1 / (2 * lam)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The gradient of the Moreau envelope of a convex function is
`λ⁻¹(I - Pλf)` (2.26). -/
theorem hasGradientAt_moreauEnvelopeReal {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam)
    (x : E) :
    HasGradientAt (moreauEnvelopeReal f lam)
      (lam⁻¹ • (x - resolventMap (subdifferential f) lam x)) x :=
  hasGradientAt_of_abs_sub_inner_le fun x' ↦ abs_moreauEnvelopeReal_sub_le hp hl hc hlam x x'

/-- **Exercise 12.23 (Moreau envelopes and Yosida regularizations).**  For a
proper lsc convex `f` and `λ > 0`, the Moreau envelope `eλf` is finite and
differentiable, its gradient mapping is the Yosida regularization
`(λI + (∂f)⁻¹)⁻¹` of `∂f`, and this mapping is maximal monotone,
single-valued and Lipschitz continuous on the whole space with constant `λ⁻¹`.
Consequently `eλf` is of class `C¹⁺`: it is `C¹` with a globally Lipschitz
gradient. -/
theorem moreauEnvelope_yosida {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam) :
    (∀ x, moreauEnvelopeEReal f lam x = (moreauEnvelopeReal f lam x : EReal)) ∧
      (∀ x, HasGradientAt (moreauEnvelopeReal f lam) (yosidaMap (subdifferential f) lam x) x) ∧
      svYosida (subdifferential f) lam = (fun x ↦ {gradient (moreauEnvelopeReal f lam) x}) ∧
      SvMaximalMonotone (svYosida (subdifferential f) lam) ∧
      LipschitzWith (Real.toNNReal lam⁻¹) (gradient (moreauEnvelopeReal f lam)) ∧
      ContDiff ℝ 1 (moreauEnvelopeReal f lam) := by
  have hT := svMaximalMonotone_subdifferential_of_convex hp hl hc
  have hgrad : ∀ x, HasGradientAt (moreauEnvelopeReal f lam)
      (yosidaMap (subdifferential f) lam x) x := fun x ↦ by
    rw [hT.yosidaMap_eq hlam]
    exact hasGradientAt_moreauEnvelopeReal hp hl hc hlam x
  have hG : gradient (moreauEnvelopeReal f lam) = yosidaMap (subdifferential f) lam :=
    funext fun x ↦ (hgrad x).gradient
  have hlip := hT.lipschitzWith_yosidaMap hlam
  refine ⟨fun x ↦ (moreauEnvelopeReal_eq_of_convex hp hl hc hlam x).1, hgrad, ?_,
    hT.svMaximalMonotone_svYosida hlam, by rw [hG]; exact hlip, ?_⟩
  · rw [hG]
    exact hT.svYosida_eq_fun hlam
  · refine contDiff_one_iff_fderiv.2 ⟨fun x ↦ (hgrad x).differentiableAt, ?_⟩
    have hF : fderiv ℝ (moreauEnvelopeReal f lam) =
        fun x ↦ InnerProductSpace.toDual ℝ E (yosidaMap (subdifferential f) lam x) :=
      funext fun x ↦ (hgrad x).hasFDerivAt.fderiv
    rw [hF]
    exact (InnerProductSpace.toDual ℝ E).continuous.comp hlip.continuous

end RW
