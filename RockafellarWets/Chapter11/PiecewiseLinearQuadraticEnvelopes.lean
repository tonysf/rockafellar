/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: piecewise linear-quadratic envelopes

**Example 11.28**:
(a) the Moreau envelopes of a proper, convex, piecewise linear-quadratic function are piecewise
linear-quadratic
(`IsPiecewiseLinearQuadratic.isPiecewiseLinearQuadratic_moreauEnvelopeEReal`);
(b) the squared distance to a nonempty polyhedral set is piecewise linear-quadratic
(`isPiecewiseLinearQuadratic_infDist_sq`).

The book justifies (a) by "11.14(a) and 11.26(b)"; it is the piecewise linear-quadratic part
11.14(b) that is used: by 11.26(b), `e_λ f` is the conjugate of `f* + (λ/2)|·|²`, which is
piecewise linear-quadratic by 11.14(b) and 10.22.
-/

import RockafellarWets.Chapter11.PiecewiseLinearQuadraticConjugacy
import RockafellarWets.Chapter11.MoreauConjugacy
import RockafellarWets.Chapter10.DistanceSubsmoothness

open Set Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The quadratic `x ↦ (1/(2t))|x|²` is piecewise linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_moreauQuadratic (t : ℝ) :
    IsPiecewiseLinearQuadratic (fun x : E ↦ (moreauQuadratic t x : EReal)) := by
  let q : QuadraticPiece E :=
    ⟨(1 / t) • ContinuousLinearMap.id ℝ E, fun x y ↦ by
      simp [real_inner_smul_right, real_inner_comm], 0, 0⟩
  refine ⟨1, fun _ ↦ univ, fun _ ↦ q, fun _ ↦ IsPolyhedral.univ, ?_, ?_⟩
  · ext x
    simp [effectiveDomain]
  · intro _ x _
    simp only [moreauQuadratic, q, QuadraticPiece.eval, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, real_inner_smul_right, real_inner_self_eq_norm_sq,
      inner_zero_left, add_zero, EReal.coe_eq_coe_iff]
    ring

/-- **Example 11.28(a)**: for a proper, convex, piecewise linear-quadratic `f` and `λ > 0`, the
Moreau envelope `e_λ f` is piecewise linear-quadratic. -/
theorem IsPiecewiseLinearQuadratic.isPiecewiseLinearQuadratic_moreauEnvelopeEReal
    {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f) (hc : Convex ℝ (epigraph f)) {t : ℝ}
    (ht : 0 < t) : IsPiecewiseLinearQuadratic (moreauEnvelopeEReal f t) := by
  have hl := hf.lowerSemicontinuous
  set g : E → EReal := fun v ↦ fenchelConjugate f v + (moreauQuadratic t⁻¹ v : EReal) with hg
  have hgconj : fenchelConjugate (moreauEnvelopeEReal f t) = g :=
    fenchelConjugate_moreauEnvelopeEReal hp ht
  have hpc := isProper_fenchelConjugate hp hl hc
  have hgp : IsProper g := by
    obtain ⟨v, hv⟩ := hpc.1
    refine ⟨⟨v, ?_⟩, fun w ↦ ?_⟩
    · change fenchelConjugate f v + (moreauQuadratic t⁻¹ v : EReal) < ⊤
      rw [← EReal.coe_toReal hv.ne (hpc.2 v).ne', ← EReal.coe_add]
      exact EReal.coe_lt_top _
    · change ⊥ < fenchelConjugate f w + (moreauQuadratic t⁻¹ w : EReal)
      exact bot_lt_iff_ne_bot.2 (EReal.add_ne_bot_iff.2 ⟨(hpc.2 w).ne', EReal.coe_ne_bot _⟩)
  have hgl : LowerSemicontinuous g := hgconj ▸ lowerSemicontinuous_fenchelConjugate _
  have hgc : Convex ℝ (epigraph g) := hgconj ▸ convex_epigraph_fenchelConjugate _
  have hgplq : IsPiecewiseLinearQuadratic g :=
    (hf.isPiecewiseLinearQuadratic_fenchelConjugate hp hl hc).add
      (isPiecewiseLinearQuadratic_moreauQuadratic t⁻¹)
  rw [← fenchelConjugate_regularized_dual hp hl hc ht]
  exact hgplq.isPiecewiseLinearQuadratic_fenchelConjugate hgp hgl hgc

/-- **Example 11.28(b)**: the squared distance to a nonempty polyhedral set is piecewise
linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_infDist_sq {C : Set E} (hC : IsPolyhedral C)
    (hne : C.Nonempty) :
    IsPiecewiseLinearQuadratic (fun x ↦ ((infDist x C ^ 2 : ℝ) : EReal)) := by
  have hplq : IsPiecewiseLinearQuadratic (indicatorVA C) :=
    ((isPiecewiseLinear_indicatorVA_iff hC.convex).2 hC).isPiecewiseLinearQuadratic
  have hcc : Convex ℝ (epigraph (indicatorVA C)) := by
    rw [epigraph_indicatorVA]
    exact hC.convex.prod (convex_Ici _)
  have he : (fun x ↦ ((infDist x C ^ 2 : ℝ) : EReal)) =
      moreauEnvelopeEReal (indicatorVA C) (1 / 2) :=
    funext fun x ↦ (moreauEnvelopeEReal_indicatorVA_half hC.isClosed hne x).symm
  rw [he]
  exact hplq.isPiecewiseLinearQuadratic_moreauEnvelopeEReal (isProper_indicatorVA hne) hcc
    (by norm_num)

end RW
