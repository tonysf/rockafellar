/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The proximal transform as a generalized conjugacy
-/
import RockafellarWets.Chapter11.GeneralizedConjugacy
import RockafellarWets.Chapter11.ProximalHullConjugacy

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coupling `Φ(x,y) = -(1/2λ)|x - y|²` of Example 11.64. -/
noncomputable def proximalCoupling (t : ℝ) (x y : E) : ℝ := -moreauQuadratic t (x - y)

/-- The second expression for the coupling in Example 11.64. -/
theorem proximalCoupling_eq (t : ℝ) (x y : E) :
    proximalCoupling t x y = (1 / t) * ⟪x,y⟫_ℝ - moreauQuadratic t x - moreauQuadratic t y := by
  simp only [proximalCoupling, moreauQuadratic, norm_sub_sq_real]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp
    ring

omit [InnerProductSpace ℝ E] in
/-- The coupling is symmetric in its two arguments. -/
theorem proximalCoupling_swap (t : ℝ) :
    Function.swap (proximalCoupling (E := E) t) = proximalCoupling t := by
  funext y x
  simp only [Function.swap, proximalCoupling, moreauQuadratic, norm_sub_rev]

private theorem coe_neg_sub_eq_neg_add (r : ℝ) (a : EReal) :
    ((-r : ℝ) : EReal) - a = -(a + (r : EReal)) := by
  cases a with
  | bot => simp
  | top => simp
  | coe a =>
    rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_neg]
    congr 1
    ring

private theorem coe_neg_sub_neg (r : ℝ) (a : EReal) :
    ((-r : ℝ) : EReal) - -a = a - (r : EReal) := by
  cases a with
  | bot => simp
  | top => simp
  | coe a =>
    rw [← EReal.coe_neg, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    ring

theorem ereal_neg_iInf {ι : Sort*} (g : ι → EReal) : -(⨅ i, g i) = ⨆ i, -g i :=
  EReal.negOrderIso.map_iInf g

omit [InnerProductSpace ℝ E] in
/-- **Example 11.64**, `f^Φ = -e_λ f` for an arbitrary extended-real function. -/
theorem pairingConjugate_proximalCoupling (t : ℝ) (f : E → EReal) :
    pairingConjugate (proximalCoupling t) f = fun y ↦ -moreauEnvelopeEReal f t y := by
  funext y
  rw [pairingConjugate, moreauEnvelopeEReal, ereal_neg_iInf]
  apply iSup_congr
  intro x
  exact coe_neg_sub_eq_neg_add _ _

/-- **Example 11.64**, `f^{ΦΦ} = h_λ f`. -/
theorem pairingBiconjugate_proximalCoupling (t : ℝ) (f : E → EReal) :
    pairingConjugate (Function.swap (proximalCoupling t))
        (pairingConjugate (proximalCoupling t) f) = proximalHull f t := by
  rw [proximalCoupling_swap, pairingConjugate_proximalCoupling t f]
  funext x
  rw [proximalHull_eq_iSup_envelope]
  change (⨆ w, ((proximalCoupling t w x : ℝ) : EReal) - -moreauEnvelopeEReal f t w) = _
  apply iSup_congr
  intro w
  rw [proximalCoupling, coe_neg_sub_neg]
  simp only [moreauQuadratic, norm_sub_rev]

/-- **Example 11.64**, the double-envelope form `h_λ f = -e_λ[-e_λ f]`. -/
theorem proximalHull_eq_neg_moreauEnvelope_neg (t : ℝ) (f : E → EReal) :
    proximalHull f t = fun x ↦ -moreauEnvelopeEReal (fun y ↦ -moreauEnvelopeEReal f t y) t x := by
  rw [← pairingBiconjugate_proximalCoupling, proximalCoupling_swap,
    ← pairingConjugate_proximalCoupling]
  rw [← pairingConjugate_proximalCoupling]

/-- **Example 11.64**, the envelope functions of the proximal coupling are
exactly the `λ`-proximal functions. -/
theorem isPairingEnvelope_proximalCoupling_iff (t : ℝ) (f : E → EReal) :
    IsPairingEnvelope (proximalCoupling t) f ↔ proximalHull f t = f := by
  rw [isPairingEnvelope_iff_biconjugate, pairingBiconjugate_proximalCoupling]

/-- **Example 11.64**, for a proper `λ`-proximal function `f`, the function
`g = -e_λ f` is again proper and `λ`-proximal, and `f = -e_λ g`. -/
theorem proximal_correspondence (t : ℝ) {f : E → EReal} (hp : IsProper f)
    (hf : proximalHull f t = f) :
    IsProper (fun y ↦ -moreauEnvelopeEReal f t y) ∧
      proximalHull (fun y ↦ -moreauEnvelopeEReal f t y) t = (fun y ↦ -moreauEnvelopeEReal f t y) ∧
      f = fun x ↦ -moreauEnvelopeEReal (fun y ↦ -moreauEnvelopeEReal f t y) t x := by
  have hbi : f = fun x ↦ -moreauEnvelopeEReal (fun y ↦ -moreauEnvelopeEReal f t y) t x := by
    rw [← proximalHull_eq_neg_moreauEnvelope_neg, hf]
  refine ⟨⟨?_, fun y ↦ ?_⟩, ?_, hbi⟩
  · obtain ⟨x, -⟩ := hp.1
    have h := hp.2 x
    rw [← hf, proximalHull_eq_iSup_envelope] at h
    obtain ⟨w, hw⟩ := lt_iSup_iff.mp h
    refine ⟨w, ?_⟩
    have hw' : ⊥ < moreauEnvelopeEReal f t w := by
      by_contra hc
      rw [not_lt, le_bot_iff] at hc
      rw [hc] at hw
      simp at hw
    have hn := EReal.neg_lt_neg_iff.mpr hw'
    rwa [EReal.neg_bot] at hn
  · obtain ⟨x, hx⟩ := hp.1
    have hle : moreauEnvelopeEReal f t y ≤ f x + ((1 / (2 * t) * ‖x - y‖ ^ 2 : ℝ) : EReal) :=
      iInf_le (fun w ↦ f w + ((1 / (2 * t) * ‖w - y‖ ^ 2 : ℝ) : EReal)) x
    have hlt : moreauEnvelopeEReal f t y < ⊤ :=
      hle.trans_lt (EReal.add_lt_top hx.ne (EReal.coe_ne_top _))
    have hn := EReal.neg_lt_neg_iff.mpr hlt
    rwa [EReal.neg_top] at hn
  · rw [← isPairingEnvelope_proximalCoupling_iff, ← pairingConjugate_proximalCoupling]
    have h := isPairingEnvelope_conjugate (proximalCoupling t) f
    rwa [proximalCoupling_swap] at h

/-- **Example 11.64**, the one-to-one correspondence `f ↔ -e_λ f` on the proper
`λ`-proximal functions, which is its own inverse. -/
noncomputable def proximalTransformEquiv (t : ℝ) :
    {f : E → EReal // IsProper f ∧ proximalHull f t = f} ≃
      {f : E → EReal // IsProper f ∧ proximalHull f t = f} where
  toFun f := ⟨fun y ↦ -moreauEnvelopeEReal f.val t y,
    (proximal_correspondence t f.property.1 f.property.2).1,
    (proximal_correspondence t f.property.1 f.property.2).2.1⟩
  invFun f := ⟨fun y ↦ -moreauEnvelopeEReal f.val t y,
    (proximal_correspondence t f.property.1 f.property.2).1,
    (proximal_correspondence t f.property.1 f.property.2).2.1⟩
  left_inv f := Subtype.ext (proximal_correspondence t f.property.1 f.property.2).2.2.symm
  right_inv f := Subtype.ext (proximal_correspondence t f.property.1 f.property.2).2.2.symm

end RW
