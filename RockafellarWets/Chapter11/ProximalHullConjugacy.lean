/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The proximal hull as a shifted biconjugate
-/

import RockafellarWets.Chapter11.MoreauConjugacy
import RockafellarWets.Chapter7.EventualProxBoundedness

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The proximal hull of Example 1.44 is the supremum of the quadratic
minorants with a fixed curvature and variable center and height. -/
noncomputable def proximalHull (f : E → EReal) (t : ℝ) (x : E) : EReal :=
  ⨆ w : E, ⨆ a : {a : ℝ // ∀ y, ((a - moreauQuadratic t (y-w) : ℝ) : EReal) ≤ f y},
    ((a.val - moreauQuadratic t (x-w) : ℝ) : EReal)

/-- The optimal height at each possible center is the Moreau envelope. -/
theorem proximalHull_eq_iSup_envelope (f : E → EReal) (t : ℝ) (x : E) :
    proximalHull f t x = ⨆ w : E, moreauEnvelopeEReal f t w - (moreauQuadratic t (x-w) : EReal) := by
  apply iSup_congr
  intro w
  let S := {a : ℝ | ∀ y, ((a - moreauQuadratic t (y-w) : ℝ) : EReal) ≤ f y}
  have hc (a : ℝ) : (a : EReal) ≤ moreauEnvelopeEReal f t w ↔ a ∈ S :=
    le_moreauEnvelopeEReal_iff_quadratic_minorant t a w
  have he : (⨆ a : S, (a.val : EReal)) = moreauEnvelopeEReal f t w := by
    apply le_antisymm (iSup_le fun a : S ↦ (hc a.val).mpr a.property)
    by_contra! h
    obtain ⟨b,hb,hb'⟩ := EReal.exists_between_coe_real h
    exact (not_le_of_gt hb) (le_iSup (fun a : S ↦ (a.val : EReal)) ⟨b,(hc b).mp hb'.le⟩)
  change (⨆ a : S, ((a.val - moreauQuadratic t (x-w) : ℝ) : EReal)) = _
  rw [← he]
  simp only [EReal.coe_sub, sub_eq_add_neg, ereal_iSup_add, EReal.coe_add, EReal.coe_neg]

/-- **11.26(c)**, biconjugate formula for the proximal hull of an
arbitrary function. -/
theorem proximalHull_eq_biconjugate_sub (f : E → EReal) {t : ℝ} (ht : 0 < t) (x : E) :
    proximalHull f t x = fenchelConjugate (fenchelConjugate (fun y ↦ f y + (moreauQuadratic t y : EReal))) x -
      (moreauQuadratic t x : EReal) := by
  let g := fenchelConjugate (fun y ↦ f y + (moreauQuadratic t y : EReal))
  rw [proximalHull_eq_iSup_envelope]
  change _ = (⨆ v : E, (⟪x,v⟫_ℝ : EReal) - g v) + _
  rw [ereal_iSup_add]
  have he (w : E) : moreauEnvelopeEReal f t w - (moreauQuadratic t (x-w) : EReal) =
      ((⟪x,t⁻¹ • w⟫_ℝ : EReal) - g (t⁻¹ • w)) - (moreauQuadratic t x : EReal) := by
    rw [moreauEnvelopeEReal_eq_sub_conjugate f ht]
    change ((moreauQuadratic t w : EReal) - g (t⁻¹ • w)) - _ = _
    cases h : g (t⁻¹ • w) with
    | bot => simp
    | top => simp
    | coe a =>
      simp only [← EReal.coe_sub,EReal.coe_eq_coe_iff,moreauQuadratic,norm_sub_sq_real,real_inner_smul_right]
      ring
  refine le_antisymm (iSup_le fun w ↦ le_iSup_of_le (t⁻¹ • w) (he w).le)
    (iSup_le fun v ↦ le_iSup_of_le (t • v) ?_)
  simpa only [smul_smul,inv_mul_cancel₀ ht.ne',one_smul] using (he (t • v)).symm.le

variable [FiniteDimensional ℝ E]

/-- **11.26(d)**. A proper function equals its proximal hull exactly when
it is lower semicontinuous and adding the quadratic makes it convex. -/
theorem proximalHull_eq_self_iff {f : E → EReal} (hp : IsProper f) {t : ℝ} (ht : 0 < t) :
    proximalHull f t = f ↔ LowerSemicontinuous f ∧
      Convex ℝ (epigraph (fun y ↦ f y + (moreauQuadratic t y : EReal))) := by
  let g := fun y ↦ f y + (moreauQuadratic t y : EReal)
  have hq : Continuous (moreauQuadratic t (E := E)) := by unfold moreauQuadratic; fun_prop
  have hgp : IsProper g := by
    obtain ⟨z,hz⟩ := hp.1
    exact ⟨⟨z,EReal.add_lt_top hz.ne (EReal.coe_ne_top _)⟩,fun x ↦ EReal.bot_lt_add_iff.mpr ⟨hp.2 x,EReal.bot_lt_coe _⟩⟩
  constructor
  · intro h
    have he : fenchelConjugate (fenchelConjugate g) = g := by
      funext x
      have hh := congrFun h x
      rw [proximalHull_eq_biconjugate_sub f ht] at hh
      exact (EReal.sub_add_cancel (a := fenchelConjugate (fenchelConjugate g) x)
        (b := moreauQuadratic t x)).symm.trans (congrArg (fun a : EReal ↦ a + (moreauQuadratic t x : EReal)) hh)
    have hg : LowerSemicontinuous g := he ▸ lowerSemicontinuous_fenchelConjugate _
    have hf : f = fun x ↦ g x + ((-moreauQuadratic t x : ℝ) : EReal) := by
      funext x
      exact (EReal.add_sub_cancel_right (a := f x) (b := moreauQuadratic t x)).symm
    refine ⟨hf ▸ lowerSemicontinuous_add_coe hg hq.neg, ?_⟩
    change Convex ℝ (epigraph g)
    rw [← he]
    exact convex_epigraph_fenchelConjugate _
  · rintro ⟨hl,hc⟩
    have hbi := fenchelConjugate_fenchelConjugate_eq hgp (lowerSemicontinuous_add_coe hl hq) hc
    funext x
    rw [proximalHull_eq_biconjugate_sub f ht]
    change fenchelConjugate (fenchelConjugate g) x - _ = _
    rw [hbi]
    exact EReal.add_sub_cancel_right

end RW
