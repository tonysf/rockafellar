/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regularity of the proximal hull below the threshold of prox-boundedness
-/

import RockafellarWets.Chapter11.ProximalHullConjugacy
import RockafellarWets.Chapter3.ConvexHullFunctions
import RockafellarWets.Chapter10.SubsmoothCalculus

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Below the threshold the regularized function has affine norm minorants
of every positive slope. -/
theorem isCoercive_add_moreauQuadratic {f : E → EReal} {t : ℝ}
    (ht : 0 < t) (hthr : (t : EReal) < proxThreshold f) :
    IsCoercive (fun x ↦ f x + (moreauQuadratic t x : EReal)) := by
  obtain ⟨s,hs⟩ := lt_iSup_iff.mp hthr
  obtain ⟨⟨hspos,b,hb⟩,hts'⟩ := lt_iSup_iff.mp hs
  have hts := EReal.coe_lt_coe_iff.mp hts'
  obtain ⟨β,_,hβ⟩ := EReal.exists_between_coe_real hb
  have hminor := (le_moreauEnvelopeEReal_iff_quadratic_minorant s β b).mp hβ.le
  have hc : 0 < 1 / (2*s) := by positivity
  have hd : 0 < 1 / (2*t) - 1 / (2*s) :=
    sub_pos.mpr (one_div_lt_one_div_of_lt (by positivity) (by linarith))
  intro γ _
  set c := 1 / (2*s) with hc_def
  set d := 1 / (2*t) - c with hd_def
  set k := γ + 2*c*‖b‖ with hk_def
  refine ⟨β - c*‖b‖^2 - k^2/(4*d), fun x ↦ ?_⟩
  have h4d : 0 < 4*d := by positivity
  have hsq : k*‖x‖ - k^2/(4*d) ≤ d*‖x‖^2 := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ h4d]
    nlinarith [sq_nonneg (2*d*‖x‖ - k)]
  have hinner : -(‖x‖*‖b‖) ≤ ⟪x,b⟫_ℝ := neg_le_of_abs_le (abs_real_inner_le_norm x b)
  have hlin := mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ 2*c)
  have hreal : γ*‖x‖ + (β - c*‖b‖^2 - k^2/(4*d)) ≤
      (β - c*‖x-b‖^2) + 1 / (2*t)*‖x‖^2 := by
    have ht' : 1 / (2*t) = d + c := by rw [hd_def]; ring
    rw [norm_sub_sq_real, ht']
    rw [hk_def] at hsq
    nlinarith
  calc ((γ*‖x‖ + (β - c*‖b‖^2 - k^2/(4*d)) : ℝ) : EReal)
      ≤ (((β - c*‖x-b‖^2) + 1 / (2*t)*‖x‖^2 : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hreal
    _ = ((β - c*‖x-b‖^2 : ℝ) : EReal) + (moreauQuadratic t x : EReal) := by
        rw [EReal.coe_add]; rfl
    _ ≤ f x + (moreauQuadratic t x : EReal) := add_le_add (hminor x) le_rfl

private theorem convexOn_toReal_of_epigraph {g : E → EReal} {S : Set E}
    (hg : IsProper g) (hc : Convex ℝ (epigraph g)) (hS : Convex ℝ S)
    (hs : S ⊆ effectiveDomain g) : ConvexOn ℝ S (fun x ↦ (g x).toReal) := by
  refine ⟨hS,fun x hx y hy a b ha hb hab ↦ ?_⟩
  have he {z : E} (hz : z ∈ S) : ((g z).toReal : EReal) = g z :=
    EReal.coe_toReal (hs hz).ne (hg.2 z).ne'
  have hx' : (x,(g x).toReal) ∈ epigraph g := by change g x ≤ _; rw [he hx]
  have hy' : (y,(g y).toReal) ∈ epigraph g := by change g y ≤ _; rw [he hy]
  have hxy := hc hx' hy' ha hb hab
  change g (a • x + b • y) ≤ ((a • (g x).toReal + b • (g y).toReal : ℝ) : EReal) at hxy
  rw [← he (hS hx hy ha hb hab)] at hxy
  exact EReal.coe_le_coe_iff.mp hxy

variable [FiniteDimensional ℝ E]

/-- **11.26(c)**. For a proper lower semicontinuous function that is
prox-bounded with threshold above `t`, the biconjugate in the proximal-hull
formula is the convex hull `con (f + t⁻¹ j)`, so that
`h_t f = con (f + t⁻¹ j) - t⁻¹ j`.  The proximal hull is then nowhere `-∞`,
its domain is exactly `con (dom f)`, and its (finite) restriction to the
interior of this convex set is lower-`C²`. -/
theorem proximalHull_regular_below_threshold {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {t : ℝ} (ht : 0 < t) (hthr : (t : EReal) < proxThreshold f) :
    let g := fun x ↦ f x + (moreauQuadratic t x : EReal)
    fenchelConjugate (fenchelConjugate g) = convexHullFunction g ∧
    (∀ x, proximalHull f t x = convexHullFunction g x - (moreauQuadratic t x : EReal)) ∧
    (∀ x, ⊥ < proximalHull f t x) ∧
    effectiveDomain (proximalHull f t) = convexHull ℝ (effectiveDomain f) ∧
    IsLowerCOn 2 (fun x ↦ (proximalHull f t x).toReal)
      (interior (convexHull ℝ (effectiveDomain f))) := by
  let g := fun x ↦ f x + (moreauQuadratic t x : EReal)
  change fenchelConjugate (fenchelConjugate g) = convexHullFunction g ∧
    (∀ x, proximalHull f t x = convexHullFunction g x - (moreauQuadratic t x : EReal)) ∧ _
  have hq : Continuous (moreauQuadratic t (E := E)) := by unfold moreauQuadratic; fun_prop
  have hgp : IsProper g := by
    obtain ⟨z,hz⟩ := hp.1
    exact ⟨⟨z,EReal.add_lt_top hz.ne (EReal.coe_ne_top _)⟩,
      fun x ↦ EReal.bot_lt_add_iff.mpr ⟨hp.2 x,EReal.bot_lt_coe _⟩⟩
  have hgl : LowerSemicontinuous g := lowerSemicontinuous_add_coe hl hq
  have hc := isCoercive_add_moreauQuadratic ht hthr
  obtain ⟨hhp,hhl,_,hhc⟩ := convexHullFunction_regular_of_isCoercive hgl hgp hc
  have hbi : fenchelConjugate (fenchelConjugate g) = convexHullFunction g :=
    (fenchelConjugate_fenchelConjugate_eq_epiClosure_convexHullFunction hhp).trans
      (epiClosure_eq_of_lowerSemicontinuous hhl)
  have hdg : effectiveDomain g = effectiveDomain f := by
    ext x
    change f x + (moreauQuadratic t x : EReal) < ⊤ ↔ f x < ⊤
    cases h : f x <;> simp [← EReal.coe_add]
  have hdom := effectiveDomain_convexHullFunction hgl hgp hc
  rw [hdg] at hdom
  have he (x : E) :
      proximalHull f t x = convexHullFunction g x - (moreauQuadratic t x : EReal) := by
    rw [proximalHull_eq_biconjugate_sub f ht]
    change fenchelConjugate (fenchelConjugate g) x - _ = _
    rw [hbi]
  refine ⟨hbi, he, fun x ↦ ?_, ?_, isLowerCOn_two_iff_locally_convex_sub.mpr ?_⟩
  · rw [he]
    have hx := hhp.2 x
    cases h : convexHullFunction g x with
    | bot => rw [h] at hx; exact absurd hx (lt_irrefl _)
    | top => simp
    | coe a => rw [← EReal.coe_sub]; exact EReal.bot_lt_coe _
  · rw [← hdom]
    ext x
    change proximalHull f t x < ⊤ ↔ convexHullFunction g x < ⊤
    rw [he]
    cases h : convexHullFunction g x <;> simp [← EReal.coe_sub]
  · let U := interior (convexHull ℝ (effectiveDomain f))
    have hU : U ⊆ effectiveDomain (convexHullFunction g) := hdom ▸ interior_subset
    intro x hx
    refine ⟨U,isOpen_interior,hx,Subset.rfl,fun y ↦ (convexHullFunction g y).toReal,
      moreauQuadratic t,
      convexOn_toReal_of_epigraph hhp hhc (convex_convexHull ℝ _).interior hU,?_,?_⟩
    · exact (contDiff_const.mul (contDiff_id.norm_sq ℝ)).contDiffOn
    · intro y hy
      rw [he,← EReal.coe_toReal (hU hy).ne (hhp.2 y).ne',← EReal.coe_sub,EReal.toReal_coe]

end RW
