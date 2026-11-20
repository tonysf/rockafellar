/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Moreau envelopes and conjugation
-/

import RockafellarWets.Chapter11.DualOperationQualifications
import RockafellarWets.Chapter11.QuadraticConjugates
import RockafellarWets.Chapter1.Proximal
import RockafellarWets.Chapter3.ExtendedProximalCancellationCompletion

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic penalty in the Moreau envelope. -/
noncomputable def moreauQuadratic (t : ℝ) (x : E) : ℝ := (1 / (2*t)) * ‖x‖^2

omit [InnerProductSpace ℝ E] in
theorem epiSum_comm (f g : E → EReal) : epiSum f g = epiSum g f := by
  funext x
  simp only [epiSum_apply]
  apply le_antisymm <;> apply le_iInf <;> intro w
  · simpa only [sub_sub_cancel,add_comm] using iInf_le (fun y ↦ f (x-y) + g y) (x-w)
  · simpa only [sub_sub_cancel,add_comm] using iInf_le (fun y ↦ g (x-y) + f y) (x-w)

theorem moreauEnvelopeEReal_eq_epiSum (f : E → EReal) (t : ℝ) :
    moreauEnvelopeEReal f t = epiSum (fun x ↦ (moreauQuadratic t x : EReal)) f := by
  funext x
  rw [epiSum_apply]
  apply iInf_congr
  intro w
  simp only [moreauQuadratic,norm_sub_rev x w,add_comm]

theorem fenchelConjugate_moreauQuadratic {t : ℝ} (ht : 0 < t) :
    fenchelConjugate (fun x : E ↦ (moreauQuadratic t x : EReal)) =
      fun v ↦ (moreauQuadratic t⁻¹ v : EReal) := by
  let A : E →ₗ[ℝ] E := t⁻¹ • LinearMap.id
  have hs : A.IsSymmetric := by intro x y; simp [A,real_inner_smul_left,real_inner_smul_right]
  have hp (x : E) : 0 ≤ ⟪x,A x⟫_ℝ := by
    simp [A,real_inner_smul_right]
    positivity
  have he : (fun x : E ↦ (moreauQuadratic t x : EReal)) = affineQuadratic A 0 0 := by
    funext x
    simp only [moreauQuadratic,affineQuadratic,A,LinearMap.smul_apply,LinearMap.id_apply,
      real_inner_smul_right,real_inner_self_eq_norm_sq,inner_zero_left,add_zero]
    congr 1
    ring
  funext v
  have hy : A (t • v) = v - 0 := by simp [A,smul_smul,ht.ne']
  rw [he,fenchelConjugate_affineQuadratic_of_preimage hs hp 0 0 hy]
  simp only [sub_zero,real_inner_smul_right,real_inner_self_eq_norm_sq,moreauQuadratic]
  congr 1
  field_simp

/-- Finite reflection converts any extended-real supremum to an infimum. -/
theorem ereal_coe_sub_iSup {ι : Sort*} (r : ℝ) (g : ι → EReal) :
    (r : EReal) - (⨆ i, g i) = ⨅ i, (r : EReal) - g i := by
  have h : -(⨆ i, g i) = ⨅ i, -g i := EReal.negOrderIso.map_iSup g
  simp only [sub_eq_add_neg,h,coe_add_iInf]

/-- **11.26(c)**, completing the square for an arbitrary extended-real
function, including improper or nonconvex functions. -/
theorem moreauEnvelopeEReal_eq_sub_conjugate (f : E → EReal) {t : ℝ} (_ht : 0 < t) (x : E) :
    moreauEnvelopeEReal f t x = (moreauQuadratic t x : EReal) -
      fenchelConjugate (fun y ↦ f y + (moreauQuadratic t y : EReal)) (t⁻¹ • x) := by
  rw [fenchelConjugate,ereal_coe_sub_iSup]
  apply iInf_congr
  intro y
  have hs : moreauQuadratic t (y-x) = moreauQuadratic t x -
      (⟪t⁻¹ • x,y⟫_ℝ - moreauQuadratic t y) := by
    simp only [moreauQuadratic,norm_sub_sq_real,real_inner_smul_left,real_inner_comm x y]
    ring
  change f y + (moreauQuadratic t (y-x) : EReal) = _
  cases h : f y with
  | bot => simp
  | top => simp
  | coe a =>
    simp only [hs,← EReal.coe_add,← EReal.coe_sub]
    congr 1
    ring

/-- **11.26(b)**, the conjugate of an envelope, valid for any proper function. -/
theorem fenchelConjugate_moreauEnvelopeEReal {f : E → EReal} (hp : IsProper f) {t : ℝ} (ht : 0 < t) :
    fenchelConjugate (moreauEnvelopeEReal f t) =
      fun v ↦ fenchelConjugate f v + (moreauQuadratic t⁻¹ v : EReal) := by
  rw [moreauEnvelopeEReal_eq_epiSum,epiSum_comm,fenchelConjugate_epiSum hp,fenchelConjugate_moreauQuadratic ht]
  exact ⟨⟨0,EReal.coe_lt_top _⟩,fun y ↦ EReal.bot_lt_coe _⟩

variable [FiniteDimensional ℝ E]

/-- **11.26(b)**, the reverse conjugacy for every positive parameter. -/
theorem fenchelConjugate_regularized_dual {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) {t : ℝ} (ht : 0 < t) :
    fenchelConjugate (fun v ↦ fenchelConjugate f v + (moreauQuadratic t⁻¹ v : EReal)) = moreauEnvelopeEReal f t := by
  let g := fun v : E ↦ (moreauQuadratic t⁻¹ v : EReal)
  have hg : IsProper g := ⟨⟨0,EReal.coe_lt_top _⟩,fun x ↦ EReal.bot_lt_coe _⟩
  have hconj : fenchelConjugate g = fun v ↦ (moreauQuadratic t v : EReal) := by
    simpa only [inv_inv,g] using (fenchelConjugate_moreauQuadratic (E := E) (inv_pos.mpr ht))
  have hcg : Convex ℝ (epigraph g) := by
    rw [show g = fenchelConjugate (fun v : E ↦ (moreauQuadratic t v : EReal)) from
      (fenchelConjugate_moreauQuadratic ht).symm]
    exact convex_epigraph_fenchelConjugate _
  have hlg : LowerSemicontinuous g := continuous_coe_real_ereal.comp (by
    unfold moreauQuadratic
    fun_prop) |>.lowerSemicontinuous
  have hd : effectiveDomain g = univ := eq_univ_of_forall fun x ↦ EReal.coe_lt_top _
  obtain ⟨z,hz⟩ := (isProper_fenchelConjugate hp hl hc).1
  have hm : (0 : E) ∈ interior (effectiveDomain (fenchelConjugate f) - effectiveDomain g) := by
    apply zero_mem_interior_sub_of_meets_interior
    exact Or.inl ⟨z,hz,by simp [hd]⟩
  change fenchelConjugate (fun v ↦ fenchelConjugate f v + g v) = _
  rw [fenchelConjugate_add_of_interior (isProper_fenchelConjugate hp hl hc) hg
    (lowerSemicontinuous_fenchelConjugate _) hlg (convex_epigraph_fenchelConjugate _) hcg hm,
    fenchelConjugate_fenchelConjugate_eq hp hl hc,hconj,moreauEnvelopeEReal_eq_epiSum,epiSum_comm]

/-- **11.26(b)**, the Moreau decomposition of the squared norm. -/
theorem moreau_conjugate_decomposition {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) {t : ℝ} (ht : 0 < t) (x : E) :
    moreauEnvelopeEReal f t x + moreauEnvelopeEReal (fenchelConjugate f) t⁻¹ (t⁻¹ • x) =
      (moreauQuadratic t x : EReal) := by
  have he := moreauEnvelopeEReal_eq_sub_conjugate (fenchelConjugate f) (inv_pos.mpr ht) (t⁻¹ • x)
  rw [fenchelConjugate_regularized_dual hp hl hc ht,inv_inv,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] at he
  have hq : moreauQuadratic t⁻¹ (t⁻¹ • x) = moreauQuadratic t x := by
    simp only [moreauQuadratic,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
    field_simp
  rw [he,hq]
  have hfin := moreauEnvelopeEReal_finite hc hl hp ht x
  rw [← EReal.coe_toReal hfin.2.ne hfin.1.ne']
  simp only [← EReal.coe_sub,← EReal.coe_add,add_sub_cancel]

end RW
