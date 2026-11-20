/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proximal and projection mappings as gradients
-/

import RockafellarWets.Chapter11.DistanceConjugacy
import RockafellarWets.Chapter11.DualMinimizationEquivalences
import RockafellarWets.Chapter10.PLQCalculus

open Set Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem argmin_add_real (f : E → EReal) (c : ℝ) : argmin (fun y ↦ f y + c) = argmin f := by
  ext x
  rw [mem_argmin_iff,mem_argmin_iff,← iInf_add_coe]
  exact and_congr (erealAddRightOrderIso c).injective.eq_iff
    (by cases h : ⨅ y, f y <;> simp [← EReal.coe_add])

private theorem proximalMapping_eq_tilted_argmin (f : E → EReal) (t : ℝ) (x : E) :
    proximalMappingEReal f t x = argmin (fun y ↦ (f y + (moreauQuadratic t y : EReal)) -
      (⟪t⁻¹ • x,y⟫_ℝ : EReal)) := by
  rw [← argmin_add_real _ (moreauQuadratic t x)]
  unfold proximalMappingEReal
  congr 1
  funext y
  change f y + (moreauQuadratic t (y-x) : EReal) = _
  have h : moreauQuadratic t (y-x) = moreauQuadratic t y - ⟪t⁻¹ • x,y⟫_ℝ + moreauQuadratic t x := by
    simp only [moreauQuadratic,norm_sub_sq_real,real_inner_smul_left,real_inner_comm x y]
    ring
  rw [h,EReal.coe_add,EReal.coe_sub]
  simp only [sub_eq_add_neg,add_assoc]

/-- **11.27(a)**. The epi-scaled dual envelope has the unique primal
proximal point as its gradient at every input. -/
theorem proximalMapping_as_gradient {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) {t : ℝ} (ht : 0 < t) (x : E) :
    ∃ p, proximalMappingEReal f t x = {p} ∧
      HasGradientAt (fun z ↦ t * (moreauEnvelopeEReal (fenchelConjugate f) t⁻¹ (t⁻¹ • z)).toReal) p x := by
  let Q := fun y : E ↦ f y + (moreauQuadratic t y : EReal)
  have hq : Convex ℝ (epigraph (fun y : E ↦ (moreauQuadratic t y : EReal))) := by
    have he := fenchelConjugate_moreauQuadratic (E := E) (inv_pos.mpr ht)
    rw [inv_inv] at he
    rw [← he]
    exact convex_epigraph_fenchelConjugate _
  have hqc : Convex ℝ (epigraph Q) := convex_epigraph_add_of_ne_bot hc hq (fun y ↦ (hp.2 y).ne')
    (fun _ ↦ EReal.coe_ne_bot _)
  have heqp : Q = proximalObjectiveEReal f t 0 := by
    funext y
    simp only [Q,proximalObjectiveEReal,moreauQuadratic,sub_zero]
  have hqp : IsProper Q := heqp ▸ isProper_proximalObjectiveEReal hp t 0
  have hql : LowerSemicontinuous Q := lowerSemicontinuous_add_coe hl (by unfold moreauQuadratic; fun_prop)
  obtain ⟨p,hpP⟩ := proximalMappingEReal_nonempty hc hl hp ht x
  have heP : proximalMappingEReal f t x = {p} := by
    apply Subset.antisymm _ (singleton_subset_iff.mpr hpP)
    intro z hz
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by
      simpa only [sub_self,norm_zero,mul_zero] using norm_sub_proximalEReal_le_two_mul hc hl hp ht hz hpP))
  have heQ : fenchelConjugate Q = moreauEnvelopeEReal (fenchelConjugate f) t⁻¹ := by
    have he := fenchelConjugate_regularized_dual (isProper_fenchelConjugate hp hl hc)
      (lowerSemicontinuous_fenchelConjugate _) (convex_epigraph_fenchelConjugate _) (inv_pos.mpr ht)
    simpa only [fenchelConjugate_fenchelConjugate_eq hp hl hc,inv_inv,Q] using he
  have hmin := (proximalMapping_eq_tilted_argmin f t x).symm.trans heP
  have hgrad := ((argmin_sub_inner_eq_singleton_iff_conjugate_hasGradientAt hqp hql hqc _ p).mp hmin).2
  rw [heQ] at hgrad
  let L : E →L[ℝ] E := t⁻¹ • ContinuousLinearMap.id ℝ E
  have H := (hgrad.hasFDerivAt.comp x L.hasFDerivAt).const_smul t
  refine ⟨p,heP,?_⟩
  change HasFDerivAt _ ((InnerProductSpace.toDual ℝ E) p) x
  convert H using 1
  ext w
  simp [L,smul_eq_mul,real_inner_smul_right,ht.ne',mul_comm,mul_left_comm,mul_assoc]

/-- **11.27(b)**. The projection onto a nonempty closed convex set is
the gradient of the unit-parameter envelope of its support function. -/
theorem nearestPoints_as_gradient {C : Set E} (hc : Convex ℝ C) (hcl : IsClosed C) (hne : C.Nonempty)
    (x : E) : ∃ p, nearestPoints C x = {p} ∧
      HasGradientAt (fun z ↦ (moreauEnvelopeEReal (supportFunction C) 1 z).toReal) p x := by
  have hpc := (indicatorVA_isProper_iff C).mpr hne
  have hcc : Convex ℝ (epigraph (indicatorVA C)) := by rw [epigraph_indicatorVA]; exact hc.prod (convex_Ici _)
  obtain ⟨p,hP,hG⟩ := proximalMapping_as_gradient hpc (lowerSemicontinuous_indicatorVA hcl) hcc zero_lt_one x
  obtain ⟨y,hy⟩ := nearestPoints_nonempty hcl hne x
  have hyP : y ∈ proximalMappingEReal (indicatorVA C) 1 x := by
    rw [mem_proximalMappingEReal_iff]
    have hval : proximalObjectiveEReal (indicatorVA C) 1 x y = (moreauQuadratic 1 (y-x) : EReal) := by
      simp [proximalObjectiveEReal,indicatorVA_apply_mem hy.1,moreauQuadratic]
    refine ⟨le_antisymm (le_iInf fun z ↦ ?_) (iInf_le _ y),?_⟩
    · by_cases hz : z ∈ C
      · rw [hval]
        simp only [proximalObjectiveEReal,indicatorVA_apply_mem hz,zero_add,moreauQuadratic,EReal.coe_le_coe_iff]
        have hd := hy.2.trans_le (infDist_le_dist_of_mem hz)
        rw [dist_comm x y,dist_comm x z,dist_eq_norm,dist_eq_norm] at hd
        gcongr
      · change _ ≤ indicatorVA C z + (moreauQuadratic 1 (z-x) : EReal)
        rw [indicatorVA_apply_not_mem hz,EReal.top_add_coe]
        exact le_top
    · exact (iInf_le (proximalObjectiveEReal (indicatorVA C) 1 x) y).trans_lt (hval.trans_lt (EReal.coe_lt_top _))
  have hyp : y = p := (show y ∈ ({p} : Set E) from hP ▸ hyP)
  refine ⟨p,Subset.antisymm (fun z hz ↦ (nearestPoints_subsingleton hc x hz hy).trans hyp)
    (singleton_subset_iff.mpr (hyp ▸ hy)),?_⟩
  simpa only [fenchelConjugate_indicatorVA,inv_one,one_smul,one_mul] using hG

end RW
