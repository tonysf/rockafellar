/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Normal vectors and subgradients as failure of the Aubin property
-/

import RockafellarWets.Chapter9.InverseCoderivatives
import RockafellarWets.Chapter8.ProfileDerivatives
import RockafellarWets.Chapter8.SubgradientsAndGradients
import RockafellarWets.Chapter8.IndicatorSubgradients
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal ENNReal Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → EReal} {x v : E} {c : ℝ}

/-- The level-set assertion in **Theorem 9.41(b)**. -/
theorem zero_subgradient_iff_not_aubin_levelSet (hx : f x = c) (hl : IsLocallyLscAt f x) :
    (0:E) ∈ subdifferential f x ↔ ¬ HasAubinPropertyAt (fun a : ℝ ↦ levelSet f a) c x := by
  have hc : IsLocallyClosedAt (svGraph (epiProfile f)) (x,c) := by
    simpa only [hx,EReal.toReal_coe] using hl.isLocallyClosedAt_epigraph
  change (0:E) ∈ subdifferential f x ↔ ¬ HasAubinPropertyAt (svInv (epiProfile f)) c x
  rw [hasAubinProperty_inverse_iff_coderivative_nonsingular (show c ∈ epiProfile f x from hx.le) hc]
  constructor
  · intro hz h
    have hm : (0:E) ∈ coderivative (epiProfile f) x c 1 := by
      rw [(coderivatives_epiProfile_of_pos hx zero_lt_one).1,one_smul]
      exact hz
    exact one_ne_zero (h 1 hm)
  · intro hn
    by_contra hz
    apply hn
    intro r hr
    rcases lt_trichotomy r 0 with hneg | he | hpos
    · rw [(coderivatives_epiProfile_of_neg f x c hneg).1] at hr
      exact (notMem_empty _ hr).elim
    · exact he
    · rw [(coderivatives_epiProfile_of_pos hx hpos).1] at hr
      obtain ⟨z,hz',he⟩ := hr
      have hz0 : z = 0 := (smul_eq_zero.mp he).resolve_left hpos.ne'
      exact (hz (hz0 ▸ hz')).elim

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem locallyClosed_preimage {P : E × ℝ → E × ℝ} {C : Set (E × ℝ)} {p : E × ℝ}
    (hP : Continuous P) (hC : IsLocallyClosedAt C (P p)) : IsLocallyClosedAt (P ⁻¹' C) p := by
  obtain ⟨V,hV,hVc,hCV⟩ := hC
  exact ⟨P ⁻¹' V,hP.continuousAt.preimage_mem_nhds hV,hVc.preimage hP,hCV.preimage hP⟩

/-- **Theorem 9.41(b)**, with the affine tilt written as addition of a
finite real number so that infinite function values remain well-defined. -/
theorem subgradient_iff_not_aubin_tilted_levelSet (hx : f x = c) (hl : IsLocallyLscAt f x) :
    v ∈ subdifferential f x ↔ ¬ HasAubinPropertyAt
      (fun a : ℝ ↦ {y | f y + ((-c-⟪v,y-x⟫_ℝ : ℝ) : EReal) ≤ a}) 0 x := by
  let k : E → ℝ := fun y ↦ -c-⟪v,y-x⟫_ℝ
  let g : E → EReal := fun y ↦ f y + (k y : EReal)
  have hk : ContDiffAt ℝ 1 k x := by
    change ContDiffAt ℝ 1 (fun y ↦ -c-(InnerProductSpace.toDual ℝ E v) (y-x)) x
    fun_prop
  have hg0 : g x = (0:ℝ) := by
    change f x + ((-c-⟪v,x-x⟫_ℝ : ℝ) : EReal) = 0
    rw [hx,sub_self,inner_zero_right,sub_zero,← EReal.coe_add]
    norm_num
  let P : E × ℝ → E × ℝ := fun p ↦ (p.1,p.2-k p.1)
  have hP : Continuous P := by dsimp [P,k]; fun_prop
  have hp : P (x,0) = (x,c) := by simp [P,k]
  have he : epigraph g = P ⁻¹' epigraph f := by
    ext ⟨y,b⟩
    change f y + (k y : EReal) ≤ (b : EReal) ↔ f y ≤ ((b-k y : ℝ) : EReal)
    cases f y using EReal.rec with
    | bot => simp
    | top => simp only [EReal.top_add_coe,top_le_iff,EReal.coe_ne_top]
    | coe z => simp only [← EReal.coe_add,EReal.coe_le_coe_iff,le_sub_iff_add_le]
  have hfg : IsLocallyClosedAt (epigraph g) (x,0) := by
    rw [he]
    apply locallyClosed_preimage hP
    rw [hp]
    simpa only [hx,EReal.toReal_coe] using hl.isLocallyClosedAt_epigraph
  have hgl := isLocallyLscAt_of_isLocallyClosedAt_epigraph hg0 hfg
  have hkder : HasFDerivAt k (InnerProductSpace.toDual ℝ E (-v)) x := by
    have heq : k = fun y ↦ (InnerProductSpace.toDual ℝ E (-v)) y + (-c+⟪v,x⟫_ℝ) := by
      funext y
      dsimp [k]
      simp only [inner_neg_left,inner_sub_right]
      ring
    rw [heq]
    exact (InnerProductSpace.toDual ℝ E (-v)).hasFDerivAt.add_const _
  have hkgrad : gradient k x = -v := (hk.differentiableAt one_ne_zero).hasGradientAt.unique
    (hasGradientAt_iff_hasFDerivAt.mpr hkder)
  have hsub := (subdifferentials_add_smooth hx hk).2.1
  have hh := zero_subgradient_iff_not_aubin_levelSet hg0 hgl
  rw [hsub,hkgrad] at hh
  simpa only [mem_image,add_neg_eq_zero,exists_eq_right] using hh

omit [FiniteDimensional ℝ E] in
private theorem aubin_neg_parameter {T : ℝ → Set E} {u : E}
    (h : HasAubinPropertyAt T 0 u) : HasAubinPropertyAt (fun a ↦ T (-a)) 0 u := by
  obtain ⟨_,hu,hc,k,V,hV,W,hW,H⟩ := h
  let L := (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ E)
  have hLc : IsLocallyClosedAt (svGraph (fun a ↦ T (-a))) (0,u) := by
    have hc' : IsLocallyClosedAt (svGraph T) (L (0,u)) := by simpa [L] using hc
    exact IsLocallyClosedAt.preimage_continuousLinearEquiv L hc'
  refine ⟨trivial,by simpa only [neg_zero] using hu,hLc,k,Neg.neg ⁻¹' V,
    ?_,W,hW,?_⟩
  · exact (show ContinuousAt (Neg.neg : ℝ → ℝ) 0 from continuous_neg.continuousAt).preimage_mem_nhds
      (by simpa only [neg_zero] using hV)
  · intro a ha b hb v hv
    obtain ⟨z,hz,hd⟩ := H (-a) ⟨trivial,ha.2⟩ (-b) ⟨trivial,hb.2⟩ v hv
    exact ⟨z,hz,by simpa only [dist_neg_neg] using hd⟩

omit [FiniteDimensional ℝ E] in
private theorem aubin_neg_parameter_iff {T : ℝ → Set E} {u : E} :
    HasAubinPropertyAt (fun a ↦ T (-a)) 0 u ↔ HasAubinPropertyAt T 0 u := by
  refine ⟨fun h ↦ ?_,aubin_neg_parameter⟩
  simpa only [neg_neg] using aubin_neg_parameter h

/-- **Theorem 9.41(a)**: a normal vector is detected by failure of Lipschitz
behavior of the sections cut out by its parallel half-spaces. -/
theorem normal_iff_not_aubin_halfspace_sections {C : Set E} (hx : x ∈ C)
    (hc : IsLocallyClosedAt C x) :
    v ∈ normalCone C x ↔
      ¬ HasAubinPropertyAt (fun a : ℝ ↦ {y | y ∈ C ∧ a ≤ ⟪v,y-x⟫_ℝ}) 0 x := by
  have hfx : indicatorVA C x = ((0:ℝ):EReal) := by simp [hx]
  have hh := subgradient_iff_not_aubin_tilted_levelSet (v := v) hfx
    ((isLocallyLscAt_indicatorVA_iff hx).mpr hc)
  rw [subdifferential_indicatorVA] at hh
  have he : (fun a : ℝ ↦ {y | indicatorVA C y + ((-(0:ℝ)-⟪v,y-x⟫_ℝ : ℝ) : EReal) ≤ a}) =
      (fun a : ℝ ↦ {y | y ∈ C ∧ -a ≤ ⟪v,y-x⟫_ℝ}) := by
    funext a
    ext y
    by_cases hy : y ∈ C
    · simp only [mem_setOf_eq,show indicatorVA C y = 0 by simp [hy],zero_add,neg_zero,zero_sub,hy,true_and]
      rw [EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith
    · simp [hy]
  rw [he] at hh
  exact hh.trans (not_congr (aubin_neg_parameter_iff
    (T := fun a : ℝ ↦ {y | y ∈ C ∧ a ≤ ⟪v,y-x⟫_ℝ}) (u := x)))

end RW
