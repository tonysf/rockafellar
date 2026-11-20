/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dual properties in minimization

Theorem 11.8 and the tilted minimization identities 11(6).
-/

import RockafellarWets.Chapter11.FenchelConjugate
import RockafellarWets.Chapter5.ProximalMappings
import RockafellarWets.Chapter10.FermatRule
import RockafellarWets.Chapter9.SmoothnessCriteria
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.SupportInterior
import RockafellarWets.Chapter3.CoercivityHorizonEquivalence

open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **11.8(a)**, the conjugate at zero is the negative primal infimum. -/
theorem iInf_eq_neg_fenchelConjugate_zero (f : E → EReal) :
    (⨅ x, f x) = -fenchelConjugate f 0 := by
  simp only [fenchelConjugate,inner_zero_left,EReal.coe_zero,zero_sub]
  apply le_antisymm
  · rw [EReal.le_neg]
    exact iSup_le fun x ↦ EReal.neg_le_neg_iff.mpr (iInf_le f x)
  · apply le_iInf
    intro x
    rw [EReal.neg_le]
    exact le_iSup (fun y ↦ -f y) x

/-- Formula **11(6)**, the value of every linearly tilted minimization problem. -/
theorem iInf_sub_inner_eq_neg_fenchelConjugate (f : E → EReal) (a : E) :
    (⨅ x, f x-(⟪a,x⟫_ℝ:EReal)) = -fenchelConjugate f a := by
  have he (x : E) : f x-(⟪a,x⟫_ℝ:EReal) = -((⟪a,x⟫_ℝ:EReal)-f x) := by
    cases h : f x with
    | bot => simp
    | top => simp
    | coe c => rw [← EReal.coe_sub,← EReal.coe_sub,← EReal.coe_neg]; congr 1; ring
  simp only [he,fenchelConjugate]
  apply le_antisymm
  · rw [EReal.le_neg]
    apply iSup_le
    intro x
    exact (EReal.le_neg).mp (iInf_le (fun y ↦ -((⟪a,y⟫_ℝ:EReal)-f y)) x)
  · apply le_iInf
    intro x
    exact EReal.neg_le_neg_iff.mpr (le_iSup (fun y ↦ (⟪a,y⟫_ℝ:EReal)-f y) x)

/-- The tilted minimizers are precisely the points admitting the prescribed
convex subgradient. -/
theorem mem_argmin_sub_inner_iff_subgradient [FiniteDimensional ℝ E]
    {f : E → EReal} (hp : IsProper f) (hc : Convex ℝ (epigraph f)) (a x : E) :
    x ∈ argmin (fun y ↦ f y-(⟪a,y⟫_ℝ:EReal)) ↔ a ∈ subdifferential f x := by
  constructor
  · intro hm
    have hxt : f x ≠ ⊤ := by
      intro ht
      have hh := hm.1.trans_lt hm.2
      simp [ht] at hh
    have hx : f x = ((f x).toReal:ℝ) := (EReal.coe_toReal hxt (hp.2 x).ne').symm
    apply (mem_subdifferential_iff_of_convex hc hp hx).mpr
    intro y
    have hh := hm.1.trans_le (iInf_le (fun z ↦ f z-(⟪a,z⟫_ℝ:EReal)) y)
    change f x-(⟪a,x⟫_ℝ:EReal) ≤ f y-(⟪a,y⟫_ℝ:EReal) at hh
    cases hy : f y with
    | bot => exact False.elim ((hp.2 y).ne' hy)
    | top => exact le_top
    | coe c =>
      rw [hx,hy,← EReal.coe_sub,← EReal.coe_sub,EReal.coe_le_coe_iff] at hh
      rw [EReal.coe_le_coe_iff,inner_sub_right]
      linarith
  · intro ha
    obtain ⟨c,hx⟩ := (mem_subdifferential_iff_exists_seq.mp ha).1
    have hsupport := (mem_subdifferential_iff_of_convex hc hp hx).mp ha
    have hmin : ∀ y, f x-(⟪a,x⟫_ℝ:EReal) ≤ f y-(⟪a,y⟫_ℝ:EReal) := by
      intro y
      cases hy : f y with
      | bot => exact False.elim ((hp.2 y).ne' hy)
      | top => simp
      | coe d =>
        have hh := hsupport y
        rw [hy,EReal.coe_le_coe_iff,inner_sub_right] at hh
        rw [hx,← EReal.coe_sub,← EReal.coe_sub,EReal.coe_le_coe_iff]
        linarith
    have he : f x-(⟪a,x⟫_ℝ:EReal) = ⨅ y, f y-(⟪a,y⟫_ℝ:EReal) :=
      le_antisymm (le_iInf hmin) (iInf_le _ x)
    exact ⟨he,by rw [← he,hx,← EReal.coe_sub]; exact EReal.coe_lt_top _⟩

/-- **11(3)**, subtracting a linear functional translates the conjugate. -/
theorem fenchelConjugate_sub_inner (f : E → EReal) (a v : E) :
    fenchelConjugate (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal)) v = fenchelConjugate f (v+a) := by
  apply iSup_congr
  intro x
  change (⟪v,x⟫_ℝ:EReal)-(f x-(⟪a,x⟫_ℝ:EReal)) = (⟪v+a,x⟫_ℝ:EReal)-f x
  rw [inner_add_left]
  cases h : f x with
  | bot => simp
  | top => simp
  | coe c =>
    rw [← EReal.coe_sub,← EReal.coe_sub,← EReal.coe_sub]
    congr 1
    ring

/-- Properness is unchanged by subtracting a linear functional. -/
theorem isProper_sub_inner {f : E → EReal} (hp : IsProper f) (a : E) :
    IsProper (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal)) := by
  obtain ⟨x,hx⟩ := hp.1
  refine ⟨⟨x,?_⟩,fun y ↦ ?_⟩
  · change f x-(⟪a,x⟫_ℝ:EReal) < ⊤
    rw [← EReal.coe_toReal hx.ne (hp.2 x).ne',← EReal.coe_sub]
    exact EReal.coe_lt_top _
  · change ⊥ < f y-(⟪a,y⟫_ℝ:EReal)
    cases hy : f y with
    | bot => exact False.elim ((hp.2 y).ne' hy)
    | top => simp
    | coe c => rw [← EReal.coe_sub]; exact EReal.bot_lt_coe _

/-- Lower semicontinuity is preserved by a linear tilt. -/
theorem lowerSemicontinuous_sub_inner {f : E → EReal} (hl : LowerSemicontinuous f) (a : E) :
    LowerSemicontinuous (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal)) := by
  simpa only [EReal.coe_neg,sub_eq_add_neg] using
    lowerSemicontinuous_add_coe hl (show Continuous (fun x ↦ -⟪a,x⟫_ℝ) by fun_prop)

private theorem sub_inner_le_coe_iff (f : E → EReal) (a x : E) (r : ℝ) :
    f x-(⟪a,x⟫_ℝ:EReal) ≤ (r:EReal) ↔ f x ≤ ((r+⟪a,x⟫_ℝ:ℝ):EReal) := by
  cases h : f x with
  | bot => simp
  | top => simp only [EReal.top_sub_coe,top_le_iff,EReal.coe_ne_top]
  | coe c => rw [← EReal.coe_sub,EReal.coe_le_coe_iff,EReal.coe_le_coe_iff]; exact sub_le_iff_le_add

/-- Convexity is preserved by a linear tilt. -/
theorem convex_epigraph_sub_inner {f : E → EReal} (hc : Convex ℝ (epigraph f)) (a : E) :
    Convex ℝ (epigraph (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal))) := by
  rintro ⟨x,r⟩ hx ⟨y,s⟩ hy α β hα hβ hab
  change f x-(⟪a,x⟫_ℝ:EReal) ≤ (r:EReal) at hx
  change f y-(⟪a,y⟫_ℝ:EReal) ≤ (s:EReal) at hy
  rw [sub_inner_le_coe_iff] at hx hy
  have hh := hc (show (x,r+⟪a,x⟫_ℝ) ∈ epigraph f from hx)
    (show (y,s+⟪a,y⟫_ℝ) ∈ epigraph f from hy) hα hβ hab
  change f (α • x+β • y) ≤ ((α*(r+⟪a,x⟫_ℝ)+β*(s+⟪a,y⟫_ℝ):ℝ):EReal) at hh
  change f (α • x+β • y)-(⟪a,α • x+β • y⟫_ℝ:EReal) ≤ ((α*r+β*s:ℝ):EReal)
  rw [sub_inner_le_coe_iff,inner_add_right,inner_smul_right,inner_smul_right]
  convert hh using 1
  congr 1
  ring

/-- A singleton subdifferential of a closed proper convex function is
already enough for strict differentiability; local finiteness follows. -/
theorem subdifferential_eq_singleton_iff_hasStrictGradientAt_of_convex
    [FiniteDimensional ℝ E] {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {x v : E} :
    subdifferential f x = {v} ↔ HasStrictGradientAt f v x := by
  refine ⟨fun hs ↦ ?_,fun h ↦ h.subdifferential_eq⟩
  have hv : v ∈ subdifferential f x := hs ▸ mem_singleton v
  obtain ⟨c,hx⟩ := (mem_subdifferential_iff_exists_seq.mp hv).1
  have hh := (horizonSubdifferential_eq_normalCone_of_subdifferential_nonempty hc hp hx ⟨v,hv⟩).2
  rw [hs,(isBounded_iff_horizonCone_eq_singleton_zero).mp (isBounded_singleton (x := v))] at hh
  apply hasStrictGradientAt_of_subdifferential_eq _ hs
  exact (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hx
    (isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ (hl.lowerSemicontinuousOn univ) (mem_univ x)
      (hx ▸ EReal.coe_ne_bot c) (hx ▸ EReal.coe_ne_top c))).mpr hh

/-- Ordinary differentiability of the locally finite representative is
equivalent to the same singleton subgradient condition. -/
theorem subdifferential_eq_singleton_iff_hasGradientAt_of_convex
    [FiniteDimensional ℝ E] {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {x v : E} :
    subdifferential f x = {v} ↔
      (∀ᶠ y in 𝓝 x, f y = ((f y).toReal:EReal)) ∧
        HasGradientAt (fun y ↦ (f y).toReal) v x := by
  rw [subdifferential_eq_singleton_iff_hasStrictGradientAt_of_convex hp hl hc]
  constructor
  · intro h
    exact ⟨h.1,hasGradientAt_iff_hasFDerivAt.mpr h.2.hasFDerivAt⟩
  · rintro ⟨hfin,hd⟩
    have hx : f x = ((f x).toReal:EReal) := hfin.self_of_nhds
    have hloc := isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ
      (hl.lowerSemicontinuousOn univ) (mem_univ x)
      (hx ▸ EReal.coe_ne_bot _) (hx ▸ EReal.coe_ne_top _)
    have hr := (isSubdifferentiallyRegularAt_of_convex hc hloc).1
    have hs := hr.hasStrictGradientAt_of_differentiableAt hfin hd.differentiableAt
    rwa [hd.gradient] at hs

/-- The coercive growth condition forces the conjugate to be finite above
at every dual vector. This direction needs no convexity or closedness. -/
theorem fenchelConjugate_lt_top_of_isCoercive {f : E → EReal} (hf : IsCoercive f) (v : E) :
    fenchelConjugate f v < ⊤ := by
  obtain ⟨β,hβ⟩ := hf (‖v‖+1) (by positivity)
  have hbound : fenchelConjugate f v ≤ ((-β:ℝ):EReal) := by
    apply (fenchelConjugate_le_iff _ _ _).mpr
    intro x
    calc
      (⟪v,x⟫_ℝ:EReal)-f x ≤ (⟪v,x⟫_ℝ:EReal)-(((‖v‖+1)*‖x‖+β:ℝ):EReal) :=
        EReal.sub_le_sub le_rfl (hβ x)
      _ = ((⟪v,x⟫_ℝ-((‖v‖+1)*‖x‖+β):ℝ):EReal) := (EReal.coe_sub _ _).symm
      _ ≤ ((-β:ℝ):EReal) := by
        rw [EReal.coe_le_coe_iff]
        have hi := (le_abs_self ⟪v,x⟫_ℝ).trans (abs_real_inner_le_norm v x)
        nlinarith [norm_nonneg x]
  exact hbound.trans_lt (EReal.coe_lt_top _)

/-- The effective domain of the conjugate of a coercive function is the
whole dual space. -/
theorem effectiveDomain_fenchelConjugate_eq_univ_of_isCoercive {f : E → EReal}
    (hf : IsCoercive f) : effectiveDomain (fenchelConjugate f) = univ := by
  exact eq_univ_of_forall (fenchelConjugate_lt_top_of_isCoercive hf)

/-- A horizon function equal to the indicator of zero gives coercivity. -/
theorem isCoercive_of_horizon_eq_indicator_zero [FiniteDimensional ℝ E]
    {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hh : horizonFunction f = indicatorVA {0}) : IsCoercive f := by
  apply (isCoercive_iff_unitSphereHorizonInf_eq_top hl hp).mpr
  apply iInf_eq_top.mpr
  intro w
  have hw : (w:E) ≠ 0 := by
    intro he
    have hnorm := w.property
    simp [he] at hnorm
  rw [hh]
  simp [indicatorVA,hw]

/-- The level-boundedness/interior duality, expressed through the horizon
identity so it can be reused for other dual representations. -/
theorem isLevelBounded_iff_zero_mem_interior_of_horizon_support [FiniteDimensional ℝ E]
    {f : E → EReal} {D : Set E} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) (hD : Convex ℝ D) (hne : D.Nonempty)
    (hh : horizonFunction f = supportFunction D) :
    IsLevelBounded f ↔ (0:E) ∈ interior D := by
  rw [isLevelBounded_iff_horizonFunction_pos hc hl hp,
    mem_interior_iff_inner_lt_supportFunction hD hne]
  simp only [hh,inner_zero_left,EReal.coe_zero]

end RW
