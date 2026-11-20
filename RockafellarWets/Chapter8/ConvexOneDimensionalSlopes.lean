/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Left and right slopes of a proper convex function on the line
-/

import RockafellarWets.Chapter8.Calmness
import RockafellarWets.Chapter8.ConvexSubderivativeInteriors
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.HorizontalEpigraphNormals

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

/-- The right slope, expressed by the radial subderivative in direction one. -/
noncomputable def rightSlope (f : ℝ → EReal) (x : ℝ) := radialSubderivative f x 1

/-- The signed left slope. Both slopes take values in the extended reals. -/
noncomputable def leftSlope (f : ℝ → EReal) (x : ℝ) := -radialSubderivative f x (-1)

variable {f : ℝ → EReal} {x c : ℝ}

private theorem signed_differenceQuotient (f : ℝ → EReal) (x t : ℝ) :
    -differenceQuotient f x (-t) (-1) = differenceQuotient f x t 1 := by
  simp [differenceQuotient,smul_eq_mul]

/-- **Example 8.52**, existence of both one-sided derivatives, with the
left difference quotient divided by its signed (negative) increment. -/
theorem tendsto_oneSidedSlopes_of_convex (hf : Convex ℝ (epigraph f)) (hx : f x = c) :
    Tendsto (fun t ↦ differenceQuotient f x t 1) (𝓝[<] (0:ℝ)) (𝓝 (leftSlope f x)) ∧
    Tendsto (fun t ↦ differenceQuotient f x t 1) (𝓝[>] (0:ℝ)) (𝓝 (rightSlope f x)) := by
  refine ⟨?_,tendsto_differenceQuotient_radialSubderivative hf hx 1⟩
  have hneg : Tendsto (fun t : ℝ ↦ -t) (𝓝[<] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · simpa only [neg_zero] using (continuous_neg.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t < 0) using neg_pos.mpr ht
  simpa only [Function.comp_def,signed_differenceQuotient] using
    ((tendsto_differenceQuotient_radialSubderivative hf hx (-1)).comp hneg).neg

/-- Convexity at the midpoint orders the two one-sided limits, including
infinite slopes at ends of the domain. -/
theorem leftSlope_le_rightSlope_of_convex (hf : Convex ℝ (epigraph f)) (hp : IsProper f) (hx : f x = c) :
    leftSlope f x ≤ rightSlope f x := by
  apply le_of_tendsto_of_tendsto ((tendsto_differenceQuotient_radialSubderivative hf hx (-1)).neg)
    (tendsto_differenceQuotient_radialSubderivative hf hx 1)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  by_cases hL : f (x+t • (-1:ℝ)) = ⊤
  · simp [differenceQuotient_eq_top ht hx hL]
  by_cases hR : f (x+t • (1:ℝ)) = ⊤
  · simp [differenceQuotient_eq_top ht hx hR]
  let l := (f (x+t • (-1:ℝ))).toReal
  let r := (f (x+t • (1:ℝ))).toReal
  have hl : f (x+t • (-1:ℝ)) = (l:EReal) := (EReal.coe_toReal hL (hp.2 _).ne').symm
  have hr : f (x+t • (1:ℝ)) = (r:EReal) := (EReal.coe_toReal hR (hp.2 _).ne').symm
  have hmid := hf (show (x+t • (-1:ℝ), l) ∈ epigraph f from hl.le)
    (show (x+t • (1:ℝ),r) ∈ epigraph f from hr.le) (a := 1/2) (b := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
  change f (1/2*(x+t*(-1))+1/2*(x+t*1)) ≤ ((1/2*l+1/2*r:ℝ):EReal) at hmid
  rw [show 1/2*(x+t*(-1))+1/2*(x+t*1) = x by ring,hx,EReal.coe_le_coe_iff] at hmid
  rw [differenceQuotient_eq_coe hx hl,differenceQuotient_eq_coe hx hr,← EReal.coe_neg,EReal.coe_le_coe_iff,
    ← mul_neg, mul_le_mul_iff_right₀ (inv_pos.mpr ht)]
  linarith

/-- **Example 8.52**, the regular and limiting subdifferentials are the real
slopes bracketed by the two extended one-sided derivatives. -/
theorem subdifferentials_eq_slopeInterval (hf : Convex ℝ (epigraph f)) (hp : IsProper f) (hx : f x = c) :
    subdifferential f x = {v : ℝ | leftSlope f x ≤ (v:EReal) ∧ (v:EReal) ≤ rightSlope f x} ∧
    regularSubdifferential f x = subdifferential f x := by
  refine ⟨?_,(subdifferential_eq_regularSubdifferential_of_convex hf hp hx).symm⟩
  ext v
  rw [mem_subdifferential_iff_of_convex hf hp hx]
  change (∀ z : ℝ, ((c+(z-x)*v:ℝ):EReal) ≤ f z) ↔
    -radialSubderivative f x (-1) ≤ (v:EReal) ∧ (v:EReal) ≤ radialSubderivative f x 1
  rw [EReal.neg_le,← EReal.coe_neg,radialSubderivative,radialSubderivative,le_iInf_iff,le_iInf_iff]
  constructor
  · intro h
    constructor
    · intro t
      apply (coe_le_differenceQuotient_iff hx t.property).mpr
      convert h (x+(t:ℝ)*(-1)) using 2; ring
    · intro t
      apply (coe_le_differenceQuotient_iff hx t.property).mpr
      convert h (x+(t:ℝ)*1) using 2; ring
  · rintro ⟨hL,hR⟩ z
    rcases lt_trichotomy z x with hzx | rfl | hxz
    · have ht : 0 < x-z := sub_pos.mpr hzx
      have hh := (coe_le_differenceQuotient_iff hx ht).mp (hL ⟨x-z,ht⟩)
      rw [show x + (x-z) • (-1:ℝ) = z by change x+(x-z)*(-1)=z; ring] at hh
      convert hh using 2; ring
    · simp [hx]
    · have ht : 0 < z-x := sub_pos.mpr hxz
      have hh := (coe_le_differenceQuotient_iff hx ht).mp (hR ⟨z-x,ht⟩)
      simpa [smul_eq_mul] using hh

private theorem exists_left_domain_iff (hx : f x = c) :
    (∃ z ∈ effectiveDomain f, z < x) ↔ ⊥ < leftSlope f x := by
  have he : (-1:ℝ) ∈ effectiveDomain (radialSubderivative f x) ↔ (-1:ℝ) ∈ radialCone (effectiveDomain f) x :=
    Set.ext_iff.mp (effectiveDomain_radialSubderivative hx) _
  change radialSubderivative f x (-1) < ⊤ ↔ _ at he
  rw [leftSlope, ← EReal.neg_top, EReal.neg_lt_neg_iff, he]
  constructor
  · rintro ⟨z,hz,hzx⟩
    exact ⟨x-z,sub_pos.mpr hzx,by simpa [smul_eq_mul] using hz⟩
  · rintro ⟨t,ht,hz⟩
    exact ⟨_,hz,by simp [smul_eq_mul]; linarith⟩

private theorem exists_right_domain_iff (hx : f x = c) :
    (∃ z ∈ effectiveDomain f, x < z) ↔ rightSlope f x < ⊤ := by
  have he : (1:ℝ) ∈ effectiveDomain (radialSubderivative f x) ↔ (1:ℝ) ∈ radialCone (effectiveDomain f) x :=
    Set.ext_iff.mp (effectiveDomain_radialSubderivative hx) _
  change radialSubderivative f x 1 < ⊤ ↔ _ at he
  rw [rightSlope,he]
  constructor
  · rintro ⟨z,hz,hxz⟩
    exact ⟨z-x,sub_pos.mpr hxz,by simpa [smul_eq_mul] using hz⟩
  · rintro ⟨t,ht,hz⟩
    exact ⟨_,hz,by simpa [smul_eq_mul] using ht⟩

/-- The horizon formula in Example 8.52 uses exactly which sides of the
base point the effective domain reaches. -/
theorem mem_normalCone_domain_iff_slopeSigns (hf : Convex ℝ (epigraph f)) (hx : f x = c) {v : ℝ} :
    v ∈ normalCone (effectiveDomain f) x ↔
      (⊥ < leftSlope f x → 0 ≤ v) ∧ (rightSlope f x < ⊤ → v ≤ 0) := by
  rw [normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hf)
    (show x ∈ effectiveDomain f from hx.trans_lt (EReal.coe_lt_top c)),
    ← exists_left_domain_iff hx,← exists_right_domain_iff hx]
  change (∀ z ∈ effectiveDomain f, (z-x)*v ≤ 0) ↔ _
  constructor
  · intro h
    constructor
    · rintro ⟨z,hz,hzx⟩
      exact nonneg_of_mul_nonpos_right (h z hz) (sub_neg.mpr hzx)
    · rintro ⟨z,hz,hxz⟩
      exact nonpos_of_mul_nonpos_right (h z hz) (sub_pos.mpr hxz)
  · rintro ⟨hL,hR⟩ z hz
    rcases lt_trichotomy z x with hzx | rfl | hxz
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hzx.le) (hL ⟨z,hz,hzx⟩)
    · simp
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxz.le) (hR ⟨z,hz,hxz⟩)

/-- **Example 8.52**, all four horizon subdifferentials according to the
endpoints of the slope interval. -/
theorem horizonSubdifferential_eq_slopeCases (hf : Convex ℝ (epigraph f)) (hp : IsProper f)
    (hx : f x = c) (hl : IsLocallyLscAt f x) :
    horizonSubdifferential f x =
      if ⊥ < leftSlope f x then (if rightSlope f x < ⊤ then {0} else Ici 0)
      else (if rightSlope f x < ⊤ then Iic 0 else univ) := by
  ext v
  rw [mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx,
    horizontal_normal_iff_normalCone_domain hf hp hx,mem_normalCone_domain_iff_slopeSigns hf hx]
  by_cases hL : ⊥ < leftSlope f x <;> by_cases hR : rightSlope f x < ⊤
  · simp only [hL,hR,if_true,true_implies]
    exact ⟨fun h ↦ le_antisymm h.2 h.1,fun h ↦ ⟨h.ge,h.le⟩⟩
  · simp [hL,hR]
  · simp [hL,hR]
  · simp [hL,hR]

end RW
