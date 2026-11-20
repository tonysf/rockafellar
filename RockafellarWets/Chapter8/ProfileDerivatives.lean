/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Graphical derivatives of the epigraph profile
-/

import RockafellarWets.Chapter8.ProtoDifferentiability
import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter8.RegularSupportDuality
import RockafellarWets.Chapter8.RegularSubderivatives

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → EReal} {x : E} {c r : ℝ}

omit [FiniteDimensional ℝ E] in
/-- **Example 8.35**, the subderivative as the graphical derivative of the profile. -/
theorem graphicalDerivative_epiProfile (hx : f x = c) :
    graphicalDerivative (epiProfile f) x c = epiProfile (subderivative f x) := by
  apply svGraph_injective
  rw [svGraph_graphicalDerivative, show svGraph (epiProfile f) = epigraph f from rfl,
    ← epigraph_subderivative_eq_tangentCone hx]
  rfl

/-- **Example 8.35**, regular graphical derivative of the profile. -/
theorem regularGraphicalDerivative_epiProfile (hx : f x = c) (hl : LowerSemicontinuousAt f x) :
    regularGraphicalDerivative (epiProfile f) x c = epiProfile (regularSubderivative f x) := by
  let T := l2ProdEquiv E
  have hp : (x,c) ∈ epigraph f := hx.le
  have he := regularTangentCone_preimage (Φ := T) (Φ' := T)
    T.toContinuousLinearMap.hasStrictFDerivAt (epigraph f) (x := WithLp.toLp 2 (x,c)) hp
  ext w b
  change WithLp.toLp 2 (w,b) ∈ regularTangentCone (T ⁻¹' epigraph f) (WithLp.toLp 2 (x,c)) ↔
    (w,b) ∈ epigraph (regularSubderivative f x)
  rw [he, epigraph_regularSubderivative_eq_regularTangentCone hx hl]
  rfl

omit [FiniteDimensional ℝ E] in
private theorem homogeneous_slice {D : ℝ → Set E} (hD : SvPositivelyHomogeneous D) (hr : 0 < r) :
    D r = r • D 1 := by simpa only [smul_eq_mul,mul_one] using hD.2 1 r hr

/-- **Example 8.35**, positive-height coderivatives. -/
theorem coderivatives_epiProfile_of_pos (hx : f x = c) (hr : 0 < r) :
    coderivative (epiProfile f) x c r = r • subdifferential f x ∧
    regularCoderivative (epiProfile f) x c r = r • regularSubdifferential f x := by
  have hp := graphicalDerivative_properties (S := epiProfile f) (x := x) (u := c) hx.le
  rw [homogeneous_slice hp.2.2.1.2 hr, homogeneous_slice hp.2.2.2.1.2.1 hr]
  have hn : coderivative (epiProfile f) x c 1 = subdifferential f x := by
    ext v
    exact (mem_subdifferential_iff_epigraph_normal hx).symm
  have hr : regularCoderivative (epiProfile f) x c 1 = regularSubdifferential f x := by
    ext v
    exact (mem_regularSubdifferential_iff_epigraph_normal hx).symm
  rw [hn,hr]
  exact ⟨rfl,rfl⟩

omit [FiniteDimensional ℝ E] in
/-- **Example 8.35**, the negative-height branches of both coderivatives. -/
theorem coderivatives_epiProfile_of_neg (f : E → EReal) (x : E) (c : ℝ) (hr : r < 0) :
    coderivative (epiProfile f) x c r = ∅ ∧ regularCoderivative (epiProfile f) x c r = ∅ := by
  constructor
  · exact eq_empty_iff_forall_notMem.mpr fun v hv ↦
      (neg_pos.mpr hr).not_ge (vertical_nonpos_of_mem_normalCone_epigraph (v := v) hv)
  · exact eq_empty_iff_forall_notMem.mpr fun v hv ↦
      (neg_pos.mpr hr).not_ge (vertical_nonpos_of_mem_regularNormalCone_epigraph (v := v) hv)

/-- **Example 8.35**, the zero-height regular coderivative in all cases.
The printed singleton branch for an empty regular subdifferential fails for
the restricted downward cusp. -/
theorem regularCoderivative_epiProfile_zero (hx : f x = c) :
    regularCoderivative (epiProfile f) x c 0 = polarCone (effectiveDomain (subderivative f x)) := by
  ext v
  change WithLp.toLp 2 (v,-(0:ℝ)) ∈ regularNormalCone (euclideanEpigraph f) _ ↔ _
  rw [neg_zero]
  exact horizontal_regularNormal_iff_polar_subderivative_domain hx v

/-- If a regular subgradient exists, the horizontal regular coderivative is
exactly the horizon of the regular subdifferential, as asserted in 8.35. -/
theorem regularCoderivative_epiProfile_zero_of_nonempty (hx : f x = c)
    (hne : (regularSubdifferential f x).Nonempty) :
    regularCoderivative (epiProfile f) x c 0 = horizonCone (regularSubdifferential f x) := by
  rw [regularCoderivative_epiProfile_zero hx]
  obtain ⟨p,hp⟩ := hne
  have hprop := subdifferential_properties hx
  ext v
  constructor
  · intro hv
    apply mem_horizonCone_of_forall_smul_add_mem (x := p)
    intro t ht
    apply (mem_regularSubdifferential_iff_inner_le_subderivative hx).mpr
    intro w
    by_cases hw : subderivative f x w = ⊤
    · simp [hw]
    have hi := hv w (show w ∈ effectiveDomain _ from lt_top_iff_ne_top.mpr hw)
    apply le_trans _ (inner_le_subderivative_of_mem_regularSubdifferential hp w)
    rw [EReal.coe_le_coe_iff,inner_add_left,real_inner_smul_left]
    linarith only [mul_nonpos_of_nonneg_of_nonpos ht hi]
  · intro hv w hw
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real (show subderivative f x w < ⊤ from hw)
    by_contra! hpos
    let t := (|r-⟪p,w⟫_ℝ|+1)/⟪v,w⟫_ℝ
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hh := EReal.coe_lt_coe_iff.mp ((inner_le_subderivative_of_mem_regularSubdifferential
      (smul_add_mem_of_mem_horizonCone hprop.2.1 hprop.1 hp hv ht) w).trans_lt hr)
    rw [inner_add_left,real_inner_smul_left,
      show t*⟪v,w⟫_ℝ = |r-⟪p,w⟫_ℝ|+1 by dsimp [t]; field_simp] at hh
    linarith [le_abs_self (r-⟪p,w⟫_ℝ)]

/-- Horizontal limiting normals include all horizon subgradients already
without lower semicontinuity. -/
theorem horizonSubdifferential_subset_coderivative_epiProfile_zero (hx : f x = c) :
    horizonSubdifferential f x ⊆ coderivative (epiProfile f) x c 0 := by
  intro v hv
  change WithLp.toLp 2 (v, -(0:ℝ)) ∈ normalCone (euclideanEpigraph f) _
  simpa only [neg_zero] using horizontal_normal_of_mem_horizonSubdifferential hx hv

/-- **Example 8.35**, the zero-height limiting coderivative at a finite
locally lower semicontinuous base point. -/
theorem coderivative_epiProfile_zero (hx : f x = c) (hl : IsLocallyLscAt f x) :
    coderivative (epiProfile f) x c 0 = horizonSubdifferential f x := by
  ext v
  change WithLp.toLp 2 (v,-(0:ℝ)) ∈ normalCone (euclideanEpigraph f) _ ↔ _
  rw [neg_zero]
  exact (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx).symm

end RW
