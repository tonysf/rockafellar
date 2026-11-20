/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometry of sets depending on parameters

Exercise 10.17, obtained by applying partial subdifferentiation to the
indicator of a graph.
-/

import RockafellarWets.Chapter10.PartialSubgradients
import RockafellarWets.Chapter8.IndicatorSubgradients
import RockafellarWets.Chapter8.RegularIndicatorDerivatives
import RockafellarWets.Chapter9.InverseCoderivatives

open Set
open scoped InnerProductSpace

namespace RW

variable {E P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  {S : E → Set P} {x : E} {u : P}

theorem partialFunction_indicator_graph (S : E → Set P) (u : P) :
    partialFunction (indicatorVA (euclideanSvGraph S)) u = indicatorVA (svInv S u) := rfl

private theorem indicator_graph_value (hx : u ∈ S x) :
    indicatorVA (euclideanSvGraph S) (WithLp.toLp 2 (x,u)) = ((0:ℝ):EReal) := by
  exact indicatorVA_apply_mem hx

private theorem indicator_graph_lsc (hS : SvOsc S) : LowerSemicontinuous (indicatorVA (euclideanSvGraph S)) :=
  lowerSemicontinuous_indicatorVA ((isClosed_svGraph_iff_svOsc.mpr hS).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ E P).continuous)

private theorem indicator_graph_qualification
    (hQ : ∀ y : P, (0:E) ∈ coderivative S x u y → y = 0) :
    ∀ y : P, WithLp.toLp 2 ((0:E),y) ∈
      horizonSubdifferential (indicatorVA (euclideanSvGraph S)) (WithLp.toLp 2 (x,u)) → y = 0 := by
  intro y hy
  rw [horizonSubdifferential_indicatorVA] at hy
  have h := hQ (-y) (by simpa only [coderivative,svOfEuclideanNormals,mem_setOf_eq,neg_neg] using hy)
  exact neg_eq_zero.mp h

/-- **Exercise 10.17**, the unconditional tangent inclusion. -/
theorem tangentCone_inverse_fiber_subset (hx : u ∈ S x) :
    tangentCone (svInv S u) x ⊆ {w | (0:P) ∈ graphicalDerivative S x u w} := by
  intro w hw
  have h := subderivative_partial_ge (indicator_graph_value hx) w
  rw [partialFunction_indicator_graph,subderivative_indicatorVA (show x ∈ svInv S u from hx),
    subderivative_indicatorVA (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hx)] at h
  have hz : indicatorVA (tangentCone (svInv S u) x) w = 0 := indicatorVA_apply_mem hw
  rw [hz] at h
  by_contra hn
  change WithLp.toLp 2 (w,(0:P)) ∉ tangentCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)) at hn
  simpa [hn] using h

/-- **Exercise 10.17**, regular coderivative values are regular normals to
the inverse fiber. -/
theorem regularNormalCone_inverse_fiber_superset (hx : u ∈ S x) :
    svRange (regularCoderivative S x u) ⊆ regularNormalCone (svInv S u) x := by
  rintro v ⟨y,hy⟩
  have h := regularSubdifferential_partial_superset (indicator_graph_value hx)
  simp only [partialFunction_indicator_graph,regularSubdifferential_indicatorVA] at h
  apply h
  refine ⟨-y,?_⟩
  exact hy

/-- **Exercise 10.17**, the regular tangent inclusion under qualification. -/
theorem regularTangentCone_inverse_fiber_superset (hS : SvOsc S) (hx : u ∈ S x)
    (hQ : ∀ y : P, (0:E) ∈ coderivative S x u y → y = 0) :
    {w | (0:P) ∈ regularGraphicalDerivative S x u w} ⊆ regularTangentCone (svInv S u) x := by
  intro w hw
  have h := regularSubderivative_partial_le (indicator_graph_lsc hS)
    (indicator_graph_value hx) (indicator_graph_qualification hQ) w
  rw [partialFunction_indicator_graph,regularSubderivative_indicatorVA (show x ∈ svInv S u from hx),
    regularSubderivative_indicatorVA (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hx)] at h
  have hz : indicatorVA (regularTangentCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)))
      (WithLp.toLp 2 (w,(0:P))) = 0 := indicatorVA_apply_mem hw
  rw [hz] at h
  by_contra hn
  simpa [hn] using h

/-- **Exercise 10.17**, limiting normals lift to a coderivative multiplier. -/
theorem normalCone_inverse_fiber_subset (hS : SvOsc S) (hx : u ∈ S x)
    (hQ : ∀ y : P, (0:E) ∈ coderivative S x u y → y = 0) :
    normalCone (svInv S u) x ⊆ svRange (coderivative S x u) := by
  intro v hv
  have h := subdifferential_partial_subset (indicator_graph_lsc hS)
    (indicator_graph_value hx) (indicator_graph_qualification hQ)
  simp only [partialFunction_indicator_graph,subdifferential_indicatorVA] at h
  obtain ⟨y,hy⟩ := h hv
  exact ⟨-y,by simpa only [coderivative,svOfEuclideanNormals,mem_setOf_eq,neg_neg] using hy⟩

/-- **Exercise 10.17**, exact tangent and normal formulas when the graph is regular. -/
theorem inverse_fiber_cones_of_graphically_regular (hS : SvOsc S) (hx : u ∈ S x)
    (hQ : ∀ y : P, (0:E) ∈ coderivative S x u y → y = 0)
    (hr : IsGraphicallyRegularAt S x u) :
    tangentCone (svInv S u) x = {w | (0:P) ∈ graphicalDerivative S x u w} ∧
      normalCone (svInv S u) x = svRange (coderivative S x u) := by
  have hreg := (isSubdifferentiallyRegularAt_indicatorVA_iff
    (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hx)).mpr hr
  constructor
  · ext w
    have he := subderivative_partial_eq_of_regular hreg (indicator_graph_lsc hS)
      (indicator_graph_qualification hQ) w
    rw [partialFunction_indicator_graph,subderivative_indicatorVA (show x ∈ svInv S u from hx),
      subderivative_indicatorVA (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hx)] at he
    constructor
    · exact fun hw ↦ tangentCone_inverse_fiber_subset hx hw
    · intro hw
      have hz : indicatorVA (tangentCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)))
          (WithLp.toLp 2 (w,(0:P))) = 0 := indicatorVA_apply_mem hw
      rw [hz] at he
      by_contra hn
      simpa [hn] using he
  · have he := subdifferential_partial_eq_of_regular hreg (indicator_graph_lsc hS)
      (indicator_graph_qualification hQ)
    simp only [partialFunction_indicator_graph,subdifferential_indicatorVA] at he
    ext v
    rw [he]
    constructor
    · rintro ⟨y,hy⟩
      exact ⟨-y,by simpa only [coderivative,svOfEuclideanNormals,mem_setOf_eq,neg_neg] using hy⟩
    · rintro ⟨y,hy⟩
      exact ⟨-y,by simpa only [subdifferential_indicatorVA] using hy⟩

/-- The qualification in 10.17 means that the inverse mapping has the
Aubin property, as stated after the exercise. -/
theorem inverse_fiber_qualification_iff_aubin (hS : SvOsc S) (hx : u ∈ S x) :
    (∀ y : P, (0:E) ∈ coderivative S x u y → y = 0) ↔ HasAubinPropertyAt (svInv S) u x := by
  exact (hasAubinProperty_inverse_iff_coderivative_nonsingular hx
    (RW.IsClosed.isLocallyClosedAt (isClosed_svGraph_iff_svOsc.mpr hS) _)).symm

end RW
