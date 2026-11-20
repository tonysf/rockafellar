/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Properties and duality of graphical derivatives
-/

import RockafellarWets.Chapter8.GraphicalDerivatives
import RockafellarWets.Chapter8.HomogeneousMappings
import RockafellarWets.Chapter6.TangentNormalPolarity
import RockafellarWets.Chapter3.HomogeneousOperations

open Set
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem properties_of_coordinates {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {H : V → Set W}
    (T : V × W →L[ℝ] WithLp 2 (E × F)) {K : Set (WithLp 2 (E × F))}
    (hgraph : svGraph H = T ⁻¹' K) (hcl : IsClosed K) (hK : IsCone K) :
    SvOsc H ∧ SvPositivelyHomogeneous H := by
  rw [← isClosed_svGraph_iff_svOsc, svPositivelyHomogeneous_iff_isCone_svGraph, hgraph]
  exact ⟨hcl.preimage T.continuous, RW.LinearMap.isCone_preimage T.toLinearMap hK⟩

/-- **Proposition 8.37**, outer semicontinuity and homogeneity of all four
mappings, convexity of both regular graphs, and the elementary inclusions. -/
theorem graphicalDerivative_properties {S : E → Set F} {x : E} {u : F} (hx : u ∈ S x) :
    (SvOsc (graphicalDerivative S x u) ∧ SvPositivelyHomogeneous (graphicalDerivative S x u)) ∧
    (SvOsc (regularGraphicalDerivative S x u) ∧ SvSublinear (regularGraphicalDerivative S x u)) ∧
    (SvOsc (coderivative S x u) ∧ SvPositivelyHomogeneous (coderivative S x u)) ∧
    (SvOsc (regularCoderivative S x u) ∧ SvSublinear (regularCoderivative S x u)) ∧
    regularGraphicalDerivative S x u ≤ graphicalDerivative S x u ∧
    regularCoderivative S x u ≤ coderivative S x u := by
  let p := WithLp.toLp 2 (x,u)
  let C := euclideanSvGraph S
  have hp : p ∈ C := hx
  have hRT := properties_of_coordinates euclideanGraphCoordinates (svGraph_svOfEuclideanGraph _)
    (isClosed_regularTangentCone C p) (isCone_regularTangentCone hp)
  have hRN := properties_of_coordinates euclideanNormalCoordinates (svGraph_svOfEuclideanNormals _)
    (isClosed_regularNormalCone C p) (isCone_regularNormalCone hp)
  exact ⟨properties_of_coordinates _ (svGraph_svOfEuclideanGraph _) (isClosed_tangentCone C p) (isCone_tangentCone hp),
    ⟨hRT.1, hRT.2, (convex_regularTangentCone hp).linear_preimage euclideanGraphCoordinates.toLinearMap⟩,
    properties_of_coordinates _ (svGraph_svOfEuclideanNormals _) (isClosed_normalCone C p) (isCone_normalCone hp),
    ⟨hRN.1, hRN.2, (convex_regularNormalCone C p).linear_preimage euclideanNormalCoordinates.toLinearMap⟩,
    fun _ _ h ↦ regularTangentCone_subset_tangentCone hp h,
    fun _ _ h ↦ regularNormalCone_subset_normalCone C p h⟩

theorem svOfEuclideanNormals_polarCone (K : Set (WithLp 2 (E × F))) :
    svOfEuclideanNormals (polarCone K) = svUpperAdjoint (svOfEuclideanGraph K) := by
  funext y
  ext v
  constructor
  · intro h w z hz
    have hh := h (WithLp.toLp 2 (w,z)) hz
    simpa [WithLp.prod_inner_apply, inner_neg_left] using hh
  · intro h p hp
    have hh := h p.fst p.snd hp
    simpa [WithLp.prod_inner_apply, inner_neg_left] using sub_nonpos.mpr hh

theorem svOfEuclideanGraph_polarCone (K : Set (WithLp 2 (E × F))) :
    svOfEuclideanGraph (polarCone K) = svLowerAdjoint (svOfEuclideanNormals K) := by
  funext w
  ext z
  constructor
  · intro h y v hv
    have hh := h (WithLp.toLp 2 (v,-y)) hv
    simpa [WithLp.prod_inner_apply, inner_neg_right, real_inner_comm] using hh
  · intro h p hp
    have hp' : p.fst ∈ svOfEuclideanNormals K (-p.snd) := by
      change WithLp.toLp 2 (p.fst, - -p.snd) ∈ K
      simpa using hp
    have hh := h (-p.snd) p.fst hp'
    change ⟪WithLp.toLp 2 (w,z), p⟫_ℝ ≤ 0
    rw [WithLp.prod_inner_apply]
    change ⟪w,p.fst⟫_ℝ + ⟪z,p.snd⟫_ℝ ≤ 0
    rw [inner_neg_right] at hh
    linarith

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {S : E → Set F} {x : E} {u : F}

/-- **Proposition 8.37**, first adjoint relation in formula 8(26). -/
theorem regularCoderivative_eq_upperAdjoint (hx : u ∈ S x) :
    regularCoderivative S x u = svUpperAdjoint (graphicalDerivative S x u) := by
  change svOfEuclideanNormals (regularNormalCone _ _) = _
  rw [regularNormalCone_eq_polarCone_tangentCone (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hx)]
  exact svOfEuclideanNormals_polarCone _

/-- **Proposition 8.37**, second adjoint relation in formula 8(26). -/
theorem regularGraphicalDerivative_eq_lowerAdjoint (hx : u ∈ S x)
    (hlc : IsLocallyClosedAt (euclideanSvGraph S) (WithLp.toLp 2 (x,u))) :
    regularGraphicalDerivative S x u = svLowerAdjoint (coderivative S x u) := by
  change svOfEuclideanGraph (regularTangentCone _ _) = _
  rw [regularTangentCone_eq_polarCone_normalCone (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hx) hlc]
  exact svOfEuclideanGraph_polarCone _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Example 8.39**, regularity of every closed convex graph. -/
theorem isGraphicallyRegularAt_of_graphConvex_of_osc (hconv : SvGraphConvex S) (hosc : SvOsc S)
    (hx : u ∈ S x) : IsGraphicallyRegularAt S x u := by
  let T := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  have hC : Convex ℝ (euclideanSvGraph S) := hconv.linear_preimage T.toLinearMap
  have hclosed : IsClosed (euclideanSvGraph S) := (isClosed_svGraph_iff_svOsc.mpr hosc).preimage T.continuous
  exact isClarkeRegularAt_of_convex hC hx (RW.IsClosed.isLocallyClosedAt hclosed _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Theorem 8.40**, equality of the regular and limiting coderivatives. -/
theorem isGraphicallyRegularAt_iff_coderivative_eq_regular
    (hlc : IsLocallyClosedAt (euclideanSvGraph S) (WithLp.toLp 2 (x,u))) :
    IsGraphicallyRegularAt S x u ↔ coderivative S x u = regularCoderivative S x u := by
  change (_ ∧ _) ↔ svOfEuclideanNormals _ = svOfEuclideanNormals _
  rw [and_iff_right hlc, svOfEuclideanNormals_injective.eq_iff]

/-- **Theorem 8.40**, equality of the two graphical derivatives. -/
theorem isGraphicallyRegularAt_iff_graphicalDerivative_eq_regular (hx : u ∈ S x)
    (hlc : IsLocallyClosedAt (euclideanSvGraph S) (WithLp.toLp 2 (x,u))) :
    IsGraphicallyRegularAt S x u ↔ graphicalDerivative S x u = regularGraphicalDerivative S x u := by
  change _ ↔ svOfEuclideanGraph _ = svOfEuclideanGraph _
  rw [svOfEuclideanGraph_injective.eq_iff]
  exact isClarkeRegularAt_iff_tangentCone_eq_regularTangentCone hx hlc

/-- **Theorem 8.40**, both adjoint characterizations. -/
theorem isGraphicallyRegularAt_iff_adjoints (hx : u ∈ S x)
    (hlc : IsLocallyClosedAt (euclideanSvGraph S) (WithLp.toLp 2 (x,u))) :
    (IsGraphicallyRegularAt S x u ↔ coderivative S x u = svUpperAdjoint (graphicalDerivative S x u)) ∧
    (IsGraphicallyRegularAt S x u ↔ graphicalDerivative S x u = svLowerAdjoint (coderivative S x u)) := by
  rw [← regularCoderivative_eq_upperAdjoint hx, ← regularGraphicalDerivative_eq_lowerAdjoint hx hlc]
  exact ⟨isGraphicallyRegularAt_iff_coderivative_eq_regular hlc,
    isGraphicallyRegularAt_iff_graphicalDerivative_eq_regular hx hlc⟩

/-- **Theorem 8.40**, universal adjoint inequality. -/
theorem isGraphicallyRegularAt_iff_inner_le (hx : u ∈ S x)
    (hlc : IsLocallyClosedAt (euclideanSvGraph S) (WithLp.toLp 2 (x,u))) :
    IsGraphicallyRegularAt S x u ↔
      ∀ y v, v ∈ coderivative S x u y → ∀ w z, z ∈ graphicalDerivative S x u w → ⟪v,w⟫_ℝ ≤ ⟪y,z⟫_ℝ := by
  rw [isGraphicallyRegularAt_iff_coderivative_eq_regular hlc]
  constructor
  · intro h y v hv
    rw [h, regularCoderivative_eq_upperAdjoint hx] at hv
    exact hv
  · intro h
    apply le_antisymm _ (graphicalDerivative_properties hx).2.2.2.2.2
    rw [regularCoderivative_eq_upperAdjoint hx]
    exact h

/-- The derivatives of a graphically regular mapping are sublinear. -/
theorem IsGraphicallyRegularAt.sublinear (h : IsGraphicallyRegularAt S x u) (hx : u ∈ S x) :
    SvSublinear (graphicalDerivative S x u) ∧ SvSublinear (coderivative S x u) := by
  have hp := graphicalDerivative_properties hx
  rw [(isGraphicallyRegularAt_iff_graphicalDerivative_eq_regular hx h.1).mp h,
    (isGraphicallyRegularAt_iff_coderivative_eq_regular h.1).mp h]
  exact ⟨hp.2.1.2, hp.2.2.2.1.2⟩

end RW
