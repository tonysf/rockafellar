/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Proto-differentiability and inverses
-/

import RockafellarWets.Chapter8.GraphicalRegularity
import RockafellarWets.Chapter6.NormalsToTangentCones
import RockafellarWets.Chapter7.SubdifferentialRegularity
import RockafellarWets.Chapter6.RegularTangentChangeOfCoordinates

open Filter Set Topology

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The set-valued difference quotient in formula 8(14). -/
def mappingDifferenceQuotient (S : E → Set F) (x : E) (u : F) (τ : ℝ) (w : E) : Set F :=
  (fun v ↦ τ⁻¹ • (v - u)) '' S (x + τ • w)

theorem mem_mappingDifferenceQuotient_iff {S : E → Set F} {x w : E} {u z : F} {τ : ℝ}
    (hτ : τ ≠ 0) : z ∈ mappingDifferenceQuotient S x u τ w ↔ u + τ • z ∈ S (x + τ • w) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [smul_smul, hτ] using hv
  · intro h
    exact ⟨_, h, by simp [smul_smul, hτ]⟩

theorem svGraph_mappingDifferenceQuotient {S : E → Set F} {x : E} {u : F} {τ : ℝ}
    (hτ : τ ≠ 0) :
    svGraph (mappingDifferenceQuotient S x u τ) = blowUp (svGraph S) (x,u) τ := by
  ext ⟨w,z⟩
  change z ∈ mappingDifferenceQuotient S x u τ w ↔ _
  rw [mem_mappingDifferenceQuotient_iff hτ]
  constructor
  · intro hz
    refine ⟨(x + τ • w, u + τ • z), hz, ?_⟩
    ext <;> simp [smul_smul, hτ]
  · rintro ⟨⟨x',u'⟩, hu', heq⟩
    change (τ⁻¹ • (x'-x), τ⁻¹ • (u'-u)) = (w,z) at heq
    obtain ⟨hw,hz⟩ := Prod.mk.inj heq
    simpa only [← hw, ← hz, smul_smul, mul_inv_cancel₀ hτ, one_smul, add_sub_cancel] using hu'

theorem svGraph_graphicalDerivative (S : E → Set F) (x : E) (u : F) :
    svGraph (graphicalDerivative S x u) = tangentCone (svGraph S) (x,u) := by
  let L := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  change L.symm ⁻¹' tangentCone (L ⁻¹' svGraph S) (WithLp.toLp 2 (x,u)) = _
  rw [tangentCone_preimage_continuousLinearEquiv]
  ext q
  exact Iff.rfl

/-- Formula 8(15), outer graphical limit of the difference quotients. -/
theorem svGraph_graphicalDerivative_eq_outerLimit (S : E → Set F) (x : E) (u : F) :
    svGraph (graphicalDerivative S x u) = outerSetLimitAlong (𝓝[>] (0:ℝ))
      (fun τ ↦ svGraph (mappingDifferenceQuotient S x u τ)) := by
  rw [svGraph_graphicalDerivative, tangentCone_eq_outerSetLimitAlong]
  apply outerSetLimitAlong_congr
  filter_upwards [self_mem_nhdsWithin] with τ hτ using (svGraph_mappingDifferenceQuotient hτ.ne').symm

/-- Proto-differentiability is full graphical convergence of the difference
quotients to the graphical derivative, as the scale decreases to zero. -/
def IsProtoDifferentiableAt (S : E → Set F) (x : E) (u : F) : Prop :=
  PKConvergesAlong (𝓝[>] (0:ℝ)) (fun τ ↦ svGraph (mappingDifferenceQuotient S x u τ))
    (svGraph (graphicalDerivative S x u))

/-- **Proposition 8.41**, equivalence with geometric derivability. -/
theorem isProtoDifferentiableAt_iff_geometricallyDerivable {S : E → Set F} {x : E} {u : F}
    (hx : u ∈ S x) : IsProtoDifferentiableAt S x u ↔
      IsGeometricallyDerivable (euclideanSvGraph S) (WithLp.toLp 2 (x,u)) := by
  let L := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  change _ ↔ IsGeometricallyDerivable (L ⁻¹' svGraph S) (WithLp.toLp 2 (x,u))
  rw [isGeometricallyDerivable_preimage_continuousLinearEquiv]
  have heq : (fun τ ↦ svGraph (mappingDifferenceQuotient S x u τ)) =ᶠ[𝓝[>] (0:ℝ)] blowUp (svGraph S) (x,u) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ using svGraph_mappingDifferenceQuotient hτ.ne'
  change (_ ∧ _) ↔ IsGeometricallyDerivable (svGraph S) (x,u)
  rw [outerSetLimitAlong_congr heq, innerSetLimitAlong_congr heq, svGraph_graphicalDerivative,
    tangentCone_eq_outerSetLimitAlong, isGeometricallyDerivable_iff (show (x,u) ∈ svGraph S from hx)]
  simp [eq_comm]

/-- Graphical derivatives commute with taking inverse mappings. -/
theorem graphicalDerivative_svInv (S : E → Set F) (x : E) (u : F) :
    graphicalDerivative (svInv S) u x = svInv (graphicalDerivative S x u) := by
  let T := (LinearIsometryEquiv.withLpProdComm 2 ℝ F E).toContinuousLinearEquiv
  have heq : euclideanSvGraph (svInv S) = T ⁻¹' euclideanSvGraph S := rfl
  ext z w
  change WithLp.toLp 2 (z,w) ∈ tangentCone (euclideanSvGraph (svInv S)) _ ↔ _
  rw [heq, tangentCone_preimage_continuousLinearEquiv]
  rfl

/-- **Proposition 8.41**, proto-differentiability of the inverse. -/
theorem isProtoDifferentiableAt_svInv_iff {S : E → Set F} {x : E} {u : F} (hx : u ∈ S x) :
    IsProtoDifferentiableAt (svInv S) u x ↔ IsProtoDifferentiableAt S x u := by
  let T := (LinearIsometryEquiv.withLpProdComm 2 ℝ F E).toContinuousLinearEquiv
  rw [isProtoDifferentiableAt_iff_geometricallyDerivable (show x ∈ svInv S u from hx),
    isProtoDifferentiableAt_iff_geometricallyDerivable hx]
  exact isGeometricallyDerivable_preimage_continuousLinearEquiv T (euclideanSvGraph S) (WithLp.toLp 2 (u,x))

section Regular

variable {P Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]
    {S : P → Set Q} {x : P} {u : Q}

/-- **Proposition 8.41**, graphical regularity implies proto-differentiability. -/
theorem IsGraphicallyRegularAt.isProtoDifferentiableAt (h : IsGraphicallyRegularAt S x u) (hx : u ∈ S x) :
    IsProtoDifferentiableAt S x u :=
  (isProtoDifferentiableAt_iff_geometricallyDerivable hx).mpr
    (isGeometricallyDerivable_of_isClarkeRegularAt (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hx) h)

private theorem graphRegular_inverse {R : P → Set Q} {a : P} {b : Q}
    (hmem : b ∈ R a) (hreg : IsGraphicallyRegularAt R a b) :
    IsGraphicallyRegularAt (svInv R) b a := by
  let T := (LinearIsometryEquiv.withLpProdComm 2 ℝ Q P).toContinuousLinearEquiv
  let p := WithLp.toLp 2 (b,a)
  let C := euclideanSvGraph R
  have hTp : T p ∈ C := hmem
  change IsClarkeRegularAt (T ⁻¹' C) p
  apply (isClarkeRegularAt_iff_tangentCone_eq_regularTangentCone (show p ∈ T ⁻¹' C from hTp)
    (IsLocallyClosedAt.preimage_continuousLinearEquiv T hreg.1)).mpr
  have hr : regularTangentCone (T ⁻¹' C) p = T ⁻¹' regularTangentCone C (T p) :=
    regularTangentCone_preimage (Φ := T) (Φ' := T) T.toContinuousLinearMap.hasStrictFDerivAt C hTp
  rw [tangentCone_preimage_continuousLinearEquiv, hr, tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hTp hreg]

/-- Graphical regularity, like proto-differentiability, is invariant under inverse. -/
theorem isGraphicallyRegularAt_svInv_iff (hx : u ∈ S x) :
    IsGraphicallyRegularAt (svInv S) u x ↔ IsGraphicallyRegularAt S x u :=
  ⟨graphRegular_inverse (show x ∈ svInv S u from hx), graphRegular_inverse hx⟩

end Regular
end RW
