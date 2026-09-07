/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangent Cones under a Constraint Qualification

The second and third displays of Theorem 6.31, the tangent-cone companion of
6.14, for `C = {x ∈ X | G(x) ∈ D}`.  The first display, which the book calls
elementary, is in [`ConstraintStructure.lean`](ConstraintStructure.lean).

The book derives the second display from 6.14's limiting-normal inclusion "by
the polarity relation in 6.28(b)".  Taken literally this asks for the polar of
a sum of a linear image and a cone; the proof here does not need it.  A vector
polar to `N_X(x̄)` whose image is polar to `N_D(G(x̄))` pairs nonpositively with
`∇G(x̄)*y + z` term by term, and by 6.14 that is every limiting normal to `C`.
So the second display is one line of Cauchy--Schwarz-free bookkeeping over the
adjoint identity `⟪∇G(x̄)*y, w⟫ = ⟪y, ∇G(x̄)w⟫`.
-/

import RockafellarWets.Chapter6.ConstraintQualification
import RockafellarWets.Chapter6.NormalsToTangentCones

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section ConstraintTangents

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {X : Set E} {D : Set F} {G : E → F} {x : E}

/-- **Theorem 6.31**, second display: under the constraint qualification of
6.14 the linearized regular tangent cone is contained in the regular tangent
cone of the constraint set. -/
theorem regularTangentCone_inter_subset_constrainedPreimage
    (hG : ContDiff ℝ 1 G) (hX : IsClosed X) (hD : IsClosed D)
    (hCQ : ConstraintQualification X G D x)
    (hxC : x ∈ constrainedPreimage X G D) :
    {w : E | w ∈ regularTangentCone X x ∧
        fderiv ℝ G x w ∈ regularTangentCone D (G x)}
      ⊆ regularTangentCone (constrainedPreimage X G D) x := by
  have hCclosed : IsClosed (constrainedPreimage X G D) :=
    hX.inter (hD.preimage hG.continuous)
  have hxX : x ∈ X := hxC.1
  have hxD : G x ∈ D := hxC.2
  rintro w ⟨hwX, hwD⟩
  rw [regularTangentCone_eq_polarCone_normalCone hxX
    (RW.IsClosed.isLocallyClosedAt hX x)] at hwX
  rw [regularTangentCone_eq_polarCone_normalCone hxD
    (RW.IsClosed.isLocallyClosedAt hD (G x))] at hwD
  rw [regularTangentCone_eq_polarCone_normalCone hxC
    (RW.IsClosed.isLocallyClosedAt hCclosed x)]
  intro v hv
  obtain ⟨y, hy, z, hz, hrep⟩ := normalCone_subset_constraintNormals hG hX hD hCQ hv
  have hadj : ⟪w, ContinuousLinearMap.adjoint (fderiv ℝ G x) y⟫_ℝ
      = ⟪fderiv ℝ G x w, y⟫_ℝ := by
    rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have h1 : ⟪w, ContinuousLinearMap.adjoint (fderiv ℝ G x) y⟫_ℝ ≤ 0 := by
    rw [hadj]
    exact hwD y hy
  have h2 : ⟪w, z⟫_ℝ ≤ 0 := hwX z hz
  rw [← hrep, inner_add_right]
  linarith

/-- **Theorem 6.31**, third display: when `X` is Clarke regular at `x̄` and `D`
at `G(x̄)`, the constraint qualification makes the elementary inclusion an
equation. -/
theorem tangentCone_constrainedPreimage_eq
    (hG : ContDiff ℝ 1 G) (hX : IsClosed X) (hD : IsClosed D)
    (hCQ : ConstraintQualification X G D x)
    (hxC : x ∈ constrainedPreimage X G D)
    (hXreg : IsClarkeRegularAt X x) (hDreg : IsClarkeRegularAt D (G x)) :
    tangentCone (constrainedPreimage X G D) x =
      {w : E | w ∈ tangentCone X x ∧ fderiv ℝ G x w ∈ tangentCone D (G x)} := by
  have hGd : HasFDerivAt G (fderiv ℝ G x) x :=
    (hG.differentiable one_ne_zero x).hasFDerivAt
  refine Subset.antisymm (tangentCone_constrainedPreimage_subset hGd) ?_
  have hxX : x ∈ X := hxC.1
  have hxD : G x ∈ D := hxC.2
  have hXeq : tangentCone X x = regularTangentCone X x :=
    (isClarkeRegularAt_iff_tangentCone_eq hxX hXreg.1).1 hXreg
  have hDeq : tangentCone D (G x) = regularTangentCone D (G x) :=
    (isClarkeRegularAt_iff_tangentCone_eq hxD hDreg.1).1 hDreg
  intro w hw
  have hw' : w ∈ {w : E | w ∈ regularTangentCone X x ∧
      fderiv ℝ G x w ∈ regularTangentCone D (G x)} := by
    rw [← hXeq, ← hDeq]
    exact hw
  exact regularTangentCone_subset_tangentCone hxC
    (regularTangentCone_inter_subset_constrainedPreimage hG hX hD hCQ hxC hw')

/-- **Theorem 6.31**, third display: under the same hypotheses the two tangent
cones of the constraint set coincide, `C` being Clarke regular by 6.14. -/
theorem regularTangentCone_constrainedPreimage_eq
    (hG : ContDiff ℝ 1 G) (hX : IsClosed X) (hD : IsClosed D)
    (hCQ : ConstraintQualification X G D x)
    (hxC : x ∈ constrainedPreimage X G D)
    (hXreg : IsClarkeRegularAt X x) (hDreg : IsClarkeRegularAt D (G x)) :
    regularTangentCone (constrainedPreimage X G D) x =
      tangentCone (constrainedPreimage X G D) x := by
  have hCreg := (isClarkeRegularAt_constrainedPreimage hG hX hD hCQ hXreg hDreg).1
  exact ((isClarkeRegularAt_iff_tangentCone_eq hxC hCreg.1).1 hCreg).symm

end ConstraintTangents

end RW
