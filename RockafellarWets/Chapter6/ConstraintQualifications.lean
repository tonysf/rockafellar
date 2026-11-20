/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangent and Convexified Normal Constraint Qualifications

The tangent-surjectivity and convexified-normal formulations in Exercise
6.39, with an explicit derivative map. The relative-interior formulation is
separate from these polarity arguments.
-/

import RockafellarWets.Chapter6.ConstraintQualificationDefs
import RockafellarWets.Chapter6.ConvexifiedCones
import RockafellarWets.Chapter6.ConeSeparation

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Exercise 6.39(a): the difference of the target regular tangent cone and
the derivative image of the source regular tangent cone fills the target space. -/
def RegularTangentConstraintQualification (X : Set E) (D : Set F) (A : E →L[ℝ] F)
    (x : E) (u : F) : Prop :=
  regularTangentCone D u + -(A '' regularTangentCone X x) = univ

/-- Exercise 6.39(c): the normal qualification with both normal cones replaced
by their closed convex hulls. -/
def ConvexifiedNormalConstraintQualification (X : Set E) (D : Set F) (A : E →L[ℝ] F)
    (x : E) (u : F) : Prop :=
  ∀ y ∈ convexifiedNormalCone D u, -(A.adjoint y) ∈ convexifiedNormalCone X x → y = 0

/-- The polar of the tangent difference has the adjoint-multiplier
description used in the guide to Exercise 6.39. -/
theorem polarCone_add_neg_image {K : Set E} {L : Set F}
    (A : E →L[ℝ] F) (hK : IsCone K) (hL : IsCone L) :
    polarCone (L + -(A '' K)) =
      {y | y ∈ polarCone L ∧ -(A.adjoint y) ∈ polarCone K} := by
  have himage : IsCone (A '' K) := LinearMap.isCone_image A.toLinearMap hK
  rw [polarCone_add_neg hL himage]
  ext y
  constructor
  · rintro ⟨hyL, hyK⟩
    refine ⟨hyL, ?_⟩
    rw [Set.mem_neg] at hyK
    intro k hk
    have h := hyK (A k) ⟨k, hk, rfl⟩
    simpa only [inner_neg_left, ContinuousLinearMap.adjoint_inner_left] using h
  · rintro ⟨hyL, hyK⟩
    refine ⟨hyL, ?_⟩
    rw [Set.mem_neg]
    rintro z ⟨k, hk, rfl⟩
    simpa only [inner_neg_left, ContinuousLinearMap.adjoint_inner_left] using hyK k hk

/-- **Exercise 6.39**, sufficiency of (c): the convexified qualification
implies the original limiting-normal constraint qualification. -/
theorem ConvexifiedNormalConstraintQualification.normalConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (h : ConvexifiedNormalConstraintQualification X D A x u) :
    NormalConstraintQualification X D A x u := by
  intro y hy hA
  exact h y (normalCone_subset_convexifiedNormalCone D u hy)
    (normalCone_subset_convexifiedNormalCone X x hA)

omit [CompleteSpace E] in
/-- At a Clarke regular point the convexified and limiting normal cones agree. -/
theorem convexifiedNormalCone_eq_normalCone_of_isClarkeRegularAt
    {X : Set E} {x : E} (hreg : IsClarkeRegularAt X x) :
    convexifiedNormalCone X x = normalCone X x := by
  unfold convexifiedNormalCone
  rw [hreg.2, (convex_regularNormalCone X x).convexHull_eq,
    (isClosed_regularNormalCone X x).closure_eq]

/-- **Exercise 6.39**, necessity of (c) in the regular case: convexification
does not change the constraint qualification when both sets are Clarke regular. -/
theorem convexifiedNormalConstraintQualification_iff_normalConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (hXreg : IsClarkeRegularAt X x) (hDreg : IsClarkeRegularAt D u) :
    ConvexifiedNormalConstraintQualification X D A x u ↔
      NormalConstraintQualification X D A x u := by
  unfold ConvexifiedNormalConstraintQualification NormalConstraintQualification
  rw [convexifiedNormalCone_eq_normalCone_of_isClarkeRegularAt hXreg,
    convexifiedNormalCone_eq_normalCone_of_isClarkeRegularAt hDreg]

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Exercise 6.39(a),(c)**: the tangent difference fills the target space
exactly when the convexified-normal multiplier qualification holds. -/
theorem regularTangentConstraintQualification_iff_convexifiedNormalConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (hx : x ∈ X) (hu : u ∈ D)
    (hXlc : IsLocallyClosedAt X x) (hDlc : IsLocallyClosedAt D u) :
    RegularTangentConstraintQualification X D A x u ↔
      ConvexifiedNormalConstraintQualification X D A x u := by
  have himageconv : Convex ℝ (A '' regularTangentCone X x) :=
    (convex_regularTangentCone hx).linear_image A.toLinearMap
  have himagecone : IsCone (A '' regularTangentCone X x) :=
    LinearMap.isCone_image A.toLinearMap (isCone_regularTangentCone hx)
  unfold RegularTangentConstraintQualification ConvexifiedNormalConstraintQualification
  rw [← polarCone_eq_singleton_iff_eq_univ
    ((convex_regularTangentCone hu).add himageconv.neg)
    (isCone_add (isCone_regularTangentCone hu) (isCone_neg himagecone)),
    polarCone_add_neg_image A (isCone_regularTangentCone hx) (isCone_regularTangentCone hu),
    ← convexifiedNormalCone_eq_polarCone_regularTangentCone hu hDlc,
    ← convexifiedNormalCone_eq_polarCone_regularTangentCone hx hXlc]
  constructor
  · intro h y hy hA
    have hm : y ∈ {y | y ∈ convexifiedNormalCone D u ∧
        -(A.adjoint y) ∈ convexifiedNormalCone X x} := ⟨hy, hA⟩
    rw [h] at hm
    exact mem_singleton_iff.1 hm
  · intro h
    apply Subset.antisymm
    · intro y hy
      exact mem_singleton_iff.2 (h y hy.1 hy.2)
    · rintro y rfl
      refine ⟨normalCone_subset_convexifiedNormalCone D u (isCone_normalCone hu).1, ?_⟩
      simpa only [map_zero, neg_zero] using
        normalCone_subset_convexifiedNormalCone X x (isCone_normalCone hx).1

/-- **Exercise 6.39**, sufficiency of (a) for the original normal
constraint qualification. -/
theorem RegularTangentConstraintQualification.normalConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (h : RegularTangentConstraintQualification X D A x u)
    (hx : x ∈ X) (hu : u ∈ D)
    (hXlc : IsLocallyClosedAt X x) (hDlc : IsLocallyClosedAt D u) :
    NormalConstraintQualification X D A x u :=
  ((regularTangentConstraintQualification_iff_convexifiedNormalConstraintQualification
    hx hu hXlc hDlc).1 h).normalConstraintQualification

/-- **Exercise 6.39**, necessity of (a) in the regular case. -/
theorem regularTangentConstraintQualification_iff_normalConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (hx : x ∈ X) (hu : u ∈ D)
    (hXreg : IsClarkeRegularAt X x) (hDreg : IsClarkeRegularAt D u) :
    RegularTangentConstraintQualification X D A x u ↔
      NormalConstraintQualification X D A x u := by
  rw [regularTangentConstraintQualification_iff_convexifiedNormalConstraintQualification
    hx hu hXreg.1 hDreg.1,
    convexifiedNormalConstraintQualification_iff_normalConstraintQualification hXreg hDreg]

end FiniteDimensional

end RW
