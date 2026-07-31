/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Minkowski--Weyl Regression Examples

Small boundary examples exercising the H/V equivalence and the unconditional
preimage theorem.
-/

import RockafellarWets.Chapter3.MinkowskiWeyl

open Set

namespace RW

/-! ## Boundary cones and sets -/

/-- The empty-set boundary case for the affine H/V equivalence. -/
example :
    IsHPolyhedral (∅ : Set ℝ) ↔ IsPolyhedral (∅ : Set ℝ) :=
  isHPolyhedral_iff_isPolyhedral

/-- The empty-set boundary case for homogeneous descriptions.  Both sides are
false, because every cone described by either convention contains zero. -/
example :
    IsHPolyhedralCone (∅ : Set ℝ) ↔
      IsFinitelyGeneratedCone (∅ : Set ℝ) :=
  isHPolyhedralCone_iff_isFinitelyGeneratedCone

/-- The zero cone. -/
example :
    IsHPolyhedralCone ({0} : Set ℝ) ↔
      IsFinitelyGeneratedCone ({0} : Set ℝ) :=
  isHPolyhedralCone_iff_isFinitelyGeneratedCone

/-- The full cone. -/
example :
    IsHPolyhedralCone (Set.univ : Set ℝ) ↔
      IsFinitelyGeneratedCone (Set.univ : Set ℝ) :=
  isHPolyhedralCone_iff_isFinitelyGeneratedCone

/-- A one-dimensional simplicial cone. -/
example :
    IsHPolyhedralCone (Set.Ici (0 : ℝ)) ↔
      IsFinitelyGeneratedCone (Set.Ici (0 : ℝ)) :=
  isHPolyhedralCone_iff_isFinitelyGeneratedCone

/-- A proper non-pointed cone: the horizontal line in the plane. -/
example :
    IsHPolyhedralCone ({p : ℝ × ℝ | p.2 = 0}) ↔
      IsFinitelyGeneratedCone ({p : ℝ × ℝ | p.2 = 0}) :=
  isHPolyhedralCone_iff_isFinitelyGeneratedCone

/-! ## Noninjective and nonsurjective preimages -/

/-- Projection onto the first coordinate is noninjective; its preimages still
preserve polyhedrality. -/
example {C : Set ℝ} (hC : IsPolyhedral C) :
    IsPolyhedral
      ((LinearMap.fst ℝ ℝ ℝ) ⁻¹' C : Set (ℝ × ℝ)) :=
  IsPolyhedral.linear_preimage hC (LinearMap.fst ℝ ℝ ℝ)

/-- Inclusion into the first coordinate is nonsurjective; its preimages still
preserve polyhedrality. -/
example {C : Set (ℝ × ℝ)} (hC : IsPolyhedral C) :
    IsPolyhedral
      ((LinearMap.inl ℝ ℝ ℝ) ⁻¹' C : Set ℝ) :=
  IsPolyhedral.linear_preimage hC (LinearMap.inl ℝ ℝ ℝ)

/-- The zero map is simultaneously noninjective and nonsurjective in positive
dimensions. -/
example {C : Set (ℝ × ℝ)} (hC : IsPolyhedral C) :
    IsPolyhedral
      ((0 : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ⁻¹' C) :=
  IsPolyhedral.linear_preimage hC 0

end RW
