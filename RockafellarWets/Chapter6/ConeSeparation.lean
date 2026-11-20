/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Separation of Convex Cones

Exercise 6.48(a)--(b). A hyperplane separating two cones can be taken through
the origin. Its nonzero normal belongs to the intersection of the first
polar and the negative of the second polar. Proper separation additionally
requires a strict inequality between some pair of points.

The criterion in (b) is sufficient for proper separation; it is not stated
as a necessary condition. Part (c) is in `StrictConeSeparation.lean`.
-/

import RockafellarWets.Chapter6.Polarity
import RockafellarWets.Chapter3.HomogeneousCompletion

open Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two cones are separated by a hyperplane through the origin with a
nonzero normal. The first cone lies on its nonpositive side. -/
def ConesSeparated (K L : Set E) : Prop :=
  ∃ v : E, v ≠ 0 ∧ (∀ x ∈ K, ⟪v, x⟫_ℝ ≤ 0) ∧ ∀ y ∈ L, 0 ≤ ⟪v, y⟫_ℝ

/-- Proper separation requires that the two cones do not both lie entirely
in the separating hyperplane. -/
def ConesProperlySeparated (K L : Set E) : Prop :=
  ∃ v : E, v ≠ 0 ∧ (∀ x ∈ K, ⟪v, x⟫_ℝ ≤ 0) ∧
    (∀ y ∈ L, 0 ≤ ⟪v, y⟫_ℝ) ∧ ∃ x ∈ K, ∃ y ∈ L, ⟪v, x⟫_ℝ < ⟪v, y⟫_ℝ

/-- Negating a cone preserves the cone property. -/
theorem isCone_neg {K : Set E} (hK : IsCone K) : IsCone (-K) := by
  refine ⟨by simpa using hK.1, ?_⟩
  intro x hx c hc
  rw [Set.mem_neg] at hx ⊢
  simpa only [smul_neg] using hK.2 hx hc

/-- The polar of the difference of two cones is the intersection appearing
throughout Exercise 6.48. -/
theorem polarCone_add_neg {K L : Set E} (hK : IsCone K) (hL : IsCone L) :
    polarCone (K + -L) = polarCone K ∩ -polarCone L := by
  ext v
  constructor
  · intro hv
    refine ⟨fun x hx ↦ ?_, ?_⟩
    · have h := hv (x + 0) (Set.mem_add.2 ⟨x, hx, 0, by simpa using hL.1, rfl⟩)
      simpa using h
    · rw [Set.mem_neg]
      intro y hy
      have h := hv (0 + -y) (Set.mem_add.2 ⟨0, hK.1, -y, by simpa, rfl⟩)
      simpa using h
  · rintro ⟨hvK, hvL⟩ z ⟨x, hx, y, hy, rfl⟩
    rw [Set.mem_neg] at hvL hy
    have h := hvL (-y) hy
    simp only [inner_neg_left, inner_neg_right, neg_neg] at h
    simpa only [inner_add_right] using add_nonpos (hvK x hx) h

/-- The homogeneous separator definition agrees with ordinary affine
hyperplane separation for cones, since both cones contain zero. -/
theorem conesSeparated_iff_exists_affine_separator {K L : Set E}
    (hK : IsCone K) (hL : IsCone L) :
    ConesSeparated K L ↔ ∃ (v : E) (c : ℝ), v ≠ 0 ∧
      (∀ x ∈ K, ⟪v, x⟫_ℝ ≤ c) ∧ ∀ y ∈ L, c ≤ ⟪v, y⟫_ℝ := by
  constructor
  · rintro ⟨v, hv, hleft, hright⟩
    exact ⟨v, 0, hv, hleft, hright⟩
  · rintro ⟨v, c, hv, hleft, hright⟩
    have hc0 : c = 0 := by
      have h1 := hleft 0 hK.1
      have h2 := hright 0 hL.1
      simp only [inner_zero_right] at h1 h2
      exact le_antisymm h2 h1
    subst c
    exact ⟨v, hv, hleft, hright⟩

/-- A separating normal is a nonzero point of the polar intersection. -/
theorem conesSeparated_iff_exists_nonzero_polar_intersection (K L : Set E) :
    ConesSeparated K L ↔ ∃ v ∈ polarCone K ∩ -polarCone L, v ≠ 0 := by
  constructor
  · rintro ⟨v, hv, hleft, hright⟩
    refine ⟨v, ⟨hleft, ?_⟩, hv⟩
    rw [Set.mem_neg]
    intro y hy
    simpa using neg_nonpos.2 (hright y hy)
  · rintro ⟨v, ⟨hleft, hright⟩, hv⟩
    refine ⟨v, hv, hleft, fun y hy ↦ ?_⟩
    rw [Set.mem_neg] at hright
    simpa using hright y hy

/-- **Exercise 6.48(a)**, polar criterion for separation. -/
theorem conesSeparated_iff_polar_intersection_ne_singleton (K L : Set E) :
    ConesSeparated K L ↔ polarCone K ∩ -polarCone L ≠ ({0} : Set E) := by
  rw [conesSeparated_iff_exists_nonzero_polar_intersection]
  constructor
  · rintro ⟨v, hv, hv0⟩ hzero
    rw [hzero] at hv
    exact hv0 (mem_singleton_iff.1 hv)
  · intro hne
    by_contra h
    push_neg at h
    apply hne
    apply Subset.antisymm
    · exact fun v hv ↦ mem_singleton_iff.2 (h v hv)
    · intro v hv
      rcases mem_singleton_iff.1 hv with rfl
      simp

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- A convex cone has zero polar precisely when it is the entire ambient
space; convexity upgrades density obtained from bipolarity to equality. -/
theorem polarCone_eq_singleton_iff_eq_univ {K : Set E}
    (hconv : Convex ℝ K) (hcone : IsCone K) :
    polarCone K = ({0} : Set E) ↔ K = Set.univ := by
  constructor
  · intro hzero
    have hcl : closure K = Set.univ := by
      rw [← conicHull_eq_self_of_convex_isCone hconv hcone,
        ← polarCone_bipolar, hzero, polarCone_singleton_zero]
    have hpointed : IsPointed (polarCone K) := by
      rw [hzero]
      intro n z hz _ i
      exact mem_singleton_iff.1 (hz i)
    have hint := (interior_nonempty_iff_isPointed_polarCone hconv hcone).2 hpointed
    have hi : interior K = Set.univ := by
      rw [← hconv.interior_closure_eq_interior_of_nonempty_interior hint, hcl,
        interior_univ]
    apply eq_univ_of_forall
    intro x
    exact interior_subset (by rw [hi]; trivial)
  · rintro rfl
    exact polarCone_univ

/-- **Exercise 6.48(a)**: two convex cones can be separated exactly when
their difference fails to fill the ambient space. -/
theorem conesSeparated_iff_add_neg_ne_univ {K L : Set E}
    (hKconv : Convex ℝ K) (hK : IsCone K) (hLconv : Convex ℝ L) (hL : IsCone L) :
    ConesSeparated K L ↔ K + -L ≠ Set.univ := by
  rw [conesSeparated_iff_polar_intersection_ne_singleton, ← polarCone_add_neg hK hL,
    ne_eq, ne_eq, polarCone_eq_singleton_iff_eq_univ
      (hKconv.add hLconv.neg) (isCone_add hK (isCone_neg hL))]

/-- **Exercise 6.48(b)**: the two printed sufficient conditions for proper
separation are equivalent to each other. -/
theorem proper_cone_separation_criteria_iff {K L : Set E}
    (hKconv : Convex ℝ K) (hK : IsCone K) (hLconv : Convex ℝ L) (hL : IsCone L) :
    (K + -L ≠ Set.univ ∧ (interior (K + -L)).Nonempty) ↔
      polarCone K ∩ -polarCone L ≠ ({0} : Set E) ∧
        IsPointed (polarCone K ∩ -polarCone L) := by
  rw [← conesSeparated_iff_add_neg_ne_univ hKconv hK hLconv hL,
    conesSeparated_iff_polar_intersection_ne_singleton,
    interior_nonempty_iff_isPointed_polarCone (hKconv.add hLconv.neg)
      (isCone_add hK (isCone_neg hL)), polarCone_add_neg hK hL]

/-- **Exercise 6.48(b)**: a nonfull difference with nonempty interior
guarantees proper separation. -/
theorem conesProperlySeparated_of_add_neg_ne_univ_of_interior_nonempty
    {K L : Set E} (hKconv : Convex ℝ K) (hK : IsCone K)
    (hLconv : Convex ℝ L) (hL : IsCone L)
    (hne : K + -L ≠ Set.univ) (hint : (interior (K + -L)).Nonempty) :
    ConesProperlySeparated K L := by
  obtain ⟨v, hv, hleft, hright⟩ :=
    (conesSeparated_iff_add_neg_ne_univ hKconv hK hLconv hL).2 hne
  have hvpolar : v ∈ polarCone (K + -L) := by
    rw [polarCone_add_neg hK hL]
    refine ⟨hleft, ?_⟩
    rw [Set.mem_neg]
    intro y hy
    simpa using neg_nonpos.2 (hright y hy)
  obtain ⟨w, hw⟩ := hint
  have hstrict := (mem_interior_iff_inner_lt_zero_on_polarCone
    (hKconv.add hLconv.neg) (isCone_add hK (isCone_neg hL))).1 hw v hvpolar hv
  obtain ⟨x, hx, z, hz, rfl⟩ := interior_subset hw
  refine ⟨v, hv, hleft, hright, x, hx, -z, ?_, ?_⟩
  · exact Set.mem_neg.1 hz
  · rw [inner_add_right] at hstrict
    rw [inner_neg_right]
    linarith

/-- The polar-intersection form of the sufficient proper-separation
condition in Exercise 6.48(b). -/
theorem conesProperlySeparated_of_polar_intersection
    {K L : Set E} (hKconv : Convex ℝ K) (hK : IsCone K)
    (hLconv : Convex ℝ L) (hL : IsCone L)
    (hne : polarCone K ∩ -polarCone L ≠ ({0} : Set E))
    (hpointed : IsPointed (polarCone K ∩ -polarCone L)) :
    ConesProperlySeparated K L := by
  obtain ⟨hdiff, hint⟩ := (proper_cone_separation_criteria_iff hKconv hK hLconv hL).2
    ⟨hne, hpointed⟩
  exact conesProperlySeparated_of_add_neg_ne_univ_of_interior_nonempty
    hKconv hK hLconv hL hdiff hint

end FiniteDimensional

end RW
