/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Almost Strict Separation of Closed Convex Cones

Exercise 6.48(c). The algebraic pointedness and polar-interior equivalences
hold in every finite dimension. Literal separation by complementary open
half-spaces requires a nonzero normal, so its equivalence additionally needs
a nontrivial ambient space. The zero-dimensional obstruction is proved below.
-/

import RockafellarWets.Chapter6.ConeSeparation
import RockafellarWets.Chapter3.SetOperations

open Set
open scoped BigOperators InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The nonzero portions of two cones lie in complementary open half-spaces
through the origin, with a nonzero normal defining the hyperplane. -/
def ConesAlmostStrictlySeparated (K L : Set E) : Prop :=
  ∃ v : E, v ≠ 0 ∧ (∀ x ∈ K, x ≠ 0 → ⟪v, x⟫_ℝ < 0) ∧
    ∀ y ∈ L, y ≠ 0 → 0 < ⟪v, y⟫_ℝ

omit [InnerProductSpace ℝ E] in
private theorem isPointed_neg_of_isPointed {K : Set E} (hK : IsPointed K) :
    IsPointed (-K) := by
  intro n z hz hsum i
  have hnegmem : ∀ j, -z j ∈ K := fun j ↦ by simpa using hz j
  have hnegsum : (∑ j, -z j) = 0 := by
    rw [Finset.sum_neg_distrib, hsum, neg_zero]
  simpa using hK n (fun j ↦ -z j) hnegmem hnegsum i

omit [InnerProductSpace ℝ E] in
private theorem left_eq_zero_of_add_eq_zero_of_isPointed
    {K : Set E} (hK : IsPointed K) {a b : E} (ha : a ∈ K) (hb : b ∈ K)
    (hab : a + b = 0) : a = 0 := by
  have h := hK 2 (fun i : Fin 2 ↦ if i = 0 then a else b)
    (by intro i; fin_cases i <;> simp [ha, hb])
    (by simpa [Fin.sum_univ_two] using hab) 0
  simpa using h

/-- The difference of convex cones is pointed exactly when the factors are
pointed and their intersection contains only zero. No closedness is needed. -/
theorem isPointed_add_neg_iff {K L : Set E}
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) (hK : IsCone K) (hL : IsCone L) :
    IsPointed (K + -L) ↔ IsPointed K ∧ IsPointed L ∧ K ∩ L = ({0} : Set E) := by
  have hKD : K ⊆ K + -L := fun a ha ↦
    ⟨a, ha, 0, by simpa using hL.1, by simp⟩
  have hnegLD : -L ⊆ K + -L := fun b hb ↦
    ⟨0, hK.1, b, hb, by simp⟩
  constructor
  · intro hD
    have hKpointed : IsPointed K := hD.mono hKD
    have hLpointed : IsPointed L := by
      simpa using isPointed_neg_of_isPointed (hD.mono hnegLD)
    refine ⟨hKpointed, hLpointed, Subset.antisymm ?_ ?_⟩
    · intro z hz
      have hzD : z ∈ K + -L := hKD hz.1
      have hnegzD : -z ∈ K + -L := hnegLD (by simpa using hz.2)
      exact mem_singleton_iff.2
        (left_eq_zero_of_add_eq_zero_of_isPointed hD hzD hnegzD (by simp))
    · rintro z rfl
      exact ⟨hK.1, hL.1⟩
  · rintro ⟨hKpointed, hLpointed, hinter⟩ n z hz hsum i
    have hdecomp : ∀ j, ∃ a ∈ K, ∃ b ∈ -L, a + b = z j := fun j ↦ hz j
    choose a ha b hb hab using hdecomp
    have hbneg : ∀ j, -b j ∈ L := fun j ↦ by simpa using hb j
    have hcancel : (∑ j, a j) + ∑ j, b j = 0 := by
      rw [← Finset.sum_add_distrib]
      simpa only [hab] using hsum
    have heq : (∑ j, a j) = ∑ j, -b j := by
      rw [Finset.sum_neg_distrib, eq_neg_iff_add_eq_zero]
      exact hcancel
    have hsumK : (∑ j, a j) ∈ K :=
      sum_mem_of_convex_isCone hKconv hK Finset.univ a (fun j _ ↦ ha j)
    have hsumL : (∑ j, -b j) ∈ L :=
      sum_mem_of_convex_isCone hLconv hL Finset.univ (fun j ↦ -b j)
        (fun j _ ↦ hbneg j)
    have hsumKzero : (∑ j, a j) = 0 := by
      have hm : (∑ j, a j) ∈ K ∩ L := ⟨hsumK, by rw [heq]; exact hsumL⟩
      simpa only [hinter, mem_singleton_iff] using hm
    have ha0 : a i = 0 := hKpointed n a ha hsumKzero i
    have hb0 : b i = 0 := by
      simpa using hLpointed n (fun j ↦ -b j) hbneg (heq.symm.trans hsumKzero) i
    rw [← hab i, ha0, hb0, add_zero]

/-- In a zero-dimensional ambient space, there is no nonzero normal with
which to define complementary open half-spaces. -/
theorem not_conesAlmostStrictlySeparated_of_subsingleton [Subsingleton E] (K L : Set E) :
    ¬ ConesAlmostStrictlySeparated K L := by
  rintro ⟨v, hv, -⟩
  exact hv (Subsingleton.elim v 0)

/-- The zero-dimensional correction to Exercise 6.48(c) is necessary:
the closed zero cones have a pointed difference but no literal almost strict
separator. -/
theorem zeroCones_almostStrictSeparation_obstruction [Subsingleton E] :
    IsPointed (closure (({0} : Set E) + -({0} : Set E))) ∧
      ¬ ConesAlmostStrictlySeparated ({0} : Set E) ({0} : Set E) := by
  refine ⟨?_, not_conesAlmostStrictlySeparated_of_subsingleton _ _⟩
  intro n z _ _ i
  exact Subsingleton.elim (z i) 0

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The difference of closed cones with trivial intersection is closed. -/
theorem isClosed_add_neg_of_inter_eq_singleton_zero {K L : Set E}
    (hKclosed : IsClosed K) (hLclosed : IsClosed L) (hK : IsCone K) (hL : IsCone L)
    (hinter : K ∩ L = ({0} : Set E)) : IsClosed (K + -L) := by
  apply isClosed_add_of_horizonCone_no_cancel hKclosed hLclosed.neg
  intro u v hu hv huv
  rw [horizonCone_eq_self_of_isClosed_isCone hKclosed hK] at hu
  rw [horizonCone_eq_self_of_isClosed_isCone hLclosed.neg (isCone_neg hL)] at hv
  have hvL : -v ∈ L := by simpa using hv
  have huL : u ∈ L := by
    rw [eq_neg_iff_add_eq_zero.mpr huv]
    exact hvL
  have hu0 : u = 0 := by
    have hm : u ∈ K ∩ L := ⟨hu, huL⟩
    simpa only [hinter, mem_singleton_iff] using hm
  exact ⟨hu0, by simpa [hu0] using huv⟩

/-- **Exercise 6.48(c)**, the pointedness criterion, including dimension
zero: the closed difference is pointed exactly when the two closed convex
cones are pointed and intersect only at zero. -/
theorem isPointed_closure_add_neg_iff {K L : Set E}
    (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) (hK : IsCone K) (hL : IsCone L) :
    IsPointed (closure (K + -L)) ↔
      IsPointed K ∧ IsPointed L ∧ K ∩ L = ({0} : Set E) := by
  constructor
  · intro h
    exact (isPointed_add_neg_iff hKconv hLconv hK hL).1 (h.mono subset_closure)
  · intro h
    rw [(isClosed_add_neg_of_inter_eq_singleton_zero hKclosed hLclosed hK hL h.2.2).closure_eq]
    exact (isPointed_add_neg_iff hKconv hLconv hK hL).2 h

/-- **Exercise 6.48(c)**, the polar-interior criterion. This algebraic
equivalence is valid also in dimension zero. -/
theorem isPointed_closure_add_neg_iff_interior_polar_intersection_nonempty
    {K L : Set E} (hK : IsCone K) (hL : IsCone L) :
    IsPointed (closure (K + -L)) ↔
      (interior (polarCone K) ∩ -interior (polarCone L)).Nonempty := by
  have hnegInterior : interior (-polarCone L) = -interior (polarCone L) := by
    simpa only [Homeomorph.coe_neg, Set.image_neg_eq_neg] using
      ((Homeomorph.neg E).image_interior (polarCone L)).symm
  rw [← interior_polarCone_nonempty_iff_isPointed isClosed_closure
    (isCone_add hK (isCone_neg hL)).closure,
    polarCone_closure, polarCone_add_neg hK hL, interior_inter, hnegInterior]

/-- **Exercise 6.48(c)**, literal almost strict separation. The nontrivial
ambient-space assumption is necessary because the separating normal must be
nonzero, even when both cones contain only zero. -/
theorem conesAlmostStrictlySeparated_iff_interior_polar_intersection_nonempty
    [Nontrivial E] {K L : Set E} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hK : IsCone K) (hL : IsCone L) :
    ConesAlmostStrictlySeparated K L ↔
      (interior (polarCone K) ∩ -interior (polarCone L)).Nonempty := by
  constructor
  · rintro ⟨v, -, hleft, hright⟩
    refine ⟨v, ?_, ?_⟩
    · apply (mem_interior_polarCone_iff_inner_lt_zero hKclosed hK).2
      intro a ha ha0
      simpa only [real_inner_comm] using hleft a ha ha0
    · rw [Set.mem_neg]
      apply (mem_interior_polarCone_iff_inner_lt_zero hLclosed hL).2
      intro b hb hb0
      rw [inner_neg_right, real_inner_comm]
      exact neg_lt_zero.2 (hright b hb hb0)
  · rintro ⟨v, hvK, hvL⟩
    have hleft : ∀ a ∈ K, a ≠ 0 → ⟪v, a⟫_ℝ < 0 := by
      intro a ha ha0
      simpa only [real_inner_comm] using
        (mem_interior_polarCone_iff_inner_lt_zero hKclosed hK).1 hvK a ha ha0
    have hright : ∀ b ∈ L, b ≠ 0 → 0 < ⟪v, b⟫_ℝ := by
      intro b hb hb0
      rw [Set.mem_neg] at hvL
      have h := (mem_interior_polarCone_iff_inner_lt_zero hLclosed hL).1 hvL b hb hb0
      simpa only [inner_neg_right, real_inner_comm, neg_lt_zero] using h
    by_cases hv0 : v = 0
    · obtain ⟨u, hu⟩ := exists_ne (0 : E)
      refine ⟨u, hu, ?_, ?_⟩
      · intro a ha ha0
        have h := hleft a ha ha0
        simp [hv0] at h
      · intro b hb hb0
        have h := hright b hb hb0
        simp [hv0] at h
    · exact ⟨v, hv0, hleft, hright⟩

/-- **Exercise 6.48(c)**: in positive dimension, almost strict separation
is equivalent to pointedness of the closed difference. -/
theorem conesAlmostStrictlySeparated_iff_isPointed_closure_add_neg
    [Nontrivial E] {K L : Set E} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hK : IsCone K) (hL : IsCone L) :
    ConesAlmostStrictlySeparated K L ↔ IsPointed (closure (K + -L)) := by
  rw [conesAlmostStrictlySeparated_iff_interior_polar_intersection_nonempty
    hKclosed hLclosed hK hL,
    isPointed_closure_add_neg_iff_interior_polar_intersection_nonempty hK hL]

/-- **Exercise 6.48(c)**: in positive dimension, two closed convex cones
are almost strictly separated exactly when both are pointed and their
intersection is the zero cone. -/
theorem conesAlmostStrictlySeparated_iff_pointed_and_inter_eq_singleton_zero
    [Nontrivial E] {K L : Set E} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) (hK : IsCone K) (hL : IsCone L) :
    ConesAlmostStrictlySeparated K L ↔
      IsPointed K ∧ IsPointed L ∧ K ∩ L = ({0} : Set E) := by
  rw [conesAlmostStrictlySeparated_iff_isPointed_closure_add_neg hKclosed hLclosed hK hL,
    isPointed_closure_add_neg_iff hKclosed hLclosed hKconv hLconv hK hL]

end FiniteDimensional

end RW
