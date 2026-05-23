/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3B: Cones

This file formalizes the basic cone calculus used throughout Chapter 3:
- cone structure of horizon cones
- Exercise 3.7: a cone is convex iff it is closed under addition
-/

import RockafellarWets.Chapter3.HorizonCones

open Set Bornology
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsCone.smul_mem {C : Set E} (hC : IsCone C) {x : E} (hx : x ∈ C) {c : ℝ}
    (hc : 0 ≤ c) : c • x ∈ C := by
  rcases hc.eq_or_lt with rfl | hc'
  · simpa using hC.1
  · exact hC.2 hx hc'

/-- Every horizon cone is a cone. -/
theorem isCone_horizonCone (C : Set E) : IsCone (horizonCone C) := by
  refine ⟨zero_mem_horizonCone C, ?_⟩
  intro x hx c hc
  rcases hx with rfl | hx
  · simp [horizonCone]
  · exact Set.mem_insert_of_mem 0 <| smul_mem_asymptoticCone hc.le hx

/-- A convex cone is closed under addition. -/
theorem add_mem_of_convex_isCone {C : Set E} (hconv : Convex ℝ C) (hcone : IsCone C)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) : x + y ∈ C := by
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ C :=
    hconv hx hy (by norm_num) (by norm_num) (by norm_num)
  have htwo :
      (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈ C :=
    hcone.smul_mem hmid (by norm_num)
  simpa [smul_add, two_smul] using htwo

/-- **Exercise 3.7** (direction `(b) → (a)`): for a cone, convexity is
equivalent to closure under addition. -/
theorem IsCone.convex_iff_add_mem {C : Set E} (hcone : IsCone C) :
    Convex ℝ C ↔ ∀ ⦃x y : E⦄, x ∈ C → y ∈ C → x + y ∈ C := by
  constructor
  · intro hconv x y hx hy
    exact add_mem_of_convex_isCone hconv hcone hx hy
  · intro hadd x hx y hy a b ha hb hab
    exact hadd (hcone.smul_mem hx ha) (hcone.smul_mem hy hb)

/-- **Proposition 3.8**: the largest linear subspace contained in a convex cone
is the set of cone elements whose negatives are also in the cone. -/
def linealitySubmoduleOfConvexCone {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) : Submodule ℝ E where
  carrier := {x | x ∈ C ∧ -x ∈ C}
  zero_mem' := ⟨hcone.1, by simpa using hcone.1⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨add_mem_of_convex_isCone hconv hcone hx.1 hy.1, ?_⟩
    have hneg : (-x) + (-y) ∈ C := add_mem_of_convex_isCone hconv hcone hx.2 hy.2
    simpa [neg_add, add_comm] using hneg
  smul_mem' := by
    intro a x hx
    by_cases ha : 0 ≤ a
    · refine ⟨hcone.smul_mem hx.1 ha, ?_⟩
      have hneg : a • (-x) ∈ C := hcone.smul_mem hx.2 ha
      simpa [smul_neg] using hneg
    · have hnega : 0 ≤ -a := le_of_lt (neg_pos.mpr (lt_of_not_ge ha))
      refine ⟨?_, ?_⟩
      · have hpos : (-a) • (-x) ∈ C := hcone.smul_mem hx.2 hnega
        simpa [neg_smul, smul_neg] using hpos
      · have hpos : (-a) • x ∈ C := hcone.smul_mem hx.1 hnega
        simpa [neg_smul] using hpos

@[simp] theorem mem_linealitySubmoduleOfConvexCone {C : Set E}
    {hconv : Convex ℝ C} {hcone : IsCone C} {x : E} :
    x ∈ linealitySubmoduleOfConvexCone hconv hcone ↔ x ∈ C ∧ -x ∈ C :=
  Iff.rfl

/-- The lineality submodule has the book's carrier `K ∩ (-K)`. -/
theorem linealitySubmoduleOfConvexCone_eq_inter_neg {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) :
    (linealitySubmoduleOfConvexCone hconv hcone : Set E) = C ∩ -C := by
  ext x
  simp [Set.mem_neg]

/-- The lineality submodule is contained in the cone. -/
theorem linealitySubmoduleOfConvexCone_subset {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) :
    (linealitySubmoduleOfConvexCone hconv hcone : Set E) ⊆ C := by
  intro x hx
  exact hx.1

/-- **Proposition 3.8** (maximality): every linear subspace contained in a
convex cone is contained in its lineality subspace. -/
theorem submodule_subset_linealitySubmoduleOfConvexCone {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) (M : Submodule ℝ E)
    (hM : (M : Set E) ⊆ C) :
    (M : Set E) ⊆ linealitySubmoduleOfConvexCone hconv hcone := by
  intro x hx
  exact ⟨hM hx, hM (M.neg_mem hx)⟩

/-- **Proposition 3.8**: the smallest linear subspace containing a convex cone
is the set of differences of cone elements. -/
def differenceSubmoduleOfConvexCone {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) : Submodule ℝ E where
  carrier := {z | ∃ x ∈ C, ∃ y ∈ C, x - y = z}
  zero_mem' := ⟨0, hcone.1, 0, hcone.1, by simp⟩
  add_mem' := by
    rintro z w ⟨x, hx, y, hy, rfl⟩ ⟨u, hu, v, hv, rfl⟩
    refine
      ⟨x + u, add_mem_of_convex_isCone hconv hcone hx hu,
        y + v, add_mem_of_convex_isCone hconv hcone hy hv, ?_⟩
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  smul_mem' := by
    intro a z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    by_cases ha : 0 ≤ a
    · refine ⟨a • x, hcone.smul_mem hx ha, a • y, hcone.smul_mem hy ha, ?_⟩
      simp [smul_sub]
    · have hnega : 0 ≤ -a := le_of_lt (neg_pos.mpr (lt_of_not_ge ha))
      refine ⟨(-a) • y, hcone.smul_mem hy hnega,
        (-a) • x, hcone.smul_mem hx hnega, ?_⟩
      simp [sub_eq_add_neg, add_comm]

@[simp] theorem mem_differenceSubmoduleOfConvexCone {C : Set E}
    {hconv : Convex ℝ C} {hcone : IsCone C} {z : E} :
    z ∈ differenceSubmoduleOfConvexCone hconv hcone ↔
      ∃ x ∈ C, ∃ y ∈ C, x - y = z :=
  Iff.rfl

/-- The difference submodule has the book's carrier `K - K`. -/
theorem differenceSubmoduleOfConvexCone_eq_sub {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) :
    (differenceSubmoduleOfConvexCone hconv hcone : Set E) = C - C := by
  ext x
  simp [Set.mem_sub]

/-- The cone is contained in its difference submodule. -/
theorem subset_differenceSubmoduleOfConvexCone {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) :
    C ⊆ differenceSubmoduleOfConvexCone hconv hcone := by
  intro x hx
  exact ⟨x, hx, 0, hcone.1, by simp⟩

/-- **Proposition 3.8** (minimality): the difference submodule of a convex cone
is contained in every linear subspace containing the cone. -/
theorem differenceSubmoduleOfConvexCone_subset_submodule {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) (M : Submodule ℝ E)
    (hM : C ⊆ (M : Set E)) :
    (differenceSubmoduleOfConvexCone hconv hcone : Set E) ⊆ M := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact M.sub_mem (hM hx) (hM hy)

/-- **Proposition 3.8** (subspace criterion): a convex cone is a linear
subspace exactly when it is closed under negation. -/
theorem exists_submodule_eq_iff_neg_mem {C : Set E}
    (hconv : Convex ℝ C) (hcone : IsCone C) :
    (∃ M : Submodule ℝ E, (M : Set E) = C) ↔
      ∀ ⦃x : E⦄, x ∈ C → -x ∈ C := by
  constructor
  · rintro ⟨M, rfl⟩ x hx
    exact M.neg_mem hx
  · intro hneg
    refine ⟨linealitySubmoduleOfConvexCone hconv hcone, ?_⟩
    apply le_antisymm
    · exact linealitySubmoduleOfConvexCone_subset hconv hcone
    · intro x hx
      exact ⟨hx, hneg hx⟩

end RW
