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

end RW
