/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2B: Level Sets and Intersections

This file formalizes Section B of Chapter 2 of Rockafellar & Wets,
"Variational Analysis":
- Proposition 2.7: Level sets of convex functions are convex
- Proposition 2.9: Intersections, suprema, and limsup preserve convexity
- Example 2.10: Polyhedral convex sets
-/

import RockafellarWets.Chapter1.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Order.Basic

set_option linter.style.openClassical false

open Set Filter Topology EReal Classical

noncomputable section

namespace RW

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## Proposition 2.7: Level sets of convex functions are convex -/

/-- **Proposition 2.7**: Every sublevel set of a convex function is convex.
This is `ConvexOn.convex_le` in Mathlib. -/
theorem convex_levelSet_of_convexOn {S : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ S f) (α : ℝ) :
    Convex ℝ {x ∈ S | f x ≤ α} :=
  hf.convex_le α

/-- **Proposition 2.7 (EReal version)**: Sublevel sets of a convex
EReal-valued function are convex. -/
theorem convex_levelSet_of_convex_ereal
    {f : E → EReal}
    (hf : ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y)
    (α : EReal) :
    Convex ℝ (levelSet f α) := by
  intro x hx y hy a b ha hb hab
  simp only [levelSet, mem_setOf_eq] at hx hy ⊢
  have ha' : (0 : EReal) ≤ (a : EReal) := EReal.coe_nonneg.mpr ha
  have hb' : (0 : EReal) ≤ (b : EReal) := EReal.coe_nonneg.mpr hb
  calc f (a • x + b • y)
      ≤ (a : EReal) * f x + (b : EReal) * f y := hf ha hb hab
    _ ≤ (a : EReal) * α + (b : EReal) * α := by gcongr
    _ = ((a : EReal) + (b : EReal)) * α :=
        (EReal.right_distrib_of_nonneg ha' hb').symm
    _ = α := by rw [← EReal.coe_add, hab, EReal.coe_one, one_mul]

/-- Strict sublevel sets of a convex function are also convex. -/
theorem convex_strictLevelSet_of_convex_ereal
    {f : E → EReal}
    (hf : ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y)
    (α : EReal) :
    Convex ℝ (strictLevelSet f α) := by
  -- Write strictLevelSet as a directed union of levelSets indexed by {β // β < α}
  have heq : strictLevelSet f α =
      ⋃ (β : {β : EReal // β < α}), levelSet f β.val := by
    ext x
    simp only [strictLevelSet, levelSet, mem_setOf_eq, mem_iUnion]
    constructor
    · intro hx; exact ⟨⟨f x, hx⟩, le_refl _⟩
    · rintro ⟨⟨β, hβα⟩, hfx⟩; exact lt_of_le_of_lt hfx hβα
  rw [heq]
  apply Directed.convex_iUnion
  · -- The family is directed (monotone)
    intro ⟨β₁, h₁⟩ ⟨β₂, h₂⟩
    exact ⟨⟨max β₁ β₂, max_lt h₁ h₂⟩,
      levelSet_monotone f (le_max_left _ _),
      levelSet_monotone f (le_max_right _ _)⟩
  · intro ⟨β, _⟩
    exact convex_levelSet_of_convex_ereal hf β

/-! ## Proposition 2.9: Intersections and suprema preserve convexity -/

/-- **Proposition 2.9 (a)**: An arbitrary intersection of convex sets is convex.
This is `convex_iInter` in Mathlib. -/
theorem convex_iInter {ι : Type*} {S : ι → Set E}
    (hS : ∀ i, Convex ℝ (S i)) :
    Convex ℝ (⋂ i, S i) :=
  _root_.convex_iInter hS

/-- **Proposition 2.9 (b)**: The pointwise supremum of a family of convex
functions is convex. Equivalently, `f = sup_i f_i` is convex when each `f_i`
is convex. This follows because a sublevel set of the sup is the intersection
of sublevel sets. -/
theorem convexOn_iSup {ι : Type*} [Nonempty ι] [Finite ι]
    {S : Set E} {f : ι → E → ℝ}
    (hS : Convex ℝ S)
    (hf : ∀ i, ConvexOn ℝ S (f i)) :
    ConvexOn ℝ S (fun x => ⨆ i, f i x) := by
  cases nonempty_fintype ι
  constructor
  · exact hS
  · intro x hx y hy a b ha hb hab
    apply ciSup_le
    intro i
    calc f i (a • x + b • y)
        ≤ a * f i x + b * f i y := (hf i).2 hx hy ha hb hab
      _ ≤ a * (⨆ j, f j x) + b * (⨆ j, f j y) := by
          gcongr
          · exact le_ciSup (finite_range (fun j => f j x)).bddAbove i
          · exact le_ciSup (finite_range (fun j => f j y)).bddAbove i

/-! ## Example 2.10: Polyhedral convex sets

A polyhedral convex set is the intersection of finitely many half-spaces.
These are always convex (as intersections of convex sets). -/

/-- **Example 2.10**: A set defined by finitely many linear inequalities
`{x | ∀ i, ⟪aᵢ, x⟫ ≤ bᵢ}` is convex. -/
theorem convex_polyhedralSet {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (a : ι → F) (b : ι → ℝ) :
    Convex ℝ {x : F | ∀ i, @inner ℝ F _ (a i) x ≤ b i} := by
  have : {x : F | ∀ i, @inner ℝ F _ (a i) x ≤ b i} =
      ⋂ i, {x : F | @inner ℝ F _ (a i) x ≤ b i} := by
    ext x; simp [Set.mem_iInter]
  rw [this]
  apply _root_.convex_iInter
  intro i
  have : {x : F | @inner ℝ F _ (a i) x ≤ b i} =
      (fun x => @inner ℝ F _ (a i) x) ⁻¹' Set.Iic (b i) := by
    ext x; simp [Set.mem_preimage, Set.mem_Iic]
  rw [this]
  exact (convex_Iic (b i)).linear_preimage (innerₗ F (a i))

end RW
