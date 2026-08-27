/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Finite Unions

The ordinary-convergence clause of Exercise 4.31.  The outer limit commutes
with a finite union of sequences; the corresponding inner-limit inclusion is
enough to transfer Painleve--Kuratowski convergence.
-/

import Mathlib.Order.Filter.Finite
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Function Set Topology

namespace RW

variable {E ι : Type*} [PseudoMetricSpace E] [Finite ι]

omit [Finite ι] in
/-- The inner limit contains the union of the componentwise inner limits. -/
theorem iUnion_innerSetLimit_subset_innerSetLimit_iUnion
    (C : ι → ℕ → Set E) :
    (⋃ i, innerSetLimit (C i)) ⊆
      innerSetLimit (fun n ↦ ⋃ i, C i n) := by
  rintro x hx V hV
  rcases mem_iUnion.1 hx with ⟨i, hxi⟩
  exact (hxi V hV).mono fun n ⟨y, hyC, hyV⟩ ↦
    ⟨y, mem_iUnion_of_mem i hyC, hyV⟩

/-- The outer limit commutes with finite indexed unions. -/
theorem outerSetLimit_iUnion (C : ι → ℕ → Set E) :
    outerSetLimit (fun n ↦ ⋃ i, C i n) =
      ⋃ i, outerSetLimit (C i) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
      ⟨φ, y, hφ, hyUnion, hyx⟩
    have hfreq : ∃ᶠ n in atTop, ∃ i, y n ∈ C i (φ n) :=
      Frequently.of_forall fun n ↦ by
        simpa only [mem_iUnion] using hyUnion n
    rw [Filter.frequently_exists] at hfreq
    rcases hfreq with ⟨i, hi⟩
    rcases extraction_of_frequently_atTop hi with ⟨ψ, hψ, hmem⟩
    apply mem_iUnion_of_mem i
    exact mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ ∘ ψ, y ∘ ψ, hφ.comp hψ, hmem,
        hyx.comp hψ.tendsto_atTop⟩
  · intro x hx V hV
    rcases mem_iUnion.1 hx with ⟨i, hxi⟩
    exact (hxi V hV).mono fun n ⟨y, hyC, hyV⟩ ↦
      ⟨y, mem_iUnion_of_mem i hyC, hyV⟩

/-- **Exercise 4.31 (ordinary convergence).** A finite union of convergent
set sequences converges to the union of their limits. -/
theorem pkConverges_iUnion {C : ι → ℕ → Set E} {D : ι → Set E}
    (h : ∀ i, PKConverges (C i) (D i)) :
    PKConverges (fun n ↦ ⋃ i, C i n) (⋃ i, D i) := by
  have hDInner : (⋃ i, D i) ⊆
      innerSetLimit (fun n ↦ ⋃ i, C i n) := by
    rw [show (⋃ i, D i) = ⋃ i, innerSetLimit (C i) by
      congr 1
      funext i
      exact (h i).inner_eq.symm]
    exact iUnion_innerSetLimit_subset_innerSetLimit_iUnion C
  have hOuter : outerSetLimit (fun n ↦ ⋃ i, C i n) = ⋃ i, D i := by
    rw [outerSetLimit_iUnion]
    congr 1
    funext i
    exact (h i).outer_eq
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans hOuter.subset) hDInner
  · exact hOuter

end RW
