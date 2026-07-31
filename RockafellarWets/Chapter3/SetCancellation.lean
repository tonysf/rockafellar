/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Cancellation in Set Addition

This file gives a direct geometric proof of Corollary 3.35.  It is independent
of the functional cancellation theorem: strict separation detects a point
outside a closed convex set, and compactness of the bounded common summand
provides an extremizer that can be cancelled from the separating inequality.
-/

import RockafellarWets.Chapter2.Separation
import RockafellarWets.Chapter3.SetOperations

open Set Bornology
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem subset_of_add_eq_add_bounded_closed_convex
    {C₁ C₂ B : Set E}
    (hC₂ne : C₂.Nonempty) (hBne : B.Nonempty)
    (hC₂conv : Convex ℝ C₂) (hC₂closed : IsClosed C₂)
    (hBclosed : IsClosed B) (hBbounded : IsBounded B)
    (hEq : C₁ + B = C₂ + B) :
    C₁ ⊆ C₂ := by
  intro x hxC₁
  by_contra hxC₂
  have hsingle_disjoint : Disjoint ({x} : Set E) C₂ := by
    rw [Set.disjoint_singleton_left]
    exact hxC₂
  obtain ⟨φ, c₁, c₂, hc, hxsep, hC₂sep⟩ :=
    strict_separation_of_convex_compact
      (S := ({x} : Set E)) (T := C₂)
      (convex_singleton x) (Set.singleton_nonempty x) isCompact_singleton
      hC₂conv hC₂ne hC₂closed hsingle_disjoint
  have hxlt : φ x < c₁ := hxsep x (by simp)
  have hBcompact : IsCompact B :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hBclosed, hBbounded⟩
  obtain ⟨b₀, hb₀B, hb₀min⟩ :=
    hBcompact.exists_isMinOn hBne φ.continuous.continuousOn
  have hxb₀ : x + b₀ ∈ C₁ + B :=
    Set.mem_add.2 ⟨x, hxC₁, b₀, hb₀B, rfl⟩
  have hxb₀' : x + b₀ ∈ C₂ + B := by
    simpa [hEq] using hxb₀
  rcases Set.mem_add.1 hxb₀' with ⟨y, hyC₂, b₁, hb₁B, hyb₁⟩
  have hygt : c₂ < φ y := hC₂sep y hyC₂
  have hxy : φ x < φ y := hxlt.trans (hc.trans hygt)
  have hb : φ b₀ ≤ φ b₁ := hb₀min hb₁B
  have hsumlt : φ (x + b₀) < φ (y + b₁) := by
    simpa using add_lt_add_of_lt_of_le hxy hb
  have heq : x + b₀ = y + b₁ := hyb₁.symm
  rw [heq] at hsumlt
  exact (lt_irrefl _) hsumlt

/-- **Corollary 3.35** (cancellation in set addition): adding the same
nonempty bounded closed convex set is cancellative on nonempty closed convex
sets in finite-dimensional real normed spaces. -/
theorem corollary335_set_eq_of_add_eq_add_bounded
    {C₁ C₂ B : Set E}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty) (hBne : B.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂conv : Convex ℝ C₂)
    (_hBconv : Convex ℝ B)
    (hC₁closed : IsClosed C₁) (hC₂closed : IsClosed C₂)
    (hBclosed : IsClosed B) (hBbounded : IsBounded B)
    (hEq : C₁ + B = C₂ + B) :
    C₁ = C₂ := by
  apply Set.Subset.antisymm
  · exact subset_of_add_eq_add_bounded_closed_convex
      hC₂ne hBne hC₂conv hC₂closed hBclosed hBbounded hEq
  · exact subset_of_add_eq_add_bounded_closed_convex
      hC₁ne hBne hC₁conv hC₁closed hBclosed hBbounded hEq.symm

end RW
