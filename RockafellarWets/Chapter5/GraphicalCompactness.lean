/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Extraction of Graphically Convergent Subsequences

Theorem 5.36, together with the notion of a sequence of mappings escaping to
the horizon that the book introduces just before it.

The proof is the one the book gives -- 4.18 applied to the sets `gph Sν` --
once escape to the horizon is identified with the vanishing of the outer limit
of those graphs.  That identification is where the sup norm on `IRⁿ × IRᵐ`
does the work: a bounded set of pairs sits inside a product of balls, and a
product ball is a ball, so quantifying over pairs of bounded sets is the same
as quantifying over balls about the origin of the product.
-/

import RockafellarWets.Chapter4.EscapeToHorizon
import RockafellarWets.Chapter4.SetConvergenceCompactness
import RockafellarWets.Chapter5.GraphicalLimits

open Bornology Filter Metric Set Topology

namespace RW

section OfGraph

variable {E F : Type*}

/-- The mapping whose graph is a prescribed set. -/
def svOfGraph (A : Set (E × F)) : E → Set F := fun x ↦ {u | (x, u) ∈ A}

@[simp]
theorem svGraph_svOfGraph (A : Set (E × F)) : svGraph (svOfGraph A) = A := by
  ext ⟨x, u⟩
  rfl

theorem svGraph_eq_empty_iff {S : E → Set F} : svGraph S = ∅ ↔ ∀ x, S x = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, mem_svGraph, Prod.forall]

theorem svDom_svOfGraph_nonempty {A : Set (E × F)} (hA : A.Nonempty) :
    (svDom (svOfGraph A)).Nonempty := by
  obtain ⟨⟨x, u⟩, hxu⟩ := hA
  exact ⟨x, u, hxu⟩

end OfGraph

section Escape

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F}

/-- The book's definition, stated just before 5.36: a sequence of mappings
escapes to the horizon when eventually no bounded set of arguments has values
meeting a given bounded set. -/
def SvEscapesToHorizon (Sseq : ℕ → E → Set F) : Prop :=
  ∀ C : Set E, IsBounded C → ∀ D : Set F, IsBounded D →
    ∀ᶠ n in atTop, ∀ x ∈ C, Sseq n x ∩ D = ∅

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- Under the sup norm a ball of the product is the product of two balls. -/
theorem closedBall_prod_zero (ρ : ℝ) :
    closedBall (0 : E × F) ρ = closedBall (0 : E) ρ ×ˢ closedBall (0 : F) ρ := by
  ext ⟨x, u⟩
  simp only [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, mem_prod]

/-- Escape to the horizon is exactly the vanishing of the outer limit of the
graphs, hence of the graphical outer limit. -/
theorem svEscapesToHorizon_iff_outerSetLimit_eq_empty :
    SvEscapesToHorizon Sseq ↔ outerSetLimit (fun n ↦ svGraph (Sseq n)) = ∅ := by
  rw [outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero]
  constructor
  · intro h ρ hρ
    filter_upwards [h (closedBall (0 : E) ρ) isBounded_closedBall
      (closedBall (0 : F) ρ) isBounded_closedBall] with n hn
    rw [Set.disjoint_left]
    rintro ⟨x, u⟩ hxu hball
    rw [closedBall_prod_zero] at hball
    have := hn x hball.1
    rw [Set.eq_empty_iff_forall_notMem] at this
    exact this u ⟨hxu, hball.2⟩
  · intro h C hC D hD
    obtain ⟨ρ₁, hC₁⟩ := hC.subset_closedBall (0 : E)
    obtain ⟨ρ₂, hD₂⟩ := hD.subset_closedBall (0 : F)
    set ρ : ℝ := max (max ρ₁ ρ₂) 1 with hρdef
    have hρ : 0 < ρ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    filter_upwards [h ρ hρ] with n hn x hx
    rw [Set.eq_empty_iff_forall_notMem]
    intro u hu
    have hgraph : ((x, u) : E × F) ∈ svGraph (Sseq n) := hu.1
    have hball : ((x, u) : E × F) ∈ closedBall (0 : E × F) ρ := by
      rw [closedBall_prod_zero]
      exact ⟨closedBall_subset_closedBall
          ((le_max_left ρ₁ ρ₂).trans (le_max_left _ _)) (hC₁ hx),
        closedBall_subset_closedBall
          ((le_max_right ρ₁ ρ₂).trans (le_max_left _ _)) (hD₂ hu.2)⟩
    exact Set.disjoint_left.1 hn hgraph hball

/-- Escape to the horizon says the graphical outer limit is empty-valued. -/
theorem svEscapesToHorizon_iff_graphicalOuterLimit_eq_empty :
    SvEscapesToHorizon Sseq ↔ ∀ x, graphicalOuterLimit Sseq x = ∅ := by
  rw [svEscapesToHorizon_iff_outerSetLimit_eq_empty,
    ← svGraph_graphicalOuterLimit, svGraph_eq_empty_iff]

/-- **Theorem 5.36 (extraction of graphically convergent subsequences).**  A
sequence of mappings either escapes to the horizon or has a subsequence
converging graphically to a mapping with nonempty domain.  This is 4.18 for
the sequence of graphs. -/
theorem svEscapesToHorizon_or_exists_graphicalConverges_subsequence
    (Sseq : ℕ → E → Set F) :
    SvEscapesToHorizon Sseq ∨
      ∃ (φ : ℕ → ℕ) (S : E → Set F), StrictMono φ ∧ (svDom S).Nonempty ∧
        GraphicalConverges (fun n ↦ Sseq (φ n)) S := by
  rcases Set.eq_empty_or_nonempty (outerSetLimit (fun n ↦ svGraph (Sseq n))) with
    hempty | hne
  · exact Or.inl (svEscapesToHorizon_iff_outerSetLimit_eq_empty.2 hempty)
  obtain ⟨φ, A, hφ, hA, hconv⟩ :=
    exists_pkConvergent_subsequence_with_nonempty_limit hne
  refine Or.inr ⟨φ, svOfGraph A, hφ, svDom_svOfGraph_nonempty hA, ?_⟩
  rw [GraphicalConverges, svGraph_svOfGraph]
  exact hconv

/-- **Theorem 5.36** without the dichotomy: a graphically convergent
subsequence always exists, the escaping case being convergence of the whole
sequence to the empty-valued mapping.  This is the form 5.47 uses. -/
theorem exists_graphicalConverges_subsequence (Sseq : ℕ → E → Set F) :
    ∃ (φ : ℕ → ℕ) (S : E → Set F), StrictMono φ ∧
      GraphicalConverges (fun n ↦ Sseq (φ n)) S := by
  rcases svEscapesToHorizon_or_exists_graphicalConverges_subsequence Sseq with
    hesc | ⟨φ, S, hφ, -, hconv⟩
  · refine ⟨id, fun _ ↦ ∅, strictMono_id, ?_⟩
    have hout : outerSetLimit (fun n ↦ svGraph (Sseq n)) = ∅ :=
      svEscapesToHorizon_iff_outerSetLimit_eq_empty.1 hesc
    refine ⟨?_, ?_⟩
    · rw [svGraph_eq_empty_iff.2 fun _ ↦ rfl]
      exact subset_empty_iff.1 ((innerSetLimit_subset_outerSetLimit _).trans hout.subset)
    · rw [svGraph_eq_empty_iff.2 fun _ ↦ rfl]
      exact hout
  · exact ⟨φ, S, hφ, hconv⟩

end Escape

end RW
