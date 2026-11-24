/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Existence of maximal monotone extensions

Proposition 12.6: every monotone mapping has a maximal monotone extension,
that is, a maximal monotone mapping whose graph contains the given graph.  As
in the book, the proof applies Zorn's lemma to the monotone graphs containing
`gph T`, ordered by inclusion: the union of a chain of monotone graphs is
monotone, and a maximal monotone graph is the graph of a maximal monotone
mapping.
-/

import RockafellarWets.Chapter12.MonotoneMappings
import Mathlib.Order.Zorn

open Set
open scoped InnerProductSpace

namespace RW

section MaximalExtensions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A subset of `E × E` satisfying the monotonicity inequality pairwise. -/
private def MonotoneGraph (G : Set (E × E)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, 0 ≤ ⟪q.2 - p.2, q.1 - p.1⟫_ℝ

/-- **Proposition 12.6 (existence of maximal extensions).** Every monotone
mapping `T` has a maximal monotone extension `T̄` with `gph T ⊂ gph T̄`. -/
theorem SvMonotone.exists_maximal_extension {T : E → Set E} (hT : SvMonotone T) :
    ∃ T' : E → Set E, SvMaximalMonotone T' ∧ ∀ x, T x ⊆ T' x := by
  have h₀ : MonotoneGraph (svGraph T) := fun p hp q hq ↦ hT hp hq
  have hchain : ∀ c ⊆ {G : Set (E × E) | MonotoneGraph G}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {G : Set (E × E) | MonotoneGraph G}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hch _
    refine ⟨⋃₀ c, ?_, fun s hs ↦ subset_sUnion_of_mem hs⟩
    intro p hp q hq
    obtain ⟨A, hAc, hpA⟩ := mem_sUnion.1 hp
    obtain ⟨B, hBc, hqB⟩ := mem_sUnion.1 hq
    rcases hch.total hAc hBc with hAB | hBA
    · exact hc hBc p (hAB hpA) q hqB
    · exact hc hAc p hpA q (hBA hqB)
  obtain ⟨G, hsub, hmax⟩ := zorn_subset_nonempty {G | MonotoneGraph G} hchain _ h₀
  have hG : MonotoneGraph G := hmax.1
  refine ⟨fun x ↦ {v | (x, v) ∈ G}, ?_, fun x v hv ↦ hsub hv⟩
  refine svMaximalMonotone_iff_forall_inner_nonneg.2
    ⟨fun x₀ v₀ h₀ x₁ v₁ h₁ ↦ hG (x₀, v₀) h₀ (x₁, v₁) h₁, fun x v h ↦ ?_⟩
  refine hmax.mem_of_prop_insert ?_
  intro p hp q hq
  rcases mem_insert_iff.1 hp with rfl | hp <;> rcases mem_insert_iff.1 hq with rfl | hq
  · simp
  · rw [inner_sub_sub_comm]
    exact h q.1 q.2 hq
  · exact h p.1 p.2 hp
  · exact hG p hp q hq

end MaximalExtensions

end RW
