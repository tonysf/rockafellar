/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Basic Examples and Regression Theorems
-/

import Mathlib.Order.Filter.AtTopBot.ModEq
import RockafellarWets.Chapter4.DistanceConvergence

open Filter Metric Set Topology

namespace RW

section Singletons

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- Convergence of singleton sets is exactly convergence of their points. -/
theorem pkConverges_singleton_iff {u : ℕ → E} {x : E} :
    PKConverges (fun n ↦ ({u n} : Set E)) {x} ↔
      Tendsto u atTop (nhds x) := by
  constructor
  · intro h
    have hdist := (pkConverges_iff_tendsto_infEDist isClosed_singleton).1 h x
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [Metric.infEDist_singleton, edist_comm, edist_self] using hdist
  · intro h
    apply (pkConverges_iff_tendsto_infEDist isClosed_singleton).2
    intro y
    simpa only [Metric.infEDist_singleton] using tendsto_const_nhds.edist h

end Singletons

section Alternating

variable {E : Type*}

/-- A sequence alternating between two sets. -/
def alternatingSets (A B : Set E) (n : ℕ) : Set E :=
  if Even n then A else B

@[simp]
theorem alternatingSets_of_even {A B : Set E} {n : ℕ} (hn : Even n) :
    alternatingSets A B n = A := by
  simp [alternatingSets, hn]

@[simp]
theorem alternatingSets_of_odd {A B : Set E} {n : ℕ} (hn : Odd n) :
    alternatingSets A B n = B := by
  simp [alternatingSets, Nat.not_even_iff_odd.mpr hn]

variable [TopologicalSpace E]

/-- The outer limit of an alternating sequence is the union of the two
closures. -/
theorem outerSetLimit_alternatingSets (A B : Set E) :
    outerSetLimit (alternatingSets A B) = closure A ∪ closure B := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← closure_union]
    refine mem_closure_iff_nhds.2 fun V hV ↦ ?_
    rcases (hx V hV).exists with ⟨n, y, hyAlt, hyV⟩
    by_cases hn : Even n
    · exact ⟨y, hyV, Or.inl (by simpa [alternatingSets, hn] using hyAlt)⟩
    · exact ⟨y, hyV, Or.inr (by simpa [alternatingSets, hn] using hyAlt)⟩
  · intro x hx V hV
    rcases hx with hxA | hxB
    · have hhit : (A ∩ V).Nonempty := by
        rcases mem_closure_iff_nhds.1 hxA V hV with ⟨y, hyV, hyA⟩
        exact ⟨y, hyA, hyV⟩
      exact Nat.frequently_even.mono fun n hn ↦ by
        simpa only [alternatingSets_of_even hn] using hhit
    · have hhit : (B ∩ V).Nonempty := by
        rcases mem_closure_iff_nhds.1 hxB V hV with ⟨y, hyV, hyB⟩
        exact ⟨y, hyB, hyV⟩
      exact Nat.frequently_odd.mono fun n hn ↦ by
        simpa only [alternatingSets_of_odd hn] using hhit

/-- The inner limit of an alternating sequence is the intersection of the two
closures. -/
theorem innerSetLimit_alternatingSets (A B : Set E) :
    innerSetLimit (alternatingSets A B) = closure A ∩ closure B := by
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · refine mem_closure_iff_nhds.2 fun V hV ↦ ?_
      have heventual := hx V hV
      rcases (Nat.frequently_even.and_eventually heventual).exists with
        ⟨n, hn, y, hyAlt, hyV⟩
      exact ⟨y, hyV, by simpa [alternatingSets, hn] using hyAlt⟩
    · refine mem_closure_iff_nhds.2 fun V hV ↦ ?_
      have heventual := hx V hV
      rcases (Nat.frequently_odd.and_eventually heventual).exists with
        ⟨n, hn, y, hyAlt, hyV⟩
      exact ⟨y, hyV, by
        simpa [alternatingSets, Nat.not_even_iff_odd.mpr hn] using hyAlt⟩
  · rintro x ⟨hxA, hxB⟩ V hV
    rcases mem_closure_iff_nhds.1 hxA V hV with ⟨a, haV, haA⟩
    rcases mem_closure_iff_nhds.1 hxB V hV with ⟨b, hbV, hbB⟩
    exact Eventually.of_forall fun n ↦ by
      by_cases hn : Even n
      · exact ⟨a, by simpa [alternatingSets, hn] using haA, haV⟩
      · exact ⟨b, by simpa [alternatingSets, hn] using hbB, hbV⟩

@[simp]
theorem outerSetLimit_alternating_empty_univ :
    outerSetLimit (alternatingSets (∅ : Set E) Set.univ) = Set.univ := by
  simp only [outerSetLimit_alternatingSets, closure_empty, closure_univ, empty_union]

@[simp]
theorem innerSetLimit_alternating_empty_univ :
    innerSetLimit (alternatingSets (∅ : Set E) Set.univ) = ∅ := by
  simp only [innerSetLimit_alternatingSets, closure_empty, closure_univ, empty_inter]

end Alternating

end RW
