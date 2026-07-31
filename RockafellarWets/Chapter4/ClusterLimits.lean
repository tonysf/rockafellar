/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Set-Convergence Cluster Limits

Proposition 4.19 recovers the inner and outer set limits from all
Painleve--Kuratowski limits of subsequences.
-/

import RockafellarWets.Chapter4.SetConvergenceCompactness

open Filter Function Set Topology

namespace RW

section ClusterLimits

variable {E : Type*} [PseudoMetricSpace E]

/-- The collection `L` in Proposition 4.19: all Painleve--Kuratowski limits
of subsequences of `C`. -/
def pkClusterLimits (C : ℕ → Set E) : Set (Set E) :=
  {D | ∃ φ : ℕ → ℕ, StrictMono φ ∧ PKConverges (C ∘ φ) D}

theorem mem_pkClusterLimits {C : ℕ → Set E} {D : Set E} :
    D ∈ pkClusterLimits C ↔
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ PKConverges (C ∘ φ) D :=
  Iff.rfl

/-- Every outer-limit point belongs to the closure of the union of all
terms. -/
private theorem outerSetLimit_subset_closure_iUnion (C : ℕ → Set E) :
    outerSetLimit C ⊆ closure (⋃ n, C n) := by
  intro x hx
  have hx0 := mem_iInter.1
    (outerSetLimit_eq_iInter_closure_iUnion_tail C ▸ hx) 0
  simpa only [Nat.zero_le, iUnion_true] using hx0

/-- **Proposition 4.19 (inner limit from cluster limits).** The inner set
limit is the intersection of every set-convergence cluster limit. -/
theorem innerSetLimit_eq_sInter_pkClusterLimits [SecondCountableTopology E]
    (C : ℕ → Set E) :
    innerSetLimit C = ⋂₀ pkClusterLimits C := by
  apply Set.Subset.antisymm
  · intro x hx
    apply Set.mem_sInter.2
    intro D hD
    rcases hD with ⟨φ, hφ, hconv⟩
    rw [← hconv.inner_eq]
    exact innerSetLimit_subset_subsequence hφ hx
  · intro x hx
    rw [innerSetLimit_eq_iInter_subsequence_closure]
    apply mem_iInter.2
    intro φ
    apply mem_iInter.2
    intro hφ
    rcases exists_pkConvergent_subsequence (C ∘ φ) with
      ⟨ψ, D, hψ, hconv⟩
    have hDcluster : D ∈ pkClusterLimits C := by
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      simpa only [Function.comp_def] using hconv
    have hxD : x ∈ D := Set.mem_sInter.1 hx D hDcluster
    have hxOuterSubsequence : x ∈ outerSetLimit ((C ∘ φ) ∘ ψ) := by
      rw [hconv.outer_eq]
      exact hxD
    have hxOuter : x ∈ outerSetLimit (C ∘ φ) :=
      outerSetLimit_subsequence_subset hψ hxOuterSubsequence
    exact outerSetLimit_subset_closure_iUnion (C ∘ φ) hxOuter

/-- **Proposition 4.19 (outer limit from cluster limits).** The outer set
limit is the union of every set-convergence cluster limit. -/
theorem outerSetLimit_eq_sUnion_pkClusterLimits [SecondCountableTopology E]
    (C : ℕ → Set E) :
    outerSetLimit C = ⋃₀ pkClusterLimits C := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
      ⟨ψ, y, hψ, hyC, hyx⟩
    rcases exists_pkConvergent_subsequence (C ∘ ψ) with
      ⟨φ, D, hφ, hconv⟩
    have hDcluster : D ∈ pkClusterLimits C := by
      refine ⟨ψ ∘ φ, hψ.comp hφ, ?_⟩
      simpa only [Function.comp_def] using hconv
    apply Set.mem_sUnion.2
    refine ⟨D, hDcluster, ?_⟩
    rw [← hconv.outer_eq]
    exact mem_outerSetLimit_iff_exists_subsequence.2
      ⟨id, y ∘ φ, strictMono_id, fun n ↦ by simpa using hyC (φ n),
        hyx.comp hφ.tendsto_atTop⟩
  · intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨D, hDcluster, hxD⟩
    rcases hDcluster with ⟨φ, hφ, hconv⟩
    apply outerSetLimit_subsequence_subset hφ
    rw [hconv.outer_eq]
    exact hxD

end ClusterLimits

end RW
