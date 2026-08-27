/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Metric Description of Total Set Convergence

This file implements the metric and convergence clauses of Corollary 4.47.
-/

import RockafellarWets.Chapter4.CosmicSetMetric
import RockafellarWets.Chapter4.TotalConvergence

open Filter Metric Set Topology

namespace RW

section TotalSetMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The cosmic closure of a closed ordinary set, as a closed cosmic set. -/
noncomputable def totalCosmicEmbedding
    (C : TopologicalSpace.Closeds E) :
    TopologicalSpace.Closeds (CosmicSpace E) :=
  ⟨closure (cosmicSet (C : Set E) ({0} : Set E)), isClosed_closure⟩

@[simp]
theorem cosmicEmbed_mem_totalCosmicEmbedding_iff
    {C : TopologicalSpace.Closeds E} {x : E} :
    cosmicEmbed x ∈ totalCosmicEmbedding C ↔ x ∈ C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  change cosmicEmbed x ∈ closure (cosmicSet (C : Set E) ({0} : Set E)) ↔ x ∈ C
  rw [closure_cosmicSet hzero,
    cosmicEmbed_mem_cosmicSet_iff, C.isClosed.closure_eq]
  rfl

theorem injective_totalCosmicEmbedding :
    Function.Injective (totalCosmicEmbedding :
      TopologicalSpace.Closeds E →
        TopologicalSpace.Closeds (CosmicSpace E)) := by
  intro C D hCD
  apply TopologicalSpace.Closeds.ext
  ext x
  have hx := congrArg
    (fun S : TopologicalSpace.Closeds (CosmicSpace E) ↦ cosmicEmbed x ∈ (S : Set _)) hCD
  exact (cosmicEmbed_mem_totalCosmicEmbedding_iff (C := C) (x := x)).symm.trans <|
    (Iff.of_eq hx).trans (cosmicEmbed_mem_totalCosmicEmbedding_iff (C := D) (x := x))

/-- Corollary 4.47: the restriction of the cosmic set distance to closed
ordinary sets. -/
noncomputable def totalSetDistance
    (C D : TopologicalSpace.Closeds E) : ℝ :=
  cosmicSetDistance (totalCosmicEmbedding C) (totalCosmicEmbedding D)

theorem totalSetDistance_nonneg (C D : TopologicalSpace.Closeds E) :
    0 ≤ totalSetDistance C D :=
  cosmicSetDistance_nonneg _ _

@[simp]
theorem totalSetDistance_self (C : TopologicalSpace.Closeds E) :
    totalSetDistance C C = 0 :=
  cosmicSetDistance_self _

theorem totalSetDistance_comm (C D : TopologicalSpace.Closeds E) :
    totalSetDistance C D = totalSetDistance D C :=
  cosmicSetDistance_comm _ _

theorem totalSetDistance_triangle (C D F : TopologicalSpace.Closeds E) :
    totalSetDistance C F ≤ totalSetDistance C D + totalSetDistance D F :=
  cosmicSetDistance_triangle _ _ _

@[simp]
theorem totalSetDistance_eq_zero_iff
    {C D : TopologicalSpace.Closeds E} :
    totalSetDistance C D = 0 ↔ C = D := by
  rw [totalSetDistance, cosmicSetDistance_eq_zero_iff]
  exact injective_totalCosmicEmbedding.eq_iff

/-- The metric axioms in Corollary 4.47. -/
noncomputable def totalClosedSetMetric :
    PseudoMetric (TopologicalSpace.Closeds E) ℝ where
  toFun := totalSetDistance
  refl' := totalSetDistance_self
  symm' := totalSetDistance_comm
  triangle' := totalSetDistance_triangle

/-- Corollary 4.47: total convergence is exactly convergence to zero in the
restricted cosmic set metric. -/
theorem totalConverges_iff_tendsto_totalSetDistance
    {Cseq : ℕ → TopologicalSpace.Closeds E}
    {C : TopologicalSpace.Closeds E} :
    TotalConverges (fun n ↦ (Cseq n : Set E)) (C : Set E) ↔
      Tendsto (fun n ↦ totalSetDistance (Cseq n) C) atTop (nhds 0) := by
  rw [TotalConverges, and_iff_right C.isClosed]
  rw [← pkConverges_closure_iff]
  simpa only [totalSetDistance, totalCosmicEmbedding] using
    (pkConverges_iff_tendsto_cosmicSetDistance
      (E := E)
      (Sseq := fun n ↦ totalCosmicEmbedding (Cseq n))
      (S := totalCosmicEmbedding C))

end TotalSetMetric

end RW
