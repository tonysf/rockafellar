/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Topological continuity of minimization under total epi-convergence
-/

import RockafellarWets.Chapter5.SequentialLimits
import RockafellarWets.Chapter7.CosmicEpiDistance
import RockafellarWets.Chapter7.HorizonLevelBoundedness

open Filter Function Set Topology

namespace RW

/-- The full space of lower semicontinuous extended-real functions equipped
with the topology of total epi-convergence. Its elements include the
identically positive-infinite function, whose closed epigraph is empty. -/
@[ext]
structure LscFunctionWithTotalTopology (E : Type*) [TopologicalSpace E] where
  toFun : E → EReal
  lowerSemicontinuous : LowerSemicontinuous toFun

namespace LscFunctionWithTotalTopology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def closedEpigraph (f : LscFunctionWithTotalTopology E) : TopologicalSpace.Closeds (WithLp 2 (E × ℝ)) :=
  ⟨euclideanEpigraph f.toFun, isClosed_euclideanEpigraph f.lowerSemicontinuous⟩

noncomputable instance : MetricSpace (LscFunctionWithTotalTopology E) where
  dist f g := totalSetDistance f.closedEpigraph g.closedEpigraph
  dist_self _ := totalSetDistance_self _
  dist_comm _ _ := totalSetDistance_comm _ _
  dist_triangle _ _ _ := totalSetDistance_triangle _ _ _
  eq_of_dist_eq_zero {f g} h := by
    apply LscFunctionWithTotalTopology.ext
    apply eq_of_epigraph_eq
    have he := congrArg (fun S : TopologicalSpace.Closeds (WithLp 2 (E × ℝ)) ↦ (S : Set (WithLp 2 (E × ℝ))))
      (totalSetDistance_eq_zero_iff.mp h)
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).surjective.preimage_injective he

theorem tendsto_iff_totalEpiConverges {f : ℕ → LscFunctionWithTotalTopology E}
    {g : LscFunctionWithTotalTopology E} :
    Tendsto f atTop (𝓝 g) ↔ TotalEpiConverges (fun n ↦ (f n).toFun) g.toFun := by
  rw [tendsto_iff_dist_tendsto_zero, totalEpiConverges_iff_euclideanEpigraph]
  exact (totalConverges_iff_tendsto_totalSetDistance (Cseq := fun n ↦ (f n).closedEpigraph)
    (C := g.closedEpigraph)).symm

/-- **Corollary 7.55.** The infimum is continuous at every proper,
level-coercive function for the topology of total epi-convergence. -/
theorem continuousAt_iInf {g : LscFunctionWithTotalTopology E} (hg : IsProper g.toFun)
    (hco : IsLevelCoercive g.toFun) :
    ContinuousAt (fun f : LscFunctionWithTotalTopology E ↦ ⨅ x, f.toFun x) g := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro f hf
  exact ((tendsto_iff_totalEpiConverges.mp hf).tendsto_iInf_and_outer_argmin
    (fun n ↦ (f n).lowerSemicontinuous) hg hco).1

/-- **Corollary 7.55.** The argmin mapping is outer semicontinuous at every
proper, level-coercive function. -/
theorem svOscAt_argmin {g : LscFunctionWithTotalTopology E} (hg : IsProper g.toFun)
    (hco : IsLevelCoercive g.toFun) :
    SvOscAt (fun f : LscFunctionWithTotalTopology E ↦ argmin f.toFun) g := by
  rw [SvOscAt, svOuterLimit_eq_iUnion]
  refine iUnion₂_subset fun f hf ↦ ?_
  exact ((tendsto_iff_totalEpiConverges.mp hf).tendsto_iInf_and_outer_argmin
    (fun n ↦ (f n).lowerSemicontinuous) hg hco).2

/-- **Corollary 7.55.** Proper level-coercive functions form an open subset
of the full space of lower semicontinuous functions for total epi-convergence. -/
theorem isOpen_isProper_isLevelCoercive :
    IsOpen {g : LscFunctionWithTotalTopology E | IsProper g.toFun ∧ IsLevelCoercive g.toFun} := by
  rw [← isClosed_compl_iff, ← isSeqClosed_iff_isClosed]
  intro f g hf hfg hgood
  obtain ⟨n, hn⟩ := ((tendsto_iff_totalEpiConverges.mp hfg).eventually_isProper_isLevelCoercive
    hgood.1 hgood.2).exists
  exact hf n hn

end LscFunctionWithTotalTopology
end RW
