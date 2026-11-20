/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Global metric regularity for mappings with polyhedral graphs
-/

import RockafellarWets.Chapter9.InverseEstimates
import RockafellarWets.Chapter9.PolyhedralLipschitz

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {S : E → Set F}

/-- **Example 9.47**: a single positive constant gives global metric
regularity and linear openness for all targets in the range. -/
theorem exists_global_metricRegularity_of_polyhedral_graph (hS : IsPolyhedral (svGraph S)) :
    ∃ k : ℝ≥0, 0 < k ∧ InverseMetricEstimate S univ (svRange S) univ k ∧
      InverseOpenEstimate S univ (svRange S) univ k := by
  have hi : IsPolyhedral (svGraph (svInv S)) :=
    hS.continuousLinear_preimage (ContinuousLinearEquiv.prodComm ℝ F E).toContinuousLinearMap
  obtain ⟨k,hk⟩ := svLipschitzOn_of_isPolyhedral_graph hi
  have ht := (svLipschitzOnWith_iff_transport hk.1).mp hk
  have hT : InverseTransportEstimate S univ (svRange S) univ (k+1) := by
    intro a _ b hb x _ ha
    obtain ⟨y,hy,hd⟩ := ht a (show a ∈ svDom (svInv S) from ⟨x,ha⟩) b hb x ha
    exact ⟨y,hy,hd.trans (mul_le_mul_of_nonneg_right (by simp) dist_nonneg)⟩
  exact ⟨k+1,by positivity,hT.metricEstimate (by positivity),inverseTransportEstimate_iff_openEstimate.mp hT⟩

end RW
