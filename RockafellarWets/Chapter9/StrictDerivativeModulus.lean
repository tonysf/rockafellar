/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The strict derivative outer norm and the Lipschitz modulus
-/

import RockafellarWets.Chapter9.GraphLipschitzLocalization
import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter9.LipschitzModulus

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuity makes an estimate on a local graph equivalent to an estimate
on a neighborhood in the input space. -/
theorem localGraphLipschitzBound_singleton_iff {f : E → F} {x : E} {k : ℝ≥0}
    (hf : ContinuousAt f x) : LocalGraphLipschitzBound (svGraph (fun a ↦ {f a})) (x,f x) k ↔
      ∃ U ∈ 𝓝 x, LipschitzOnWith k f U := by
  constructor
  · rintro ⟨δ,hδ,hbound⟩
    let U := ball x δ ∩ f ⁻¹' ball (f x) δ
    have hU : U ∈ 𝓝 x := inter_mem (ball_mem_nhds x hδ) (hf (ball_mem_nhds (f x) hδ))
    refine ⟨U,hU,LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_⟩
    have hgraph {a : E} (ha : a ∈ U) : (a,f a) ∈ svGraph (fun a ↦ {f a}) ∩ ball (x,f x) δ := by
      refine ⟨mem_singleton _,?_⟩
      rw [← ball_prod_same]
      exact ha
    exact hbound _ (hgraph ha) _ (hgraph hb)
  · rintro ⟨U,hU,hk⟩
    obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨δ,hδ,?_⟩
    intro p hp q hq
    have hpf := mem_singleton_iff.mp hp.1
    have hqf := mem_singleton_iff.mp hq.1
    have hpball := hp.2
    have hqball := hq.2
    rw [← ball_prod_same] at hpball hqball
    rw [hpf,hqf]
    exact hk.dist_le_mul _ (hδU hpball.1) _ (hδU hqball.1)

/-- **Theorem 9.54**, the sharp strict-derivative norm for a continuous
single-valued mapping. Infinite moduli are included. -/
theorem svOuterNorm_strictGraphicalDerivative_singleton [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {x : E} (hf : ContinuousAt f x) :
    svOuterNorm (strictGraphicalDerivative (fun a ↦ {f a}) x (f x)) = lipschitzModulus f x := by
  have hhom := svPositivelyHomogeneous_strictGraphicalDerivative (S := fun a ↦ {f a}) (mem_singleton (f x))
  apply le_antisymm
  · change _ ≤ ⨅ k : {k : ℝ≥0 // ∃ U ∈ 𝓝[univ] x, LipschitzOnWith k f U}, ((k : ℝ≥0) : ℝ≥0∞)
    apply le_iInf
    intro k
    have hlocal : LocalGraphLipschitzBound (svGraph (fun a ↦ {f a})) (x,f x) k.val :=
      (localGraphLipschitzBound_singleton_iff hf).mpr (by simpa only [nhdsWithin_univ] using k.property)
    exact hhom.svOuterNorm_le_iff.mpr fun w z hz ↦ hlocal.norm_le hz
  · by_contra hno
    obtain ⟨l,hNl,hlM⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hno)
    have hNfin := ne_top_of_lt hNl
    let k := (svOuterNorm (strictGraphicalDerivative (fun a ↦ {f a}) x (f x))).toNNReal
    have hk : (k:ℝ≥0∞) = svOuterNorm (strictGraphicalDerivative (fun a ↦ {f a}) x (f x)) :=
      ENNReal.coe_toNNReal hNfin
    have hkl : k < l := ENNReal.coe_lt_coe.mp (hk.symm ▸ hNl)
    have hcone := hhom.svOuterNorm_le_iff.mp (show svOuterNorm _ ≤ (k:ℝ≥0∞) from hk.symm.le)
    have hlocal := localGraphLipschitzBound_of_strictTangent_bound hkl hcone
    obtain ⟨U,hU,hUlip⟩ := (localGraphLipschitzBound_singleton_iff hf).mp hlocal
    exact (not_le_of_gt hlM) (lipschitzModulus_le hU hUlip)

end RW
