/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stability bounds for finite sums of mappings
-/

import RockafellarWets.Chapter10.FiniteMappingSumCoderivatives
import RockafellarWets.Chapter10.CompositionLipschitz

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : ι → E → Set F} {x : E} {b : F} {u : PiLp 2 (fun _ : ι ↦ F)}

theorem finiteSumCoderivativeQualification_of_aubin
    (ha : ∀ i, HasAubinPropertyAt (S i) x (u i)) : FiniteSumCoderivativeQualification S x u := by
  intro v hv _ i
  simpa only [(hasAubinPropertyAt_iff_coderivative_zero (ha i).2.1 (ha i).2.2.1).mp (ha i),
    mem_singleton_iff] using hv i

theorem isLocallyClosedAt_svGraph_svFiniteSum (hS : ∀ i, SvOsc (S i))
    (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,b)) :
    IsLocallyClosedAt (svGraph (svFiniteSum S)) (x,b) :=
  (isLocallyClosedAt_graph_svFiniteSum hS hb).preimage_continuousLinearEquiv
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm

/-- **Corollary 10.42**, Aubin stability of a finite mapping sum. -/
theorem hasAubinPropertyAt_svFiniteSum (hS : ∀ i, SvOsc (S i))
    (hbmem : b ∈ svFiniteSum S x) (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,b))
    (ha : ∀ u ∈ finiteSumMappingAux S (x,b), ∀ i, HasAubinPropertyAt (S i) x (u i)) :
    HasAubinPropertyAt (svFiniteSum S) x b := by
  apply (hasAubinPropertyAt_iff_coderivative_zero hbmem (isLocallyClosedAt_svGraph_svFiniteSum hS hb)).mpr
  apply Subset.antisymm
  · intro v hv
    obtain ⟨u,hu,q,hq,rfl⟩ := mem_iUnion₂.mp (coderivative_svFiniteSum_subset hS hb
      (fun u hu ↦ finiteSumCoderivativeQualification_of_aubin (ha u hu)) 0 hv)
    have hz (i : ι) : q i = 0 := by
      simpa only [(hasAubinPropertyAt_iff_coderivative_zero (ha u hu i).2.1 (ha u hu i).2.2.1).mp
        (ha u hu i),mem_singleton_iff] using hq i
    simp [hz]
  · exact singleton_subset_iff.mpr (graphicalDerivative_properties hbmem).2.2.1.2.1

theorem svOuterNorm_svFiniteSum_le (H : ι → F → Set E) :
    svOuterNorm (svFiniteSum H) ≤ ∑ i, svOuterNorm (H i) := by
  apply svOuterNorm_le_iff_ball.mpr
  intro y hy v hv
  obtain ⟨q,hq,rfl⟩ := hv
  calc
    (‖∑ i, q i‖₊ : ℝ≥0∞) ≤ ∑ i, (‖q i‖₊ : ℝ≥0∞) := by
      exact_mod_cast nnnorm_sum_le Finset.univ q
    _ ≤ ∑ i, svOuterNorm (H i) := Finset.sum_le_sum fun i _ ↦ coe_nnnorm_le_svOuterNorm hy (hq i)

theorem graphicalLipschitzModulus_svFiniteSum_le_iSup (hS : ∀ i, SvOsc (S i))
    (hbmem : b ∈ svFiniteSum S x) (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,b))
    (ha : ∀ u ∈ finiteSumMappingAux S (x,b), ∀ i, HasAubinPropertyAt (S i) x (u i)) :
    graphicalLipschitzModulus (svFiniteSum S) x b ≤
      ⨆ u ∈ finiteSumMappingAux S (x,b), ∑ i, graphicalLipschitzModulus (S i) x (u i) := by
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative hbmem (isLocallyClosedAt_svGraph_svFiniteSum hS hb)]
  apply svOuterNorm_le_iff_ball.mpr
  intro y hy v hv
  obtain ⟨u,hu,hv⟩ := mem_iUnion₂.mp (coderivative_svFiniteSum_subset hS hb
    (fun u hu ↦ finiteSumCoderivativeQualification_of_aubin (ha u hu)) y hv)
  apply ((coe_nnnorm_le_svOuterNorm (H := svFiniteSum (fun i ↦ coderivative (S i) x (u i))) hy hv).trans
    (svOuterNorm_svFiniteSum_le _)).trans
  apply le_iSup₂_of_le u hu
  apply Finset.sum_le_sum
  intro i _
  exact (graphicalLipschitzModulus_eq_svOuterNorm_coderivative (ha u hu i).2.1 (ha u hu i).2.2.1).symm.le

theorem graphicalLipschitzModulus_svFiniteSum_le_of_convex (hS : ∀ i, SvOsc (S i))
    (hc : ∀ i, SvGraphConvex (S i)) (hu : u ∈ finiteSumMappingAux S (x,b))
    (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,b))
    (ha : ∀ i, HasAubinPropertyAt (S i) x (u i)) :
    graphicalLipschitzModulus (svFiniteSum S) x b ≤ ∑ i, graphicalLipschitzModulus (S i) x (u i) := by
  have hbmem : b ∈ svFiniteSum S x := ⟨fun i ↦ u i,hu.1,hu.2⟩
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative hbmem (isLocallyClosedAt_svGraph_svFiniteSum hS hb)]
  have he : coderivative (svFiniteSum S) x b = svFiniteSum (fun i ↦ coderivative (S i) x (u i)) := by
    have hub : ∑ i, u i = b := hu.2
    rw [← hub]
    exact funext (coderivative_svFiniteSum_eq_of_convex hS hc hu.1
      (finiteSumCoderivativeQualification_of_aubin ha))
  rw [he]
  exact (svOuterNorm_svFiniteSum_le _).trans (Finset.sum_le_sum fun i _ ↦
    (graphicalLipschitzModulus_eq_svOuterNorm_coderivative (ha i).2.1 (ha i).2.2.1).symm.le)

theorem isCompact_finiteSumMappingAux (hS : ∀ i, SvOsc (S i))
    (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,b)) :
    IsCompact (finiteSumMappingAux S (x,b)) := by
  apply Metric.isCompact_of_isClosed_isBounded _ hb.isBounded_apply
  apply (isClosed_l2PiSet (fun i ↦ (hS i x).isClosed)).inter
  change IsClosed {q : PiLp 2 (fun _ : ι ↦ F) | ∑ i, q i = b}
  simp_rw [← l2PiSum_apply]
  exact (isClosed_singleton (x := b)).preimage (l2PiSum (ι := ι) (E := F)).continuous

/-- The maximum in 10.42 is attained on the compact set of decompositions. -/
theorem exists_max_finite_sum_modulus (hS : ∀ i, SvOsc (S i))
    (hbmem : b ∈ svFiniteSum S x) (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,b))
    (ha : ∀ u ∈ finiteSumMappingAux S (x,b), ∀ i, HasAubinPropertyAt (S i) x (u i)) :
    ∃ u ∈ finiteSumMappingAux S (x,b),
      IsMaxOn (fun u : PiLp 2 (fun _ : ι ↦ F) ↦ ∑ i, graphicalLipschitzModulus (S i) x (u i))
        (finiteSumMappingAux S (x,b)) u ∧
      graphicalLipschitzModulus (svFiniteSum S) x b ≤ ∑ i, graphicalLipschitzModulus (S i) x (u i) := by
  have hne : (finiteSumMappingAux S (x,b)).Nonempty := by
    obtain ⟨u,hu,hb⟩ := hbmem
    exact ⟨WithLp.toLp 2 u,hu,hb⟩
  have hU : UpperSemicontinuous (fun u : PiLp 2 (fun _ : ι ↦ F) ↦
      ∑ i, graphicalLipschitzModulus (S i) x (u i)) :=
    upperSemicontinuous_sum fun i _ ↦ (upperSemicontinuous_graphicalLipschitzModulusWithin (S i) univ).comp
      (continuous_const.prodMk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ F) i).continuous)
  obtain ⟨u,hu,hm⟩ := UpperSemicontinuousOn.exists_isMaxOn hne (isCompact_finiteSumMappingAux hS hb)
    (hU.upperSemicontinuousOn _)
  exact ⟨u,hu,hm,(graphicalLipschitzModulus_svFiniteSum_le_iSup hS hbmem hb ha).trans
    (iSup₂_le fun v hv ↦ hm hv)⟩

end RW
