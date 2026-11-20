/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: The Mordukhovich criterion and the exact graphical modulus
-/

import RockafellarWets.Chapter9.AubinNormalCriterion
import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter6.ConeSeparation

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {S : E → Set F} {x : E} {u : F}

/-- **Theorem 9.40.** The exact graphical Lipschitz modulus equals the outer
norm of the coderivative, including when both are infinite. -/
theorem graphicalLipschitzModulus_eq_svOuterNorm_coderivative (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    graphicalLipschitzModulus S x u = svOuterNorm (coderivative S x u) := by
  have hom := (graphicalDerivative_properties hu).2.2.1.2
  apply le_antisymm
  · by_contra! hn
    obtain ⟨l,hl₁,hl₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hn
    obtain ⟨k,hk₁,hk₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hl₁
    have hb := graphNormalBound_iff_coderivative.mpr (hom.svOuterNorm_le_iff.mp hk₁.le)
    exact hl₂.not_ge (hb.aubinEstimate_of_lt hu hl (ENNReal.coe_lt_coe.mp hk₂)).modulus_le
  · exact le_iInf fun k ↦ hom.svOuterNorm_le_iff.mpr (graphNormalBound_iff_coderivative.mp k.2.graphNormalBound)

/-- **Theorem 9.40.** Finiteness of the coderivative's outer norm detects
the Aubin property. -/
theorem hasAubinPropertyAt_iff_svOuterNorm_coderivative_lt_top (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    HasAubinPropertyAt S x u ↔ svOuterNorm (coderivative S x u) < ⊤ := by
  change HasAubinPropertyWithinAt S univ x u ↔ _
  rw [hasAubinPropertyWithinAt_iff_modulus_lt_top]
  simp only [mem_univ,true_and,hu,hl]
  change graphicalLipschitzModulus S x u < ⊤ ↔ _
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative hu hl]

/-- **Theorem 9.40 (Mordukhovich criterion).** The only horizontal limiting
graph normal at the base point must be zero. -/
theorem hasAubinPropertyAt_iff_coderivative_zero (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    HasAubinPropertyAt S x u ↔ coderivative S x u 0 = {0} := by
  have h := (graphicalDerivative_properties hu).2.2.1
  rw [hasAubinPropertyAt_iff_svOuterNorm_coderivative_lt_top hu hl]
  exact ⟨h.2.apply_zero_eq_of_svOuterNorm_lt_top,fun hz ↦ h.2.svOuterNorm_lt_top_of_svOscWithinAt
    (U := univ) univ_mem ((h.1 0).svOscWithinAt _) hz⟩

/-- The full domain of the regular graphical derivative suffices, with no
graphical regularity assumption. -/
theorem hasAubinPropertyAt_of_regularGraphicalDerivative_full_domain (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) (hD : svDom (regularGraphicalDerivative S x u) = univ) :
    HasAubinPropertyAt S x u := by
  rw [hasAubinPropertyAt_iff_coderivative_zero hu hl]
  refine Subset.antisymm (fun v hv ↦ ?_) (singleton_subset_iff.mpr (graphicalDerivative_properties hu).2.2.1.2.1)
  have hvD : v ∈ svDom (regularGraphicalDerivative S x u) := hD ▸ mem_univ _
  obtain ⟨z,hz⟩ := hvD
  let L := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  have H := inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone
    (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hu)
    (IsLocallyClosedAt.preimage_continuousLinearEquiv L hl) hv hz
  change ⟪v,v⟫_ℝ + ⟪-(0:F),z⟫_ℝ ≤ 0 at H
  simpa only [neg_zero,inner_zero_left,add_zero,real_inner_self_eq_norm_sq,
    sq_nonpos_iff,norm_eq_zero,mem_singleton_iff] using H

/-- Under graphical regularity, full domain of the regular graphical
derivative is also necessary. -/
theorem hasAubinPropertyAt_iff_regularGraphicalDerivative_full_domain_of_regular (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) (hr : IsGraphicallyRegularAt S x u) :
    HasAubinPropertyAt S x u ↔ svDom (regularGraphicalDerivative S x u) = univ := by
  refine ⟨?_,hasAubinPropertyAt_of_regularGraphicalDerivative_full_domain hu hl⟩
  rintro ⟨_,_,_,k,hk⟩
  rw [← (isGraphicallyRegularAt_iff_graphicalDerivative_eq_regular hu hr.1).mp hr]
  exact eq_univ_of_forall fun w ↦ (hk.exists_graphicalDerivative_norm_le hu w).imp fun z hz ↦ hz.1

end RW
