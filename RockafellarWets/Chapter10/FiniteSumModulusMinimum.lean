/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Attainment of the convex finite-sum modulus bound
-/

import RockafellarWets.Chapter10.FiniteMappingSumLipschitz
import RockafellarWets.Chapter10.CompositionConvexMinimum

open Set
open scoped NNReal ENNReal InnerProductSpace

namespace RW

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : ι → E → Set F} {x : E} {b : F}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem convex_finiteSumMappingAux (hc : ∀ i, SvGraphConvex (S i)) :
    Convex ℝ (finiteSumMappingAux S (x,b)) := by
  intro p hp q hq a c ha hc' hac
  refine ⟨fun i ↦ (hc i).svConvexValued x (hp.1 i) (hq.1 i) ha hc' hac,?_⟩
  change ∑ i, (a • p i+c • q i) = b
  rw [Finset.sum_add_distrib,← Finset.smul_sum,← Finset.smul_sum,hp.2,hq.2,← add_smul,hac,one_smul]

theorem finite_sum_coderivatives_subset_of_intrinsicInterior
    (hc : ∀ i, SvGraphConvex (S i)) {p q : PiLp 2 (fun _ : ι ↦ F)}
    (hp : p ∈ intrinsicInterior ℝ (finiteSumMappingAux S (x,b)))
    (hq : q ∈ finiteSumMappingAux S (x,b)) (i : ι) (y : F) :
    coderivative (S i) x (p i) y ⊆ coderivative (S i) x (q i) y := by
  have hpK := intrinsicInterior_subset hp
  obtain ⟨t,ht,hstep⟩ := exists_extrapolation_of_mem_intrinsicInterior hp hq
  have hci : Convex ℝ (euclideanSvGraph (S i)) := (hc i).linear_preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearEquiv.toLinearMap
  have he : WithLp.toLp 2 (x,p i)+t • (WithLp.toLp 2 (x,p i)-WithLp.toLp 2 (x,q i)) =
      WithLp.toLp 2 (x,p i+t • (p i-q i)) := by
    apply WithLp.ofLp_injective
    simp
  exact fun _ hv ↦ normalCone_subset_of_extrapolation hci
    (a := WithLp.toLp 2 (x,p i)) (b := WithLp.toLp 2 (x,q i)) (hpK.1 i) (hq.1 i) ht
    (by rw [he]; exact hstep.1 i) hv

/-- **Corollary 10.42**, the convex bound attains a minimum. -/
theorem exists_min_finite_sum_modulus (hS : ∀ i, SvOsc (S i))
    (hc : ∀ i, SvGraphConvex (S i)) (hbmem : b ∈ svFiniteSum S x)
    (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,b))
    (ha : ∀ u ∈ finiteSumMappingAux S (x,b), ∀ i, HasAubinPropertyAt (S i) x (u i)) :
    ∃ u ∈ finiteSumMappingAux S (x,b),
      IsMinOn (fun u : PiLp 2 (fun _ : ι ↦ F) ↦ ∑ i, graphicalLipschitzModulus (S i) x (u i))
        (finiteSumMappingAux S (x,b)) u ∧
      graphicalLipschitzModulus (svFiniteSum S) x b ≤ ∑ i, graphicalLipschitzModulus (S i) x (u i) := by
  have hne : (finiteSumMappingAux S (x,b)).Nonempty := by
    obtain ⟨u,hu,hb⟩ := hbmem
    exact ⟨WithLp.toLp 2 u,hu,hb⟩
  obtain ⟨u,hu⟩ := nonempty_relInterior_of_convex (convex_finiteSumMappingAux hc) hne
  have huK := intrinsicInterior_subset hu
  refine ⟨u,huK,?_,graphicalLipschitzModulus_svFiniteSum_le_of_convex hS hc huK hb (ha u huK)⟩
  intro v hv
  change (∑ i, graphicalLipschitzModulus (S i) x (u i)) ≤ ∑ i, graphicalLipschitzModulus (S i) x (v i)
  apply Finset.sum_le_sum
  intro i _
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative (ha u huK i).2.1 (ha u huK i).2.2.1,
    graphicalLipschitzModulus_eq_svOuterNorm_coderivative (ha v hv i).2.1 (ha v hv i).2.2.1]
  exact svOuterNorm_le_iff_ball.mpr (fun y hy z hz ↦ coe_nnnorm_le_svOuterNorm hy
    (finite_sum_coderivatives_subset_of_intrinsicInterior hc hu hv i y hz))

end RW
