/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stability and regularity for inner compositions
-/

import RockafellarWets.Chapter10.InnerCompositionCoderivatives
import RockafellarWets.Chapter9.CoderivativeNorms
import RockafellarWets.Chapter8.SubdifferentialRegularityCriterion

open Filter Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : F → Set G} {f : E → F} {x : E} {u : G}

theorem isLocallyClosedAt_graph_inner_comp (hS : SvOsc S) (hf : StrictlyContinuousAt f x) :
    IsLocallyClosedAt (svGraph (fun a ↦ S (f a))) (x,u) := by
  obtain ⟨g,k,hg,he⟩ := hf.exists_global_lipschitz_germ
  have hclosed : IsClosed (svGraph (fun a ↦ S (g a))) :=
    (isClosed_svGraph_iff_svOsc.mpr hS).preimage
      ((hg.continuous.comp continuous_fst).prodMk continuous_snd)
  exact (RW.IsClosed.isLocallyClosedAt hclosed (x,u)).congr_nhds
    (svGraph_eventuallyEq_of_eventuallyEq (he.symm.mono fun a ha ↦ congrArg S ha) u)

theorem isLocallyClosedAt_euclideanGraph_inner_comp (hS : SvOsc S) (hf : StrictlyContinuousAt f x) :
    IsLocallyClosedAt (euclideanSvGraph (fun a ↦ S (f a))) (WithLp.toLp 2 (x,u)) :=
  (isLocallyClosedAt_graph_inner_comp hS hf).preimage_continuousLinearEquiv
    (WithLp.prodContinuousLinearEquiv 2 ℝ E G)

/-- The Aubin assertion of 10.40. -/
theorem hasAubinPropertyAt_inner_comp (hS : SvOsc S) (hf : StrictlyContinuousAt f x)
    (ha : HasAubinPropertyAt S (f x) u) : HasAubinPropertyAt (fun a ↦ S (f a)) x u := by
  apply (hasAubinPropertyAt_iff_coderivative_zero (S := fun a ↦ S (f a)) ha.2.1
    (isLocallyClosedAt_graph_inner_comp hS hf)).mpr
  apply Subset.antisymm
  · intro v hv
    have hQ : ∀ z ∈ coderivative S (f x) u 0,
        (0:E) ∈ coderivative (svSingleton f) x (f x) z → z = 0 := by
      intro z hz _
      simpa only [(hasAubinPropertyAt_iff_coderivative_zero ha.2.1 ha.2.2.1).mp ha,mem_singleton_iff] using hz
    obtain ⟨z,hz,hv⟩ := mem_svComp.mp (coderivative_inner_comp_subset hS hf hQ 0 hv)
    have hz0 : z = 0 := hQ z hz (by
      have := (hasAubinPropertyAt_iff_coderivative_zero ha.2.1 ha.2.2.1).mp ha
      have hz0 : z = 0 := by simpa only [this,mem_singleton_iff] using hz
      exact hz0 ▸ (graphicalDerivative_properties (S := svSingleton f) (mem_singleton (f x))).2.2.1.2.1)
    simpa only [hz0,(hasAubinPropertyAt_iff_coderivative_zero
      hf.hasAubinProperty_singleton.2.1 hf.hasAubinProperty_singleton.2.2.1).mp
      hf.hasAubinProperty_singleton] using hv
  · exact singleton_subset_iff.mpr (graphicalDerivative_properties (S := fun a ↦ S (f a)) ha.2.1).2.2.1.2.1

theorem graphicalLipschitzModulus_inner_comp_le (hS : SvOsc S) (hf : StrictlyContinuousAt f x)
    (ha : HasAubinPropertyAt S (f x) u) :
    graphicalLipschitzModulus (fun a ↦ S (f a)) x u ≤
      lipschitzModulus f x * graphicalLipschitzModulus S (f x) u := by
  have hQ : ∀ z ∈ coderivative S (f x) u 0,
      (0:E) ∈ coderivative (svSingleton f) x (f x) z → z = 0 := by
    intro z hz _
    simpa only [(hasAubinPropertyAt_iff_coderivative_zero ha.2.1 ha.2.2.1).mp ha,mem_singleton_iff] using hz
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative (S := fun a ↦ S (f a)) ha.2.1
    (isLocallyClosedAt_graph_inner_comp hS hf),
    ← svOuterNorm_coderivative_svSingleton hf,
    graphicalLipschitzModulus_eq_svOuterNorm_coderivative ha.2.1 ha.2.2.1]
  apply le_trans (b := svOuterNorm (svComp (coderivative (svSingleton f) x (f x)) (coderivative S (f x) u)))
  · apply svOuterNorm_le_iff_ball.mpr
    intro y hy v hv
    exact coe_nnnorm_le_svOuterNorm hy (coderivative_inner_comp_subset hS hf hQ y hv)
  exact svOuterNorm_svComp_le (graphicalDerivative_properties (S := svSingleton f) (mem_singleton (f x))).2.2.1.2
    (Or.inl (by rw [svOuterNorm_coderivative_svSingleton hf]; exact hf.ne))

/-- The regularity clause of 10.40, in its scalarized form. -/
theorem inner_comp_regular_and_coderivative_eq (hS : SvOsc S) (hf : StrictlyContinuousAt f x)
    (hu : u ∈ S (f x))
    (hQ : ∀ z ∈ coderivative S (f x) u 0,
      (0:E) ∈ subdifferential (fun a ↦ (⟪z,f a⟫_ℝ:EReal)) x → z = 0)
    (hrS : IsGraphicallyRegularAt S (f x) u)
    (hrf : ∀ y z, z ∈ coderivative S (f x) u y →
      IsSubdifferentiallyRegularAt (fun a ↦ (⟪z,f a⟫_ℝ:EReal)) x) :
    IsGraphicallyRegularAt (fun a ↦ S (f a)) x u ∧
      coderivative (fun a ↦ S (f a)) x u =
        svComp (coderivative (svSingleton f) x (f x)) (coderivative S (f x) u) := by
  have heS := (isGraphicallyRegularAt_iff_coderivative_eq_regular hrS.1).mp hrS
  have hlower (y : G) :
      svComp (coderivative (svSingleton f) x (f x)) (coderivative S (f x) u) y ⊆
        regularCoderivative (fun a ↦ S (f a)) x u y := by
    intro v hv
    obtain ⟨z,hz,hv⟩ := mem_svComp.mp hv
    apply regularCoderivative_inner_comp_superset hf hu y
    refine mem_svComp.mpr ⟨z,heS ▸ hz,?_⟩
    rw [regularCoderivative_svSingleton_eq_regularSubdifferential hf z,
      ← (hrf y z hz).subdifferential_eq_regularSubdifferential,
      ← coderivative_svSingleton_eq_subdifferential hf z]
    exact hv
  have he : coderivative (fun a ↦ S (f a)) x u = regularCoderivative (fun a ↦ S (f a)) x u := by
    funext y
    exact Subset.antisymm
      ((coderivative_inner_comp_subset_of_scalar_qualification hS hf hQ y).trans (hlower y))
      ((graphicalDerivative_properties (S := fun a ↦ S (f a)) hu).2.2.2.2.2 y)
  refine ⟨(isGraphicallyRegularAt_iff_coderivative_eq_regular
    (isLocallyClosedAt_euclideanGraph_inner_comp hS hf)).mpr he,?_⟩
  funext y
  exact Subset.antisymm (coderivative_inner_comp_subset_of_scalar_qualification hS hf hQ y)
    (by rw [he]; exact hlower y)

end RW
