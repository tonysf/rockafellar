/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Locally bounded outer composition and Hausdorff modulus bounds
-/

import RockafellarWets.Chapter10.OuterComposition

open Filter Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {f : F → G} {x : E}

/-- Local boundedness of the inner map supplies all the closedness needed
for the final part of Exercise 10.39. -/
theorem bounded_outer_singleton_composition_data (hS : SvOsc S)
    (hb : SvLocallyBoundedAt S x) (hf : ∀ w ∈ S x, StrictlyContinuousAt f w) :
    SvLocallyBoundedAt (svComp (svSingleton f) S) x ∧
    SvOscAt (svComp (svSingleton f) S) x ∧
    ∀ᶠ a in 𝓝 x, IsClosed (svComp (svSingleton f) S a) := by
  have hK := Metric.isCompact_of_isClosed_isBounded (hS x).isClosed hb.isBounded_apply
  obtain ⟨C,hC,hSC,hCf⟩ := exists_compact_between hK (isOpen_setOf_strictlyContinuousAt f) hf
  have hT := svOsc_restrictedSingleton hC (fun w hw ↦ (hCf hw).continuousAt.continuousWithinAt)
  obtain ⟨V,hV,hVC⟩ := (hS x).exists_nhds_svImage_subset hb isOpen_interior hSC
  have he : svComp (restrictedSingleton f C) S =ᶠ[𝓝 x] svComp (svSingleton f) S := by
    filter_upwards [hV] with a ha
    ext u
    constructor
    · intro hu
      obtain ⟨w,hw,huw⟩ := mem_svComp.mp hu
      exact mem_svComp.mpr ⟨w,hw,huw.2⟩
    · intro hu
      obtain ⟨w,hw,huw⟩ := mem_svComp.mp hu
      exact mem_svComp.mpr ⟨w,hw,interior_subset (hVC (mem_svImage.mpr ⟨a,ha,hw⟩)),huw⟩
  refine ⟨svLocallyBoundedAt_svComp (hS x) hb
    (fun w hw ↦ svLocallyBoundedAt_svSingleton_of_continuousAt (hf w hw).continuousAt),
    (svOscAt_congr he).mp (svOscAt_svComp_of_locallyBounded hS hT hb),?_⟩
  filter_upwards [hV] with a ha
  have hSa : S a ⊆ C := fun w hw ↦ interior_subset (hVC (mem_svImage.mpr ⟨a,ha,hw⟩))
  have hcSa : IsCompact (S a) := hC.of_isClosed_subset (hS a).isClosed hSa
  have heimage : svComp (svSingleton f) S a = f '' S a := by
    ext u
    simp only [mem_svComp,svSingleton,mem_singleton_iff,mem_image]
    exact ⟨fun ⟨w,hw,he⟩ ↦ ⟨w,hw,he.symm⟩,fun ⟨w,hw,he⟩ ↦ ⟨w,hw,he.symm⟩⟩
  rw [heimage]
  exact (hcSa.image_of_continuousOn (fun w hw ↦ (hCf (hSa hw)).continuousAt.continuousWithinAt)).isClosed

/-- **Exercise 10.39**, strict continuity and local boundedness when the
inner mapping is locally bounded. -/
theorem svStrictlyContinuousAt_outer_singleton_comp_of_locallyBounded (hS : SvOsc S)
    (hs : SvStrictlyContinuousAt S x) (hb : SvLocallyBoundedAt S x)
    (hf : ∀ w ∈ S x, StrictlyContinuousAt f w) :
    SvStrictlyContinuousAt (svComp (svSingleton f) S) x ∧ SvLocallyBoundedAt (svComp (svSingleton f) S) x := by
  obtain ⟨hbound,ho,hc⟩ := bounded_outer_singleton_composition_data hS hb hf
  exact ⟨svStrictlyContinuousAt_outer_singleton_comp_of_closed hS hs hf
    (fun u _ ↦ svLocallyBoundedAt_svCompAux_left hb u) ho hc,hbound⟩

/-- **Exercise 10.39**, both attained bounds for the radius-infinity
modulus. The first maximizes the product, and the second separates the
inner Hausdorff modulus from the maximum outer Lipschitz modulus. -/
theorem exists_max_outer_singleton_hausdorff_bounds (hS : SvOsc S)
    (hs : SvStrictlyContinuousAt S x) (hb : SvLocallyBoundedAt S x)
    (hf : ∀ w ∈ S x, StrictlyContinuousAt f w) :
    ∃ w ∈ S x, ∃ z ∈ S x,
      IsMaxOn (fun v ↦ graphicalLipschitzModulus S x v*lipschitzModulus f v) (S x) w ∧
      IsMaxOn (lipschitzModulus f) (S x) z ∧
      svHausdorffLipschitzModulus (svComp (svSingleton f) S) x ≤
        graphicalLipschitzModulus S x w*lipschitzModulus f w ∧
      graphicalLipschitzModulus S x w*lipschitzModulus f w ≤
        svHausdorffLipschitzModulus S x*lipschitzModulus f z := by
  have hK := Metric.isCompact_of_isClosed_isBounded (hS x).isClosed hb.isBounded_apply
  have hUS : UpperSemicontinuous (fun w ↦ graphicalLipschitzModulus S x w) :=
    (upperSemicontinuous_graphicalLipschitzModulusWithin S univ).comp (continuous_const.prodMk continuous_id)
  have hUF : UpperSemicontinuous (lipschitzModulus f) := upperSemicontinuous_lipschitzModulusWithin f univ
  have hprod : UpperSemicontinuousOn
      (fun w ↦ graphicalLipschitzModulus S x w*lipschitzModulus f w) (S x) := by
    intro w hw
    exact upperSemicontinuousWithinAt_ennreal_mul (hUS.upperSemicontinuousOn _ w hw)
      (hUF.upperSemicontinuousOn _ w hw)
      ((hasAubinPropertyWithinAt_iff_modulus_lt_top.mp (hs.hasAubinPropertyAt hw)).2.2.2) (hf w hw)
  obtain ⟨w,hw,hmw⟩ := UpperSemicontinuousOn.exists_isMaxOn hs.nonempty_isClosed.1 hK hprod
  obtain ⟨z,hz,hmz⟩ := UpperSemicontinuousOn.exists_isMaxOn hs.nonempty_isClosed.1 hK (hUF.upperSemicontinuousOn _)
  obtain ⟨hbound,ho,hc⟩ := bounded_outer_singleton_composition_data hS hb hf
  have hscomp := (svStrictlyContinuousAt_outer_singleton_comp_of_locallyBounded hS hs hb hf).1
  have hclosed : ∀ᶠ a in 𝓝 x, (svComp (svSingleton f) S a).Nonempty ∧ IsClosed (svComp (svSingleton f) S a) := by
    simpa only [nhdsWithin_univ] using hscomp.2.1
  refine ⟨w,hw,z,hz,hmw,hmz,?_,?_⟩
  · apply (svHausdorffLipschitzModulus_le_iSup_graphical ho hbound hclosed).trans
    refine iSup₂_le fun u hu ↦ ?_
    obtain ⟨v,hv,_,hvu⟩ := exists_max_outer_singleton_composition_modulus hS hs hf hu
      (svLocallyBoundedAt_svCompAux_left hb u)
    exact hvu.trans (hmw hv.1)
  · exact mul_le_mul' (graphicalLipschitzModulus_le_hausdorffModulus
      (by simpa only [nhdsWithin_univ] using hs.2.1) w) (hmz hw)

end RW
