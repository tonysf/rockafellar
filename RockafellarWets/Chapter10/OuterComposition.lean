/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Composition with a single-valued outer mapping
-/

import RockafellarWets.Chapter10.OuterCompositionLocalization

open Filter Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {f : F → G} {x : E} {u : G}

/-- **Exercise 10.39**, the coderivative inclusion. Strict continuity is
required only at points of the base fiber, as in the book. -/
theorem coderivative_outer_singleton_comp_subset (hS : SvOsc S)
    (hf : ∀ w ∈ S x, StrictlyContinuousAt f w)
    (hb : SvLocallyBoundedAt (svCompAux (svSingleton f) S) (x,u)) (y : G) :
    coderivative (svComp (svSingleton f) S) x u y ⊆
      ⋃ w ∈ svCompAux (svSingleton f) S (x,u),
        svComp (coderivative S x w) (coderivative (svSingleton f) w (f w)) y := by
  obtain ⟨C,hC,hKC,_,ho,hb',hK,he⟩ := exists_outerComposition_cutoff hS hf hb
  have ha (w : F) (hw : w ∈ svCompAux (restrictedSingleton f C) S (x,u)) :
      HasAubinPropertyAt (restrictedSingleton f C) w u := by
    have hw' := hK ▸ hw
    have hue : u = f w := hw'.2
    rw [hue]
    exact (hf w hw'.1).hasAubinProperty_singleton.congr_nhds (restrictedSingleton_eventuallyEq (hKC hw')).symm
  have hinc := coderivative_svComp_subset hS ho hb'
    (fun w hw ↦ compositionCoderivativeQualification_of_aubin_outer (ha w hw)) y
  rw [coderivative_congr_graph_nhds he] at hinc
  intro v hv
  obtain ⟨w,hw,hv⟩ := mem_iUnion₂.mp (hinc hv)
  have hw' := hK ▸ hw
  refine mem_iUnion₂.mpr ⟨w,hw',?_⟩
  have hue : u = f w := hw'.2
  rwa [coderivative_congr_nhds (restrictedSingleton_eventuallyEq (hKC hw')) u,hue] at hv

/-- **Exercise 10.39**, the graph-local Lipschitz conclusion. -/
theorem hasAubinPropertyAt_outer_singleton_comp (hS : SvOsc S)
    (hs : SvStrictlyContinuousAt S x) (hf : ∀ w ∈ S x, StrictlyContinuousAt f w)
    (hu : u ∈ svComp (svSingleton f) S x)
    (hb : SvLocallyBoundedAt (svCompAux (svSingleton f) S) (x,u)) :
    HasAubinPropertyAt (svComp (svSingleton f) S) x u := by
  obtain ⟨C,hC,hKC,_,ho,hb',hK,he⟩ := exists_outerComposition_cutoff hS hf hb
  have he0 : (u ∈ svComp (restrictedSingleton f C) S x) = (u ∈ svComp (svSingleton f) S x) := he.eq_of_nhds
  apply (hasAubinPropertyAt_svComp hS ho (he0.symm ▸ hu) hb' (fun w hw ↦ hs.hasAubinPropertyAt hw.1) ?_).congr_graph_nhds he
  intro w hw
  have hw' := hK ▸ hw
  have hue : u = f w := hw'.2
  rw [hue]
  exact (hf w hw'.1).hasAubinProperty_singleton.congr_nhds (restrictedSingleton_eventuallyEq (hKC hw')).symm

/-- **Exercise 10.39**, the sharp product upper bound is attained on the
compact intermediate fiber. -/
theorem exists_max_outer_singleton_composition_modulus (hS : SvOsc S)
    (hs : SvStrictlyContinuousAt S x) (hf : ∀ w ∈ S x, StrictlyContinuousAt f w)
    (hu : u ∈ svComp (svSingleton f) S x)
    (hb : SvLocallyBoundedAt (svCompAux (svSingleton f) S) (x,u)) :
    ∃ w ∈ svCompAux (svSingleton f) S (x,u),
      IsMaxOn (fun w ↦ graphicalLipschitzModulus S x w*lipschitzModulus f w)
        (svCompAux (svSingleton f) S (x,u)) w ∧
      graphicalLipschitzModulus (svComp (svSingleton f) S) x u ≤
        graphicalLipschitzModulus S x w*lipschitzModulus f w := by
  obtain ⟨C,hC,hKC,_,ho,hb',hK,he⟩ := exists_outerComposition_cutoff hS hf hb
  have he0 : (u ∈ svComp (restrictedSingleton f C) S x) = (u ∈ svComp (svSingleton f) S x) := he.eq_of_nhds
  have ha (w : F) (hw : w ∈ svCompAux (restrictedSingleton f C) S (x,u)) :
      HasAubinPropertyAt (restrictedSingleton f C) w u := by
    have hw' := hK ▸ hw
    have hue : u = f w := hw'.2
    rw [hue]
    exact (hf w hw'.1).hasAubinProperty_singleton.congr_nhds (restrictedSingleton_eventuallyEq (hKC hw')).symm
  have hm (w : F) (hw : w ∈ svCompAux (svSingleton f) S (x,u)) :
      graphicalLipschitzModulus (restrictedSingleton f C) w u = lipschitzModulus f w := by
    rw [graphicalLipschitzModulus_congr_nhds (restrictedSingleton_eventuallyEq (hKC hw)) u]
    have hue : u = f w := hw.2
    rw [hue,graphicalLipschitzModulus_singleton (hf w hw.1).continuousAt]
  obtain ⟨w,hw,hmax,hbound⟩ := exists_max_composition_modulus hS ho (he0.symm ▸ hu) hb'
    (fun w hw ↦ hs.hasAubinPropertyAt hw.1) ha
  have hw' := hK ▸ hw
  refine ⟨w,hw',?_,?_⟩
  · intro z hz
    have hh := hmax (hK.symm ▸ hz)
    change graphicalLipschitzModulus S x z*graphicalLipschitzModulus (restrictedSingleton f C) z u ≤
      graphicalLipschitzModulus S x w*graphicalLipschitzModulus (restrictedSingleton f C) w u at hh
    rwa [hm z hz,hm w hw'] at hh
  · have hmod : graphicalLipschitzModulus (svComp (restrictedSingleton f C) S) x u =
        graphicalLipschitzModulus (svComp (svSingleton f) S) x u :=
      graphicalLipschitzModulusWithin_congr_graph_nhds (X := univ) he
    rwa [hmod,hm w hw'] at hbound

/-- Corrected strict-continuity clause: graph-local conclusions do not
supply outer semicontinuity or closed values of the entire composition. -/
theorem svStrictlyContinuousAt_outer_singleton_comp_of_closed (hS : SvOsc S)
    (hs : SvStrictlyContinuousAt S x) (hf : ∀ w ∈ S x, StrictlyContinuousAt f w)
    (hb : ∀ u ∈ svComp (svSingleton f) S x,
      SvLocallyBoundedAt (svCompAux (svSingleton f) S) (x,u))
    (ho : SvOscAt (svComp (svSingleton f) S) x)
    (hc : ∀ᶠ a in 𝓝 x, IsClosed (svComp (svSingleton f) S a)) :
    SvStrictlyContinuousAt (svComp (svSingleton f) S) x := by
  have hne : (svComp (svSingleton f) S x).Nonempty := by
    obtain ⟨w,hw⟩ := hs.nonempty_isClosed.1
    exact ⟨f w,mem_svComp.mpr ⟨w,hw,rfl⟩⟩
  exact SvStrictlyContinuousAt.of_osc_aubin_eventually_closed ho hne hc
    (fun u hu ↦ hasAubinPropertyAt_outer_singleton_comp hS hs hf hu (hb u hu))

end RW
