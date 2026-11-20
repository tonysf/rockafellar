/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Attainment of the composition modulus bound
-/

import RockafellarWets.Chapter10.CompositionLipschitz

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

/-- Products of finite nonnegative upper semicontinuous functions are
upper semicontinuous, even when neighboring values may be infinite. -/
theorem upperSemicontinuousWithinAt_ennreal_mul {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ≥0∞} {A : Set X} {x : X}
    (hf : UpperSemicontinuousWithinAt f A x) (hg : UpperSemicontinuousWithinAt g A x)
    (hfin : f x < ⊤) (hgfin : g x < ⊤) :
    UpperSemicontinuousWithinAt (fun y ↦ f y*g y) A x := by
  intro r hr
  have hc := ENNReal.tendsto_mul (a := f x) (b := g x) (Or.inr hgfin.ne) (Or.inr hfin.ne)
  obtain ⟨U,V,hU,hxU,hV,hxV,hUV⟩ := mem_nhds_prod_iff'.mp (hc (gt_mem_nhds hr))
  obtain ⟨a,ha,haU⟩ := exists_Ico_subset_of_mem_nhds (hU.mem_nhds hxU) ⟨⊤,hfin⟩
  obtain ⟨b,hb,hbV⟩ := exists_Ico_subset_of_mem_nhds (hV.mem_nhds hxV) ⟨⊤,hgfin⟩
  filter_upwards [hf a ha,hg b hb] with y hya hyb
  have hu : max (f y) (f x) ∈ U := haU ⟨le_max_right _ _,max_lt hya ha⟩
  have hv : max (g y) (g x) ∈ V := hbV ⟨le_max_right _ _,max_lt hyb hb⟩
  have hlt : max (f y) (f x) * max (g y) (g x) < r :=
    hUV (a := (max (f y) (f x),max (g y) (g x))) ⟨hu,hv⟩
  exact (mul_le_mul' (le_max_left _ _) (le_max_left _ _)).trans_lt hlt

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {T : F → Set G} {x : E} {u : G}

theorem isCompact_svCompAux (hS : SvOsc S) (hT : SvOsc T)
    (hb : SvLocallyBoundedAt (svCompAux T S) (x,u)) : IsCompact (svCompAux T S (x,u)) :=
  Metric.isCompact_of_isClosed_isBounded ((svOsc_svCompAux hS hT) (x,u)).isClosed hb.isBounded_apply

/-- **Corollary 10.38**, the product bound is attained at an intermediate
value, so the displayed supremum is a genuine maximum. -/
theorem exists_max_composition_modulus (hS : SvOsc S) (hT : SvOsc T)
    (hu : u ∈ svComp T S x) (hb : SvLocallyBoundedAt (svCompAux T S) (x,u))
    (haS : ∀ w ∈ svCompAux T S (x,u), HasAubinPropertyAt S x w)
    (haT : ∀ w ∈ svCompAux T S (x,u), HasAubinPropertyAt T w u) :
    ∃ w ∈ svCompAux T S (x,u),
      IsMaxOn (fun w ↦ graphicalLipschitzModulus S x w * graphicalLipschitzModulus T w u)
        (svCompAux T S (x,u)) w ∧
      graphicalLipschitzModulus (svComp T S) x u ≤
        graphicalLipschitzModulus S x w * graphicalLipschitzModulus T w u := by
  have hne : (svCompAux T S (x,u)).Nonempty := by
    obtain ⟨w,hw,hu⟩ := mem_svComp.mp hu
    exact ⟨w,hw,hu⟩
  have hU : UpperSemicontinuousOn
      (fun w ↦ graphicalLipschitzModulus S x w * graphicalLipschitzModulus T w u)
      (svCompAux T S (x,u)) := by
    intro w hw
    have h₁ : UpperSemicontinuous (fun w ↦ graphicalLipschitzModulus S x w) :=
      (upperSemicontinuous_graphicalLipschitzModulusWithin S univ).comp
        (continuous_const.prodMk continuous_id)
    have h₂ : UpperSemicontinuous (fun w ↦ graphicalLipschitzModulus T w u) :=
      (upperSemicontinuous_graphicalLipschitzModulusWithin T univ).comp
        (continuous_id.prodMk continuous_const)
    exact upperSemicontinuousWithinAt_ennreal_mul (h₁.upperSemicontinuousOn _ w hw)
      (h₂.upperSemicontinuousOn _ w hw)
      (hasAubinPropertyWithinAt_iff_modulus_lt_top.mp (haS w hw)).2.2.2
      (hasAubinPropertyWithinAt_iff_modulus_lt_top.mp (haT w hw)).2.2.2
  obtain ⟨w,hw,hm⟩ := UpperSemicontinuousOn.exists_isMaxOn hne (isCompact_svCompAux hS hT hb) hU
  exact ⟨w,hw,hm,(graphicalLipschitzModulus_svComp_le_iSup hS hT hu hb haS haT).trans
    (iSup₂_le fun v hv ↦ hm hv)⟩

end RW
