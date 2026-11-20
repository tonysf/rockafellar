/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Locality of graphical calculus
-/

import RockafellarWets.Chapter10.CompositionLipschitz
import RockafellarWets.Chapter9.HilbertLipschitzExtension
import RockafellarWets.Chapter9.StrictGraphicalDerivatives
import RockafellarWets.Chapter9.LocalizationDerivatives

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S T : E → Set F} {x : E} {u : F}

theorem svGraph_eventuallyEq_of_eventuallyEq (h : S =ᶠ[𝓝 x] T) (u : F) :
    svGraph S =ᶠ[𝓝 (x,u)] svGraph T := by
  filter_upwards [(continuous_fst.tendsto (x,u)).eventually h] with p hp
  change (p.2 ∈ S p.1) = (p.2 ∈ T p.1)
  rw [hp]

theorem euclideanSvGraph_eventuallyEq_of_eventuallyEq (h : S =ᶠ[𝓝 x] T) (u : F) :
    euclideanSvGraph S =ᶠ[𝓝 (WithLp.toLp 2 (x,u))] euclideanSvGraph T := by
  filter_upwards [((WithLp.continuous_fst 2 E F).tendsto (WithLp.toLp 2 (x,u))).eventually h] with p hp
  change (p.snd ∈ S p.fst) = (p.snd ∈ T p.fst)
  rw [hp]

theorem coderivative_congr_nhds (h : S =ᶠ[𝓝 x] T) (u : F) :
    coderivative S x u = coderivative T x u := by
  unfold coderivative
  rw [normalCone_congr_nhds (euclideanSvGraph_eventuallyEq_of_eventuallyEq h u)]

theorem regularCoderivative_congr_nhds (h : S =ᶠ[𝓝 x] T) (u : F) :
    regularCoderivative S x u = regularCoderivative T x u := by
  unfold regularCoderivative
  rw [regularNormalCone_congr_nhds (euclideanSvGraph_eventuallyEq_of_eventuallyEq h u)]

theorem graphicalDerivative_congr_nhds (h : S =ᶠ[𝓝 x] T) (u : F) :
    graphicalDerivative S x u = graphicalDerivative T x u := by
  unfold graphicalDerivative
  rw [tangentCone_congr_nhds (euclideanSvGraph_eventuallyEq_of_eventuallyEq h u)]

theorem strictGraphicalDerivative_congr_nhds (h : S =ᶠ[𝓝 x] T) (u : F) :
    strictGraphicalDerivative S x u = strictGraphicalDerivative T x u := by
  unfold strictGraphicalDerivative
  rw [strictTangentCone_congr_nhds (svGraph_eventuallyEq_of_eventuallyEq h u)]

theorem AubinEstimate.congr_nhds {X : Set E} {k : ℝ≥0}
    (ha : AubinEstimate S X x u k) (h : S =ᶠ[𝓝 x] T) : AubinEstimate T X x u k := by
  obtain ⟨V,hV,W,hW,H⟩ := ha
  refine ⟨V ∩ {a | S a = T a},inter_mem hV h,W,hW,?_⟩
  intro a ha b hb v hv
  obtain ⟨z,hz,hd⟩ := H a ⟨ha.1,ha.2.1⟩ b ⟨hb.1,hb.2.1⟩ v ⟨ha.2.2 ▸ hv.1,hv.2⟩
  exact ⟨z,hb.2.2 ▸ hz,hd⟩

theorem HasAubinPropertyAt.congr_nhds (ha : HasAubinPropertyAt S x u) (h : S =ᶠ[𝓝 x] T) :
    HasAubinPropertyAt T x u := by
  obtain ⟨hx,hu,hc,k,hk⟩ := ha
  exact ⟨hx,h.eq_of_nhds ▸ hu,hc.congr_nhds (svGraph_eventuallyEq_of_eventuallyEq h u),k,hk.congr_nhds h⟩

theorem graphicalLipschitzModulus_congr_nhds (h : S =ᶠ[𝓝 x] T) (u : F) :
    graphicalLipschitzModulus S x u = graphicalLipschitzModulus T x u := by
  apply le_antisymm
  · exact le_iInf fun k ↦ (k.2.congr_nhds h.symm).modulus_le
  · exact le_iInf fun k ↦ (k.2.congr_nhds h).modulus_le

theorem IsGraphicallyRegularAt.congr_nhds (hr : IsGraphicallyRegularAt S x u)
    (h : S =ᶠ[𝓝 x] T) : IsGraphicallyRegularAt T x u := by
  have he := euclideanSvGraph_eventuallyEq_of_eventuallyEq h u
  refine ⟨hr.1.congr_nhds he,?_⟩
  rw [← normalCone_congr_nhds he,← regularNormalCone_congr_nhds he]
  exact hr.2

/-- A strictly continuous map can be replaced locally by a globally
Lipschitz map; this keeps composition theorems local in their hypotheses. -/
theorem StrictlyContinuousAt.exists_global_lipschitz_germ {f : E → F}
    (hf : StrictlyContinuousAt f x) :
    ∃ g : E → F, ∃ k : ℝ≥0, LipschitzWith k g ∧ f =ᶠ[𝓝 x] g := by
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp hf
  obtain ⟨g,hg,he⟩ := exists_lipschitz_extension_same_constant hL
  exact ⟨g,k,hg,Eventually.mono hU he⟩

end RW
