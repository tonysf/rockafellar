/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost everywhere differentiability on the strict continuity locus
-/

import RockafellarWets.Chapter9.LipschitzModulus
import Mathlib.Analysis.Calculus.Rademacher

open Filter Metric Set Topology MeasureTheory
open scoped NNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F} {O : Set E} {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- **Theorem 9.60 (Rademacher).** A mapping is differentiable almost
everywhere on its strict continuity locus. Local Lipschitz constants may
depend on the point. -/
theorem ae_differentiableAt_of_strictlyContinuousAt (f : E → F) (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    ∀ᵐ x ∂μ, StrictlyContinuousAt f x → DifferentiableAt ℝ f x := by
  classical
  let B := TopologicalSpace.countableBasis E
  have hb := TopologicalSpace.isBasis_countableBasis E
  haveI : Countable B := TopologicalSpace.countable_countableBasis E
  have h (V : B) : ∀ᵐ x ∂μ, (∃ k, LipschitzOnWith k f (V : Set E)) → x ∈ V.val → DifferentiableAt ℝ f x := by
    by_cases he : ∃ k, LipschitzOnWith k f (V : Set E)
    · obtain ⟨k,hk⟩ := he
      filter_upwards [hk.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx _ hxV
      exact (hx hxV).differentiableAt ((hb.isOpen V.property).mem_nhds hxV)
    · exact .of_forall fun _ h ↦ (he h).elim
  filter_upwards [ae_all_iff.mpr h] with x hall hx
  obtain ⟨k,U,hU,hk⟩ := strictlyContinuousAt_iff.mp hx
  obtain ⟨V,hVB,hxV,hVU⟩ := hb.mem_nhds_iff.mp hU
  exact hall ⟨V,hVB⟩ ⟨k,hk.mono hVU⟩ hxV

/-- The differentiability points in an open region of strict continuity
are dense in that region. -/
theorem subset_closure_differentiableAt_of_strictlyContinuousOn (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (hO : IsOpen O) (hf : ∀ x ∈ O, StrictlyContinuousAt f x) :
    O ⊆ closure {x ∈ O | DifferentiableAt ℝ f x} := by
  have hD := Measure.dense_of_ae (ae_differentiableAt_of_strictlyContinuousAt f μ)
  intro x hx
  rw [_root_.mem_closure_iff]
  intro U hU hxU
  obtain ⟨y,hy,hyU,hyO⟩ := hD.exists_mem_open (hU.inter hO) ⟨x,hxU,hx⟩
  exact ⟨y,hyU,hyO,hy (hf y hyO)⟩

end RW
