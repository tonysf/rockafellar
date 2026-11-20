/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Negligibility of singular values of locally Lipschitz maps
-/

import RockafellarWets.Chapter9.Rademacher
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.Jacobian

open Filter Metric Set Topology MeasureTheory
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {f : E → E} {O A : Set E}
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- A Lipschitz map between spaces of the same finite dimension preserves
sets of Haar measure zero. -/
theorem measure_image_eq_zero_of_lipschitzOnWith {k : ℝ≥0} (hf : LipschitzOnWith k f A)
    (hA : μ A = 0) : μ (f '' A) = 0 := by
  let ν : Measure E := μH[Module.finrank ℝ E]
  have hνA : ν A = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure ν μ) hA
  have hνImage : ν (f '' A) = 0 := by
    apply le_antisymm _ (zero_le _)
    have h := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
    change ν (f '' A) ≤ _ * ν A at h
    simpa only [hνA,mul_zero] using h
  exact (Measure.absolutelyContinuous_isAddHaarMeasure μ ν) hνImage

/-- The same null-set property holds with pointwise local Lipschitz constants. -/
theorem measure_image_eq_zero_of_strictlyContinuousOn (hf : ∀ x ∈ O, StrictlyContinuousAt f x)
    (hAO : A ⊆ O) (hA : μ A = 0) : μ (f '' A) = 0 := by
  classical
  let B := TopologicalSpace.countableBasis E
  have hb := TopologicalSpace.isBasis_countableBasis E
  let good := {V : B // ∃ k, LipschitzOnWith k f (V : Set E)}
  have cover : A ⊆ ⋃ V : good, A ∩ (V.val : Set E) := by
    intro x hx
    obtain ⟨k,U,hU,hk⟩ := strictlyContinuousAt_iff.mp (hf x (hAO hx))
    obtain ⟨V,hVB,hxV,hVU⟩ := hb.mem_nhds_iff.mp hU
    exact mem_iUnion.mpr ⟨⟨⟨V,hVB⟩,k,hk.mono hVU⟩,hx,hxV⟩
  apply measure_mono_null (image_mono cover)
  rw [image_iUnion]
  apply measure_iUnion_null
  intro V
  obtain ⟨k,hk⟩ := V.property
  exact measure_image_eq_zero_of_lipschitzOnWith μ (hk.mono inter_subset_right) (measure_mono_null inter_subset_left hA)

/-- Values all of whose preimages in a specified region are differentiability
points with nonsingular derivative. -/
def regularValuesWithin (f : E → E) (O : Set E) : Set E :=
  {y | y ∈ f '' O ∧ ∀ x ∈ O, f x = y → DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det ≠ 0}

/-- **Theorem 9.65 (Mignot).** The image values having any singular or
nondifferentiable preimage form a negligible set. -/
theorem measure_nonregularValues_eq_zero (hf : ∀ x ∈ O, StrictlyContinuousAt f x) :
    μ (f '' O \ regularValuesWithin f O) = 0 := by
  let N := {x ∈ O | ¬DifferentiableAt ℝ f x}
  let C := {x ∈ O | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det = 0}
  have hN : μ N = 0 := by
    apply measure_mono_null _ (ae_iff.mp (ae_differentiableAt_of_strictlyContinuousAt f μ))
    intro x hx h
    exact hx.2 (h (hf x hx.1))
  have himageN := measure_image_eq_zero_of_strictlyContinuousOn μ hf (fun _ h ↦ h.1) hN
  have himageC : μ (f '' C) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun _ h ↦ h.2.1.hasFDerivAt.hasFDerivWithinAt) (fun _ h ↦ h.2.2)
  apply measure_mono_null _ (measure_union_null himageN himageC)
  rintro y ⟨hy,hbad⟩
  have h := not_forall.mp (fun h ↦ hbad ⟨hy,h⟩)
  obtain ⟨x,hx⟩ := h
  push_neg at hx
  rcases hx with ⟨hxO,hxy,hx⟩
  by_cases hd : DifferentiableAt ℝ f x
  · right
    exact ⟨x,⟨hxO,hd,hx hd⟩,hxy⟩
  · left
    exact ⟨x,⟨hxO,hd⟩,hxy⟩

/-- Regular values are dense in the interior of the image. -/
theorem interior_image_subset_closure_regularValues (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (hf : ∀ x ∈ O, StrictlyContinuousAt f x) :
    interior (f '' O) ⊆ closure (regularValuesWithin f O) := by
  have hnull := measure_nonregularValues_eq_zero μ hf
  have hD := Measure.dense_of_ae (compl_mem_ae_iff.mpr hnull)
  intro y hy
  rw [_root_.mem_closure_iff]
  intro U hU hyU
  obtain ⟨z,hz,hzU,hzI⟩ := hD.exists_mem_open (hU.inter isOpen_interior) ⟨y,hyU,hy⟩
  exact ⟨z,hzU,Classical.byContradiction fun h ↦ hz ⟨interior_subset hzI,h⟩⟩

end RW
