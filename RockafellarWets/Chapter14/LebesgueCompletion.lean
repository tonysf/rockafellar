/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Completed σ-fields and the Lebesgue field

The corrected Theorem 14.8 and its consequences 14.34, 14.35, 14.53(b) and 14.56 (graph of
`∂^∞f`) assume that the σ-field `A` is complete for an s-finite measure; the book names the
Lebesgue field `L(ℝᵈ)` as the main example (14.34).  A measure `μ` on `(T, A)` has the completion
`μ.completion` on the type synonym `NullMeasurableSpace T μ`, whose σ-field consists of the
`μ`-null-measurable sets; for `T = ℝᵈ` and Lebesgue measure `volume` this is `L(ℝᵈ)`.  Mathlib
provides the completeness of `μ.completion` but neither its σ-finiteness nor its s-finiteness,
which are supplied here (`sigmaFinite_completion`, `sFinite_completion`).  The adapted statements
then apply to the completion of any s-finite measure (for instance
`(graph_measurability hSc).2.2 μ.completion`); the corollaries below are stated for σ-finite
measures and in particular for `T = ℝᵈ` with `A = L(ℝᵈ)`.
-/

import RockafellarWets.Chapter14.IntegrandOperations
import RockafellarWets.Chapter14.SubgradientMeasurability
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open Set Filter Topology MeasureTheory

noncomputable section

namespace RW

/-- The completion of a σ-finite measure is σ-finite (the spanning sets of `μ` serve). -/
instance sigmaFinite_completion {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] : SigmaFinite μ.completion := by
  refine ⟨⟨⟨spanningSets μ, fun _ ↦ trivial, fun i ↦ ?_, iUnion_spanningSets μ⟩⟩⟩
  rw [Measure.completion_apply]
  exact measure_spanningSets_lt_top μ i

/-- The completion of an s-finite measure is s-finite: each finite summand `sfiniteSeq μ n ≤ μ`
extends to the `μ`-null-measurable sets, as its pullback along the identity
`NullMeasurableSpace α μ → α`, and these extensions add up to `μ.completion`. -/
instance sFinite_completion {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] :
    SFinite μ.completion := by
  have hac : ∀ n, sfiniteSeq μ n ≪ μ := fun n ↦
    Measure.absolutelyContinuous_of_le (sfiniteSeq_le μ n)
  have key : ∀ t : Set α, NullMeasurableSet t μ → μ t = ∑' n, sfiniteSeq μ n t := by
    intro t ht
    have h := Measure.sum_apply (sfiniteSeq μ) (measurableSet_toMeasurable μ t)
    rw [sum_sfiniteSeq, measure_toMeasurable] at h
    rw [h]
    congr 1
    funext n
    exact measure_congr ((hac n).ae_eq ht.toMeasurable_ae_eq)
  set ι : NullMeasurableSpace α μ → α := id with hιdef
  have hι : ∀ n (s : Set (NullMeasurableSpace α μ)), MeasurableSet s →
      NullMeasurableSet (ι '' s) (sfiniteSeq μ n) := fun n s hs ↦ by
    rw [hιdef, image_id]
    exact NullMeasurableSet.mono_ac (μ := μ) hs (hac n)
  refine ⟨⟨fun n ↦ (sfiniteSeq μ n).comap ι, fun n ↦ ⟨?_⟩, ?_⟩⟩
  · rw [Measure.comap_apply₀ ι _ Function.injective_id (hι n)
      MeasurableSet.univ.nullMeasurableSet]
    exact measure_lt_top _ _
  · ext s hs
    rw [Measure.sum_apply _ hs, Measure.completion_apply]
    simp_rw [Measure.comap_apply₀ ι _ Function.injective_id (hι _) hs.nullMeasurableSet, hιdef,
      image_id]
    exact key s hs

section Completion

variable {T : Type*} [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]

/-- **Theorem 14.8** on the completion of a σ-finite measure: for closed-valued `S`, the three
properties (a) measurability, (b) `A ⊗ B(F)`-measurability of the graph and (c) measurability of
`S⁻¹(D)` for all Borel `D` are equivalent when `A` is the σ-field of `μ`-null-measurable sets. -/
theorem graph_measurability_completion {F : Type*} [MetricSpace F] [ProperSpace F]
    [MeasurableSpace F] [BorelSpace F] {S : NullMeasurableSpace T μ → Set F}
    (hSc : ∀ t, IsClosed (S t)) :
    List.TFAE [SvMeasurable S, MeasurableSet (svGraph S),
      ∀ D : Set F, MeasurableSet D → MeasurableSet (svPreimage S D)] :=
  (graph_measurability hSc).2.2 μ.completion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Corollary 14.34 (joint measurability criterion)** on the completion of a σ-finite measure:
`f` is a normal integrand iff it is `A ⊗ B(E)`-measurable and lsc in `x`. -/
theorem joint_measurability_criterion_completion {f : NullMeasurableSpace T μ → E → EReal} :
    IsNormalIntegrand f ↔ Measurable (Function.uncurry f) ∧ ∀ t, LowerSemicontinuous (f t) :=
  joint_measurability_criterion.2 μ.completion

/-- **Exercise 14.35** on the completion of a σ-finite measure: `cl f₀(t, ·)` is a normal
integrand for every `A ⊗ B(E)`-measurable `f₀`. -/
theorem isNormalIntegrand_epiClosure_of_measurable_completion
    {f₀ : NullMeasurableSpace T μ → E → EReal} (hf₀ : Measurable (Function.uncurry f₀)) :
    IsNormalIntegrand (fun t ↦ epiClosure (f₀ t)) :=
  isNormalIntegrand_epiClosure_of_measurable μ.completion hf₀

/-- **Proposition 14.53(b)**, lim inf clause, on the completion of a σ-finite measure:
`cl [p-lim inf fν(t, ·)]` is a normal integrand for normal integrands `fν`. -/
theorem IsNormalIntegrand.epiClosure_liminf_completion
    {f : ℕ → NullMeasurableSpace T μ → E → EReal} (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand (fun t ↦ epiClosure (fun x ↦ Filter.liminf (fun n ↦ f n t x) atTop)) :=
  IsNormalIntegrand.epiClosure_liminf μ.completion hf

end Completion

section Subgradients

variable {T : Type*} [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Theorem 14.56**, graphical mappings, on the completion of a σ-finite measure:
`t ↦ gph ∂f(t, ·)` and `t ↦ gph ∂^∞f(t, ·)` are measurable for every normal integrand. -/
theorem svMeasurable_svGraph_subdifferential_completion
    {f : NullMeasurableSpace T μ → E → EReal} (hf : IsNormalIntegrand f) :
    SvMeasurable (fun t ↦ svGraph (subdifferential (f t))) ∧
      SvMeasurable (fun t ↦ svGraph (horizonSubdifferential (f t))) :=
  svMeasurable_svGraph_subdifferential_of_isComplete μ.completion hf

end Subgradients

section Lebesgue

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Corollary 14.34** for `T = ℝᵈ` with the Lebesgue field `A = L(ℝᵈ)` (the σ-field of
`volume`-null-measurable sets), the case named in the book: `f` is a normal integrand iff it is
`L(ℝᵈ) ⊗ B(E)`-measurable and lsc in `x`. -/
theorem joint_measurability_criterion_lebesgue
    {f : NullMeasurableSpace (EuclideanSpace ℝ (Fin d))
      (volume : Measure (EuclideanSpace ℝ (Fin d))) → E → EReal} :
    IsNormalIntegrand f ↔ Measurable (Function.uncurry f) ∧ ∀ t, LowerSemicontinuous (f t) :=
  joint_measurability_criterion_completion _

/-- **Exercise 14.35** for `T = ℝᵈ` with the Lebesgue field `L(ℝᵈ)`. -/
theorem isNormalIntegrand_epiClosure_of_measurable_lebesgue
    {f₀ : NullMeasurableSpace (EuclideanSpace ℝ (Fin d))
      (volume : Measure (EuclideanSpace ℝ (Fin d))) → E → EReal}
    (hf₀ : Measurable (Function.uncurry f₀)) :
    IsNormalIntegrand (fun t ↦ epiClosure (f₀ t)) :=
  isNormalIntegrand_epiClosure_of_measurable_completion _ hf₀

/-- **Proposition 14.53(b)**, lim inf clause, for `T = ℝᵈ` with the Lebesgue field `L(ℝᵈ)`. -/
theorem IsNormalIntegrand.epiClosure_liminf_lebesgue
    {f : ℕ → NullMeasurableSpace (EuclideanSpace ℝ (Fin d))
      (volume : Measure (EuclideanSpace ℝ (Fin d))) → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand (fun t ↦ epiClosure (fun x ↦ Filter.liminf (fun n ↦ f n t x) atTop)) :=
  IsNormalIntegrand.epiClosure_liminf_completion _ hf

end Lebesgue

end RW
