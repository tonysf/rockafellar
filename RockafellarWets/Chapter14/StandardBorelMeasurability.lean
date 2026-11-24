/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Graph measurability on standard Borel spaces

Theorem 14.8 and Corollary 14.34 of Rockafellar–Wets assume that the σ-field `A` is "complete for
some measure"; the adapted statements (`graph_measurability`, `joint_measurability_criterion`)
assume completeness for an s-finite measure.  When `(T, A)` is a standard Borel space, e.g. `ℝᵈ`
with its Borel field, no measure is needed for closed-valued mappings into a proper metric space
such as `ℝⁿ`: the inverse image `S⁻¹(K)` of a compact set `K` is the projection of the Borel set
`gph S ∩ (T × K)`, whose sections `S(t) ∩ K` are compact, so it is Borel by Novikov's theorem
(`measurableSet_image_fst_of_isClosed_sections_of_isCompact` in `NovikovProjection`).

* `graph_measurability_standardBorel`: a closed-valued `S` is measurable iff `gph S` is
  `A ⊗ B(F)`-measurable.  The third property in 14.8, measurability of `S⁻¹(D)` for all Borel
  `D`, still fails on the Baire space `ℕ → ℕ`, which is standard Borel
  (`graph_measurability_closedValued_counterexample`).
* `joint_measurability_criterion_standardBorel`, and `joint_measurability_criterion_borel` for
  `T = ℝᵈ` with its Borel field (14.34): `f` is a normal integrand iff it is `A ⊗ B(E)`-measurable
  and lsc in `x`.

Exercise 14.35, the lim inf clause of Proposition 14.53(b) and the graph of `∂^∞f` in
Theorem 14.56 concern mappings that need not be closed-valued; their counterexamples
(`closure_integrand_counterexample`, `liminf_integrand_counterexample`,
`HorizonGraph.horizon_graph_counterexample`) live on the Baire space with its Borel field, so
there a completeness hypothesis cannot be dropped.

Some hypothesis on `(T, A)` is needed in 14.8 and 14.34 all the same: on a non-standard subspace of
the Baire space with the trace of the Borel field, both the converse of 14.34 and the closed-valued
(b) ⇒ (a) of 14.8 fail (`joint_measurability_criterion_counterexample`,
`graph_measurability_nonstandard_counterexample` in `BorelInseparability`).
-/

import RockafellarWets.Chapter14.IntegrandExamples
import RockafellarWets.Chapter14.NovikovProjection
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open Set MeasureTheory

noncomputable section

namespace RW

section GraphMeasurability

variable {T F : Type*} [MeasurableSpace T] [StandardBorelSpace T] [MetricSpace F] [ProperSpace F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Theorem 14.8**, (b) ⇒ (a) for closed-valued `S` on a standard Borel space, with no measure:
`S⁻¹(K)` is the projection of the Borel set `gph S ∩ (T × K)`, whose sections `S(t) ∩ K` are
closed subsets of the compact set `K` (Novikov's theorem). -/
theorem svMeasurable_of_measurableSet_svGraph_of_standardBorel {S : T → Set F}
    (hSc : ∀ t, IsClosed (S t)) (hS : MeasurableSet (svGraph S)) : SvMeasurable S := by
  refine svMeasurable_of_measurableSet_svPreimage_isCompact fun K hK ↦ ?_
  have heq : svPreimage S K = Prod.fst '' (svGraph S ∩ univ ×ˢ K) := by
    ext t
    simp only [mem_svPreimage, mem_image, mem_inter_iff, mem_svGraph, mem_prod, mem_univ,
      true_and, Prod.exists, exists_and_right, exists_eq_right]
    rfl
  rw [heq]
  refine measurableSet_image_fst_of_isClosed_sections_of_isCompact hK
    (hS.inter (MeasurableSet.univ.prod hK.measurableSet)) inter_subset_right fun t ↦ ?_
  rw [preimage_inter, mk_preimage_prod_right (mem_univ t)]
  exact (hSc t).inter hK.isClosed

/-- **Theorem 14.8 (graph measurability)** on a standard Borel space: a closed-valued `S` into a
proper metric space is measurable iff its graph is `A ⊗ B(F)`-measurable, with no measure.  The
third property, measurability of `S⁻¹(D)` for all Borel `D`, implies both
(`svMeasurable_of_measurableSet_svPreimage_borel`) but is not implied by them, even on the Baire
space (`graph_measurability_closedValued_counterexample`). -/
theorem graph_measurability_standardBorel {S : T → Set F} (hSc : ∀ t, IsClosed (S t)) :
    SvMeasurable S ↔ MeasurableSet (svGraph S) :=
  ⟨fun h ↦ h.measurableSet_svGraph hSc,
    svMeasurable_of_measurableSet_svGraph_of_standardBorel hSc⟩

end GraphMeasurability

section JointMeasurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Corollary 14.34**, converse, on a standard Borel space: an `A ⊗ B(E)`-measurable `f` that
is lsc in `x` is a normal integrand, with no measure (its level-set mappings are closed-valued with
measurable graphs, and 14.8 applies). -/
theorem isNormalIntegrand_of_measurable_uncurry_of_standardBorel {T : Type*} [MeasurableSpace T]
    [StandardBorelSpace T] {f : T → E → EReal} (hf : Measurable (Function.uncurry f))
    (hlsc : ∀ t, LowerSemicontinuous (f t)) : IsNormalIntegrand f := by
  rw [measurability_of_level_set_mappings]
  intro α
  have hc : ∀ t, IsClosed {x | f t x ≤ α} := fun t ↦ (hlsc t).isClosed_preimage (α : EReal)
  exact ⟨hc, svMeasurable_of_measurableSet_svGraph_of_standardBorel hc (hf measurableSet_Iic)⟩

/-- **Corollary 14.34 (joint measurability criterion)** on a standard Borel space: `f` is a normal
integrand iff it is `A ⊗ B(E)`-measurable and lsc in `x`. -/
theorem joint_measurability_criterion_standardBorel {T : Type*} [MeasurableSpace T]
    [StandardBorelSpace T] {f : T → E → EReal} :
    IsNormalIntegrand f ↔ Measurable (Function.uncurry f) ∧ ∀ t, LowerSemicontinuous (f t) :=
  ⟨fun hf ↦ ⟨hf.measurable_uncurry, hf.lowerSemicontinuous⟩,
    fun h ↦ isNormalIntegrand_of_measurable_uncurry_of_standardBorel h.1 h.2⟩

/-- **Corollary 14.34** for `T = ℝᵈ` with its Borel field `B(ℝᵈ)`: `f` is a normal integrand iff
it is `B(ℝᵈ) ⊗ B(E)`-measurable and lsc in `x` (for the Lebesgue field `L(ℝᵈ)` named in the book
see `joint_measurability_criterion_lebesgue`). -/
theorem joint_measurability_criterion_borel {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → E → EReal} :
    IsNormalIntegrand f ↔ Measurable (Function.uncurry f) ∧ ∀ t, LowerSemicontinuous (f t) :=
  joint_measurability_criterion_standardBorel

end JointMeasurability

end RW
