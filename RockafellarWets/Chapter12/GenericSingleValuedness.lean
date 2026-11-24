/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Generic single-valuedness from monotonicity

Corollary 12.66.

As in the book, the resolvent `R = (I + T)⁻¹` is nonexpansive with
`rge R = dom T`, and by Theorem 12.65 ((c′) ⇒ (a′)) a point `x = R(z)` at which
`T` is not differentiable has a preimage `z` at which `R` is not differentiable
or `∇R(z)` is singular.  Such values are negligible by Mignot's theorem 9.65.
This even shows that `T` is differentiable almost everywhere on `dom T`, not only
on `int(dom T)`.  Part (b) is part (a) for the maximal monotone mapping `T⁻¹`.
Negligibility is with respect to any additive Haar measure, Lebesgue measure on
`IRⁿ` in particular.  A measure-free consequence used for 12.67 is that the
differentiability points of `T` are dense in `int(dom T)`.
-/

import RockafellarWets.Chapter12.MonotoneSemidifferentiability
import RockafellarWets.Chapter9.RegularValues

open Filter MeasureTheory Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A set-valued mapping that is differentiable at `x` is single-valued there. -/
theorem SvDifferentiableAt.exists_eq_singleton {T : E → Set E} {x : E}
    (h : SvDifferentiableAt T x) : ∃ v, T x = {v} := by
  obtain ⟨u, A, he⟩ := h
  exact ⟨u, (graphicalDerivative_and_linearGrowth_of_expansion A.continuous
    (svPositivelyHomogeneous_svSingleton_continuousLinearMap A) he).2.baseFiber⟩

omit [FiniteDimensional ℝ E] in
/-- A set-valued mapping that is differentiable at `x` is nonempty-valued around
`x`, so `x ∈ int(dom T)`. -/
theorem SvDifferentiableAt.mem_interior_svDom {T : E → Set E} {x : E}
    (h : SvDifferentiableAt T x) : x ∈ interior (svDom T) := by
  obtain ⟨u, A, he⟩ := h
  rw [mem_interior_iff_mem_nhds]
  exact (he 1 one_pos).mono fun y hy ↦ hy.1

/-- The points of `dom T` where a maximal monotone `T` is not differentiable are
values `R(z)` of the resolvent `R = (I + T)⁻¹` that are not regular values: some
preimage `z` is a nondifferentiability point of `R` or has `det ∇R(z) = 0`. -/
theorem SvMaximalMonotone.not_svDifferentiableAt_subset {T : E → Set E}
    (hT : SvMaximalMonotone T) :
    {x ∈ svDom T | ¬ SvDifferentiableAt T x} ⊆
      resolventMap T 1 '' univ \ regularValuesWithin (resolventMap T 1) univ := by
  rintro x ⟨⟨v, hv⟩, hnd⟩
  have hR : resolventMap T 1 (x + (1 : ℝ) • v) = x := hT.resolventMap_add_smul one_pos hv
  refine ⟨⟨_, mem_univ _, hR⟩, fun hreg ↦ hnd ?_⟩
  obtain ⟨hd, hdet⟩ := hreg.2 _ (mem_univ _) hR
  exact (hT.svDifferentiableAt_iff hv).2
    ((hT.exists_linear_iff_differentiableAt_resolventMap hv one_pos).2 ⟨hd, hdet⟩)

section Measure

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A maximal monotone mapping is differentiable at almost every point of its
domain. -/
theorem SvMaximalMonotone.measure_not_svDifferentiableAt {T : E → Set E}
    (hT : SvMaximalMonotone T) : μ {x ∈ svDom T | ¬ SvDifferentiableAt T x} = 0 :=
  measure_mono_null hT.not_svDifferentiableAt_subset
    (measure_nonregularValues_eq_zero μ fun z _ ↦ hT.strictlyContinuousAt_resolventMap one_pos z)

/-- **Corollary 12.66(a)**: the points of `int(dom T)` where a maximal monotone
`T` fails to be differentiable form a negligible set; in particular `T` is
single-valued almost everywhere on `int(dom T)`. -/
theorem SvMaximalMonotone.generic_differentiability {T : E → Set E} (hT : SvMaximalMonotone T) :
    μ {x ∈ interior (svDom T) | ¬ SvDifferentiableAt T x} = 0 ∧
      ∀ᵐ x ∂μ, x ∈ interior (svDom T) → ∃ v, T x = {v} := by
  have hnull : μ {x ∈ interior (svDom T) | ¬ SvDifferentiableAt T x} = 0 :=
    measure_mono_null (show {x ∈ interior (svDom T) | ¬ SvDifferentiableAt T x} ⊆
        {x ∈ svDom T | ¬ SvDifferentiableAt T x} from fun x hx ↦ ⟨interior_subset hx.1, hx.2⟩)
      (hT.measure_not_svDifferentiableAt μ)
  refine ⟨hnull, ?_⟩
  filter_upwards [compl_mem_ae_iff.2 hnull] with x hx hint
  by_contra hns
  exact hx ⟨hint, fun hd ↦ hns hd.exists_eq_singleton⟩

/-- **Corollary 12.66 (generic single-valuedness from monotonicity)**.  For a
maximal monotone `T`: (a) the points of `int(dom T)` where `T` fails to be
differentiable form a negligible set, so `T` is single-valued almost everywhere on
`int(dom T)`; (b) the points of `int(rge T)` where `T⁻¹` fails to be
differentiable form a negligible set, so `T⁻¹` is single-valued almost everywhere
on `int(rge T)`. -/
theorem generic_single_valuedness_from_monotonicity {T : E → Set E}
    (hT : SvMaximalMonotone T) :
    (μ {x ∈ interior (svDom T) | ¬ SvDifferentiableAt T x} = 0 ∧
      ∀ᵐ x ∂μ, x ∈ interior (svDom T) → ∃ v, T x = {v}) ∧
    (μ {u ∈ interior (svRange T) | ¬ SvDifferentiableAt (svInv T) u} = 0 ∧
      ∀ᵐ u ∂μ, u ∈ interior (svRange T) → ∃ x, svInv T u = {x}) := by
  refine ⟨hT.generic_differentiability μ, ?_⟩
  have h := hT.inv.generic_differentiability μ
  rwa [svDom_svInv] at h

end Measure

/-- The differentiability points of a maximal monotone `T` are dense in
`int(dom T)` (12.66(a); a nonempty open set has positive measure). -/
theorem SvMaximalMonotone.interior_svDom_subset_closure_svDifferentiableAt {T : E → Set E}
    (hT : SvMaximalMonotone T) :
    interior (svDom T) ⊆ closure {x ∈ interior (svDom T) | SvDifferentiableAt T x} := by
  borelize E
  have hnull := (hT.generic_differentiability (Measure.addHaar : Measure E)).1
  have hD := Measure.dense_of_ae (μ := (Measure.addHaar : Measure E)) (compl_mem_ae_iff.2 hnull)
  intro x hx
  rw [_root_.mem_closure_iff]
  intro U hU hxU
  obtain ⟨y, hy, hyU, hyI⟩ := hD.exists_mem_open (hU.inter isOpen_interior) ⟨x, hxU, hx⟩
  refine ⟨y, hyU, hyI, ?_⟩
  by_contra hnd
  exact hy ⟨hyI, hnd⟩

end RW
