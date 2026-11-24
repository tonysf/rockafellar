/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Hulls and polars of measurable mappings

Exercise 14.12 of Rockafellar–Wets.  The convex, affine and linear hulls are written as
countable unions over `m` of the continuous images of `Λₘ × S(t)ᵐ` under
`(λ, x) ↦ ∑ λᵢ xᵢ` (this avoids Carathéodory's bound on `m`); the positive hull is
`{0} ∪ ⋃_{λ > 0} λ S(t)` (formula 3(11), `positiveHull`).  The polars follow the guide:
a Castaing representation of `cl S` and countable intersections of solid half-spaces.
-/

import RockafellarWets.Chapter14.MeasurableCompositions
import RockafellarWets.Chapter11.PolarSets
import RockafellarWets.Chapter6.Polarity
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Pointwise InnerProductSpace Classical

noncomputable section

namespace RW

section Hulls

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The finite combinations `∑ λᵢ xᵢ` with weights `λ ∈ Λ ⊂ ℝᵐ` and points `xᵢ ∈ A`. -/
def finCombinations (m : ℕ) (Λ : Set (Fin m → ℝ)) (A : Set E) : Set E :=
  (fun p : (Fin m → ℝ) × (Fin m → E) ↦ ∑ i, p.1 i • p.2 i) '' (Λ ×ˢ Set.pi univ fun _ ↦ A)

omit [FiniteDimensional ℝ E] in
theorem mem_finCombinations {m : ℕ} {Λ : Set (Fin m → ℝ)} {A : Set E} {x : E} :
    x ∈ finCombinations m Λ A ↔ ∃ w ∈ Λ, ∃ z : Fin m → E, (∀ i, z i ∈ A) ∧ ∑ i, w i • z i = x := by
  constructor
  · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
    exact ⟨w, hw, z, fun i ↦ hz i (mem_univ i), rfl⟩
  · rintro ⟨w, hw, z, hz, rfl⟩
    exact ⟨(w, z), ⟨hw, fun i _ ↦ hz i⟩, rfl⟩

theorem SvMeasurable.finCombinations {S : T → Set E} (hS : SvMeasurable S) (m : ℕ)
    (Λ : Set (Fin m → ℝ)) : SvMeasurable (fun t ↦ RW.finCombinations m Λ (S t)) :=
  ((svMeasurable_const Λ).prod (SvMeasurable.pi fun _ ↦ hS)).image
    (continuous_finset_sum _ fun i _ ↦
      ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd))

omit [FiniteDimensional ℝ E] in
theorem convexHull_eq_iUnion_finCombinations (A : Set E) :
    convexHull ℝ A = ⋃ m, finCombinations m {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} A := by
  ext x
  rw [mem_convexHull_iff_exists_fintype, mem_iUnion]
  constructor
  · rintro ⟨ι, _, w, z, hw0, hw1, hz, rfl⟩
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, mem_finCombinations.2 ⟨w ∘ e.symm, ⟨fun i ↦ hw0 _, ?_⟩, z ∘ e.symm,
      fun i ↦ hz _, ?_⟩⟩
    · rw [← hw1]
      exact e.symm.sum_comp w
    · exact e.symm.sum_comp (fun j ↦ w j • z j)
  · rintro ⟨m, hx⟩
    obtain ⟨w, ⟨hw0, hw1⟩, z, hz, rfl⟩ := mem_finCombinations.1 hx
    exact ⟨Fin m, inferInstance, w, z, hw0, hw1, hz, rfl⟩

omit [FiniteDimensional ℝ E] in
theorem span_eq_iUnion_finCombinations (A : Set E) :
    (Submodule.span ℝ A : Set E) = ⋃ m, finCombinations m univ A := by
  ext x
  rw [SetLike.mem_coe, Submodule.mem_span_set', mem_iUnion]
  constructor
  · rintro ⟨m, f, g, rfl⟩
    exact ⟨m, mem_finCombinations.2 ⟨f, mem_univ _, fun i ↦ g i, fun i ↦ (g i).2, rfl⟩⟩
  · rintro ⟨m, hx⟩
    obtain ⟨w, -, z, hz, rfl⟩ := mem_finCombinations.1 hx
    exact ⟨m, w, fun i ↦ ⟨z i, hz i⟩, rfl⟩

omit [FiniteDimensional ℝ E] in
theorem affineSpan_eq_iUnion_finCombinations (A : Set E) :
    (affineSpan ℝ A : Set E) = ⋃ m, finCombinations m {w | ∑ i, w i = 1} A := by
  ext x
  rw [SetLike.mem_coe, mem_iUnion]
  constructor
  · intro hx
    rw [← Subtype.range_coe (s := A)] at hx
    obtain ⟨s, w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan hx
    rw [Finset.affineCombination_eq_linear_combination s _ w hw1]
    let e := s.equivFin
    refine ⟨s.card, mem_finCombinations.2 ⟨fun i ↦ w (e.symm i), ?_, fun i ↦ (e.symm i : A),
      fun i ↦ (e.symm i : A).2, ?_⟩⟩
    · change ∑ i, w (e.symm i) = 1
      rw [← hw1, ← Finset.sum_coe_sort s]
      exact e.symm.sum_comp (fun j : s ↦ w j)
    · rw [← Finset.sum_coe_sort s]
      exact e.symm.sum_comp (fun j : s ↦ w j • ((j : A) : E))
  · rintro ⟨m, hx⟩
    obtain ⟨w, hw1, z, hz, rfl⟩ := mem_finCombinations.1 hx
    have hmem := affineCombination_mem_affineSpan (s := Finset.univ) (k := ℝ) hw1 z
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at hmem
    exact affineSpan_mono ℝ (range_subset_iff.2 hz) hmem

/-- **Exercise 14.12(a)**: `t ↦ con S(t)` is measurable. -/
theorem SvMeasurable.convexHull {S : T → Set E} (hS : SvMeasurable S) :
    SvMeasurable (fun t ↦ _root_.convexHull ℝ (S t)) := by
  have heq : (fun t ↦ _root_.convexHull ℝ (S t)) = fun t ↦
      ⋃ m, RW.finCombinations m {w : Fin m → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} (S t) :=
    funext fun t ↦ convexHull_eq_iUnion_finCombinations (S t)
  rw [heq]
  exact SvMeasurable.iUnion fun m ↦ hS.finCombinations m _

omit [FiniteDimensional ℝ E] in
/-- **Exercise 14.12(b)**: `t ↦ pos S(t)` (formula 3(11)) is measurable. -/
theorem SvMeasurable.positiveHull {S : T → Set E} (hS : SvMeasurable S) :
    SvMeasurable (fun t ↦ RW.positiveHull (S t)) := by
  intro O hO
  have hU : IsOpen (⋃ a ∈ Ioi (0 : ℝ), (fun y : E ↦ a • y) ⁻¹' O) :=
    isOpen_biUnion fun a _ ↦ hO.preimage (continuous_const_smul a)
  have : svPreimage (fun t ↦ RW.positiveHull (S t)) O =
      {_t | (0 : E) ∈ O} ∪ svPreimage S (⋃ a ∈ Ioi (0 : ℝ), (fun y : E ↦ a • y) ⁻¹' O) := by
    ext t
    constructor
    · rintro ⟨x, hx, hxO⟩
      rcases (mem_positiveHull.1 hx) with rfl | ⟨a, ha, y, hy, rfl⟩
      · exact Or.inl hxO
      · exact Or.inr ⟨y, hy, mem_iUnion₂.2 ⟨a, ha, hxO⟩⟩
    · rintro (h0 | ⟨y, hy, hyU⟩)
      · exact ⟨0, mem_positiveHull.2 (Or.inl rfl), h0⟩
      · obtain ⟨a, ha, hyO⟩ := mem_iUnion₂.1 hyU
        exact ⟨a • y, mem_positiveHull.2 (Or.inr ⟨a, ha, y, hy, rfl⟩), hyO⟩
  rw [this]
  exact (MeasurableSet.const _).union (hS _ hU)

/-- **Exercise 14.12(c)**: `t ↦ aff S(t)` is measurable. -/
theorem SvMeasurable.affineSpan {S : T → Set E} (hS : SvMeasurable S) :
    SvMeasurable (fun t ↦ (_root_.affineSpan ℝ (S t) : Set E)) := by
  have heq : (fun t ↦ (_root_.affineSpan ℝ (S t) : Set E)) = fun t ↦
      ⋃ m, RW.finCombinations m {w : Fin m → ℝ | ∑ i, w i = 1} (S t) :=
    funext fun t ↦ affineSpan_eq_iUnion_finCombinations (S t)
  rw [heq]
  exact SvMeasurable.iUnion fun m ↦ hS.finCombinations m _

/-- **Exercise 14.12(d)**: `t ↦ lin S(t)` is measurable. -/
theorem SvMeasurable.span {S : T → Set E} (hS : SvMeasurable S) :
    SvMeasurable (fun t ↦ (Submodule.span ℝ (S t) : Set E)) := by
  have heq : (fun t ↦ (Submodule.span ℝ (S t) : Set E)) = fun t ↦
      ⋃ m, RW.finCombinations m (univ : Set (Fin m → ℝ)) (S t) :=
    funext fun t ↦ span_eq_iUnion_finCombinations (S t)
  rw [heq]
  exact SvMeasurable.iUnion fun m ↦ hS.finCombinations m _

end Hulls

section Polars

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Closed half-spaces `{v | ⟪v, a⟫ ≤ β}` with `β ≥ 0` (all of `E` when `a = 0`) are solid. -/
theorem halfspace_eq_closure_interior (a : E) {β : ℝ} (hβ : 0 ≤ β) :
    {v : E | ⟪v, a⟫_ℝ ≤ β} = closure (interior {v : E | ⟪v, a⟫_ℝ ≤ β}) := by
  have hconv : Convex ℝ {v : E | ⟪v, a⟫_ℝ ≤ β} := by
    intro x hx y hy c d hc hd hcd
    simp only [mem_setOf_eq, inner_add_left, inner_smul_left, RCLike.conj_to_real] at hx hy ⊢
    nlinarith
  have hclosed : IsClosed {v : E | ⟪v, a⟫_ℝ ≤ β} :=
    isClosed_le (continuous_id.inner continuous_const) continuous_const
  refine eq_closure_interior_of_convex hconv hclosed ?_
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, ?_⟩
    have : {v : E | ⟪v, (0 : E)⟫_ℝ ≤ β} = univ := by
      ext v
      simp [hβ]
    rw [this, interior_univ]
    trivial
  · have hsub : {v : E | ⟪v, a⟫_ℝ < β} ⊆ {v : E | ⟪v, a⟫_ℝ ≤ β} := fun v hv ↦
      le_of_lt (show ⟪v, a⟫_ℝ < β from hv)
    refine ⟨-a, interior_mono hsub ?_⟩
    have hopen : IsOpen {v : E | ⟪v, a⟫_ℝ < β} :=
      isOpen_lt (continuous_id.inner continuous_const) continuous_const
    rw [hopen.interior_eq]
    simp only [mem_setOf_eq, inner_neg_left, real_inner_self_eq_norm_sq]
    have : 0 < ‖a‖ := norm_pos_iff.2 ha
    nlinarith

/-- The half-space mappings `t ↦ {v | ⟪v, x(t)⟫ ≤ β}` on a measurable set `A` (all of `E` off
`A`) are closed-valued and measurable. -/
theorem svMeasurable_halfspace_ite {A : Set T} (hA : MeasurableSet A) {x : T → E}
    (hx : Measurable x) {β : ℝ} (hβ : 0 ≤ β) :
    SvMeasurable (fun t ↦ if t ∈ A then {v : E | ⟪v, x t⟫_ℝ ≤ β} else univ) := by
  refine (svMeasurable_iff_of_solidValued fun t ↦ ?_).2 fun v ↦ ?_
  · by_cases ht : t ∈ A
    · simp only [ht, if_true]
      exact halfspace_eq_closure_interior (x t) hβ
    · simp only [ht, if_false, interior_univ, closure_univ]
  · have : {t | v ∈ if t ∈ A then {v : E | ⟪v, x t⟫_ℝ ≤ β} else univ} =
        (A ∩ {t | ⟪v, x t⟫_ℝ ≤ β}) ∪ Aᶜ := by
      ext t
      by_cases ht : t ∈ A <;> simp [ht]
    rw [this]
    exact (hA.inter (measurableSet_le (measurable_const.inner hx) measurable_const)).union
      hA.compl

omit [MeasurableSpace T] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem isClosed_halfspace_ite (A : Set T) (x : T → E) (β : ℝ) (t : T) :
    IsClosed (if t ∈ A then {v : E | ⟪v, x t⟫_ℝ ≤ β} else univ) := by
  split_ifs
  · exact isClosed_le (continuous_id.inner continuous_const) continuous_const
  · exact isClosed_univ

/-- Polars of measurable mappings, in the general form `{v | ⟪v, x⟫ ≤ β ∀ x ∈ S(t)}`
for `β ≥ 0`, following the guide of Exercise 14.12. -/
theorem SvMeasurable.svMeasurable_polar_le {S : T → Set E} (hS : SvMeasurable S) {β : ℝ}
    (hβ : 0 ≤ β) : SvMeasurable (fun t ↦ {v : E | ∀ x ∈ S t, ⟪v, x⟫_ℝ ≤ β}) := by
  have hS' : SvMeasurable (fun t ↦ _root_.closure (S t)) := hS.closure
  rcases isEmpty_or_nonempty E with hE | hE
  · intro O _
    have : svPreimage (fun t ↦ {v : E | ∀ x ∈ S t, ⟪v, x⟫_ℝ ≤ β}) O = ∅ := by
      ext t
      simp only [mem_svPreimage, mem_empty_iff_false, iff_false]
      rintro ⟨s, -⟩
      exact hE.elim s
    rw [this]
    exact MeasurableSet.empty
  obtain ⟨x, hx⟩ := hS'.exists_castaingRepresentation fun _ ↦ isClosed_closure
  have hdom : MeasurableSet (svDom fun t ↦ _root_.closure (S t)) := hS'.measurableSet_svDom
  set H : ℕ → T → Set E := fun n t ↦
    if t ∈ svDom (fun t ↦ _root_.closure (S t)) then {v : E | ⟪v, x n t⟫_ℝ ≤ β} else univ
  have hH : ∀ n, SvMeasurable (H n) := fun n ↦ svMeasurable_halfspace_ite hdom (hx.1 n) hβ
  have hHc : ∀ n t, IsClosed (H n t) := fun n t ↦ isClosed_halfspace_ite _ _ _ t
  have heq : (fun t ↦ {v : E | ∀ x ∈ S t, ⟪v, x⟫_ℝ ≤ β}) = fun t ↦ ⋂ n, H n t := by
    funext t
    ext v
    simp only [mem_setOf_eq, mem_iInter, H]
    by_cases ht : t ∈ svDom (fun t ↦ _root_.closure (S t))
    · simp only [ht, if_true, mem_setOf_eq]
      have hcl : _root_.closure (S t) = _root_.closure (range fun n ↦ x n t) := hx.2 t ht
      constructor
      · intro hv n
        have hmem : x n t ∈ _root_.closure (S t) := by rw [hcl]; exact subset_closure ⟨n, rfl⟩
        have hcont : Continuous fun y : E ↦ ⟪v, y⟫_ℝ := continuous_const.inner continuous_id
        exact closure_minimal (s := S t) (t := {y | ⟪v, y⟫_ℝ ≤ β}) (fun y hy ↦ hv y hy)
          (isClosed_le hcont continuous_const) hmem
      · intro hv y hy
        have hy' : y ∈ _root_.closure (range fun n ↦ x n t) := hcl ▸ subset_closure hy
        have hcont : Continuous fun y : E ↦ ⟪v, y⟫_ℝ := continuous_const.inner continuous_id
        exact closure_minimal (s := range fun n ↦ x n t) (t := {y | ⟪v, y⟫_ℝ ≤ β})
          (by rintro _ ⟨n, rfl⟩; exact hv n) (isClosed_le hcont continuous_const) hy'
    · simp only [ht, if_false, mem_univ, implies_true, iff_true]
      intro y hy
      exact absurd ⟨y, subset_closure hy⟩ ht
  rw [heq]
  exact SvMeasurable.iInter hH hHc

/-- **Exercise 14.12(e)**: `t ↦ S(t)°` is measurable. -/
theorem SvMeasurable.polarSet {S : T → Set E} (hS : SvMeasurable S) :
    SvMeasurable (fun t ↦ RW.polarSet (S t)) :=
  hS.svMeasurable_polar_le zero_le_one

/-- **Exercise 14.12(f)**: `t ↦ S(t)*` is measurable. -/
theorem SvMeasurable.polarCone {S : T → Set E} (hS : SvMeasurable S) :
    SvMeasurable (fun t ↦ RW.polarCone (S t)) :=
  hS.svMeasurable_polar_le le_rfl

/-- **Exercise 14.12 (hulls and polars)**, all six parts. -/
theorem hulls_and_polars {S : T → Set E} (hS : SvMeasurable S) :
    SvMeasurable (fun t ↦ _root_.convexHull ℝ (S t)) ∧
      SvMeasurable (fun t ↦ RW.positiveHull (S t)) ∧
      SvMeasurable (fun t ↦ (_root_.affineSpan ℝ (S t) : Set E)) ∧
      SvMeasurable (fun t ↦ (Submodule.span ℝ (S t) : Set E)) ∧
      SvMeasurable (fun t ↦ RW.polarSet (S t)) ∧
      SvMeasurable (fun t ↦ RW.polarCone (S t)) :=
  ⟨hS.convexHull, hS.positiveHull, hS.affineSpan, hS.span, hS.polarSet, hS.polarCone⟩

end Polars

end RW
