/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Normal integrands

Definition 14.27, Proposition 14.28, Examples 14.29–14.32, Proposition 14.33 and the forward
half of Corollary 14.34 of Rockafellar–Wets.

An integrand `f : T × ℝⁿ → ℝ̄` is a curried function `f : T → E → EReal`, with `E` a
finite-dimensional real normed space.  Its epigraphical mapping 14(8) is
`t ↦ epigraph (f t) ⊂ E × ℝ` and its domain mapping is `t ↦ effectiveDomain (f t)`.
-/

import RockafellarWets.Chapter14.GraphMeasurability
import RockafellarWets.Chapter14.MeasurableLimits
import RockafellarWets.Chapter1.Semicontinuity
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.Real.Cardinality

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace RW

section ERealMeasurability

variable {T : Type*} [MeasurableSpace T]

theorem ereal_eq_bot_of_forall_le_neg_nat {x : EReal} (h : ∀ n : ℕ, x ≤ ((-(n : ℝ) : ℝ) : EReal)) :
    x = ⊥ := by
  induction x with
  | bot => rfl
  | coe r =>
    obtain ⟨n, hn⟩ := exists_nat_gt (-r)
    have := h n
    rw [EReal.coe_le_coe_iff] at this
    linarith
  | top =>
    have := h 0
    simp at this

/-- An extended-real function is measurable as soon as its real sublevel sets are measurable. -/
theorem measurable_ereal_of_le_coe {g : T → EReal}
    (h : ∀ α : ℝ, MeasurableSet {t | g t ≤ α}) : Measurable g := by
  refine measurable_of_Iic fun a ↦ ?_
  induction a with
  | bot =>
    have : g ⁻¹' Iic ⊥ = ⋂ n : ℕ, {t | g t ≤ ((-(n : ℝ) : ℝ) : EReal)} := by
      ext t
      simp only [mem_preimage, mem_Iic, mem_iInter, mem_setOf_eq]
      constructor
      · intro ht n
        exact ht.trans bot_le
      · intro ht
        rw [ereal_eq_bot_of_forall_le_neg_nat ht]
    rw [this]
    exact MeasurableSet.iInter fun n ↦ h _
  | coe a => exact h a
  | top =>
    have : g ⁻¹' Iic ⊤ = univ := by ext t; simp
    rw [this]
    exact MeasurableSet.univ

/-- An extended-real function is measurable as soon as its real strict sublevel sets are
measurable. -/
theorem measurable_ereal_of_lt_coe {g : T → EReal}
    (h : ∀ β : ℝ, MeasurableSet {t | g t < β}) : Measurable g := by
  refine measurable_of_Iio fun a ↦ ?_
  induction a with
  | bot =>
    have : g ⁻¹' Iio ⊥ = ∅ := by ext t; simp
    rw [this]
    exact MeasurableSet.empty
  | coe a => exact h a
  | top =>
    have : g ⁻¹' Iio ⊤ = ⋃ n : ℕ, {t | g t < ((n : ℝ) : EReal)} := by
      ext t
      simp only [mem_preimage, mem_Iio, mem_iUnion, mem_setOf_eq]
      constructor
      · intro ht
        induction h' : g t with
        | bot => exact ⟨0, by simp⟩
        | coe r =>
          obtain ⟨n, hn⟩ := exists_nat_gt r
          exact ⟨n, by exact_mod_cast hn⟩
        | top => rw [h'] at ht; exact absurd ht (lt_irrefl _)
      · rintro ⟨n, hn⟩
        exact hn.trans (EReal.coe_lt_top _)
    rw [this]
    exact MeasurableSet.iUnion fun n ↦ h _

end ERealMeasurability

section Definition1427

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E]

/-- The **epigraphical mapping** `S_f(t) = epi f(t, ·)` of formula 14(8). -/
def epiMapping (f : T → E → EReal) : T → Set (E × ℝ) := fun t ↦ epigraph (f t)

/-- The **domain mapping** `D_f(t) = dom f(t, ·)` of formula 14(8). -/
def domMapping (f : T → E → EReal) : T → Set E := fun t ↦ effectiveDomain (f t)

/-- **Definition 14.27 (normal integrands).**  `f` is a normal integrand if its epigraphical
mapping is closed-valued and measurable. -/
def IsNormalIntegrand (f : T → E → EReal) : Prop :=
  (∀ t, IsClosed (epigraph (f t))) ∧ SvMeasurable (epiMapping f)

end Definition1427

section Proposition1428

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem svPreimage_domMapping [TopologicalSpace E] (f : T → E → EReal) (O : Set E) :
    svPreimage (domMapping f) O = svPreimage (epiMapping f) (O ×ˢ univ) := by
  ext t
  simp only [mem_svPreimage]
  constructor
  · rintro ⟨x, hx, hxO⟩
    have hlt : f t x < ⊤ := hx
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f t x < r := by
      induction h : f t x with
      | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
      | coe r => exact ⟨r + 1, by exact_mod_cast (lt_add_one r)⟩
      | top => rw [h] at hlt; exact absurd hlt (lt_irrefl _)
    exact ⟨(x, r), (show (r : EReal) ≥ f t x from hr.le), hxO, mem_univ _⟩
  · rintro ⟨⟨x, r⟩, hxr, hxO, -⟩
    have : f t x ≤ r := hxr
    exact ⟨x, lt_of_le_of_lt this (EReal.coe_lt_top r), hxO⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Proposition 14.28**: the domain mapping of a normal integrand is measurable. -/
theorem IsNormalIntegrand.svMeasurable_domMapping {f : T → E → EReal}
    (hf : IsNormalIntegrand f) : SvMeasurable (domMapping f) := fun O hO ↦ by
  rw [svPreimage_domMapping]
  exact hf.2 _ (hO.prod isOpen_univ)

omit [MeasurableSpace T] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- **Proposition 14.28**: `f(t, x)` is lsc in `x`. -/
theorem IsNormalIntegrand.lowerSemicontinuous [MeasurableSpace T] {f : T → E → EReal}
    (hf : IsNormalIntegrand f) (t : T) : LowerSemicontinuous (f t) :=
  (lsc_iff_epigraph_closed_ereal _).2 (hf.1 t)

/-- **Proposition 14.28**: `t ↦ f(t, x(t))` is measurable whenever `x` is measurable. -/
theorem IsNormalIntegrand.measurable_comp {f : T → E → EReal} (hf : IsNormalIntegrand f)
    {x : T → E} (hx : Measurable x) : Measurable fun t ↦ f t (x t) := by
  refine measurable_ereal_of_le_coe fun α ↦ ?_
  have hy : Measurable fun t ↦ ((x t, α) : E × ℝ) := hx.prodMk measurable_const
  have hR := hf.2.inter (svMeasurable_singleton_iff.2 hy) hf.1 (fun _ ↦ isClosed_singleton)
  have : {t | f t (x t) ≤ α} = svDom (fun t ↦ epiMapping f t ∩ {(x t, α)}) := by
    ext t
    simp only [mem_setOf_eq, mem_svDom]
    constructor
    · intro h
      exact ⟨(x t, α), (show ((α : ℝ) : EReal) ≥ f t (x t) from h), rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp
  rw [this]
  exact hR.measurableSet_svDom

/-- **Proposition 14.28**: `f(t, x)` is measurable in `t` for each fixed `x`. -/
theorem IsNormalIntegrand.measurable_apply {f : T → E → EReal} (hf : IsNormalIntegrand f)
    (x : E) : Measurable fun t ↦ f t x :=
  hf.measurable_comp measurable_const

/-- **Proposition 14.28 (basic consequences of normality)**, first part. -/
theorem basic_consequences_of_normality {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    SvMeasurable (domMapping f) ∧ (∀ t, LowerSemicontinuous (f t)) ∧
      (∀ x, Measurable fun t ↦ f t x) ∧
      ∀ {x : T → E}, Measurable x → Measurable fun t ↦ f t (x t) :=
  ⟨hf.svMeasurable_domMapping, hf.lowerSemicontinuous, hf.measurable_apply,
    fun hx ↦ hf.measurable_comp hx⟩

/-- There is a subset of `ℝ` that is not Borel (cardinality: the Borel field is countably
generated, hence has at most continuum many members). -/
theorem exists_not_measurableSet_real : ∃ D : Set ℝ, ¬ MeasurableSet D := by
  by_contra h
  push_neg at h
  set s : Set (Set ℝ) := ⋃ a : ℚ, {Iio (a : ℝ)}
  have hs : Cardinal.mk s ≤ Cardinal.continuum := by
    have hc : s.Countable := countable_iUnion fun a ↦ countable_singleton _
    exact (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype).trans Cardinal.aleph0_le_continuum
  have hle := MeasurableSpace.cardinal_measurableSet_le_continuum hs
  have hall : {t : Set ℝ | @MeasurableSet ℝ (MeasurableSpace.generateFrom s) t} = univ := by
    ext D
    simp only [mem_setOf_eq, mem_univ, iff_true]
    have hD := h D
    rw [← Real.borel_eq_generateFrom_Iio_rat]
    rw [← BorelSpace.measurable_eq (α := ℝ)]
    exact hD
  rw [hall, Cardinal.mk_univ, Cardinal.mk_set, Cardinal.mk_real] at hle
  exact absurd hle (not_le.2 (Cardinal.cantor _))

/-- **Proposition 14.28**, second part: an integrand that is lsc in `x` and measurable in `t`
need not be normal, and need not make `t ↦ f(t, x(t))` measurable (here `T = ℝ` with its
Borel field, `x(t) = t`, `f(t, x) = 0` if `t = x ∈ D`, `∞` otherwise, `D` non-Borel).  Each
`f(t, ·)` is also convex (`exists_lsc_convex_measurable_not_normal`, for 14.39). -/
theorem exists_lsc_measurable_not_normal :
    ∃ f : ℝ → ℝ → EReal, (∀ t, LowerSemicontinuous (f t)) ∧ (∀ x, Measurable fun t ↦ f t x) ∧
      ¬ IsNormalIntegrand f ∧ ¬ Measurable fun t ↦ f t t := by
  classical
  obtain ⟨D, hD⟩ := exists_not_measurableSet_real
  set f : ℝ → ℝ → EReal := fun t x ↦ if t = x ∧ x ∈ D then 0 else ⊤ with hfdef
  have hnot : ¬ Measurable fun t ↦ f t t := by
    intro hm
    have : (fun t ↦ f t t) ⁻¹' {0} = D := by
      ext t
      simp [hfdef]
    exact hD (this ▸ hm (measurableSet_singleton 0))
  refine ⟨f, fun t ↦ ?_, fun x ↦ ?_, fun hf ↦ hnot (hf.measurable_comp measurable_id), hnot⟩
  · have : f t = indicatorVA {x | t = x ∧ x ∈ D} := by
      funext x
      simp only [hfdef, indicatorVA, mem_setOf_eq]
      split_ifs <;> rfl
    rw [this]
    refine lowerSemicontinuous_indicatorVA ?_
    by_cases ht : t ∈ D
    · have : {x | t = x ∧ x ∈ D} = {t} := by
        ext x
        simp only [mem_setOf_eq, mem_singleton_iff]
        constructor
        · rintro ⟨rfl, -⟩
          rfl
        · rintro rfl
          exact ⟨rfl, ht⟩
      rw [this]
      exact isClosed_singleton
    · have : {x | t = x ∧ x ∈ D} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        rintro rfl
        exact ht
      rw [this]
      exact isClosed_empty
  · exact Measurable.ite ((measurableSet_singleton x).inter (MeasurableSet.const _))
      measurable_const measurable_const

end Proposition1428

end RW
