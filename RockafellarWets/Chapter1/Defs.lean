/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1: Max and Min — Core Definitions

This file formalizes the foundational definitions from Chapter 1 of
Rockafellar & Wets, "Variational Analysis":
- Extended-real-valued functions (Section A)
- Effective domain, proper/improper functions
- Indicator functions of sets
- Epigraphs (Section B)
- Level sets
- Level boundedness (Definition 1.8)

We work over `EReal` (= ℝ̄ = [-∞, ∞]) and connect to existing Mathlib
definitions where possible.
-/

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Basic

open Set Filter Topology EReal Classical

noncomputable section

namespace RW

variable {E : Type*}

/-- The **effective domain** of an extended-real-valued function `f` is the set
of points where `f` is finite (i.e., `f(x) < ∞`). This corresponds to `dom f`
in Rockafellar & Wets. -/
def effectiveDomain (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- A function `f : E → ℝ̄` is **proper** if its effective domain is nonempty
and `f` never takes the value `-∞`. That is, `dom f ≠ ∅` and `f(x) > -∞`
for all `x`. This is the central class of functions in variational analysis. -/
def IsProper (f : E → EReal) : Prop :=
  (∃ x, f x < ⊤) ∧ (∀ x, f x > ⊥)

/-- The **indicator function** `δ_C` of a set `C`, in the sense of variational
analysis (not probability). Takes value `0` on `C` and `∞` outside `C`.

Note: This is NOT the usual indicator/characteristic function from measure
theory (which takes values 0 and 1). -/
def indicatorVA (C : Set E) : E → EReal :=
  fun x => if x ∈ C then 0 else ⊤

/-- The **epigraph** of a function `f : E → ℝ̄` is the set of points `(x, α)`
lying on or above the graph of `f`:
  `epi f = {(x, α) ∈ E × ℝ | α ≥ f(x)}` -/
def epigraph (f : E → EReal) : Set (E × ℝ) :=
  {p | (p.2 : EReal) ≥ f p.1}

/-- The **hypograph** of `f`:
  `hypo f = {(x, α) ∈ E × ℝ | α ≤ f(x)}` -/
def hypograph (f : E → EReal) : Set (E × ℝ) :=
  {p | (p.2 : EReal) ≤ f p.1}

/-- Lower level set: `lev≤α f = {x | f(x) ≤ α}` -/
def levelSet (f : E → EReal) (α : EReal) : Set E :=
  {x | f x ≤ α}

/-- Strict lower level set: `lev<α f = {x | f(x) < α}` -/
def strictLevelSet (f : E → EReal) (α : EReal) : Set E :=
  {x | f x < α}

/-- Upper level set: `lev≥α f = {x | f(x) ≥ α}` -/
def upperLevelSet (f : E → EReal) (α : EReal) : Set E :=
  {x | f x ≥ α}

/-- **Level boundedness** (Definition 1.8): A function `f : E → ℝ̄` is
level-bounded if for every `α ∈ ℝ` the sublevel set `{x | f(x) ≤ α}` is
bounded. This corresponds to `f(x) → ∞` as `‖x‖ → ∞`. -/
def IsLevelBounded [PseudoMetricSpace E] (f : E → EReal) : Prop :=
  ∀ α : ℝ, Bornology.IsBounded (levelSet f α)

/-- **Inf-compactness**: the sublevel sets `{x | f(x) ≤ α}` are all compact
for finite `α`. This is the crucial ingredient in Theorem 1.9. -/
def IsInfCompact [TopologicalSpace E] (f : E → EReal) : Prop :=
  ∀ α : ℝ, IsCompact (levelSet f α)

/-- **Prox-boundedness** (Definition 1.23): `f` is prox-bounded if there
exists `r ∈ ℝ` such that `f(x) ≥ -(r/2)‖x‖²` for all `x`.
Equivalently, `f` majorizes a quadratic function. -/
def IsProxBounded [SeminormedAddCommGroup E] (f : E → EReal) : Prop :=
  ∃ r : ℝ, ∀ x : E, f x ≥ (-(r / 2) * ‖x‖ ^ 2 : ℝ)

/-- The **threshold of prox-boundedness** `λ_f`. -/
def proxThreshold [SeminormedAddCommGroup E] (f : E → EReal) : EReal :=
  ⨆ (lam : ℝ) (_ : lam > 0 ∧ ∃ x : E,
    (⨅ w : E, f w + ((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ)) > ⊥), (lam : EReal)

/-! ## Basic properties of effective domain and properness -/

theorem effectiveDomain_eq (f : E → EReal) :
    effectiveDomain f = {x | f x ≠ ⊤} := by
  ext x; simp [effectiveDomain, lt_top_iff_ne_top]

theorem mem_effectiveDomain_iff (f : E → EReal) (x : E) :
    x ∈ effectiveDomain f ↔ f x < ⊤ :=
  Iff.rfl

theorem isProper_iff (f : E → EReal) :
    IsProper f ↔ (effectiveDomain f).Nonempty ∧ ∀ x, f x > ⊥ := by
  simp [IsProper, effectiveDomain, Set.Nonempty]

/-! ## Properties of indicator functions -/

@[simp]
theorem indicatorVA_apply_mem {C : Set E} {x : E} (hx : x ∈ C) :
    indicatorVA C x = 0 :=
  if_pos hx

@[simp]
theorem indicatorVA_apply_not_mem {C : Set E} {x : E} (hx : x ∉ C) :
    indicatorVA C x = ⊤ :=
  if_neg hx

theorem effectiveDomain_indicatorVA (C : Set E) :
    effectiveDomain (indicatorVA C) = C := by
  ext x
  simp only [effectiveDomain, indicatorVA, mem_setOf_eq]
  constructor
  · intro h
    by_contra hx
    simp [hx] at h
  · intro hx
    simp [hx]

theorem indicatorVA_isProper_iff (C : Set E) :
    IsProper (indicatorVA C) ↔ C.Nonempty := by
  constructor
  · intro ⟨⟨x, hx⟩, _⟩
    exact ⟨x, (effectiveDomain_indicatorVA C) ▸ hx⟩
  · intro ⟨x, hx⟩
    exact ⟨⟨x, by simp [indicatorVA, hx]⟩,
           fun y => by simp only [indicatorVA]; split <;> simp⟩

theorem indicatorVA_inter (C D : Set E) :
    indicatorVA (C ∩ D) = fun x => indicatorVA C x + indicatorVA D x := by
  funext x
  by_cases hC : x ∈ C <;> by_cases hD : x ∈ D <;> simp [indicatorVA, hC, hD]

/-! ## Epigraph properties -/

theorem mem_epigraph_iff (f : E → EReal) (x : E) (α : ℝ) :
    (x, α) ∈ epigraph f ↔ f x ≤ (α : EReal) := by
  simp [epigraph, ge_iff_le]

/-- The projection of `epi f` onto `E` is the effective domain of `f`. -/
theorem epigraph_proj_eq_effectiveDomain (f : E → EReal) :
    Prod.fst '' (epigraph f) = effectiveDomain f := by
  ext x
  simp only [mem_image, Prod.exists, epigraph, mem_setOf_eq, effectiveDomain, ge_iff_le]
  constructor
  · rintro ⟨_, α, hα, rfl⟩
    exact lt_of_le_of_lt hα (EReal.coe_lt_top α)
  · intro hx
    by_cases hbot : f x = ⊥
    · exact ⟨x, 0, by simp [hbot]⟩
    · have hne_top := ne_of_lt hx
      have := EReal.coe_toReal hne_top hbot
      exact ⟨x, (f x).toReal, this ▸ le_refl _, rfl⟩

/-! ## Level set basics -/

theorem levelSet_top (f : E → EReal) : levelSet f ⊤ = univ := by
  ext x; simp [levelSet, le_top]

theorem levelSet_monotone (f : E → EReal) :
    Monotone (levelSet f) := by
  intro a b hab x (hx : f x ≤ a)
  exact le_trans hx hab

/-- `argmin f` is the set of global minimizers, with the convention from
Rockafellar--Wets that an identically-`+∞` problem has no minimizer.  Values
equal to `-∞` are retained as genuine minimizers. -/
def argmin (f : E → EReal) : Set E :=
  {x | f x = ⨅ y, f y ∧ (⨅ y, f y) < ⊤}

@[simp]
theorem mem_argmin_iff (f : E → EReal) (x : E) :
    x ∈ argmin f ↔ f x = ⨅ y, f y ∧ (⨅ y, f y) < ⊤ :=
  Iff.rfl

/-- For a problem whose infimum is below `+∞`, the book's `argmin` agrees
with the usual equality-based minimizer set. -/
theorem argmin_eq_setOf_eq_iInf {f : E → EReal}
    (hfin : (⨅ y, f y) < ⊤) :
    argmin f = {x | f x = ⨅ y, f y} := by
  ext x
  simp [argmin, hfin]

theorem iInf_lt_top_of_isProper {f : E → EReal} (hproper : IsProper f) :
    (⨅ y, f y) < ⊤ := by
  rcases hproper.1 with ⟨x, hx⟩
  exact lt_of_le_of_lt (iInf_le f x) hx

/-- Proper functions automatically satisfy the nondegeneracy condition in
`argmin_eq_setOf_eq_iInf`. -/
theorem argmin_eq_setOf_eq_iInf_of_isProper {f : E → EReal}
    (hproper : IsProper f) :
    argmin f = {x | f x = ⨅ y, f y} := by
  exact argmin_eq_setOf_eq_iInf (iInf_lt_top_of_isProper hproper)

theorem mem_argmin_iff_eq_iInf_of_isProper {f : E → EReal}
    (hproper : IsProper f) (x : E) :
    x ∈ argmin f ↔ f x = ⨅ y, f y := by
  rw [argmin_eq_setOf_eq_iInf_of_isProper hproper]
  rfl

@[simp]
theorem argmin_const_top :
    argmin (fun _ : E ↦ (⊤ : EReal)) = ∅ := by
  ext x
  simp [argmin]

@[simp]
theorem argmin_const_bot :
    argmin (fun _ : E ↦ (⊥ : EReal)) = Set.univ := by
  ext x
  letI : Nonempty E := ⟨x⟩
  simp [argmin]

end RW
