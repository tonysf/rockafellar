/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2A: Extended-real-valued convex functions

This file formalizes Section A of Chapter 2 of Rockafellar–Wets with the
book's extended arithmetic.  Inequality 2(3) is read with inf-addition
(`∞ - ∞ = ∞`, `RW.infAddition`), so a convex function may take both infinite
values, and Jensen's inequality 2(5) uses the finite inf-addition
`RW.finiteInfAddition` of Chapter 7.

* Definition 2.1: `IsConvexRelative`, `IsStrictlyConvexRelative`, and the
  equivalent forms 2(4), with the closed parameter interval, and by extension
  with the value `∞` outside `C`.
* Theorem 2.2: convex combinations and Jensen's inequality.
* Exercise 2.3: effective domains, proper convex functions, and indicators.
* Proposition 2.4: convexity of epigraphs and strict epigraphs.
* Exercise 2.5: improper convex functions.
* Theorem 2.6: local and global optimality, convexity and uniqueness of
  minimizers.

The repository-wide convention `Convex ℝ (epigraph f)` for the convexity of
`f : E → EReal` is exactly Proposition 2.4 (`isConvexRelative_univ_iff`).
-/

import RockafellarWets.Chapter1.Semicontinuity
import RockafellarWets.Chapter7.FiniteEpiSums
import Mathlib.Analysis.Convex.Combination

open Set Filter Topology

noncomputable section

namespace RW

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## Definition 2.1 -/

/-- **Definition 2.1(a)**: `C` is convex exactly when it contains
`(1 - τ)x₀ + τx₁` for all `x₀, x₁ ∈ C` and `τ ∈ (0,1)`, condition 2(2). -/
theorem convex_iff_forall_mem_Ioo (C : Set E) :
    Convex ℝ C ↔ ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → ∀ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
      (1 - τ) • x₀ + τ • x₁ ∈ C := by
  constructor
  · exact fun hC x₀ hx₀ x₁ hx₁ τ hτ0 hτ1 ↦ hC hx₀ hx₁ (by linarith) hτ0.le (by ring)
  · intro h x₀ hx₀ x₁ hx₁ a b ha hb hab
    rcases hb.eq_or_lt with rfl | hb'
    · obtain rfl : a = 1 := by linarith
      simpa using hx₀
    rcases ha.eq_or_lt with rfl | ha'
    · obtain rfl : b = 1 := by linarith
      simpa using hx₁
    obtain rfl : a = 1 - b := by linarith
    exact h hx₀ hx₁ hb' (by linarith)

/-- **Definition 2.1(b)**: `f` is convex relative to `C` when the convexity
inequality 2(3) holds for all `x₀, x₁ ∈ C` and `τ ∈ (0,1)`, the right side
being formed with the book's inf-addition `∞ - ∞ = ∞`.  The set `C` is assumed
convex in the theorems below, as in the book. -/
def IsConvexRelative (C : Set E) (f : E → EReal) : Prop :=
  ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → ∀ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
    f ((1 - τ) • x₀ + τ • x₁) ≤
      infAddition (((1 - τ : ℝ) : EReal) * f x₀) ((τ : EReal) * f x₁)

/-- **Definition 2.1(b)**, strict version: the inequality 2(3) is strict for
distinct points with finite function values. -/
def IsStrictlyConvexRelative (C : Set E) (f : E → EReal) : Prop :=
  IsConvexRelative C f ∧
    ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → x₀ ≠ x₁ → f x₀ ≠ ⊤ → f x₀ ≠ ⊥ →
      f x₁ ≠ ⊤ → f x₁ ≠ ⊥ → ∀ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
        f ((1 - τ) • x₀ + τ • x₁) <
          infAddition (((1 - τ : ℝ) : EReal) * f x₀) ((τ : EReal) * f x₁)

/-- A function is concave relative to `C` when its negative is convex. -/
def IsConcaveRelative (C : Set E) (f : E → EReal) : Prop :=
  IsConvexRelative C (fun x ↦ -f x)

/-- The epigraph of `f` relative to `C`, the set `{(x, α) | x ∈ C, f x ≤ α}`. -/
def relativeEpigraph (C : Set E) (f : E → EReal) : Set (E × ℝ) :=
  {p | p.1 ∈ C ∧ f p.1 ≤ (p.2 : EReal)}

/-- The strict epigraph `{(x, α) | f x < α < ∞}` of Proposition 2.4. -/
def strictEpigraph (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 < (p.2 : EReal)}

omit [AddCommGroup E] [Module ℝ E] in
@[simp] theorem mem_relativeEpigraph {C : Set E} {f : E → EReal} {p : E × ℝ} :
    p ∈ relativeEpigraph C f ↔ p.1 ∈ C ∧ f p.1 ≤ (p.2 : EReal) :=
  Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
@[simp] theorem mem_strictEpigraph {f : E → EReal} {p : E × ℝ} :
    p ∈ strictEpigraph f ↔ f p.1 < (p.2 : EReal) :=
  Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
theorem relativeEpigraph_univ (f : E → EReal) :
    relativeEpigraph univ f = epigraph f := by
  ext p
  simp [relativeEpigraph, epigraph]

/-! ### Extended-real arithmetic helpers -/

/-- Dividing an upper bound by a positive real coefficient. -/
theorem ereal_le_coe_div_of_coe_mul_le {t : ℝ} (ht : 0 < t) {u : EReal} {r : ℝ}
    (h : (t : EReal) * u ≤ (r : EReal)) : u ≤ ((r / t : ℝ) : EReal) := by
  induction u using EReal.rec with
  | bot => exact bot_le
  | top =>
    rw [EReal.coe_mul_top_of_pos ht] at h
    exact absurd h (by simp)
  | coe y =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff, le_div_iff₀ ht]
    linarith

/-- A positive coefficient preserves strict inequalities with a real bound. -/
theorem ereal_coe_mul_lt_coe_mul {t : ℝ} (ht : 0 < t) {u : EReal} {r : ℝ}
    (h : u < (r : EReal)) : (t : EReal) * u < ((t * r : ℝ) : EReal) := by
  induction u using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ht]; exact EReal.bot_lt_coe _
  | top => exact absurd h (by simp)
  | coe y =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff]
    exact mul_lt_mul_of_pos_left (EReal.coe_lt_coe_iff.mp h) ht

theorem ereal_coe_mul_lt_top {t : ℝ} (ht : 0 ≤ t) {u : EReal} (hu : u < ⊤) :
    (t : EReal) * u < ⊤ := by
  induction u using EReal.rec with
  | bot =>
    rcases ht.eq_or_lt with rfl | h
    · simp
    · rw [EReal.coe_mul_bot_of_pos h]; exact bot_lt_top
  | top => exact absurd hu (lt_irrefl _)
  | coe y => rw [← EReal.coe_mul]; exact EReal.coe_lt_top _

/-- The right side of 2(3) when both values are below `∞`. -/
theorem infAddition_convexCombination_of_lt_top {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {a b : EReal} (ha : a < ⊤) (hb : b < ⊤) :
    infAddition (((1 - τ : ℝ) : EReal) * a) ((τ : EReal) * b) =
      ((1 - τ : ℝ) : EReal) * a + (τ : EReal) * b := by
  rw [infAddition, if_neg]
  rintro (h | h)
  · exact (ereal_coe_mul_lt_top (by linarith) ha).ne h
  · exact (ereal_coe_mul_lt_top hτ0 hb).ne h

/-- With a positive coefficient, a value `∞` makes the right side of 2(3)
equal to `∞`. -/
theorem infAddition_convexCombination_left_top {τ : ℝ} (hτ : τ < 1) (b : EReal) :
    infAddition (((1 - τ : ℝ) : EReal) * ⊤) ((τ : EReal) * b) = ⊤ := by
  rw [EReal.coe_mul_top_of_pos (by linarith), infAddition, if_pos (Or.inl rfl)]

theorem infAddition_convexCombination_right_top {τ : ℝ} (hτ : 0 < τ) (a : EReal) :
    infAddition (((1 - τ : ℝ) : EReal) * a) ((τ : EReal) * ⊤) = ⊤ := by
  rw [EReal.coe_mul_top_of_pos hτ, infAddition, if_pos (Or.inr rfl)]

/-! ### The basic epigraphical characterization -/

/-- Convexity relative to a convex set `C` is convexity of the epigraph
relative to `C`. -/
theorem isConvexRelative_iff_convex_relativeEpigraph {C : Set E} (hC : Convex ℝ C)
    (f : E → EReal) :
    IsConvexRelative C f ↔ Convex ℝ (relativeEpigraph C f) := by
  constructor
  · rintro hf ⟨x₀, α₀⟩ ⟨hx₀, h₀⟩ ⟨x₁, α₁⟩ ⟨hx₁, h₁⟩ a b ha hb hab
    simp only at hx₀ h₀ hx₁ h₁
    refine ⟨hC hx₀ hx₁ ha hb hab, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rcases hb.eq_or_lt with rfl | hb'
    · obtain rfl : a = 1 := by linarith
      simpa using h₀
    rcases ha.eq_or_lt with rfl | ha'
    · obtain rfl : b = 1 := by linarith
      simpa using h₁
    have ha1 : a = 1 - b := by linarith
    subst ha1
    refine (hf hx₀ hx₁ hb' (by linarith)).trans ?_
    rw [EReal.coe_add]
    refine (infAddition_le_coe_iff _ _ _).mpr ⟨(1 - b) * α₀, b * α₁, ?_, ?_, rfl⟩
    · rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left h₀ (EReal.coe_nonneg.mpr ha)
    · rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left h₁ (EReal.coe_nonneg.mpr hb)
  · intro hE x₀ hx₀ x₁ hx₁ τ hτ0 hτ1
    refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ ?_
    obtain ⟨r, s, hr, hs, hrs⟩ := (infAddition_le_coe_iff _ _ _).mp hz.le
    have h1τ : 0 < 1 - τ := by linarith
    have hm := hE (x := (x₀, r / (1 - τ))) (y := (x₁, s / τ))
      ⟨hx₀, ereal_le_coe_div_of_coe_mul_le h1τ hr⟩
      ⟨hx₁, ereal_le_coe_div_of_coe_mul_le hτ0 hs⟩ h1τ.le hτ0.le (by ring)
    simp only [mem_relativeEpigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hm
    rw [← hrs]
    have hval : (1 - τ) * (r / (1 - τ)) + τ * (s / τ) = r + s := by
      field_simp
    simpa [hval] using hm.2

/-- Convexity relative to `C` in the form 2(4), with strict real upper bounds. -/
theorem isConvexRelative_iff_lt {C : Set E} (hC : Convex ℝ C) (f : E → EReal) :
    IsConvexRelative C f ↔
      ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → ∀ ⦃α₀ α₁ : ℝ⦄,
        f x₀ < (α₀ : EReal) → f x₁ < (α₁ : EReal) → ∀ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
          f ((1 - τ) • x₀ + τ • x₁) ≤ (((1 - τ) * α₀ + τ * α₁ : ℝ) : EReal) := by
  rw [isConvexRelative_iff_convex_relativeEpigraph hC]
  constructor
  · intro hE x₀ hx₀ x₁ hx₁ α₀ α₁ h₀ h₁ τ hτ0 hτ1
    have hm := hE (x := (x₀, α₀)) (y := (x₁, α₁)) ⟨hx₀, h₀.le⟩ ⟨hx₁, h₁.le⟩
      (by linarith : (0 : ℝ) ≤ 1 - τ) hτ0.le (by ring)
    simpa only [mem_relativeEpigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hm.2
  · rintro h ⟨x₀, α₀⟩ ⟨hx₀, h₀⟩ ⟨x₁, α₁⟩ ⟨hx₁, h₁⟩ a b ha hb hab
    simp only at hx₀ h₀ hx₁ h₁
    refine ⟨hC hx₀ hx₁ ha hb hab, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rcases hb.eq_or_lt with rfl | hb'
    · obtain rfl : a = 1 := by linarith
      simpa using h₀
    rcases ha.eq_or_lt with rfl | ha'
    · obtain rfl : b = 1 := by linarith
      simpa using h₁
    have ha1 : a = 1 - b := by linarith
    subst ha1
    refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ ?_
    have hz' : (1 - b) * α₀ + b * α₁ < z := by exact_mod_cast hz
    set ε := z - ((1 - b) * α₀ + b * α₁) with hε
    have hεpos : 0 < ε := by linarith
    have key := h hx₀ hx₁ (α₀ := α₀ + ε) (α₁ := α₁ + ε)
      (h₀.trans_lt (by exact_mod_cast (by linarith : α₀ < α₀ + ε)))
      (h₁.trans_lt (by exact_mod_cast (by linarith : α₁ < α₁ + ε))) hb' (by linarith)
    refine key.trans (le_of_eq ?_)
    congr 1
    rw [hε]
    ring

/-- In 2(3) the open parameter interval may be replaced by `[0,1]`. -/
theorem isConvexRelative_iff_Icc (C : Set E) (f : E → EReal) :
    IsConvexRelative C f ↔
      ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → ∀ ⦃τ : ℝ⦄, 0 ≤ τ → τ ≤ 1 →
        f ((1 - τ) • x₀ + τ • x₁) ≤
          infAddition (((1 - τ : ℝ) : EReal) * f x₀) ((τ : EReal) * f x₁) := by
  constructor
  · intro hf x₀ hx₀ x₁ hx₁ τ hτ0 hτ1
    rcases hτ0.eq_or_lt with rfl | hτ0'
    · simp
    rcases hτ1.eq_or_lt with rfl | hτ1'
    · simp only [sub_self, EReal.coe_zero, zero_mul, one_smul, zero_smul, zero_add,
        EReal.coe_one, one_mul, infAddition]
      split_ifs <;> simp_all
    exact hf hx₀ hx₁ hτ0' hτ1'
  · exact fun hf x₀ hx₀ x₁ hx₁ τ hτ0 hτ1 ↦ hf hx₀ hx₁ hτ0.le hτ1.le

theorem IsConvexRelative.mono {C D : Set E} {f : E → EReal} (hf : IsConvexRelative C f)
    (hDC : D ⊆ C) : IsConvexRelative D f :=
  fun _ hx₀ _ hx₁ _ hτ0 hτ1 ↦ hf (hDC hx₀) (hDC hx₁) hτ0 hτ1

open Classical in
/-- A convex function on a convex set `C` is identified with the convex
function on the whole space taking the value `∞` outside `C`. -/
theorem isConvexRelative_iff_extension {C : Set E} (hC : Convex ℝ C) (f : E → EReal) :
    IsConvexRelative C f ↔
      IsConvexRelative univ (fun x ↦ if x ∈ C then f x else ⊤) := by
  constructor
  · intro hf x₀ _ x₁ _ τ hτ0 hτ1
    by_cases h₀ : x₀ ∈ C
    · by_cases h₁ : x₁ ∈ C
      · have hτ : (1 - τ) • x₀ + τ • x₁ ∈ C := hC h₀ h₁ (by linarith) hτ0.le (by ring)
        simpa [h₀, h₁, hτ] using hf h₀ h₁ hτ0 hτ1
      · change _ ≤ infAddition (_ * (if x₀ ∈ C then f x₀ else ⊤)) (_ * (if x₁ ∈ C then f x₁ else ⊤))
        rw [if_neg h₁, infAddition_convexCombination_right_top hτ0]
        exact le_top
    · change _ ≤ infAddition (_ * (if x₀ ∈ C then f x₀ else ⊤)) (_ * (if x₁ ∈ C then f x₁ else ⊤))
      rw [if_neg h₀, infAddition_convexCombination_left_top hτ1]
      exact le_top
  · intro hf x₀ hx₀ x₁ hx₁ τ hτ0 hτ1
    have hτ : (1 - τ) • x₀ + τ • x₁ ∈ C := hC hx₀ hx₁ (by linarith) hτ0.le (by ring)
    simpa [hx₀, hx₁, hτ] using hf (mem_univ x₀) (mem_univ x₁) hτ0 hτ1

/-- For real-valued functions, convexity relative to `C` is Mathlib's
`ConvexOn`. -/
theorem isConvexRelative_coe_iff {C : Set E} (hC : Convex ℝ C) (g : E → ℝ) :
    IsConvexRelative C (fun x ↦ (g x : EReal)) ↔ ConvexOn ℝ C g := by
  rw [isConvexRelative_iff_convex_relativeEpigraph hC, convexOn_iff_convex_epigraph]
  simp only [relativeEpigraph, EReal.coe_le_coe_iff]

/-- For real-valued functions, strict convexity relative to `C` is Mathlib's
`StrictConvexOn`. -/
theorem isStrictlyConvexRelative_coe_iff {C : Set E} (hC : Convex ℝ C) (g : E → ℝ) :
    IsStrictlyConvexRelative C (fun x ↦ (g x : EReal)) ↔ StrictConvexOn ℝ C g := by
  have hsum : ∀ τ x₀ x₁, infAddition (((1 - τ : ℝ) : EReal) * (g x₀ : EReal))
      ((τ : EReal) * (g x₁ : EReal)) = (((1 - τ) * g x₀ + τ * g x₁ : ℝ) : EReal) := by
    intro τ x₀ x₁
    rw [← EReal.coe_mul, ← EReal.coe_mul,
      infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _), ← EReal.coe_add]
  constructor
  · rintro ⟨-, hs⟩
    refine ⟨hC, fun x₀ hx₀ x₁ hx₁ hne a b ha hb hab ↦ ?_⟩
    have ha1 : a = 1 - b := by linarith
    subst ha1
    have := hs hx₀ hx₁ hne (EReal.coe_ne_top _) (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
      (EReal.coe_ne_bot _) hb (by linarith)
    rw [hsum] at this
    beta_reduce at this
    rw [smul_eq_mul, smul_eq_mul]
    exact_mod_cast this
  · intro hg
    refine ⟨(isConvexRelative_coe_iff hC g).mpr hg.convexOn, ?_⟩
    intro x₀ hx₀ x₁ hx₁ hne _ _ _ _ τ hτ0 hτ1
    rw [hsum]
    have := hg.2 hx₀ hx₁ hne (by linarith : (0 : ℝ) < 1 - τ) hτ0 (by ring)
    rw [smul_eq_mul, smul_eq_mul] at this
    beta_reduce
    exact_mod_cast this

/-- Convexity relative to `C` transfers to a function agreeing with `f` on `C`. -/
theorem IsConvexRelative.congr {C : Set E} (hC : Convex ℝ C) {f g : E → EReal}
    (hf : IsConvexRelative C f) (h : ∀ x ∈ C, f x = g x) : IsConvexRelative C g := by
  intro x₀ hx₀ x₁ hx₁ τ hτ0 hτ1
  rw [← h x₀ hx₀, ← h x₁ hx₁, ← h _ (hC hx₀ hx₁ (by linarith) hτ0.le (by ring))]
  exact hf hx₀ hx₁ hτ0 hτ1

/-! ## Proposition 2.4 -/

/-- **Proposition 2.4**: a function on the whole space is convex if and only
if its epigraph is convex. -/
theorem isConvexRelative_univ_iff (f : E → EReal) :
    IsConvexRelative univ f ↔ Convex ℝ (epigraph f) := by
  rw [isConvexRelative_iff_convex_relativeEpigraph convex_univ, relativeEpigraph_univ]

/-- **Proposition 2.4**, strict form: the epigraph is convex if and only if the
strict epigraph `{(x, α) | f x < α < ∞}` is convex. -/
theorem convex_epigraph_iff_convex_strictEpigraph (f : E → EReal) :
    Convex ℝ (epigraph f) ↔ Convex ℝ (strictEpigraph f) := by
  constructor
  · rintro hE ⟨x₀, α₀⟩ h₀ ⟨x₁, α₁⟩ h₁ a b ha hb hab
    simp only [mem_strictEpigraph] at h₀ h₁
    obtain ⟨β₀, hβ₀, hβα₀⟩ := EReal.lt_iff_exists_real_btwn.mp h₀
    obtain ⟨β₁, hβ₁, hβα₁⟩ := EReal.lt_iff_exists_real_btwn.mp h₁
    have hβα₀' : β₀ < α₀ := by exact_mod_cast hβα₀
    have hβα₁' : β₁ < α₁ := by exact_mod_cast hβα₁
    have hm := hE (x := (x₀, β₀)) (y := (x₁, β₁))
      (by simpa [mem_epigraph_iff] using hβ₀.le) (by simpa [mem_epigraph_iff] using hβ₁.le)
      ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mem_strictEpigraph]
    rw [epigraph, mem_setOf_eq] at hm
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, ge_iff_le] at hm
    refine hm.trans_lt ?_
    have : a * β₀ + b * β₁ < a * α₀ + b * α₁ := by
      rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_add] at hab; subst hab; simpa using hβα₁'
      · nlinarith
    exact_mod_cast this
  · rintro hS ⟨x₀, α₀⟩ h₀ ⟨x₁, α₁⟩ h₁ a b ha hb hab
    rw [mem_epigraph_iff] at h₀ h₁
    change (a • (x₀, α₀) + b • (x₁, α₁)) ∈ epigraph f
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mem_epigraph_iff]
    refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ ?_
    have hz' : a * α₀ + b * α₁ < z := by exact_mod_cast hz
    set ε := z - (a * α₀ + b * α₁) with hε
    have hεpos : 0 < ε := by linarith
    have hm := hS (x := (x₀, α₀ + ε)) (y := (x₁, α₁ + ε))
      (show f x₀ < ((α₀ + ε : ℝ) : EReal) from
        h₀.trans_lt (by exact_mod_cast (by linarith : α₀ < α₀ + ε)))
      (show f x₁ < ((α₁ + ε : ℝ) : EReal) from
        h₁.trans_lt (by exact_mod_cast (by linarith : α₁ < α₁ + ε))) ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mem_strictEpigraph] at hm
    refine hm.le.trans (le_of_eq ?_)
    congr 1
    have hb' : b = 1 - a := by linarith
    rw [hε, hb']
    ring

/-- **Proposition 2.4**, combined: convexity of `f`, of `epi f`, and of the
strict epigraph are equivalent. -/
theorem isConvexRelative_univ_iff_convex_strictEpigraph (f : E → EReal) :
    IsConvexRelative univ f ↔ Convex ℝ (strictEpigraph f) := by
  rw [isConvexRelative_univ_iff, convex_epigraph_iff_convex_strictEpigraph]

/-! ## Theorem 2.2 -/

/-- **Theorem 2.2(a)**: a set is convex if and only if it contains all convex
combinations of its elements. -/
theorem convex_iff_forall_convexCombination_mem (C : Set E) :
    Convex ℝ C ↔ ∀ (p : ℕ) (lam : Fin (p + 1) → ℝ) (x : Fin (p + 1) → E),
      (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 → (∀ i, x i ∈ C) → ∑ i, lam i • x i ∈ C := by
  constructor
  · intro hC p lam x h0 h1 hx
    exact hC.sum_mem (fun i _ ↦ h0 i) h1 (fun i _ ↦ hx i)
  · intro h x hx y hy a b ha hb hab
    have := h 1 ![a, b] ![x, y] (by intro i; fin_cases i <;> simp [ha, hb])
      (by simp [Fin.sum_univ_two, hab]) (by intro i; fin_cases i <;> simp [hx, hy])
    simpa [Fin.sum_univ_two] using this

/-- **Theorem 2.2(b) (Jensen's inequality)**: `f` is convex relative to a
convex set `C` if and only if inequality 2(5) holds for all convex
combinations of points of `C`, the right side being the finite inf-addition
of the terms `λᵢ f(xᵢ)`. -/
theorem isConvexRelative_iff_jensen {C : Set E} (hC : Convex ℝ C) (f : E → EReal) :
    IsConvexRelative C f ↔ ∀ (p : ℕ) (lam : Fin (p + 1) → ℝ) (x : Fin (p + 1) → E),
      (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 → (∀ i, x i ∈ C) →
        f (∑ i, lam i • x i) ≤ finiteInfAddition (fun i ↦ (lam i : EReal) * f (x i)) := by
  constructor
  · intro hf p lam x h0 h1 hx
    have hE := (isConvexRelative_iff_convex_relativeEpigraph hC f).mp hf
    unfold finiteInfAddition
    refine le_iInf fun r ↦ ?_
    obtain ⟨r, hr⟩ := r
    set S := Finset.univ.filter (fun i ↦ 0 < lam i) with hS
    have hzero : ∀ i, i ∉ S → lam i = 0 := by
      intro i hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (h0 i)
    have hrnonneg : ∀ i, i ∉ S → 0 ≤ r i := by
      intro i hi
      have := hr i
      simp only [hzero i hi, EReal.coe_zero, zero_mul] at this
      exact_mod_cast this
    have hpos : ∀ i ∈ S, 0 < lam i := fun i hi ↦ (Finset.mem_filter.mp hi).2
    have hpt : ∀ i ∈ S, (x i, r i / lam i) ∈ relativeEpigraph C f := fun i hi ↦
      ⟨hx i, ereal_le_coe_div_of_coe_mul_le (hpos i hi) (hr i)⟩
    have hsumS : ∑ i ∈ S, lam i = 1 := by
      rw [Finset.sum_filter_of_ne]
      · exact h1
      · intro i _ hne
        exact lt_of_le_of_ne (h0 i) (Ne.symm hne)
    have hmem := hE.sum_mem (t := S) (w := lam) (z := fun i ↦ (x i, r i / lam i))
      (fun i _ ↦ h0 i) hsumS hpt
    have hfst : (∑ i ∈ S, lam i • (x i, r i / lam i)).1 = ∑ i, lam i • x i := by
      rw [Prod.fst_sum]
      simp only [Prod.smul_fst]
      rw [Finset.sum_filter_of_ne]
      intro i _ hne
      refine lt_of_le_of_ne (h0 i) (fun h ↦ hne ?_)
      rw [← h, zero_smul]
    have hsnd : (∑ i ∈ S, lam i • (x i, r i / lam i)).2 = ∑ i ∈ S, r i := by
      rw [Prod.snd_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [Prod.smul_snd, smul_eq_mul]
      field_simp [(hpos i hi).ne']
    have hle : ∑ i ∈ S, r i ≤ ∑ i, r i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ hi ↦ hrnonneg i hi)
    have h2 := hmem.2
    rw [hfst, hsnd] at h2
    exact h2.trans (by exact_mod_cast hle)
  · intro h x₀ hx₀ x₁ hx₁ τ hτ0 hτ1
    have hJ := h 1 ![1 - τ, τ] ![x₀, x₁]
      (by intro i; fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_two]) (by intro i; fin_cases i <;> simp [hx₀, hx₁])
    calc f ((1 - τ) • x₀ + τ • x₁) = f (∑ i, (![1 - τ, τ] : Fin 2 → ℝ) i •
          (![x₀, x₁] : Fin 2 → E) i) := by simp [Fin.sum_univ_two]
      _ ≤ finiteInfAddition (fun i : Fin 2 ↦ (((![1 - τ, τ] : Fin 2 → ℝ) i : ℝ) : EReal) *
          f ((![x₀, x₁] : Fin 2 → E) i)) := hJ
      _ = finiteInfAddition ![((1 - τ : ℝ) : EReal) * f x₀, (τ : EReal) * f x₁] := by
          congr 1
          funext i
          fin_cases i <;> rfl
      _ = _ := finiteInfAddition_fin_two _ _

/-- The relative-epigraph form of convexity at two real upper bounds. -/
theorem IsConvexRelative.le_of_le {f : E → EReal} (hf : IsConvexRelative univ f) {x₀ x₁ : E}
    {r s : ℝ} (h₀ : f x₀ ≤ (r : EReal)) (h₁ : f x₁ ≤ (s : EReal)) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) : f ((1 - τ) • x₀ + τ • x₁) ≤ (((1 - τ) * r + τ * s : ℝ) : EReal) := by
  have hE := (isConvexRelative_iff_convex_relativeEpigraph convex_univ f).mp hf
  have := hE (x := (x₀, r)) (y := (x₁, s)) ⟨mem_univ _, h₀⟩ ⟨mem_univ _, h₁⟩
    (by linarith : 0 ≤ 1 - τ) hτ0 (by ring)
  simpa using this.2

/-! ## Exercise 2.3 -/

/-- **Exercise 2.3**: the effective domain of a convex function is convex. -/
theorem IsConvexRelative.convex_effectiveDomain {f : E → EReal}
    (hf : IsConvexRelative univ f) : Convex ℝ (effectiveDomain f) := by
  rw [← epigraph_proj_eq_effectiveDomain]
  simpa using ((isConvexRelative_univ_iff f).mp hf).linear_image (LinearMap.fst ℝ E ℝ)

/-- **Exercise 2.3**: a convex function is convex relative to its effective
domain. -/
theorem IsConvexRelative.isConvexRelative_effectiveDomain {f : E → EReal}
    (hf : IsConvexRelative univ f) : IsConvexRelative (effectiveDomain f) f :=
  hf.mono (subset_univ _)

/-- **Exercise 2.3**: the proper convex functions are exactly the finite convex
functions on nonempty convex sets `C`, extended by `∞` outside `C`. -/
theorem isProper_and_isConvexRelative_iff (f : E → EReal) :
    (IsProper f ∧ IsConvexRelative univ f) ↔
      ∃ C : Set E, C.Nonempty ∧ Convex ℝ C ∧ ∃ g : E → ℝ, ConvexOn ℝ C g ∧
        (∀ x ∈ C, f x = (g x : EReal)) ∧ ∀ x ∉ C, f x = ⊤ := by
  constructor
  · rintro ⟨hp, hf⟩
    have hdom := hf.convex_effectiveDomain
    refine ⟨effectiveDomain f, hp.1, hdom, fun x ↦ (f x).toReal, ?_, ?_, ?_⟩
    · rw [← isConvexRelative_coe_iff hdom]
      refine hf.isConvexRelative_effectiveDomain.congr hdom fun x hx ↦ ?_
      exact (EReal.coe_toReal hx.ne (hp.2 x).ne').symm
    · intro x hx
      exact (EReal.coe_toReal hx.ne (hp.2 x).ne').symm
    · intro x hx
      simpa [effectiveDomain] using hx
  · rintro ⟨C, hCne, hC, g, hg, hfC, hfout⟩
    refine ⟨⟨?_, fun x ↦ ?_⟩, ?_⟩
    · obtain ⟨x, hx⟩ := hCne
      exact ⟨x, by rw [hfC x hx]; exact EReal.coe_lt_top _⟩
    · by_cases hx : x ∈ C
      · rw [hfC x hx]; exact EReal.bot_lt_coe _
      · rw [hfout x hx]; exact bot_lt_top
    · classical
      have hext := (isConvexRelative_iff_extension hC (fun x ↦ (g x : EReal))).mp
        ((isConvexRelative_coe_iff hC g).mpr hg)
      refine hext.congr convex_univ fun x _ ↦ ?_
      by_cases hx : x ∈ C
      · simp [hx, hfC x hx]
      · simp [hx, hfout x hx]

/-- **Exercise 2.3**: the indicator `δ_C` is convex if and only if `C` is
convex. -/
theorem isConvexRelative_indicatorVA_iff (C : Set E) :
    IsConvexRelative univ (indicatorVA C) ↔ Convex ℝ C := by
  constructor
  · intro h
    simpa [effectiveDomain_indicatorVA] using h.convex_effectiveDomain
  · intro hC
    have h0 : IsConvexRelative C (fun _ ↦ ((0 : ℝ) : EReal)) :=
      (isConvexRelative_coe_iff hC _).mpr (convexOn_const 0 hC)
    refine ((isConvexRelative_iff_extension hC _).mp h0).congr convex_univ fun x _ ↦ ?_
    by_cases hx : x ∈ C <;> simp [hx, indicatorVA]

/-! ## Level sets (used for Theorem 2.6 and Proposition 2.7) -/

/-- Lower level sets `lev≤α f` of a convex function are convex. -/
theorem IsConvexRelative.convex_levelSet {f : E → EReal} (hf : IsConvexRelative univ f)
    (α : EReal) : Convex ℝ (levelSet f α) := by
  have hE := (isConvexRelative_univ_iff f).mp hf
  intro x₀ hx₀ x₁ hx₁ a b ha hb hab
  refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ ?_
  have hm := hE (x := (x₀, z)) (y := (x₁, z))
    ((mem_epigraph_iff f x₀ z).mpr ((show f x₀ ≤ α from hx₀).trans hz.le))
    ((mem_epigraph_iff f x₁ z).mpr ((show f x₁ ≤ α from hx₁).trans hz.le)) ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hm
  rw [mem_epigraph_iff, ← add_mul, hab, one_mul] at hm
  exact hm

/-- Strict lower level sets `lev<α f` of a convex function are convex. -/
theorem IsConvexRelative.convex_strictLevelSet {f : E → EReal} (hf : IsConvexRelative univ f)
    (α : EReal) : Convex ℝ (strictLevelSet f α) := by
  intro x₀ hx₀ x₁ hx₁ a b ha hb hab
  have hmax : max (f x₀) (f x₁) < α := max_lt hx₀ hx₁
  obtain ⟨z, hz, hzα⟩ := EReal.lt_iff_exists_real_btwn.mp hmax
  have := hf.convex_levelSet (z : EReal) (x := x₀) (y := x₁)
    ((le_max_left _ _).trans hz.le) ((le_max_right _ _).trans hz.le) ha hb hab
  exact lt_of_le_of_lt this hzα

/-! ## Exercise 2.5 -/

/-- Guide to **Exercise 2.5**: if `f(x₀) = -∞` and `f(x₁) < ∞`, then `f = -∞`
at every intermediate point of the segment. -/
theorem IsConvexRelative.eq_bot_of_eq_bot {C : Set E} {f : E → EReal}
    (hf : IsConvexRelative C f) {x₀ x₁ : E} (hx₀ : x₀ ∈ C) (hx₁ : x₁ ∈ C)
    (h₀ : f x₀ = ⊥) (h₁ : f x₁ < ⊤) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    f ((1 - τ) • x₀ + τ • x₁) = ⊥ := by
  have h := hf hx₀ hx₁ hτ0 hτ1
  rw [h₀, EReal.coe_mul_bot_of_pos (by linarith), infAddition, if_neg] at h
  · rw [EReal.bot_add] at h
    exact le_bot_iff.mp h
  · rintro (h' | h')
    · exact bot_ne_top h'
    · exact (ereal_coe_mul_lt_top hτ0.le h₁).ne h'

omit [AddCommGroup E] [Module ℝ E] in
/-- An improper function with nonempty effective domain takes the value
`-∞` somewhere. -/
theorem exists_eq_bot_of_not_isProper {f : E → EReal} (hnp : ¬IsProper f)
    (hdom : ∃ x, f x < ⊤) : ∃ x₀, f x₀ = ⊥ := by
  by_contra h
  push_neg at h
  exact hnp ⟨hdom, fun y ↦ bot_lt_iff_ne_bot.mpr (h y)⟩

end Algebraic

section Topological

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Exercise 2.5**: an improper convex function equals `-∞` on the interior
of its effective domain. -/
theorem IsConvexRelative.eq_bot_of_mem_interior_of_not_isProper {f : E → EReal}
    (hf : IsConvexRelative univ f) (hnp : ¬IsProper f) {x : E}
    (hx : x ∈ interior (effectiveDomain f)) : f x = ⊥ := by
  have hxdom : x ∈ effectiveDomain f := interior_subset hx
  obtain ⟨x₀, hx₀⟩ := exists_eq_bot_of_not_isProper hnp ⟨x, hxdom⟩
  have hcont : Continuous (fun ε : ℝ ↦ x + ε • (x - x₀)) := by fun_prop
  have htend : Tendsto (fun ε : ℝ ↦ x + ε • (x - x₀)) (𝓝[>] 0) (𝓝 x) := by
    have := hcont.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hε, hεpos⟩ :=
    ((htend.eventually (mem_interior_iff_mem_nhds.mp hx)).and self_mem_nhdsWithin).exists
  have hεpos' : (0 : ℝ) < ε := hεpos
  set τ : ℝ := 1 / (1 + ε) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 := by
    rw [hτ, div_lt_one (by linarith)]
    linarith
  have hkey : τ * (1 + ε) = 1 := by
    rw [hτ]
    field_simp
  have hx_eq : (1 - τ) • x₀ + τ • (x + ε • (x - x₀)) = x := by
    calc (1 - τ) • x₀ + τ • (x + ε • (x - x₀))
        = (1 - τ * (1 + ε)) • x₀ + (τ * (1 + ε)) • x := by module
      _ = x := by rw [hkey]; simp
  have := hf.eq_bot_of_eq_bot (mem_univ x₀) (mem_univ _) hx₀ hε hτ0 hτ1
  rwa [hx_eq] at this

/-- **Exercise 2.5**: an improper lower semicontinuous convex function takes
only infinite values; it is `-∞` on a closed convex set `D` and `∞` outside. -/
theorem IsConvexRelative.exists_closed_of_not_isProper {f : E → EReal}
    (hf : IsConvexRelative univ f) (hnp : ¬IsProper f) (hlsc : LowerSemicontinuous f) :
    ∃ D : Set E, IsClosed D ∧ Convex ℝ D ∧ (∀ x ∈ D, f x = ⊥) ∧ ∀ x ∉ D, f x = ⊤ := by
  have hbot : ∀ x ∈ effectiveDomain f, f x = ⊥ := by
    intro x hx
    obtain ⟨x₀, hx₀⟩ := exists_eq_bot_of_not_isProper hnp ⟨x, hx⟩
    by_contra hne
    have hev := hlsc x ⊥ (bot_lt_iff_ne_bot.mpr hne)
    have hcont : Continuous (fun τ : ℝ ↦ (1 - τ) • x₀ + τ • x) := by fun_prop
    have htend : Tendsto (fun τ : ℝ ↦ (1 - τ) • x₀ + τ • x) (𝓝[<] 1) (𝓝 x) := by
      have := hcont.tendsto 1
      simp only [sub_self, zero_smul, one_smul, zero_add] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨τ, hτ, hτmem⟩ := ((htend.eventually hev).and (Ioo_mem_nhdsLT zero_lt_one)).exists
    have := hf.eq_bot_of_eq_bot (mem_univ x₀) (mem_univ x) hx₀ hx hτmem.1 hτmem.2
    exact (ne_of_gt hτ) this
  refine ⟨effectiveDomain f, ?_, hf.convex_effectiveDomain, hbot, fun x hx ↦ ?_⟩
  · have : effectiveDomain f = f ⁻¹' Iic 0 := by
      ext x
      constructor
      · intro hx
        simp [hbot x hx]
      · intro hx
        exact lt_of_le_of_lt (show f x ≤ 0 from hx) EReal.zero_lt_top
    rw [this]
    exact hlsc.isClosed_preimage 0
  · simpa [effectiveDomain] using hx

/-! ## Theorem 2.6 -/

/-- A strict decrease along a segment, used for Theorem 2.6. -/
theorem ereal_convexCombination_lt {a b : EReal} (ha : a ≠ ⊤) (hb : b < a) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    infAddition (((1 - τ : ℝ) : EReal) * a) ((τ : EReal) * b) < a := by
  have ha' : a ≠ ⊥ := (hb.trans_le' bot_le).ne' |>.symm |> fun h ↦ by
    intro hbot; rw [hbot] at hb; exact not_lt_bot hb
  lift a to ℝ using ⟨ha, ha'⟩
  rw [infAddition_convexCombination_of_lt_top hτ0.le hτ1.le (EReal.coe_lt_top _)
    (hb.trans (EReal.coe_lt_top _))]
  induction b using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hτ0, EReal.add_bot]; exact EReal.bot_lt_coe _
  | top => exact absurd hb (not_lt_of_ge le_top)
  | coe c =>
    have hc : c < a := by exact_mod_cast hb
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    nlinarith

/-- **Theorem 2.6**: for a convex function, every locally optimal solution is
globally optimal. -/
theorem IsConvexRelative.mem_argmin_of_isLocalMin {f : E → EReal}
    (hf : IsConvexRelative univ f) {x₀ : E} (hfin : f x₀ < ⊤)
    (hloc : ∀ᶠ x in 𝓝 x₀, f x₀ ≤ f x) : x₀ ∈ argmin f := by
  have hglob : ∀ x, f x₀ ≤ f x := by
    intro x
    by_contra hlt
    push_neg at hlt
    have hcont : Continuous (fun τ : ℝ ↦ (1 - τ) • x₀ + τ • x) := by fun_prop
    have htend : Tendsto (fun τ : ℝ ↦ (1 - τ) • x₀ + τ • x) (𝓝[>] 0) (𝓝 x₀) := by
      have := hcont.tendsto 0
      simp only [sub_zero, one_smul, zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨τ, hτ, hτmem⟩ := ((htend.eventually hloc).and (Ioo_mem_nhdsGT zero_lt_one)).exists
    have h1 := hf (mem_univ x₀) (mem_univ x) hτmem.1 hτmem.2
    have h2 := ereal_convexCombination_lt hfin.ne hlt hτmem.1 hτmem.2
    exact (lt_irrefl _) (hτ.trans_lt (h1.trans_lt h2))
  rw [mem_argmin_iff]
  exact ⟨le_antisymm (le_iInf hglob) (iInf_le _ _), (iInf_le _ _).trans_lt hfin⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Theorem 2.6**: the set `argmin f` of a convex function is convex. -/
theorem IsConvexRelative.convex_argmin {f : E → EReal} (hf : IsConvexRelative univ f) :
    Convex ℝ (argmin f) := by
  by_cases hm : (⨅ y, f y) < ⊤
  · have : argmin f = levelSet f (⨅ y, f y) := by
      rw [argmin_eq_setOf_eq_iInf hm]
      ext x
      exact ⟨fun h ↦ le_of_eq h, fun h ↦ le_antisymm h (iInf_le _ _)⟩
    rw [this]
    exact hf.convex_levelSet _
  · have : argmin f = ∅ := by
      ext x
      simp [mem_argmin_iff, hm]
    rw [this]
    exact convex_empty

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Theorem 2.6**: a strictly convex proper function has at most one
minimizer. -/
theorem IsStrictlyConvexRelative.argmin_subsingleton {f : E → EReal}
    (hf : IsStrictlyConvexRelative univ f) (hp : IsProper f) : (argmin f).Subsingleton := by
  intro x₀ hx₀ x₁ hx₁
  by_contra hne
  rw [mem_argmin_iff] at hx₀ hx₁
  set m := ⨅ y, f y with hm
  have hmbot : m ≠ ⊥ := by rw [← hx₀.1]; exact (hp.2 x₀).ne'
  have hmtop : m ≠ ⊤ := hx₀.2.ne
  have h := hf.2 (mem_univ x₀) (mem_univ x₁) hne (hx₀.1 ▸ hmtop) (hx₀.1 ▸ hmbot)
    (hx₁.1 ▸ hmtop) (hx₁.1 ▸ hmbot) (τ := 1 / 2) (by norm_num) (by norm_num)
  rw [hx₀.1, hx₁.1] at h
  lift m to ℝ using ⟨hmtop, hmbot⟩ with a
  rw [← EReal.coe_mul, ← EReal.coe_mul,
    infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _), ← EReal.coe_add] at h
  have hval : (1 - 1 / 2 : ℝ) * a + 1 / 2 * a = a := by ring
  rw [hval] at h
  have hle : (a : EReal) ≤ f ((1 - 1 / 2 : ℝ) • x₀ + (1 / 2 : ℝ) • x₁) := by
    rw [hm]
    exact iInf_le _ _
  exact (lt_irrefl _) (h.trans_le' hle)

end Topological

end RW
