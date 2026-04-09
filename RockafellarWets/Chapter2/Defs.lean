/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2A: Convex Sets and Functions — Core Definitions

This file formalizes Section A of Chapter 2 of Rockafellar & Wets,
"Variational Analysis":
- Definition 2.1: Convex sets and convex functions (via Mathlib)
- Theorem 2.2: Jensen's inequality / convex combinations characterization
- Exercise 2.3: Effective domain of a convex function is convex
- Proposition 2.4: f is convex iff epi f is convex
- Exercise 2.5: Improper convex functions
- Theorem 2.6: Local min = global min for convex, argmin is convex

We use Mathlib's `Convex`, `ConvexOn`, `StrictConvexOn` throughout.
-/

import RockafellarWets.Chapter1.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.Basic

set_option linter.style.openClassical false

open Set Filter Topology EReal Classical

noncomputable section

namespace RW

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-! ## Definition 2.1: Convex Sets and Functions

We use Mathlib's existing definitions:
- `Convex ℝ S` for convex sets
- `ConvexOn ℝ S f` for convex functions on a set S
- `StrictConvexOn ℝ S f` for strictly convex functions

See `Mathlib.Analysis.Convex.Basic` and `Mathlib.Analysis.Convex.Function`.
-/

/-! ## Theorem 2.2: Jensen's Inequality / Convex Combinations

A function is convex iff its value at any convex combination of points
is at most the corresponding convex combination of function values.
This is essentially the definition of `ConvexOn` in Mathlib. -/

/-- **Theorem 2.2** (restated): A real-valued function `f` is convex on a
convex set `S` iff for all `x, y ∈ S` and `t ∈ [0,1]`,
`f(tx + (1-t)y) ≤ t * f(x) + (1-t) * f(y)`.
This is precisely `ConvexOn ℝ S f` in Mathlib. -/
theorem convexOn_iff_jensen {S : Set E} (hS : Convex ℝ S) (f : E → ℝ) :
    ConvexOn ℝ S f ↔
      ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S →
        ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
          f (a • x + b • y) ≤ a * f x + b * f y := by
  constructor
  · exact fun ⟨_, hf⟩ => hf
  · exact fun hf => ⟨hS, hf⟩

/-! ## Exercise 2.3: Effective domain of a convex function is convex -/

/-- **Exercise 2.3**: The effective domain of a convex (EReal-valued) function
is a convex set. Stated for functions `f : E → EReal` using our `effectiveDomain`. -/
theorem convex_effectiveDomain_of_convexOn_ereal
    {f : E → EReal}
    (hf : ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y) :
    Convex ℝ (effectiveDomain f) := by
  intro x hx y hy a b ha hb hab
  simp only [effectiveDomain, mem_setOf_eq] at hx hy ⊢
  have hconv := @hf x y a b ha hb hab
  apply lt_of_le_of_lt hconv
  have hx_ne_top : f x ≠ ⊤ := ne_of_lt hx
  have hy_ne_top : f y ≠ ⊤ := ne_of_lt hy
  have ha_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top a
  have hb_ne_top : (b : EReal) ≠ ⊤ := EReal.coe_ne_top b
  have ha_mul : (a : EReal) * f x ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot a), Or.inl (EReal.coe_nonneg.mpr ha),
           Or.inl ha_ne_top, Or.inr hx_ne_top⟩
  have hb_mul : (b : EReal) * f y ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot b), Or.inl (EReal.coe_nonneg.mpr hb),
           Or.inl hb_ne_top, Or.inr hy_ne_top⟩
  exact EReal.add_lt_top ha_mul hb_mul

/-! ## Proposition 2.4: Convexity via epigraphs -/

/-- **Proposition 2.4**: A function `f : E → EReal` is convex (in the sense
that `epi f` is a convex subset of `E × ℝ`) iff it satisfies the convexity
inequality. This connects the "epigraphical" and "functional" views of
convexity. -/
theorem convex_epigraph_iff_convexOn (f : E → ℝ) (S : Set E) (hS : Convex ℝ S) :
    Convex ℝ {p : E × ℝ | p.1 ∈ S ∧ f p.1 ≤ p.2} ↔ ConvexOn ℝ S f := by
  exact convexOn_iff_convex_epigraph.symm

/-! ## Exercise 2.5: Improper convex functions

An improper convex function (one taking the value `-∞`) must take `-∞`
everywhere on its effective domain. -/

/-- **Exercise 2.5**: If `f : E → EReal` is convex and takes `-∞` somewhere,
then `f` takes `-∞` on a convex subset of its effective domain. -/
theorem improper_convex_bot {f : E → EReal}
    (hconv : ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y)
    {x₀ : E} (hx₀ : f x₀ = ⊥) :
    ∀ y ∈ effectiveDomain f, ∀ t : ℝ, 0 < t → t < 1 →
      f ((1 - t) • x₀ + t • y) = ⊥ := by
  intro y _ t ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  have h1t_add : (1 - t) + t = 1 := by ring
  have hconv := @hconv x₀ y (1 - t) t (le_of_lt h1t) (le_of_lt ht0) h1t_add
  have : ((1 - t : ℝ) : EReal) * f x₀ = ⊥ := by
    rw [hx₀]
    exact EReal.coe_mul_bot_of_pos h1t
  rw [this, EReal.bot_add] at hconv
  exact le_antisymm (le_of_le_of_eq hconv rfl) bot_le

/-! ## Theorem 2.6: Local min = global min for convex functions -/

/-- **Theorem 2.6 (a)**: For a convex function on a convex set, every local
minimizer is a global minimizer. -/
theorem local_min_eq_global_min_of_convexOn
    [inst1 : IsTopologicalAddGroup E] [inst2 : ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) {f : E → ℝ} (hf : ConvexOn ℝ S f)
    {x₀ : E} (hx₀S : x₀ ∈ S)
    (hloc : ∃ U ∈ nhds x₀, ∀ x ∈ S ∩ U, f x₀ ≤ f x) :
    ∀ x ∈ S, f x₀ ≤ f x := by
  have hlocalmin : IsLocalMinOn f S x₀ := by
    obtain ⟨U, hU, hle⟩ := hloc
    rw [IsLocalMinOn, IsMinFilter]
    rw [Filter.Eventually, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨U, hU, fun z ⟨hzU, hzS⟩ => hle z ⟨hzS, hzU⟩⟩
  exact IsMinOn.of_isLocalMinOn_of_convexOn hx₀S hlocalmin hf

/-- **Theorem 2.6 (b)**: The set of global minimizers of a convex function
on a convex set is itself convex. -/
theorem convex_argmin_of_convexOn
    {S : Set E} (hS : Convex ℝ S) {f : E → ℝ} (hf : ConvexOn ℝ S f) :
    Convex ℝ {x ∈ S | ∀ y ∈ S, f x ≤ f y} := by
  intro x hx y hy a b ha hb hab
  constructor
  · exact hS hx.1 hy.1 ha hb hab
  · intro z hz
    have hfx := hx.2 z hz
    have hfy := hy.2 z hz
    calc f (a • x + b • y) ≤ a * f x + b * f y := hf.2 hx.1 hy.1 ha hb hab
    _ ≤ a * f z + b * f z := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hfx ha
        · exact mul_le_mul_of_nonneg_left hfy hb
    _ = f z := by rw [← add_mul, hab, one_mul]

/-- **Theorem 2.6 (b')**: For a strictly convex function, any minimizer is
unique. -/
theorem unique_argmin_of_strictConvexOn
    {S : Set E} (hS : Convex ℝ S) {f : E → ℝ} (hf : StrictConvexOn ℝ S f)
    {x y : E} (hxS : x ∈ S) (hyS : y ∈ S)
    (hx : ∀ z ∈ S, f x ≤ f z) (hy : ∀ z ∈ S, f y ≤ f z) :
    x = y := by
  by_contra hne
  have hmid : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ S :=
    hS hxS hyS (by norm_num) (by norm_num) (by norm_num)
  have hstrict := hf.2 hxS hyS hne (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  have hfx_eq : f x = f y := le_antisymm (hx y hyS) (hy x hxS)
  have hmin_x := hx _ hmid
  have : (1/2 : ℝ) • f x + (1/2 : ℝ) • f y = f x := by
    simp only [smul_eq_mul]; rw [hfx_eq]; ring
  linarith [this]

end RW
