/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3C: Positive Homogeneity and Sublinearity

This file formalizes the basic definitions from Section C that are needed for
horizon functions:
- Definition 3.18: positive homogeneity
- Definition 3.18: sublinearity
- the indicator-function examples attached to those notions
-/

import RockafellarWets.Chapter3.Cones
import RockafellarWets.Chapter1.Defs
import Mathlib.Data.EReal.Operations

open Set EReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 3.18**: a function is positively homogeneous if `0` belongs to
its effective domain and scaling by a positive real scales its value by the same
factor. -/
def PositivelyHomogeneous (h : E → EReal) : Prop :=
  h 0 < ⊤ ∧ ∀ ⦃x : E⦄ ⦃c : ℝ⦄, 0 < c → h (c • x) = (c : EReal) * h x

/-- **Definition 3.18**: a function is sublinear if it is positively homogeneous
and subadditive. -/
def Sublinear (h : E → EReal) : Prop :=
  PositivelyHomogeneous h ∧ ∀ x y : E, h (x + y) ≤ h x + h y

/-- A positively homogeneous function takes at the origin either the value `0`
or the value `⊥`. -/
theorem PositivelyHomogeneous.zero_eq_zero_or_bot {h : E → EReal}
    (hh : PositivelyHomogeneous h) :
    h 0 = 0 ∨ h 0 = ⊥ := by
  rcases hh with ⟨h0lt, hsmul⟩
  by_cases hbot : h 0 = ⊥
  · exact Or.inr hbot
  · left
    have hne_top : h 0 ≠ ⊤ := ne_of_lt h0lt
    have htwo : h 0 = (2 : EReal) * h 0 := by
      simpa using hsmul (x := 0) (c := 2) (by norm_num : (0 : ℝ) < 2)
    have htwo_real : h 0 = ((2 : ℝ) : EReal) * h 0 := by
      simpa using htwo
    have hreal : (((h 0).toReal : ℝ) : EReal) = h 0 := EReal.coe_toReal hne_top hbot
    have htwo_coe :
        (((h 0).toReal : ℝ) : EReal) = (((2 : ℝ) * (h 0).toReal : ℝ) : EReal) := by
      calc
        (((h 0).toReal : ℝ) : EReal) = h 0 := hreal
        _ = ((2 : ℝ) : EReal) * h 0 := htwo_real
        _ = ((2 : ℝ) : EReal) * (((h 0).toReal : ℝ) : EReal) := by rw [hreal]
        _ = (((2 : ℝ) * (h 0).toReal : ℝ) : EReal) := by rw [EReal.coe_mul]
    have htwo' : (h 0).toReal = 2 * (h 0).toReal := by
      exact_mod_cast htwo_coe
    have hzero : (h 0).toReal = 0 := by linarith
    rw [← EReal.coe_zero, ← hzero, hreal]

/-- A positively homogeneous function has value at the origin bounded above by
`0`. -/
theorem PositivelyHomogeneous.map_zero_le_zero {h : E → EReal}
    (hh : PositivelyHomogeneous h) :
    h 0 ≤ 0 := by
  rcases hh.zero_eq_zero_or_bot with h0 | h0
  · simp [h0]
  · simp [h0]

/-- A positively homogeneous function satisfies the expected scaling inequality
for nonnegative coefficients, with equality away from `0`. -/
theorem PositivelyHomogeneous.map_smul_le {h : E → EReal}
    (hh : PositivelyHomogeneous h) {x : E} {c : ℝ} (hc : 0 ≤ c) :
    h (c • x) ≤ (c : EReal) * h x := by
  rcases hc.eq_or_lt with rfl | hc'
  · simpa using hh.map_zero_le_zero
  · rw [hh.2 hc']

/-- The epigraph of a positively homogeneous function is a cone. -/
theorem isCone_epigraph_of_positivelyHomogeneous {h : E → EReal}
    (hh : PositivelyHomogeneous h) :
    IsCone (epigraph h) := by
  refine ⟨?_, ?_⟩
  · simpa [epigraph, ge_iff_le] using hh.map_zero_le_zero
  · intro p hp c hc
    rcases p with ⟨x, α⟩
    simp only [epigraph, mem_setOf_eq, ge_iff_le, Prod.smul_mk, smul_eq_mul] at hp ⊢
    calc
      h (c • x) = (c : EReal) * h x := hh.2 hc
      _ ≤ (c : EReal) * α := by gcongr
      _ = ((c * α : ℝ) : EReal) := by rw [EReal.coe_mul]

/-- The epigraph of a sublinear function is convex. -/
theorem convex_epigraph_of_sublinear {h : E → EReal} (hh : Sublinear h) :
    Convex ℝ (epigraph h) := by
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, α⟩
  rcases q with ⟨y, β⟩
  simp only [epigraph, mem_setOf_eq, ge_iff_le, Prod.smul_mk, Prod.mk_add_mk,
    smul_eq_mul] at hp hq ⊢
  calc
    h (a • x + b • y) ≤ h (a • x) + h (b • y) := hh.2 _ _
    _ ≤ (a : EReal) * h x + (b : EReal) * h y := by
      exact add_le_add (hh.1.map_smul_le ha) (hh.1.map_smul_le hb)
    _ ≤ (a : EReal) * α + (b : EReal) * β := by gcongr
    _ = (((a * α) + (b * β) : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]

/-- A nonnegative function with convex epigraph satisfies the convexity
inequality. This is the `EReal` version that avoids the `⊥` pathologies coming
from the project's arithmetic conventions. -/
theorem convex_inequality_of_convex_epigraph_of_nonneg {h : E → EReal}
    (hep : Convex ℝ (epigraph h)) (hnonneg : ∀ x, 0 ≤ h x) :
    ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      h (a • x + b • y) ≤ (a : EReal) * h x + (b : EReal) * h y := by
  intro x y a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1
    simp
  by_cases htop : (a : EReal) * h x + (b : EReal) * h y = ⊤
  · rw [htop]
    exact le_top
  · by_contra hxy
    have hlt :
        (a : EReal) * h x + (b : EReal) * h y <
          h (a • x + b • y) := by
      exact lt_of_not_ge hxy
    obtain ⟨γ, hγ₁, hγ₂⟩ := EReal.exists_between_coe_real hlt
    have hxbot : h x ≠ ⊥ := by
      intro hxbot
      simpa [hxbot] using hnonneg x
    have hybot : h y ≠ ⊥ := by
      intro hybot
      simpa [hybot] using hnonneg y
    have hxtop : h x ≠ ⊤ := by
      intro hxtop
      have hby_nonneg : (0 : EReal) ≤ (b : EReal) * h y := by
        exact mul_nonneg (by exact_mod_cast hb) (hnonneg y)
      have hby_ne_bot : (b : EReal) * h y ≠ ⊥ := by
        intro hby_bot
        rw [hby_bot] at hby_nonneg
        simp at hby_nonneg
      have hsum_top :
          (a : EReal) * h x + (b : EReal) * h y = ⊤ := by
        rw [hxtop, EReal.coe_mul_top_of_pos ha', EReal.top_add_of_ne_bot hby_ne_bot]
      exact htop hsum_top
    have hytop : h y ≠ ⊤ := by
      intro hytop
      have hax_nonneg : (0 : EReal) ≤ (a : EReal) * h x := by
        exact mul_nonneg (by exact_mod_cast ha) (hnonneg x)
      have hax_ne_bot : (a : EReal) * h x ≠ ⊥ := by
        intro hax_bot
        rw [hax_bot] at hax_nonneg
        simp at hax_nonneg
      have hsum_top :
          (a : EReal) * h x + (b : EReal) * h y = ⊤ := by
        rw [hytop, EReal.coe_mul_top_of_pos hb', EReal.add_top_of_ne_bot hax_ne_bot]
      exact htop hsum_top
    let α : ℝ := (h x).toReal
    let β : ℝ := (h y).toReal
    have hα : (α : EReal) = h x := EReal.coe_toReal hxtop hxbot
    have hβ : (β : EReal) = h y := EReal.coe_toReal hytop hybot
    have hxepi : (x, α) ∈ epigraph h := by
      rw [mem_epigraph_iff]
      exact le_of_eq hα.symm
    have hyepi : (y, β) ∈ epigraph h := by
      rw [mem_epigraph_iff]
      exact le_of_eq hβ.symm
    have hmem := hep hxepi hyepi ha hb hab
    have hzle :
        h (a • x + b • y) ≤ (((a * α + b * β : ℝ) : EReal)) := by
      simpa [mem_epigraph_iff, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hmem
    have hsum_lt : a * α + b * β < γ := by
      have hsum_lt' :
          (((a * α + b * β : ℝ) : EReal)) < (γ : EReal) := by
        calc
          (((a * α + b * β : ℝ) : EReal))
              = (a : EReal) * h x + (b : EReal) * h y := by
                  rw [← hα, ← hβ, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
          _ < (γ : EReal) := hγ₁
      exact_mod_cast hsum_lt'
    have hltγ : h (a • x + b • y) < (γ : EReal) := by
      exact lt_of_le_of_lt hzle (by exact_mod_cast hsum_lt)
    exact not_lt_of_ge (le_of_lt hγ₂) hltγ

/-- A sublinear function satisfies the convexity inequality. -/
theorem convex_inequality_of_sublinear {h : E → EReal}
    (hh : Sublinear h) :
    ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      h (a • x + b • y) ≤ (a : EReal) * h x + (b : EReal) * h y := by
  intro x y a b ha hb hab
  calc
    h (a • x + b • y) ≤ h (a • x) + h (b • y) := hh.2 _ _
    _ ≤ (a : EReal) * h x + (b : EReal) * h y := by
      exact add_le_add (hh.1.map_smul_le ha) (hh.1.map_smul_le hb)

/-- Positive homogeneity plus convexity implies sublinearity. -/
theorem sublinear_of_positivelyHomogeneous_of_convex
    {h : E → EReal}
    (hph : PositivelyHomogeneous h)
    (hconv : ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      h (a • x + b • y) ≤ (a : EReal) * h x + (b : EReal) * h y) :
    Sublinear h := by
  refine ⟨hph, ?_⟩
  intro x y
  have hmid :
      h ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤
        (((1 / 2 : ℝ) : EReal) * h x + ((1 / 2 : ℝ) : EReal) * h y) := by
    exact hconv (x := x) (y := y) (a := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  have hscale :
      h (x + y) = ((2 : ℝ) : EReal) * h ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
    simpa [smul_add, two_smul] using
      hph.2 (x := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) (c := 2) (by norm_num : (0 : ℝ) < 2)
  have htwo_nonneg : (0 : EReal) ≤ ((2 : ℝ) : EReal) := by positivity
  have htwo_ne_top : (((2 : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top 2
  calc
    h (x + y) = ((2 : ℝ) : EReal) * h ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := hscale
    _ ≤ ((2 : ℝ) : EReal) *
          ((((1 / 2 : ℝ) : EReal) * h x) + (((1 / 2 : ℝ) : EReal) * h y)) := by
          gcongr
    _ = h x + h y := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top htwo_nonneg htwo_ne_top]
      have hhalf : (((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal))) = (1 : EReal) := by
        rw [← EReal.coe_mul]
        norm_num
      rw [← mul_assoc, ← mul_assoc]
      rw [hhalf, one_mul]
      rw [one_mul]

/-- Positive homogeneity together with convex epigraph and nonnegativity implies
sublinearity. This is the version compatible with the project's `EReal`
arithmetic. -/
theorem sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_nonneg
    {h : E → EReal}
    (hph : PositivelyHomogeneous h)
    (hep : Convex ℝ (epigraph h))
    (hnonneg : ∀ x, 0 ≤ h x) :
    Sublinear h :=
  sublinear_of_positivelyHomogeneous_of_convex hph
    (convex_inequality_of_convex_epigraph_of_nonneg hep hnonneg)

/-- A function is sublinear iff it is positively homogeneous and satisfies the
convexity inequality. -/
theorem sublinear_iff_positivelyHomogeneous_and_convex
    {h : E → EReal} :
    Sublinear h ↔
      PositivelyHomogeneous h ∧
      ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
        0 ≤ a → 0 ≤ b → a + b = 1 →
        h (a • x + b • y) ≤ (a : EReal) * h x + (b : EReal) * h y := by
  constructor
  · intro hh
    exact ⟨hh.1, convex_inequality_of_sublinear hh⟩
  · rintro ⟨hph, hconv⟩
    exact sublinear_of_positivelyHomogeneous_of_convex hph hconv

/-- The indicator function of a set is positively homogeneous iff the set is a
cone. -/
theorem positivelyHomogeneous_indicatorVA_iff {C : Set E} :
    PositivelyHomogeneous (indicatorVA C) ↔ IsCone C := by
  constructor
  · rintro ⟨h0, hsmul⟩
    refine ⟨?_, ?_⟩
    · by_contra hC0
      simp [indicatorVA, hC0] at h0
    · intro x hx c hc
      have hcx : indicatorVA C (c • x) = 0 := by
        simpa [indicatorVA, hx] using hsmul (x := x) (c := c) hc
      by_contra hmem
      simp [indicatorVA, hmem] at hcx
  · intro hC
    refine ⟨by simp [indicatorVA, hC.1], ?_⟩
    intro x c hc
    by_cases hx : x ∈ C
    · have hcx : c • x ∈ C := hC.2 hx hc
      simp [indicatorVA, hx, hcx]
    · have hcx : c • x ∉ C := by
        intro hcx
        have : x ∈ C := by
          simpa [inv_smul_smul₀ hc.ne'] using hC.2 hcx (inv_pos_of_pos hc)
        exact hx this
      simp [indicatorVA, hx, hcx, EReal.coe_mul_top_of_pos hc]

/-- The indicator function of a set is sublinear iff the set is a convex cone. -/
theorem sublinear_indicatorVA_iff {C : Set E} :
    Sublinear (indicatorVA C) ↔ Convex ℝ C ∧ IsCone C := by
  constructor
  · rintro ⟨hph, hadd⟩
    have hcone : IsCone C := positivelyHomogeneous_indicatorVA_iff.mp hph
    refine ⟨(hcone.convex_iff_add_mem).2 ?_, hcone⟩
    intro x y hx hy
    by_contra hxy
    have h := hadd x y
    simp [indicatorVA, hx, hy, hxy] at h
  · rintro ⟨hconv, hcone⟩
    refine ⟨positivelyHomogeneous_indicatorVA_iff.mpr hcone, ?_⟩
    intro x y
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
    · have hxy : x + y ∈ C := add_mem_of_convex_isCone hconv hcone hx hy
      simp [indicatorVA, hx, hy, hxy]
    · simp [indicatorVA, hx, hy]
    · simp [indicatorVA, hx, hy]
    · simp [indicatorVA, hx, hy]

end RW
