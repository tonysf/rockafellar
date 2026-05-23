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
import RockafellarWets.Chapter1.Semicontinuity
import Mathlib.Data.EReal.Operations

open Set EReal Filter Topology

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

private theorem ereal_eq_of_forall_real_upper_bounds {a b : EReal}
    (h : ∀ α : ℝ, a ≤ (α : EReal) ↔ b ≤ (α : EReal)) :
    a = b := by
  apply le_antisymm
  · by_contra hle
    have hlt : b < a := lt_of_not_ge hle
    obtain ⟨α, hbα, hαa⟩ := EReal.exists_between_coe_real hlt
    have hb_le : b ≤ (α : EReal) := le_of_lt hbα
    have ha_le : a ≤ (α : EReal) := (h α).2 hb_le
    exact (not_le_of_gt hαa) ha_le
  · by_contra hle
    have hlt : a < b := lt_of_not_ge hle
    obtain ⟨α, haα, hαb⟩ := EReal.exists_between_coe_real hlt
    have ha_le : a ≤ (α : EReal) := le_of_lt haα
    have hb_le : b ≤ (α : EReal) := (h α).1 ha_le
    exact (not_le_of_gt hαb) hb_le

private theorem coe_mul_le_coe_iff_le_inv_mul {a : EReal} {c α : ℝ}
    (hc : 0 < c) :
    ((c : EReal) * a ≤ (α : EReal) ↔
      a ≤ ((c⁻¹ * α : ℝ) : EReal)) := by
  cases a with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top =>
      rw [EReal.coe_mul_top_of_pos hc]
      have hfinite : ((c⁻¹ : EReal) * (α : EReal)) ≠ ⊤ := by
        rw [← EReal.coe_inv, ← EReal.coe_mul]
        exact EReal.coe_ne_top _
      constructor
      · intro htop
        exact False.elim ((EReal.coe_ne_top α) (top_le_iff.mp htop))
      · intro htop
        exact False.elim (hfinite (top_le_iff.mp htop))
  | coe x =>
      rw [← EReal.coe_mul]
      norm_cast
      exact (le_inv_mul_iff₀ hc).symm

/-- **Exercise 3.19**: if the epigraph of a function is a cone, then the
function is positively homogeneous. -/
theorem positivelyHomogeneous_of_isCone_epigraph {h : E → EReal}
    (hep : IsCone (epigraph h)) :
    PositivelyHomogeneous h := by
  refine ⟨?_, ?_⟩
  · have hmem : ((0 : E), (0 : ℝ)) ∈ epigraph h := by
      simpa using hep.1
    have hle : h 0 ≤ (0 : EReal) := by
      simpa [mem_epigraph_iff] using hmem
    exact lt_of_le_of_lt hle (EReal.coe_lt_top 0)
  · intro x c hc
    apply ereal_eq_of_forall_real_upper_bounds
    intro α
    calc
      h (c • x) ≤ (α : EReal)
          ↔ (c • x, α) ∈ epigraph h := (mem_epigraph_iff h (c • x) α).symm
      _ ↔ (x, c⁻¹ * α) ∈ epigraph h := by
            constructor
            · intro hp
              have hscaled : (c⁻¹ : ℝ) • (c • x, α) ∈ epigraph h :=
                hep.2 hp (inv_pos.mpr hc)
              simpa [Prod.smul_mk, smul_smul, smul_eq_mul,
                inv_mul_cancel₀ hc.ne'] using hscaled
            · intro hp
              have hscaled : c • (x, c⁻¹ * α) ∈ epigraph h := hep.2 hp hc
              have hα : c * (c⁻¹ * α) = α := by
                field_simp [hc.ne']
              simpa [Prod.smul_mk, smul_eq_mul, hα] using hscaled
      _ ↔ h x ≤ (((c⁻¹ * α : ℝ) : EReal)) := mem_epigraph_iff h x (c⁻¹ * α)
      _ ↔ (c : EReal) * h x ≤ (α : EReal) :=
            (coe_mul_le_coe_iff_le_inv_mul (a := h x) hc).symm

/-- **Exercise 3.19**: positive homogeneity is equivalent to conicity of the
epigraph. -/
theorem positivelyHomogeneous_iff_isCone_epigraph {h : E → EReal} :
    PositivelyHomogeneous h ↔ IsCone (epigraph h) := by
  constructor
  · exact isCone_epigraph_of_positivelyHomogeneous
  · exact positivelyHomogeneous_of_isCone_epigraph

/-- The zero lower level set of a positively homogeneous function is a cone. -/
theorem PositivelyHomogeneous.isCone_levelSet_zero {h : E → EReal}
    (hh : PositivelyHomogeneous h) :
    IsCone (levelSet h (0 : EReal)) := by
  refine ⟨?_, ?_⟩
  · exact hh.map_zero_le_zero
  · intro x hx c hc
    change h (c • x) ≤ (0 : EReal)
    rw [hh.2 hc]
    calc
      (c : EReal) * h x ≤ (c : EReal) * (0 : EReal) := by
        gcongr
        exact hx
      _ = 0 := by simp

/-- The zero lower level set of a sublinear function is a cone. -/
theorem Sublinear.isCone_levelSet_zero {h : E → EReal}
    (hh : Sublinear h) :
    IsCone (levelSet h (0 : EReal)) :=
  hh.1.isCone_levelSet_zero

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

/-- A function with convex epigraph and no value `⊥` satisfies the convexity
inequality. This is the `EReal` bridge needed for functions like entropy that
can take negative values but never `⊥`. -/
theorem convex_inequality_of_convex_epigraph_of_ne_bot {h : E → EReal}
    (hep : Convex ℝ (epigraph h)) (hbot : ∀ x, h x ≠ ⊥) :
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
    have hxbot : h x ≠ ⊥ := hbot x
    have hybot : h y ≠ ⊥ := hbot y
    have hxtop : h x ≠ ⊤ := by
      intro hxtop
      have hby_ne_bot : (b : EReal) * h y ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        exact ⟨Or.inl (EReal.coe_ne_bot b), Or.inr hybot,
          Or.inl (EReal.coe_ne_top b), Or.inl (by exact_mod_cast hb)⟩
      have hsum_top :
          (a : EReal) * h x + (b : EReal) * h y = ⊤ := by
        rw [hxtop, EReal.coe_mul_top_of_pos ha', EReal.top_add_of_ne_bot hby_ne_bot]
      exact htop hsum_top
    have hytop : h y ≠ ⊤ := by
      intro hytop
      have hax_ne_bot : (a : EReal) * h x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        exact ⟨Or.inl (EReal.coe_ne_bot a), Or.inr hxbot,
          Or.inl (EReal.coe_ne_top a), Or.inl (by exact_mod_cast ha)⟩
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

/-- Positive homogeneity together with convex epigraph and absence of `⊥`
values implies sublinearity. -/
theorem sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot
    {h : E → EReal}
    (hph : PositivelyHomogeneous h)
    (hep : Convex ℝ (epigraph h))
    (hbot : ∀ x, h x ≠ ⊥) :
    Sublinear h :=
  sublinear_of_positivelyHomogeneous_of_convex hph
    (convex_inequality_of_convex_epigraph_of_ne_bot hep hbot)

/-- **Exercise 3.19**, `EReal`-safe form: for functions with no `⊥` values,
sublinearity is equivalent to the epigraph being a convex cone. -/
theorem sublinear_iff_convex_isCone_epigraph_of_ne_bot {h : E → EReal}
    (hbot : ∀ x, h x ≠ ⊥) :
    Sublinear h ↔ Convex ℝ (epigraph h) ∧ IsCone (epigraph h) := by
  constructor
  · intro hh
    exact ⟨convex_epigraph_of_sublinear hh, isCone_epigraph_of_positivelyHomogeneous hh.1⟩
  · rintro ⟨hconv, hcone⟩
    exact sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot
      (positivelyHomogeneous_of_isCone_epigraph hcone) hconv hbot

/-- Proper-function specialization of the epigraph convex-cone criterion for
sublinearity. -/
theorem sublinear_iff_convex_isCone_epigraph_of_isProper {h : E → EReal}
    (hproper : IsProper h) :
    Sublinear h ↔ Convex ℝ (epigraph h) ∧ IsCone (epigraph h) :=
  sublinear_iff_convex_isCone_epigraph_of_ne_bot
    (fun x => ne_of_gt (hproper.2 x))

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

/-- A positively homogeneous proper function has value `0` at the origin. -/
theorem PositivelyHomogeneous.map_zero_eq_zero_of_isProper {h : E → EReal}
    (hh : PositivelyHomogeneous h) (hproper : IsProper h) :
    h 0 = 0 := by
  rcases hh.zero_eq_zero_or_bot with h0 | h0
  · exact h0
  · exact False.elim ((ne_of_gt (hproper.2 0)) h0)

/-- **Exercise 3.19**: a lower-semicontinuous positively homogeneous function
with value `0` at the origin is proper. -/
theorem PositivelyHomogeneous.isProper_of_lowerSemicontinuous_map_zero_eq_zero
    {h : E → EReal} (hh : PositivelyHomogeneous h)
    (hlsc : LowerSemicontinuous h) (h0 : h 0 = 0) :
    IsProper h := by
  refine ⟨⟨0, by simp [h0]⟩, ?_⟩
  intro x
  by_contra hx_not
  have hx_bot : h x = ⊥ := le_bot_iff.mp (not_lt.mp hx_not)
  have hclosed : IsClosed (epigraph h) := isClosed_epigraph_of_lsc_ereal h hlsc
  let u : ℕ → E × ℝ := fun n => ((((n : ℝ) + 1)⁻¹) • x, (-1 : ℝ))
  have hcoef_tendsto :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hsmul_tendsto :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹) • x) atTop (𝓝 (0 : E)) := by
    simpa using hcoef_tendsto.smul_const x
  have hu_tendsto : Tendsto u atTop (𝓝 ((0 : E), (-1 : ℝ))) := by
    simpa [u] using hsmul_tendsto.prodMk_nhds tendsto_const_nhds
  have hu_mem : ∀ᶠ n : ℕ in atTop, u n ∈ epigraph h := by
    refine Filter.Eventually.of_forall ?_
    intro n
    have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    rw [mem_epigraph_iff]
    rw [hh.2 (x := x) (c := ((n : ℝ) + 1)⁻¹) hpos, hx_bot,
      EReal.coe_mul_bot_of_pos hpos]
    exact bot_le
  have hlim : ((0 : E), (-1 : ℝ)) ∈ epigraph h :=
    hclosed.mem_of_tendsto hu_tendsto hu_mem
  have hbad : (0 : EReal) ≤ ((-1 : ℝ) : EReal) := by
    simpa [mem_epigraph_iff, h0] using hlim
  exact (by norm_num : ¬ (0 : EReal) ≤ ((-1 : ℝ) : EReal)) hbad

/-- The linearity region from **Exercise 3.20**, represented as the projection
of the lineality space of the epigraph. -/
noncomputable def linearitySubmoduleOfProperConvexPosHom
    (h : E → EReal) (hconv : Convex ℝ (epigraph h))
    (hph : PositivelyHomogeneous h) : Submodule ℝ E :=
  (linealitySubmoduleOfConvexCone hconv
    (isCone_epigraph_of_positivelyHomogeneous hph)).map (LinearMap.fst ℝ E ℝ)

/-- A finite-value subadditivity consequence used to identify the lineality
projection in Exercise 3.20. -/
private theorem neg_le_apply_neg_of_sublinear_of_isProper {h : E → EReal}
    (hh : Sublinear h) (hproper : IsProper h) (x : E) :
    -h x ≤ h (-x) := by
  have h0 : h 0 = 0 := hh.1.map_zero_eq_zero_of_isProper hproper
  have h0le : (0 : EReal) ≤ h x + h (-x) := by
    calc
      (0 : EReal) = h (x + -x) := by simp [h0]
      _ ≤ h x + h (-x) := hh.2 x (-x)
  have hsub : (0 : EReal) - h x ≤ h (-x) := by
    exact EReal.sub_le_of_le_add (by simpa [add_comm] using h0le)
  simpa using hsub

/-- **Exercise 3.20**: for a proper convex positively homogeneous function,
the projected lineality space of the epigraph is exactly the set where
`h (-x) = -h x`. -/
theorem mem_linearitySubmoduleOfProperConvexPosHom_iff
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    {x : E} :
    x ∈ linearitySubmoduleOfProperConvexPosHom h hconv hph ↔
      h (-x) = -h x := by
  let L :=
    linealitySubmoduleOfConvexCone hconv
      (isCone_epigraph_of_positivelyHomogeneous hph)
  have hsub : Sublinear h :=
    sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot hph hconv
      (fun y => ne_of_gt (hproper.2 y))
  constructor
  · intro hx
    rw [linearitySubmoduleOfProperConvexPosHom, Submodule.mem_map] at hx
    rcases hx with ⟨p, hp, hp_eq⟩
    rcases p with ⟨y, a⟩
    have hyx : y = x := by simpa using hp_eq
    subst y
    have hxy : h x ≤ (a : EReal) := by
      simpa [L, mem_epigraph_iff] using hp.1
    have hnegxy : h (-x) ≤ ((-a : ℝ) : EReal) := by
      simpa [L, mem_epigraph_iff, Prod.neg_mk] using hp.2
    have hneg_bound : ((-a : ℝ) : EReal) ≤ -h x := by
      have : -((a : ℝ) : EReal) ≤ -h x :=
        EReal.neg_le_neg_iff.2 hxy
      simpa [EReal.coe_neg] using this
    exact le_antisymm (hnegxy.trans hneg_bound)
      (neg_le_apply_neg_of_sublinear_of_isProper hsub hproper x)
  · intro hx
    rw [linearitySubmoduleOfProperConvexPosHom, Submodule.mem_map]
    have hx_bot : h x ≠ ⊥ := ne_of_gt (hproper.2 x)
    have hx_top : h x ≠ ⊤ := by
      intro htop
      have hneg_bot : h (-x) = ⊥ := by simpa [htop] using hx
      exact (ne_of_gt (hproper.2 (-x))) hneg_bot
    let a : ℝ := (h x).toReal
    have ha : (a : EReal) = h x := EReal.coe_toReal hx_top hx_bot
    refine ⟨(x, a), ?_, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [mem_epigraph_iff]
      exact le_of_eq ha.symm
    · rw [mem_epigraph_iff]
      simpa [Prod.neg_mk, EReal.coe_neg, ha] using le_of_eq hx

/-- **Exercise 3.20**: the equality region `h (-x) = -h x` is a linear
subspace for a proper convex positively homogeneous function. -/
theorem exists_submodule_eq_neg_apply_eq_neg_of_isProper_convex_posHom
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h) :
    ∃ M : Submodule ℝ E, (M : Set E) = {x | h (-x) = -h x} := by
  refine ⟨linearitySubmoduleOfProperConvexPosHom h hconv hph, ?_⟩
  ext x
  exact mem_linearitySubmoduleOfProperConvexPosHom_iff hproper hconv hph

private theorem apply_eq_coe_of_mem_lineality_epigraph
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    {x : E} {a : ℝ}
    (hp : (x, a) ∈
      linealitySubmoduleOfConvexCone hconv
        (isCone_epigraph_of_positivelyHomogeneous hph)) :
    h x = (a : EReal) := by
  have hsub : Sublinear h :=
    sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot hph hconv
      (fun y => ne_of_gt (hproper.2 y))
  have h0 : h 0 = 0 := hph.map_zero_eq_zero_of_isProper hproper
  have hxa : h x ≤ (a : EReal) := by
    simpa [mem_epigraph_iff] using hp.1
  have hnxa : h (-x) ≤ ((-a : ℝ) : EReal) := by
    simpa [mem_epigraph_iff, Prod.neg_mk] using hp.2
  have h0le : (0 : EReal) ≤ h x + h (-x) := by
    calc
      (0 : EReal) = h (x + -x) := by simp [h0]
      _ ≤ h x + h (-x) := hsub.2 x (-x)
  have h0le' : (0 : EReal) ≤ h x + ((-a : ℝ) : EReal) := by
    have hadd : h x + h (-x) ≤ h x + ((-a : ℝ) : EReal) := by
      gcongr
    exact h0le.trans hadd
  have ha_le : (a : EReal) ≤ h x := by
    have hsub' : (0 : EReal) - ((-a : ℝ) : EReal) ≤ h x := by
      exact EReal.sub_le_of_le_add (by simpa [add_comm] using h0le')
    simpa [EReal.coe_neg] using hsub'
  exact le_antisymm hxa ha_le

/-- **Exercise 3.20**: on the linearity subspace, `h` is additive. -/
theorem apply_add_of_mem_linearitySubmoduleOfProperConvexPosHom
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    {x y : E}
    (hx : x ∈ linearitySubmoduleOfProperConvexPosHom h hconv hph)
    (hy : y ∈ linearitySubmoduleOfProperConvexPosHom h hconv hph) :
    h (x + y) = h x + h y := by
  let L :=
    linealitySubmoduleOfConvexCone hconv
      (isCone_epigraph_of_positivelyHomogeneous hph)
  rw [linearitySubmoduleOfProperConvexPosHom, Submodule.mem_map] at hx hy
  rcases hx with ⟨p, hp, hp_eq⟩
  rcases hy with ⟨q, hq, hq_eq⟩
  rcases p with ⟨x', a⟩
  rcases q with ⟨y', b⟩
  have hx' : x' = x := by simpa using hp_eq
  have hy' : y' = y := by simpa using hq_eq
  subst x'
  subst y'
  have hxval : h x = (a : EReal) :=
    apply_eq_coe_of_mem_lineality_epigraph hproper hconv hph hp
  have hyval : h y = (b : EReal) :=
    apply_eq_coe_of_mem_lineality_epigraph hproper hconv hph hq
  have hsum_mem : ((x + y, a + b) : E × ℝ) ∈ L := by
    simpa [L, Prod.mk_add_mk] using L.add_mem hp hq
  have hsum : h (x + y) = ((a + b : ℝ) : EReal) :=
    apply_eq_coe_of_mem_lineality_epigraph hproper hconv hph hsum_mem
  calc
    h (x + y) = ((a + b : ℝ) : EReal) := hsum
    _ = h x + h y := by rw [hxval, hyval, EReal.coe_add]

/-- **Exercise 3.20**: on the linearity subspace, positive homogeneity upgrades
to full real homogeneity. -/
theorem apply_smul_of_mem_linearitySubmoduleOfProperConvexPosHom
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    {x : E} (hx : x ∈ linearitySubmoduleOfProperConvexPosHom h hconv hph)
    (c : ℝ) :
    h (c • x) = (c : EReal) * h x := by
  let L :=
    linealitySubmoduleOfConvexCone hconv
      (isCone_epigraph_of_positivelyHomogeneous hph)
  rw [linearitySubmoduleOfProperConvexPosHom, Submodule.mem_map] at hx
  rcases hx with ⟨p, hp, hp_eq⟩
  rcases p with ⟨x', a⟩
  have hx' : x' = x := by simpa using hp_eq
  subst x'
  have hxval : h x = (a : EReal) :=
    apply_eq_coe_of_mem_lineality_epigraph hproper hconv hph hp
  have hscaled_mem : ((c • x, c * a) : E × ℝ) ∈ L := by
    simpa [L, Prod.smul_mk, smul_eq_mul] using L.smul_mem c hp
  have hscaled : h (c • x) = ((c * a : ℝ) : EReal) :=
    apply_eq_coe_of_mem_lineality_epigraph hproper hconv hph hscaled_mem
  calc
    h (c • x) = ((c * a : ℝ) : EReal) := hscaled
    _ = (c : EReal) * h x := by rw [hxval, EReal.coe_mul]

/-- **Exercise 3.20**: the linearity subspace is all of the ambient space
exactly when `h (-x) = -h x` holds for every `x`. -/
theorem linearitySubmoduleOfProperConvexPosHom_eq_top_iff
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h) :
    linearitySubmoduleOfProperConvexPosHom h hconv hph = ⊤ ↔
      ∀ x : E, h (-x) = -h x := by
  constructor
  · intro htop x
    exact (mem_linearitySubmoduleOfProperConvexPosHom_iff hproper hconv hph).1
      (by rw [htop]; exact Submodule.mem_top)
  · intro hall
    ext x
    constructor
    · intro hx
      exact Submodule.mem_top
    · intro hx
      exact (mem_linearitySubmoduleOfProperConvexPosHom_iff hproper hconv hph).2
        (hall x)

/-- If the Exercise 3.20 linearity subspace is all of `E`, then `h` is
additive everywhere. -/
theorem apply_add_of_linearitySubmodule_eq_top
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    (htop : linearitySubmoduleOfProperConvexPosHom h hconv hph = ⊤)
    (x y : E) :
    h (x + y) = h x + h y := by
  apply apply_add_of_mem_linearitySubmoduleOfProperConvexPosHom hproper hconv hph
  · rw [htop]
    exact Submodule.mem_top
  · rw [htop]
    exact Submodule.mem_top

/-- If the Exercise 3.20 linearity subspace is all of `E`, then positive
homogeneity upgrades to full real homogeneity everywhere. -/
theorem apply_smul_of_linearitySubmodule_eq_top
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    (htop : linearitySubmoduleOfProperConvexPosHom h hconv hph = ⊤)
    (c : ℝ) (x : E) :
    h (c • x) = (c : EReal) * h x := by
  apply apply_smul_of_mem_linearitySubmoduleOfProperConvexPosHom hproper hconv hph
  rw [htop]
  exact Submodule.mem_top

/-- If the Exercise 3.20 linearity subspace is all of `E`, then `h` is finite
everywhere. -/
theorem apply_ne_top_of_linearitySubmodule_eq_top
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    (htop : linearitySubmoduleOfProperConvexPosHom h hconv hph = ⊤)
    (x : E) :
    h x ≠ ⊤ := by
  intro hx_top
  have hneg :
      h (-x) = -h x :=
    (linearitySubmoduleOfProperConvexPosHom_eq_top_iff hproper hconv hph).1 htop x
  have hneg_bot : h (-x) = ⊥ := by
    simpa [hx_top] using hneg
  exact (ne_of_gt (hproper.2 (-x))) hneg_bot

/-- If the Exercise 3.20 linearity subspace is all of `E`, then the real-valued
representative `toReal ∘ h` coerces back to `h`. -/
theorem coe_toReal_apply_of_linearitySubmodule_eq_top
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    (htop : linearitySubmoduleOfProperConvexPosHom h hconv hph = ⊤)
    (x : E) :
    (((h x).toReal : ℝ) : EReal) = h x :=
  EReal.coe_toReal
    (apply_ne_top_of_linearitySubmodule_eq_top hproper hconv hph htop x)
    (ne_of_gt (hproper.2 x))

/-- **Exercise 3.20**: if the linearity subspace is all of `E`, then `h` is a
real linear function, represented by a `LinearMap` into `ℝ`. -/
theorem exists_linearMap_coe_eq_of_linearitySubmodule_eq_top
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    (htop : linearitySubmoduleOfProperConvexPosHom h hconv hph = ⊤) :
    ∃ L : E →ₗ[ℝ] ℝ, ∀ x : E, h x = (L x : EReal) := by
  let hfin : ∀ x : E, (((h x).toReal : ℝ) : EReal) = h x :=
    coe_toReal_apply_of_linearitySubmodule_eq_top hproper hconv hph htop
  refine ⟨{
    toFun := fun x => (h x).toReal
    map_add' := ?_
    map_smul' := ?_
  }, ?_⟩
  · intro x y
    have hcoe :
        (((h (x + y)).toReal : ℝ) : EReal) =
          (((h x).toReal + (h y).toReal : ℝ) : EReal) := by
      calc
        (((h (x + y)).toReal : ℝ) : EReal) = h (x + y) := hfin (x + y)
        _ = h x + h y :=
          apply_add_of_linearitySubmodule_eq_top hproper hconv hph htop x y
        _ = (((h x).toReal : ℝ) : EReal) + (((h y).toReal : ℝ) : EReal) := by
          rw [hfin x, hfin y]
        _ = (((h x).toReal + (h y).toReal : ℝ) : EReal) := by
          rw [EReal.coe_add]
    exact_mod_cast hcoe
  · intro c x
    have hcoe :
        (((h (c • x)).toReal : ℝ) : EReal) =
          (((c * (h x).toReal : ℝ)) : EReal) := by
      calc
        (((h (c • x)).toReal : ℝ) : EReal) = h (c • x) := hfin (c • x)
        _ = (c : EReal) * h x :=
          apply_smul_of_linearitySubmodule_eq_top hproper hconv hph htop c x
        _ = (c : EReal) * (((h x).toReal : ℝ) : EReal) := by rw [hfin x]
        _ = (((c * (h x).toReal : ℝ)) : EReal) := by rw [EReal.coe_mul]
    exact_mod_cast hcoe
  · intro x
    exact (hfin x).symm

/-- **Exercise 3.20**: if `h` is represented by a real linear map, then its
linearity subspace is all of `E`. -/
theorem linearitySubmodule_eq_top_of_exists_linearMap_coe_eq
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h)
    (hlin : ∃ L : E →ₗ[ℝ] ℝ, ∀ x : E, h x = (L x : EReal)) :
    linearitySubmoduleOfProperConvexPosHom h hconv hph = ⊤ := by
  rcases hlin with ⟨L, hL⟩
  exact
    (linearitySubmoduleOfProperConvexPosHom_eq_top_iff hproper hconv hph).2
      (fun x => by
        calc
          h (-x) = (L (-x) : EReal) := hL (-x)
          _ = ((-L x : ℝ) : EReal) := by rw [map_neg]
          _ = -h x := by rw [EReal.coe_neg, hL x])

/-- **Exercise 3.20**: the linearity subspace is all of `E` iff `h` is a real
linear function. -/
theorem linearitySubmodule_eq_top_iff_exists_linearMap_coe_eq
    {h : E → EReal} (hproper : IsProper h)
    (hconv : Convex ℝ (epigraph h)) (hph : PositivelyHomogeneous h) :
    linearitySubmoduleOfProperConvexPosHom h hconv hph = ⊤ ↔
      ∃ L : E →ₗ[ℝ] ℝ, ∀ x : E, h x = (L x : EReal) := by
  constructor
  · exact exists_linearMap_coe_eq_of_linearitySubmodule_eq_top hproper hconv hph
  · exact linearitySubmodule_eq_top_of_exists_linearMap_coe_eq hproper hconv hph

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
