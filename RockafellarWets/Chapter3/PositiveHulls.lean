/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Positive Hulls

This file starts Section G by formalizing the positive hull of a set and its
basic properties:
- the positive hull is the smallest cone containing the set;
- the positive hull of a convex set is convex.
-/

import RockafellarWets.Chapter3.HorizonCones
import RockafellarWets.Chapter3.HomogeneousOperations
import RockafellarWets.Chapter1.Semicontinuity
import Mathlib.Analysis.SpecificLimits.Basic

open Set EReal
open scoped Pointwise

namespace RW

section Sets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Section G**: the positive hull of a set. This matches formula `3(11)`,
including the convention `positiveHull ∅ = {0}`. -/
def positiveHull (C : Set E) : Set E :=
  {x | x = 0 ∨ ∃ a : ℝ, 0 < a ∧ ∃ y ∈ C, x = a • y}

theorem mem_positiveHull {C : Set E} {x : E} :
    x ∈ positiveHull C ↔ x = 0 ∨ ∃ a : ℝ, 0 < a ∧ ∃ y ∈ C, x = a • y := by
  rfl

theorem zero_mem_positiveHull (C : Set E) : (0 : E) ∈ positiveHull C := by
  left
  rfl

theorem subset_positiveHull {C : Set E} : C ⊆ positiveHull C := by
  intro x hx
  right
  exact ⟨1, by norm_num, x, hx, by simp⟩

/-- The positive hull is a cone. -/
theorem isCone_positiveHull {C : Set E} : IsCone (positiveHull C) := by
  refine ⟨zero_mem_positiveHull C, ?_⟩
  intro x hx c hc
  rcases hx with rfl | ⟨a, ha, y, hy, rfl⟩
  · left
    simp
  · right
    refine ⟨c * a, mul_pos hc ha, y, hy, ?_⟩
    simp [smul_smul]

/-- The positive hull is the smallest cone containing the set. -/
theorem positiveHull_minimal {C K : Set E}
    (hK : IsCone K) (hCK : C ⊆ K) :
    positiveHull C ⊆ K := by
  intro x hx
  rcases hx with rfl | ⟨a, ha, y, hy, rfl⟩
  · exact hK.1
  · exact hK.2 (hCK hy) ha

theorem positiveHull_eq_self {C : Set E} (hC : IsCone C) :
    positiveHull C = C := by
  apply le_antisymm
  · exact positiveHull_minimal hC subset_rfl
  · exact subset_positiveHull

theorem positiveHull_eq_iff_isCone {C : Set E} :
    positiveHull C = C ↔ IsCone C := by
  constructor
  · intro hC
    rw [← hC]
    exact isCone_positiveHull
  · exact positiveHull_eq_self

/-- **Exercise 3.49(a)**: the positive hull of a convex set is convex. -/
theorem convex_positiveHull {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (positiveHull C) := by
  rw [(isCone_positiveHull : IsCone (positiveHull C)).convex_iff_add_mem]
  intro x y hx hy
  rcases hx with rfl | ⟨a, ha, u, hu, rfl⟩
  · simpa using hy
  · rcases hy with rfl | ⟨b, hb, v, hv, rfl⟩
    · right
      exact ⟨a, ha, u, hu, by simp⟩
    · have hs : 0 < a + b := add_pos ha hb
      have hsa : 0 ≤ a / (a + b) := div_nonneg ha.le hs.le
      have hsb : 0 ≤ b / (a + b) := div_nonneg hb.le hs.le
      have hsum : a / (a + b) + b / (a + b) = 1 := by
        field_simp [hs.ne']
      have huv :
          (a / (a + b)) • u + (b / (a + b)) • v ∈ C :=
        hC hu hv hsa hsb hsum
      right
      refine ⟨a + b, hs, (a / (a + b)) • u + (b / (a + b)) • v, huv, ?_⟩
      rw [smul_add, smul_smul, smul_smul]
      have hcoef_a : (a + b) * (a / (a + b)) = a := by
        field_simp [hs.ne']
      have hcoef_b : (a + b) * (b / (a + b)) = b := by
        field_simp [hs.ne']
      simp [hcoef_a, hcoef_b]

end Sets

section Functions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Section G**: the positive hull of a function is the lower boundary of the
positive hull of its epigraph, matching formula `3(12)`. -/
noncomputable def positiveHullFunction (f : E → EReal) (x : E) : EReal :=
  ⨅ a : {a : ℝ // (x, a) ∈ positiveHull (epigraph f)}, (a : EReal)

/-- Any point of `positiveHull (epi f)` lies on or above `positiveHullFunction f`. -/
theorem positiveHullFunction_le_of_mem_positiveHull_epigraph {f : E → EReal} {x : E} {a : ℝ}
    (ha : (x, a) ∈ positiveHull (epigraph f)) :
    positiveHullFunction f x ≤ (a : EReal) := by
  exact iInf_le
    (fun b : {a : ℝ // (x, a) ∈ positiveHull (epigraph f)} => (b : EReal))
    ⟨a, ha⟩

/-- The positive hull of `epi f` is contained in `epi(pos f)`. -/
theorem positiveHull_epigraph_subset_epigraph_positiveHullFunction (f : E → EReal) :
    positiveHull (epigraph f) ⊆ epigraph (positiveHullFunction f) := by
  intro p hp
  rcases p with ⟨x, a⟩
  rw [mem_epigraph_iff]
  exact positiveHullFunction_le_of_mem_positiveHull_epigraph hp

/-- The infimum of the real epigraph slice above an `EReal` point is the point
itself. -/
theorem iInf_coe_real_ge_eq (z : EReal) :
    (⨅ a : {a : ℝ // z ≤ (a : EReal)}, (a : EReal)) = z := by
  cases z using EReal.rec with
  | bot =>
      rw [iInf_subtype]
      simp only [bot_le, iInf_pos]
      refine le_antisymm ?_ bot_le
      by_contra hne
      have hlt : (⊥ : EReal) < ⨅ a : ℝ, (a : EReal) := by
        exact lt_of_not_ge hne
      obtain ⟨r, hr₁, hr₂⟩ := EReal.exists_between_coe_real hlt
      exact not_le_of_gt hr₂ (iInf_le (fun a : ℝ => (a : EReal)) r)
  | coe r =>
      refine le_antisymm ?_ ?_
      · exact iInf_le
          (fun a : {a : ℝ // (r : EReal) ≤ (a : EReal)} => (a : EReal))
          ⟨r, by simp⟩
      · refine le_iInf ?_
        intro a
        exact a.property
  | top =>
      simp

/-- The positive hull function is always a minorant of the original function. -/
theorem positiveHullFunction_le_apply (f : E → EReal) (x : E) :
    positiveHullFunction f x ≤ f x := by
  let A : Type := {a : ℝ // f x ≤ (a : EReal)}
  calc
    positiveHullFunction f x ≤ ⨅ a : A, (a : EReal) := by
      refine le_iInf ?_
      intro a
      exact positiveHullFunction_le_of_mem_positiveHull_epigraph <|
        subset_positiveHull <| by
          simpa [mem_epigraph_iff] using a.property
    _ = f x := by
      simpa [A] using iInf_coe_real_ge_eq (f x)

/-- Positive scaling of the argument scales the positive hull function by at
least the same factor. -/
theorem smul_positiveHullFunction_le {f : E → EReal} {w : E} {c : ℝ} (hc : 0 < c) :
    (c : EReal) * positiveHullFunction f w ≤ positiveHullFunction f (c • w) := by
  refine le_iInf ?_
  intro b
  have hscaled :
      (w, (c⁻¹ : ℝ) * (b : ℝ)) ∈ positiveHull (epigraph f) := by
    have hsmul :
        (c⁻¹ : ℝ) • (c • w, (b : ℝ)) ∈ positiveHull (epigraph f) :=
      (isCone_positiveHull (C := epigraph f)).2 b.property (inv_pos_of_pos hc)
    simpa [Prod.smul_mk, smul_smul, inv_mul_cancel₀ hc.ne'] using hsmul
  have hbound :
      positiveHullFunction f w ≤ (((c⁻¹ : ℝ) * (b : ℝ) : ℝ) : EReal) :=
    positiveHullFunction_le_of_mem_positiveHull_epigraph hscaled
  have hmul :
      (c : EReal) * positiveHullFunction f w ≤
        (c : EReal) * ((((c⁻¹ : ℝ) * (b : ℝ) : ℝ) : EReal)) := by
    gcongr
  have hcancel :
      (c : EReal) * ((((c⁻¹ : ℝ) * (b : ℝ) : ℝ) : EReal)) = (b : EReal) := by
    rw [← EReal.coe_mul]
    have hreal : c * ((c⁻¹ : ℝ) * (b : ℝ)) = (b : ℝ) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    exact_mod_cast hreal
  calc
    (c : EReal) * positiveHullFunction f w ≤
        (c : EReal) * ((((c⁻¹ : ℝ) * (b : ℝ) : ℝ) : EReal)) := hmul
    _ = (b : EReal) := hcancel

/-- The positive hull function is positively homogeneous. -/
theorem positivelyHomogeneous_positiveHullFunction (f : E → EReal) :
    PositivelyHomogeneous (positiveHullFunction f) := by
  refine ⟨?_, ?_⟩
  · have hzero :
      positiveHullFunction f 0 ≤ (0 : EReal) :=
        positiveHullFunction_le_of_mem_positiveHull_epigraph
          (zero_mem_positiveHull (epigraph f))
    exact lt_of_le_of_lt hzero (by simp)
  · intro w c hc
    apply le_antisymm
    · have hInv :
          (((c⁻¹ : ℝ) : EReal) * positiveHullFunction f (c • w)) ≤ positiveHullFunction f w := by
        simpa [smul_smul, hc.ne'] using
          smul_positiveHullFunction_le (f := f) (w := c • w) (c := c⁻¹) (inv_pos_of_pos hc)
      have hmul :
          (c : EReal) * ((((c⁻¹ : ℝ) : EReal) * positiveHullFunction f (c • w))) ≤
            (c : EReal) * positiveHullFunction f w := by
        gcongr
      have hhalf : (c : EReal) * (((c⁻¹ : ℝ) : EReal)) = 1 := by
        rw [← EReal.coe_mul]
        exact_mod_cast (mul_inv_cancel₀ hc.ne' : c * c⁻¹ = (1 : ℝ))
      calc
        positiveHullFunction f (c • w)
            = (1 : EReal) * positiveHullFunction f (c • w) := by rw [one_mul]
        _ = (c : EReal) * ((((c⁻¹ : ℝ) : EReal) * positiveHullFunction f (c • w))) := by
          rw [← mul_assoc, hhalf]
        _ ≤ (c : EReal) * positiveHullFunction f w := hmul
    · exact smul_positiveHullFunction_le (f := f) (w := w) hc

/-- The positive hull function is the greatest positively homogeneous minorant
of the original function. -/
theorem le_positiveHullFunction_of_positivelyHomogeneous_of_le {f g : E → EReal}
    (hg : PositivelyHomogeneous g) (hgf : g ≤ f) :
    g ≤ positiveHullFunction f := by
  have hsubset : epigraph f ⊆ epigraph g := by
    intro p hp
    rcases p with ⟨x, a⟩
    rw [mem_epigraph_iff] at hp ⊢
    exact le_trans (hgf x) hp
  have hpos : positiveHull (epigraph f) ⊆ epigraph g :=
    positiveHull_minimal (isCone_epigraph_of_positivelyHomogeneous hg) hsubset
  intro x
  refine le_iInf ?_
  intro a
  have ha : (x, (a : ℝ)) ∈ epigraph g := hpos a.property
  simpa [mem_epigraph_iff] using ha

/-- A positively homogeneous function is unchanged by the positive hull
operation. -/
theorem positiveHullFunction_eq_self_of_positivelyHomogeneous {f : E → EReal}
    (hf : PositivelyHomogeneous f) :
    positiveHullFunction f = f := by
  funext x
  exact le_antisymm (positiveHullFunction_le_apply f x)
    (le_positiveHullFunction_of_positivelyHomogeneous_of_le hf (fun _ => le_rfl) x)

/-- If `positiveHullFunction f x` lies strictly below a real number `α`, then
some point of the positive hull of the epigraph realizes a lower real height
below `α`. -/
theorem exists_mem_positiveHull_epigraph_lt {f : E → EReal} {x : E} {α : ℝ}
    (hα : positiveHullFunction f x < (α : EReal)) :
    ∃ a : ℝ, (x, a) ∈ positiveHull (epigraph f) ∧ (a : EReal) < α := by
  let A : Type := {a : ℝ // (x, a) ∈ positiveHull (epigraph f)}
  have hA_nonempty : Nonempty A := by
    by_contra hA
    letI : IsEmpty A := not_nonempty_iff.mp hA
    have htop : positiveHullFunction f x = ⊤ := by
      rw [positiveHullFunction]
      exact iInf_of_empty _
    have : (⊤ : EReal) < (α : EReal) := by
      rw [htop] at hα
      simp at hα
    exact not_top_lt this
  letI : Nonempty A := hA_nonempty
  have hlt : (⨅ a : A, (a : EReal)) < (α : EReal) := by
    simpa [A, positiveHullFunction] using hα
  obtain ⟨a, ha⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨a, a.property, ha⟩

/-- The epigraph of the positive hull function is convex whenever the original
epigraph is convex. This is the function-side form of Exercise `3.49(b)`. -/
theorem convex_epigraph_positiveHullFunction {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) :
    Convex ℝ (epigraph (positiveHullFunction f)) := by
  have hconvPos : Convex ℝ (positiveHull (epigraph f)) := convex_positiveHull hconv
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, α⟩
  rcases q with ⟨y, β⟩
  rw [mem_epigraph_iff] at hp hq ⊢
  by_contra hxy
  have hlt :
      (((a * α + b * β : ℝ) : EReal)) <
        positiveHullFunction f (a • x + b • y) :=
    lt_of_not_ge hxy
  obtain ⟨γ, hγ₁, hγ₂⟩ := EReal.exists_between_coe_real hlt
  let ε : ℝ := (γ - (a * α + b * β)) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    have hγ₁' : a * α + b * β < γ := by
      exact_mod_cast hγ₁
    linarith
  have hxlt : positiveHullFunction f x < ((α + ε : ℝ) : EReal) := by
    calc
      positiveHullFunction f x ≤ (α : EReal) := hp
      _ < ((α + ε : ℝ) : EReal) := by
        exact_mod_cast lt_add_of_pos_right α hε
  have hylt : positiveHullFunction f y < ((β + ε : ℝ) : EReal) := by
    calc
      positiveHullFunction f y ≤ (β : EReal) := hq
      _ < ((β + ε : ℝ) : EReal) := by
        exact_mod_cast lt_add_of_pos_right β hε
  obtain ⟨α', hα'mem, hα'lt⟩ := exists_mem_positiveHull_epigraph_lt hxlt
  obtain ⟨β', hβ'mem, hβ'lt⟩ := exists_mem_positiveHull_epigraph_lt hylt
  have hmem :
      (a • x + b • y, a * α' + b * β') ∈ positiveHull (epigraph f) := by
    have hmem' := hconvPos hα'mem hβ'mem ha hb hab
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hmem'
  have hbound :
      positiveHullFunction f (a • x + b • y) ≤ (((a * α' + b * β' : ℝ)) : EReal) :=
    positiveHullFunction_le_of_mem_positiveHull_epigraph hmem
  have hα'lt' : α' < α + ε := by
    exact_mod_cast hα'lt
  have hβ'lt' : β' < β + ε := by
    exact_mod_cast hβ'lt
  have hγ₁' : a * α + b * β < γ := by
    exact_mod_cast hγ₁
  have hsumlt : a * α' + b * β' < γ := by
    have hsumlt' : a * α' + b * β' < a * (α + ε) + b * (β + ε) := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith [hab, ha0]
        subst ha0
        subst hb1
        simpa using hβ'lt'
      · have ha_pos : 0 < a := lt_of_le_of_ne ha fun h => ha0 h.symm
        have hαmul : a * α' < a * (α + ε) := by
          gcongr
        have hβmul : b * β' ≤ b * (β + ε) := by
          gcongr
        exact add_lt_add_of_lt_of_le hαmul hβmul
    have hsumlt'' : a * (α + ε) + b * (β + ε) < γ := by
      calc
        a * (α + ε) + b * (β + ε) = (a * α + b * β) + ε := by
          nlinarith [hab]
        _ < γ := by
          dsimp [ε]
          nlinarith [hγ₁']
    exact lt_trans hsumlt' hsumlt''
  have hltγ : positiveHullFunction f (a • x + b • y) < (γ : EReal) := by
    exact lt_of_le_of_lt hbound (by exact_mod_cast hsumlt)
  exact not_lt_of_ge (le_of_lt hγ₂) hltγ

/-- If the original function is nonnegative, every real height appearing in the
positive hull of its epigraph is nonnegative as well. -/
theorem nonneg_of_mem_positiveHull_epigraph_of_nonneg {f : E → EReal}
    (hf : ∀ x, 0 ≤ f x) {x : E} {a : ℝ}
    (ha : (x, a) ∈ positiveHull (epigraph f)) :
    0 ≤ a := by
  rcases ha with hzero | ⟨c, hc, p, hp, hpEq⟩
  · have : a = 0 := by
      simpa using congrArg Prod.snd hzero
    simp [this]
  · rcases p with ⟨y, b⟩
    rw [mem_epigraph_iff] at hp
    have hab : a = c * b := by
      simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.snd hpEq
    have hb_nonneg : 0 ≤ b := by
      have : (0 : EReal) ≤ (b : EReal) := le_trans (hf y) hp
      exact_mod_cast this
    simp [hab, mul_nonneg hc.le hb_nonneg]

/-- Positive hulls of nonnegative functions remain nonnegative. -/
theorem nonneg_positiveHullFunction_of_nonneg {f : E → EReal}
    (hf : ∀ x, 0 ≤ f x) (x : E) :
    0 ≤ positiveHullFunction f x := by
  refine le_iInf ?_
  intro a
  exact_mod_cast nonneg_of_mem_positiveHull_epigraph_of_nonneg hf a.property

/-- The function on `ℝ × E` supported on the slice `λ = 1`. Its positive hull
is the perspective-style homogenization from Exercise `3.49(c)`. -/
noncomputable def unitSliceFunction (f : E → EReal) : ℝ × E → EReal
  := fun p => if p.1 = 1 then f p.2 else ⊤

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_epigraph_unitSliceFunction_iff {f : E → EReal} {lam : ℝ} {x : E} {a : ℝ} :
    ((lam, x), a) ∈ epigraph (unitSliceFunction f) ↔ lam = 1 ∧ f x ≤ (a : EReal) := by
  by_cases hlam : lam = 1
  · simp [unitSliceFunction, hlam, mem_epigraph_iff]
  · simp [unitSliceFunction, hlam, mem_epigraph_iff]

/-- The epigraph of the unit-slice function is convex whenever the original
epigraph is convex. -/
theorem convex_epigraph_unitSliceFunction {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) :
    Convex ℝ (epigraph (unitSliceFunction f)) := by
  intro p hp q hq a b ha hb hab
  rcases p with ⟨⟨lam, x⟩, α⟩
  rcases q with ⟨⟨mu, y⟩, β⟩
  rw [mem_epigraph_unitSliceFunction_iff] at hp hq ⊢
  rcases hp with ⟨hlam, hx⟩
  rcases hq with ⟨hmu, hy⟩
  have hxepi : (x, α) ∈ epigraph f := by
    simpa [mem_epigraph_iff] using hx
  have hyepi : (y, β) ∈ epigraph f := by
    simpa [mem_epigraph_iff] using hy
  have hmem := hconv hxepi hyepi ha hb hab
  refine ⟨by simp [hlam, hmu, hab], ?_⟩
  simpa [mem_epigraph_iff, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hmem

/-- The explicit perspective-style function from Exercise `3.49(c)`. -/
noncomputable def perspectiveFunction (f : E → EReal) : ℝ × E → EReal
  := by
    classical
    exact fun p =>
      if hlam : 0 < p.1 then
        (p.1 : EReal) * f (p.1⁻¹ • p.2)
      else if p.1 = 0 then
        if p.2 = 0 then 0 else ⊤
      else
        ⊤

theorem positiveHullFunction_unitSliceFunction_pos {f : E → EReal}
    (hbot : ∀ x, f x > ⊥) {lam : ℝ} {x : E} (hlam : 0 < lam) :
    positiveHullFunction (unitSliceFunction f) (lam, x) =
      (lam : EReal) * f (lam⁻¹ • x) := by
  let v : E := lam⁻¹ • x
  have hvbot : f v ≠ ⊥ := ne_of_gt (hbot v)
  by_cases hvtop : f v = ⊤
  · have hA : IsEmpty {a : ℝ // ((lam, x), a) ∈ positiveHull (epigraph (unitSliceFunction f))} := by
      refine ⟨?_⟩
      intro a
      rcases a.property with hzero | ⟨c, hc, y, hy, hyEq⟩
      · have : lam = 0 := by
          simpa using congrArg (fun p : (ℝ × E) × ℝ => p.1.1) hzero
        exact hlam.ne' this
      · rcases y with ⟨⟨μ, u⟩, b⟩
        rw [mem_epigraph_unitSliceFunction_iff] at hy
        rcases hy with ⟨hμ, hub⟩
        subst hμ
        have hlamc : lam = c := by
          simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun p : (ℝ × E) × ℝ => p.1.1) hyEq
        have hxu : x = c • u := by
          simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun p : (ℝ × E) × ℝ => p.1.2) hyEq
        have hvu : v = u := by
          calc
            v = lam⁻¹ • x := by rfl
            _ = lam⁻¹ • (c • u) := by rw [hxu]
            _ = (lam⁻¹ * c) • u := by rw [smul_smul]
            _ = (c⁻¹ * c) • u := by rw [hlamc]
            _ = (1 : ℝ) • u := by rw [inv_mul_cancel₀ hc.ne']
            _ = u := by simp
        have hfvb : f v ≤ (b : EReal) := by simpa [hvu] using hub
        have htopb : (⊤ : EReal) ≤ (b : EReal) := by
          rw [hvtop] at hfvb
          exact hfvb
        simp at htopb
    letI : IsEmpty {a : ℝ // ((lam, x), a) ∈ positiveHull (epigraph (unitSliceFunction f))} := hA
    rw [positiveHullFunction]
    simp [v, hvtop, EReal.coe_mul_top_of_pos hlam, iInf_of_empty]
  · apply le_antisymm
    · let r : ℝ := (f v).toReal
      have hr : ((r : ℝ) : EReal) = f v := EReal.coe_toReal hvtop hvbot
      have hmem_epi : (((1 : ℝ), v), r) ∈ epigraph (unitSliceFunction f) := by
        rw [mem_epigraph_unitSliceFunction_iff]
        refine ⟨rfl, ?_⟩
        simpa [r] using le_of_eq hr.symm
      have hmem_pos :
          (((lam, x), lam * r) : (ℝ × E) × ℝ) ∈ positiveHull (epigraph (unitSliceFunction f)) := by
        right
        refine ⟨lam, hlam, ((1, v), r), hmem_epi, ?_⟩
        simp [v, Prod.smul_mk, smul_smul, mul_inv_cancel₀ hlam.ne', smul_eq_mul]
      calc
        positiveHullFunction (unitSliceFunction f) (lam, x)
            ≤ (((lam * r : ℝ) : EReal)) :=
              positiveHullFunction_le_of_mem_positiveHull_epigraph hmem_pos
        _ = (lam : EReal) * f v := by
              calc
                (((lam * r : ℝ) : EReal)) = (lam : EReal) * (r : EReal) := by
                  rw [EReal.coe_mul]
                _ = (lam : EReal) * f v := by rw [hr]
    · refine le_iInf ?_
      intro a
      rcases a.property with hzero | ⟨c, hc, y, hy, hyEq⟩
      · have : lam = 0 := by
          simpa using congrArg (fun p : (ℝ × E) × ℝ => p.1.1) hzero
        exact (hlam.ne' this).elim
      · rcases y with ⟨⟨μ, u⟩, b⟩
        rw [mem_epigraph_unitSliceFunction_iff] at hy
        rcases hy with ⟨hμ, hub⟩
        subst hμ
        have hlamc : lam = c := by
          simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun p : (ℝ × E) × ℝ => p.1.1) hyEq
        have hxu : x = c • u := by
          simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun p : (ℝ × E) × ℝ => p.1.2) hyEq
        have hab : (a : ℝ) = c * b := by
          simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.snd hyEq
        have hvu : v = u := by
          calc
            v = lam⁻¹ • x := by rfl
            _ = lam⁻¹ • (c • u) := by rw [hxu]
            _ = (lam⁻¹ * c) • u := by rw [smul_smul]
            _ = (c⁻¹ * c) • u := by rw [hlamc]
            _ = (1 : ℝ) • u := by rw [inv_mul_cancel₀ hc.ne']
            _ = u := by simp
        calc
          (lam : EReal) * f v ≤ (lam : EReal) * (b : EReal) := by
            rw [hvu]
            gcongr
          _ = (((c * b : ℝ) : EReal)) := by rw [hlamc, EReal.coe_mul]
          _ = (a : EReal) := by
            exact_mod_cast hab.symm

theorem positiveHullFunction_unitSliceFunction_zero_zero {f : E → EReal} :
    positiveHullFunction (unitSliceFunction f) ((0 : ℝ), (0 : E)) = 0 := by
  have hle :
      positiveHullFunction (unitSliceFunction f) ((0 : ℝ), (0 : E)) ≤ 0 :=
    positiveHullFunction_le_of_mem_positiveHull_epigraph (zero_mem_positiveHull _)
  have hge : (0 : EReal) ≤ positiveHullFunction (unitSliceFunction f) ((0 : ℝ), (0 : E)) := by
    refine le_iInf ?_
    intro a
    rcases a.property with hzero | ⟨c, hc, y, hy, hyEq⟩
    · have : (a : ℝ) = 0 := by
        simpa using congrArg Prod.snd hzero
      simp [this]
    · rcases y with ⟨⟨μ, u⟩, b⟩
      rw [mem_epigraph_unitSliceFunction_iff] at hy
      rcases hy with ⟨hμ, _⟩
      subst hμ
      have h0c : (0 : ℝ) = c := by
        simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun p : (ℝ × E) × ℝ => p.1.1) hyEq
      exact (hc.ne' h0c.symm).elim
  exact le_antisymm hle hge

theorem positiveHullFunction_unitSliceFunction_zero_nonzero {f : E → EReal} {x : E}
    (hx : x ≠ 0) :
    positiveHullFunction (unitSliceFunction f) ((0 : ℝ), x) = ⊤ := by
  have hA :
      IsEmpty {a : ℝ // (((0 : ℝ), x), a) ∈ positiveHull (epigraph (unitSliceFunction f))} := by
    refine ⟨?_⟩
    intro a
    rcases a.property with hzero | ⟨c, hc, y, hy, hyEq⟩
    · have : x = 0 := by
        simpa using congrArg (fun p : (ℝ × E) × ℝ => p.1.2) hzero
      exact hx this
    · rcases y with ⟨⟨μ, u⟩, b⟩
      rw [mem_epigraph_unitSliceFunction_iff] at hy
      rcases hy with ⟨hμ, _⟩
      subst hμ
      have h0c : (0 : ℝ) = c := by
        simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun p : (ℝ × E) × ℝ => p.1.1) hyEq
      exact (hc.ne' h0c.symm).elim
  letI : IsEmpty {a : ℝ // (((0 : ℝ), x), a) ∈ positiveHull (epigraph (unitSliceFunction f))} := hA
  rw [positiveHullFunction, iInf_of_empty]

theorem positiveHullFunction_unitSliceFunction_neg {f : E → EReal} {lam : ℝ} {x : E}
    (hlam : lam < 0) :
    positiveHullFunction (unitSliceFunction f) (lam, x) = ⊤ := by
  have hA : IsEmpty {a : ℝ // ((lam, x), a) ∈ positiveHull (epigraph (unitSliceFunction f))} := by
    refine ⟨?_⟩
    intro a
    rcases a.property with hzero | ⟨c, hc, y, hy, hyEq⟩
    · have : lam = 0 := by
        simpa using congrArg (fun p : (ℝ × E) × ℝ => p.1.1) hzero
      exact (ne_of_lt hlam) this
    · rcases y with ⟨⟨μ, u⟩, b⟩
      rw [mem_epigraph_unitSliceFunction_iff] at hy
      rcases hy with ⟨hμ, _⟩
      subst hμ
      have : lam = c := by
        simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun p : (ℝ × E) × ℝ => p.1.1) hyEq
      exact (not_lt_of_gt hc) <| by simpa [this] using hlam
  letI : IsEmpty {a : ℝ // ((lam, x), a) ∈ positiveHull (epigraph (unitSliceFunction f))} := hA
  rw [positiveHullFunction, iInf_of_empty]

/-- Formula `3.49(c)` as an equality with the positive hull of the unit slice. -/
theorem positiveHullFunction_unitSliceFunction_eq_perspectiveFunction {f : E → EReal}
    (hproper : IsProper f) :
    positiveHullFunction (unitSliceFunction f) = perspectiveFunction f := by
  funext p
  rcases p with ⟨lam, x⟩
  by_cases hlam : 0 < lam
  · simp [perspectiveFunction, hlam,
      positiveHullFunction_unitSliceFunction_pos hproper.2 hlam]
  · by_cases h0 : lam = 0
    · subst h0
      by_cases hx : x = 0
      · subst hx
        rw [positiveHullFunction_unitSliceFunction_zero_zero]
        simp [perspectiveFunction]
      · rw [positiveHullFunction_unitSliceFunction_zero_nonzero hx]
        simp [perspectiveFunction, hx]
    · have hneg : lam < 0 := lt_of_le_of_ne (le_of_not_gt hlam) h0
      rw [positiveHullFunction_unitSliceFunction_neg hneg]
      simp [perspectiveFunction, hlam, h0]

/-- The perspective function is positively homogeneous in `(λ, x)`. -/
theorem positivelyHomogeneous_perspectiveFunction {f : E → EReal} (hproper : IsProper f) :
    PositivelyHomogeneous (perspectiveFunction f) := by
  simpa [positiveHullFunction_unitSliceFunction_eq_perspectiveFunction hproper] using
    positivelyHomogeneous_positiveHullFunction (f := unitSliceFunction f)

/-- In the proper convex case, the perspective function has convex epigraph. -/
theorem convex_epigraph_perspectiveFunction {f : E → EReal} (hproper : IsProper f)
    (hconv : Convex ℝ (epigraph f)) :
    Convex ℝ (epigraph (perspectiveFunction f)) := by
  simpa [positiveHullFunction_unitSliceFunction_eq_perspectiveFunction hproper] using
    convex_epigraph_positiveHullFunction (f := unitSliceFunction f)
      (convex_epigraph_unitSliceFunction hconv)

/-- The epigraph of `δ_C + 1` is the vertical cylinder over `C` starting at
height `1`. -/
theorem epigraph_indicatorVA_add_one (C : Set E) :
    epigraph (fun x => indicatorVA C x + 1) = C ×ˢ Set.Ici (1 : ℝ) := by
  ext p
  rcases p with ⟨x, a⟩
  by_cases hx : x ∈ C
  · constructor
    · intro h
      have h' : (1 : EReal) ≤ (a : EReal) := by
        simpa [mem_epigraph_iff, indicatorVA_apply_mem hx] using h
      refine ⟨hx, ?_⟩
      change (1 : ℝ) ≤ a
      exact_mod_cast h'
    · rintro ⟨_, ha⟩
      have ha' : (1 : EReal) ≤ (a : EReal) := by
        exact_mod_cast ha
      simpa [mem_epigraph_iff, indicatorVA_apply_mem hx] using ha'
  · constructor
    · intro h
      rw [mem_epigraph_iff, indicatorVA_apply_not_mem hx] at h
      have htop : (⊤ : EReal) + 1 = (⊤ : EReal) := EReal.top_add_coe 1
      have : (⊤ : EReal) ≤ (a : EReal) := by
        rw [← htop]
        exact h
      simp at this
    · rintro ⟨hx', _⟩
      exact (hx hx').elim

/-- `δ_C + 1` is pointwise nonnegative. -/
theorem nonneg_indicatorVA_add_one (C : Set E) (x : E) :
    0 ≤ indicatorVA C x + 1 := by
  by_cases hx : x ∈ C
  · rw [indicatorVA_apply_mem hx]
    norm_num
  · rw [indicatorVA_apply_not_mem hx]
    have htop : (⊤ : EReal) + 1 = (⊤ : EReal) := EReal.top_add_coe 1
    rw [htop]
    exact le_top

/-- **Example 3.50**: the gauge associated with a set, expressed as a positive
hull. -/
noncomputable def gaugeFunction (C : Set E) : E → EReal :=
  positiveHullFunction (fun x => indicatorVA C x + 1)

/-- Gauge functions are positively homogeneous. -/
theorem positivelyHomogeneous_gaugeFunction (C : Set E) :
    PositivelyHomogeneous (gaugeFunction C) := by
  simpa [gaugeFunction] using
    positivelyHomogeneous_positiveHullFunction (f := fun x => indicatorVA C x + 1)

/-- Gauge functions are nonnegative. -/
theorem nonneg_gaugeFunction (C : Set E) (x : E) :
    0 ≤ gaugeFunction C x := by
  simpa [gaugeFunction] using
    nonneg_positiveHullFunction_of_nonneg
      (f := fun x => indicatorVA C x + 1)
      (nonneg_indicatorVA_add_one C)
      x

@[simp] theorem gaugeFunction_zero (C : Set E) :
    gaugeFunction C 0 = 0 := by
  have hle : gaugeFunction C 0 ≤ 0 := by
    simpa [gaugeFunction] using
      (positiveHullFunction_le_of_mem_positiveHull_epigraph
        (f := fun x => indicatorVA C x + 1)
        (x := 0) (a := 0)
        (zero_mem_positiveHull (epigraph (fun x => indicatorVA C x + 1))))
  exact le_antisymm hle (nonneg_gaugeFunction C 0)

/-- Negating the first coordinate preserves membership in the positive hull of
`epi (δ_C + 1)` when `C` is symmetric. -/
theorem mem_positiveHull_epigraph_indicatorVA_add_one_neg_iff
    {C : Set E} (hneg : ∀ ⦃x : E⦄, x ∈ C → -x ∈ C)
    {x : E} {a : ℝ} :
    ((-x), a) ∈ positiveHull (epigraph (fun x => indicatorVA C x + 1)) ↔
      (x, a) ∈ positiveHull (epigraph (fun x => indicatorVA C x + 1)) := by
  constructor <;> intro ha
  · rcases ha with hzero | ⟨c, hc, p, hp, hpEq⟩
    · have hx0 : x = 0 := by
        simpa using congrArg Prod.fst hzero
      have ha0 : a = 0 := by
        simpa using congrArg Prod.snd hzero
      left
      simpa [hx0, ha0]
    · rcases p with ⟨y, b⟩
      rw [epigraph_indicatorVA_add_one] at hp ⊢
      rcases hp with ⟨hy, hb⟩
      right
      refine ⟨c, hc, (-y, b), ?_, ?_⟩
      · exact ⟨hneg hy, hb⟩
      · ext
        · have hx : -x = c • y := by
            simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.fst hpEq
          calc
            x = -(-x) := by simp
            _ = -(c • y) := by rw [hx]
            _ = c • (-y) := by simp
        · simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.snd hpEq
  · rcases ha with hzero | ⟨c, hc, p, hp, hpEq⟩
    · have hx0 : x = 0 := by
        simpa using congrArg Prod.fst hzero
      have ha0 : a = 0 := by
        simpa using congrArg Prod.snd hzero
      left
      simpa [hx0, ha0]
    · rcases p with ⟨y, b⟩
      rw [epigraph_indicatorVA_add_one] at hp ⊢
      rcases hp with ⟨hy, hb⟩
      right
      refine ⟨c, hc, (-y, b), ?_, ?_⟩
      · exact ⟨hneg hy, hb⟩
      · ext
        · have hx : x = c • y := by
            simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.fst hpEq
          calc
            -x = -(c • y) := by rw [hx]
            _ = c • (-y) := by simp
        · simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.snd hpEq

/-- Symmetry of `C` corresponds to evenness of its gauge. -/
theorem gaugeFunction_neg_eq_of_symmetric {C : Set E}
    (hneg : ∀ ⦃x : E⦄, x ∈ C → -x ∈ C) (x : E) :
    gaugeFunction C (-x) = gaugeFunction C x := by
  apply le_antisymm
  · refine le_iInf ?_
    intro a
    exact positiveHullFunction_le_of_mem_positiveHull_epigraph <|
      (mem_positiveHull_epigraph_indicatorVA_add_one_neg_iff hneg).2 a.property
  · refine le_iInf ?_
    intro a
    exact positiveHullFunction_le_of_mem_positiveHull_epigraph <|
      (mem_positiveHull_epigraph_indicatorVA_add_one_neg_iff hneg).1 a.property

/-- Every point of the positive hull of the gauge epigraph projects to a point
of the positive hull of the underlying set. -/
theorem mem_positiveHull_of_mem_positiveHull_epigraph_indicatorVA_add_one
    {C : Set E} {x : E} {a : ℝ}
    (ha : (x, a) ∈ positiveHull (epigraph (fun x => indicatorVA C x + 1))) :
    x ∈ positiveHull C := by
  rcases ha with hzero | ⟨c, hc, p, hp, hpEq⟩
  · have : x = 0 := by
      simpa using congrArg Prod.fst hzero
    simpa [this] using zero_mem_positiveHull C
  · rcases p with ⟨y, b⟩
    rw [epigraph_indicatorVA_add_one] at hp
    rcases hp with ⟨hy, _⟩
    right
    refine ⟨c, hc, y, hy, ?_⟩
    simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.fst hpEq

/-- The positive hull of `C` is contained in the effective domain of its gauge. -/
theorem positiveHull_subset_effectiveDomain_gaugeFunction (C : Set E) :
    positiveHull C ⊆ effectiveDomain (gaugeFunction C) := by
  intro x hx
  rw [mem_effectiveDomain_iff]
  rcases hx with rfl | ⟨c, hc, y, hy, rfl⟩
  · have hle : gaugeFunction C 0 ≤ 0 := by
      simpa [gaugeFunction] using
        (positiveHullFunction_le_of_mem_positiveHull_epigraph
          (f := fun x => indicatorVA C x + 1)
          (x := 0) (a := 0)
          (zero_mem_positiveHull (epigraph (fun x => indicatorVA C x + 1))))
    exact lt_of_le_of_lt hle (by simp)
  · have hyepi : (y, (1 : ℝ)) ∈ epigraph (fun x => indicatorVA C x + 1) := by
      rw [epigraph_indicatorVA_add_one]
      exact ⟨hy, by simp⟩
    have hmem :
        (c • y, c) ∈ positiveHull (epigraph (fun x => indicatorVA C x + 1)) := by
      right
      refine ⟨c, hc, (y, 1), hyepi, ?_⟩
      simp [Prod.smul_mk, smul_eq_mul]
    have hle : gaugeFunction C (c • y) ≤ (c : EReal) := by
      simpa [gaugeFunction] using
        (positiveHullFunction_le_of_mem_positiveHull_epigraph
          (f := fun x => indicatorVA C x + 1) hmem)
    exact lt_of_le_of_lt hle (EReal.coe_lt_top c)

/-- The gauge is finite exactly on the positive hull of the set. -/
theorem effectiveDomain_gaugeFunction (C : Set E) :
    effectiveDomain (gaugeFunction C) = positiveHull C := by
  ext x
  constructor
  · intro hx
    rw [mem_effectiveDomain_iff] at hx
    obtain ⟨a, hga, _⟩ := EReal.exists_between_coe_real hx
    obtain ⟨b, hbmem, _⟩ :=
      exists_mem_positiveHull_epigraph_lt
        (f := fun x => indicatorVA C x + 1) (x := x) hga
    exact mem_positiveHull_of_mem_positiveHull_epigraph_indicatorVA_add_one hbmem
  · intro hx
    exact positiveHull_subset_effectiveDomain_gaugeFunction C hx

/-- Points of `C` lie in the unit sublevel set of the gauge. -/
theorem gaugeFunction_le_one_of_mem {C : Set E} {x : E} (hx : x ∈ C) :
    gaugeFunction C x ≤ 1 := by
  have hmem : (x, (1 : ℝ)) ∈ positiveHull (epigraph (fun x => indicatorVA C x + 1)) := by
    exact subset_positiveHull <| by
      rw [epigraph_indicatorVA_add_one]
      exact ⟨hx, by simp⟩
  simpa [gaugeFunction] using
    (positiveHullFunction_le_of_mem_positiveHull_epigraph
      (f := fun x => indicatorVA C x + 1) hmem)

/-- Gauge functions inherit convex epigraphs from convex sets. -/
theorem convex_epigraph_gaugeFunction {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (epigraph (gaugeFunction C)) := by
  have hconv :
      Convex ℝ (epigraph (fun x => indicatorVA C x + 1)) := by
    simpa [epigraph_indicatorVA_add_one] using hC.prod (convex_Ici (1 : ℝ))
  simpa [gaugeFunction] using
    convex_epigraph_positiveHullFunction
      (f := fun x => indicatorVA C x + 1) hconv

/-- The gauge of a convex set is sublinear. -/
theorem sublinear_gaugeFunction {C : Set E} (hC : Convex ℝ C) :
    Sublinear (gaugeFunction C) := by
  exact sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_nonneg
    (positivelyHomogeneous_gaugeFunction C)
    (convex_epigraph_gaugeFunction hC)
    (nonneg_gaugeFunction C)

/-- If `C` is convex and contains `0`, then its positive scalings are nested. -/
theorem smul_set_mono_of_nonneg_le {C : Set E} (hC : Convex ℝ C) (h0 : (0 : E) ∈ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a • C ⊆ b • C := by
  intro x hx
  rcases hab.eq_or_lt with rfl | hb'
  · simpa using hx
  rcases ha.eq_or_lt with rfl | ha'
  · have hx0 : x = 0 := by
      simpa using zero_smul_set_subset C hx
    subst hx0
    simpa using (Set.smul_mem_smul_set (a := b) h0)
  · have hb : 0 < b := lt_of_le_of_lt ha hb'
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hb.ne']
    have hx' : a⁻¹ • x ∈ C := by
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha'.ne'] at hx
      exact hx
    have hmem : (a / b) • (a⁻¹ • x) ∈ C := by
      refine hC.smul_mem_of_zero_mem h0 hx' ⟨by positivity, ?_⟩
      rw [div_eq_mul_inv, mul_comm, inv_mul_le_iff₀ hb, mul_one]
      exact hab
    have hcalc : b⁻¹ • x = (a / b) • (a⁻¹ • x) := by
      calc
        b⁻¹ • x = b⁻¹ • (a • (a⁻¹ • x)) := by rw [smul_inv_smul₀ ha'.ne']
        _ = (b⁻¹ * a) • (a⁻¹ • x) := by rw [smul_smul]
        _ = (a / b) • (a⁻¹ • x) := by rw [div_eq_mul_inv, mul_comm]
    simpa [hcalc] using hmem

/-- A point of the positive hull of `epi (δ_C + 1)` at height `a` lies in the
scaled set `a • C` whenever `C` is convex and contains `0`. -/
theorem mem_smul_of_mem_positiveHull_epigraph_indicatorVA_add_one
    {C : Set E} (hC : Convex ℝ C) (h0 : (0 : E) ∈ C)
    {x : E} {a : ℝ}
    (hx : (x, a) ∈ positiveHull (epigraph (fun x => indicatorVA C x + 1))) :
    x ∈ a • C := by
  rcases hx with hzero | ⟨c, hc, p, hp, hpEq⟩
  · have hx0 : x = 0 := by
      simpa using congrArg Prod.fst hzero
    subst hx0
    simpa using (Set.smul_mem_smul_set (a := a) h0)
  · rcases p with ⟨y, b⟩
    rw [epigraph_indicatorVA_add_one] at hp
    rcases hp with ⟨hy, hb⟩
    have hxa : x = c • y := by
      simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.fst hpEq
    have haa : a = c * b := by
      simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.snd hpEq
    have hb1 : 1 ≤ b := hb
    have hca : c ≤ a := by
      rw [haa]
      nlinarith [hc, hb1]
    exact smul_set_mono_of_nonneg_le hC h0 hc.le hca <| by
      rw [hxa]
      exact Set.smul_mem_smul_set hy

/-- Membership in a scaled set gives the corresponding upper bound on the
gauge. -/
theorem gaugeFunction_le_of_mem_smul {C : Set E} {a : ℝ} (ha : 0 ≤ a) {x : E}
    (hx : x ∈ a • C) :
    gaugeFunction C x ≤ a := by
  rcases ha.eq_or_lt with rfl | ha'
  · have hx0 : x = 0 := by
      simpa using zero_smul_set_subset C hx
    subst hx0
    have hle : gaugeFunction C 0 ≤ 0 := by
      simpa [gaugeFunction] using
        (positiveHullFunction_le_of_mem_positiveHull_epigraph
          (f := fun x => indicatorVA C x + 1)
          (x := 0) (a := 0)
          (zero_mem_positiveHull (epigraph (fun x => indicatorVA C x + 1))))
    simpa using hle
  · have hx' : a⁻¹ • x ∈ C := by
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha'.ne'] at hx
      exact hx
    have hunit : gaugeFunction C (a⁻¹ • x) ≤ 1 := gaugeFunction_le_one_of_mem hx'
    calc
      gaugeFunction C x
          = gaugeFunction C (a • (a⁻¹ • x)) := by rw [smul_inv_smul₀ ha'.ne']
      _ = (a : EReal) * gaugeFunction C (a⁻¹ • x) := by
            simpa using
              (positivelyHomogeneous_gaugeFunction C).2 (x := a⁻¹ • x) (c := a) ha'
      _ ≤ (a : EReal) * 1 := by gcongr
      _ = a := by simp

/-- The gauge sublevel set at height `a ≥ 0` is the intersection of all scaled
copies `r • C` with `r > a`. -/
theorem levelSet_gaugeFunction_eq_iInter_smul {C : Set E}
    (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) {a : ℝ} (ha : 0 ≤ a) :
    levelSet (gaugeFunction C) a = ⋂ (r : ℝ) (_ : a < r), r • C := by
  ext x
  simp only [levelSet, mem_iInter, mem_setOf_eq]
  constructor
  · intro hx r hr
    have hlt : gaugeFunction C x < (r : EReal) := lt_of_le_of_lt hx (by exact_mod_cast hr)
    obtain ⟨b, hbmem, hbr⟩ :=
      exists_mem_positiveHull_epigraph_lt
        (f := fun x => indicatorVA C x + 1) (x := x) hlt
    have hb_nonneg : 0 ≤ b := by
      exact nonneg_of_mem_positiveHull_epigraph_of_nonneg (nonneg_indicatorVA_add_one C) hbmem
    have hxb : x ∈ b • C :=
      mem_smul_of_mem_positiveHull_epigraph_indicatorVA_add_one hC h0 hbmem
    have hbr' : b < r := by
      exact_mod_cast hbr
    exact smul_set_mono_of_nonneg_le hC h0 hb_nonneg hbr'.le hxb
  · intro hx
    have htop : gaugeFunction C x ≠ ⊤ := by
      have hx1 : x ∈ (a + 1) • C := hx (a + 1) (by linarith)
      exact ne_of_lt <| lt_of_le_of_lt
        (gaugeFunction_le_of_mem_smul (by linarith) hx1) (EReal.coe_lt_top (a + 1))
    have hbot : gaugeFunction C x ≠ ⊥ := by
      intro hbot
      simpa [hbot] using nonneg_gaugeFunction C x
    have hreal : (gaugeFunction C x).toReal ≤ a := by
      apply le_of_forall_pos_lt_add
      intro ε hε
      have hxε : x ∈ (a + ε / 2) • C := hx (a + ε / 2) (by linarith)
      have hle : gaugeFunction C x ≤ (a + ε / 2 : ℝ) :=
        gaugeFunction_le_of_mem_smul (by linarith) hxε
      have hle' : (gaugeFunction C x).toReal ≤ a + ε / 2 := by
        rw [← EReal.coe_toReal htop hbot] at hle
        exact_mod_cast hle
      linarith
    have hrealE : (((gaugeFunction C x).toReal : ℝ) : EReal) ≤ (a : EReal) := by
      exact_mod_cast hreal
    simpa [EReal.coe_toReal htop hbot] using hrealE

/-- For a closed convex set containing `0`, positive gauge sublevel sets are
exactly the corresponding scaled copies of the set. -/
theorem levelSet_gaugeFunction_eq_smul {C : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (h0 : (0 : E) ∈ C)
    {a : ℝ} (ha : 0 < a) :
    levelSet (gaugeFunction C) a = a • C := by
  rw [levelSet_gaugeFunction_eq_iInter_smul hC h0 ha.le]
  apply Subset.antisymm
  · intro x hx
    simp only [mem_iInter] at hx
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
    have hxn : ∀ n : ℕ, ((a + 1 / (n + 1 : ℝ))⁻¹) • x ∈ C := by
      intro n
      let r : ℝ := a + 1 / (n + 1 : ℝ)
      have hr : a < r := by
        dsimp [r]
        have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        linarith
      have hr0 : 0 < r := lt_of_le_of_lt ha.le hr
      have hxmem : x ∈ r • C := hx r hr
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr0.ne'] at hxmem
      exact hxmem
    have hsum :
        Filter.Tendsto (fun n : ℕ => (a + 1 / (n + 1 : ℝ))) Filter.atTop (nhds a) := by
      simpa using
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hinv :
        Filter.Tendsto (fun n : ℕ => ((a + 1 / (n + 1 : ℝ))⁻¹ : ℝ)) Filter.atTop (nhds a⁻¹) := by
      exact (continuousAt_inv₀ ha.ne').tendsto.comp hsum
    have hsmul :
        Filter.Tendsto (fun n : ℕ => ((a + 1 / (n + 1 : ℝ))⁻¹ • x)) Filter.atTop
          (nhds (a⁻¹ • x)) := by
      exact (((continuous_id.smul continuous_const).continuousAt : ContinuousAt
        (fun r : ℝ => r • x) a⁻¹).tendsto).comp hinv
    exact hC_closed.mem_of_tendsto hsmul (Filter.Eventually.of_forall hxn)
  · intro x hx
    simp only [mem_iInter]
    intro r hr
    exact smul_set_mono_of_nonneg_le hC h0 ha.le hr.le hx

/-- In particular, the unit sublevel set of the gauge is the original closed
convex set containing `0`. -/
theorem levelSet_gaugeFunction_one {C : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (h0 : (0 : E) ∈ C) :
    levelSet (gaugeFunction C) 1 = C := by
  simpa using levelSet_gaugeFunction_eq_smul hC hC_closed h0 (a := 1) zero_lt_one

/-- The zero sublevel set of the gauge is the horizon cone. This is the
project's form of `lev≤0 γ_C = C^∞`. -/
theorem levelSet_gaugeFunction_zero {C : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (h0 : (0 : E) ∈ C) :
    levelSet (gaugeFunction C) (0 : ℝ) = horizonCone C := by
  rw [levelSet_gaugeFunction_eq_iInter_smul hC h0 (a := (0 : ℝ)) le_rfl]
  apply Subset.antisymm
  · intro x hx
    simp only [mem_iInter] at hx
    refine mem_horizonCone_of_forall_smul_add_mem (C := C) (x := 0) (w := x) ?_
    intro τ hτ
    rcases eq_or_lt_of_le hτ with rfl | hτpos
    · simpa using h0
    · have hxmem : x ∈ τ⁻¹ • C := hx τ⁻¹ (inv_pos.mpr hτpos)
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hτpos.ne')] at hxmem
      simpa using hxmem
  · intro x hx
    simp only [mem_iInter]
    intro r hr
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
    simpa using
      smul_add_mem_of_mem_horizonCone (C := C) hC hC_closed h0 hx
        (show 0 ≤ r⁻¹ by positivity)

/-- In the finite-dimensional bounded case, the zero sublevel set of the gauge
collapses to `{0}`. -/
theorem levelSet_gaugeFunction_zero_eq_singleton_zero_of_isBounded
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (h0 : (0 : E) ∈ C)
    (hCbdd : Bornology.IsBounded C) :
    levelSet (gaugeFunction C) (0 : ℝ) = ({0} : Set E) := by
  rw [levelSet_gaugeFunction_zero hC hC_closed h0]
  exact (isBounded_iff_horizonCone_eq_singleton_zero (C := C)).mp hCbdd

/-- In the finite-dimensional bounded case, the gauge vanishes only at `0`. -/
theorem gaugeFunction_eq_zero_iff_of_isBounded
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (h0 : (0 : E) ∈ C)
    (hCbdd : Bornology.IsBounded C) {x : E} :
    gaugeFunction C x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hxlevel : x ∈ levelSet (gaugeFunction C) (0 : ℝ) := by
      simpa [levelSet, hx]
    rw [levelSet_gaugeFunction_zero_eq_singleton_zero_of_isBounded hC hC_closed h0 hCbdd] at hxlevel
    simpa using hxlevel
  · intro hx
    simpa [hx] using gaugeFunction_zero C

/-- Finiteness of the gauge everywhere is equivalent to `positiveHull C = univ`.
This is the project form of the `dom γ_C = pos C` statement. -/
theorem effectiveDomain_gaugeFunction_eq_univ_iff (C : Set E) :
    effectiveDomain (gaugeFunction C) = Set.univ ↔ positiveHull C = Set.univ := by
  rw [effectiveDomain_gaugeFunction]

/-- If `0` lies in the interior of `C`, then `positiveHull C` is all of `E`. -/
theorem positiveHull_eq_univ_of_mem_interior_zero {C : Set E}
    (h0int : (0 : E) ∈ interior C) :
    positiveHull C = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hAbs : Absorbent ℝ C := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0int)
    rcases (hAbs x).exists_pos with ⟨r, hr, hrC⟩
    have hxmem : x ∈ r • C := by
      have hsubset : ({x} : Set E) ⊆ r • C := hrC r (by simpa [Real.norm_of_nonneg hr.le])
      exact hsubset (by simp)
    rcases hxmem with ⟨y, hy, hxy⟩
    right
    exact ⟨r, hr, y, hy, hxy.symm⟩

/-- In particular, `0 ∈ interior C` implies the gauge is finite everywhere. -/
theorem effectiveDomain_gaugeFunction_eq_univ_of_mem_interior_zero {C : Set E}
    (h0int : (0 : E) ∈ interior C) :
    effectiveDomain (gaugeFunction C) = Set.univ := by
  rw [effectiveDomain_gaugeFunction, positiveHull_eq_univ_of_mem_interior_zero h0int]

/-- The gauge of a closed convex set containing `0` is lower semicontinuous. -/
theorem lowerSemicontinuous_gaugeFunction {C : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (h0 : (0 : E) ∈ C) :
    LowerSemicontinuous (gaugeFunction C) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro α
  rcases eq_top_or_lt_top α with rfl | hαtop
  · simp
  by_cases hαbot : α = ⊥
  · have hset : (gaugeFunction C) ⁻¹' Set.Iic α = ∅ := by
      ext x
      constructor
      · intro hx
        have hnonbot : gaugeFunction C x ≠ ⊥ := by
          intro hbot
          simpa [hbot] using nonneg_gaugeFunction C x
        exact False.elim <| hnonbot (le_antisymm (by simpa [hαbot] using hx) bot_le)
      · simp
    simpa [hset] using isClosed_empty
  · have hαreal : ((α.toReal : ℝ) : EReal) = α := EReal.coe_toReal (ne_of_lt hαtop) hαbot
    by_cases ha : 0 < α.toReal
    · have hset : (gaugeFunction C) ⁻¹' Set.Iic α = α.toReal • C := by
        simpa [levelSet, hαreal] using
          levelSet_gaugeFunction_eq_smul hC hC_closed h0 (a := α.toReal) ha
      rw [hset]
      exact hC_closed.smul_of_ne_zero (c := α.toReal) ha.ne'
    · have hαnonpos : α.toReal ≤ 0 := le_of_not_gt ha
      rcases hαnonpos.eq_or_lt with hzero | hneg
      · have hset :
            (gaugeFunction C) ⁻¹' Set.Iic α = ⋂ (r : ℝ) (_ : 0 < r), r • C := by
          have hαzero : α = (0 : EReal) := by
            calc
              α = ((α.toReal : ℝ) : EReal) := hαreal.symm
              _ = 0 := by simpa [hzero]
          simpa [levelSet, hαzero] using
            (levelSet_gaugeFunction_eq_iInter_smul hC h0 (a := 0) le_rfl)
        have hclosed : IsClosed (⋂ (r : ℝ) (_ : 0 < r), r • C) := by
          refine isClosed_iInter ?_
          intro r
          refine isClosed_iInter ?_
          intro hr
          simpa using hC_closed.smul_of_ne_zero (c := r) hr.ne'
        rw [hset]
        exact hclosed
      · have hαneg : α < (0 : EReal) := by
          calc
            α = ((α.toReal : ℝ) : EReal) := hαreal.symm
            _ < 0 := by exact_mod_cast hneg
        have hset : (gaugeFunction C) ⁻¹' Set.Iic α = ∅ := by
          ext x
          constructor
          · intro hx
            have hnonneg : (0 : EReal) ≤ gaugeFunction C x := nonneg_gaugeFunction C x
            exact False.elim <| (not_lt_of_ge (le_trans hnonneg hx)) hαneg
          · simp
        rw [hset]
        exact isClosed_empty

end Functions

end RW
