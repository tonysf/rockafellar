/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1I*: Auxiliary facts and principles

* **Definition 1.33** and **Exercise 1.34**: local lower and upper semicontinuity.
* **Proposition 1.35**: interchange of order of minimization.
* **Exercise 1.36**: max and min of a sum, under inf-addition `∞ - ∞ = ∞`.
* **Exercise 1.37**: scalar multiples versus max and min (corrected: `λ = 0` needs `X ≠ ∅`).
* **Proposition 1.38**: lower limits of sums and scalar multiples.
* **Proposition 1.39**: semicontinuity of sums and scalar multiples.
* **Exercise 1.40**: semicontinuity under composition.
* **Exercise 1.41**: level boundedness of sums and epi-sums.
* **Proposition 1.43**: Ekeland's variational principle.
-/

import RockafellarWets.Chapter1.Attainment
import RockafellarWets.Chapter3.ERealInfimum
import RockafellarWets.Chapter3.EpiAddition
import RockafellarWets.Chapter7.EpigraphAddition
import RockafellarWets.Chapter7.ApproximateMinimizers
import RockafellarWets.Chapter7.SubdifferentialRegularity
import Mathlib.Analysis.Normed.Group.Pointwise
import RockafellarWets.Chapter5.ProximalMappings
import RockafellarWets.Chapter14.MonotoneComposition

open Set Filter Topology Metric Bornology
open scoped Pointwise

noncomputable section

namespace RW

variable {α β E : Type*}

/-! ## Proposition 1.35 -/

section Interchange

/-- **Proposition 1.35**: `inf_{x,u} f(x,u) = inf_u p(u)` for `p(u) = inf_x f(x,u)`. -/
theorem iInf_prod_eq_iInf_valueFunction (f : α × β → EReal) :
    (⨅ q, f q) = ⨅ u, ⨅ x, f (x, u) := by
  rw [iInf_prod, iInf_comm]

/-- **Proposition 1.35**: `inf_{x,u} f(x,u) = inf_x q(x)` for `q(x) = inf_u f(x,u)`. -/
theorem iInf_prod_eq_iInf_iInf (f : α × β → EReal) :
    (⨅ q, f q) = ⨅ x, ⨅ u, f (x, u) :=
  iInf_prod

/-- **Proposition 1.35**: `argmin_{x,u} f = {(x̄, ū) | ū ∈ argmin p, x̄ ∈ argmin_x f(x, ū)}`. -/
theorem argmin_prod_eq_valueFunction (f : α × β → EReal) :
    argmin f = {q | q.2 ∈ argmin (fun u ↦ ⨅ x, f (x, u)) ∧ q.1 ∈ argmin (fun x ↦ f (x, q.2))} := by
  ext ⟨x, u⟩
  simp only [mem_argmin_iff, mem_setOf_eq]
  rw [iInf_prod_eq_iInf_valueFunction]
  constructor
  · rintro ⟨hx, hlt⟩
    have hle : (⨅ y, f (y, u)) ≤ f (x, u) := iInf_le (fun y ↦ f (y, u)) x
    have hge : (⨅ v, ⨅ y, f (y, v)) ≤ ⨅ y, f (y, u) := iInf_le (fun v ↦ ⨅ y, f (y, v)) u
    have hp : (⨅ y, f (y, u)) = ⨅ v, ⨅ y, f (y, v) := le_antisymm (hle.trans hx.le) hge
    exact ⟨⟨hp, hlt⟩, ⟨le_antisymm hle (hx.le.trans hge) |>.symm, hp ▸ hlt⟩⟩
  · rintro ⟨⟨hp, hlt⟩, hx, -⟩
    exact ⟨hx.trans hp, hlt⟩

/-- **Proposition 1.35**: `argmin_{x,u} f = {(x̄, ū) | x̄ ∈ argmin q, ū ∈ argmin_u f(x̄, u)}`. -/
theorem argmin_prod_eq_iInf_snd (f : α × β → EReal) :
    argmin f = {q | q.1 ∈ argmin (fun x ↦ ⨅ u, f (x, u)) ∧ q.2 ∈ argmin (fun u ↦ f (q.1, u))} := by
  ext ⟨x, u⟩
  simp only [mem_argmin_iff, mem_setOf_eq]
  rw [iInf_prod_eq_iInf_iInf]
  constructor
  · rintro ⟨hx, hlt⟩
    have hle : (⨅ v, f (x, v)) ≤ f (x, u) := iInf_le (fun v ↦ f (x, v)) u
    have hge : (⨅ y, ⨅ v, f (y, v)) ≤ ⨅ v, f (x, v) := iInf_le (fun y ↦ ⨅ v, f (y, v)) x
    have hq : (⨅ v, f (x, v)) = ⨅ y, ⨅ v, f (y, v) := le_antisymm (hle.trans hx.le) hge
    exact ⟨⟨hq, hlt⟩, ⟨le_antisymm hle (hx.le.trans hge) |>.symm, hq ▸ hlt⟩⟩
  · rintro ⟨⟨hq, hlt⟩, hx, -⟩
    exact ⟨hx.trans hq, hlt⟩

end Interchange

/-! ## Exercise 1.36 -/

section Sums

theorem infAddition_mono {a a' b b' : EReal} (ha : a ≤ a') (hb : b ≤ b') :
    infAddition a b ≤ infAddition a' b' := by
  by_cases h' : a' = ⊤ ∨ b' = ⊤
  · have : infAddition a' b' = ⊤ := if_pos h'
    rw [this]; exact le_top
  · push_neg at h'
    have h : ¬ (a = ⊤ ∨ b = ⊤) := by
      push_neg
      exact ⟨ne_top_of_le_ne_top h'.1 ha, ne_top_of_le_ne_top h'.2 hb⟩
    rw [infAddition, if_neg h, infAddition, if_neg (by push_neg; exact h')]
    exact add_le_add ha hb

/-- An extended real below every real number above `b` lies below `b`. -/
theorem ereal_le_of_forall_lt_coe {a b : EReal} (h : ∀ c : ℝ, b < c → a ≤ c) : a ≤ b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hbc, hca⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  exact absurd (h c hbc) (not_le.2 hca)

/-- **Exercise 1.36**: `inf_X (f₁ + f₂) ≥ inf_X f₁ + inf_X f₂` under inf-addition. -/
theorem infAddition_iInf_le (X : Set α) (f₁ f₂ : α → EReal) :
    infAddition (⨅ x ∈ X, f₁ x) (⨅ x ∈ X, f₂ x) ≤ ⨅ x ∈ X, infAddition (f₁ x) (f₂ x) :=
  le_iInf₂ fun _ hx ↦ infAddition_mono (biInf_le f₁ hx) (biInf_le f₂ hx)

/-- **Exercise 1.36**: `sup_X (f₁ + f₂) ≤ sup_X f₁ + sup_X f₂` under inf-addition. -/
theorem iSup_infAddition_le (X : Set α) (f₁ f₂ : α → EReal) :
    (⨆ x ∈ X, infAddition (f₁ x) (f₂ x)) ≤ infAddition (⨆ x ∈ X, f₁ x) (⨆ x ∈ X, f₂ x) :=
  iSup₂_le fun _ hx ↦ infAddition_mono (le_biSup f₁ hx) (le_biSup f₂ hx)

/-- **Exercise 1.36**: `inf_{X₁ × X₂} f₁(x₁) + f₂(x₂) = inf_{X₁} f₁ + inf_{X₂} f₂` under
inf-addition. -/
theorem iInf_prod_infAddition (X₁ : Set α) (X₂ : Set β) (f₁ : α → EReal) (f₂ : β → EReal) :
    (⨅ p ∈ X₁ ×ˢ X₂, infAddition (f₁ p.1) (f₂ p.2)) =
      infAddition (⨅ x ∈ X₁, f₁ x) (⨅ x ∈ X₂, f₂ x) := by
  apply le_antisymm
  · refine ereal_le_of_forall_lt_coe fun c hc ↦ ?_
    obtain ⟨c', hc', hc'c⟩ := EReal.lt_iff_exists_real_btwn.1 hc
    obtain ⟨r, s, hr, hs, hrs⟩ := (infAddition_le_coe_iff _ _ c').1 hc'.le
    have hcc : c' < c := EReal.coe_lt_coe_iff.1 hc'c
    set δ := (c - c') / 2 with hδ
    have hδpos : 0 < δ := by linarith
    obtain ⟨x₁, hx₁, h₁⟩ : ∃ x ∈ X₁, f₁ x < ((r + δ : ℝ) : EReal) := by
      have := lt_of_le_of_lt hr (EReal.coe_lt_coe_iff.2 (by linarith : r < r + δ))
      simpa [iInf_lt_iff] using this
    obtain ⟨x₂, hx₂, h₂⟩ : ∃ x ∈ X₂, f₂ x < ((s + δ : ℝ) : EReal) := by
      have := lt_of_le_of_lt hs (EReal.coe_lt_coe_iff.2 (by linarith : s < s + δ))
      simpa [iInf_lt_iff] using this
    refine (biInf_le _ (show (x₁, x₂) ∈ X₁ ×ˢ X₂ from ⟨hx₁, hx₂⟩)).trans ?_
    refine (infAddition_le_coe_iff _ _ c).2 ⟨r + δ, s + δ, h₁.le, h₂.le, by linarith⟩
  · exact le_iInf₂ fun p hp ↦ infAddition_mono (biInf_le f₁ hp.1) (biInf_le f₂ hp.2)

end Sums

/-! ## Exercise 1.37 -/

section ScalarMultiples

/-- Multiplication by a positive real as an order automorphism of `ℝ̄`. -/
def erealMulLeftOrderIso (c : ℝ) (hc : 0 < c) : EReal ≃o EReal where
  toFun x := (c : EReal) * x
  invFun x := ((c⁻¹ : ℝ) : EReal) * x
  left_inv x := by
    simp only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
  right_inv x := by
    simp only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul]
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 (inv_nonneg.2 hc.le))
      simpa only [Equiv.coe_fn_mk, ← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne',
        EReal.coe_one, one_mul] using this
    · intro h
      exact mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 hc.le)

theorem erealMulLeftOrderIso_apply {c : ℝ} (hc : 0 < c) (x : EReal) :
    erealMulLeftOrderIso c hc x = (c : EReal) * x := rfl

/-- **Exercise 1.37**: `inf_X λf = λ inf_X f` for `λ > 0`. -/
theorem iInf_coe_mul_of_pos (X : Set α) (f : α → EReal) {c : ℝ} (hc : 0 < c) :
    (⨅ x ∈ X, (c : EReal) * f x) = (c : EReal) * ⨅ x ∈ X, f x := by
  simp only [← erealMulLeftOrderIso_apply hc, OrderIso.map_iInf]

/-- **Exercise 1.37**: `sup_X λf = λ sup_X f` for `λ > 0`. -/
theorem iSup_coe_mul_of_pos (X : Set α) (f : α → EReal) {c : ℝ} (hc : 0 < c) :
    (⨆ x ∈ X, (c : EReal) * f x) = (c : EReal) * ⨆ x ∈ X, f x := by
  simp only [← erealMulLeftOrderIso_apply hc, OrderIso.map_iSup]

/-- **Exercise 1.37** for `λ = 0` (with `0·∞ = 0`), on a nonempty set. -/
theorem iInf_zero_mul {X : Set α} (hX : X.Nonempty) (f : α → EReal) :
    (⨅ x ∈ X, (0 : EReal) * f x) = 0 * ⨅ x ∈ X, f x := by
  simp only [zero_mul]
  obtain ⟨x, hx⟩ := hX
  exact le_antisymm (biInf_le _ hx) (le_iInf₂ fun _ _ ↦ le_rfl)

theorem iSup_zero_mul {X : Set α} (hX : X.Nonempty) (f : α → EReal) :
    (⨆ x ∈ X, (0 : EReal) * f x) = 0 * ⨆ x ∈ X, f x := by
  simp only [zero_mul]
  obtain ⟨x, hx⟩ := hX
  exact le_antisymm (iSup₂_le fun _ _ ↦ le_rfl) (le_biSup (fun _ ↦ (0 : EReal)) hx)

/-- **Exercise 1.37** fails as printed for `λ = 0` and `X = ∅`: then `inf_X 0·f = ∞` while
`0·inf_X f = 0·∞ = 0`, and `sup_X 0·f = -∞` while `0·sup_X f = 0`. -/
theorem scalar_multiple_empty_counterexample (f : α → EReal) :
    (⨅ x ∈ (∅ : Set α), (0 : EReal) * f x) ≠ 0 * ⨅ x ∈ (∅ : Set α), f x ∧
      (⨆ x ∈ (∅ : Set α), (0 : EReal) * f x) ≠ 0 * ⨆ x ∈ (∅ : Set α), f x := by
  simp

/-- **Exercise 1.37**: `inf_X f = -sup_X (-f)`. -/
theorem iInf_eq_neg_iSup_neg (X : Set α) (f : α → EReal) :
    (⨅ x ∈ X, f x) = -⨆ x ∈ X, -f x := by
  rw [neg_iSup_ereal]
  simp only [neg_iSup_ereal, neg_neg]

/-- **Exercise 1.37**: `sup_X f = -inf_X (-f)`. -/
theorem iSup_eq_neg_iInf_neg (X : Set α) (f : α → EReal) :
    (⨆ x ∈ X, f x) = -⨅ x ∈ X, -f x := by
  rw [neg_iInf_ereal]
  simp only [neg_iInf_ereal, neg_neg]

end ScalarMultiples

/-! ## Proposition 1.38 and Proposition 1.39 -/

section SumsOfLimits

theorem infAddition_eq_add_of_not_top_bot {a b : EReal} (h₁ : ¬ (a = ⊤ ∧ b = ⊥))
    (h₂ : ¬ (a = ⊥ ∧ b = ⊤)) : infAddition a b = a + b := by
  unfold infAddition
  split_ifs with h
  · rcases h with rfl | rfl
    · have hb : b ≠ ⊥ := fun hb ↦ h₁ ⟨rfl, hb⟩
      exact (EReal.top_add_of_ne_bot hb).symm
    · have ha : a ≠ ⊥ := fun ha ↦ h₂ ⟨ha, rfl⟩
      exact (EReal.add_top_of_ne_bot ha).symm
  · rfl

variable [PseudoMetricSpace E]

/-- With ordinary `EReal` addition (`⊥ + ⊤ = ⊥`), the lower limit is superadditive with no
restriction. -/
theorem add_lowerLimit_le (f₁ f₂ : E → EReal) (x : E) :
    lowerLimit f₁ x + lowerLimit f₂ x ≤ lowerLimit (fun y ↦ f₁ y + f₂ y) x := by
  simp only [lowerLimit_eq_liminf]
  exact EReal.le_liminf_add

/-- **Proposition 1.38**: `liminf (f₁ + f₂) ≥ liminf f₁ + liminf f₂` under the book's inf-addition,
if the sum on the right is not `∞ - ∞`. -/
theorem infAddition_lowerLimit_le {f₁ f₂ : E → EReal} {x : E}
    (h₁ : ¬ (lowerLimit f₁ x = ⊤ ∧ lowerLimit f₂ x = ⊥))
    (h₂ : ¬ (lowerLimit f₁ x = ⊥ ∧ lowerLimit f₂ x = ⊤)) :
    infAddition (lowerLimit f₁ x) (lowerLimit f₂ x) ≤
      lowerLimit (fun y ↦ infAddition (f₁ y) (f₂ y)) x := by
  rw [infAddition_eq_add_of_not_top_bot h₁ h₂]
  exact (add_lowerLimit_le f₁ f₂ x).trans (lowerLimit_mono (fun y ↦ add_le_infAddition _ _) x)

/-- **Proposition 1.38**: `liminf λ f = λ liminf f` for `λ ≥ 0`. -/
theorem lowerLimit_coe_mul {c : ℝ} (hc : 0 ≤ c) (f : E → EReal) (x : E) :
    lowerLimit (fun y ↦ (c : EReal) * f y) x = (c : EReal) * lowerLimit f x := by
  rcases hc.lt_or_eq with hc | rfl
  · simp only [lowerLimit, ← erealMulLeftOrderIso_apply hc, OrderIso.map_iSup, OrderIso.map_iInf]
  · simp only [EReal.coe_zero, zero_mul, lowerLimit]
    exact le_antisymm (iSup₂_le fun _ _ ↦ iInf₂_le_of_le x (mem_closedBall_self (by linarith))
      le_rfl) (le_iSup₂_of_le 1 one_pos (le_iInf₂ fun _ _ ↦ le_rfl))

/-- With ordinary `EReal` addition the sum of lsc functions is lsc. -/
theorem lowerSemicontinuous_add_ereal {f₁ f₂ : E → EReal} (h₁ : LowerSemicontinuous f₁)
    (h₂ : LowerSemicontinuous f₂) : LowerSemicontinuous (fun y ↦ f₁ y + f₂ y) := by
  rw [lowerSemicontinuous_iff_forall_le_lowerLimit] at h₁ h₂ ⊢
  exact fun x ↦ (add_le_add (h₁ x) (h₂ x)).trans (add_lowerLimit_le f₁ f₂ x)

/-- **Proposition 1.39(a)**: `f₁ + f₂` is lsc if `f₁` and `f₂` are lsc and proper (the sum taken
with inf-addition, which agrees with ordinary addition here). -/
theorem lowerSemicontinuous_infAddition {f₁ f₂ : E → EReal} (h₁ : LowerSemicontinuous f₁)
    (h₂ : LowerSemicontinuous f₂) (hp₁ : IsProper f₁) (hp₂ : IsProper f₂) :
    LowerSemicontinuous (fun y ↦ infAddition (f₁ y) (f₂ y)) := by
  have : (fun y ↦ infAddition (f₁ y) (f₂ y)) = fun y ↦ f₁ y + f₂ y := funext fun y ↦
    infAddition_eq_add_of_ne_bot (hp₁.2 y).ne' (hp₂.2 y).ne'
  rw [this]
  exact lowerSemicontinuous_add_ereal h₁ h₂

/-- **Proposition 1.39(b)**: `λ f` is lsc if `f` is lsc and `λ ≥ 0`. -/
theorem lowerSemicontinuous_coe_mul {f : E → EReal} (hf : LowerSemicontinuous f) {c : ℝ}
    (hc : 0 ≤ c) : LowerSemicontinuous (fun y ↦ (c : EReal) * f y) := by
  rw [lowerSemicontinuous_iff_forall_le_lowerLimit] at hf ⊢
  intro x
  rw [lowerLimit_coe_mul hc]
  exact mul_le_mul_of_nonneg_left (hf x) (EReal.coe_nonneg.2 hc)

end SumsOfLimits

/-! ## Exercise 1.40 -/

section Composition

/-- **Exercise 1.40(a)**: `g ∘ F` is lsc for continuous `F` and lsc `g`. -/
theorem lowerSemicontinuous_comp_continuous [TopologicalSpace α] [TopologicalSpace β]
    {g : β → EReal} (hg : LowerSemicontinuous g) {F : α → β} (hF : Continuous F) :
    LowerSemicontinuous (fun x ↦ g (F x)) :=
  hg.comp hF

/-- `monotoneExtension` (Chapter 14) extends `θ` by `θ(∞) = sup θ` and `θ(-∞) = inf θ`. -/
@[simp] theorem monotoneExtension_bot (θ : ℝ → EReal) : monotoneExtension θ ⊥ = ⨅ t, θ t := by
  simp [monotoneExtension]

@[simp] theorem monotoneExtension_top (θ : ℝ → EReal) : monotoneExtension θ ⊤ = ⨆ t, θ t := by
  simp [monotoneExtension]

@[simp] theorem monotoneExtension_coe (θ : ℝ → EReal) (t : ℝ) : monotoneExtension θ t = θ t := by
  simp [monotoneExtension]

theorem monotone_monotoneExtension {θ : ℝ → EReal} (hθ : Monotone θ) :
    Monotone (monotoneExtension θ) := by
  intro a b hab
  induction a using EReal.rec with
  | bot => rw [monotoneExtension_bot]
           induction b using EReal.rec with
           | bot => rw [monotoneExtension_bot]
           | top => rw [monotoneExtension_top]; exact (iInf_le θ 0).trans (le_iSup θ 0)
           | coe t => rw [monotoneExtension_coe]; exact iInf_le θ t
  | top =>
    rw [top_le_iff.1 hab]
  | coe s =>
    rw [monotoneExtension_coe]
    induction b using EReal.rec with
    | bot => exact absurd hab (not_le.2 (EReal.bot_lt_coe s))
    | top => rw [monotoneExtension_top]; exact le_iSup θ s
    | coe t => rw [monotoneExtension_coe]; exact hθ (EReal.coe_le_coe_iff.1 hab)

/-- **Exercise 1.40(b)**: `θ ∘ g` is lsc for lsc `g` and lsc nondecreasing `θ : ℝ → ℝ̄`, extended
by `θ(∞) = sup θ` and `θ(-∞) = inf θ`. -/
theorem lowerSemicontinuous_monotoneExtension_comp [TopologicalSpace α] {θ : ℝ → EReal}
    (hθ : LowerSemicontinuous θ) (hmono : Monotone θ) {g : α → EReal}
    (hg : LowerSemicontinuous g) : LowerSemicontinuous (fun x ↦ monotoneExtension θ (g x)) := by
  have hm := monotone_monotoneExtension hmono
  intro x y hy
  change y < monotoneExtension θ (g x) at hy
  change ∀ᶠ x' in 𝓝 x, y < monotoneExtension θ (g x')
  induction hgx : g x using EReal.rec with
  | bot =>
    rw [hgx] at hy
    exact Eventually.of_forall fun x' ↦ lt_of_lt_of_le hy (hm bot_le)
  | top =>
    rw [hgx, monotoneExtension_top] at hy
    obtain ⟨t, ht⟩ := lt_iSup_iff.1 hy
    have hev : ∀ᶠ x' in 𝓝 x, (t : EReal) < g x' :=
      hg x t (show (t : EReal) < g x by rw [hgx]; exact EReal.coe_lt_top t)
    have ht' : y < monotoneExtension θ (t : EReal) := by rwa [monotoneExtension_coe]
    exact hev.mono fun x' hx' ↦ lt_of_lt_of_le ht' (hm hx'.le)
  | coe s =>
    rw [hgx, monotoneExtension_coe] at hy
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hθ s y hy)
    have ht0 : y < θ (s - ε / 2) := hball (by
      rw [Real.dist_eq, show s - ε / 2 - s = -(ε / 2) by ring, abs_neg, abs_of_pos (by positivity)]
      linarith)
    have hev : ∀ᶠ x' in 𝓝 x, (((s - ε / 2) : ℝ) : EReal) < g x' :=
      hg x _ (show (((s - ε / 2) : ℝ) : EReal) < g x by
        rw [hgx]; exact EReal.coe_lt_coe_iff.2 (by linarith))
    have ht' : y < monotoneExtension θ (((s - ε / 2) : ℝ) : EReal) := by rwa [monotoneExtension_coe]
    exact hev.mono fun x' hx' ↦ lt_of_lt_of_le ht' (hm hx'.le)

end Composition

/-! ## Exercise 1.41 -/

section LevelBoundedSums

theorem le_coe_sub_of_add_coe_le {a : EReal} {m c : ℝ} (h : a + m ≤ c) :
    a ≤ ((c - m : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => simp at h
  | coe a =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
    exact EReal.coe_le_coe_iff.2 (by linarith)

variable [NormedAddCommGroup E]

/-- **Exercise 1.41(a)**: `f₁ + f₂` is level-bounded if `f₁` is level-bounded and `f₂` is
bounded from below. -/
theorem isLevelBounded_add_of_left {f₁ f₂ : E → EReal} (h₁ : IsLevelBounded f₁)
    (h₂ : ∃ m : ℝ, ∀ x, (m : EReal) ≤ f₂ x) : IsLevelBounded (fun x ↦ f₁ x + f₂ x) := by
  obtain ⟨m, hm⟩ := h₂
  intro c
  refine (h₁ (c - m)).subset fun x hx ↦ le_coe_sub_of_add_coe_le ?_
  exact (add_le_add le_rfl (hm x)).trans hx

/-- **Exercise 1.41(a)**, the symmetric case. -/
theorem isLevelBounded_add_of_right {f₁ f₂ : E → EReal} (h₁ : ∃ m : ℝ, ∀ x, (m : EReal) ≤ f₁ x)
    (h₂ : IsLevelBounded f₂) : IsLevelBounded (fun x ↦ f₁ x + f₂ x) := by
  simpa only [add_comm] using isLevelBounded_add_of_left h₂ h₁

/-- **Exercise 1.41(b)**: the epi-sum `f₁ □ f₂` of two level-bounded functions that are bounded
from below is level-bounded. -/
theorem isLevelBounded_epiSum [NormedSpace ℝ E] {f₁ f₂ : E → EReal}
    (hb₁ : ∃ m : ℝ, ∀ x, (m : EReal) ≤ f₁ x) (hb₂ : ∃ m : ℝ, ∀ x, (m : EReal) ≤ f₂ x)
    (h₁ : IsLevelBounded f₁) (h₂ : IsLevelBounded f₂) : IsLevelBounded (epiSum f₁ f₂) := by
  obtain ⟨m₁, hm₁⟩ := hb₁
  obtain ⟨m₂, hm₂⟩ := hb₂
  intro c
  refine ((h₁ (c + 1 - m₂)).add (h₂ (c + 1 - m₁))).subset fun x hx ↦ ?_
  have hlt : epiSum f₁ f₂ x < ((c + 1 : ℝ) : EReal) :=
    lt_of_le_of_lt hx (EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨w, hw⟩ := iInf_lt_iff.1 hlt
  refine ⟨x - w, ?_, w, ?_, sub_add_cancel x w⟩
  · exact le_coe_sub_of_add_coe_le ((add_le_add le_rfl (hm₂ w)).trans hw.le)
  · refine le_coe_sub_of_add_coe_le ?_
    rw [add_comm]
    exact (add_le_add (hm₁ (x - w)) le_rfl).trans hw.le

end LevelBoundedSums

/-! ## Proposition 1.43 -/

section Ekeland

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Proposition 1.43** (variational principle; Ekeland): for `f` lsc with `inf f = m` finite,
`x̄ ∈ ε-argmin f` and `δ > 0`, some `x̃ ∈ IB(x̄, ε/δ)` has `f(x̃) ≤ f(x̄)` and is the unique
minimizer of `f + δ|· - x̃|`.  (The sign of `ε` plays no role in the proof.) -/
theorem ekeland_variational_principle {f : E → EReal} (hl : LowerSemicontinuous f) {m : ℝ}
    (hm : (⨅ x, f x) = m) {ε : ℝ} {x₀ : E} (hx₀ : x₀ ∈ approxArgmin f ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x₁ ∈ closedBall x₀ (ε / δ), f x₁ ≤ f x₀ ∧
      argmin (fun x ↦ f x + ((δ * ‖x - x₁‖ : ℝ) : EReal)) = {x₁} := by
  have hfm : ∀ x, (m : EReal) ≤ f x := fun x ↦ hm ▸ iInf_le f x
  have hx₀' : f x₀ ≤ ((m + ε : ℝ) : EReal) := by
    have h := hx₀
    simp only [approxArgmin, mem_setOf_eq, hm] at h
    rwa [EReal.coe_add]
  have hfin : ∀ x, f x ≠ ⊥ := fun x ↦ ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hfm x)
  set fbar : E → EReal := fun x ↦ f x + ((δ * ‖x - x₀‖ : ℝ) : EReal) with hfbar
  have hlbar : LowerSemicontinuous fbar := lowerSemicontinuous_add_coe hl (by fun_prop)
  have hfbar₀ : fbar x₀ = f x₀ := by simp [hfbar]
  have hpbar : IsProper fbar := by
    refine ⟨⟨x₀, by rw [hfbar₀]; exact lt_of_le_of_lt hx₀' (EReal.coe_lt_top _)⟩, fun x ↦ ?_⟩
    exact EReal.bot_lt_add_iff.2 ⟨(hfin x).bot_lt, EReal.bot_lt_coe _⟩
  have hbbar : IsLevelBounded fbar := by
    intro α
    refine (isBounded_closedBall (x := x₀) (r := (α - m) / δ)).subset fun x hx ↦ ?_
    have h1 : ((m + δ * ‖x - x₀‖ : ℝ) : EReal) ≤ α :=
      le_trans (by rw [EReal.coe_add]; exact add_le_add (hfm x) le_rfl) hx
    rw [EReal.coe_le_coe_iff] at h1
    rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hδ]
    linarith
  obtain ⟨-, hCne, hCcpt⟩ := attainment_of_minimum hlbar hbbar hpbar
  obtain ⟨x₁, hx₁C, hmin⟩ := (hl.lowerSemicontinuousOn _).exists_isMinOn hCne hCcpt
  have hinfbar : (⨅ x, fbar x) < ⊤ := hx₁C.2
  have hx₁bar : fbar x₁ = ⨅ x, fbar x := hx₁C.1
  have hbar_le : fbar x₁ ≤ f x₀ := hx₁bar ▸ (iInf_le fbar x₀).trans_eq hfbar₀
  -- `f x₁` is finite
  have hf₁le : f x₁ ≤ fbar x₁ := le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity))
  have htop₁ : f x₁ ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top (m + ε))
    ((hf₁le.trans hbar_le).trans hx₀')
  set a₁ := (f x₁).toReal with ha₁def
  have ha₁ : f x₁ = a₁ := (EReal.coe_toReal htop₁ (hfin x₁)).symm
  have hbar₁ : fbar x₁ = ((a₁ + δ * ‖x₁ - x₀‖ : ℝ) : EReal) := by
    simp only [hfbar, ha₁, EReal.coe_add]
  refine ⟨x₁, ?_, hf₁le.trans hbar_le, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hδ]
    have h := hbar_le.trans hx₀'
    rw [hbar₁, EReal.coe_le_coe_iff] at h
    have hm₁ : m ≤ a₁ := EReal.coe_le_coe_iff.1 (ha₁ ▸ hfm x₁)
    linarith
  -- strict inequality away from `x₁`
  have hstrict : ∀ x, x ≠ x₁ → f x₁ < f x + ((δ * ‖x - x₁‖ : ℝ) : EReal) := by
    intro x hx
    have hpos : 0 < ‖x - x₁‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
    by_cases hxtop : f x = ⊤
    · rw [hxtop, EReal.top_add_coe, ha₁]; exact EReal.coe_lt_top _
    set a := (f x).toReal with hadef
    have ha : f x = a := (EReal.coe_toReal hxtop (hfin x)).symm
    rw [ha₁, ha, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    by_cases hxC : x ∈ argmin fbar
    · have h1 : f x₁ ≤ f x := hmin hxC
      rw [ha₁, ha, EReal.coe_le_coe_iff] at h1
      nlinarith
    · have hlt : fbar x₁ < fbar x := by
        rw [hx₁bar]
        refine lt_of_le_of_ne (iInf_le fbar x) fun h ↦ hxC ⟨h.symm, hinfbar⟩
      have hbarx : fbar x = ((a + δ * ‖x - x₀‖ : ℝ) : EReal) := by
        simp only [hfbar, ha, EReal.coe_add]
      rw [hbar₁, hbarx, EReal.coe_lt_coe_iff] at hlt
      have htri : ‖x - x₀‖ ≤ ‖x - x₁‖ + ‖x₁ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub x x₁ x₀
      nlinarith
  have hval₁ : f x₁ + ((δ * ‖x₁ - x₁‖ : ℝ) : EReal) = f x₁ := by simp
  have hinf : (⨅ x, f x + ((δ * ‖x - x₁‖ : ℝ) : EReal)) = f x₁ := by
    refine le_antisymm ((iInf_le _ x₁).trans_eq hval₁) (le_iInf fun x ↦ ?_)
    by_cases hx : x = x₁
    · rw [hx, hval₁]
    · exact (hstrict x hx).le
  ext x
  rw [mem_argmin_iff, hinf, mem_singleton_iff]
  constructor
  · rintro ⟨h, -⟩
    by_contra hx
    exact absurd h (hstrict x hx).ne'
  · rintro rfl
    exact ⟨hval₁, lt_top_iff_ne_top.2 htop₁⟩

end Ekeland

/-! ## Definition 1.33 and Exercise 1.34 -/

section LocalSemicontinuity

variable [PseudoMetricSpace E]

/-- **Definition 1.33**, upper half: `f` is locally upper semicontinuous at `x̄`, a point where
`f(x̄)` is finite, if for some `ε > 0` all sets `{x ∈ IB(x̄, ε) | f(x) ≥ α}` with
`α ≥ f(x̄) - ε` are closed.  The lower half is `IsLocallyLscAt` (Chapter 7). -/
def IsLocallyUscAt (f : E → EReal) (x : E) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∃ ε > 0, ∀ α : ℝ, (f x).toReal - ε ≤ α →
    IsClosed (closedBall x ε ∩ {y | (α : EReal) ≤ f y})

/-- **Exercise 1.34(a)**: at a point where `f(x̄)` is finite, `f` is locally lsc iff `epi f` is
locally closed at `(x̄, f(x̄))`. -/
theorem isLocallyLscAt_iff_isLocallyClosedAt_epigraph {f : E → EReal} {x : E} (hb : f x ≠ ⊥)
    (ht : f x ≠ ⊤) : IsLocallyLscAt f x ↔ IsLocallyClosedAt (epigraph f) (x, (f x).toReal) := by
  refine ⟨IsLocallyLscAt.isLocallyClosedAt_epigraph, fun ⟨V, hV, _, hEV⟩ ↦ ?_⟩
  set c := (f x).toReal with hcdef
  have hfx : f x = c := (EReal.coe_toReal ht hb).symm
  obtain ⟨δ, hδ, hδV⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
  have hbox : IsClosed (epigraph f ∩ closedBall (x, c) δ) := by
    have heq : epigraph f ∩ closedBall (x, c) δ = (epigraph f ∩ V) ∩ closedBall (x, c) δ := by
      ext p
      exact ⟨fun h ↦ ⟨⟨h.1, hδV h.2⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩
    rw [heq]
    exact hEV.inter isClosed_closedBall
  have hslice : ∀ a : ℝ, c - δ ≤ a → a ≤ c + δ →
      IsClosed (closedBall x δ ∩ {y | f y ≤ a}) := by
    intro a ha1 ha2
    have hac : a ∈ closedBall c δ := by
      rw [mem_closedBall, Real.dist_eq, abs_le]; constructor <;> linarith
    have heq : closedBall x δ ∩ {y | f y ≤ a} =
        (fun y ↦ (y, a)) ⁻¹' (epigraph f ∩ closedBall (x, c) δ) := by
      ext y
      simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_epigraph_iff,
        ← closedBall_prod_same, mem_prod]
      tauto
    rw [heq]
    exact hbox.preimage (continuous_id.prodMk continuous_const)
  have hlow : ∃ ρ > 0, ρ ≤ δ ∧ ∀ y ∈ closedBall x ρ, ((c - δ : ℝ) : EReal) < f y := by
    have hcl := hslice (c - δ) le_rfl (by linarith)
    have hx : x ∉ closedBall x δ ∩ {y | f y ≤ ((c - δ : ℝ) : EReal)} := by
      rintro ⟨-, hy⟩
      rw [mem_setOf_eq, hfx, EReal.coe_le_coe_iff] at hy
      linarith
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
      (hcl.isOpen_compl.mem_nhds hx)
    refine ⟨min ρ δ, lt_min hρ hδ, min_le_right _ _, fun y hy ↦ ?_⟩
    by_contra h
    push_neg at h
    exact hρsub (closedBall_subset_closedBall (min_le_left _ _) hy)
      ⟨closedBall_subset_closedBall (min_le_right _ _) hy, h⟩
  obtain ⟨ρ, hρ, hρδ, hρlow⟩ := hlow
  refine ⟨hb, ht, ρ, hρ, fun a ha ↦ ?_⟩
  by_cases hac : a < c - δ
  · have hempty : closedBall x ρ ∩ {y | f y ≤ a} = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      exact fun hy ↦ lt_trans (EReal.coe_lt_coe_iff.2 hac) (hρlow y hy)
    rw [hempty]
    exact isClosed_empty
  · push_neg at hac
    have heq : closedBall x ρ ∩ {y | f y ≤ a} =
        closedBall x ρ ∩ (closedBall x δ ∩ {y | f y ≤ a}) := by
      ext y
      exact ⟨fun h ↦ ⟨h.1, closedBall_subset_closedBall hρδ h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
    rw [heq]
    exact isClosed_closedBall.inter (hslice a hac (by rw [← hcdef] at ha; linarith))

/-- Closed lower level sets on a ball give lower semicontinuity inside the ball at points below
the levels considered. -/
theorem lowerSemicontinuousAt_of_isClosed_levels {f : E → EReal} {x y : E} {r c : ℝ}
    (hA : ∀ a : ℝ, a ≤ c → IsClosed (closedBall x r ∩ {w | f w ≤ a})) (hy : y ∈ ball x r)
    (hyc : f y ≤ c) : LowerSemicontinuousAt f y := by
  intro z hz
  obtain ⟨a, hza, hay⟩ := EReal.lt_iff_exists_real_btwn.1 hz
  have hac : a ≤ c := EReal.coe_le_coe_iff.1 (hay.le.trans hyc)
  have hyA : y ∉ closedBall x r ∩ {w | f w ≤ a} := fun h ↦ absurd h.2 (not_le.2 hay)
  filter_upwards [(hA a hac).isOpen_compl.mem_nhds hyA, isOpen_ball.mem_nhds hy] with w hw hwb
  have : ¬ f w ≤ a := fun h ↦ hw ⟨ball_subset_closedBall hwb, h⟩
  exact lt_trans hza (not_le.1 this)

/-- Closed upper level sets on a ball give upper semicontinuity inside the ball at points above
the levels considered. -/
theorem upperSemicontinuousAt_of_isClosed_levels {f : E → EReal} {x y : E} {r c : ℝ}
    (hB : ∀ a : ℝ, c ≤ a → IsClosed (closedBall x r ∩ {w | (a : EReal) ≤ f w})) (hy : y ∈ ball x r)
    (hyc : (c : EReal) ≤ f y) : UpperSemicontinuousAt f y := by
  intro z hz
  obtain ⟨a, hya, haz⟩ := EReal.lt_iff_exists_real_btwn.1 hz
  have hca : c ≤ a := EReal.coe_le_coe_iff.1 (hyc.trans hya.le)
  have hyB : y ∉ closedBall x r ∩ {w | (a : EReal) ≤ f w} := fun h ↦ absurd h.2 (not_le.2 hya)
  filter_upwards [(hB a hca).isOpen_compl.mem_nhds hyB, isOpen_ball.mem_nhds hy] with w hw hwb
  have : ¬ (a : EReal) ≤ f w := fun h ↦ hw ⟨ball_subset_closedBall hwb, h⟩
  exact lt_trans (not_le.1 this) haz

/-- **Exercise 1.34(b)**: `f` is finite and continuous on some neighborhood of `x̄` iff `f(x̄)` is
finite and `f` is both locally lsc and locally usc at `x̄`. -/
theorem finite_continuousOn_nhds_iff {f : E → EReal} {x : E} :
    (∃ V ∈ 𝓝 x, ContinuousOn f V ∧ ∀ y ∈ V, f y ≠ ⊥ ∧ f y ≠ ⊤) ↔
      f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ IsLocallyLscAt f x ∧ IsLocallyUscAt f x := by
  constructor
  · rintro ⟨V, hV, hc, hfin⟩
    obtain ⟨ε, hε, hεV⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
    have hcε := hc.mono hεV
    obtain ⟨hb, ht⟩ := hfin x (mem_of_mem_nhds hV)
    refine ⟨hb, ht, ⟨hb, ht, ε, hε, fun a _ ↦ ?_⟩, ⟨hb, ht, ε, hε, fun a _ ↦ ?_⟩⟩
    · exact hcε.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
    · exact hcε.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Ici
  · rintro ⟨hb, ht, ⟨-, -, ε₁, hε₁, hA⟩, ⟨-, -, ε₂, hε₂, hB⟩⟩
    set c := (f x).toReal with hcdef
    have hfx : f x = c := (EReal.coe_toReal ht hb).symm
    set r := min ε₁ ε₂ with hr
    have hr0 : 0 < r := lt_min hε₁ hε₂
    have hA' : ∀ a : ℝ, a ≤ c + r → IsClosed (closedBall x r ∩ {w | f w ≤ a}) := by
      intro a ha
      have heq : closedBall x r ∩ {w | f w ≤ a} =
          closedBall x r ∩ (closedBall x ε₁ ∩ {w | f w ≤ a}) := by
        ext w
        exact ⟨fun h ↦ ⟨h.1, closedBall_subset_closedBall (min_le_left _ _) h.1, h.2⟩,
          fun h ↦ ⟨h.1, h.2.2⟩⟩
      rw [heq]
      exact isClosed_closedBall.inter (hA a (by linarith [min_le_left ε₁ ε₂]))
    have hB' : ∀ a : ℝ, c - r ≤ a → IsClosed (closedBall x r ∩ {w | (a : EReal) ≤ f w}) := by
      intro a ha
      have heq : closedBall x r ∩ {w | (a : EReal) ≤ f w} =
          closedBall x r ∩ (closedBall x ε₂ ∩ {w | (a : EReal) ≤ f w}) := by
        ext w
        exact ⟨fun h ↦ ⟨h.1, closedBall_subset_closedBall (min_le_right _ _) h.1, h.2⟩,
          fun h ↦ ⟨h.1, h.2.2⟩⟩
      rw [heq]
      exact isClosed_closedBall.inter (hB a (by linarith [min_le_right ε₁ ε₂]))
    have hxball : x ∈ ball x r := mem_ball_self hr0
    have hlx := lowerSemicontinuousAt_of_isClosed_levels hA' hxball
      (by rw [hfx]; exact EReal.coe_le_coe_iff.2 (by linarith))
    have hux := upperSemicontinuousAt_of_isClosed_levels hB' hxball
      (by rw [hfx]; exact EReal.coe_le_coe_iff.2 (by linarith))
    have hlow : ∀ᶠ y in 𝓝 x, ((c - r : ℝ) : EReal) < f y :=
      hlx _ (show ((c - r : ℝ) : EReal) < f x by
        rw [hfx]; exact EReal.coe_lt_coe_iff.2 (by linarith))
    have hup : ∀ᶠ y in 𝓝 x, f y < ((c + r : ℝ) : EReal) :=
      hux _ (show f x < ((c + r : ℝ) : EReal) by
        rw [hfx]; exact EReal.coe_lt_coe_iff.2 (by linarith))
    set V := {y | y ∈ ball x r ∧ ((c - r : ℝ) : EReal) < f y ∧ f y < ((c + r : ℝ) : EReal)}
    have hV : V ∈ 𝓝 x := by
      filter_upwards [isOpen_ball.mem_nhds hxball, hlow, hup] with y h1 h2 h3
      exact ⟨h1, h2, h3⟩
    refine ⟨V, hV, fun y hy ↦ ?_, fun y hy ↦ ⟨ne_bot_of_gt hy.2.1, ne_top_of_lt hy.2.2⟩⟩
    refine ContinuousAt.continuousWithinAt ?_
    rw [continuousAt_iff_lower_upperSemicontinuousAt]
    exact ⟨lowerSemicontinuousAt_of_isClosed_levels hA' hy.1 hy.2.2.le,
      upperSemicontinuousAt_of_isClosed_levels hB' hy.1 hy.2.1.le⟩

end LocalSemicontinuity

end RW
