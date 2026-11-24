/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second subderivatives of convex functions

Proposition 13.20.  Convexity of `f` is convexity of its epigraph and
`v̄ ∈ ∂f(x̄)` is a limiting subgradient, which for convex `f` is a subgradient in
the sense of convex analysis.

**Correction to 13.20(b).**  The book asserts that `d²f(x̄ | v̄) = γ_C²` for a
*unique* closed set `C ∋ 0`.  The gauge of an arbitrary closed set does not
determine the set: in a nontrivial space the closed unit ball and the set
`{0} ∪ {‖w‖ = 1}` both have gauge `‖·‖` (`gaugeFunction_closedBall_one`,
`gaugeFunction_insert_zero_sphere`), and `‖·‖²` is `d²f(0 | 0)` for the convex
function `f = ½‖·‖²` (`gauge_uniqueness_counterexample`).  Uniqueness holds
among closed sets containing `0` that are star-shaped with respect to `0`,
and the set `C = {w | d²f(x̄ | v̄)(w) ≤ 1}` is of that kind.  The failure is
one of definitions rather than of the theorem: Example 3.50 defines `γ_C` for
closed convex `C` only, and 13.20(b) applies it to a closed set that need not
be convex; `gaugeFunction` extends the formula `γ_C = pos(δ_C + 1)` of 3.50 to
arbitrary sets.  For closed star-shaped `C ∋ 0` the gauge determines the set,
`C = {γ_C ≤ 1}` (`mem_of_gaugeFunction_le_one`).

Part (c) concerns continuous convergence of the quotients `Δ²_τ f(x̄ | v̄)`,
which is the meaning of "twice semidifferentiable at `x̄` for `v̄`" in the
book's proof; this is made precise as `TwiceSemidifferentiableAtFor`.  Its
finiteness conjunct is redundant for proper convex `f` and `v̄ ∈ ∂f(x̄)`
(`twiceSemidifferentiableAtFor_iff_tendsto`): `d²f(x̄ | v̄) ≥ 0`, and
continuous convergence in the direction `0` alone bounds the quotients near
every `w` through the scaling law, so `d²f(x̄ | v̄) < ∞`
(`secondSubderivative_ne_top_of_tendsto_zero`; the remark after
Definition 13.6).
-/

import RockafellarWets.Chapter13.ProxRegularity
import RockafellarWets.Chapter13.SecondOrderExpansions
import RockafellarWets.Chapter13.ParabolicSubderivatives
import RockafellarWets.Chapter7.ConvexEpiConvergence
import RockafellarWets.Chapter8.MappingSemiderivatives
import RockafellarWets.Chapter3.PositiveHulls

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Convexity of inner limits and of the quotients -/

section Convexity

/-- Inner limits of convex sets are convex. -/
theorem convex_innerSetLimitAlong {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} {C : ι → Set F} (hC : ∀ i, Convex ℝ (C i)) :
    Convex ℝ (innerSetLimitAlong l C) := by
  intro a ha b hb s t hs ht hst N hN
  have hcont : Continuous fun p : F × F ↦ s • p.1 + t • p.2 := by fun_prop
  have hN' : (fun p : F × F ↦ s • p.1 + t • p.2) ⁻¹' N ∈ 𝓝 (a, b) :=
    hcont.continuousAt.preimage_mem_nhds hN
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.1 hN'
  filter_upwards [ha U hU, hb W hW] with i ⟨a', ha'C, ha'U⟩ ⟨b', hb'C, hb'W⟩
  exact ⟨s • a' + t • b', hC i ha'C hb'C hs ht hst, hUW (mk_mem_prod ha'U hb'W)⟩

/-- The epigraph inequality for the quotient 13(5) at a positive scale. -/
theorem secondDifferenceQuotient_le_coe_iff {f : E → EReal} {x v w : E} {c τ α : ℝ}
    (hx : f x = c) (hτ : 0 < τ) :
    secondDifferenceQuotient f x v τ w ≤ (α : EReal) ↔
      f (x + τ • w) ≤ ((c + τ * ⟪v, w⟫_ℝ + τ ^ 2 / 2 * α : ℝ) : EReal) := by
  have h2 : (0 : ℝ) < 2 / τ ^ 2 := by positivity
  rcases ereal_trichotomy (f (x + τ • w)) with h | h | ⟨r, h⟩
  · rw [secondDifferenceQuotient_of_bot hτ.ne' hx h, h]
    exact iff_of_true bot_le bot_le
  · rw [secondDifferenceQuotient_of_top hτ.ne' hx h, h]
    exact iff_of_false (fun h ↦ EReal.coe_ne_top _ (top_le_iff.1 h))
      (fun h ↦ EReal.coe_ne_top _ (top_le_iff.1 h))
  · rw [secondDifferenceQuotient_of_coe hx h, h, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    have hτ2 : 0 < τ ^ 2 := by positivity
    constructor
    · intro hle
      have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ τ ^ 2 / 2)
      have heq : τ ^ 2 / 2 * (2 / τ ^ 2 * (r - c - τ * ⟪v, w⟫_ℝ)) = r - c - τ * ⟪v, w⟫_ℝ := by
        field_simp
      linarith
    · intro hle
      have := mul_le_mul_of_nonneg_left (show r - c - τ * ⟪v, w⟫_ℝ ≤ τ ^ 2 / 2 * α by linarith)
        h2.le
      have heq : 2 / τ ^ 2 * (τ ^ 2 / 2 * α) = α := by field_simp
      linarith

/-- For convex `f` the quotients `Δ²_τ f(x̄ | v)` are convex. -/
theorem convex_epigraph_secondDifferenceQuotient {f : E → EReal} {x v : E} {c τ : ℝ}
    (hc : Convex ℝ (epigraph f)) (hx : f x = c) (hτ : 0 < τ) :
    Convex ℝ (epigraph (secondDifferenceQuotient f x v τ)) := by
  rintro ⟨w₁, α₁⟩ h₁ ⟨w₂, α₂⟩ h₂ a b ha hb hab
  rw [mem_epigraph_iff, secondDifferenceQuotient_le_coe_iff hx hτ] at h₁ h₂
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [mem_epigraph_iff, secondDifferenceQuotient_le_coe_iff hx hτ]
  have hP := hc (show (x + τ • w₁, c + τ * ⟪v, w₁⟫_ℝ + τ ^ 2 / 2 * α₁) ∈ epigraph f from h₁)
    (show (x + τ • w₂, c + τ * ⟪v, w₂⟫_ℝ + τ ^ 2 / 2 * α₂) ∈ epigraph f from h₂) ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hP
  have e1 : a • (x + τ • w₁) + b • (x + τ • w₂) = x + τ • (a • w₁ + b • w₂) := by
    rw [smul_add, smul_add, smul_add, smul_comm a τ, smul_comm b τ, add_add_add_comm,
      ← add_smul, hab, one_smul]
  have e2 : a * (c + τ * ⟪v, w₁⟫_ℝ + τ ^ 2 / 2 * α₁) + b * (c + τ * ⟪v, w₂⟫_ℝ + τ ^ 2 / 2 * α₂) =
      c + τ * ⟪v, a • w₁ + b • w₂⟫_ℝ + τ ^ 2 / 2 * (a * α₁ + b * α₂) := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    linear_combination c * hab
  rw [e1, e2] at hP
  exact hP

end Convexity

/-! ### Proposition 13.20(a) -/

section Part_a

variable [FiniteDimensional ℝ E] {f : E → EReal} {x v : E} {c : ℝ}

/-- The quotients `Δ²_τ f(x̄ | v)` of a proper convex function are nonnegative for
`v ∈ ∂f(x̄)`. -/
theorem secondDifferenceQuotient_nonneg_of_convex (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hx : f x = c) (hv : v ∈ subdifferential f x) {τ : ℝ} (hτ : 0 < τ) (w : E) :
    0 ≤ secondDifferenceQuotient f x v τ w := by
  have h := (mem_subdifferential_iff_of_convex hc hp hx).1 hv (x + τ • w)
  rw [add_sub_cancel_left, real_inner_smul_right] at h
  rcases ereal_trichotomy (f (x + τ • w)) with h' | h' | ⟨r, h'⟩
  · rw [h'] at h
    exact absurd (le_bot_iff.1 h) (EReal.coe_ne_bot _)
  · rw [secondDifferenceQuotient_of_top hτ.ne' hx h']
    exact le_top
  · rw [h', EReal.coe_le_coe_iff] at h
    rw [secondDifferenceQuotient_of_coe hx h']
    exact EReal.coe_nonneg.2 (mul_nonneg (by positivity) (by linarith))

/-- **Proposition 13.20(a)**: `d²f(x̄ | v) ≥ 0`. -/
theorem secondSubderivative_nonneg_of_convex (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hx : f x = c) (hv : v ∈ subdifferential f x) (w : E) : 0 ≤ secondSubderivative f x v w := by
  refine le_liminf_of_le (h := ?_)
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp'
  exact secondDifferenceQuotient_nonneg_of_convex hp hc hx hv hp' p.2

omit [FiniteDimensional ℝ E] in
/-- **Proposition 13.20(a)**: under twice epi-differentiability `d²f(x̄ | v)` is convex. -/
theorem convex_epigraph_secondSubderivative_of_convex (hc : Convex ℝ (epigraph f)) (hx : f x = c)
    (h : TwiceEpiDifferentiableAt f x v) : Convex ℝ (epigraph (secondSubderivative f x v)) := by
  rw [← h.2.2.inner_eq]
  have hcongr : (fun τ ↦ epigraph (secondDifferenceQuotient f x v τ)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun τ ↦ if 0 < τ then epigraph (secondDifferenceQuotient f x v τ) else univ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [if_pos (show (0 : ℝ) < τ from hτ)]
  rw [innerSetLimitAlong_congr hcongr]
  refine convex_innerSetLimitAlong fun τ ↦ ?_
  split_ifs with hτ
  · exact convex_epigraph_secondDifferenceQuotient hc hx hτ
  · exact convex_univ

end Part_a

/-! ### Gauges of star-shaped sets -/

section Gauges

/-- `C` is star-shaped with respect to `0`: `tC ⊂ C` for `t ∈ [0, 1]`. -/
def IsStarShapedZero (C : Set E) : Prop :=
  ∀ w ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • w ∈ C

/-- `γ_C(x) < a` gives `x = 0`, or `x = λy` with `y ∈ C` and `0 < λ < a`. -/
theorem eq_zero_or_exists_smul_of_gaugeFunction_lt {C : Set E} {x : E} {a : ℝ}
    (h : gaugeFunction C x < a) : x = 0 ∨ ∃ l : ℝ, 0 < l ∧ l < a ∧ ∃ y ∈ C, x = l • y := by
  obtain ⟨r, hr, hra⟩ := exists_mem_positiveHull_epigraph_lt (f := fun x ↦ indicatorVA C x + 1) h
  rcases mem_positiveHull.1 hr with h0 | ⟨l, hl, ⟨y, b⟩, hyb, heq⟩
  · exact Or.inl (congrArg Prod.fst h0)
  · rw [epigraph_indicatorVA_add_one] at hyb
    obtain ⟨hyC, hb⟩ := hyb
    change 1 ≤ b at hb
    have hx : x = l • y := congrArg Prod.fst heq
    have hr' : r = l * b := congrArg Prod.snd heq
    refine Or.inr ⟨l, hl, ?_, y, hyC, hx⟩
    have : l ≤ r := by rw [hr']; nlinarith
    exact lt_of_le_of_lt this (EReal.coe_lt_coe_iff.1 hra)

/-- For a closed set containing `0` that is star-shaped with respect to `0`, `C = {γ_C ≤ 1}`. -/
theorem mem_of_gaugeFunction_le_one {C : Set E} (hC : IsClosed C) (h0 : (0 : E) ∈ C)
    (hstar : IsStarShapedZero C) {w : E} (hw : gaugeFunction C w ≤ 1) : w ∈ C := by
  rw [← hC.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  set η : ℝ := ε / (‖w‖ + 1)
  have hη : 0 < η := by positivity
  have hlt : gaugeFunction C w < ((1 + η : ℝ) : EReal) :=
    lt_of_le_of_lt hw (EReal.coe_lt_coe_iff.2 (by linarith))
  rcases eq_zero_or_exists_smul_of_gaugeFunction_lt hlt with rfl | ⟨l, hl, hl1, y, hyC, rfl⟩
  · exact ⟨0, h0, by simpa using hε⟩
  · by_cases hle : l ≤ 1
    · exact ⟨l • y, hstar y hyC l hl.le hle, by simpa using hε⟩
    · refine ⟨y, hyC, ?_⟩
      push_neg at hle
      rw [dist_eq_norm, ← one_smul ℝ y, smul_smul, mul_one, ← sub_smul, norm_smul,
        Real.norm_of_nonneg (by linarith)]
      have hy : ‖y‖ ≤ ‖l • y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hl.le]
        exact le_mul_of_one_le_left (norm_nonneg y) hle.le
      calc (l - 1) * ‖y‖ ≤ η * ‖l • y‖ :=
            mul_le_mul (by linarith) hy (norm_nonneg y) hη.le
        _ < ε := by
          have : η * (‖l • y‖ + 1) = ε := div_mul_cancel₀ ε (by positivity)
          nlinarith [norm_nonneg (l • y)]

/-- Squares of nonnegative extended reals determine them. -/
theorem ereal_sq_injOn {a b : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  have key : ∀ d : EReal, 0 ≤ d → (d = ⊤ ↔ d ^ 2 = ⊤) := by
    intro d hd
    rcases ereal_trichotomy d with h1 | h1 | ⟨r, h1⟩
    · rw [h1] at hd
      exact absurd hd (not_le.2 EReal.bot_lt_zero)
    · simp [h1, pow_two]
    · rw [h1]
      refine iff_of_false (EReal.coe_ne_top r) ?_
      rw [← EReal.coe_pow]
      exact EReal.coe_ne_top _
  by_cases hat : a = ⊤
  · have hb2 : b ^ 2 = ⊤ := by rw [← h]; exact (key a ha).1 hat
    rw [hat, (key b hb).2 hb2]
  · have hbt : b ≠ ⊤ := fun hbt ↦ hat ((key a ha).2 (h.trans ((key b hb).1 hbt)))
    have hab : a ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero ha)
    have hbb : b ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hb)
    obtain ⟨r, rfl⟩ : ∃ r : ℝ, a = r := ⟨a.toReal, (EReal.coe_toReal hat hab).symm⟩
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, b = t := ⟨b.toReal, (EReal.coe_toReal hbt hbb).symm⟩
    rw [← EReal.coe_pow, ← EReal.coe_pow, EReal.coe_eq_coe_iff] at h
    rw [EReal.coe_nonneg] at ha hb
    rw [EReal.coe_eq_coe_iff]
    nlinarith [sq_nonneg (r - t), sq_nonneg (r + t)]

/-- Closed star-shaped sets containing `0` are determined by the squares of their gauges. -/
theorem eq_of_gaugeFunction_sq_eq {C D : Set E} (hC : IsClosed C) (hC0 : (0 : E) ∈ C)
    (hCs : IsStarShapedZero C) (hD : IsClosed D) (hD0 : (0 : E) ∈ D) (hDs : IsStarShapedZero D)
    (h : ∀ w, gaugeFunction C w ^ 2 = gaugeFunction D w ^ 2) : C = D := by
  have hg : ∀ w, gaugeFunction C w = gaugeFunction D w := fun w ↦
    ereal_sq_injOn (nonneg_gaugeFunction C w) (nonneg_gaugeFunction D w) (h w)
  ext w
  constructor
  · intro hw
    exact mem_of_gaugeFunction_le_one hD hD0 hDs ((hg w) ▸ gaugeFunction_le_one_of_mem hw)
  · intro hw
    exact mem_of_gaugeFunction_le_one hC hC0 hCs ((hg w).symm ▸ gaugeFunction_le_one_of_mem hw)

/-- A set between the unit sphere and the closed unit ball has gauge `‖·‖`. -/
theorem gaugeFunction_eq_norm {C : Set E} (hC : C ⊆ closedBall 0 1) (hS : sphere 0 1 ⊆ C)
    (w : E) : gaugeFunction C w = ‖w‖ := by
  apply le_antisymm
  · rcases eq_or_ne w 0 with rfl | hw
    · simp
    · have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
      refine gaugeFunction_le_of_mem_smul hn.le ⟨‖w‖⁻¹ • w, hS ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      · change ‖w‖ • ‖w‖⁻¹ • w = w
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  · by_contra hlt
    push_neg at hlt
    rcases eq_zero_or_exists_smul_of_gaugeFunction_lt hlt with rfl | ⟨l, hl, hlw, y, hyC, rfl⟩
    · simp at hlt
    · have hy := mem_closedBall_zero_iff.1 (hC hyC)
      rw [norm_smul, Real.norm_of_nonneg hl.le] at hlw
      nlinarith

end Gauges

/-! ### Proposition 13.20(b) -/

section Part_b

variable [FiniteDimensional ℝ E] {f : E → EReal} {x v : E} {c : ℝ}

/-- **Proposition 13.20(b)**: with `C = {w | d²f(x̄ | v)(w) ≤ 1}`, a closed set containing `0`
that is star-shaped with respect to `0`, `d²f(x̄ | v) = γ_C²`. -/
theorem secondSubderivative_eq_gauge_sq (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hx : f x = c) (hv : v ∈ subdifferential f x) :
    IsClosed {w | secondSubderivative f x v w ≤ 1} ∧
      (0 : E) ∈ {w | secondSubderivative f x v w ≤ 1} ∧
      IsStarShapedZero {w | secondSubderivative f x v w ≤ 1} ∧
      ∀ w, secondSubderivative f x v w =
        gaugeFunction {w | secondSubderivative f x v w ≤ 1} w ^ 2 := by
  set h := secondSubderivative f x v with hh
  set C := {w | h w ≤ 1} with hC
  have hnn : ∀ w, 0 ≤ h w := secondSubderivative_nonneg_of_convex hp hc hx hv
  have h0 : h 0 = 0 := le_antisymm (secondSubderivative_zero_le hx) (hnn 0)
  have hsm : ∀ l : ℝ, 0 < l → ∀ w, h (l • w) = ((l ^ 2 : ℝ) : EReal) * h w :=
    fun l hl w ↦ secondSubderivative_smul f x v hl w
  have hclosed : IsClosed C :=
    (lowerSemicontinuous_secondSubderivative f x v).isClosed_preimage 1
  have hC0 : (0 : E) ∈ C := by
    change h 0 ≤ 1
    rw [h0]
    exact zero_le_one
  have hstar : IsStarShapedZero C := by
    intro w hw t ht0 ht1
    rcases eq_or_lt_of_le ht0 with rfl | htpos
    · rw [zero_smul]
      exact hC0
    · change h (t • w) ≤ 1
      rw [hsm t htpos]
      change h w ≤ 1 at hw
      calc ((t ^ 2 : ℝ) : EReal) * h w ≤ ((t ^ 2 : ℝ) : EReal) * 1 :=
            mul_le_mul_of_nonneg_left hw (EReal.coe_nonneg.2 (sq_nonneg t))
        _ ≤ 1 := by
          rw [mul_one, ← EReal.coe_one, EReal.coe_le_coe_iff]
          nlinarith
  refine ⟨hclosed, hC0, hstar, fun w ↦ ?_⟩
  have hgnn := nonneg_gaugeFunction C w
  rcases ereal_trichotomy (h w) with hb | ht | ⟨s, hs⟩
  · exact absurd (hb ▸ hnn w) (by simp)
  · -- `h w = ∞` forces `γ_C(w) = ∞`
    have hg : gaugeFunction C w = ⊤ := by
      by_contra hne
      obtain ⟨a, ha, -⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.2 hne)
      rcases eq_zero_or_exists_smul_of_gaugeFunction_lt ha with rfl | ⟨l, hl, -, y, hyC, rfl⟩
      · rw [h0] at ht
        exact EReal.zero_ne_top ht
      · rw [hsm l hl] at ht
        change h y ≤ 1 at hyC
        have : ((l ^ 2 : ℝ) : EReal) * h y ≤ ((l ^ 2 : ℝ) : EReal) * 1 :=
          mul_le_mul_of_nonneg_left hyC (EReal.coe_nonneg.2 (sq_nonneg l))
        rw [ht, mul_one] at this
        exact EReal.coe_ne_top _ (top_le_iff.1 this)
    rw [ht, hg, pow_two, EReal.top_mul_top]
  · have hs0 : 0 ≤ s := by
      have := hnn w
      rw [hs] at this
      exact EReal.coe_nonneg.1 this
    rcases eq_or_lt_of_le hs0 with rfl | hspos
    · -- `h w = 0` forces `γ_C(w) = 0`
      have hg : gaugeFunction C w = 0 := by
        refine le_antisymm ?_ hgnn
        refine EReal.le_of_forall_lt_iff_le.1 fun a ha ↦ ?_
        have ha' : (0 : ℝ) < a := EReal.coe_pos.1 ha
        refine (gaugeFunction_le_of_mem_smul ha'.le ⟨a⁻¹ • w, ?_, ?_⟩).trans le_rfl
        · change h (a⁻¹ • w) ≤ 1
          rw [hsm _ (inv_pos.2 ha'), hs, EReal.coe_zero, mul_zero]
          exact zero_le_one
        · change a • a⁻¹ • w = w
          rw [smul_smul, mul_inv_cancel₀ ha'.ne', one_smul]
      rw [hs, hg]
      simp
    · -- `h w = s > 0` forces `γ_C(w) = √s`
      have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
      have hg : gaugeFunction C w = Real.sqrt s := by
        apply le_antisymm
        · refine gaugeFunction_le_of_mem_smul hsq.le ⟨(Real.sqrt s)⁻¹ • w, ?_, ?_⟩
          · change h ((Real.sqrt s)⁻¹ • w) ≤ 1
            rw [hsm _ (inv_pos.2 hsq), hs, ← EReal.coe_mul, inv_pow, Real.sq_sqrt hs0,
              inv_mul_cancel₀ hspos.ne', EReal.coe_one]
          · change Real.sqrt s • (Real.sqrt s)⁻¹ • w = w
            rw [smul_smul, mul_inv_cancel₀ hsq.ne', one_smul]
        · by_contra hlt
          push_neg at hlt
          rcases eq_zero_or_exists_smul_of_gaugeFunction_lt hlt with rfl | ⟨l, hl, hls, y, hyC, rfl⟩
          · rw [h0, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at hs
            linarith
          · rw [hsm l hl] at hs
            change h y ≤ 1 at hyC
            have h1 : ((l ^ 2 : ℝ) : EReal) * h y ≤ ((l ^ 2 : ℝ) : EReal) * 1 :=
              mul_le_mul_of_nonneg_left hyC (EReal.coe_nonneg.2 (sq_nonneg l))
            rw [hs, mul_one, EReal.coe_le_coe_iff] at h1
            have h2 : l ^ 2 < s := by
              rw [← Real.sq_sqrt hs0]
              exact pow_lt_pow_left₀ hls hl.le two_ne_zero
            linarith
      rw [hs, hg, ← EReal.coe_pow, Real.sq_sqrt hs0]

/-- **Proposition 13.20(b)**: the set `C` is unique among closed sets containing `0` that are
star-shaped with respect to `0`. -/
theorem secondSubderivative_gauge_unique (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hx : f x = c) (hv : v ∈ subdifferential f x) {D : Set E} (hD : IsClosed D)
    (hD0 : (0 : E) ∈ D) (hDs : IsStarShapedZero D)
    (hDeq : ∀ w, secondSubderivative f x v w = gaugeFunction D w ^ 2) :
    D = {w | secondSubderivative f x v w ≤ 1} := by
  obtain ⟨hC, hC0, hCs, hCeq⟩ := secondSubderivative_eq_gauge_sq hp hc hx hv
  exact eq_of_gaugeFunction_sq_eq hD hD0 hDs hC hC0 hCs fun w ↦ (hDeq w).symm.trans (hCeq w)

omit [FiniteDimensional ℝ E] in
/-- **Proposition 13.20(b)**: under twice epi-differentiability the set `C` is convex. -/
theorem convex_setOf_secondSubderivative_le_one (hc : Convex ℝ (epigraph f)) (hx : f x = c)
    (h : TwiceEpiDifferentiableAt f x v) : Convex ℝ {w | secondSubderivative f x v w ≤ 1} := by
  have hconv := convex_epigraph_secondSubderivative_of_convex hc hx h
  intro a ha b hb s t hs ht hst
  have := hconv (show (a, (1 : ℝ)) ∈ epigraph (secondSubderivative f x v) from ha)
    (show (b, (1 : ℝ)) ∈ epigraph (secondSubderivative f x v) from hb) hs ht hst
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, hst] at this
  exact this

end Part_b

/-! ### The counterexample to uniqueness in 13.20(b) -/

section Uniqueness

/-- The convex function `½‖·‖²`. -/
noncomputable def halfSqNorm (y : E) : EReal := ((‖y‖ ^ 2 / 2 : ℝ) : EReal)

omit [InnerProductSpace ℝ E] in
theorem isProper_halfSqNorm : IsProper (halfSqNorm (E := E)) :=
  ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩

theorem convex_epigraph_halfSqNorm : Convex ℝ (epigraph (halfSqNorm (E := E))) := by
  have h1 : ConvexOn ℝ univ (fun y : E ↦ ‖y‖ ^ 2) := by
    have := (convexOn_univ_norm : ConvexOn ℝ univ (norm : E → ℝ)).pow
      (fun y _ ↦ norm_nonneg y) 2
    simpa only [Pi.pow_apply] using this
  have hconv : ConvexOn ℝ univ (fun y : E ↦ ‖y‖ ^ 2 / 2) := by
    have := h1.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    convert this using 1
    funext y
    simp only [smul_eq_mul]
    ring
  have h := convexOn_iff_convex_epigraph.1 hconv
  convert h using 1
  ext ⟨y, a⟩
  simp [epigraph, halfSqNorm, ge_iff_le]

theorem zero_mem_subdifferential_halfSqNorm :
    (0 : E) ∈ subdifferential (halfSqNorm (E := E)) 0 := by
  have hmin : IsLocalMin (halfSqNorm (E := E)) 0 := Eventually.of_forall fun y ↦ by
    change ((‖(0 : E)‖ ^ 2 / 2 : ℝ) : EReal) ≤ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff, norm_zero]
    have := sq_nonneg ‖y‖
    linarith
  exact regularSubdifferential_subset_subdifferential _ _
    (RW.IsLocalMin.zero_mem_regularSubdifferential hmin (c := 0) (by simp [halfSqNorm]))

/-- `d²(½‖·‖²)(0 | 0) = ‖·‖²`. -/
theorem secondSubderivative_halfSqNorm (w : E) :
    secondSubderivative (halfSqNorm (E := E)) 0 0 w = ((‖w‖ ^ 2 : ℝ) : EReal) := by
  have heq : (fun p : ℝ × E ↦ secondDifferenceQuotient (halfSqNorm (E := E)) 0 0 p.1 p.2)
      =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 w] fun p ↦ ((‖p.2‖ ^ 2 : ℝ) : EReal) := by
    filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
    change 0 < p.1 at hp
    rw [secondDifferenceQuotient_of_coe (c := 0) (r := ‖p.1 • p.2‖ ^ 2 / 2)
      (by simp [halfSqNorm]) (by simp [halfSqNorm]), EReal.coe_eq_coe_iff, inner_zero_left,
      norm_smul, Real.norm_of_nonneg hp.le]
    field_simp
    ring
  have hlim : Tendsto (fun p : ℝ × E ↦ ((‖p.2‖ ^ 2 : ℝ) : EReal)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 ((‖w‖ ^ 2 : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 (((continuous_norm.tendsto w).comp tendsto_snd).pow 2)
  rw [secondSubderivative, liminf_congr heq, hlim.liminf_eq]

/-- **Correction to Proposition 13.20(b)**: for `f = ½‖·‖²` (proper and convex, with
`0 ∈ ∂f(0)`) on a nontrivial space, `d²f(0 | 0) = γ_C²` both for the closed unit ball and for the
closed set `{0} ∪ {‖w‖ = 1}`, two different closed sets containing `0`. -/
theorem gauge_uniqueness_counterexample [Nontrivial E] :
    IsProper (halfSqNorm (E := E)) ∧ Convex ℝ (epigraph (halfSqNorm (E := E))) ∧
      (0 : E) ∈ subdifferential (halfSqNorm (E := E)) 0 ∧
      closedBall (0 : E) 1 ≠ insert 0 (sphere (0 : E) 1) ∧
      IsClosed (closedBall (0 : E) 1) ∧ IsClosed (insert 0 (sphere (0 : E) 1)) ∧
      ∀ w, secondSubderivative (halfSqNorm (E := E)) 0 0 w = gaugeFunction (closedBall 0 1) w ^ 2 ∧
        secondSubderivative (halfSqNorm (E := E)) 0 0 w =
          gaugeFunction (insert 0 (sphere 0 1)) w ^ 2 := by
  refine ⟨isProper_halfSqNorm, convex_epigraph_halfSqNorm, zero_mem_subdifferential_halfSqNorm,
    ?_, isClosed_closedBall, by rw [insert_eq]; exact isClosed_singleton.union isClosed_sphere,
    fun w ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨u, hu⟩ := exists_ne (0 : E)
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
    intro h
    have hmem : (2 * ‖u‖)⁻¹ • u ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_mul, Real.norm_two, norm_norm]
      rw [mul_inv, mul_assoc, inv_mul_cancel₀ hun.ne']
      norm_num
    rw [h] at hmem
    rcases hmem with h0 | hs
    · have : (2 * ‖u‖)⁻¹ ≠ 0 := by positivity
      exact hu ((smul_eq_zero.1 h0).resolve_left this)
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_mul, Real.norm_two, norm_norm,
        mul_inv, mul_assoc, inv_mul_cancel₀ hun.ne'] at hs
      norm_num at hs
  · rw [secondSubderivative_halfSqNorm, gaugeFunction_eq_norm le_rfl sphere_subset_closedBall,
      ← EReal.coe_pow]
  · rw [secondSubderivative_halfSqNorm, gaugeFunction_eq_norm
      (insert_subset (mem_closedBall_self zero_le_one) sphere_subset_closedBall)
      (subset_insert _ _), ← EReal.coe_pow]

end Uniqueness

/-! ### Proposition 13.20(c) -/

section Part_c

/-- "Twice semidifferentiable at `x̄` for `v`" in 13.20(c): the quotients `Δ²_τ f(x̄ | v)`
converge continuously to a finite `d²f(x̄ | v)`. -/
def TwiceSemidifferentiableAtFor (f : E → EReal) (x v : E) : Prop :=
  ∀ w, (secondSubderivative f x v w ≠ ⊥ ∧ secondSubderivative f x v w ≠ ⊤) ∧
    Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 (secondSubderivative f x v w))

/-- Continuous convergence of the quotients 13(5) in the direction `0` alone forces
`d²f(x̄ | v) < ∞` everywhere (the remark after Definition 13.6): the quotients near `(0, 0)` are
below `1`, and the scaling law `Δ²_τ f(x̄ | v)(w') = a⁻² Δ²_{τ/a} f(x̄ | v)(aw')` bounds those near
any `w`. -/
theorem secondSubderivative_ne_top_of_tendsto_zero {f : E → EReal} {x v : E} {c : ℝ}
    (hx : f x = c)
    (h0 : Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) (𝓝 (secondSubderivative f x v 0))) (w : E) :
    secondSubderivative f x v w ≠ ⊤ := by
  have hlt : secondSubderivative f x v 0 < 1 :=
    (secondSubderivative_zero_le hx).trans_lt (by norm_num)
  have hev := h0.eventually (Iio_mem_nhds hlt)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hev
  obtain ⟨δ, hδ, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  have hδ' : (0 : ℝ) < δ := hδ
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hη' : (0 : ℝ) < η := hη
  set a : ℝ := η / (2 * (‖w‖ + 1)) with ha
  have ha0 : 0 < a := by positivity
  have hbound : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      secondDifferenceQuotient f x v p.1 p.2 ≤ ((1 / a ^ 2 : ℝ) : EReal) := by
    have hmem : Ioo (0 : ℝ) (a * δ) ×ˢ ball w 1 ∈ 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w :=
      prod_mem_prod (Ioo_mem_nhdsGT (mul_pos ha0 hδ')) (ball_mem_nhds w one_pos)
    filter_upwards [hmem] with p hp
    obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
    have hτ : p.1 / a ∈ Ioo (0 : ℝ) δ := ⟨div_pos hp0 ha0, by rwa [div_lt_iff₀ ha0, mul_comm]⟩
    have hw : a • p.2 ∈ ball (0 : E) η := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ha0.le]
      have h1 : ‖p.2‖ < ‖w‖ + 1 := by
        have := norm_sub_norm_le p.2 w
        rw [mem_ball, dist_eq_norm] at hp2
        linarith
      calc a * ‖p.2‖ < a * (‖w‖ + 1) := mul_lt_mul_of_pos_left h1 ha0
        _ = η / 2 := by rw [ha]; field_simp
        _ < η := half_lt_self hη'
    have hq : secondDifferenceQuotient f x v (p.1 / a) (a • p.2) < 1 :=
      hUV (show (p.1 / a, a • p.2) ∈ U ×ˢ V from ⟨hIoo hτ, hball hw⟩)
    rw [secondDifferenceQuotient_smul f x v _ ha0.ne', mul_div_cancel₀ _ ha0.ne'] at hq
    rcases ereal_trichotomy (secondDifferenceQuotient f x v p.1 p.2) with h | h | ⟨r, h⟩
    · rw [h]; exact bot_le
    · rw [h, EReal.coe_mul_top_of_pos (by positivity)] at hq
      exact absurd hq (not_lt.2 le_top)
    · rw [h] at hq ⊢
      rw [← EReal.coe_mul, ← EReal.coe_one, EReal.coe_lt_coe_iff] at hq
      rw [EReal.coe_le_coe_iff, le_div_iff₀ (by positivity)]
      linarith
  exact ne_of_lt (lt_of_le_of_lt (liminf_le_of_frequently_le' hbound.frequently)
    (EReal.coe_lt_top _))

variable [FiniteDimensional ℝ E] {f : E → EReal} {x v : E} {c : ℝ}

/-- **Proposition 13.20(c)**: continuous convergence of the quotients to a finite limit is the
same as twice epi-differentiability with `d²f(x̄ | v)` finite everywhere. -/
theorem twiceSemidifferentiableAtFor_iff (hc : Convex ℝ (epigraph f)) (hx : f x = c) :
    TwiceSemidifferentiableAtFor f x v ↔ TwiceEpiDifferentiableAt f x v ∧
      ∀ w, secondSubderivative f x v w ≠ ⊥ ∧ secondSubderivative f x v w ≠ ⊤ := by
  constructor
  · intro h
    refine ⟨⟨by rw [hx]; exact EReal.coe_ne_bot c, by rw [hx]; exact EReal.coe_ne_top c, ?_,
      (epigraph_secondSubderivative f x v).symm⟩, fun w ↦ (h w).1⟩
    refine Subset.antisymm ?_ ?_
    · rw [epigraph_secondSubderivative]
      exact innerSetLimitAlong_subset_outerSetLimitAlong _
    · refine epigraph_subset_innerSetLimitAlong_of_tendsto fun w ↦ ?_
      have h2 := (h w).2.comp (tendsto_pair_const w)
      exact h2
  · rintro ⟨hepi, hfin⟩ w
    refine ⟨hfin w, ?_⟩
    have hdom : w ∉ frontier (effectiveDomain (secondSubderivative f x v)) := by
      have : effectiveDomain (secondSubderivative f x v) = univ :=
        eq_univ_of_forall fun u ↦ lt_top_iff_ne_top.2 (hfin u).2
      rw [this, frontier_univ]
      exact notMem_empty w
    rw [tendsto_iff_seq_tendsto]
    intro p hp
    have hτ : Tendsto (fun n ↦ (p n).1) atTop (𝓝[>] (0 : ℝ)) := tendsto_fst.comp hp
    have hw : Tendsto (fun n ↦ (p n).2) atTop (𝓝 w) := tendsto_snd.comp hp
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hτ.eventually self_mem_nhdsWithin)
    have hτN : Tendsto (fun n ↦ (p (n + N)).1) atTop (𝓝[>] (0 : ℝ)) :=
      hτ.comp (tendsto_add_atTop_nat N)
    have hconv : EpiConverges (fun n ↦ secondDifferenceQuotient f x v (p (n + N)).1)
        (secondSubderivative f x v) :=
      (pkConvergesAlong_iff_forall_seq.1 hepi.2.2) _ hτN
    have hcvx : ∀ n, Convex ℝ (epigraph (secondDifferenceQuotient f x v (p (n + N)).1)) :=
      fun n ↦ convex_epigraph_secondDifferenceQuotient hc hx (hN (n + N) (Nat.le_add_left N n))
    have := hconv.convergesContinuouslyWithinAt_of_notMem_frontier hcvx hdom univ
      (fun n ↦ (p (n + N)).2) (fun _ ↦ mem_univ _) (hw.comp (tendsto_add_atTop_nat N))
    exact (tendsto_add_atTop_iff_nat N).1 this

/-- **Proposition 13.20(c)**: for proper convex `f` and `v ∈ ∂f(x̄)`,
`TwiceSemidifferentiableAtFor f x v` is plain continuous convergence of the quotients
`Δ²_τ f(x̄ | v)` to `d²f(x̄ | v)`.  The finiteness conjunct of the definition is redundant:
`d²f(x̄ | v) ≥ 0` by 13.20(a), and `d²f(x̄ | v) < ∞` by
`secondSubderivative_ne_top_of_tendsto_zero`. -/
theorem twiceSemidifferentiableAtFor_iff_tendsto (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hx : f x = c) (hv : v ∈ subdifferential f x) :
    TwiceSemidifferentiableAtFor f x v ↔
      ∀ w, Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (secondSubderivative f x v w)) := by
  refine ⟨fun h w ↦ (h w).2, fun h w ↦
    ⟨⟨?_, secondSubderivative_ne_top_of_tendsto_zero hx (h 0) w⟩, h w⟩⟩
  exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero
    (secondSubderivative_nonneg_of_convex hp hc hx hv w))

omit [FiniteDimensional ℝ E] in
/-- A direction of finite subderivative is tangent to the domain. -/
theorem mem_tangentCone_effectiveDomain_of_subderivative_lt_top (hx : f x = c) {w : E}
    (hw : subderivative f x w < ⊤) : w ∈ tangentCone (effectiveDomain f) x := by
  obtain ⟨α, hα, -⟩ := EReal.exists_between_coe_real hw
  have hmem : (w, α) ∈ tangentCone (epigraph f) (x, c) := by
    rw [← epigraph_subderivative_eq_tangentCone hx]
    exact hα.le
  obtain ⟨ps, τs, hpsC, hpsx, hτpos, hτ0, hlim⟩ := hmem
  refine ⟨fun n ↦ (ps n).1, τs, fun n ↦ ?_, (continuous_fst.tendsto _).comp hpsx, hτpos, hτ0, ?_⟩
  · change f (ps n).1 < ⊤
    exact lt_of_le_of_lt (hpsC n) (EReal.coe_lt_top _)
  · have := (continuous_fst.tendsto _).comp hlim
    simpa using this

/-- **Proposition 13.20(c)**: twice semidifferentiability for `v` makes `f` differentiable at
`x̄` with `∇f(x̄) = v`, and then `f` is twice semidifferentiable at `x̄` (Definition 13.6(a)). -/
theorem TwiceSemidifferentiableAtFor.differentiable (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hx : f x = c) (h : TwiceSemidifferentiableAtFor f x v) :
    HasERealGradientAt f x (innerSL ℝ v) ∧ TwiceSemidifferentiableAt f x := by
  have hd : ∀ w, subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) := fun w ↦
    subderivative_eq_inner_of_secondSubderivative_finite hx (h w).1.2 (h w).1.1
  -- `x̄` is interior to the domain
  have hdomconv : Convex ℝ (effectiveDomain f) := convex_effectiveDomain_of_convex_epigraph hc
  have hxdom : x ∈ effectiveDomain f := by
    change f x < ⊤
    rw [hx]
    exact EReal.coe_lt_top c
  have hT : tangentCone (effectiveDomain f) x = univ := eq_univ_of_forall fun w ↦
    mem_tangentCone_effectiveDomain_of_subderivative_lt_top hx
      (by rw [hd]; exact EReal.coe_lt_top _)
  have hint : x ∈ interior (effectiveDomain f) := by
    have h0 : (0 : E) ∈ interior (tangentCone (effectiveDomain f) x) := by
      rw [hT, interior_univ]
      exact mem_univ 0
    rw [interior_tangentCone_of_convex hdomconv hxdom] at h0
    obtain ⟨l, -, hl⟩ := h0
    simpa using hl
  have hs : SemidifferentiableAt f x :=
    (semidifferentiableAt_of_convex_of_mem_interior hp hc hint).2.2.2
  have hsemi : ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((⟪v, w⟫_ℝ : ℝ) : EReal)) := fun w ↦ by
    have := (hs w).hasSemiderivative.2.2
    rwa [hd w] at this
  obtain ⟨hfin, ho⟩ := isLittleO_of_forall_tendsto hx (g := fun w ↦ ⟪v, w⟫_ℝ)
    (continuous_const.inner continuous_id) (fun a _ w ↦ real_inner_smul_right v w a) hsemi
  have hgrad : HasERealGradientAt f x (innerSL ℝ v) := by
    refine ⟨by rw [hx]; exact EReal.coe_ne_bot c, by rw [hx]; exact EReal.coe_ne_top c, hfin, ?_⟩
    have hxr : (f x).toReal = c := by rw [hx, EReal.toReal_coe]
    simpa only [innerSL_apply_apply, hxr] using ho
  refine ⟨hgrad, hs, fun w ↦ ?_⟩
  rw [secondSubderivativeAt_eq_secondSubderivative_of_subderivative_eq hd]
  have heq : (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2) =
      fun p ↦ secondDifferenceQuotient f x v p.1 p.2 :=
    funext fun p ↦ secondDifferenceQuotientAt_eq_of_subderivative_eq (hd p.2)
  rw [heq]
  exact (h w).2

/-- **Proposition 13.20**, all three parts (with the corrected uniqueness clause in (b)). -/
theorem second_subderivatives_of_convex_functions (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hx : f x = c) (hv : v ∈ subdifferential f x) :
    (∀ w, 0 ≤ secondSubderivative f x v w) ∧
    (TwiceEpiDifferentiableAt f x v → Convex ℝ (epigraph (secondSubderivative f x v))) ∧
    (IsClosed {w | secondSubderivative f x v w ≤ 1} ∧
      (0 : E) ∈ {w | secondSubderivative f x v w ≤ 1} ∧
      IsStarShapedZero {w | secondSubderivative f x v w ≤ 1} ∧
      (∀ w, secondSubderivative f x v w =
        gaugeFunction {w | secondSubderivative f x v w ≤ 1} w ^ 2) ∧
      (∀ D : Set E, IsClosed D → (0 : E) ∈ D → IsStarShapedZero D →
        (∀ w, secondSubderivative f x v w = gaugeFunction D w ^ 2) →
          D = {w | secondSubderivative f x v w ≤ 1}) ∧
      (TwiceEpiDifferentiableAt f x v → Convex ℝ {w | secondSubderivative f x v w ≤ 1})) ∧
    ((TwiceSemidifferentiableAtFor f x v ↔ TwiceEpiDifferentiableAt f x v ∧
      ∀ w, secondSubderivative f x v w ≠ ⊥ ∧ secondSubderivative f x v w ≠ ⊤) ∧
      (TwiceSemidifferentiableAtFor f x v →
        HasERealGradientAt f x (innerSL ℝ v) ∧ TwiceSemidifferentiableAt f x)) := by
  obtain ⟨hC, hC0, hCs, hCeq⟩ := secondSubderivative_eq_gauge_sq hp hc hx hv
  exact ⟨secondSubderivative_nonneg_of_convex hp hc hx hv,
    convex_epigraph_secondSubderivative_of_convex hc hx,
    ⟨hC, hC0, hCs, hCeq, fun D hD hD0 hDs hDeq ↦
      secondSubderivative_gauge_unique hp hc hx hv hD hD0 hDs hDeq,
      convex_setOf_secondSubderivative_le_one hc hx⟩,
    twiceSemidifferentiableAtFor_iff hc hx, fun h ↦ h.differentiable hp hc hx⟩

end Part_c

end RW
