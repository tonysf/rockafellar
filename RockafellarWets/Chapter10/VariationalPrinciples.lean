/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: variational principles for subgradients

* **Proposition 10.44**: if `f` is lsc with `inf f` finite and `f(x̄) ≤ inf f + ε`, then for
  every `δ > 0` there are `x̃` with `|x̃ - x̄| ≤ ε/δ`, `f(x̃) ≤ f(x̄)` and `ṽ ∈ ∂f(x̃)` with
  `|ṽ| ≤ δ` (`exists_small_subgradient_of_le_inf_add`).
* **Exercise 10.45**: if `f(x̄) < inf f + ε`, then for every `δ > 0` there are `x̃` with
  `|x̃ - x̄| < ε/δ`, `f(x̃) < inf f + ε` and a regular subgradient `ṽ ∈ ∂̂f(x̃)` with `|ṽ| < δ`
  (`exists_small_regularSubgradient_of_lt_inf_add`).

The variational principle 1.43 used in the book is not available in the library; in finite
dimensions the needed form (`exists_ekeland_point`) follows by minimizing the lsc function
`f + δ|· - x̄|` over the compact ball `IB(x̄, ε/δ)`, outside of which it exceeds `f(x̄)`.  Then,
as in the book, Fermat's rule 10.1, the sum rule 10.10 and the Lipschitz bound on subgradients
of `δ|· - x̃|` give 10.44, and 10.45 follows from 10.44 with smaller `ε` and `δ` and the
approximation of subgradients by regular subgradients (Definition 8.3).
-/

import RockafellarWets.Chapter10.FermatRule
import RockafellarWets.Chapter10.LipschitzSums
import RockafellarWets.Chapter9.StrictContinuityCriteria
import RockafellarWets.Chapter8.SubderivativeFormulas
import RockafellarWets.Chapter5.ProximalMappings

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Ekeland's principle in finite dimensions, in the form used in 10.44: a point `x₁` within
`ε/δ` of an `ε`-minimizer `x₀`, no worse than `x₀`, minimizing `f + δ|· - x₁|`. -/
theorem exists_ekeland_point {f : E → EReal} (hl : LowerSemicontinuous f) {m ε δ : ℝ}
    (hm : ∀ x, (m : EReal) ≤ f x) (hε : 0 < ε) (hδ : 0 < δ) {x₀ : E}
    (hx₀ : f x₀ ≤ ((m + ε : ℝ) : EReal)) :
    ∃ x₁, ‖x₁ - x₀‖ ≤ ε / δ ∧ f x₁ ≤ f x₀ ∧
      ∀ x, f x₁ ≤ f x + ((δ * ‖x - x₁‖ : ℝ) : EReal) := by
  set φ : E → EReal := fun x ↦ f x + ((δ * ‖x - x₀‖ : ℝ) : EReal) with hφ
  have hφl : LowerSemicontinuous φ :=
    lowerSemicontinuous_add_coe hl (continuous_const.mul (continuous_id.sub continuous_const).norm)
  have hK : (closedBall x₀ (ε / δ)).Nonempty := nonempty_closedBall.2 (by positivity)
  obtain ⟨x₁, hx₁K, hmin⟩ := (hφl.lowerSemicontinuousOn _).exists_isMinOn hK
    (isCompact_closedBall x₀ (ε / δ))
  rw [isMinOn_iff] at hmin
  have hφx₀ : φ x₀ = f x₀ := by simp [hφ]
  have hglob : ∀ x, φ x₁ ≤ φ x := by
    intro x
    by_cases hx : x ∈ closedBall x₀ (ε / δ)
    · exact hmin x hx
    · refine (hmin x₀ (mem_closedBall_self (by positivity))).trans ?_
      rw [hφx₀]
      rw [mem_closedBall, dist_eq_norm, not_le, div_lt_iff₀ hδ] at hx
      refine hx₀.trans ?_
      calc ((m + ε : ℝ) : EReal) ≤ (m : EReal) + ((δ * ‖x - x₀‖ : ℝ) : EReal) := by
            rw [← EReal.coe_add, EReal.coe_le_coe_iff]
            linarith
        _ ≤ φ x := add_le_add (hm x) le_rfl
  have hfx₁ : f x₁ ≤ φ x₁ := by
    show f x₁ ≤ f x₁ + ((δ * ‖x₁ - x₀‖ : ℝ) : EReal)
    exact le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity))
  refine ⟨x₁, by simpa [mem_closedBall, dist_eq_norm] using hx₁K,
    hfx₁.trans ((hglob x₀).trans hφx₀.le), fun x ↦ ?_⟩
  -- `f x₁` is finite
  have hfx₁_top : f x₁ ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (hfx₁.trans ((hglob x₀).trans (hφx₀.le.trans hx₀)))
  have hfx₁_bot : f x₁ ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hm x₁)
  by_cases hfx : f x = ⊤
  · rw [hfx, EReal.top_add_coe]
    exact le_top
  have hfx_bot : f x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hm x)
  have h1 := hglob x
  simp only [hφ] at h1
  rw [← EReal.coe_toReal hfx₁_top hfx₁_bot, ← EReal.coe_toReal hfx hfx_bot] at h1 ⊢
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have htri : ‖x - x₀‖ ≤ ‖x - x₁‖ + ‖x₁ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub x x₁ x₀
  nlinarith

/-- **Proposition 10.44** (variational principle for subgradients). -/
theorem exists_small_subgradient_of_le_inf_add {f : E → EReal} (hl : LowerSemicontinuous f)
    {m : ℝ} (hinf : ⨅ x, f x = (m : EReal)) {ε : ℝ} (hε : 0 < ε) {x₀ : E}
    (hx₀ : f x₀ ≤ ((m + ε : ℝ) : EReal)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x₁, ‖x₁ - x₀‖ ≤ ε / δ ∧ f x₁ ≤ f x₀ ∧ ∃ v ∈ subdifferential f x₁, ‖v‖ ≤ δ := by
  have hm : ∀ x, (m : EReal) ≤ f x := fun x ↦ hinf ▸ iInf_le f x
  obtain ⟨x₁, h1, h2, h3⟩ := exists_ekeland_point hl hm hε hδ hx₀
  refine ⟨x₁, h1, h2, ?_⟩
  have hfx₁_top : f x₁ ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (h2.trans hx₀)
  have hfx₁_bot : f x₁ ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hm x₁)
  set c := (f x₁).toReal with hc
  have hfc : f x₁ = (c : EReal) := (EReal.coe_toReal hfx₁_top hfx₁_bot).symm
  set G : E → EReal := fun x ↦ ((δ * ‖x - x₁‖ : ℝ) : EReal) with hG
  have hGL : LipschitzWith ⟨δ, hδ.le⟩ (fun x ↦ δ * ‖x - x₁‖) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mk, ← mul_sub, abs_mul, abs_of_pos hδ]
    refine mul_le_mul_of_nonneg_left ?_ hδ.le
    have := abs_norm_sub_norm_le (x - x₁) (y - x₁)
    rwa [sub_sub_sub_cancel_right] at this
  have hGsc : ERealStrictlyContinuousAt G x₁ := eRealStrictlyContinuousAt_coe_of_lipschitz hGL
  have hprop : IsProper f :=
    ⟨⟨x₀, lt_of_le_of_lt hx₀ (EReal.coe_lt_top _)⟩, fun x ↦ lt_of_lt_of_le (EReal.bot_lt_coe m) (hm x)⟩
  have hmin : IsLocalMin (G + f) x₁ := Eventually.of_forall fun x ↦ by
    show G x₁ + f x₁ ≤ G x + f x
    simp only [hG, sub_self, norm_zero, mul_zero, EReal.coe_zero, zero_add]
    rw [add_comm]
    exact h3 x
  have hval : (G + f) x₁ = (c : EReal) := by
    show G x₁ + f x₁ = (c : EReal)
    simp only [hG, sub_self, norm_zero, mul_zero, EReal.coe_zero, zero_add]
    exact hfc
  have h0 := IsLocalMin.zero_mem_subdifferential hmin hval
  obtain ⟨u, hu, w, hw, huw⟩ :=
    subdifferential_add_subset_of_strictlyContinuous hGsc hl hprop hfc h0
  have hu_le : ‖u‖ ≤ δ := by
    have hGr : (fun y ↦ (G y).toReal) = fun y ↦ δ * ‖y - x₁‖ :=
      funext fun y ↦ EReal.toReal_coe _
    have hfin : ∀ y ∈ (univ : Set E), G y = ((G y).toReal : EReal) := fun y _ ↦ by
      simp only [hG, EReal.toReal_coe]
    have hLip : LipschitzOnWith ⟨δ, hδ.le⟩ (fun y ↦ (G y).toReal) univ := by
      rw [hGr]
      exact hGL.lipschitzOnWith
    exact norm_le_of_mem_subdifferential_of_lipschitzOnWith isOpen_univ hfin hLip (mem_univ x₁) hu
  refine ⟨w, hw, ?_⟩
  have hw' : w = -u := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact huw
  rw [hw', norm_neg]
  exact hu_le

/-- **Exercise 10.45** (variational principle for regular subgradients). -/
theorem exists_small_regularSubgradient_of_lt_inf_add {f : E → EReal}
    (hl : LowerSemicontinuous f) {m : ℝ} (hinf : ⨅ x, f x = (m : EReal)) {ε : ℝ} (hε : 0 < ε)
    {x₀ : E} (hx₀ : f x₀ < ((m + ε : ℝ) : EReal)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x₁, ‖x₁ - x₀‖ < ε / δ ∧ f x₁ < ((m + ε : ℝ) : EReal) ∧
      ∃ v ∈ regularSubdifferential f x₁, ‖v‖ < δ := by
  have hm : ∀ x, (m : EReal) ≤ f x := fun x ↦ hinf ▸ iInf_le f x
  have hx₀_top : f x₀ ≠ ⊤ := ne_top_of_lt hx₀
  have hx₀_bot : f x₀ ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hm x₀)
  set a := (f x₀).toReal with ha
  have hfa : f x₀ = (a : EReal) := (EReal.coe_toReal hx₀_top hx₀_bot).symm
  have hma : m ≤ a := by have := hm x₀; rw [hfa] at this; exact_mod_cast this
  have haε : a < m + ε := by have := hx₀; rw [hfa] at this; exact_mod_cast this
  set ε' := max (a - m) (ε / 2) with hε'
  have hε'pos : 0 < ε' := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hε'lt : ε' < ε := max_lt (by linarith) (by linarith)
  set δ' := δ * (ε' + ε) / (2 * ε) with hδ'
  have hδ'pos : 0 < δ' := by positivity
  have hδ'lt : δ' < δ := by
    rw [hδ', div_lt_iff₀ (by positivity)]
    nlinarith
  have hratio : ε' / δ' < ε / δ := by
    rw [div_lt_div_iff₀ hδ'pos hδ, hδ']
    field_simp
    nlinarith
  have hx₀' : f x₀ ≤ ((m + ε' : ℝ) : EReal) := by
    rw [hfa, EReal.coe_le_coe_iff]
    linarith [le_max_left (a - m) (ε / 2)]
  obtain ⟨x₁, h1, h2, v, hv, hvδ⟩ :=
    exists_small_subgradient_of_le_inf_add hl hinf hε'pos hx₀' hδ'pos
  obtain ⟨-, xs, vs, hxs, hfxs, hvs, hvlim⟩ := mem_subdifferential_iff_exists_seq.1 hv
  have hev1 : ∀ᶠ n in atTop, ‖xs n - x₀‖ < ε / δ :=
    ((continuous_norm.tendsto _).comp (hxs.sub_const x₀)).eventually
      (gt_mem_nhds (lt_of_le_of_lt h1 hratio))
  have hev2 : ∀ᶠ n in atTop, f (xs n) < ((m + ε : ℝ) : EReal) :=
    hfxs.eventually (gt_mem_nhds (lt_of_le_of_lt h2 hx₀))
  have hev3 : ∀ᶠ n in atTop, ‖vs n‖ < δ :=
    ((continuous_norm.tendsto _).comp hvlim).eventually (gt_mem_nhds (lt_of_le_of_lt hvδ hδ'lt))
  obtain ⟨n, hn1, hn2, hn3⟩ := (hev1.and (hev2.and hev3)).exists
  exact ⟨xs n, hn1, hn2, vs n, hvs n, hn3⟩

end RW
