/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Subderivatives and the basic subgradient formulas

* Definition 8.1: `df(x̄)` is the lower epi-limit of the difference quotients
  (`subderivative_eq_lowerEpiDerivative`), and the upper subderivative is
  `-d(-f)(x̄)` (`neg_subderivative_neg`).  Formula 8(1) is
  `epigraph_differenceQuotient` and Theorem 8.2(a) is
  `epigraph_subderivative_eq_tangentCone`, both in
  `Chapter7/EpiDerivatives.lean`.
* Theorem 8.2(b): `dδ_C(x̄) = δ_K` with `K = T_C(x̄)`
  (`subderivative_indicatorVA`).
* The formulas attached to Definition 8.3: the regular subgradient inequality
  in the limit form 8(4) (`mem_regularSubdifferential_iff_liminf`), and the
  sequential reading 8.3(b) of the limiting subdifferential defined through
  the outer limit 8(5) (`mem_subdifferential_iff_exists_seq`).
* Proposition 8.5, first statement: regular subgradients are the gradients at
  `x̄` of differentiable minorants touching `f` at `x̄`
  (`mem_regularSubdifferential_iff_exists_hasGradientAt`).  The refinement to a
  smooth minorant that is strict away from `x̄` is not formalized here.
-/

import RockafellarWets.Chapter8.RegularSubgradientBridge
import RockafellarWets.Chapter7.EpiDerivativeCounterexample
import Mathlib.Analysis.Calculus.Gradient.Basic

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

/-! ### Definition 8.1 and Theorem 8.2(b) -/

section Subderivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 8.1**: `df(x̄)` is the lower epi-limit of the difference
quotients as `τ ↓ 0`. -/
theorem subderivative_eq_lowerEpiDerivative (f : E → EReal) (x : E) :
    subderivative f x = lowerEpiDerivative f x :=
  (lowerEpiDerivative_eq_subderivative f x).symm

/-- **Definition 8.1**: the upper subderivative is `-d(-f)(x̄)`. -/
theorem neg_subderivative_neg {f : E → EReal} {x : E} (hx : f x ≠ ⊥) (hx' : f x ≠ ⊤)
    (w : E) : -subderivative (fun y ↦ -f y) x w = upperSemiderivative f x w := by
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx' hx).symm
  have hfun : (fun p : ℝ × E ↦ differenceQuotient (fun y ↦ -f y) x p.1 p.2) =
      -(fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) := by
    funext p
    exact differenceQuotient_neg hxc p.1 p.2
  rw [subderivative, upperSemiderivative, hfun, EReal.liminf_neg, neg_neg]

/-- **Theorem 8.2(b)**: for `x̄ ∈ C`, `dδ_C(x̄) = δ_K` with `K = T_C(x̄)`. -/
theorem subderivative_indicatorVA {C : Set E} {x : E} (hx : x ∈ C) :
    subderivative (indicatorVA C) x = indicatorVA (tangentCone C x) := by
  have hx0 : indicatorVA C x = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem hx, EReal.coe_zero]
  have hval : ∀ τ : ℝ, 0 < τ → ∀ w',
      differenceQuotient (indicatorVA C) x τ w' = indicatorVA (blowUp C x τ) w' := by
    intro τ hτ w'
    have hmem : x + τ • w' ∈ C ↔ w' ∈ blowUp C x τ := by
      constructor
      · intro h
        refine ⟨x + τ • w', h, ?_⟩
        show τ⁻¹ • (x + τ • w' - x) = w'
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
      · rintro ⟨y, hy, rfl⟩
        rwa [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
    by_cases h : x + τ • w' ∈ C
    · rw [differenceQuotient_eq_coe (r := 0) hx0 (by rw [indicatorVA_apply_mem h, EReal.coe_zero]),
        indicatorVA_apply_mem (hmem.1 h)]
      simp
    · rw [differenceQuotient_eq_top hτ hx0 (indicatorVA_apply_not_mem h),
        indicatorVA_apply_not_mem fun h' ↦ h (hmem.2 h')]
  funext w
  by_cases hw : w ∈ tangentCone C x
  · rw [indicatorVA_apply_mem hw]
    apply le_antisymm
    · apply liminf_le_of_frequently_le'
      rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨U₁, hU₁, V, hV, hUV⟩ := mem_prod_iff.1 hU
      rw [tangentCone_eq_outerSetLimitAlong] at hw
      obtain ⟨τ, ⟨⟨w', hw'B, hw'V⟩, hτU⟩, hτpos⟩ :=
        (((hw V hV).and_eventually hU₁).and_eventually self_mem_nhdsWithin).exists
      refine ⟨(τ, w'), hUV ⟨hτU, hw'V⟩, ?_⟩
      exact le_of_eq (by rw [hval τ hτpos, indicatorVA_apply_mem hw'B])
    · refine le_liminf_of_le (h := ?_)
      filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
      rw [hval p.1 hp]
      by_cases h : p.2 ∈ blowUp C x p.1
      · exact le_of_eq (indicatorVA_apply_mem h).symm
      · rw [indicatorVA_apply_not_mem h]
        exact le_top
  · rw [indicatorVA_apply_not_mem hw]
    rw [tangentCone_eq_outerSetLimitAlong, not_mem_outerSetLimitAlong] at hw
    obtain ⟨V, hV, hev⟩ := hw
    apply top_le_iff.1
    refine le_liminf_of_le (h := ?_)
    filter_upwards [tendsto_fst.eventually (hev.and self_mem_nhdsWithin),
      tendsto_snd.eventually hV] with p hp hpV
    have hnot : p.2 ∉ blowUp C x p.1 := fun hB ↦ by
      have hne : (blowUp C x p.1 ∩ V).Nonempty := ⟨p.2, hB, hpV⟩
      rw [hp.1] at hne
      exact hne.ne_empty rfl
    exact le_of_eq (by rw [hval p.1 hp.2, indicatorVA_apply_not_mem hnot])

end Subderivatives

/-! ### Formula 8(4) -/

section RegularSubgradients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An `EReal` form of the inequality `r ≤ (a - s)/t` for `t > 0`. -/
theorem coe_le_inv_mul_sub_iff {t s r : ℝ} (ht : 0 < t) {a : EReal} :
    (r : EReal) ≤ ((t⁻¹ : ℝ) : EReal) * (a - s) ↔ ((s + t * r : ℝ) : EReal) ≤ a := by
  cases a with
  | bot =>
    rw [EReal.bot_sub, EReal.coe_mul_bot_of_pos (inv_pos.2 ht)]
    constructor <;> intro h
    · exact absurd (le_bot_iff.1 h) (EReal.coe_ne_bot r)
    · exact absurd (le_bot_iff.1 h) (EReal.coe_ne_bot _)
  | top =>
    rw [EReal.top_sub_coe, EReal.coe_mul_top_of_pos (inv_pos.2 ht)]
    exact ⟨fun _ ↦ le_top, fun _ ↦ le_top⟩
  | coe a =>
    rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
      le_inv_mul_iff₀ ht]
    constructor <;> intro h <;> linarith

/-- **Formula 8(4)**: the regular subgradient inequality 8(3) in limit form,
`liminf_{x → x̄, x ≠ x̄} [f(x) - f(x̄) - ⟪v, x - x̄⟫]/|x - x̄| ≥ 0`. -/
theorem mem_regularSubdifferential_iff_liminf {f : E → EReal} {x v : E} {c : ℝ}
    (hxc : f x = c) :
    v ∈ regularSubdifferential f x ↔
      0 ≤ liminf (fun y ↦ ((‖y - x‖⁻¹ : ℝ) : EReal) *
        (f y - ((c + ⟪v, y - x⟫_ℝ : ℝ) : EReal))) (𝓝[≠] x) := by
  constructor
  · rintro ⟨c', hc', hreg⟩
    have hcc : c' = c := by
      rw [hxc] at hc'
      exact (EReal.coe_injective hc').symm
    subst hcc
    by_contra hneg
    push_neg at hneg
    obtain ⟨b, hb1, hb2⟩ := EReal.exists_between_coe_real hneg
    have hb : b < 0 := by exact_mod_cast hb2
    have hev : ∀ᶠ y in 𝓝[≠] x, (b : EReal) ≤ ((‖y - x‖⁻¹ : ℝ) : EReal) *
        (f y - ((c' + ⟪v, y - x⟫_ℝ : ℝ) : EReal)) := by
      filter_upwards [nhdsWithin_le_nhds (hreg (-b) (by linarith)), self_mem_nhdsWithin]
        with y hy hyx
      have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
      rw [coe_le_inv_mul_sub_iff hpos]
      convert hy using 2
      ring
    exact lt_irrefl _ (hb1.trans_le (le_liminf_of_le (h := hev)))
  · intro hlim
    refine ⟨c, hxc, fun ε hε ↦ ?_⟩
    have hlt : ((-ε : ℝ) : EReal) < liminf (fun y ↦ ((‖y - x‖⁻¹ : ℝ) : EReal) *
        (f y - ((c + ⟪v, y - x⟫_ℝ : ℝ) : EReal))) (𝓝[≠] x) :=
      lt_of_lt_of_le (by exact_mod_cast (show -ε < (0 : ℝ) by linarith)) hlim
    have hev := eventually_lt_of_lt_liminf hlt
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with y hy
    rcases eq_or_ne y x with rfl | hyx
    · rw [hxc]
      simp
    · have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
      have h1 := (hy hyx).le
      rw [coe_le_inv_mul_sub_iff hpos] at h1
      convert h1 using 2
      ring

end RegularSubgradients

/-! ### The sequential reading of Definition 8.3(b) -/

section Sequences

/-- Along a countably generated index filter, outer limits are limits of
sequences of selections. -/
theorem mem_outerSetLimitAlong_iff_exists_seq {ι F : Type*} [TopologicalSpace F]
    [FirstCountableTopology F] {l : Filter ι} [l.IsCountablyGenerated] {S : ι → Set F} {v : F} :
    v ∈ outerSetLimitAlong l S ↔ ∃ (xs : ℕ → ι) (vs : ℕ → F), Tendsto xs atTop l ∧
      (∀ n, vs n ∈ S (xs n)) ∧ Tendsto vs atTop (𝓝 v) := by
  constructor
  · intro hv
    obtain ⟨U, hU⟩ := l.exists_antitone_basis
    obtain ⟨V, hV⟩ := (𝓝 v).exists_antitone_basis
    have hpick : ∀ n, ∃ i ∈ U n, (S i ∩ V n).Nonempty := fun n ↦
      Filter.frequently_iff.1 (hv (V n) (hV.mem n)) (hU.mem n)
    choose xs hxsU hxsS using hpick
    choose vs hvs using hxsS
    exact ⟨xs, vs, hU.tendsto hxsU, fun n ↦ (hvs n).1, hV.tendsto fun n ↦ (hvs n).2⟩
  · rintro ⟨xs, vs, hxs, hvs, hvto⟩ V hV
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨n, hn1, hn2⟩ := ((hxs.eventually hU).and (hvto.eventually hV)).exists
    exact ⟨xs n, hn1, vs n, hvs n, hn2⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

instance attentiveNhds_isCountablyGenerated (f : E → EReal) (x : E) :
    (attentiveNhds f x).IsCountablyGenerated := by
  unfold attentiveNhds
  infer_instance

/-- **Definition 8.3(b)** read through formula 8(5): `v ∈ ∂f(x̄)` exactly when
there are `xν →_f x̄` and regular subgradients `vν ∈ ∂̂f(xν)` with `vν → v`. -/
theorem mem_subdifferential_iff_exists_seq {f : E → EReal} {x v : E} :
    v ∈ subdifferential f x ↔ (∃ c : ℝ, f x = c) ∧ ∃ (xs vs : ℕ → E),
      Tendsto xs atTop (𝓝 x) ∧ Tendsto (f ∘ xs) atTop (𝓝 (f x)) ∧
      (∀ n, vs n ∈ regularSubdifferential f (xs n)) ∧ Tendsto vs atTop (𝓝 v) := by
  rw [subdifferential, mem_setOf_eq, mem_outerSetLimitAlong_iff_exists_seq]
  simp only [tendsto_attentiveNhds_iff]
  constructor
  · rintro ⟨hc, xs, vs, ⟨h1, h2⟩, h3, h4⟩
    exact ⟨hc, xs, vs, h1, h2, h3, h4⟩
  · rintro ⟨hc, xs, vs, h1, h2, h3, h4⟩
    exact ⟨hc, xs, vs, ⟨h1, h2⟩, h3, h4⟩

end Sequences

/-! ### Proposition 8.5 -/

section Minorants

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Classical in
/-- **Proposition 8.5**, first statement: `v ∈ ∂̂f(x̄)` if and only if on some
neighborhood of `x̄` there is a function `h ≤ f` with `h(x̄) = f(x̄)` that is
differentiable at `x̄` with `∇h(x̄) = v`. -/
theorem mem_regularSubdifferential_iff_exists_hasGradientAt {f : E → EReal} {x v : E}
    {c : ℝ} (hxc : f x = c) :
    v ∈ regularSubdifferential f x ↔
      ∃ h : E → ℝ, (∀ᶠ y in 𝓝 x, (h y : EReal) ≤ f y) ∧ h x = c ∧ HasGradientAt h v x := by
  constructor
  · rintro ⟨c', hc', hreg⟩
    have hcc : c' = c := by
      rw [hxc] at hc'
      exact (EReal.coe_injective hc').symm
    subst hcc
    set g : E → ℝ := fun y ↦ if f y = ⊤ then 0 else max (c' + ⟪v, y - x⟫_ℝ - (f y).toReal) 0
      with hg_def
    have hg_bound : ∀ ε > 0, ∀ᶠ y in 𝓝 x, 0 ≤ g y ∧ g y ≤ ε * ‖y - x‖ ∧
        (((c' + ⟪v, y - x⟫_ℝ - g y : ℝ) : EReal) ≤ f y) := by
      intro ε hε
      filter_upwards [hreg ε hε] with y hy
      by_cases htop : f y = ⊤
      · simp only [hg_def, htop, if_true, sub_zero, le_refl, true_and, le_top, and_true]
        positivity
      · have hbot : f y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hy
        have hfy : f y = (((f y).toReal : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
        rw [hfy, EReal.coe_le_coe_iff] at hy
        simp only [hg_def, htop, if_false]
        refine ⟨le_max_right _ _, max_le (by linarith) (by positivity), ?_⟩
        refine le_trans (EReal.coe_le_coe_iff.2 ?_) (le_of_eq hfy.symm)
        linarith [le_max_left (c' + ⟪v, y - x⟫_ℝ - (f y).toReal) 0]
    refine ⟨fun y ↦ c' + ⟪v, y - x⟫_ℝ - g y, ?_, ?_, ?_⟩
    · filter_upwards [hg_bound 1 one_pos] with y hy
      exact hy.2.2
    · simp [hg_def, hc']
    · rw [hasGradientAt_iff_hasFDerivAt]
      refine hasFDerivAtFilter_iff_isLittleO.2 ?_
      have hgx : g x = 0 := by simp [hg_def, hc']
      refine Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_
      filter_upwards [hg_bound ε hε] with y hy
      show ‖(c' + ⟪v, y - x⟫_ℝ - g y) - (c' + ⟪v, x - x⟫_ℝ - g x) -
        (InnerProductSpace.toDual ℝ E v) (y - x)‖ ≤ ε * ‖y - x‖
      rw [InnerProductSpace.toDual_apply_apply, hgx, sub_self, inner_zero_right, Real.norm_eq_abs]
      have : c' + ⟪v, y - x⟫_ℝ - g y - (c' + 0 - 0) - ⟪v, y - x⟫_ℝ = -g y := by ring
      rw [this, abs_neg, abs_of_nonneg hy.1]
      exact hy.2.1
  · rintro ⟨h, hle, hx, hgrad⟩
    refine ⟨c, hxc, fun ε hε ↦ ?_⟩
    have hlo := hasFDerivAtFilter_iff_isLittleO.1 (hasGradientAt_iff_hasFDerivAt.1 hgrad)
    filter_upwards [Asymptotics.isLittleO_iff.1 hlo hε, hle] with y hy hyle
    have hy' : ‖h y - h x - (InnerProductSpace.toDual ℝ E v) (y - x)‖ ≤ ε * ‖y - x‖ := hy
    rw [InnerProductSpace.toDual_apply_apply, hx, Real.norm_eq_abs] at hy'
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hyle
    have := neg_abs_le (h y - c - ⟪v, y - x⟫_ℝ)
    linarith [hy']

end Minorants

end RW
