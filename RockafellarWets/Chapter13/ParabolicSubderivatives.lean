/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Parabolic subderivatives

Section 13J: Definition 13.59, Example 13.60, Example 13.62, Proposition 13.64,
Definition 13.65 and Theorem 13.66.

The parabolic difference quotient uses the same inf-addition convention as
13(4), of which it is the case `z = 0`.  The lower limit with
`[w' - w]/τ` bounded in 13.64 is the infimum over `R` of the lower limits
along the filters `boundedRatioFilter w R` of pairs `(τ, w')` with
`τ ↓ 0`, `w' → w` and `‖w' - w‖ ≤ Rτ`.
-/

import RockafellarWets.Chapter13.SecondOrderTangents
import RockafellarWets.Chapter13.SecondOrderOptimality
import RockafellarWets.Chapter13.SmoothAddition
import RockafellarWets.Chapter8.SubderivativeFormulas

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Definition 13.59 -/

section Definition1359

/-- The parabolic difference quotient
`Δ²_τ f(x̄)(w | z) = [f(x̄ + τw + ½τ²z) - f(x̄) - τ df(x̄)(w)] / (½τ²)`. -/
noncomputable def parabolicDifferenceQuotient (f : E → EReal) (x w : E) (τ : ℝ) (z : E) : EReal :=
  ((2 / τ ^ 2 : ℝ) : EReal) *
    infAddition (f (x + τ • w + (τ ^ 2 / 2) • z) - f x) (-((τ : EReal) * subderivative f x w))

/-- **Definition 13.59**: the parabolic subderivative
`d²f(x̄)(w | z) = liminf_{τ ↓ 0, z' → z} Δ²_τ f(x̄)(w | z')`. -/
noncomputable def parabolicSubderivative (f : E → EReal) (x w z : E) : EReal :=
  liminf (fun p : ℝ × E ↦ parabolicDifferenceQuotient f x w p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z)

/-- **Definition 13.59**: `f` is parabolically epi-differentiable at `x̄` for `w` (with
`f(x̄)` and `df(x̄)(w)` finite) when the quotients `Δ²_τ f(x̄)(w | ·)` epi-converge to
`d²f(x̄)(w | ·)` and this function is not identically `∞`. -/
def IsParabolicallyEpiDifferentiableAt (f : E → EReal) (x w : E) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ subderivative f x w ≠ ⊥ ∧ subderivative f x w ≠ ⊤ ∧
    (∃ z, parabolicSubderivative f x w z < ⊤) ∧
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (parabolicDifferenceQuotient f x w τ))
      (epigraph (parabolicSubderivative f x w))

/-- **Definition 13.59**: `d²f(x̄)(w | ·)` is the lower epi-limit of the parabolic quotients. -/
theorem epigraph_parabolicSubderivative (f : E → EReal) (x w : E) :
    epigraph (parabolicSubderivative f x w) =
      outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (parabolicDifferenceQuotient f x w τ)) :=
  epigraph_liminf_prod _ _

/-- With `z = 0` the parabolic quotient is the quotient 13(4). -/
theorem parabolicDifferenceQuotient_zero (f : E → EReal) (x w : E) (τ : ℝ) :
    parabolicDifferenceQuotient f x w τ 0 = secondDifferenceQuotientAt f x τ w := by
  rw [parabolicDifferenceQuotient, secondDifferenceQuotientAt, smul_zero, add_zero]

/-- The parabolic quotient when `df(x̄)(w) = β` is finite. -/
theorem parabolicDifferenceQuotient_of_subderivative_eq {f : E → EReal} {x w : E} {β : ℝ}
    (hd : subderivative f x w = β) (τ : ℝ) (z : E) :
    parabolicDifferenceQuotient f x w τ z = ((2 / τ ^ 2 : ℝ) : EReal) *
      (f (x + τ • w + (τ ^ 2 / 2) • z) - f x - ((τ * β : ℝ) : EReal)) := by
  rw [parabolicDifferenceQuotient, hd, ← EReal.coe_mul, ← EReal.coe_neg, infAddition_coe_right,
    EReal.coe_neg, ← sub_eq_add_neg]

/-- The epigraph form of the discussion after 13.59: a parabolic quotient is the parabolic
difference set of the epigraph. -/
theorem epigraph_parabolicDifferenceQuotient {f : E → EReal} {x w : E} {α β : ℝ}
    (hx : f x = α) (hd : subderivative f x w = β) {τ : ℝ} (hτ : τ ≠ 0) :
    epigraph (parabolicDifferenceQuotient f x w τ) =
      parabolicBlowUp (epigraph f) (x, α) (w, β) τ := by
  have hτ2 : (0 : ℝ) < 2 / τ ^ 2 := by positivity
  ext ⟨z, γ⟩
  rw [mem_epigraph_iff, mem_parabolicBlowUp_iff hτ,
    parabolicDifferenceQuotient_of_subderivative_eq hd, hx]
  change _ ↔ f (x + τ • w + (τ ^ 2 / 2) • z) ≤ ((α + τ * β + τ ^ 2 / 2 * γ : ℝ) : EReal)
  rcases ereal_trichotomy (f (x + τ • w + (τ ^ 2 / 2) • z)) with h | h | ⟨r, h⟩
  · rw [h, EReal.bot_sub, EReal.bot_sub, EReal.coe_mul_bot_of_pos hτ2]
    simp
  · rw [h, EReal.top_sub_coe, EReal.top_sub_coe, EReal.coe_mul_top_of_pos hτ2]
    exact iff_of_false (fun h ↦ EReal.coe_ne_top _ (top_le_iff.1 h))
      (fun h ↦ EReal.coe_ne_top _ (top_le_iff.1 h))
  · rw [h, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff,
      EReal.coe_le_coe_iff, ← sub_nonneg, ← sub_nonneg (a := α + τ * β + τ ^ 2 / 2 * γ)]
    have hτ2' : 0 < τ ^ 2 := by positivity
    constructor
    · intro hle
      have : 0 ≤ τ ^ 2 / 2 * (γ - 2 / τ ^ 2 * (r - α - τ * β)) := mul_nonneg (by positivity) hle
      have heq : τ ^ 2 / 2 * (γ - 2 / τ ^ 2 * (r - α - τ * β)) = α + τ * β + τ ^ 2 / 2 * γ - r := by
        field_simp
        ring
      linarith
    · intro hle
      have : 0 ≤ 2 / τ ^ 2 * (α + τ * β + τ ^ 2 / 2 * γ - r) := mul_nonneg hτ2.le hle
      have heq : 2 / τ ^ 2 * (α + τ * β + τ ^ 2 / 2 * γ - r) = γ - 2 / τ ^ 2 * (r - α - τ * β) := by
        field_simp
        ring
      linarith

end Definition1359

/-! ### Example 13.62 -/

section Example1362

/-- **Example 13.62(b)**: with `α = f(x̄)` and `β = df(x̄)(w)` finite,
`epi d²f(x̄)(w | ·) = T²_{epi f}((x̄, α) | (w, β))`. -/
theorem epigraph_parabolicSubderivative_eq_secondOrderTangentSet {f : E → EReal} {x w : E}
    {α β : ℝ} (hx : f x = α) (hd : subderivative f x w = β) :
    epigraph (parabolicSubderivative f x w) = secondOrderTangentSet (epigraph f) (x, α) (w, β) := by
  rw [epigraph_parabolicSubderivative, secondOrderTangentSet]
  apply outerSetLimitAlong_congr
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact epigraph_parabolicDifferenceQuotient hx hd (ne_of_gt hτ)

/-- **Example 13.62(b)**: parabolic epi-differentiability of `f` at `x̄` for `w` is parabolic
derivability of `epi f` at `(x̄, α)` for `(w, β)`. -/
theorem isParabolicallyEpiDifferentiableAt_iff {f : E → EReal} {x w : E} {α β : ℝ}
    (hx : f x = α) (hd : subderivative f x w = β) :
    IsParabolicallyEpiDifferentiableAt f x w ↔
      IsParabolicallyDerivable (epigraph f) (x, α) (w, β) := by
  have hcongr : (fun τ ↦ epigraph (parabolicDifferenceQuotient f x w τ)) =ᶠ[𝓝[>] (0 : ℝ)]
      parabolicBlowUp (epigraph f) (x, α) (w, β) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact epigraph_parabolicDifferenceQuotient hx hd (ne_of_gt hτ)
  have hT := epigraph_parabolicSubderivative_eq_secondOrderTangentSet hx hd
  have hdom : (∃ z, parabolicSubderivative f x w z < ⊤) ↔
      (secondOrderTangentSet (epigraph f) (x, α) (w, β)).Nonempty := by
    rw [← hT]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨γ, hγ, -⟩ := EReal.exists_between_coe_real hz
      exact ⟨(z, γ), hγ.le⟩
    · rintro ⟨⟨z, γ⟩, hzγ⟩
      exact ⟨z, lt_of_le_of_lt hzγ (EReal.coe_lt_top γ)⟩
  unfold IsParabolicallyEpiDifferentiableAt IsParabolicallyDerivable PKConvergesAlong
  rw [innerSetLimitAlong_congr hcongr, outerSetLimitAlong_congr hcongr, hT, hdom, hx, hd]
  simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true, EReal.coe_ne_top, true_and]

omit [InnerProductSpace ℝ E] in
/-- Lower limits of indicators are indicators of outer limits. -/
theorem liminf_indicatorVA_prod {ι : Type*} {l : Filter ι} (S : ι → Set E) (z : E) :
    liminf (fun p : ι × E ↦ indicatorVA (S p.1) p.2) (l ×ˢ 𝓝 z) =
      indicatorVA (outerSetLimitAlong l S) z := by
  by_cases hz : z ∈ outerSetLimitAlong l S
  · rw [indicatorVA_apply_mem hz]
    refine le_antisymm (liminf_le_of_frequently_le' ?_) (le_liminf_of_le (h := ?_))
    · rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.1 hU
      obtain ⟨i, ⟨z', hz'S, hz'B⟩, hiA⟩ := ((hz B hB).and_eventually hA).exists
      exact ⟨(i, z'), hAB ⟨hiA, hz'B⟩, by rw [indicatorVA_apply_mem hz'S]⟩
    · exact Eventually.of_forall fun p ↦ by
        unfold indicatorVA
        split_ifs <;> simp
  · rw [indicatorVA_apply_not_mem hz]
    obtain ⟨V, hV, hev⟩ := not_mem_outerSetLimitAlong.1 hz
    refine eq_top_iff.2 (le_liminf_of_le (h := ?_))
    filter_upwards [prod_mem_prod hev hV] with p hp
    have : p.2 ∉ S p.1 := fun h ↦ (show S p.1 ∩ V = ∅ from hp.1).subset ⟨h, hp.2⟩
    rw [indicatorVA_apply_not_mem this]

/-- **Example 13.62(a)**: for `x̄ ∈ C` and `w ∈ T_C(x̄)`, `d²δ_C(x̄)(w | ·) = δ_{T²_C(x̄ | w)}`. -/
theorem parabolicSubderivative_indicatorVA {C : Set E} {x w : E} (hx : x ∈ C)
    (hw : w ∈ tangentCone C x) :
    parabolicSubderivative (indicatorVA C) x w = indicatorVA (secondOrderTangentSet C x w) := by
  have hx0 : indicatorVA C x = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem hx, EReal.coe_zero]
  have hd : subderivative (indicatorVA C) x w = ((0 : ℝ) : EReal) := by
    rw [subderivative_indicatorVA hx, indicatorVA_apply_mem hw, EReal.coe_zero]
  funext z
  have heq : (fun p : ℝ × E ↦ parabolicDifferenceQuotient (indicatorVA C) x w p.1 p.2)
      =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 z] fun p ↦ indicatorVA (parabolicBlowUp C x w p.1) p.2 := by
    filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
    change 0 < p.1 at hp
    rw [parabolicDifferenceQuotient_of_subderivative_eq hd, hx0, mul_zero, EReal.coe_zero,
      sub_zero, sub_zero]
    by_cases hmem : x + p.1 • w + (p.1 ^ 2 / 2) • p.2 ∈ C
    · rw [indicatorVA_apply_mem hmem, indicatorVA_apply_mem
        ((mem_parabolicBlowUp_iff hp.ne').2 hmem), mul_zero]
    · rw [indicatorVA_apply_not_mem hmem, indicatorVA_apply_not_mem
        (mt (mem_parabolicBlowUp_iff hp.ne').1 hmem), EReal.coe_mul_top_of_pos (by positivity)]
  rw [parabolicSubderivative, liminf_congr heq, liminf_indicatorVA_prod]
  rfl

variable {ι : Type*}

omit [InnerProductSpace ℝ E] in
theorem outerSetLimitAlong_prod_Ici {l : Filter ι} (A : ι → Set E) :
    outerSetLimitAlong l (fun i ↦ A i ×ˢ Ici (0 : ℝ)) = outerSetLimitAlong l A ×ˢ Ici 0 := by
  ext ⟨z, γ⟩
  constructor
  · intro h
    refine ⟨fun V hV ↦ (h (V ×ˢ univ) (prod_mem_nhds hV univ_mem)).mono
      fun i ⟨q, hq, hqV⟩ ↦ ⟨q.1, hq.1, hqV.1⟩, ?_⟩
    by_contra hγ
    have hγ' : γ < 0 := lt_of_not_ge hγ
    have := h (univ ×ˢ Iio 0) (prod_mem_nhds univ_mem (Iio_mem_nhds hγ'))
    obtain ⟨i, q, hq, hqV⟩ := this.exists
    exact absurd (show (0 : ℝ) ≤ q.2 from hq.2) (not_le.2 hqV.2)
  · rintro ⟨hz, hγ⟩ N hN
    obtain ⟨V, hV, I, hI, hVI⟩ := mem_nhds_prod_iff.1 hN
    exact (hz V hV).mono fun i ⟨z', hz'A, hz'V⟩ ↦
      ⟨(z', γ), ⟨hz'A, hγ⟩, hVI ⟨hz'V, mem_of_mem_nhds hI⟩⟩

omit [InnerProductSpace ℝ E] in
theorem innerSetLimitAlong_prod_Ici {l : Filter ι} [l.NeBot] (A : ι → Set E) :
    innerSetLimitAlong l (fun i ↦ A i ×ˢ Ici (0 : ℝ)) = innerSetLimitAlong l A ×ˢ Ici 0 := by
  ext ⟨z, γ⟩
  constructor
  · intro h
    refine ⟨fun V hV ↦ (h (V ×ˢ univ) (prod_mem_nhds hV univ_mem)).mono
      fun i ⟨q, hq, hqV⟩ ↦ ⟨q.1, hq.1, hqV.1⟩, ?_⟩
    by_contra hγ
    have hγ' : γ < 0 := lt_of_not_ge hγ
    have := h (univ ×ˢ Iio 0) (prod_mem_nhds univ_mem (Iio_mem_nhds hγ'))
    obtain ⟨i, q, hq, hqV⟩ := this.exists
    exact absurd (show (0 : ℝ) ≤ q.2 from hq.2) (not_le.2 hqV.2)
  · rintro ⟨hz, hγ⟩ N hN
    obtain ⟨V, hV, I, hI, hVI⟩ := mem_nhds_prod_iff.1 hN
    exact (hz V hV).mono fun i ⟨z', hz'A, hz'V⟩ ↦
      ⟨(z', γ), ⟨hz'A, hγ⟩, hVI ⟨hz'V, mem_of_mem_nhds hI⟩⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem prod_Ici_injective {A B : Set E} (h : A ×ˢ Ici (0 : ℝ) = B ×ˢ Ici 0) : A = B := by
  ext z
  constructor
  · intro hz
    exact (h ▸ (show (z, (0 : ℝ)) ∈ A ×ˢ Ici 0 from ⟨hz, self_mem_Ici⟩)).1
  · intro hz
    exact (h.symm ▸ (show (z, (0 : ℝ)) ∈ B ×ˢ Ici 0 from ⟨hz, self_mem_Ici⟩)).1

/-- **Example 13.62(a)**: parabolic epi-differentiability of `δ_C` at `x̄` for `w ∈ T_C(x̄)` is
parabolic derivability of `C` at `x̄` for `w`. -/
theorem isParabolicallyEpiDifferentiableAt_indicatorVA_iff {C : Set E} {x w : E} (hx : x ∈ C)
    (hw : w ∈ tangentCone C x) :
    IsParabolicallyEpiDifferentiableAt (indicatorVA C) x w ↔ IsParabolicallyDerivable C x w := by
  have hd : subderivative (indicatorVA C) x w = ((0 : ℝ) : EReal) := by
    rw [subderivative_indicatorVA hx, indicatorVA_apply_mem hw, EReal.coe_zero]
  have hcongr : (fun τ ↦ epigraph (parabolicDifferenceQuotient (indicatorVA C) x w τ))
      =ᶠ[𝓝[>] (0 : ℝ)] fun τ ↦ parabolicBlowUp C x w τ ×ˢ Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : (0 : ℝ) < τ := hτ
    rw [← epigraph_indicatorVA]
    congr 1
    funext z
    rw [parabolicDifferenceQuotient_of_subderivative_eq hd, indicatorVA_apply_mem hx, mul_zero,
      EReal.coe_zero, sub_zero, sub_zero]
    by_cases hmem : x + τ • w + (τ ^ 2 / 2) • z ∈ C
    · rw [indicatorVA_apply_mem hmem, indicatorVA_apply_mem
        ((mem_parabolicBlowUp_iff hτ'.ne').2 hmem), mul_zero]
    · rw [indicatorVA_apply_not_mem hmem, indicatorVA_apply_not_mem
        (mt (mem_parabolicBlowUp_iff hτ'.ne').1 hmem), EReal.coe_mul_top_of_pos (by positivity)]
  have hT : epigraph (parabolicSubderivative (indicatorVA C) x w) =
      secondOrderTangentSet C x w ×ˢ Ici (0 : ℝ) := by
    rw [parabolicSubderivative_indicatorVA hx hw, epigraph_indicatorVA]
  unfold IsParabolicallyEpiDifferentiableAt IsParabolicallyDerivable PKConvergesAlong
  rw [innerSetLimitAlong_congr hcongr, outerSetLimitAlong_congr hcongr,
    innerSetLimitAlong_prod_Ici, outerSetLimitAlong_prod_Ici, hT, hd, indicatorVA_apply_mem hx,
    parabolicSubderivative_indicatorVA hx hw]
  have hdom : (∃ z, indicatorVA (secondOrderTangentSet C x w) z < ⊤) ↔
      (secondOrderTangentSet C x w).Nonempty := by
    constructor
    · rintro ⟨z, hz⟩
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      rw [indicatorVA_apply_not_mem (by rw [hne]; exact notMem_empty z)] at hz
      exact lt_irrefl _ hz
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [indicatorVA_apply_mem hz]; exact EReal.zero_lt_top⟩
  rw [hdom]
  simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true, EReal.coe_ne_top, true_and,
    EReal.zero_ne_bot, EReal.zero_ne_top]
  constructor
  · rintro ⟨hne, hin, -⟩
    exact ⟨hne, prod_Ici_injective hin, rfl⟩
  · rintro ⟨hne, hin, -⟩
    exact ⟨hne, by rw [hin], rfl⟩

end Example1362

/-! ### Example 13.60 -/

section Example1360

omit [InnerProductSpace ℝ E] in
/-- Pointwise convergence of a family of functions puts the epigraph of the limit inside the
inner limit of the epigraphs. -/
theorem epigraph_subset_innerSetLimitAlong_of_tendsto {ι : Type*} {l : Filter ι}
    {g : ι → E → EReal} {G : E → EReal} (hg : ∀ z, Tendsto (fun i ↦ g i z) l (𝓝 (G z))) :
    epigraph G ⊆ innerSetLimitAlong l (fun i ↦ epigraph (g i)) := by
  rintro ⟨z, α⟩ hzα N hN
  change G z ≤ (α : EReal) at hzα
  obtain ⟨V, hV, I, hI, hVI⟩ := mem_nhds_prod_iff.1 hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hI
  have hlt : G z < ((α + ε / 2 : ℝ) : EReal) :=
    lt_of_le_of_lt hzα (EReal.coe_lt_coe_iff.2 (by linarith))
  filter_upwards [(hg z).eventually (Iio_mem_nhds hlt)] with i hi
  refine ⟨(z, α + ε / 2), le_of_lt hi, hVI ⟨mem_of_mem_nhds hV, hball ?_⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
  linarith

/-- The parabolic quotients of a function twice differentiable at `x̄` (classical sense)
converge continuously to `w ↦ f''(w)(w) + ⟪∇f(x̄), z⟫`. -/
theorem tendsto_parabolicDifferenceQuotient_of_hasFDerivAt {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E →L[ℝ] E →L[ℝ] ℝ} {x v : E} (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hf' : HasFDerivAt f' f'' x) (hv : ∀ w, f' x w = ⟪v, w⟫_ℝ) (w z : E) :
    Tendsto (fun p : ℝ × E ↦ parabolicDifferenceQuotient (fun y ↦ (f y : EReal)) x w p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 ((f'' w w + ⟪v, z⟫_ℝ : ℝ) : EReal)) := by
  have hd : subderivative (fun y ↦ (f y : EReal)) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) := by
    rw [(hf.self_of_nhds.hasDirectionalSemiderivative w).subderivative_eq, hv]
  have hpath : Tendsto (fun p : ℝ × E ↦ (p.1, w + (p.1 / 2) • p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := by
    refine tendsto_fst.prodMk ?_
    have h0 : Tendsto (fun p : ℝ × E ↦ p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 0) :=
      tendsto_fst.mono_right nhdsWithin_le_nhds
    have h1 : Tendsto (fun p : ℝ × E ↦ p.1 / 2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 0) := by
      simpa using h0.div_const (2 : ℝ)
    simpa using tendsto_const_nhds.add (h1.smul tendsto_snd)
  have hQ := (tendsto_secondDifferenceQuotient_of_hasFDerivAt hf hf' hv w).comp hpath
  have hinner : Tendsto (fun p : ℝ × E ↦ ⟪v, p.2⟫_ℝ) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 ⟪v, z⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto z).comp tendsto_snd
  refine EReal.tendsto_coe.2 (hQ.add hinner) |>.congr' ?_
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  change 0 < p.1 at hp
  rw [parabolicDifferenceQuotient_of_subderivative_eq hd, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_mul, Function.comp_apply, EReal.coe_eq_coe_iff]
  have hpt : x + p.1 • (w + (p.1 / 2) • p.2) = x + p.1 • w + (p.1 ^ 2 / 2) • p.2 := by
    rw [smul_add, smul_smul, add_assoc]
    congr 3
    ring
  simp only
  rw [hpt, inner_add_right, real_inner_smul_right]
  field_simp
  ring

/-- **Example 13.60**: a `C²` function is parabolically epi-differentiable at every `x̄` for
every `w`, with `d²f(x̄)(w | z) = ⟪w, ∇²f(x̄)w⟫ + ⟪∇f(x̄), z⟫`. -/
theorem parabolic_aspects_of_twice_smooth [CompleteSpace E] {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x w : E) :
    IsParabolicallyEpiDifferentiableAt (fun y ↦ (f y : EReal)) x w ∧
      ∀ z, parabolicSubderivative (fun y ↦ (f y : EReal)) x w z =
        ((fderiv ℝ (fderiv ℝ f) x w w + ⟪gradient f x, z⟫_ℝ : ℝ) : EReal) := by
  have hf₀ : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y :=
    Eventually.of_forall (hasFDerivAt_fderiv_of_contDiff_two hf)
  have hf₀' := hasFDerivAt_fderiv_fderiv_of_contDiff_two hf x
  have hv := fderiv_apply_eq_inner_gradient f x
  have hlim := tendsto_parabolicDifferenceQuotient_of_hasFDerivAt hf₀ hf₀' hv w
  have hval : ∀ z, parabolicSubderivative (fun y ↦ (f y : EReal)) x w z =
      ((fderiv ℝ (fderiv ℝ f) x w w + ⟪gradient f x, z⟫_ℝ : ℝ) : EReal) :=
    fun z ↦ (hlim z).liminf_eq
  have hd : subderivative (fun y ↦ (f y : EReal)) x w = ((⟪gradient f x, w⟫_ℝ : ℝ) : EReal) := by
    rw [(hf₀.self_of_nhds.hasDirectionalSemiderivative w).subderivative_eq, hv]
  have hepi := epigraph_parabolicSubderivative (fun y ↦ (f y : EReal)) x w
  have hpt : ∀ z, Tendsto (fun τ ↦ parabolicDifferenceQuotient (fun y ↦ (f y : EReal)) x w τ z)
      (𝓝[>] (0 : ℝ)) (𝓝 (parabolicSubderivative (fun y ↦ (f y : EReal)) x w z)) := by
    intro z
    have h1 : Tendsto (fun τ ↦ parabolicDifferenceQuotient (fun y ↦ (f y : EReal)) x w τ z)
        (𝓝[>] (0 : ℝ)) (𝓝 ((fderiv ℝ (fderiv ℝ f) x w w + ⟪gradient f x, z⟫_ℝ : ℝ) : EReal)) :=
      by
        have h2 := (hlim z).comp (tendsto_pair_const z)
        exact h2
    rwa [← hval z] at h1
  have hin := epigraph_subset_innerSetLimitAlong_of_tendsto hpt
  have hout : innerSetLimitAlong (𝓝[>] (0 : ℝ))
      (fun τ ↦ epigraph (parabolicDifferenceQuotient (fun y ↦ (f y : EReal)) x w τ)) ⊆
        epigraph (parabolicSubderivative (fun y ↦ (f y : EReal)) x w) := by
    rw [hepi]
    exact innerSetLimitAlong_subset_outerSetLimitAlong _
  refine ⟨⟨EReal.coe_ne_bot (f x), EReal.coe_ne_top (f x), ?_, ?_, ⟨0, ?_⟩,
    Subset.antisymm hout hin, hepi.symm⟩, hval⟩
  · rw [hd]
    exact EReal.coe_ne_bot _
  · rw [hd]
    exact EReal.coe_ne_top _
  · rw [hval]
    exact EReal.coe_lt_top _

end Example1360

/-! ### Proposition 13.64 -/

section Proposition1364

/-- **Proposition 13.64**: `d²f(x̄)(w | ·)` is lower semicontinuous. -/
theorem lowerSemicontinuous_parabolicSubderivative (f : E → EReal) (x w : E) :
    LowerSemicontinuous (parabolicSubderivative f x w) :=
  lowerSemicontinuous_liminf_prod _ _

/-- The identity behind 13(39): when `df(x̄)(w) = ⟪v, w⟫`,
`Δ²_τ f(x̄)(w | z) - ⟪v, z⟫ = Δ²_τ f(x̄ | v)(w + ½τz)`. -/
theorem parabolicDifferenceQuotient_sub_inner {f : E → EReal} {x w v : E} {c : ℝ}
    (hx : f x = c) (hd : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) {τ : ℝ} (hτ : τ ≠ 0)
    (z : E) :
    parabolicDifferenceQuotient f x w τ z - ((⟪v, z⟫_ℝ : ℝ) : EReal) =
      secondDifferenceQuotient f x v τ (w + (τ / 2) • z) := by
  have hpt : x + τ • (w + (τ / 2) • z) = x + τ • w + (τ ^ 2 / 2) • z := by
    rw [smul_add, smul_smul, add_assoc]
    congr 3
    ring
  rw [parabolicDifferenceQuotient_of_subderivative_eq hd]
  rcases ereal_trichotomy (f (x + τ • w + (τ ^ 2 / 2) • z)) with h | h | ⟨r, h⟩
  · rw [secondDifferenceQuotient_of_bot hτ hx (by rw [hpt, h]), h, EReal.bot_sub, EReal.bot_sub,
      EReal.coe_mul_bot_of_pos (by positivity), EReal.bot_sub]
  · rw [secondDifferenceQuotient_of_top hτ hx (by rw [hpt, h]), h, hx, EReal.top_sub_coe,
      EReal.top_sub_coe, EReal.coe_mul_top_of_pos (by positivity), EReal.top_sub_coe]
  · rw [secondDifferenceQuotient_of_coe hx (by rw [hpt, h]), h, hx, ← EReal.coe_sub,
      ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_eq_coe_iff, inner_add_right,
      real_inner_smul_right]
    field_simp
    ring

/-- **Proposition 13.64**, the substitution `w' = w + ½τz`:
`d²f(x̄)(w | z) - ⟪v, z⟫` is the lower limit of `Δ²_τ f(x̄ | v)(w + ½τz')` as `τ ↓ 0`, `z' → z`. -/
theorem parabolicSubderivative_sub_inner_eq_liminf {f : E → EReal} {x w v : E} {c : ℝ}
    (hx : f x = c) (hd : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) (z : E) :
    parabolicSubderivative f x w z - ((⟪v, z⟫_ℝ : ℝ) : EReal) =
      liminf (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 (w + (p.1 / 2) • p.2))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) := by
  have hinner : Tendsto (fun p : ℝ × E ↦ ((-⟪v, p.2⟫_ℝ : ℝ) : EReal)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z)
      (𝓝 ((-⟪v, z⟫_ℝ : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 ((((continuous_const.inner continuous_id).tendsto z).comp
      tendsto_snd).neg)
  rw [sub_eq_add_neg, ← EReal.coe_neg, parabolicSubderivative,
    ← liminf_add_of_tendsto_coe hinner]
  apply liminf_congr
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  rw [← parabolicDifferenceQuotient_sub_inner hx hd (ne_of_gt hp), EReal.coe_neg,
    ← sub_eq_add_neg]

/-- The substitution path `(τ, z') ↦ (τ, w + ½τz')` tends to the joint filter at `w`. -/
theorem tendsto_parabolic_path (w z : E) :
    Tendsto (fun p : ℝ × E ↦ (p.1, w + (p.1 / 2) • p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := by
  refine tendsto_fst.prodMk ?_
  have h0 : Tendsto (fun p : ℝ × E ↦ p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have h1 : Tendsto (fun p : ℝ × E ↦ p.1 / 2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 0) := by
    simpa using h0.div_const (2 : ℝ)
  simpa using tendsto_const_nhds.add (h1.smul tendsto_snd)

/-- **Proposition 13.64**, formula 13(39): if `df(x̄)(w) = ⟪v, w⟫` then
`d²f(x̄)(w | z) - ⟪v, z⟫ ≥ d²f(x̄ | v)(w)` for every `z`. -/
theorem secondSubderivative_le_parabolicSubderivative_sub_inner {f : E → EReal} {x w v : E}
    {c : ℝ} (hx : f x = c) (hd : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) (z : E) :
    secondSubderivative f x v w ≤ parabolicSubderivative f x w z - ((⟪v, z⟫_ℝ : ℝ) : EReal) := by
  rw [parabolicSubderivative_sub_inner_eq_liminf hx hd, secondSubderivative]
  change _ ≤ liminf ((fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2) ∘
    (fun p : ℝ × E ↦ (p.1, w + (p.1 / 2) • p.2))) _
  rw [liminf_comp]
  exact liminf_le_liminf_of_le (tendsto_parabolic_path w z)

/-- **Proposition 13.64**, formula 13(39). -/
theorem secondSubderivative_le_iInf_parabolicSubderivative {f : E → EReal} {x w v : E} {c : ℝ}
    (hx : f x = c) (hd : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) :
    secondSubderivative f x v w ≤
      ⨅ z, (parabolicSubderivative f x w z - ((⟪v, z⟫_ℝ : ℝ) : EReal)) :=
  le_iInf fun z ↦ secondSubderivative_le_parabolicSubderivative_sub_inner hx hd z

/-- The filter of `τ ↓ 0`, `w' → w` with `‖w' - w‖ ≤ Rτ`, i.e. `[w' - w]/τ` bounded by `R`. -/
def boundedRatioFilter (w : E) (R : ℝ) : Filter (ℝ × E) :=
  (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) ⊓ 𝓟 {p | ‖p.2 - w‖ ≤ R * p.1}

/-- Lower limits along the bounded-ratio filters dominate `d²f(x̄)(w | z) - ⟪v, z⟫` once the
bound exceeds `‖z‖/2`. -/
theorem liminf_boundedRatioFilter_le {f : E → EReal} {x w v : E} {c : ℝ} (hx : f x = c)
    (hd : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) (z : E) :
    liminf (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
        (boundedRatioFilter w (‖z‖ / 2 + 1)) ≤
      parabolicSubderivative f x w z - ((⟪v, z⟫_ℝ : ℝ) : EReal) := by
  rw [parabolicSubderivative_sub_inner_eq_liminf hx hd]
  change _ ≤ liminf ((fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2) ∘
    (fun p : ℝ × E ↦ (p.1, w + (p.1 / 2) • p.2))) _
  rw [liminf_comp]
  refine liminf_le_liminf_of_le (tendsto_inf.2 ⟨tendsto_parabolic_path w z, ?_⟩)
  rw [tendsto_principal]
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin,
    tendsto_snd.eventually (ball_mem_nhds z one_pos)] with p hp hz'
  change 0 < p.1 at hp
  rw [dist_eq_norm] at hz'
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity)]
  have : ‖p.2‖ ≤ ‖z‖ + 1 := by linarith [norm_sub_norm_le p.2 z]
  nlinarith

/-- **Proposition 13.64**: when `df(x̄)(w) = ⟪v, w⟫`, the left side of 13(39),
`inf_z [d²f(x̄)(w | z) - ⟪v, z⟫]`, equals the lower limit of `Δ²_τ f(x̄ | v)(w')` as `τ ↓ 0` and
`w' → w` with `[w' - w]/τ` bounded, i.e. the infimum over `R` of the lower limits along
`boundedRatioFilter w R`; the right side `d²f(x̄ | v)(w)` is the same lower limit without the
boundedness. -/
theorem iInf_parabolicSubderivative_sub_inner_eq [FiniteDimensional ℝ E] {f : E → EReal}
    {x w v : E} {c : ℝ} (hx : f x = c) (hd : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) :
    ⨅ z, (parabolicSubderivative f x w z - ((⟪v, z⟫_ℝ : ℝ) : EReal)) =
      ⨅ R : ℝ, liminf (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
        (boundedRatioFilter w R) := by
  apply le_antisymm
  · refine le_iInf fun R ↦ ?_
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs1, hs2⟩ := EReal.exists_between_coe_real hcon
    have hall : ∀ z, (s : EReal) < liminf
        (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 (w + (p.1 / 2) • p.2))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) := fun z ↦ by
      rw [← parabolicSubderivative_sub_inner_eq_liminf hx hd]
      exact lt_of_lt_of_le hs2 (iInf_le _ z)
    set K : Set E := closedBall (0 : E) (2 * |R|)
    have hK : IsCompact K := isCompact_closedBall 0 _
    have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝ˢ K,
        (s : EReal) < secondDifferenceQuotient f x v p.1 (w + (p.1 / 2) • p.2) :=
      hK.mem_prod_nhdsSet_of_forall fun z _ ↦ eventually_lt_of_lt_liminf (hall z)
    have hψ : Tendsto (fun p : ℝ × E ↦ (p.1, (2 / p.1) • (p.2 - w))) (boundedRatioFilter w R)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝ˢ K) := by
      have hle : boundedRatioFilter w R ≤ 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w := inf_le_left
      refine (tendsto_fst.mono_left hle).prodMk ?_
      refine Tendsto.mono_right ?_ principal_le_nhdsSet
      rw [tendsto_principal]
      filter_upwards [inf_le_right (a := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (mem_principal_self _),
        (tendsto_fst.mono_left hle).eventually self_mem_nhdsWithin] with p hp hτ
      change 0 < p.1 at hτ
      change ‖p.2 - w‖ ≤ R * p.1 at hp
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
      calc 2 / p.1 * ‖p.2 - w‖ ≤ 2 / p.1 * (R * p.1) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = 2 * R := by field_simp
        _ ≤ 2 * |R| := by linarith [le_abs_self R]
    have hev' := hψ.eventually hev
    have hle : (s : EReal) ≤ liminf (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
        (boundedRatioFilter w R) := by
      refine le_liminf_of_le (h := ?_)
      have hpos : ∀ᶠ p in boundedRatioFilter w R, 0 < p.1 :=
        (tendsto_fst.mono_left (inf_le_left : boundedRatioFilter w R ≤ _)).eventually
          self_mem_nhdsWithin
      filter_upwards [hev', hpos] with p hp hτ
      have heq : w + (p.1 / 2) • (2 / p.1) • (p.2 - w) = p.2 := by
        rw [smul_smul, div_mul_div_comm, mul_comm p.1 2, div_self (by positivity), one_smul,
          add_sub_cancel]
      rw [heq] at hp
      exact hp.le
    exact absurd hs1 (not_lt.2 hle)
  · refine le_iInf fun z ↦ ?_
    exact (iInf_le _ (‖z‖ / 2 + 1)).trans (liminf_boundedRatioFilter_le hx hd z)

end Proposition1364

/-! ### Definition 13.65 -/

section Definition1365

/-- **Definition 13.65**: `f` is parabolically regular at `x̄` for `v` when `f(x̄)` is finite
and 13(39) holds with equality for every `w` with `df(x̄)(w) = ⟪v, w⟫`. -/
def IsParabolicallyRegularAt (f : E → EReal) (x v : E) : Prop :=
  (∃ c : ℝ, f x = c) ∧ ∀ w, subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) →
    ⨅ z, (parabolicSubderivative f x w z - ((⟪v, z⟫_ℝ : ℝ) : EReal)) =
      secondSubderivative f x v w

/-- **Definition 13.65**, the paraphrase "in other words": if for every such `w` with
`d²f(x̄ | v)(w) < ∞` the value `d²f(x̄ | v)(w)` is already attained as a lower limit along pairs
with `[w' - w]/τ` bounded, then `f` is parabolically regular at `x̄` for `v`. -/
theorem isParabolicallyRegularAt_of_boundedRatio [FiniteDimensional ℝ E] {f : E → EReal}
    {x v : E} {c : ℝ} (hx : f x = c)
    (h : ∀ w, subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) → secondSubderivative f x v w < ⊤ →
      ∃ R : ℝ, liminf (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
        (boundedRatioFilter w R) ≤ secondSubderivative f x v w) :
    IsParabolicallyRegularAt f x v := by
  refine ⟨⟨c, hx⟩, fun w hw ↦ le_antisymm ?_ (secondSubderivative_le_iInf_parabolicSubderivative
    hx hw)⟩
  rcases eq_or_lt_of_le (le_top : secondSubderivative f x v w ≤ ⊤) with htop | hlt
  · rw [htop]
    exact le_top
  · obtain ⟨R, hR⟩ := h w hw hlt
    rw [iInf_parabolicSubderivative_sub_inner_eq hx hw]
    exact (iInf_le _ R).trans hR

/-- Conversely, at a point of parabolic regularity, if the infimum in 13(39) is attained, the
value `d²f(x̄ | v)(w)` is attained along pairs with `[w' - w]/τ` bounded. -/
theorem IsParabolicallyRegularAt.exists_boundedRatio {f : E → EReal} {x v w : E}
    (hreg : IsParabolicallyRegularAt f x v) (hw : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal))
    {z : E} (hz : parabolicSubderivative f x w z - ((⟪v, z⟫_ℝ : ℝ) : EReal) =
      ⨅ z', (parabolicSubderivative f x w z' - ((⟪v, z'⟫_ℝ : ℝ) : EReal))) :
    ∃ R : ℝ, liminf (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
      (boundedRatioFilter w R) ≤ secondSubderivative f x v w := by
  obtain ⟨⟨c, hx⟩, h⟩ := hreg
  refine ⟨‖z‖ / 2 + 1, (liminf_boundedRatioFilter_le hx hw z).trans ?_⟩
  rw [hz, h w hw]

end Definition1365

/-! ### Theorem 13.66 -/

section Theorem1366

/-- At a finite local minimum, `df(x̄) ≥ 0`. -/
theorem IsLocalMin.subderivative_nonneg {f : E → EReal} {x : E} {c : ℝ} (hm : IsLocalMin f x)
    (hx : f x = c) (w : E) : 0 ≤ subderivative f x w := by
  refine le_liminf_of_le (h := ?_)
  filter_upwards [(tendsto_add_smul_nhds x w).eventually hm,
    tendsto_fst.eventually self_mem_nhdsWithin] with p hp hτ
  change 0 < p.1 at hτ
  rw [hx] at hp
  rcases ereal_trichotomy (f (x + p.1 • p.2)) with h | h | ⟨r, h⟩
  · rw [h] at hp
    exact absurd (le_bot_iff.1 hp) (EReal.coe_ne_bot c)
  · rw [differenceQuotient_eq_top hτ hx h]
    exact le_top
  · rw [h] at hp
    rw [differenceQuotient_eq_coe hx h]
    exact EReal.coe_nonneg.2 (mul_nonneg (inv_nonneg.2 hτ.le)
      (sub_nonneg.2 (EReal.coe_le_coe_iff.1 hp)))

/-- **Theorem 13.66(a)**: if `x̄` is locally optimal, then `df(x̄)(w) ≥ 0` for all `w`, and
`inf_z d²f(x̄)(w | z) ≥ 0` for `w ≠ 0` with `df(x̄)(w) = 0`. -/
theorem IsLocalMin.parabolic_necessary {f : E → EReal} {x : E} {c : ℝ} (hm : IsLocalMin f x)
    (hx : f x = c) :
    (∀ w, 0 ≤ subderivative f x w) ∧
      ∀ w, w ≠ 0 → subderivative f x w = 0 → 0 ≤ ⨅ z, parabolicSubderivative f x w z := by
  refine ⟨RW.IsLocalMin.subderivative_nonneg hm hx, fun w _ hw0 ↦ ?_⟩
  have hd : subderivative f x w = ((⟪(0 : E), w⟫_ℝ : ℝ) : EReal) := by
    rw [hw0, inner_zero_left, EReal.coe_zero]
  have h1 := secondSubderivative_le_iInf_parabolicSubderivative hx hd
  simp only [inner_zero_left, EReal.coe_zero, sub_zero] at h1
  exact ((RW.IsLocalMin.secondOrder_necessary hm hx).2 w).trans h1

/-- **Theorem 13.66(b)**: if `f` is parabolically regular at `x̄` for `v = 0`, `df(x̄) ≥ 0`, and
`inf_z d²f(x̄)(w | z) > 0` for `w ≠ 0` with `df(x̄)(w) = 0`, then there are `ε > 0` and `δ > 0`
with `f(x) ≥ f(x̄) + ε‖x - x̄‖²` when `‖x - x̄‖ ≤ δ`; in particular `x̄` is locally optimal. -/
theorem parabolic_sufficient [FiniteDimensional ℝ E] {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (hreg : IsParabolicallyRegularAt f x 0) (h1 : ∀ w, 0 ≤ subderivative f x w)
    (h2 : ∀ w, w ≠ 0 → subderivative f x w = 0 → 0 < ⨅ z, parabolicSubderivative f x w z) :
    (∃ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ((c + ε * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y) ∧
      IsLocalMin f x := by
  have hpos : ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w := by
    intro w hw
    rcases eq_or_lt_of_le (h1 w) with h0 | hlt
    · have hd : subderivative f x w = ((⟪(0 : E), w⟫_ℝ : ℝ) : EReal) := by
        rw [← h0, inner_zero_left, EReal.coe_zero]
      rw [← hreg.2 w hd]
      simp only [inner_zero_left, EReal.coe_zero, sub_zero]
      exact h2 w hw h0.symm
    · have hlt' : ((⟪(0 : E), w⟫_ℝ : ℝ) : EReal) < subderivative f x w := by
        rwa [inner_zero_left, EReal.coe_zero]
      rw [secondSubderivative_eq_top_of_inner_lt hx hlt']
      exact EReal.zero_lt_top
  exact ⟨exists_growth_of_secondSubderivative_pos hx hpos,
    isLocalMin_of_secondSubderivative_pos hx hpos⟩

/-- **Theorem 13.66**, both parts. -/
theorem parabolic_second_order_optimality [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    {c : ℝ} (hx : f x = c) :
    (IsLocalMin f x → (∀ w, 0 ≤ subderivative f x w) ∧
      ∀ w, w ≠ 0 → subderivative f x w = 0 → 0 ≤ ⨅ z, parabolicSubderivative f x w z) ∧
    (IsParabolicallyRegularAt f x 0 → (∀ w, 0 ≤ subderivative f x w) →
      (∀ w, w ≠ 0 → subderivative f x w = 0 → 0 < ⨅ z, parabolicSubderivative f x w z) →
      IsLocalMin f x ∧
        ∃ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ((c + ε * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y) :=
  ⟨fun hm ↦ RW.IsLocalMin.parabolic_necessary hm hx, fun hreg h1 h2 ↦
    ⟨(parabolic_sufficient hx hreg h1 h2).2, (parabolic_sufficient hx hreg h1 h2).1⟩⟩

end Theorem1366

end RW
