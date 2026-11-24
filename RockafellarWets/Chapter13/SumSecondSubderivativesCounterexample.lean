/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: the lower bound of Proposition 13.19 and the convention for `∞ - ∞`

Proposition 13.19 bounds `d²f(x̄ ∣ v)(w)` below by `sup Σ d²fᵢ(x̄ ∣ vᵢ)(w)` over decompositions
`v = Σ vᵢ`, `vᵢ ∈ ∂fᵢ(x̄)`.  `second_subderivatives_of_a_sum` forms the sums in `EReal`, where
`∞ + (-∞) = -∞` (`ereal_sum_eq_bot_of_mem`).  The book's default convention is inf-addition,
`∞ + (-∞) = ∞` (`infAddition`, Chapter 1), and with it the printed inequality fails: for
`f₁ = x₊^{3/2}` and `f₂ = -x₊^{3/2}` on `ℝ`, both of class `C¹`, all hypotheses of 13.19 hold at
`x̄ = 0` with `v = v₁ = v₂ = 0`, while `d²f₁(0 ∣ 0)(1) = ∞`, `d²f₂(0 ∣ 0)(1) = -∞` and
`d²(f₁ + f₂)(0 ∣ 0)(1) = 0` because `f₁ + f₂ = 0` (`sum_lower_bound_infAddition_counterexample`).

At Chapter 10's counterexample to the first-order clause of 13.19
(`qualified_sum_regularity_counterexample`) the sum has no subgradient at `x̄`
(`sum_regularity_counterexample_subdifferential_empty`), so the hypothesis `∂f(x̄) ≠ ∅` of the
corrected clause excludes it.
-/

import RockafellarWets.Chapter13.SumSecondSubderivatives
import RockafellarWets.Chapter10.SumRegularityCounterexample

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW
namespace SumSecondSubderivativesCounterexample

/-- `k(x) = x^{3/2}` as a real power (`0` for `x ≤ 0`); it is of class `C¹`. -/
noncomputable def k32 (x : ℝ) : ℝ := x ^ (3 / 2 : ℝ)

theorem contDiff_k32 : ContDiff ℝ 1 k32 := by
  have h := Real.contDiff_rpow_const_of_le (p := 3 / 2) (n := 1) (by norm_num)
  exact_mod_cast h

theorem k32_zero : k32 0 = 0 := Real.zero_rpow (by norm_num)

theorem k32_of_nonneg {y : ℝ} (hy : 0 ≤ y) : k32 y = y * Real.sqrt y := by
  rw [k32, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hy (by norm_num), Real.rpow_one]

theorem gradient_k32_zero : gradient k32 0 = 0 := by
  have h := (Real.hasDerivAt_rpow_const (x := 0) (p := 3 / 2) (Or.inr (by norm_num))).hasGradientAt'
  rw [Real.zero_rpow (by norm_num), mul_zero] at h
  exact h.gradient

theorem gradient_neg_k32_zero : gradient (fun x ↦ -k32 x) 0 = 0 := by
  have h := (Real.hasDerivAt_rpow_const (x := 0) (p := 3 / 2)
    (Or.inr (by norm_num))).neg.hasGradientAt'
  rw [Real.zero_rpow (by norm_num), mul_zero, neg_zero] at h
  exact h.gradient

/-- `f₁(x) = x₊^{3/2}`. -/
noncomputable def P32 (x : ℝ) : EReal := ((k32 x : ℝ) : EReal)

/-- `f₂(x) = -x₊^{3/2}`. -/
noncomputable def Q32 (x : ℝ) : EReal := ((-k32 x : ℝ) : EReal)

theorem secondDifferenceQuotient_P32 {τ w : ℝ} (hτ : 0 < τ) (hw : 0 ≤ w) :
    secondDifferenceQuotient P32 0 0 τ w = ((2 * w * Real.sqrt (τ * w) / τ : ℝ) : EReal) := by
  rw [secondDifferenceQuotient_of_coe (c := 0) (r := k32 (τ * w)) (by simp [P32, k32_zero])
    (by simp [P32]), k32_of_nonneg (mul_nonneg hτ.le hw), EReal.coe_eq_coe_iff, inner_zero_left,
    mul_zero, sub_zero, sub_zero, div_mul_eq_mul_div, div_eq_div_iff (by positivity) hτ.ne']
  ring

theorem secondDifferenceQuotient_Q32 {τ w : ℝ} (hτ : 0 < τ) (hw : 0 ≤ w) :
    secondDifferenceQuotient Q32 0 0 τ w = ((-(2 * w * Real.sqrt (τ * w) / τ) : ℝ) : EReal) := by
  rw [secondDifferenceQuotient_of_coe (c := 0) (r := -k32 (τ * w)) (by simp [Q32, k32_zero])
    (by simp [Q32]), k32_of_nonneg (mul_nonneg hτ.le hw), EReal.coe_eq_coe_iff, inner_zero_left,
    mul_zero, sub_zero, sub_zero, div_mul_eq_mul_div, ← neg_div,
    div_eq_div_iff (by positivity) hτ.ne']
  ring

theorem secondSubderivative_P32 : secondSubderivative P32 0 0 1 = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  have hδ : (0 : ℝ) < 1 / (2 * (|M| + 1) ^ 2) := by positivity
  have e1 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 (1 : ℝ), 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have e2 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 (1 : ℝ), p.1 < 1 / (2 * (|M| + 1) ^ 2) :=
    tendsto_fst.eventually (nhdsWithin_le_nhds (Iio_mem_nhds hδ))
  have e3 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 (1 : ℝ), 1 / 2 < p.2 :=
    tendsto_snd.eventually (Ioi_mem_nhds (by norm_num))
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one M)) (le_liminf_of_le (h := ?_))
  filter_upwards [e1, e2, e3] with p hp1 hp2 hp3
  obtain ⟨τ, u⟩ := p
  simp only at hp1 hp2 hp3 ⊢
  rw [secondDifferenceQuotient_P32 hp1 (by linarith), EReal.coe_le_coe_iff, le_div_iff₀ hp1]
  have h2 : τ * (2 * (|M| + 1) ^ 2) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hp2
  have h4 : (|M| + 1) ^ 2 * τ < u := by nlinarith
  have h1 : (|M| + 1) * τ ≤ Real.sqrt (τ * u) := by
    rw [Real.le_sqrt (by positivity) (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left h4.le hp1.le]
  have h3 : Real.sqrt (τ * u) ≤ 2 * u * Real.sqrt (τ * u) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * u - 1) (Real.sqrt_nonneg (τ * u))]
  nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self M)) hp1.le]

theorem secondSubderivative_Q32 : secondSubderivative Q32 0 0 1 = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  refine lt_of_le_of_lt (liminf_le_of_frequently_le' ?_) (EReal.coe_lt_coe_iff.2 (sub_one_lt M))
  refine (tendsto_pair_const (1 : ℝ)).frequently (Eventually.frequently ?_)
  have hδ : (0 : ℝ) < 1 / (|M| + 1) ^ 2 := by positivity
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with τ hτ hτ2
  have hτ0 : (0 : ℝ) < τ := hτ
  have hτ2' : τ < 1 / (|M| + 1) ^ 2 := hτ2
  have hτ3 : τ * (|M| + 1) ^ 2 < 1 := by rwa [lt_div_iff₀ (by positivity)] at hτ2'
  change secondDifferenceQuotient Q32 0 0 τ 1 ≤ ((M - 1 : ℝ) : EReal)
  rw [secondDifferenceQuotient_Q32 hτ0 zero_le_one, EReal.coe_le_coe_iff, mul_one, mul_one,
    neg_le, le_div_iff₀ hτ0]
  have h1 : (|M| + 1) * τ ≤ Real.sqrt τ := by
    rw [Real.le_sqrt (by positivity) hτ0.le]
    nlinarith [mul_le_mul_of_nonneg_left hτ3.le hτ0.le]
  nlinarith [mul_nonneg (by linarith [neg_abs_le M] : (0 : ℝ) ≤ |M| + M) hτ0.le,
    Real.sqrt_nonneg τ]

theorem sum_PQ : (fun z : ℝ ↦ ∑ i : Fin 2, ![P32, Q32] i z) = fun _ ↦ (0 : EReal) := by
  funext z
  rw [Fin.sum_univ_two]
  change ((k32 z : ℝ) : EReal) + ((-k32 z : ℝ) : EReal) = 0
  rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]

theorem secondSubderivative_zero_fun :
    secondSubderivative (fun _ : ℝ ↦ (0 : EReal)) 0 0 1 = 0 := by
  have heq : (fun p : ℝ × ℝ ↦ secondDifferenceQuotient (fun _ : ℝ ↦ (0 : EReal)) 0 0 p.1 p.2) =
      fun _ ↦ (0 : EReal) := by
    funext p
    rw [secondDifferenceQuotient_of_coe (c := 0) (r := 0) (by simp) (by simp)]
    simp
  rw [secondSubderivative, heq, liminf_const]

/-- **Proposition 13.19**, the lower bound under the book's inf-addition.  All hypotheses of
13.19 hold for `f₁ = x₊^{3/2}` and `f₂ = -x₊^{3/2}` at `x̄ = 0` (proper, lsc, finite and regular
summands, the horizon qualification, `0 ∈ ∂(f₁ + f₂)(0)`, `0 ∈ ∂fᵢ(0)`), with `v = v₁ = v₂ = 0`.
Here `d²f₁(0 ∣ 0)(1) = ∞`, `d²f₂(0 ∣ 0)(1) = -∞` and `d²(f₁ + f₂)(0 ∣ 0)(1) = 0`, so the printed
inequality `d²f(x̄ ∣ v)(w) ≥ Σ d²fᵢ(x̄ ∣ vᵢ)(w)` fails when the sum is formed with
inf-addition `∞ + (-∞) = ∞` (`infAddition`). -/
theorem sum_lower_bound_infAddition_counterexample :
    (∀ i, IsProper (![P32, Q32] i)) ∧ (∀ i, LowerSemicontinuous (![P32, Q32] i)) ∧
    (∀ i, (0 : ℝ) ∈ effectiveDomain (![P32, Q32] i)) ∧
    (∀ i, IsSubdifferentiallyRegularAt (![P32, Q32] i) 0) ∧
    (∀ v : Fin 2 → ℝ, (∀ i, v i ∈ horizonSubdifferential (![P32, Q32] i) 0) →
      ∑ i, v i = 0 → ∀ i, v i = 0) ∧
    (0 : ℝ) ∈ subdifferential (fun z ↦ ∑ i, ![P32, Q32] i z) 0 ∧
    (∀ i, (0 : ℝ) ∈ subdifferential (![P32, Q32] i) 0) ∧
    secondSubderivative (fun z ↦ ∑ i, ![P32, Q32] i z) 0 0 1 = 0 ∧
    secondSubderivative P32 0 0 1 = ⊤ ∧ secondSubderivative Q32 0 0 1 = ⊥ ∧
    ¬ infAddition (secondSubderivative P32 0 0 1) (secondSubderivative Q32 0 0 1) ≤
      secondSubderivative (fun z ↦ ∑ i, ![P32, Q32] i z) 0 0 1 := by
  have hP : ContDiff ℝ 1 k32 := contDiff_k32
  have hQ : ContDiff ℝ 1 (fun x ↦ -k32 x) := contDiff_k32.neg
  have sP := subdifferentials_of_smooth (hP.contDiffAt (x := 0))
  have sQ := subdifferentials_of_smooth (hQ.contDiffAt (x := 0))
  have sP1 : subdifferential P32 0 = {gradient k32 0} := sP.1
  have sP2 : horizonSubdifferential P32 0 = {0} := sP.2.1
  have sQ1 : subdifferential Q32 0 = {gradient (fun x ↦ -k32 x) 0} := sQ.1
  have sQ2 : horizonSubdifferential Q32 0 = {0} := sQ.2.1
  have rP : IsSubdifferentiallyRegularAt P32 0 :=
    (regularSubderivatives_of_smooth (x := (0 : ℝ)) univ_mem hP.contDiffOn).1
  have rQ : IsSubdifferentiallyRegularAt Q32 0 :=
    (regularSubderivatives_of_smooth (x := (0 : ℝ)) univ_mem hQ.contDiffOn).1
  have cP : Continuous P32 := continuous_coe_real_ereal.comp hP.continuous
  have cQ : Continuous Q32 := continuous_coe_real_ereal.comp hQ.continuous
  have hsum0 : secondSubderivative (fun z ↦ ∑ i, ![P32, Q32] i z) 0 0 1 = 0 := by
    rw [sum_PQ]; exact secondSubderivative_zero_fun
  refine ⟨Fin.forall_fin_two.2 ⟨⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩,
      ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩⟩,
    Fin.forall_fin_two.2 ⟨cP.lowerSemicontinuous, cQ.lowerSemicontinuous⟩,
    Fin.forall_fin_two.2 ⟨EReal.coe_lt_top _, EReal.coe_lt_top _⟩,
    Fin.forall_fin_two.2 ⟨rP, rQ⟩, ?_, ?_, Fin.forall_fin_two.2 ⟨?_, ?_⟩, hsum0,
    secondSubderivative_P32, secondSubderivative_Q32, ?_⟩
  · intro v hv _
    have h0 : v 0 ∈ horizonSubdifferential P32 0 := hv 0
    have h1 : v 1 ∈ horizonSubdifferential Q32 0 := hv 1
    rw [sP2] at h0
    rw [sQ2] at h1
    exact Fin.forall_fin_two.2 ⟨h0, h1⟩
  · rw [sum_PQ]
    have hmin : IsLocalMin (fun _ : ℝ ↦ (0 : EReal)) 0 := Eventually.of_forall fun _ ↦ le_rfl
    exact regularSubdifferential_subset_subdifferential _ _
      (RW.IsLocalMin.zero_mem_regularSubdifferential hmin (c := 0) (by simp))
  · change (0 : ℝ) ∈ subdifferential P32 0
    rw [sP1, gradient_k32_zero]; rfl
  · change (0 : ℝ) ∈ subdifferential Q32 0
    rw [sQ1, gradient_neg_k32_zero]; rfl
  · rw [hsum0, secondSubderivative_P32, secondSubderivative_Q32]
    simp [infAddition]

/-- **Proposition 13.19**, the first-order clause: at Chapter 10's counterexample to the regularity
clause (`qualified_sum_regularity_counterexample`) the sum has no subgradient at `x̄`, so the
second-order statements of 13.19 are vacuous there, and `∂f(x̄) ≠ ∅` in
`second_subderivatives_of_a_sum` excludes it. -/
theorem sum_regularity_counterexample_subdifferential_empty :
    ∃ f g : WithLp 2 (ℝ × ℝ) → EReal,
      IsProper f ∧ IsProper g ∧ LowerSemicontinuous f ∧ LowerSemicontinuous g ∧
      IsSubdifferentiallyRegularAt f 0 ∧ IsSubdifferentiallyRegularAt g 0 ∧
      (∀ u ∈ horizonSubdifferential f 0, ∀ v ∈ horizonSubdifferential g 0,
        u + v = 0 → u = 0 ∧ v = 0) ∧
      ¬ IsSubdifferentiallyRegularAt (f + g) 0 ∧ subdifferential (f + g) 0 = ∅ := by
  obtain ⟨f, g, hpf, hpg, hlf, hlg, hf0, hg0, hrf, hrg, hQ, hnr⟩ :=
    qualified_sum_regularity_counterexample
  refine ⟨f, g, hpf, hpg, hlf, hlg, hrf, hrg, hQ, hnr, ?_⟩
  by_contra hne
  have hne' : (subdifferential (f + g) 0).Nonempty := Set.nonempty_iff_ne_empty.2 hne
  have hsum : (fun z ↦ ∑ i : Fin 2, ![f, g] i z) = f + g := by
    funext z
    rw [Fin.sum_univ_two]
    rfl
  have h := second_subderivatives_of_a_sum (f := ![f, g]) (x := (0 : WithLp 2 (ℝ × ℝ)))
    (Fin.forall_fin_two.2 ⟨hpf, hpg⟩) (Fin.forall_fin_two.2 ⟨hlf, hlg⟩)
    (Fin.forall_fin_two.2 ⟨by change f 0 < ⊤; rw [hf0]; exact EReal.zero_lt_top,
      by change g 0 < ⊤; rw [hg0]; exact EReal.zero_lt_top⟩)
    (Fin.forall_fin_two.2 ⟨hrf, hrg⟩)
    (fun v hv hs ↦ by
      rw [Fin.sum_univ_two] at hs
      obtain ⟨h0, h1⟩ := hQ (v 0) (hv 0) (v 1) (hv 1) hs
      exact Fin.forall_fin_two.2 ⟨h0, h1⟩)
  rw [hsum] at h
  exact hnr (h.2.1 hne').1

end SumSecondSubderivativesCounterexample
end RW
