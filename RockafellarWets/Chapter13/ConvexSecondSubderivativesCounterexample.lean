/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: the reading of twice semidifferentiability in Proposition 13.20(c)

Proposition 13.20(c) speaks of `f` being twice semidifferentiable "at `x̄` for `v̄`", which
Definition 13.6(a) does not define: 13.6(a) defines twice semidifferentiability at `x̄`, without
`v̄` (`TwiceSemidifferentiableAt`).  Read with that notion, (c) is false.  `f = |·|` on `ℝ` is
proper and convex with `0 ∈ ∂f(0)`, and it is twice semidifferentiable at `0`, since
`Δ²_τ f(0) ≡ 0`; but `f` is not differentiable at `0`, and for every `v̄` some `d²f(0 ∣ v̄)(w)` is
`∞`, so `f` is twice semidifferentiable at `0` for no `v̄` in the sense that
`second_subderivatives_of_convex_functions` uses (`TwiceSemidifferentiableAtFor`)
(`twiceSemidifferentiableAt_abs_counterexample`).
-/

import RockafellarWets.Chapter13.ConvexSecondSubderivatives
import Mathlib.Analysis.Calculus.Deriv.Abs

open Filter Set Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace RW
namespace ConvexSecondSubderivativesCounterexample

/-- `f(x) = |x|` as an extended-real-valued function on `ℝ`. -/
noncomputable def absE (x : ℝ) : EReal := ((|x| : ℝ) : EReal)

theorem absE_zero : absE 0 = ((0 : ℝ) : EReal) := by simp [absE]

theorem differenceQuotient_absE {τ : ℝ} (hτ : 0 < τ) (w : ℝ) :
    differenceQuotient absE 0 τ w = ((|w| : ℝ) : EReal) := by
  rw [differenceQuotient_eq_coe absE_zero (r := |τ * w|) (by simp [absE]), EReal.coe_eq_coe_iff,
    sub_zero, abs_mul, abs_of_pos hτ, inv_mul_cancel_left₀ hτ.ne']

theorem tendsto_differenceQuotient_absE (w : ℝ) :
    Tendsto (fun p : ℝ × ℝ ↦ differenceQuotient absE 0 p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 ((|w| : ℝ) : EReal)) := by
  have h : Tendsto (fun p : ℝ × ℝ ↦ ((|p.2| : ℝ) : EReal)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 ((|w| : ℝ) : EReal)) :=
    ((continuous_coe_real_ereal.comp continuous_abs).tendsto w).comp tendsto_snd
  refine h.congr' ?_
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  exact (differenceQuotient_absE hp p.2).symm

theorem subderivative_absE (w : ℝ) : subderivative absE 0 w = ((|w| : ℝ) : EReal) :=
  (tendsto_differenceQuotient_absE w).liminf_eq

/-- The quotients 13(4) of `|·|` at `0` vanish: `Δ²_τ f(0) ≡ 0`. -/
theorem secondDifferenceQuotientAt_absE {τ : ℝ} (hτ : 0 < τ) (w : ℝ) :
    secondDifferenceQuotientAt absE 0 τ w = 0 := by
  have h1 : absE (0 + τ • w) - absE 0 = ((τ * |w| : ℝ) : EReal) := by
    rw [absE_zero, absE, zero_add, smul_eq_mul, abs_mul, abs_of_pos hτ, ← EReal.coe_sub,
      sub_zero]
  have h2 : -((τ : EReal) * subderivative absE 0 w) = ((-(τ * |w|) : ℝ) : EReal) := by
    rw [subderivative_absE, ← EReal.coe_mul, EReal.coe_neg]
  rw [secondDifferenceQuotientAt, h1, h2, infAddition_coe_right, ← EReal.coe_add,
    add_neg_cancel, EReal.coe_zero, mul_zero]

theorem secondSubderivativeAt_absE (w : ℝ) : secondSubderivativeAt absE 0 w = 0 := by
  rw [secondSubderivativeAt]
  have h : (fun p : ℝ × ℝ ↦ secondDifferenceQuotientAt absE 0 p.1 p.2) =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 w]
      fun _ ↦ 0 := by
    filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
    exact secondDifferenceQuotientAt_absE hp p.2
  rw [liminf_congr h, liminf_const]

/-- `|·|` is twice semidifferentiable at `0` in the sense of Definition 13.6(a). -/
theorem twiceSemidifferentiableAt_absE : TwiceSemidifferentiableAt absE 0 := by
  refine ⟨fun w ↦ ⟨_, by rw [absE_zero]; exact EReal.coe_ne_bot 0,
    by rw [absE_zero]; exact EReal.coe_ne_top 0, tendsto_differenceQuotient_absE w⟩, fun w ↦ ?_⟩
  rw [secondSubderivativeAt_absE]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  exact (secondDifferenceQuotientAt_absE hp p.2).symm

/-- `|·|` has no gradient at `0`. -/
theorem not_hasERealGradientAt_absE (L : ℝ →L[ℝ] ℝ) : ¬ HasERealGradientAt absE 0 L := by
  rintro ⟨-, -, -, ho⟩
  apply not_differentiableAt_abs_zero
  refine ⟨L, HasFDerivAtFilter.of_isLittleO ?_⟩
  simpa [absE] using ho

/-- For every `v̄`, `d²f(0 ∣ v̄)(w) = ∞` at `w = -1` if `v̄ ≥ 0` and at `w = 1` if `v̄ < 0`: there
`|w| - v̄w = 1 + |v̄|`, and `Δ²_τ f(0 ∣ v̄)(w') = (2/τ)(|w'| - v̄w')`. -/
theorem secondSubderivative_absE_eq_top (v : ℝ) :
    secondSubderivative absE 0 v (if 0 ≤ v then -1 else 1) = ⊤ := by
  set w₀ : ℝ := if 0 ≤ v then -1 else 1 with hw₀
  have hg0 : 1 ≤ |w₀| - v * w₀ := by
    rw [hw₀]
    split_ifs with hv
    · rw [abs_neg, abs_one]; linarith
    · rw [abs_one]; push_neg at hv; linarith
  have hg : ∀ᶠ w' in 𝓝 w₀, 1 / 2 < |w'| - v * w' := by
    have hc : Continuous fun w' : ℝ ↦ |w'| - v * w' := continuous_abs.sub (continuous_mul_left v)
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by linarith))
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  have hδ : (0 : ℝ) < 1 / (|M| + 1) := by positivity
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one M)) (le_liminf_of_le (h := ?_))
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin,
    tendsto_fst.eventually (nhdsWithin_le_nhds (Iio_mem_nhds hδ)), tendsto_snd.eventually hg]
    with p hp1 hp2 hp3
  obtain ⟨τ, w'⟩ := p
  change 0 < τ at hp1
  change τ < 1 / (|M| + 1) at hp2
  change 1 / 2 < |w'| - v * w' at hp3
  change ((M + 1 : ℝ) : EReal) ≤ secondDifferenceQuotient absE 0 v τ w'
  rw [secondDifferenceQuotient_of_coe absE_zero (r := |τ * w'|) (by simp [absE]),
    EReal.coe_le_coe_iff]
  have hin : ⟪v, w'⟫_ℝ = v * w' := by simp [mul_comm]
  rw [hin, abs_mul, abs_of_pos hp1, sub_zero]
  have hτM : τ * (|M| + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hp2
  have key : 2 / τ ^ 2 * (τ * |w'| - τ * (v * w')) = 2 * (|w'| - v * w') / τ := by
    field_simp
  rw [key, le_div_iff₀ hp1]
  nlinarith [mul_le_mul_of_nonneg_right (add_le_add_right (le_abs_self M) 1) hp1.le]

theorem isProper_absE : IsProper absE :=
  ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩

theorem convex_epigraph_absE : Convex ℝ (epigraph absE) := by
  have h := (convex_epigraph_iff_convexOn (fun y : ℝ ↦ |y|) univ convex_univ).mpr
    (by simpa only [Real.norm_eq_abs] using convexOn_norm (E := ℝ) convex_univ)
  simpa [epigraph, absE] using h

theorem zero_mem_subdifferential_absE : (0 : ℝ) ∈ subdifferential absE 0 := by
  have hmin : IsLocalMin absE 0 := Eventually.of_forall fun y ↦ by
    simp only [absE, abs_zero, EReal.coe_le_coe_iff]
    exact abs_nonneg y
  exact regularSubdifferential_subset_subdifferential _ _
    (RW.IsLocalMin.zero_mem_regularSubdifferential hmin absE_zero)

/-- **Proposition 13.20(c)** fails when "twice semidifferentiable at `x̄` for `v̄`" is read as twice
semidifferentiability at `x̄` (Definition 13.6(a)).  `f = |·|` on `ℝ` is proper and convex, finite
at `0` with `0 ∈ ∂f(0)`, and twice semidifferentiable at `0`; yet `f` has no gradient at `0`, and
for every `v̄` the second subderivative `d²f(0 ∣ v̄)` takes the value `∞`, so `f` is twice
semidifferentiable at `0` for no `v̄` in the sense of `TwiceSemidifferentiableAtFor`, the reading
under which `second_subderivatives_of_convex_functions` proves (c). -/
theorem twiceSemidifferentiableAt_abs_counterexample :
    IsProper absE ∧ Convex ℝ (epigraph absE) ∧ absE 0 = ((0 : ℝ) : EReal) ∧
    (0 : ℝ) ∈ subdifferential absE 0 ∧ TwiceSemidifferentiableAt absE 0 ∧
    (∀ L : ℝ →L[ℝ] ℝ, ¬ HasERealGradientAt absE 0 L) ∧
    ∀ v : ℝ, (∃ w, secondSubderivative absE 0 v w = ⊤) ∧
      ¬ TwiceSemidifferentiableAtFor absE 0 v :=
  ⟨isProper_absE, convex_epigraph_absE, absE_zero, zero_mem_subdifferential_absE,
    twiceSemidifferentiableAt_absE, not_hasERealGradientAt_absE, fun v ↦
      ⟨⟨_, secondSubderivative_absE_eq_top v⟩,
        fun h ↦ (h _).1.2 (secondSubderivative_absE_eq_top v)⟩⟩

end ConvexSecondSubderivativesCounterexample
end RW
