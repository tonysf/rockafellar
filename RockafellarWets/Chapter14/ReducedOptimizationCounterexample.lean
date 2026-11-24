/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: The proviso of Example 14.62 is insufficient

Example 14.62 (reduced optimization) of Rockafellar–Wets asserts `inf(P) = inf(P')` whenever
`inf(P) < ∞`.  Its detail applies Theorem 14.60 to `I_h`, `h(t, u) = g(t, x(t), u)`, "whenever
`I_f[x] < ∞`", but 14.60 also needs `I_h ≢ ∞` on `U`, which can fail for a decomposable
`U ≠ M(T, A; ℝᵐ)`.  Here `T = ℕ` with the counting measure (σ-finite), `U = ℓ^∞` (bounded
sequences, decomposable), `X = {0, 1}` (constant sequences), `J = 0` and the finite Carathéodory
integrand `g(t, x, u) = |u - x t| + |1 - x| 2^{-t-1}`, so that `f(t, x) = |1 - x| 2^{-t-1}` is
continuous in `x`.  Every hypothesis of the example holds, yet `inf(P) = 1` and `inf(P') = 0`: no
bounded `u` makes `I_g[1, u]` finite, while `I_f[1] = 0` (`reduced_optimization_counterexample`).
The corrected `reduced_optimization` assumes instead that some `u ∈ U` has `I_g[x, u] < ∞` whenever
`J[x] < ∞` and `I_f[x] < ∞`, which always holds for `U = M(T, A; ℝᵐ)`
(`reduced_optimization_measurable`).
-/

import RockafellarWets.Chapter14.IntegralFunctionals

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace RW

namespace ReducedOptimizationCounterexample

/-- The finite integrand `g(t, x, u) = |u - x t| + |1 - x| 2^{-t-1}` on `ℕ × (ℝ × ℝ)`. -/
def gReal (t : ℕ) (p : ℝ × ℝ) : ℝ := |p.2 - p.1 * t| + |1 - p.1| * (1 / 2 : ℝ) ^ (t + 1)

/-- The integrand `g` with extended-real values. -/
def gEReal (t : ℕ) (p : ℝ × ℝ) : EReal := ((gReal t p : ℝ) : EReal)

theorem isNormalIntegrand_gEReal : IsNormalIntegrand gEReal := by
  have h : IsCaratheodory gReal :=
    ⟨fun p ↦ measurable_from_nat, fun t ↦ by unfold gReal; fun_prop⟩
  exact h.isNormalIntegrand

/-- `f(t, y) = inf_u g(t, y, u) = |1 - y| 2^{-t-1}`, attained at `u = y t`. -/
theorem iInf_gEReal (t : ℕ) (y : ℝ) :
    (⨅ v, gEReal t (y, v)) = ((|1 - y| * (1 / 2 : ℝ) ^ (t + 1) : ℝ) : EReal) := by
  apply le_antisymm
  · refine (iInf_le _ (y * t)).trans ?_
    simp [gEReal, gReal]
  · refine le_iInf fun v ↦ ?_
    simp only [gEReal, gReal, EReal.coe_le_coe_iff]
    linarith [abs_nonneg (v - y * t)]

theorem lowerSemicontinuous_iInf_gEReal (t : ℕ) :
    LowerSemicontinuous fun y ↦ ⨅ v, gEReal t (y, v) := by
  have : (fun y ↦ ⨅ v, gEReal t (y, v)) =
      fun y ↦ ((|1 - y| * (1 / 2 : ℝ) ^ (t + 1) : ℝ) : EReal) := funext (iInf_gEReal t)
  rw [this]
  exact (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous

/-- `ℓ^∞`: the bounded sequences. -/
def boundedSeqs : Set (ℕ → ℝ) := {u | ∃ C : ℝ, ∀ t, |u t| ≤ C}

theorem isDecomposable_boundedSeqs :
    IsDecomposable (Measure.count : Measure ℕ) boundedSeqs := by
  classical
  refine ⟨fun _ _ ↦ measurable_from_nat, ?_⟩
  rintro x₀ ⟨C₀, hC₀⟩ A - - x₁ - ⟨C₁, hC₁⟩
  refine ⟨max C₀ C₁, fun t ↦ ?_⟩
  by_cases ht : t ∈ A
  · rw [Set.piecewise_eq_of_mem _ _ _ ht]
    exact le_trans (by simpa [Real.norm_eq_abs] using hC₁ t ht) (le_max_right C₀ C₁)
  · rw [Set.piecewise_eq_of_notMem _ _ _ ht]
    exact (hC₀ t).trans (le_max_left C₀ C₁)

/-- The two constant sequences `0` and `1`. -/
def zeroOne : Set (ℕ → ℝ) := {fun _ ↦ 0, fun _ ↦ 1}

private theorem zero_infAddition' (a : EReal) : infAddition 0 a = a := by
  by_cases ha : a = ⊤ <;> simp [infAddition, ha]

theorem upperIntegral_count_zero :
    upperIntegral (Measure.count : Measure ℕ) (fun _ ↦ (0 : EReal)) = 0 := by
  simp [upperIntegral]

/-- The upper integral of a summable nonnegative real sequence for the counting measure is its
sum. -/
theorem upperIntegral_count_coe {α : ℕ → ℝ} (h0 : ∀ t, 0 ≤ α t) (hs : Summable α) :
    upperIntegral (Measure.count : Measure ℕ) (fun t ↦ ((α t : ℝ) : EReal)) =
      ((∑' t, α t : ℝ) : EReal) := by
  have hpos : ∫⁻ t, ((α t : ℝ) : EReal).toENNReal ∂(Measure.count : Measure ℕ) =
      ENNReal.ofReal (∑' t, α t) := by
    rw [lintegral_count]
    simp only [EReal.real_coe_toENNReal]
    rw [ENNReal.ofReal_tsum_of_nonneg h0 hs]
  have hneg : ∫⁻ t, (-((α t : ℝ) : EReal)).toENNReal ∂(Measure.count : Measure ℕ) = 0 := by
    have : ∀ t, (-((α t : ℝ) : EReal)).toENNReal = 0 := fun t ↦
      EReal.toENNReal_of_nonpos (by
        rw [← EReal.coe_neg]
        exact_mod_cast neg_nonpos.2 (h0 t))
    simp only [this, lintegral_zero]
  rw [upperIntegral_of_lintegral_ne_top (by rw [hpos]; exact ENNReal.ofReal_ne_top), hpos, hneg,
    EReal.coe_ennreal_ofReal, max_eq_left (tsum_nonneg h0)]
  simp

theorem summable_half_pow_succ : Summable fun t : ℕ ↦ (1 / 2 : ℝ) ^ (t + 1) :=
  (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem tsum_half_pow_succ : ∑' t : ℕ, (1 / 2 : ℝ) ^ (t + 1) = 1 := by
  have : ∀ t : ℕ, (1 / 2 : ℝ) ^ (t + 1) = 1 / 2 * (1 / 2) ^ t := fun t ↦ by
    rw [pow_succ, mul_comm]
  simp only [this]
  rw [tsum_mul_left, tsum_geometric_two]
  norm_num

/-- `∑_t 2^{-t-1} = 1` as an upper integral for the counting measure. -/
theorem upperIntegral_count_half_pow_succ :
    upperIntegral (Measure.count : Measure ℕ) (fun t ↦ (((1 / 2 : ℝ) ^ (t + 1) : ℝ) : EReal)) =
      1 := by
  rw [upperIntegral_count_coe (fun t ↦ by positivity) summable_half_pow_succ, tsum_half_pow_succ,
    EReal.coe_one]

theorem upperIntegral_count_eq_top {α : ℕ → EReal} (N : ℕ)
    (h : ∀ t, N ≤ t → (1 : EReal) ≤ α t) :
    upperIntegral (Measure.count : Measure ℕ) α = ⊤ := by
  have h1 : (1 : EReal).toENNReal = 1 := by
    rw [← EReal.coe_one, EReal.real_coe_toENNReal, ENNReal.ofReal_one]
  have htop : ∫⁻ t, (α t).toENNReal ∂(Measure.count : Measure ℕ) = ⊤ := by
    refine top_unique ?_
    calc (⊤ : ℝ≥0∞) = Measure.count (Set.Ici N) :=
          (Measure.count_apply_infinite (Set.Ici_infinite N)).symm
      _ = ∫⁻ t, (Set.Ici N).indicator 1 t ∂Measure.count :=
          (lintegral_indicator_one measurableSet_Ici).symm
      _ ≤ ∫⁻ t, (α t).toENNReal ∂Measure.count := lintegral_mono fun t ↦ ?_
    by_cases ht : t ∈ Set.Ici N
    · rw [Set.indicator_of_mem ht]
      have := EReal.toENNReal_le_toENNReal (h t ht)
      rwa [h1] at this
    · rw [Set.indicator_of_notMem ht]
      exact zero_le _
  rw [upperIntegral, if_pos htop]

/-- `inf(P') = 0`, attained at `x = 1`. -/
theorem inf_reduced_eq_zero :
    (⨅ x ∈ zeroOne, infAddition (0 : EReal)
      (integralFunctional Measure.count (fun t y ↦ ⨅ v, gEReal t (y, v)) x)) = 0 := by
  apply le_antisymm
  · refine (iInf₂_le (fun _ ↦ (1 : ℝ)) (by simp [zeroOne])).trans ?_
    have : integralFunctional (Measure.count : Measure ℕ) (fun t y ↦ ⨅ v, gEReal t (y, v))
        (fun _ ↦ (1 : ℝ)) = 0 := by
      unfold integralFunctional
      simp only [iInf_gEReal, sub_self, abs_zero, zero_mul, EReal.coe_zero]
      exact upperIntegral_count_zero
    rw [this, zero_infAddition']
  · refine le_iInf₂ fun x _ ↦ ?_
    rw [zero_infAddition']
    unfold integralFunctional
    simp only [iInf_gEReal]
    rw [← upperIntegral_count_zero]
    exact upperIntegral_mono fun t ↦ by
      exact_mod_cast (by positivity : (0 : ℝ) ≤ |1 - x t| * (1 / 2 : ℝ) ^ (t + 1))

/-- `inf(P) = 1`, attained at `(x, u) = (0, 0)`; for `x = 1` no bounded `u` makes `I_g` finite. -/
theorem inf_joint_eq_one :
    (⨅ x ∈ zeroOne, ⨅ u ∈ boundedSeqs, infAddition (0 : EReal)
      (integralFunctional Measure.count gEReal (fun t ↦ (x t, u t)))) = 1 := by
  apply le_antisymm
  · refine (iInf₂_le (fun _ ↦ (0 : ℝ)) (by simp [zeroOne])).trans ?_
    refine (iInf₂_le (fun _ ↦ (0 : ℝ)) ⟨0, fun _ ↦ by simp⟩).trans ?_
    rw [zero_infAddition']
    unfold integralFunctional
    have : (fun t ↦ gEReal t ((fun _ ↦ (0 : ℝ)) t, (fun _ ↦ (0 : ℝ)) t)) =
        fun t ↦ (((1 / 2 : ℝ) ^ (t + 1) : ℝ) : EReal) := by
      funext t
      simp [gEReal, gReal]
    rw [this, upperIntegral_count_half_pow_succ]
  · refine le_iInf₂ fun x hx ↦ le_iInf₂ fun u hu ↦ ?_
    rw [zero_infAddition']
    obtain ⟨C, hC⟩ := hu
    rcases hx with rfl | hx
    · rw [← upperIntegral_count_half_pow_succ]
      refine upperIntegral_mono fun t ↦ ?_
      simp only [gEReal, gReal, EReal.coe_le_coe_iff]
      have := abs_nonneg (u t - 0 * (t : ℝ))
      norm_num at this ⊢
    · rw [mem_singleton_iff] at hx
      subst hx
      obtain ⟨N, hN⟩ := exists_nat_ge (C + 1)
      have htop : upperIntegral (Measure.count : Measure ℕ)
          (fun t ↦ gEReal t ((1 : ℝ), u t)) = ⊤ := by
        refine upperIntegral_count_eq_top N fun t ht ↦ ?_
        simp only [gEReal, gReal]
        have h1 : (C + 1 : ℝ) ≤ t := hN.trans (by exact_mod_cast ht)
        have h2 : u t ≤ C := (le_abs_self _).trans (hC t)
        have h3 : (1 : ℝ) ≤ |u t - 1 * t| := by
          rw [abs_sub_comm]
          exact le_trans (by linarith) (le_abs_self _)
        exact_mod_cast (by simpa using h3 :
          (1 : ℝ) ≤ |u t - 1 * t| + |1 - 1| * (1 / 2 : ℝ) ^ (t + 1))
      have hI : integralFunctional (Measure.count : Measure ℕ) gEReal
          (fun t ↦ ((1 : ℝ), u t)) = ⊤ := htop
      rw [hI]
      exact le_top

end ReducedOptimizationCounterexample

open ReducedOptimizationCounterexample in
/-- **Example 14.62** fails under its printed proviso `inf(P) < ∞`: for the σ-finite counting
measure on `ℕ`, a normal (Carathéodory) integrand `g` with `f(t, ·) = inf_u g(t, ·, u)` lsc,
`X = {0, 1}` of measurable sequences, the decomposable space `U = ℓ^∞` and `J = 0`, one has
`inf(P) = 1 < ∞` but `inf(P') = 0`. -/
theorem reduced_optimization_counterexample :
    SigmaFinite (Measure.count : Measure ℕ) ∧
      ∃ (g : ℕ → ℝ × ℝ → EReal) (X U : Set (ℕ → ℝ)) (J : (ℕ → ℝ) → EReal),
        IsNormalIntegrand g ∧ (∀ t, LowerSemicontinuous fun y ↦ ⨅ v, g t (y, v)) ∧
        (∀ x ∈ X, Measurable x) ∧ IsDecomposable (Measure.count : Measure ℕ) U ∧
        (⨅ x ∈ X, ⨅ u ∈ U, infAddition (J x)
          (integralFunctional Measure.count g (fun t ↦ (x t, u t)))) = 1 ∧
        (⨅ x ∈ X, infAddition (J x)
          (integralFunctional Measure.count (fun t y ↦ ⨅ v, g t (y, v)) x)) = 0 :=
  ⟨inferInstance, gEReal, zeroOne, boundedSeqs, fun _ ↦ 0, isNormalIntegrand_gEReal,
    lowerSemicontinuous_iInf_gEReal, fun _ _ ↦ measurable_from_nat, isDecomposable_boundedSeqs,
    inf_joint_eq_one, inf_reduced_eq_zero⟩

end RW
