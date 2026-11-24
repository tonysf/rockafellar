/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Sufficiency of the second-order Lipschitz condition

Exercise 13.55, corrected sufficiency.  The printed sufficiency fails for merely finite functions
(`hamelFunction_counterexample`); here `f` is also bounded around `x̄`.

If `f` is bounded on `IB(x̄, ε)` and satisfies 13(35)
`|f(y + w + z) - f(y + w) - f(y + z) + f(y)| ≤ κ‖w‖‖z‖` (`SecondOrderLipschitzBound`), then the
dyadic quotients `2ᵏ[f(y + 2⁻ᵏw) - f(y)]` converge geometrically (13(35) with `w = z = 2⁻ᵏ⁻¹w`), to
an additive function of `w` (13(35) once more) that is bounded near `0`, hence to a continuous linear
`ℓ_y` with `|f(y + w) - f(y) - ℓ_y(w)| ≤ κ‖w‖²/2`.  So `f` is differentiable around `x̄`, and
comparing these expansions at `y` and `y'` through 13(35) gives `‖∇f(y') - ∇f(y)‖ ≤ κ‖y' - y‖`
(`SecondOrderLipschitzBound.isC1PlusOn`).  No appeal to Rademacher's theorem is needed.
-/

import RockafellarWets.Chapter13.SecondOrderLipschitz

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The second-order Lipschitz condition 13(35) on the `ε`-ball around `x̄` with constant `κ`. -/
def SecondOrderLipschitzBound (f : E → ℝ) (x : E) (ε κ : ℝ) : Prop :=
  ∀ y w z : E, ‖y - x‖ ≤ ε → ‖w‖ ≤ ε → ‖z‖ ≤ ε →
    |f (y + w + z) - f (y + w) - f (y + z) + f y| ≤ κ * ‖w‖ * ‖z‖

/-- The dyadic difference quotients `2ᵏ[f(y + 2⁻ᵏw) - f(y)]`. -/
noncomputable def dyadicQuotient (f : E → ℝ) (y w : E) (k : ℕ) : ℝ :=
  2 ^ k * (f (y + ((2 : ℝ) ^ k)⁻¹ • w) - f y)

theorem dyadicQuotient_zero_index (f : E → ℝ) (y w : E) :
    dyadicQuotient f y w 0 = f (y + w) - f y := by
  simp [dyadicQuotient]

theorem dyadicQuotient_add_index (f : E → ℝ) (y w : E) (k m : ℕ) :
    dyadicQuotient f y w (k + m) = 2 ^ m * dyadicQuotient f y (((2 : ℝ) ^ m)⁻¹ • w) k := by
  simp only [dyadicQuotient, smul_smul, pow_add, mul_inv]
  ring_nf

theorem dyadicQuotient_zero_vector (f : E → ℝ) (y : E) (k : ℕ) : dyadicQuotient f y 0 k = 0 := by
  simp [dyadicQuotient]

theorem norm_inv_two_pow_smul (w : E) (k : ℕ) : ‖((2 : ℝ) ^ k)⁻¹ • w‖ = ‖w‖ / 2 ^ k := by
  rw [norm_smul, norm_inv, norm_pow, Real.norm_two, div_eq_inv_mul]

theorem norm_inv_two_pow_smul_le (w : E) (k : ℕ) : ‖((2 : ℝ) ^ k)⁻¹ • w‖ ≤ ‖w‖ := by
  rw [norm_inv_two_pow_smul]
  exact div_le_self (norm_nonneg _) (one_le_pow₀ (by norm_num))

namespace SecondOrderLipschitzBound

variable {f : E → ℝ} {x : E} {ε κ : ℝ}

/-- One dyadic step: `|2ᵏ⁺¹[f(y + 2⁻ᵏ⁻¹w) - f(y)] - 2ᵏ[f(y + 2⁻ᵏw) - f(y)]| ≤ κ‖w‖²/(4·2ᵏ)`. -/
theorem dyadic_step (h : SecondOrderLipschitzBound f x ε κ) {y w : E} (hy : ‖y - x‖ ≤ ε)
    (hw : ‖w‖ ≤ ε) (k : ℕ) :
    dist (dyadicQuotient f y w k) (dyadicQuotient f y w (k + 1)) ≤ κ * ‖w‖ ^ 2 / 2 / 2 / 2 ^ k := by
  set a : E := ((2 : ℝ) ^ (k + 1))⁻¹ • w with ha
  have haa : ((2 : ℝ) ^ k)⁻¹ • w = a + a := by
    rw [ha, ← two_smul ℝ, smul_smul, pow_succ, mul_inv, mul_comm (2 : ℝ), mul_assoc,
      inv_mul_cancel₀ (two_ne_zero), mul_one]
  have hnorm : ‖a‖ = ‖w‖ / 2 ^ (k + 1) := norm_inv_two_pow_smul w (k + 1)
  have haε : ‖a‖ ≤ ε := (norm_inv_two_pow_smul_le w (k + 1)).trans hw
  have hb := h y a a hy haε haε
  rw [Real.dist_eq, dyadicQuotient, dyadicQuotient, haa, ← ha]
  have heq : 2 ^ k * (f (y + (a + a)) - f y) - 2 ^ (k + 1) * (f (y + a) - f y) =
      2 ^ k * (f (y + a + a) - f (y + a) - f (y + a) + f y) := by
    rw [← add_assoc]; ring
  rw [heq, abs_mul, abs_of_pos (by positivity)]
  calc 2 ^ k * |f (y + a + a) - f (y + a) - f (y + a) + f y| ≤ 2 ^ k * (κ * ‖a‖ * ‖a‖) := by
        gcongr
    _ = κ * ‖w‖ ^ 2 / 2 / 2 / 2 ^ k := by
        rw [hnorm]; field_simp; ring

/-- The dyadic quotients converge, and their limit approximates `f(y + w) - f(y)` to second order. -/
theorem exists_tendsto_dyadic (h : SecondOrderLipschitzBound f x ε κ) {y w : E}
    (hy : ‖y - x‖ ≤ ε) (hw : ‖w‖ ≤ ε) :
    ∃ L, Tendsto (dyadicQuotient f y w) atTop (𝓝 L) ∧ |f (y + w) - f y - L| ≤ κ * ‖w‖ ^ 2 / 2 := by
  have hstep : ∀ n, dist (dyadicQuotient f y w n) (dyadicQuotient f y w (n + 1)) ≤
      κ * ‖w‖ ^ 2 / 2 / 2 / 2 ^ n := h.dyadic_step hy hw
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hstep)
  refine ⟨L, hL, ?_⟩
  have h0 := dist_le_of_le_geometric_two_of_tendsto₀ hstep hL
  rwa [Real.dist_eq, dyadicQuotient_zero_index] at h0

/-- The dyadic quotients converge for every `w` (rescale by a power of `2`). -/
theorem exists_tendsto_dyadic' (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {y : E}
    (hy : ‖y - x‖ ≤ ε) (w : E) : ∃ L, Tendsto (dyadicQuotient f y w) atTop (𝓝 L) := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (‖w‖ / ε) (by norm_num : (1 : ℝ) < 2)
  have hw' : ‖((2 : ℝ) ^ m)⁻¹ • w‖ ≤ ε := by
    rw [norm_inv_two_pow_smul, div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hm
    linarith
  obtain ⟨L, hL, -⟩ := h.exists_tendsto_dyadic hy hw'
  refine ⟨2 ^ m * L, ?_⟩
  rw [← tendsto_add_atTop_iff_nat m]
  simp only [dyadicQuotient_add_index]
  exact hL.const_mul _

end SecondOrderLipschitzBound

/-- The limit `ℓ_y(w)` of the dyadic quotients. -/
noncomputable def dyadicDerivative (f : E → ℝ) (y w : E) : ℝ :=
  limUnder atTop (dyadicQuotient f y w)

namespace SecondOrderLipschitzBound

variable {f : E → ℝ} {x : E} {ε κ : ℝ}

theorem tendsto_dyadicDerivative (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {y : E}
    (hy : ‖y - x‖ ≤ ε) (w : E) :
    Tendsto (dyadicQuotient f y w) atTop (𝓝 (dyadicDerivative f y w)) :=
  tendsto_nhds_limUnder (h.exists_tendsto_dyadic' hε hy w)

/-- The second-order remainder estimate `|f(y + w) - f(y) - ℓ_y(w)| ≤ κ‖w‖²/2`. -/
theorem abs_sub_dyadicDerivative_le (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε)
    {y w : E} (hy : ‖y - x‖ ≤ ε) (hw : ‖w‖ ≤ ε) :
    |f (y + w) - f y - dyadicDerivative f y w| ≤ κ * ‖w‖ ^ 2 / 2 := by
  obtain ⟨L, hL, hle⟩ := h.exists_tendsto_dyadic hy hw
  rwa [tendsto_nhds_unique (h.tendsto_dyadicDerivative hε hy w) hL]

/-- `ℓ_y` is additive. -/
theorem dyadicDerivative_add (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {y : E}
    (hy : ‖y - x‖ ≤ ε) (w z : E) :
    dyadicDerivative f y (w + z) = dyadicDerivative f y w + dyadicDerivative f y z := by
  have h1 : Tendsto (fun k ↦ dyadicQuotient f y (w + z) k - dyadicQuotient f y w k -
      dyadicQuotient f y z k) atTop
      (𝓝 (dyadicDerivative f y (w + z) - dyadicDerivative f y w - dyadicDerivative f y z)) :=
    ((h.tendsto_dyadicDerivative hε hy (w + z)).sub (h.tendsto_dyadicDerivative hε hy w)).sub
      (h.tendsto_dyadicDerivative hε hy z)
  have h2 : Tendsto (fun k ↦ dyadicQuotient f y (w + z) k - dyadicQuotient f y w k -
      dyadicQuotient f y z k) atTop (𝓝 0) := by
    have hb : Tendsto (fun k : ℕ ↦ κ * ‖w‖ * ‖z‖ / 2 ^ k) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (κ * ‖w‖ * ‖z‖)
      rw [mul_zero] at this
      refine this.congr fun k ↦ ?_
      rw [one_div, inv_pow, div_eq_mul_inv]
    refine squeeze_zero_norm' ?_ hb
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((‖w‖ + ‖z‖) / ε) (by norm_num : (1 : ℝ) < 2)
    filter_upwards [eventually_ge_atTop m] with k hk
    have hpow : (2 : ℝ) ^ m ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    have hsmall : ∀ u : E, ‖u‖ ≤ ‖w‖ + ‖z‖ → ‖((2 : ℝ) ^ k)⁻¹ • u‖ ≤ ε := by
      intro u hu
      rw [norm_inv_two_pow_smul, div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hm
      nlinarith [norm_nonneg u]
    have hwε := hsmall w (by linarith [norm_nonneg z])
    have hzε := hsmall z (by linarith [norm_nonneg w])
    have hb := h y _ _ hy hwε hzε
    rw [Real.norm_eq_abs, dyadicQuotient, dyadicQuotient, dyadicQuotient, smul_add, ← add_assoc]
    have heq : 2 ^ k * (f (y + ((2 : ℝ) ^ k)⁻¹ • w + ((2 : ℝ) ^ k)⁻¹ • z) - f y) -
        2 ^ k * (f (y + ((2 : ℝ) ^ k)⁻¹ • w) - f y) - 2 ^ k * (f (y + ((2 : ℝ) ^ k)⁻¹ • z) - f y) =
        2 ^ k * (f (y + ((2 : ℝ) ^ k)⁻¹ • w + ((2 : ℝ) ^ k)⁻¹ • z) -
          f (y + ((2 : ℝ) ^ k)⁻¹ • w) - f (y + ((2 : ℝ) ^ k)⁻¹ • z) + f y) := by ring
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    calc 2 ^ k * |f (y + ((2 : ℝ) ^ k)⁻¹ • w + ((2 : ℝ) ^ k)⁻¹ • z) -
          f (y + ((2 : ℝ) ^ k)⁻¹ • w) - f (y + ((2 : ℝ) ^ k)⁻¹ • z) + f y| ≤
          2 ^ k * (κ * ‖((2 : ℝ) ^ k)⁻¹ • w‖ * ‖((2 : ℝ) ^ k)⁻¹ • z‖) := by gcongr
      _ = κ * ‖w‖ * ‖z‖ / 2 ^ k := by
          rw [norm_inv_two_pow_smul, norm_inv_two_pow_smul]; field_simp
  have := tendsto_nhds_unique h1 h2
  linarith

theorem dyadicDerivative_zero (f : E → ℝ) (y : E) : dyadicDerivative f y 0 = 0 := by
  have h : Tendsto (dyadicQuotient f y 0) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun k ↦ (dyadicQuotient_zero_vector f y k).symm
  exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨0, h⟩) h

/-- `ℓ_y` as an additive homomorphism. -/
noncomputable def dyadicAddHom (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {y : E}
    (hy : ‖y - x‖ ≤ ε) : E →+ ℝ where
  toFun := dyadicDerivative f y
  map_zero' := dyadicDerivative_zero f y
  map_add' := h.dyadicDerivative_add hε hy

/-- For `f` bounded on `IB(x̄, ε)`, `ℓ_y` is continuous at `y ∈ IB(x̄, ε/2)`. -/
theorem continuous_dyadicAddHom (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {M : ℝ}
    (hM : ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) {y : E} (hy : ‖y - x‖ ≤ ε / 2) :
    Continuous (h.dyadicAddHom hε (hy.trans (by linarith))) := by
  set ℓ := h.dyadicAddHom hε (hy.trans (by linarith))
  have hy' : ‖y - x‖ ≤ ε := hy.trans (by linarith)
  set B := 2 * M + |κ| * ε ^ 2
  have hbound : ∀ w : E, ‖w‖ ≤ ε / 2 → |ℓ w| ≤ B := by
    intro w hw
    have hwε : ‖w‖ ≤ ε := hw.trans (by linarith)
    have h1 := h.abs_sub_dyadicDerivative_le hε hy' hwε
    have h2 := hM (y + w) (by
      calc ‖y + w - x‖ = ‖(y - x) + w‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖w‖ := norm_add_le _ _
        _ ≤ ε := by linarith)
    have h3 := hM y hy'
    have h4 : κ * ‖w‖ ^ 2 / 2 ≤ |κ| * ε ^ 2 := by
      have : ‖w‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwε 2
      have : κ ≤ |κ| := le_abs_self κ
      nlinarith [sq_nonneg ‖w‖, abs_nonneg κ]
    change |dyadicDerivative f y w| ≤ B
    rw [abs_le] at h1 h2 h3 ⊢
    constructor <;> nlinarith [abs_nonneg κ]
  apply continuous_of_continuousAt_zero ℓ
  rw [Metric.continuousAt_iff]
  intro η hη
  obtain ⟨n, hn⟩ := exists_nat_gt (B / η)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (by
    have := hbound 0 (by rw [norm_zero]; positivity); exact (abs_nonneg _).trans this) hη.le) hn
  refine ⟨ε / 2 / n, by positivity, fun v hv ↦ ?_⟩
  rw [dist_zero_right] at hv
  rw [map_zero, dist_zero_right, Real.norm_eq_abs]
  have hnv : ‖(n : ℝ) • v‖ ≤ ε / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hn0.le]
    rw [lt_div_iff₀ hn0] at hv
    linarith
  have h1 := hbound _ hnv
  have h2 : ℓ ((n : ℝ) • v) = n * ℓ v := by
    rw [← nsmul_eq_mul, ← map_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, abs_mul, abs_of_pos hn0] at h1
  have h3 : B < η * n := by rw [div_lt_iff₀ hη] at hn; linarith
  have h4 : n * |ℓ v| < n * η := lt_of_le_of_lt h1 (by linarith)
  exact lt_of_mul_lt_mul_left h4 hn0.le

/-- The continuous linear map `ℓ_y`. -/
noncomputable def dyadicCLM (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {M : ℝ}
    (hM : ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) {y : E} (hy : ‖y - x‖ ≤ ε / 2) : E →L[ℝ] ℝ :=
  (h.dyadicAddHom hε (hy.trans (by linarith))).toRealLinearMap (h.continuous_dyadicAddHom hε hM hy)

theorem dyadicCLM_apply (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {M : ℝ}
    (hM : ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) {y : E} (hy : ‖y - x‖ ≤ ε / 2) (w : E) :
    h.dyadicCLM hε hM hy w = dyadicDerivative f y w := rfl

/-- `f` is differentiable at the points of `IB(x̄, ε/2)` with derivative `ℓ_y`. -/
theorem hasFDerivAt_dyadicCLM (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {M : ℝ}
    (hM : ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) {y : E} (hy : ‖y - x‖ ≤ ε / 2) :
    HasFDerivAt f (h.dyadicCLM hε hM hy) y := by
  have hy' : ‖y - x‖ ≤ ε := hy.trans (by linarith)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [ball_mem_nhds (0 : E) (show 0 < min ε (2 * c / (|κ| + 1)) by positivity)]
    with w hw
  rw [mem_ball, dist_zero_right, lt_min_iff] at hw
  have h1 := h.abs_sub_dyadicDerivative_le hε hy' hw.1.le
  rw [dyadicCLM_apply, Real.norm_eq_abs]
  refine h1.trans ?_
  have h2 : ‖w‖ * (|κ| + 1) ≤ 2 * c := by
    have := hw.2; rw [lt_div_iff₀ (by positivity)] at this; linarith
  have h3 : κ * ‖w‖ ^ 2 ≤ |κ| * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self κ) (sq_nonneg _)
  have h4 : ‖w‖ * (|κ| + 1) * ‖w‖ ≤ 2 * c * ‖w‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
  nlinarith [norm_nonneg w, abs_nonneg κ, sq_nonneg ‖w‖]

/-- Comparing the expansions at `y` and `y'` through 13(35): `‖ℓ_{y'} - ℓ_y‖ ≤ κ‖y' - y‖`. -/
theorem norm_dyadicCLM_sub_le (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) {M : ℝ}
    (hM : ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) (hκ : 0 ≤ κ) {y y' : E} (hy : ‖y - x‖ ≤ ε / 2)
    (hy' : ‖y' - x‖ ≤ ε / 2) :
    ‖h.dyadicCLM hε hM hy' - h.dyadicCLM hε hM hy‖ ≤ κ * ‖y' - y‖ := by
  have hyε : ‖y - x‖ ≤ ε := hy.trans (by linarith)
  have hy'ε : ‖y' - x‖ ≤ ε := hy'.trans (by linarith)
  have hyy : ‖y' - y‖ ≤ ε := by
    calc ‖y' - y‖ = ‖(y' - x) - (y - x)‖ := by congr 1; abel
      _ ≤ ‖y' - x‖ + ‖y - x‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e ↦ ?_
  rw [ContinuousLinearMap.sub_apply, dyadicCLM_apply, dyadicCLM_apply, Real.norm_eq_abs]
  set D := dyadicDerivative f y' e - dyadicDerivative f y e
  have hlin : ∀ t : ℝ, dyadicDerivative f y' (t • e) - dyadicDerivative f y (t • e) = t * D := by
    intro t
    have h1 := (h.dyadicCLM hε hM hy').map_smul t e
    have h2 := (h.dyadicCLM hε hM hy).map_smul t e
    rw [dyadicCLM_apply, dyadicCLM_apply, smul_eq_mul] at h1 h2
    rw [h1, h2]; ring
  have hkey : ∀ t : ℝ, 0 < t → ‖t • e‖ ≤ ε → |D| ≤ κ * ‖y' - y‖ * ‖e‖ + κ * t * ‖e‖ ^ 2 := by
    intro t ht hte
    have hR' := h.abs_sub_dyadicDerivative_le hε hy'ε hte
    have hR := h.abs_sub_dyadicDerivative_le hε hyε hte
    have hΔ := h y (y' - y) (t • e) hyε hyy hte
    rw [show y + (y' - y) = y' by abel] at hΔ
    have hn : ‖t • e‖ = t * ‖e‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
    rw [hn] at hR hR' hΔ
    have hdiff : t * D = (f (y' + t • e) - f y' - f (y + t • e) + f y) -
        (f (y' + t • e) - f y' - dyadicDerivative f y' (t • e)) +
        (f (y + t • e) - f y - dyadicDerivative f y (t • e)) := by
      rw [← hlin t]; ring
    have habs : t * |D| ≤ κ * ‖y' - y‖ * (t * ‖e‖) + κ * (t * ‖e‖) ^ 2 / 2 +
        κ * (t * ‖e‖) ^ 2 / 2 := by
      have e1 : t * |D| = |t * D| := by rw [abs_mul, abs_of_pos ht]
      rw [e1, hdiff]
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ((abs_sub _ _).trans (add_le_add hΔ hR')) hR
    have : t * |D| ≤ t * (κ * ‖y' - y‖ * ‖e‖ + κ * t * ‖e‖ ^ 2) := by
      calc t * |D| ≤ _ := habs
        _ = t * (κ * ‖y' - y‖ * ‖e‖ + κ * t * ‖e‖ ^ 2) := by ring
    exact le_of_mul_le_mul_left this ht
  have hlim : Tendsto (fun t : ℝ ↦ κ * ‖y' - y‖ * ‖e‖ + κ * t * ‖e‖ ^ 2) (𝓝[>] 0)
      (𝓝 (κ * ‖y' - y‖ * ‖e‖)) := by
    have hc : Continuous (fun t : ℝ ↦ κ * ‖y' - y‖ * ‖e‖ + κ * t * ‖e‖ ^ 2) := by fun_prop
    have := hc.tendsto 0
    rw [mul_zero, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖t • e‖ ≤ ε := by
    have hc0 : Continuous (fun t : ℝ ↦ ‖t • e‖) := by fun_prop
    have hc := hc0.tendsto 0
    rw [zero_smul, norm_zero] at hc
    exact (hc.eventually (ge_mem_nhds hε)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with t hte ht
  exact hkey t ht hte

end SecondOrderLipschitzBound

section C1Plus

variable [FiniteDimensional ℝ E]

/-- **Exercise 13.55**, corrected sufficiency: a function bounded on `IB(x̄, ε)` that satisfies
13(35) there is of class `C¹⁺` on `int IB(x̄, ε/2)`, with `∇f` Lipschitz continuous with constant
`κ` there. -/
theorem SecondOrderLipschitzBound.isC1PlusOn {f : E → ℝ} {x : E} {ε κ M : ℝ}
    (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) (hκ : 0 ≤ κ)
    (hM : ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) :
    IsC1PlusOn f (ball x (ε / 2)) ∧
      LipschitzOnWith (Real.toNNReal κ) (gradient f) (ball x (ε / 2)) := by
  have hmem : ∀ y ∈ ball x (ε / 2), ‖y - x‖ ≤ ε / 2 := fun y hy ↦ by
    rw [mem_ball, dist_eq_norm] at hy; exact hy.le
  have hgrad : ∀ y (hy : y ∈ ball x (ε / 2)),
      gradient f y = (InnerProductSpace.toDual ℝ E).symm (h.dyadicCLM hε hM (hmem y hy)) := by
    intro y hy
    rw [gradient, (h.hasFDerivAt_dyadicCLM hε hM (hmem y hy)).fderiv]
  have hlip : LipschitzOnWith (Real.toNNReal κ) (gradient f) (ball x (ε / 2)) := by
    refine LipschitzOnWith.of_dist_le_mul fun y' hy' y hy ↦ ?_
    rw [hgrad y' hy', hgrad y hy, dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map,
      Real.coe_toNNReal _ hκ, dist_eq_norm]
    exact h.norm_dyadicCLM_sub_le hε hM hκ (hmem y hy) (hmem y' hy')
  refine ⟨fun y hy ↦ ⟨(h.hasFDerivAt_dyadicCLM hε hM (hmem y hy)).differentiableAt, ?_⟩, hlip⟩
  exact strictlyContinuousAt_iff.2 ⟨_, _, isOpen_ball.mem_nhds hy, hlip⟩

end C1Plus

end RW
