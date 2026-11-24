/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order Lipschitz continuity and strict second-order differentiability

Exercise 13.55 and Proposition 13.56.

* `second_order_lipschitz_continuity` (13.55): `f` is of class `C¹⁺` around `x̄` if and only if it is
  bounded around `x̄` and satisfies 13(35) (`SecondOrderLipschitzBound`).  Necessity by the mean
  value theorem (`secondOrderLipschitzBound_of_lipschitzOnWith`), sufficiency by the dyadic argument
  of `SecondOrderLipschitzSufficiency`.  `SecondOrderLipschitzBound` bounds the absolute value of
  the mixed difference, while the book bounds it from above only; the two forms are equivalent on a
  smaller ball, since `(y, w) ↦ (y + w, -w)` changes the sign of the difference
  (`secondOrderLipschitzBound_of_one_sided`), and `second_order_lipschitz_continuity_one_sided`
  states 13.55 with 13(35) exactly as printed.
* `second_order_lipschitz_modulus` (13.55, the formula): the upper limit of the quotients
  `[f(x + w + z) - f(x + w) - f(x + z) + f(x)]/(‖w‖‖z‖)` as `x → x̄`, `w, z → 0` (`w, z ≠ 0`) is
  `max {‖A‖ ∣ A ∈ ∇̄²f(x̄)}`, and this is the lowest limiting value of the constants `κ` in 13(35):
  13(35) holds near `x̄` for every larger `κ` and for no smaller one.  The upper estimate comes from
  `lip ∇f(x̄) = |D_*(∇f)(x̄)|⁺` (9.54) and 13(33); the lower one from 13(34) (Theorem 13.52) along
  directions attaining the norm.
* `strict_second_order_differentiability` (13.56): (a) ⇔ (b) through 9.64, (a) ⇒ (c) with the
  value of the limit, and (c) ⇒ (a) through 13.55 and 13.52.

**Correction.**  In 13.55 and in 13.56(c), "finite around `x̄`" must be strengthened to "finite and
bounded around `x̄`": the additive Hamel function `hamelFunction` satisfies 13(35) with `κ = 0` and
has all mixed second-difference limits equal to `0`, but it is nowhere continuous
(`hamelFunction_counterexample`).
-/

import RockafellarWets.Chapter13.SecondOrderLipschitzSufficiency
import RockafellarWets.Chapter9.DerivativeContinuity
import RockafellarWets.Chapter9.StrictDerivativeModulus

open Filter Set Topology Metric MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Necessity of 13(35) -/

/-- If `∇f` exists and is Lipschitz continuous with constant `L` on `int IB(x̄, r)`, then 13(35)
holds on `IB(x̄, r/4)` with `κ = L` (mean value theorem along `t ↦ f(y + w + tz) - f(y + tz)`). -/
theorem secondOrderLipschitzBound_of_lipschitzOnWith {f : E → ℝ} {x : E} {r : ℝ} {L : ℝ≥0}
    (hd : ∀ y ∈ ball x r, DifferentiableAt ℝ f y)
    (hL : LipschitzOnWith L (gradient f) (ball x r)) :
    SecondOrderLipschitzBound f x (r / 4) L := by
  intro y w z hy hw hz
  by_cases hr0 : r ≤ 0
  · have hz0 : ‖z‖ = 0 := le_antisymm (by linarith) (norm_nonneg z)
    rw [norm_eq_zero] at hz0
    subst hz0
    simp
  push_neg at hr0
  have hmem : ∀ a : E, ‖a - x‖ < r → a ∈ ball x r := fun a ha ↦ by rwa [mem_ball, dist_eq_norm]
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c : E, ‖c‖ ≤ r / 4 → ‖y + c + t • z - x‖ < r := by
    intro t ht c hc
    have h1 : ‖t • z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]; exact mul_le_of_le_one_left (norm_nonneg z) ht.2
    calc ‖y + c + t • z - x‖ = ‖(y - x) + c + t • z‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖c‖ + ‖t • z‖ := norm_add₃_le
      _ < r := by linarith
  set g : ℝ → ℝ := fun t ↦ f (y + w + t • z) - f (y + t • z) with hg
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g
      (⟪gradient f (y + w + t • z) - gradient f (y + t • z), z⟫_ℝ) (Icc 0 1) t := by
    intro t ht
    have hd' : ∀ c : E, ‖c‖ ≤ r / 4 → HasDerivAt (fun t : ℝ ↦ f (y + c + t • z))
        ⟪gradient f (y + c + t • z), z⟫_ℝ t := by
      intro c hc
      have hdiff := hd _ (hmem _ (hpt t ht c hc))
      have hgr := hdiff.hasGradientAt
      rw [hasGradientAt_iff_hasFDerivAt] at hgr
      have hp : HasDerivAt (fun t : ℝ ↦ y + c + t • z) z t := by
        simpa using ((hasDerivAt_id t).smul_const z).const_add (y + c)
      have := hgr.comp_hasDerivAt t hp
      simpa [InnerProductSpace.toDual_apply_apply] using this
    have h1 := hd' w hw
    have h2 := hd' 0 (by rw [norm_zero]; positivity)
    simp only [add_zero] at h2
    rw [inner_sub_left]
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖⟪gradient f (y + w + t • z) - gradient f (y + t • z), z⟫_ℝ‖ ≤ L * ‖w‖ * ‖z‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have h1 := hL.norm_sub_le (hmem _ (hpt t ht' w hw))
      (hmem _ (by simpa using hpt t ht' 0 (by rw [norm_zero]; positivity)))
    rw [show y + w + t • z - (y + t • z) = w by abel] at h1
    rw [Real.norm_eq_abs]
    calc |⟪gradient f (y + w + t • z) - gradient f (y + t • z), z⟫_ℝ| ≤
          ‖gradient f (y + w + t • z) - gradient f (y + t • z)‖ * ‖z‖ := abs_real_inner_le_norm _ _
      _ ≤ L * ‖w‖ * ‖z‖ := by gcongr
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 (by simp)
  simp only [hg, one_smul, zero_smul, add_zero, sub_zero, mul_one, Real.norm_eq_abs] at h
  calc |f (y + w + z) - f (y + w) - f (y + z) + f y| =
        |f (y + w + z) - f (y + z) - (f (y + w) - f y)| := by ring_nf
    _ ≤ L * ‖w‖ * ‖z‖ := h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- 13(35) persists on smaller balls and with larger constants. -/
theorem SecondOrderLipschitzBound.mono {f : E → ℝ} {x : E} {ε ε' κ κ' : ℝ}
    (h : SecondOrderLipschitzBound f x ε κ) (hε : ε' ≤ ε) (hκ : κ ≤ κ') :
    SecondOrderLipschitzBound f x ε' κ' := by
  intro y w z hy hw hz
  refine (h y w z (hy.trans hε) (hw.trans hε) (hz.trans hε)).trans ?_
  have := mul_nonneg (norm_nonneg w) (norm_nonneg z)
  nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A function continuous at `x̄` is bounded on a ball around `x̄`. -/
theorem exists_abs_le_of_continuousAt {f : E → ℝ} {x : E} (hf : ContinuousAt f x) :
    ∃ ε > 0, ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ |f x| + 1 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hf 1 one_pos
  refine ⟨δ / 2, by positivity, fun y hy ↦ ?_⟩
  have h := hball (show dist y x < δ by rw [dist_eq_norm]; linarith)
  rw [Real.dist_eq] at h
  have := abs_sub_abs_le_abs_sub (f y) (f x)
  linarith

/-! ### The Lipschitz modulus of `∇f` -/

/-- `lip ∇f(x̄) ≤ c` when every generalized Hessian has norm at most `c` (9.54 with 13(33)). -/
theorem lipschitzModulus_gradient_le {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : IsC1PlusOn f O)
    {x : E} (hx : x ∈ O) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ B ∈ reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x,
      ‖B‖ ≤ c) :
    lipschitzModulus (gradient f) x ≤ ENNReal.ofReal c := by
  borelize E
  have hg : ∀ y ∈ O, StrictlyContinuousAt (gradient f) y := fun y hy ↦ (hf y hy).2
  rw [← svOuterNorm_strictGraphicalDerivative_singleton (hg x hx).continuousAt,
    svOuterNorm_le_iff_ball]
  intro w hw ζ hζ
  have hh := (convexHull_strictGraphicalDerivative_eq_reachableJacobians hO hg
    (D := {y ∈ O | DifferentiableAt ℝ (gradient f) y}) (fun _ hy ↦ hy.2) (by simp) hx w).1
  have hmem : ζ ∈ convexHull ℝ ((fun A : E →L[ℝ] E ↦ A w) ''
      reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x) :=
    hh ▸ subset_convexHull ℝ _ hζ
  have hsub : (fun A : E →L[ℝ] E ↦ A w) ''
      reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x ⊆
      closedBall 0 c := by
    rintro _ ⟨B, hB, rfl⟩
    rw [mem_closedBall_zero_iff]
    calc ‖B w‖ ≤ ‖B‖ * ‖w‖ := B.le_opNorm w
      _ ≤ c * 1 := mul_le_mul (hc B hB) hw (norm_nonneg _) hc0
      _ = c := mul_one c
  have hζc : ‖ζ‖ ≤ c := by
    have := convexHull_min hsub (convex_closedBall 0 c) hmem
    rwa [mem_closedBall_zero_iff] at this
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  exact ENNReal.ofReal_le_ofReal hζc

/-- A generalized Hessian of maximal norm. -/
theorem exists_reachableJacobian_max_norm {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : IsC1PlusOn f O) {x : E} (hx : x ∈ O) :
    ∃ A ∈ reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x,
      ∀ B ∈ reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x,
        ‖B‖ ≤ ‖A‖ := by
  borelize E
  obtain ⟨hne, hcpt, -⟩ := generalization_of_second_derivative_symmetry hO hf
    (D := {y ∈ O | DifferentiableAt ℝ (gradient f) y}) (fun _ hy ↦ hy) (by simp) hx
  obtain ⟨A, hA, hmax⟩ := hcpt.exists_isMaxOn hne continuous_norm.continuousOn
  exact ⟨A, hA, fun B hB ↦ hmax hB⟩

/-! ### Exercise 13.55 -/

/-- **Exercise 13.55** (second-order Lipschitz continuity), corrected: `f` is of class `C¹⁺` around
`x̄` if and only if, for some `ε > 0`, it is bounded on `IB(x̄, ε)` and satisfies 13(35) there with
some `κ ≥ 0`.  As printed ("finite around `x̄`" instead of bounded) the sufficiency fails
(`hamelFunction_counterexample`). -/
theorem second_order_lipschitz_continuity {f : E → ℝ} {x : E} :
    (∃ O, IsOpen O ∧ x ∈ O ∧ IsC1PlusOn f O) ↔
      ∃ ε > 0, (∃ M, ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) ∧
        ∃ κ ≥ 0, SecondOrderLipschitzBound f x ε κ := by
  constructor
  · rintro ⟨O, hO, hx, hf⟩
    obtain ⟨L, U, hU, hL⟩ := strictlyContinuousAt_iff.1 (hf x hx).2
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 (inter_mem hU (hO.mem_nhds hx))
    obtain ⟨ε₁, hε₁, hb⟩ := exists_abs_le_of_continuousAt (hf x hx).1.continuousAt
    have hbound := secondOrderLipschitzBound_of_lipschitzOnWith (r := r) (L := L)
      (fun y hy ↦ (hf y (hrU hy).2).1) (hL.mono fun y hy ↦ (hrU hy).1)
    exact ⟨min ε₁ (r / 4), by positivity, ⟨_, fun y hy ↦ hb y (hy.trans (min_le_left _ _))⟩, L,
      L.coe_nonneg, hbound.mono (min_le_right _ _) le_rfl⟩
  · rintro ⟨ε, hε, ⟨M, hM⟩, κ, hκ, h⟩
    exact ⟨_, isOpen_ball, mem_ball_self (by positivity), (h.isC1PlusOn hε hκ hM).1⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- 13(35) as printed (an upper bound, no absolute value) on `IB(x̄, ε)` gives the two-sided
`SecondOrderLipschitzBound` on `IB(x̄, ε/2)`: replacing `(y, w)` by `(y + w, -w)` changes the sign
of the mixed difference. -/
theorem secondOrderLipschitzBound_of_one_sided {f : E → ℝ} {x : E} {ε κ : ℝ}
    (h : ∀ y w z : E, ‖y - x‖ ≤ ε → ‖w‖ ≤ ε → ‖z‖ ≤ ε →
      f (y + w + z) - f (y + w) - f (y + z) + f y ≤ κ * ‖w‖ * ‖z‖) :
    SecondOrderLipschitzBound f x (ε / 2) κ := by
  intro y w z hy hw hz
  have hε : 0 ≤ ε := by linarith [norm_nonneg w]
  rw [abs_le]
  constructor
  · have hyw : ‖y + w - x‖ ≤ ε := by
      calc ‖y + w - x‖ = ‖(y - x) + w‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖w‖ := norm_add_le _ _
        _ ≤ ε := by linarith
    have := h (y + w) (-w) z hyw (by rw [norm_neg]; linarith) (by linarith)
    rw [norm_neg, add_neg_cancel_right] at this
    linarith
  · exact h y w z (by linarith) (by linarith) (by linarith)

/-- **Exercise 13.55** with 13(35) exactly as printed (an upper bound, no absolute value), and with
the boundedness of the corrected statement: `f` is of class `C¹⁺` around `x̄` if and only if, for
some `ε > 0`, it is bounded on `IB(x̄, ε)` and
`f(y + w + z) - f(y + w) - f(y + z) + f(y) ≤ κ‖w‖‖z‖` there with some `κ ≥ 0`. -/
theorem second_order_lipschitz_continuity_one_sided {f : E → ℝ} {x : E} :
    (∃ O, IsOpen O ∧ x ∈ O ∧ IsC1PlusOn f O) ↔
      ∃ ε > 0, (∃ M, ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) ∧
        ∃ κ ≥ 0, ∀ y w z : E, ‖y - x‖ ≤ ε → ‖w‖ ≤ ε → ‖z‖ ≤ ε →
          f (y + w + z) - f (y + w) - f (y + z) + f y ≤ κ * ‖w‖ * ‖z‖ := by
  rw [second_order_lipschitz_continuity]
  constructor
  · rintro ⟨ε, hε, hM, κ, hκ, hb⟩
    exact ⟨ε, hε, hM, κ, hκ, fun y w z hy hw hz ↦ (le_abs_self _).trans (hb y w z hy hw hz)⟩
  · rintro ⟨ε, hε, ⟨M, hM⟩, κ, hκ, hb⟩
    exact ⟨ε / 2, by positivity, ⟨M, fun y hy ↦ hM y (by linarith)⟩, κ, hκ,
      secondOrderLipschitzBound_of_one_sided hb⟩

/-- The quotient `[f(x + w + z) - f(x + w) - f(x + z) + f(x)]/(‖w‖‖z‖)` of Exercise 13.55, at
`p = (x, w, z)`. -/
noncomputable def mixedDifferenceRatio (f : E → ℝ) (p : E × E × E) : ℝ :=
  (f (p.1 + p.2.1 + p.2.2) - f (p.1 + p.2.1) - f (p.1 + p.2.2) + f p.1) / (‖p.2.1‖ * ‖p.2.2‖)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Under 13(35) on `IB(x̄, ε)`, eventually as `x → x̄`, `w, z → 0` (`w, z ≠ 0`), the quotient is
bounded in absolute value by `κ`. -/
theorem SecondOrderLipschitzBound.eventually_abs_ratio_le {f : E → ℝ} {x : E} {ε κ : ℝ}
    (h : SecondOrderLipschitzBound f x ε κ) (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 x ×ˢ (𝓝[≠] (0 : E) ×ˢ 𝓝[≠] (0 : E)), |mixedDifferenceRatio f p| ≤ κ := by
  have h0 : ∀ᶠ y in 𝓝 x, ‖y - x‖ ≤ ε := by
    filter_upwards [Metric.closedBall_mem_nhds x hε] with y hy
    rwa [mem_closedBall, dist_eq_norm] at hy
  have h1 : ∀ᶠ p in 𝓝 x ×ˢ (𝓝[≠] (0 : E) ×ˢ 𝓝[≠] (0 : E)), ‖p.1 - x‖ ≤ ε :=
    tendsto_fst.eventually h0
  have hw : ∀ᶠ v in 𝓝[≠] (0 : E), v ≠ 0 ∧ ‖v‖ ≤ ε := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Metric.closedBall_mem_nhds (0 : E) hε)] with v hv hvb
    exact ⟨hv, by rwa [mem_closedBall, dist_zero_right] at hvb⟩
  have h2 : ∀ᶠ p in 𝓝 x ×ˢ (𝓝[≠] (0 : E) ×ˢ 𝓝[≠] (0 : E)), p.2.1 ≠ 0 ∧ ‖p.2.1‖ ≤ ε :=
    (tendsto_fst.comp tendsto_snd).eventually hw
  have h3 : ∀ᶠ p in 𝓝 x ×ˢ (𝓝[≠] (0 : E) ×ˢ 𝓝[≠] (0 : E)), p.2.2 ≠ 0 ∧ ‖p.2.2‖ ≤ ε :=
    (tendsto_snd.comp tendsto_snd).eventually hw
  filter_upwards [h1, h2, h3] with p hp1 ⟨hp2, hp2'⟩ ⟨hp3, hp3'⟩
  have hpos : 0 < ‖p.2.1‖ * ‖p.2.2‖ := mul_pos (norm_pos_iff.2 hp2) (norm_pos_iff.2 hp3)
  rw [mixedDifferenceRatio, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, ← mul_assoc]
  exact h _ _ _ hp1 hp2' hp3'

/-- **Exercise 13.55**, the formula: for `f` of class `C¹⁺` on an open `O ∋ x̄`, let `A` be a
generalized Hessian of maximal norm (over `D = {x ∈ O ∣ ∇f differentiable at x}`).  Then the upper
limit of `[f(x + w + z) - f(x + w) - f(x + z) + f(x)]/(‖w‖‖z‖)` (or of its absolute value) as
`x → x̄`, `w → 0`, `z → 0` (`w, z ≠ 0`) is `‖A‖ = max {‖B‖ ∣ B ∈ ∇̄²f(x̄)}`, and `‖A‖` is the lowest
limiting value of the constants in 13(35) as `ε ↓ 0`: 13(35) holds on some ball for every
`κ > ‖A‖`, and on no ball for any `κ < ‖A‖`. -/
theorem second_order_lipschitz_modulus [Nontrivial E] {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : IsC1PlusOn f O) {x : E} (hx : x ∈ O) :
    ∃ A ∈ reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x,
      (∀ B ∈ reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x,
        ‖B‖ ≤ ‖A‖) ∧
      limsup (fun p ↦ ((mixedDifferenceRatio f p : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[≠] (0 : E) ×ˢ 𝓝[≠] (0 : E))) = ((‖A‖ : ℝ) : EReal) ∧
      limsup (fun p ↦ ((|mixedDifferenceRatio f p| : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[≠] (0 : E) ×ˢ 𝓝[≠] (0 : E))) = ((‖A‖ : ℝ) : EReal) ∧
      (∀ κ > ‖A‖, ∃ ε > 0, SecondOrderLipschitzBound f x ε κ) ∧
      (∀ κ < ‖A‖, ∀ ε > 0, ¬ SecondOrderLipschitzBound f x ε κ) := by
  classical
  borelize E
  set D := {y ∈ O | DifferentiableAt ℝ (gradient f) y}
  set F := 𝓝 x ×ˢ (𝓝[≠] (0 : E) ×ˢ 𝓝[≠] (0 : E))
  obtain ⟨A, hA, hmax⟩ := exists_reachableJacobian_max_norm hO hf hx
  -- the upper estimate
  have hupper : ∀ κ > ‖A‖, ∃ ε > 0, SecondOrderLipschitzBound f x ε κ := by
    intro κ hκ
    have hκ0 : 0 < κ := lt_of_le_of_lt (norm_nonneg A) hκ
    have hlip := lipschitzModulus_gradient_le hO hf hx (norm_nonneg A) hmax
    have hlt : lipschitzModulus (gradient f) x < ((Real.toNNReal κ : ℝ≥0) : ℝ≥0∞) := by
      refine lt_of_le_of_lt hlip ?_
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hκ0.le]
      exact (ENNReal.ofReal_lt_ofReal_iff hκ0).2 hκ
    obtain ⟨U, hU, hLU⟩ := exists_lipschitzOnWith_of_modulus_lt hlt
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 (inter_mem hU (hO.mem_nhds hx))
    have hb := secondOrderLipschitzBound_of_lipschitzOnWith (r := r)
      (fun y hy ↦ (hf y (hrU hy).2).1) (hLU.mono fun y hy ↦ (hrU hy).1)
    rw [Real.coe_toNNReal _ hκ0.le] at hb
    exact ⟨r / 4, by positivity, hb⟩
  have hle_of : ∀ κ : ℝ, ∀ ε > 0, SecondOrderLipschitzBound f x ε κ →
      limsup (fun p ↦ ((|mixedDifferenceRatio f p| : ℝ) : EReal)) F ≤ (κ : EReal) := by
    intro κ ε hε hb
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hb.eventually_abs_ratio_le hε] with p hp
    exact EReal.coe_le_coe_iff.2 hp
  have habs_le : limsup (fun p ↦ ((|mixedDifferenceRatio f p| : ℝ) : EReal)) F ≤
      ((‖A‖ : ℝ) : EReal) := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨κ, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    obtain ⟨ε, hε, hb⟩ := hupper κ (EReal.coe_lt_coe_iff.1 h1)
    exact absurd (hle_of κ ε hε hb) (not_le.2 h2)
  -- the lower estimate along directions attaining `‖A‖`
  obtain ⟨w, hw1, hAw⟩ := exists_unit_attaining_opNorm A
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  set z : E := if A w = 0 then w else ‖A w‖⁻¹ • A w with hz
  have hz1 : ‖z‖ = 1 := by
    rw [hz]; split_ifs with h0
    · exact hw1
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  have hz0 : z ≠ 0 := by rintro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  have hzAw : ⟪z, A w⟫_ℝ = ‖A‖ := by
    rw [hz]; split_ifs with h0
    · rw [h0, inner_zero_right, ← hAw, h0, norm_zero]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, ← hAw]
      field_simp [norm_ne_zero_iff.2 h0]
  obtain ⟨-, -, -, -, h34⟩ := generalization_of_second_derivative_symmetry hO hf
    (D := D) (fun _ hy ↦ hy) (by simp [D]) hx
  obtain ⟨A', hA', hmax', -, -, h3, -⟩ := h34 z w
  have hge : ((‖A‖ : ℝ) : EReal) ≤ limsup (fun p ↦ ((mixedDifferenceRatio f p : ℝ) : EReal)) F := by
    have h1 : ((‖A‖ : ℝ) : EReal) ≤ ((⟪z, A' w⟫_ℝ : ℝ) : EReal) := by
      rw [← hzAw]; exact EReal.coe_le_coe_iff.2 (hmax' A hA)
    rw [← h3] at h1
    refine h1.trans ?_
    set g : E × ℝ × ℝ → E × E × E := fun p ↦ (p.1, p.2.1 • w, p.2.2 • z) with hg
    have hsm : ∀ v : E, v ≠ 0 → Tendsto (fun τ : ℝ ↦ τ • v) (𝓝[>] 0) (𝓝[≠] (0 : E)) := by
      intro v hv
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : Continuous (fun τ : ℝ ↦ τ • v) := by fun_prop
        have := hc.tendsto 0
        rw [zero_smul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        exact smul_ne_zero (ne_of_gt hτ) hv
    have hgt : Tendsto g (𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))) F :=
      tendsto_fst.prodMk (((hsm w hw0).comp (tendsto_fst.comp tendsto_snd)).prodMk
        ((hsm z hz0).comp (tendsto_snd.comp tendsto_snd)))
    have heq : (fun p : E × ℝ × ℝ ↦ ((mixedSecondDifference f p.1 w z p.2.1 p.2.2 : ℝ) : EReal))
        =ᶠ[𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))]
        fun p ↦ ((mixedDifferenceRatio f (g p) : ℝ) : EReal) := by
      have hpos : ∀ᶠ p in 𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)), 0 < p.2.1 ∧ 0 < p.2.2 :=
        ((tendsto_fst.comp tendsto_snd).eventually self_mem_nhdsWithin).and
          ((tendsto_snd.comp tendsto_snd).eventually self_mem_nhdsWithin)
      filter_upwards [hpos] with p ⟨hp1, hp2⟩
      simp only [hg, mixedDifferenceRatio, mixedSecondDifference, norm_smul,
        Real.norm_of_nonneg hp1.le, Real.norm_of_nonneg hp2.le, hw1, hz1, mul_one]
    rw [limsup_congr heq]
    exact ereal_limsup_le_of_tendsto hgt fun _ ↦ rfl
  have hmono : limsup (fun p ↦ ((mixedDifferenceRatio f p : ℝ) : EReal)) F ≤
      limsup (fun p ↦ ((|mixedDifferenceRatio f p| : ℝ) : EReal)) F :=
    limsup_le_limsup (Eventually.of_forall fun p ↦ EReal.coe_le_coe_iff.2 (le_abs_self _))
      (by isBoundedDefault) (by isBoundedDefault)
  have hr1 : limsup (fun p ↦ ((mixedDifferenceRatio f p : ℝ) : EReal)) F = ((‖A‖ : ℝ) : EReal) :=
    le_antisymm (hmono.trans habs_le) hge
  have hr2 : limsup (fun p ↦ ((|mixedDifferenceRatio f p| : ℝ) : EReal)) F =
      ((‖A‖ : ℝ) : EReal) := le_antisymm habs_le (hge.trans hmono)
  refine ⟨A, hA, hmax, hr1, hr2, hupper, fun κ hκ ε hε hb ↦ ?_⟩
  have := hle_of κ ε hε hb
  rw [hr2] at this
  exact absurd (EReal.coe_le_coe_iff.1 this) (not_le.2 hκ)

/-! ### From directional limits to 13(35) -/

omit [FiniteDimensional ℝ E] in
/-- Telescoping along an orthonormal basis: steps `t • bᵢ` changing `φ` by at most `K|t|` give
`|φ(u + w) - φ(u)| ≤ K ∑ᵢ |⟪bᵢ, w⟫|`. -/
theorem abs_sub_le_of_basis_steps {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {φ : E → ℝ} {u : E} {R K : ℝ}
    (hstep : ∀ v, ‖v - u‖ ≤ R → ∀ i, ∀ t : ℝ, |t| ≤ R → |φ (v + t • b i) - φ v| ≤ K * |t|)
    {w : E} (hw : ∑ i, |⟪b i, w⟫_ℝ| ≤ R) :
    |φ (u + w) - φ u| ≤ K * ∑ i, |⟪b i, w⟫_ℝ| := by
  classical
  have key : ∀ s : Finset ι, ∑ i ∈ s, |⟪b i, w⟫_ℝ| ≤ R →
      |φ (u + ∑ i ∈ s, ⟪b i, w⟫_ℝ • b i) - φ u| ≤ K * ∑ i ∈ s, |⟪b i, w⟫_ℝ| := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert j s hj ih =>
      intro hs
      simp only [Finset.sum_insert hj] at hs ⊢
      have hnn : 0 ≤ ∑ i ∈ s, |⟪b i, w⟫_ℝ| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
      have hs' : ∑ i ∈ s, |⟪b i, w⟫_ℝ| ≤ R := by linarith [abs_nonneg ⟪b j, w⟫_ℝ]
      have hj' : |⟪b j, w⟫_ℝ| ≤ R := by linarith
      set v := u + ∑ i ∈ s, ⟪b i, w⟫_ℝ • b i with hv_def
      have hv : ‖v - u‖ ≤ R := by
        calc ‖v - u‖ = ‖∑ i ∈ s, ⟪b i, w⟫_ℝ • b i‖ := by rw [hv_def, add_sub_cancel_left]
          _ ≤ ∑ i ∈ s, ‖⟪b i, w⟫_ℝ • b i‖ := norm_sum_le _ _
          _ = ∑ i ∈ s, |⟪b i, w⟫_ℝ| := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]
          _ ≤ R := hs'
      have h1 := hstep v hv j _ hj'
      have h2 := ih hs'
      rw [show u + (⟪b j, w⟫_ℝ • b j + ∑ i ∈ s, ⟪b i, w⟫_ℝ • b i) = v + ⟪b j, w⟫_ℝ • b j by
        rw [hv_def]; abel]
      calc |φ (v + ⟪b j, w⟫_ℝ • b j) - φ u| ≤
            |φ (v + ⟪b j, w⟫_ℝ • b j) - φ v| + |φ v - φ u| := abs_sub_le _ _ _
        _ ≤ K * |⟪b j, w⟫_ℝ| + K * ∑ i ∈ s, |⟪b i, w⟫_ℝ| := add_le_add h1 h2
        _ = K * (|⟪b j, w⟫_ℝ| + ∑ i ∈ s, |⟪b i, w⟫_ℝ|) := by ring
  have h := key Finset.univ hw
  rwa [b.sum_repr'] at h

omit [FiniteDimensional ℝ E] in
theorem sum_abs_inner_basis_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (w : E) :
    ∑ i, |⟪b i, w⟫_ℝ| ≤ Fintype.card ι * ‖w‖ := by
  calc ∑ i, |⟪b i, w⟫_ℝ| ≤ ∑ _i : ι, ‖w‖ := by
        refine Finset.sum_le_sum fun i _ ↦ (abs_real_inner_le_norm _ _).trans ?_
        rw [b.orthonormal.1 i, one_mul]
    _ = Fintype.card ι * ‖w‖ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

omit [FiniteDimensional ℝ E] in
/-- Limits of the mixed second differences in the finitely many directions `±bᵢ`, `±bⱼ` bound the
mixed differences along the coordinate directions uniformly near `x̄`. -/
theorem exists_coordinate_mixed_bound {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {f : E → ℝ} {x : E}
    (hlim : ∀ w z : E, ∃ L, Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
      (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 L)) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ y, ‖y - x‖ < δ → ∀ i j, ∀ t s : ℝ, |t| < δ → |s| < δ →
      |f (y + t • b i + s • b j) - f (y + t • b i) - f (y + s • b j) + f y| ≤ C * |t| * |s| := by
  classical
  set sg : Bool → ℝ := fun e ↦ if e then 1 else -1 with hsg
  set dir : ι × ι × Bool × Bool → E × E := fun k ↦ (sg k.2.2.1 • b k.1, sg k.2.2.2 • b k.2.1)
  choose L hL using fun k : ι × ι × Bool × Bool ↦ hlim (dir k).1 (dir k).2
  set C : ℝ := ∑ k, (|L k| + 1)
  have hC : ∀ k, |L k| + 1 ≤ C := fun k ↦
    Finset.single_le_sum (f := fun k ↦ |L k| + 1) (fun _ _ ↦ by positivity) (Finset.mem_univ k)
  have hev : ∀ᶠ p in 𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)), ∀ k,
      |mixedSecondDifference f p.1 (dir k).1 (dir k).2 p.2.1 p.2.2| ≤ C := by
    refine eventually_all.2 fun k ↦ ?_
    filter_upwards [(hL k).eventually (Metric.ball_mem_nhds (L k) one_pos)] with p hp
    rw [Real.dist_eq] at hp
    have := abs_sub_abs_le_abs_sub (mixedSecondDifference f p.1 (dir k).1 (dir k).2 p.2.1 p.2.2)
      (L k)
    linarith [hC k]
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.1 hev
  obtain ⟨V₁, hV₁, V₂, hV₂, hV12⟩ := Filter.mem_prod_iff.1 hV
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨a₁, ha₁, hI₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hV₁
  obtain ⟨a₂, ha₂, hI₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hV₂
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ by positivity
  refine ⟨min r (min a₁ a₂), lt_min hr (lt_min ha₁ ha₂), C, hC0, ?_⟩
  intro y hy i j t s ht hs
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  set k : ι × ι × Bool × Bool := (i, j, decide (0 < t), decide (0 < s))
  have hsgn : ∀ (c : ℝ) (v : E), c ≠ 0 → c • v = |c| • (sg (decide (0 < c)) • v) := by
    intro c v hc
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · simp [hsg, hneg.not_gt, abs_of_neg hneg]
    · simp [hsg, hpos, abs_of_pos hpos]
  have hmem : (y, |t|, |s|) ∈ U ×ˢ V := by
    refine ⟨hrU (by rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_left _ _)), ?_⟩
    refine hV12 ⟨hI₁ ⟨abs_pos.2 ht0, lt_of_lt_of_le ht ?_⟩, hI₂ ⟨abs_pos.2 hs0,
      lt_of_lt_of_le hs ?_⟩⟩
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hb := hUV hmem k
  simp only [mixedSecondDifference] at hb
  rw [hsgn t (b i) ht0, hsgn s (b j) hs0]
  have hpos : 0 < |t| * |s| := mul_pos (abs_pos.2 ht0) (abs_pos.2 hs0)
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at hb
  calc _ ≤ C * (|t| * |s|) := hb
    _ = C * |t| * |s| := by ring

/-- Limits of all mixed second differences at `x̄` give 13(35) near `x̄`. -/
theorem secondOrderLipschitzBound_of_tendsto {f : E → ℝ} {x : E}
    (hlim : ∀ w z : E, ∃ L, Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
      (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 L)) :
    ∃ ε > 0, ∃ κ ≥ 0, SecondOrderLipschitzBound f x ε κ := by
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨δ, hδ, C, hC, hbound⟩ := exists_coordinate_mixed_bound b hlim
  set N : ℝ := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set ρ := δ / (4 * (N + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hNρ : N * ρ < δ := by
    rw [hρ, mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have h2Nρ : ρ + N * ρ + N * ρ < δ := by
    rw [hρ]
    have : ρ * (4 * (N + 1)) = δ := by rw [hρ]; field_simp
    nlinarith
  refine ⟨ρ, hρ0, C * N * N, by positivity, ?_⟩
  intro u w z hu hw hz
  -- Stage 1: along `w`, with `z = s • bⱼ`
  have stage1 : ∀ v, ‖v - x‖ + N * ρ < δ → ∀ j, ∀ s : ℝ, |s| < δ →
      |f (v + w + s • b j) - f (v + w) - f (v + s • b j) + f v| ≤ C * N * |s| * ‖w‖ := by
    intro v hv j s hs
    have hstep : ∀ v', ‖v' - v‖ ≤ N * ρ → ∀ i, ∀ t : ℝ, |t| ≤ N * ρ →
        |(f (v' + t • b i + s • b j) - f (v' + t • b i)) - (f (v' + s • b j) - f v')| ≤
          (C * |s|) * |t| := by
      intro v' hv' i t ht
      have hv'x : ‖v' - x‖ < δ := by
        calc ‖v' - x‖ = ‖(v' - v) + (v - x)‖ := by congr 1; abel
          _ ≤ ‖v' - v‖ + ‖v - x‖ := norm_add_le _ _
          _ < δ := by linarith
      have := hbound v' hv'x i j t s (lt_of_le_of_lt ht hNρ) hs
      calc _ = |f (v' + t • b i + s • b j) - f (v' + t • b i) - f (v' + s • b j) + f v'| := by
            ring_nf
        _ ≤ C * |t| * |s| := this
        _ = C * |s| * |t| := by ring
    have hw' : ∑ i, |⟪b i, w⟫_ℝ| ≤ N * ρ :=
      (sum_abs_inner_basis_le b w).trans (mul_le_mul_of_nonneg_left hw hN)
    have h := abs_sub_le_of_basis_steps b (φ := fun v' ↦ f (v' + s • b j) - f v') hstep hw'
    simp only at h
    calc |f (v + w + s • b j) - f (v + w) - f (v + s • b j) + f v| =
          |(f (v + w + s • b j) - f (v + w)) - (f (v + s • b j) - f v)| := by ring_nf
      _ ≤ C * |s| * ∑ i, |⟪b i, w⟫_ℝ| := h
      _ ≤ C * |s| * (N * ‖w‖) := by
          gcongr
          exact sum_abs_inner_basis_le b w
      _ = C * N * |s| * ‖w‖ := by ring
  -- Stage 2: along `z`
  have hstep2 : ∀ v, ‖v - u‖ ≤ N * ρ → ∀ j, ∀ s : ℝ, |s| ≤ N * ρ →
      |(f (v + s • b j + w) - f (v + s • b j)) - (f (v + w) - f v)| ≤ (C * N * ‖w‖) * |s| := by
    intro v hv j s hs
    have hvx : ‖v - x‖ + N * ρ < δ := by
      have : ‖v - x‖ ≤ ‖v - u‖ + ‖u - x‖ := by
        calc ‖v - x‖ = ‖(v - u) + (u - x)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    have := stage1 v hvx j s (lt_of_le_of_lt hs hNρ)
    rw [add_right_comm v (s • b j) w]
    calc _ = |f (v + w + s • b j) - f (v + w) - f (v + s • b j) + f v| := by ring_nf
      _ ≤ C * N * |s| * ‖w‖ := this
      _ = C * N * ‖w‖ * |s| := by ring
  have hz' : ∑ i, |⟪b i, z⟫_ℝ| ≤ N * ρ :=
    (sum_abs_inner_basis_le b z).trans (mul_le_mul_of_nonneg_left hz hN)
  have h := abs_sub_le_of_basis_steps b (φ := fun v ↦ f (v + w) - f v) hstep2 hz'
  simp only at h
  rw [add_right_comm u z w] at h
  calc |f (u + w + z) - f (u + w) - f (u + z) + f u| =
        |(f (u + w + z) - f (u + z)) - (f (u + w) - f u)| := by ring_nf
    _ ≤ C * N * ‖w‖ * ∑ i, |⟪b i, z⟫_ℝ| := h
    _ ≤ C * N * ‖w‖ * (N * ‖z‖) := by
        gcongr
        exact sum_abs_inner_basis_le b z
    _ = C * N * N * ‖w‖ * ‖z‖ := by ring

/-! ### Proposition 13.56 -/

omit [FiniteDimensional ℝ E] in
/-- Reversing `z` in a mixed second difference: `Δ(x; w, -z) = -Δ(x - σz; w, z)`. -/
theorem mixedSecondDifference_neg_right (f : E → ℝ) (y w z : E) (τ σ : ℝ) :
    mixedSecondDifference f y w (-z) τ σ = -mixedSecondDifference f (y - σ • z) w z τ σ := by
  have e1 : y - σ • z + τ • w + σ • z = y + τ • w := by abel
  have e2 : y - σ • z + σ • z = y := by abel
  have e3 : y - σ • z + τ • w = y + τ • w + -(σ • z) := by abel
  have e4 : y + -(σ • z) = y - σ • z := by abel
  rw [mixedSecondDifference, mixedSecondDifference, smul_neg, e1, e2, e3, e4]
  ring

omit [FiniteDimensional ℝ E] in
/-- The limits of the mixed second differences are odd in `z`. -/
theorem tendsto_mixedSecondDifference_neg_right {f : E → ℝ} {x w z : E} {L : ℝ}
    (h : Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
      (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 L)) :
    Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w (-z) p.2.1 p.2.2)
      (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 (-L)) := by
  have hshift : Tendsto (fun p : E × ℝ × ℝ ↦ (p.1 - p.2.2 • z, p.2))
      (𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))) (𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))) := by
    refine Tendsto.prodMk ?_ tendsto_snd
    have h1 : Tendsto (fun p : E × ℝ × ℝ ↦ p.2.2) (𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))) (𝓝 0) :=
      ((tendsto_snd.comp tendsto_snd).mono_right nhdsWithin_le_nhds)
    have h2 := tendsto_fst.sub (h1.smul_const z)
    rwa [zero_smul, sub_zero] at h2
  have := (h.comp hshift).neg
  refine this.congr fun p ↦ ?_
  simp only [Function.comp, mixedSecondDifference_neg_right]

/-- If the mixed second differences converge for all directions, all generalized Hessians agree. -/
theorem reachableJacobians_eq_of_tendsto {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : IsC1PlusOn f O) {x : E} (hx : x ∈ O)
    (hlim : ∀ w z : E, ∃ L, Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
      (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 L))
    {B B' : E →L[ℝ] E}
    (hB : B ∈ reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x)
    (hB' : B' ∈ reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x) :
    B = B' := by
  borelize E
  obtain ⟨-, -, -, -, h34⟩ := generalization_of_second_derivative_symmetry hO hf
    (D := {y ∈ O | DifferentiableAt ℝ (gradient f) y}) (fun _ hy ↦ hy) (by simp) hx
  -- the limit is the maximum of `⟪z, Aw⟫` over the generalized Hessians
  have hval : ∀ w z L, Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
      (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 L) → ∀ C ∈ reachableJacobians (gradient f)
        {y ∈ O | DifferentiableAt ℝ (gradient f) y} x, ⟪z, C w⟫_ℝ ≤ L := by
    intro w z L hL C hC
    obtain ⟨A, -, hmax, -, -, h3, -⟩ := h34 z w
    have hE : Tendsto (fun p : E × ℝ × ℝ ↦ ((mixedSecondDifference f p.1 w z p.2.1 p.2.2 : ℝ) :
        EReal)) (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 (L : EReal)) :=
      (continuous_coe_real_ereal.tendsto L).comp hL
    rw [hE.limsup_eq, EReal.coe_eq_coe_iff] at h3
    rw [h3]
    exact hmax C hC
  have heq : ∀ C ∈ reachableJacobians (gradient f) {y ∈ O | DifferentiableAt ℝ (gradient f) y} x,
      ∀ w z, ∀ L, Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 L) → ⟪z, C w⟫_ℝ = L := by
    intro C hC w z L hL
    refine le_antisymm (hval w z L hL C hC) ?_
    have h2 := hval w (-z) (-L) (tendsto_mixedSecondDifference_neg_right hL) C hC
    rw [inner_neg_left] at h2
    linarith
  refine ContinuousLinearMap.ext fun w ↦ ext_inner_left ℝ fun z ↦ ?_
  obtain ⟨L, hL⟩ := hlim w z
  rw [heq B hB w z L hL, heq B' hB' w z L hL]

/-- A strictly continuous mapping with a single reachable Jacobian `A` at `x̄` is strictly
differentiable at `x̄` with derivative `A` (as in 9.64). -/
theorem hasStrictFDerivAt_of_reachableJacobians_eq {F : E → E} {O : Set E} (hO : IsOpen O)
    (hF : ∀ y ∈ O, StrictlyContinuousAt F y) {x : E} (hx : x ∈ O) {A : E →L[ℝ] E}
    (hA : A ∈ reachableJacobians F {y ∈ O | DifferentiableAt ℝ F y} x)
    (hsub : ∀ B ∈ reachableJacobians F {y ∈ O | DifferentiableAt ℝ F y} x, B = A) :
    HasStrictFDerivAt F A x := by
  borelize E
  apply (hasStrictFDerivAt_iff_strictGraphicalDerivative_linear (hF x hx).continuousAt).mpr
  funext w
  change strictGraphicalDerivative (svSingleton F) x (F x) w = {A w}
  have hJ : reachableJacobians F {y ∈ O | DifferentiableAt ℝ F y} x = {A} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨hA, hsub⟩
  have hh := (convexHull_strictGraphicalDerivative_eq_reachableJacobians hO hF
    (D := {y ∈ O | DifferentiableAt ℝ F y}) (fun _ hy ↦ hy.2) (by simp) hx w).2
  rw [hJ, convexHull_singleton, image_singleton] at hh
  have hsub' : strictGraphicalDerivative (svSingleton F) x (F x) w ⊆ {A w} :=
    (subset_convexHull ℝ _).trans hh.subset
  obtain ⟨v, hv⟩ := ((hF x hx).strictGraphicalDerivative_nonempty_compact w).1
  exact hsub'.antisymm (singleton_subset_iff.mpr ((mem_singleton_iff.mp (hsub' hv)) ▸ hv))

/-- **Proposition 13.56** (strict second-order differentiability), with (c) corrected to require `f`
bounded around `x̄`.  The following are equivalent:
* (a) `f` is differentiable on a neighborhood of `x̄` and `∇f` is strictly differentiable at `x̄`;
* (b) `f` is of class `C¹⁺` on a neighborhood of `x̄`, twice differentiable at `x̄` in the classical
  sense (first equivalence) or in the extended sense (second equivalence), and `x ↦ ∇²f(x)`
  (`fderiv ℝ (∇f)`) is continuous at `x̄` relative to its domain of existence (the points where
  `∇f` is differentiable; near `x̄` these are the points of twice differentiability, by
  `IsC1PlusOn.twice_differentiable_iff`);
* (c) `f` is bounded on a neighborhood of `x̄` and for all `z, w` the mixed second differences
  `[f(x + τw + σz) - f(x + τw) - f(x + σz) + f(x)]/(τσ)` converge as `x → x̄`, `τ ↓ 0`, `σ ↓ 0`.
In that case the limit is `⟪z, ∇²f(x̄)w⟫`.  As printed, (c) only asks `f` finite around `x̄`, and
then (c) ⇒ (a) fails (`hamelFunction_counterexample`). -/
theorem strict_second_order_differentiability {f : E → ℝ} {x : E} :
    (((∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) ∧ ∃ A : E →L[ℝ] E, HasStrictFDerivAt (gradient f) A x) ↔
      (∃ O, IsOpen O ∧ x ∈ O ∧ IsC1PlusOn f O) ∧
        (∃ A : E →L[ℝ] E, HasClassicalHessianAt (fun y ↦ (f y : EReal)) x A) ∧
        ContinuousWithinAt (fderiv ℝ (gradient f)) {y | DifferentiableAt ℝ (gradient f) y} x) ∧
    (((∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) ∧ ∃ A : E →L[ℝ] E, HasStrictFDerivAt (gradient f) A x) ↔
      (∃ O, IsOpen O ∧ x ∈ O ∧ IsC1PlusOn f O) ∧
        (∃ A : E →L[ℝ] E, HasExtendedHessianAt (fun y ↦ (f y : EReal)) x A) ∧
        ContinuousWithinAt (fderiv ℝ (gradient f)) {y | DifferentiableAt ℝ (gradient f) y} x) ∧
    (((∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) ∧ ∃ A : E →L[ℝ] E, HasStrictFDerivAt (gradient f) A x) ↔
      (∃ ε > 0, ∃ M, ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M) ∧
        ∀ w z : E, ∃ L, Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
          (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 L)) ∧
    ∀ A : E →L[ℝ] E, (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) → HasStrictFDerivAt (gradient f) A x →
      fderiv ℝ (gradient f) x = A ∧ ∀ w z : E,
        Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
          (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 ⟪z, A w⟫_ℝ) := by
  borelize E
  -- (a) ⇒ the `C¹⁺` property
  have hC1 : ∀ A : E →L[ℝ] E, (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) →
      HasStrictFDerivAt (gradient f) A x →
      ∃ O, IsOpen O ∧ x ∈ O ∧ IsC1PlusOn f O := by
    intro A hf hA
    obtain ⟨K, s, hs, hK⟩ := hA.exists_lipschitzOnWith
    refine ⟨interior (s ∩ {y | DifferentiableAt ℝ f y}), isOpen_interior,
      mem_interior_iff_mem_nhds.2 (inter_mem hs hf), fun y hy ↦ ⟨(interior_subset hy).2, ?_⟩⟩
    exact strictlyContinuousAt_iff.2 ⟨K, _, isOpen_interior.mem_nhds hy,
      hK.mono (interior_subset.trans inter_subset_left)⟩
  -- (b) ⇒ (a), given the Hessian at `x̄` as a derivative of `∇f`
  have hba : ∀ O, IsOpen O → x ∈ O → IsC1PlusOn f O → ∀ A : E →L[ℝ] E,
      HasFDerivAt (gradient f) A x →
      ContinuousWithinAt (fderiv ℝ (gradient f)) {y | DifferentiableAt ℝ (gradient f) y} x →
      (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) ∧
        ∃ A : E →L[ℝ] E, HasStrictFDerivAt (gradient f) A x := by
    intro O hO hx hC A hA hc
    refine ⟨Filter.mem_of_superset (hO.mem_nhds hx) fun y hy ↦ (hC y hy).1, _,
      (hasStrictFDerivAt_iff_differentiableAt_continuousWithinAt_fderiv hO
        (fun y hy ↦ (hC y hy).2) hx).2 ⟨hA.differentiableAt, hc.mono fun y hy ↦ hy.2⟩⟩
  have hab : ∀ A : E →L[ℝ] E, (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) →
      HasStrictFDerivAt (gradient f) A x →
      HasFDerivAt (gradient f) A x ∧
        ContinuousWithinAt (fderiv ℝ (gradient f)) {y | DifferentiableAt ℝ (gradient f) y} x :=
    fun A _ hA ↦ ⟨hA.hasFDerivAt, (HasStrictFDerivAt.continuousWithinAt_fderiv hA).2⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, fun A hf hA ↦ ⟨hA.hasFDerivAt.fderiv,
    fun w z ↦ tendsto_mixedSecondDifference_of_hasStrictFDerivAt hf hA w z⟩⟩
  · rintro ⟨hf, A, hA⟩
    exact ⟨hC1 A hf hA, ⟨A, (hasClassicalHessianAt_coe_iff hf).2 (hab A hf hA).1⟩,
      (hab A hf hA).2⟩
  · rintro ⟨⟨O, hO, hx, hC⟩, ⟨A, hH⟩, hc⟩
    have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
      Filter.mem_of_superset (hO.mem_nhds hx) fun y hy ↦ (hC y hy).1
    exact hba O hO hx hC A ((hasClassicalHessianAt_coe_iff hev).1 hH) hc
  · rintro ⟨hf, A, hA⟩
    exact ⟨hC1 A hf hA, ⟨A, (hasExtendedHessianAt_coe_iff hf).2 (hab A hf hA).1⟩,
      (hab A hf hA).2⟩
  · rintro ⟨⟨O, hO, hx, hC⟩, ⟨A, hH⟩, hc⟩
    have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
      Filter.mem_of_superset (hO.mem_nhds hx) fun y hy ↦ (hC y hy).1
    exact hba O hO hx hC A ((hasExtendedHessianAt_coe_iff hev).1 hH) hc
  · rintro ⟨hf, A, hA⟩
    obtain ⟨ε, hε, hb⟩ := exists_abs_le_of_continuousAt hf.self_of_nhds.continuousAt
    exact ⟨⟨ε, hε, _, hb⟩, fun w z ↦ ⟨_, tendsto_mixedSecondDifference_of_hasStrictFDerivAt hf hA w z⟩⟩
  · rintro ⟨⟨ε₀, hε₀, M, hM⟩, hlim⟩
    obtain ⟨ε₁, hε₁, κ, hκ, hb⟩ := secondOrderLipschitzBound_of_tendsto hlim
    set ε := min ε₀ ε₁
    have hε : 0 < ε := lt_min hε₀ hε₁
    have hb' := hb.mono (min_le_right ε₀ ε₁) le_rfl
    have hM' : ∀ y, ‖y - x‖ ≤ ε → |f y| ≤ M := fun y hy ↦ hM y (hy.trans (min_le_left _ _))
    have hC := (hb'.isC1PlusOn hε hκ hM').1
    have hx : x ∈ ball x (ε / 2) := mem_ball_self (by positivity)
    obtain ⟨hne, -⟩ := generalization_of_second_derivative_symmetry isOpen_ball hC
      (D := {y ∈ ball x (ε / 2) | DifferentiableAt ℝ (gradient f) y}) (fun _ hy ↦ hy)
      (by simp [ε]) hx
    obtain ⟨A, hA⟩ := hne
    refine ⟨Filter.mem_of_superset (isOpen_ball.mem_nhds hx) fun y hy ↦ (hC y hy).1, A, ?_⟩
    exact hasStrictFDerivAt_of_reachableJacobians_eq isOpen_ball (fun y hy ↦ (hC y hy).2) hx hA
      fun B hB ↦ reachableJacobians_eq_of_tendsto isOpen_ball hC hx hlim hB hA

end RW
