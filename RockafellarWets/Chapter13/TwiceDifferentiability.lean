/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Twice differentiable functions

Definition 13.1 and Theorem 13.2.

A function `f : E → ℝ̄` is handled through its finite real representative
`y ↦ (f y).toReal` near `x̄`.  The Hessian is a continuous linear map
`A : E →L[ℝ] E`, the coordinate-free form of a matrix, and `∇f` is Mathlib's
`gradient`.  The domain `D` of existence of `∇f` is the set of points where the
representative is differentiable; in the extended sense the expansion of `∇f`
is required along `D`, i.e. along the filter `𝓝[D] x̄`.

The quadratic expansion in 13.2(b) is obtained from the line-integration bound
behind Theorem 9.61 (`sub_le_mul_of_fderiv_le_off_null`), applied to `f` minus
a quadratic whose derivative in the fixed direction `w` is `⟪A(y - x̄), w⟫`.
-/

import RockafellarWets.Chapter13.SecondOrderSemidifferentiability
import RockafellarWets.Chapter9.Rademacher
import RockafellarWets.Chapter9.LineDerivativeBounds
import RockafellarWets.Chapter9.StrictDifferentiability
import RockafellarWets.Chapter9.StrictContinuityCriteria
import RockafellarWets.Chapter9.ClarkeReachableGradients
import RockafellarWets.Chapter12.MonotoneSemidifferentiability
import RockafellarWets.Chapter13.ParabolicSubderivatives

open Filter Set Topology Metric Asymptotics MeasureTheory
open scoped InnerProductSpace NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Definition 13.1 -/

section Definition131

/-- **Definition 13.1(a)**: `f` is twice differentiable at `x̄` in the classical sense with
Hessian `A`: it is finite and differentiable on a neighborhood of `x̄`, and its gradient
mapping is differentiable at `x̄` with Jacobian `A`. -/
def HasClassicalHessianAt (f : E → EReal) (x : E) (A : E →L[ℝ] E) : Prop :=
  (∀ᶠ y in 𝓝 x, f y = ((f y).toReal : EReal) ∧ DifferentiableAt ℝ (fun z ↦ (f z).toReal) y) ∧
    HasFDerivAt (gradient fun z ↦ (f z).toReal) A x

/-- **Definition 13.1(b)**: `f` is twice differentiable at `x̄` in the extended sense with
Hessian `A`: it is differentiable and strictly continuous at `x̄`, and
`∇f(x) = ∇f(x̄) + A[x - x̄] + o(‖x - x̄‖)` for `x ∈ D`, the domain of existence of `∇f`. -/
def HasExtendedHessianAt (f : E → EReal) (x : E) (A : E →L[ℝ] E) : Prop :=
  ERealStrictlyContinuousAt f x ∧ DifferentiableAt ℝ (fun z ↦ (f z).toReal) x ∧
    (fun y ↦ gradient (fun z ↦ (f z).toReal) y - gradient (fun z ↦ (f z).toReal) x - A (y - x))
      =o[𝓝[{y | DifferentiableAt ℝ (fun z ↦ (f z).toReal) y}] x] (fun y ↦ y - x)

/-- **Definition 13.1(c)**: `f` has a quadratic expansion at `x̄` with matrix `A`: it is
differentiable at `x̄` (formula 7(16)) with gradient `v`, and
`f(x) = f(x̄) + ⟪v, x - x̄⟫ + ½⟪x - x̄, A[x - x̄]⟫ + o(‖x - x̄‖²)`. -/
def HasQuadraticExpansionAt (f : E → EReal) (x : E) (A : E →L[ℝ] E) : Prop :=
  ∃ v : E, HasERealGradientAt f x (innerSL ℝ v) ∧
    (fun y ↦ (f y).toReal - (f x).toReal - ⟪v, y - x⟫_ℝ - 1 / 2 * ⟪y - x, A (y - x)⟫_ℝ)
      =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2)

omit [CompleteSpace E] in
/-- Differentiability points of a function that is strictly continuous at `x̄` are dense near
`x̄`. -/
theorem exists_nhds_subset_closure_differentiableAt [FiniteDimensional ℝ E] {f : E → EReal}
    {x : E} (hsc : ERealStrictlyContinuousAt f x) :
    ∃ U ∈ 𝓝 x, IsOpen U ∧
      U ⊆ closure {y ∈ U | DifferentiableAt ℝ (fun z ↦ (f z).toReal) y} := by
  borelize E
  obtain ⟨k, V, hV, hk⟩ := strictlyContinuousAt_iff.1 hsc.2
  obtain ⟨U, hUV, hUo, hxU⟩ := _root_.mem_nhds_iff.1 hV
  refine ⟨U, hUo.mem_nhds hxU, hUo, subset_closure_differentiableAt_of_strictlyContinuousOn
    Measure.addHaar hUo fun y hy ↦ strictlyContinuousAt_iff.2 ⟨k, U, hUo.mem_nhds hy,
      hk.mono hUV⟩⟩

/-- **Definition 13.1(b)**: the Hessian in the extended sense is unique. -/
theorem HasExtendedHessianAt.unique [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    {A B : E →L[ℝ] E} (hA : HasExtendedHessianAt f x A) (hB : HasExtendedHessianAt f x B) :
    A = B := by
  obtain ⟨U, hU, hUo, hdense⟩ := exists_nhds_subset_closure_differentiableAt hA.1
  set D := {y | DifferentiableAt ℝ (fun z ↦ (f z).toReal) y}
  -- `(A - B)(y - x) = o(‖y - x‖)` along `D`
  have ho : (fun y ↦ (A - B) (y - x)) =o[𝓝[D] x] (fun y ↦ y - x) := by
    have := hB.2.2.sub hA.2.2
    refine this.congr_left fun y ↦ ?_
    simp only [ContinuousLinearMap.sub_apply]
    abel
  ext u
  rw [← sub_eq_zero, ← ContinuousLinearMap.sub_apply, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  -- the estimate with constant `ε/(‖u‖+1)` near `x` along `D`, extended by density
  have hε' : 0 < ε / (‖u‖ + 1) := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (isLittleO_iff.1 ho hε')
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hest : ∀ z ∈ ball x (min δ r), ‖(A - B) (z - x)‖ ≤ ε / (‖u‖ + 1) * ‖z - x‖ := by
    intro z hz
    have hzU : z ∈ U := hrU (ball_subset_ball (min_le_right _ _) hz)
    have hcl : IsClosed {y : E | ‖(A - B) (y - x)‖ ≤ ε / (‖u‖ + 1) * ‖y - x‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : ball x (min δ r) ∩ {y ∈ U | DifferentiableAt ℝ (fun z ↦ (f z).toReal) y} ⊆
        {y : E | ‖(A - B) (y - x)‖ ≤ ε / (‖u‖ + 1) * ‖y - x‖} := fun y ⟨hyb, _, hyD⟩ ↦
      hball ⟨ball_subset_ball (min_le_left _ _) hyb, hyD⟩
    have hzcl : z ∈ closure (ball x (min δ r) ∩
        {y ∈ U | DifferentiableAt ℝ (fun z ↦ (f z).toReal) y}) :=
      isOpen_ball.inter_closure ⟨hz, hdense hzU⟩
    exact closure_minimal hsub hcl hzcl
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hε.le]
  · have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
    set t : ℝ := min δ r / (2 * ‖u‖)
    have ht : 0 < t := by positivity
    have hz : x + t • u ∈ ball x (min δ r) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
      have : min δ r / (2 * ‖u‖) * ‖u‖ = min δ r / 2 := by field_simp
      simp only [t, this]
      linarith [lt_min hδ hr]
    have h1 := hest _ hz
    rw [add_sub_cancel_left, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg ht.le] at h1
    have h2 : ‖(A - B) u‖ ≤ ε / (‖u‖ + 1) * ‖u‖ := by
      rw [show ε / (‖u‖ + 1) * (t * ‖u‖) = t * (ε / (‖u‖ + 1) * ‖u‖) by ring] at h1
      exact le_of_mul_le_mul_left h1 ht
    calc ‖(A - B) u‖ ≤ ε / (‖u‖ + 1) * ‖u‖ := h2
      _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith


/-- The gradient and the derivative of a real function have the same norm. -/
theorem norm_fderiv_eq_norm_gradient (g : E → ℝ) (y : E) : ‖fderiv ℝ g y‖ = ‖gradient g y‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]

omit [CompleteSpace E] in
/-- **Definition 13.1(b)**: the domain of existence of `∇f` has negligible complement relative
to a neighborhood of `x̄` when `f` is strictly continuous at `x̄` (Rademacher's theorem 9.60). -/
theorem exists_nhds_volume_diff_differentiableAt [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {f : E → EReal} {x : E} (hsc : ERealStrictlyContinuousAt f x) :
    ∃ U ∈ 𝓝 x, volume (U \ {y | DifferentiableAt ℝ (fun z ↦ (f z).toReal) y}) = 0 := by
  obtain ⟨k, V, hV, hk⟩ := strictlyContinuousAt_iff.1 hsc.2
  obtain ⟨U, hUV, hUo, hxU⟩ := _root_.mem_nhds_iff.1 hV
  refine ⟨U, hUo.mem_nhds hxU, measure_mono_null (fun y ⟨hyU, hyD⟩ ↦ ?_)
    (ae_iff.1 (ae_differentiableAt_of_strictlyContinuousAt (fun z ↦ (f z).toReal) volume))⟩
  exact fun h ↦ hyD (h (strictlyContinuousAt_iff.2 ⟨k, U, hUo.mem_nhds hyU, hk.mono hUV⟩))

end Definition131

/-! ### Theorem 13.2 -/

section Theorem132

/-- **Theorem 13.2(a)**: twice differentiability in the classical sense implies twice
differentiability in the extended sense, with the same Hessian. -/
theorem HasClassicalHessianAt.hasExtendedHessianAt {f : E → EReal} {x : E} {A : E →L[ℝ] E}
    (h : HasClassicalHessianAt f x A) : HasExtendedHessianAt f x A := by
  obtain ⟨hev, hA⟩ := h
  set g : E → ℝ := fun z ↦ (f z).toReal
  have hbd : ∀ᶠ y in 𝓝 x, ‖gradient g y‖ < ‖gradient g x‖ + 1 :=
    hA.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hev.and hbd)
  have hL : LipschitzOnWith (‖gradient g x‖₊ + 1) g (ball x r) := by
    refine (convex_ball x r).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy ↦ (hball hy).1.2) fun y hy ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_add, coe_nnnorm, NNReal.coe_one,
      norm_fderiv_eq_norm_gradient]
    exact (hball hy).2.le
  exact ⟨⟨hev.mono fun y hy ↦ hy.1, strictlyContinuousAt_iff.2 ⟨_, _, ball_mem_nhds x hr, hL⟩⟩,
    hev.self_of_nhds.2, (HasFDerivAtFilter.isLittleO hA).mono nhdsWithin_le_nhds⟩

/-- The auxiliary quadratic behind the expansion in Theorem 13.2(b): its derivative in the
direction `w` is `y ↦ ⟪w, A (y - x̄)⟫` and it increases by `½⟪w, A w⟫` from `x̄` to `x̄ + w`. -/
noncomputable def hessianLineQuadratic (A : E →L[ℝ] E) (x w y : E) : ℝ :=
  ⟪w, A (y - x)⟫_ℝ * (⟪w, y - x⟫_ℝ / ‖w‖ ^ 2) -
    1 / 2 * ⟪w, A w⟫_ℝ * ((⟪w, y - x⟫_ℝ / ‖w‖ ^ 2) * (⟪w, y - x⟫_ℝ / ‖w‖ ^ 2))

omit [CompleteSpace E] in
theorem hessianLineQuadratic_self (A : E →L[ℝ] E) (x w : E) : hessianLineQuadratic A x w x = 0 := by
  simp [hessianLineQuadratic]

omit [CompleteSpace E] in
theorem hessianLineQuadratic_add {w : E} (A : E →L[ℝ] E) (x : E) (hw : w ≠ 0) :
    hessianLineQuadratic A x w (x + w) = 1 / 2 * ⟪w, A w⟫_ℝ := by
  have hw2 : ‖w‖ ^ 2 ≠ 0 := by positivity
  simp only [hessianLineQuadratic, add_sub_cancel_left, real_inner_self_eq_norm_sq,
    div_self hw2]
  ring

omit [CompleteSpace E] in
theorem contDiff_hessianLineQuadratic (A : E →L[ℝ] E) (x w : E) :
    ContDiff ℝ 1 (hessianLineQuadratic A x w) := by
  have h1 : ContDiff ℝ 1 (fun y : E ↦ ⟪w, A (y - x)⟫_ℝ) :=
    contDiff_const.inner ℝ (A.contDiff.comp (contDiff_id.sub contDiff_const))
  have h2 : ContDiff ℝ 1 (fun y : E ↦ ⟪w, y - x⟫_ℝ / ‖w‖ ^ 2) :=
    (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).div_const _
  exact (h1.mul h2).sub (contDiff_const.mul (h2.mul h2))

omit [CompleteSpace E] in
theorem exists_hasFDerivAt_hessianLineQuadratic (A : E →L[ℝ] E) {x w : E} (hw : w ≠ 0) (z : E) :
    ∃ L : E →L[ℝ] ℝ, HasFDerivAt (hessianLineQuadratic A x w) L z ∧
      L w = ⟪w, A (z - x)⟫_ℝ := by
  set ℓa : E →L[ℝ] ℝ := (innerSL ℝ w).comp A
  set ℓs : E →L[ℝ] ℝ := (‖w‖ ^ 2)⁻¹ • innerSL ℝ w
  have ha : HasFDerivAt (fun y ↦ ⟪w, A (y - x)⟫_ℝ) ℓa z := by
    have h1 := ℓa.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)
    rw [ContinuousLinearMap.comp_id] at h1
    exact h1
  have hs : HasFDerivAt (fun y ↦ ⟪w, y - x⟫_ℝ / ‖w‖ ^ 2) ℓs z := by
    have h1 := ℓs.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)
    rw [ContinuousLinearMap.comp_id] at h1
    refine h1.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
    simp [ℓs, div_eq_inv_mul]
  refine ⟨_, (ha.mul hs).sub ((hs.mul hs).const_mul (1 / 2 * ⟪w, A w⟫_ℝ)), ?_⟩
  have hw2 : ‖w‖ ^ 2 ≠ 0 := by positivity
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ℓa, ℓs, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- The core estimate behind **Theorem 13.2(b)**: if `g` is Lipschitz on `𝔹(x̄, ρ)` and, off a
null set, differentiable with `‖∇g(z) - v - A(z - x̄)‖ ≤ c`, then
`|g(x̄ + w) - g(x̄) - ⟪v, w⟫ - ½⟪w, A w⟫| ≤ c‖w‖` whenever `‖w‖ < ρ`. -/
theorem abs_quadratic_remainder_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {g : E → ℝ} {x v w : E} {A : E →L[ℝ] E} {k : ℝ≥0} {ρ c : ℝ}
    (hL : LipschitzOnWith k g (ball x ρ)) {N : Set E} (hN : volume N = 0)
    (hd : ∀ z ∈ ball x ρ, z ∉ N → DifferentiableAt ℝ g z ∧ ‖gradient g z - v - A (z - x)‖ ≤ c)
    (hw : ‖w‖ < ρ) :
    |g (x + w) - g x - ⟪v, w⟫_ℝ - 1 / 2 * ⟪w, A w⟫_ℝ| ≤ c * ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have hρ : 0 < ρ := (norm_nonneg w).trans_lt hw
  set Φ := hessianLineQuadratic A x w
  obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K (fun y ↦ ⟪v, y⟫_ℝ + Φ y) (ball x ρ) := by
    have hc : ContDiff ℝ 1 (fun y ↦ ⟪v, y⟫_ℝ + Φ y) :=
      (contDiff_const.inner ℝ contDiff_id).add (contDiff_hessianLineQuadratic A x w)
    obtain ⟨K, hK⟩ := hc.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall x ρ)
      (isCompact_closedBall x ρ)
    exact ⟨K, hK.mono ball_subset_closedBall⟩
  set φ : E → ℝ := fun y ↦ g y - (⟪v, y⟫_ℝ + Φ y) with hφ
  have hφL : LipschitzOnWith (k + K) φ (ball x ρ) := hL.sub hK
  have hderiv : ∀ z ∈ ball x ρ, z ∉ N → ∃ L : E →L[ℝ] ℝ, HasFDerivAt φ L z ∧
      |L w| ≤ c * ‖w‖ := by
    intro z hz hzN
    obtain ⟨hdz, hbz⟩ := hd z hz hzN
    obtain ⟨L, hLz, hLw⟩ := exists_hasFDerivAt_hessianLineQuadratic A hw0 z (x := x)
    have hv : HasFDerivAt (fun y ↦ ⟪v, y⟫_ℝ) (innerSL ℝ v) z := (innerSL ℝ v).hasFDerivAt
    refine ⟨fderiv ℝ g z - (innerSL ℝ v + L), hdz.hasFDerivAt.sub (hv.add hLz), ?_⟩
    have hval : (fderiv ℝ g z - (innerSL ℝ v + L)) w = ⟪gradient g z - v - A (z - x), w⟫_ℝ := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, hLw, innerSL_apply_apply,
        fderiv_apply_eq_inner_gradient, inner_sub_left, inner_sub_left,
        real_inner_comm (A (z - x)) w]
      ring
    rw [hval]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hbz (norm_nonneg w))
  have hx₀ : x ∈ ball x ρ := mem_ball_self hρ
  have hxw : x + (1 : ℝ) • w ∈ ball x ρ := by
    rwa [one_smul, mem_ball, dist_eq_norm, add_sub_cancel_left]
  have h1 := sub_le_mul_of_fderiv_le_off_null hφL hN (fun z hz hzN ↦
    let ⟨L, hLz, hLw⟩ := hderiv z hz hzN; ⟨L, hLz, (le_abs_self _).trans hLw⟩) zero_le_one hx₀ hxw
  have h2 := sub_le_mul_of_fderiv_le_off_null hφL.neg hN (fun z hz hzN ↦
    let ⟨L, hLz, hLw⟩ := hderiv z hz hzN
    ⟨-L, hLz.neg, by rw [ContinuousLinearMap.neg_apply]; exact (neg_le_abs _).trans hLw⟩)
    zero_le_one hx₀ hxw
  have e1 : Φ (x + w) = 1 / 2 * ⟪w, A w⟫_ℝ := hessianLineQuadratic_add A x hw0
  have e0 : Φ x = 0 := hessianLineQuadratic_self A x w
  simp only [one_smul, mul_one, Pi.neg_apply, hφ] at h1 h2
  rw [e1, e0, inner_add_right] at h1 h2
  rw [abs_le]
  constructor <;> linarith

omit [CompleteSpace E] in
/-- A first-order expansion of a set-valued mapping forces it to be single-valued at the point. -/
theorem HasMappingFirstOrderExpansion.eq_singleton {S : E → Set E} {x u : E} {A : E →L[ℝ] E}
    (he : HasMappingFirstOrderExpansion S x u A) : S x = {u} := by
  obtain ⟨hne, hall⟩ := (he 1 one_pos).self_of_nhds
  refine eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, fun u' hu' ↦ ?_⟩
  have h1 := hall u' hu'
  simp only [sub_self, map_zero, sub_zero, norm_zero, mul_zero] at h1
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)

/-- **Theorem 13.2(c)**, necessity: twice differentiability in the extended sense yields the
first-order expansion 13(1) of `∂f` at `x̄`, with `v = ∇f(x̄)` and `A = ∇²f(x̄)`. -/
theorem HasExtendedHessianAt.hasMappingFirstOrderExpansion [FiniteDimensional ℝ E]
    {f : E → EReal} {x : E} {A : E →L[ℝ] E} (h : HasExtendedHessianAt f x A) :
    HasMappingFirstOrderExpansion (subdifferential f) x
      (gradient (fun z ↦ (f z).toReal) x) A := by
  borelize E
  obtain ⟨hsc, -, ho⟩ := h
  set g : E → ℝ := fun z ↦ (f z).toReal
  set D : Set E := {y | DifferentiableAt ℝ g y}
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hsc.2
  obtain ⟨U, hUx, hUo, hfin, hLU⟩ := hsc.exists_lipschitzOnWith hk
  have hscU : ∀ y ∈ U, StrictlyContinuousAt g y := fun y hy ↦
    strictlyContinuousAt_iff.2 ⟨k, U, hUo.mem_nhds hy, hLU⟩
  intro ε hε
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhdsWithin_iff.1 (isLittleO_iff.1 ho hε)
  filter_upwards [inter_mem hUx (ball_mem_nhds x hδ)] with y ⟨hyU, hyδ⟩
  have hnull : volume ({y ∈ U | DifferentiableAt ℝ g y} \ D) = 0 := by
    rw [diff_eq_empty.2 fun y hy ↦ hy.2]
    exact measure_empty
  obtain ⟨hne, -, hsub, hconv, -⟩ := clarke_reachableGradient_representation hUo hscU
    (D := D) (fun _ h ↦ h) hnull hyU
  have hcongr : subdifferential f y = subdifferential (fun z ↦ (g z : EReal)) y :=
    subdifferential_congr_nhds_of_finite (hfin y hyU)
      (Filter.eventually_of_mem (hUo.mem_nhds hyU) hfin)
  set S := closedBall (gradient g x + A (y - x)) (ε * ‖y - x‖)
  have hRS : reachableGradients g D y ⊆ S := by
    intro u hu
    obtain ⟨s, hsD, hsy, hsu⟩ := mem_clusterValuesWithin_iff.1 hu
    have hev : ∀ᶠ n in atTop,
        ‖gradient g (s n) - (gradient g x + A (s n - x))‖ ≤ ε * ‖s n - x‖ := by
      filter_upwards [hsy.eventually (isOpen_ball.mem_nhds hyδ)] with n hn
      rw [← sub_sub]
      exact hδball ⟨hn, hsD n⟩
    rw [mem_closedBall, dist_eq_norm]
    refine le_of_tendsto_of_tendsto ?_ (((hsy.sub_const x).norm).const_mul ε) hev
    exact (hsu.sub (tendsto_const_nhds.add ((A.continuous.tendsto _).comp
      (hsy.sub_const x)))).norm
  have hconvS : convexHull ℝ (reachableGradients g D y) ⊆ S :=
    convexHull_min hRS (convex_closedBall _ _)
  refine ⟨?_, fun u hu ↦ ?_⟩
  · rw [hcongr]
    exact hne.mono hsub
  · rw [hcongr] at hu
    have h1 : u ∈ S := hconvS (by rw [hconv]; exact subset_convexHull ℝ _ hu)
    rwa [mem_closedBall, dist_eq_norm, ← sub_sub] at h1

/-- **Theorem 13.2(c)**, sufficiency: a function finite and locally lsc at `x̄` whose subgradient
mapping has the first-order expansion 13(1) is twice differentiable at `x̄` in the extended
sense, and necessarily `∇f(x̄) = v` and `∇²f(x̄) = A`. -/
theorem hasExtendedHessianAt_of_hasMappingFirstOrderExpansion [FiniteDimensional ℝ E]
    {f : E → EReal} {x v : E} {c : ℝ} {A : E →L[ℝ] E} (hx : f x = c) (hl : IsLocallyLscAt f x)
    (he : HasMappingFirstOrderExpansion (subdifferential f) x v A) :
    HasExtendedHessianAt f x A ∧ gradient (fun z ↦ (f z).toReal) x = v := by
  set g : E → ℝ := fun z ↦ (f z).toReal
  have hbd : SvLocallyBoundedAt (subdifferential f) x := by
    refine ⟨{y | ∀ u ∈ subdifferential f y, ‖u - v - A (y - x)‖ ≤ 1 * ‖y - x‖} ∩ ball x 1,
      inter_mem ((he 1 one_pos).mono fun y hy ↦ hy.2) (ball_mem_nhds x one_pos),
      (isBounded_closedBall (x := (0 : E)) (r := ‖v‖ + ‖A‖ + 1)).subset ?_⟩
    intro u hu
    obtain ⟨y, ⟨hy1, hy2⟩, hu⟩ := mem_svImage.mp hu
    have hyx : ‖y - x‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hy2
    have h1 := hy1 u hu
    have h2 := A.le_opNorm (y - x)
    rw [mem_closedBall_zero_iff]
    calc ‖u‖ = ‖(u - v - A (y - x)) + v + A (y - x)‖ := by congr 1; abel
      _ ≤ ‖u - v - A (y - x)‖ + ‖v‖ + ‖A (y - x)‖ := norm_add₃_le
      _ ≤ ‖v‖ + ‖A‖ + 1 := by nlinarith [norm_nonneg A, norm_nonneg (y - x)]
  have hsc : ERealStrictlyContinuousAt f x :=
    (eRealStrictlyContinuousAt_iff_locallyBoundedAt_subdifferential hx hl).2 hbd
  have hsg : HasStrictGradientAt f v x :=
    hasStrictGradientAt_of_subdifferential_eq hsc he.eq_singleton
  have hgrad : HasGradientAt g v x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hfd := hsg.2.hasFDerivAt
    convert hfd using 1
  have hgx : gradient g x = v := hgrad.gradient
  refine ⟨⟨hsc, hgrad.differentiableAt, ?_⟩, hgx⟩
  rw [hgx, isLittleO_iff]
  intro ε hε
  have hloc : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, f z = ((g z : ℝ) : EReal) := hsc.1.eventually_nhds
  filter_upwards [nhdsWithin_le_nhds ((he ε hε).and hloc), self_mem_nhdsWithin]
    with y ⟨⟨_, hall⟩, hyloc⟩ hyD
  have hmem : gradient g y ∈ subdifferential f y := by
    rw [subdifferential_congr_nhds_of_finite hyloc.self_of_nhds hyloc]
    exact (regularSubdifferential_of_hasGradientAt hyD.hasGradientAt).2
  exact hall _ hmem

/-- **Theorem 13.2(c)**: `f` is twice differentiable at `x̄` in the extended sense if and only
if it is finite and locally lsc at `x̄` and `∂f` is differentiable at `x̄`. -/
theorem exists_hasExtendedHessianAt_iff [FiniteDimensional ℝ E] {f : E → EReal} {x : E} :
    (∃ A, HasExtendedHessianAt f x A) ↔
      (∃ c : ℝ, f x = c) ∧ IsLocallyLscAt f x ∧ SvDifferentiableAt (subdifferential f) x := by
  constructor
  · rintro ⟨A, h⟩
    exact ⟨⟨_, h.1.finite⟩, h.1.isLocallyLscAt, _, A, h.hasMappingFirstOrderExpansion⟩
  · rintro ⟨⟨c, hx⟩, hl, v, A, he⟩
    exact ⟨A, (hasExtendedHessianAt_of_hasMappingFirstOrderExpansion hx hl he).1⟩

/-- **Theorem 13.2(b)**, strict differentiability. -/
theorem HasExtendedHessianAt.hasStrictGradientAt [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    {A : E →L[ℝ] E} (h : HasExtendedHessianAt f x A) :
    HasStrictGradientAt f (gradient (fun z ↦ (f z).toReal) x) x :=
  hasStrictGradientAt_of_subdifferential_eq h.1 h.hasMappingFirstOrderExpansion.eq_singleton

/-- Under twice differentiability in the extended sense, `f` is differentiable at `x̄` in the
sense of 7(16) with gradient `∇f(x̄)`. -/
theorem HasExtendedHessianAt.hasERealGradientAt {f : E → EReal} {x : E} {A : E →L[ℝ] E}
    (h : HasExtendedHessianAt f x A) :
    HasERealGradientAt f x (innerSL ℝ (gradient (fun z ↦ (f z).toReal) x)) := by
  obtain ⟨hsc, hdx, -⟩ := h
  have hxc := hsc.finite
  refine ⟨by rw [hxc]; exact EReal.coe_ne_bot _, by rw [hxc]; exact EReal.coe_ne_top _,
    hsc.1.mono fun y hy ↦
      ⟨by rw [hy]; exact EReal.coe_ne_bot _, by rw [hy]; exact EReal.coe_ne_top _⟩, ?_⟩
  have h1 := HasFDerivAtFilter.isLittleO (hasGradientAt_iff_hasFDerivAt.1 hdx.hasGradientAt)
  refine h1.congr_left fun y ↦ ?_
  simp

/-- **Theorem 13.2(b)**, quadratic expansion:
`f(x) = f(x̄) + ⟪∇f(x̄), x - x̄⟫ + ½⟪x - x̄, ∇²f(x̄)(x - x̄)⟫ + o(‖x - x̄‖²)`. -/
theorem HasExtendedHessianAt.isLittleO_quadratic [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    {A : E →L[ℝ] E} (h : HasExtendedHessianAt f x A) :
    (fun y ↦ (f y).toReal - (f x).toReal - ⟪gradient (fun z ↦ (f z).toReal) x, y - x⟫_ℝ -
      1 / 2 * ⟪y - x, A (y - x)⟫_ℝ) =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2) := by
  borelize E
  obtain ⟨hsc, -, ho⟩ := h
  set g : E → ℝ := fun z ↦ (f z).toReal
  obtain ⟨k, U, hU, hLU⟩ := strictlyContinuousAt_iff.1 hsc.2
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  set N : Set E := {y | ¬(StrictlyContinuousAt g y → DifferentiableAt ℝ g y)}
  have hN : volume N = 0 := ae_iff.1 (ae_differentiableAt_of_strictlyContinuousAt g volume)
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhdsWithin_iff.1 (isLittleO_iff.1 ho (half_pos hε))
  have hm : 0 < min δ r := lt_min hδ hr
  filter_upwards [ball_mem_nhds x (half_pos hm)] with y hy
  have hyx : ‖y - x‖ < min δ r / 2 := by rwa [mem_ball, dist_eq_norm] at hy
  rcases eq_or_ne (y - x) 0 with h0 | h0
  · rw [sub_eq_zero.1 h0]
    simp
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 h0
  set ρ := 2 * ‖y - x‖
  have hρδ : ball x ρ ⊆ ball x δ := ball_subset_ball (by linarith [min_le_left δ r])
  have hρr : ball x ρ ⊆ ball x r := ball_subset_ball (by linarith [min_le_right δ r])
  have hcore := abs_quadratic_remainder_le (g := g) (x := x) (v := gradient g x) (w := y - x)
    (A := A) (k := k) (ρ := ρ) (c := ε / 2 * ρ) ((hLU.mono hrU).mono hρr) hN
    (fun z hz hzN ↦ by
      have hzr := hρr hz
      have hdz : DifferentiableAt ℝ g z := (not_not.1 hzN)
        (strictlyContinuousAt_iff.2 ⟨k, ball x r, isOpen_ball.mem_nhds hzr, hLU.mono hrU⟩)
      refine ⟨hdz, (hδball ⟨hρδ hz, hdz⟩).trans ?_⟩
      have : ‖z - x‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hz
      exact mul_le_mul_of_nonneg_left this.le (by positivity))
    (by simp only [ρ]; linarith)
  rw [add_sub_cancel] at hcore
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  calc _ ≤ ε / 2 * ρ * ‖y - x‖ := hcore
    _ = ε * ‖y - x‖ ^ 2 := by simp only [ρ]; ring

/-- **Theorem 13.2(b)**: twice differentiability in the extended sense gives a quadratic
expansion with the Hessian as matrix. -/
theorem HasExtendedHessianAt.hasQuadraticExpansionAt [FiniteDimensional ℝ E] {f : E → EReal}
    {x : E} {A : E →L[ℝ] E} (h : HasExtendedHessianAt f x A) : HasQuadraticExpansionAt f x A :=
  ⟨_, h.hasERealGradientAt, h.isLittleO_quadratic⟩

/-- **Theorem 13.2** (extended second-order differentiability). -/
theorem extended_second_order_differentiability [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    {A : E →L[ℝ] E} :
    (HasClassicalHessianAt f x A → HasExtendedHessianAt f x A) ∧
    (HasExtendedHessianAt f x A →
      HasStrictGradientAt f (gradient (fun z ↦ (f z).toReal) x) x ∧
      (fun y ↦ (f y).toReal - (f x).toReal - ⟪gradient (fun z ↦ (f z).toReal) x, y - x⟫_ℝ -
        1 / 2 * ⟪y - x, A (y - x)⟫_ℝ) =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2)) ∧
    ((∃ B, HasExtendedHessianAt f x B) ↔
      (∃ c : ℝ, f x = c) ∧ IsLocallyLscAt f x ∧ SvDifferentiableAt (subdifferential f) x) ∧
    (∀ (c : ℝ) (v : E), f x = c → IsLocallyLscAt f x →
      HasMappingFirstOrderExpansion (subdifferential f) x v A →
      HasExtendedHessianAt f x A ∧ gradient (fun z ↦ (f z).toReal) x = v) :=
  ⟨HasClassicalHessianAt.hasExtendedHessianAt,
    fun h ↦ ⟨h.hasStrictGradientAt, h.isLittleO_quadratic⟩, exists_hasExtendedHessianAt_iff,
    fun _ _ hx hl he ↦ hasExtendedHessianAt_of_hasMappingFirstOrderExpansion hx hl he⟩

end Theorem132

/-! ### Example 13.8 -/

section Example138

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A gradient in the sense of 7(16) is a semiderivative in every direction. -/
theorem HasERealGradientAt.hasSemiderivative {f : E → EReal} {x : E} {L : E →L[ℝ] ℝ}
    (hf : HasERealGradientAt f x L) (w : E) : HasSemiderivative f x w (L w : EReal) := by
  obtain ⟨hx, hx', hfin, ho⟩ := hf
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx' hx).symm
  exact ⟨hx, hx', tendsto_of_isLittleO hxc L.continuous
    (fun a _ w ↦ by rw [map_smul, smul_eq_mul]) hfin ho w⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem inner_smul_map_smul (A : E →L[ℝ] E) (a : ℝ) (w : E) :
    ⟪a • w, A (a • w)⟫_ℝ = a ^ 2 * ⟪w, A w⟫_ℝ := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Example 13.8**, second part: `f` has a quadratic expansion at `x̄` with matrix `A` if and
only if it is differentiable at `x̄` and twice semidifferentiable there with `d²f(x̄)` the
quadratic form `w ↦ ⟪w, A w⟫`. -/
theorem hasQuadraticExpansionAt_iff {f : E → EReal} {x : E} {A : E →L[ℝ] E} :
    HasQuadraticExpansionAt f x A ↔ ERealDifferentiableAt f x ∧ TwiceSemidifferentiableAt f x ∧
      ∀ w, secondSubderivativeAt f x w = ((⟪w, A w⟫_ℝ : ℝ) : EReal) := by
  constructor
  · rintro ⟨v, hv, ho⟩
    have hs : SemidifferentiableAt f x := fun w ↦ ⟨_, hv.hasSemiderivative w⟩
    have hsub : ∀ w, subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) := fun w ↦ by
      rw [(hv.hasSemiderivative w).subderivative_eq, innerSL_apply_apply]
    have hHc : Continuous fun w : E ↦ ⟪w, A w⟫_ℝ := continuous_id.inner A.continuous
    have hHs : ∀ a : ℝ, 0 < a → ∀ w : E, ⟪a • w, A (a • w)⟫_ℝ = a ^ 2 * ⟪w, A w⟫_ℝ :=
      fun a _ w ↦ inner_smul_map_smul A a w
    have ho' : (fun y ↦ (f y).toReal - (f x).toReal - (subderivative f x (y - x)).toReal -
        1 / 2 * ⟪y - x, A (y - x)⟫_ℝ) =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2) :=
      ho.congr_left fun y ↦ by rw [hsub, EReal.toReal_coe]
    have h31 := (characterizations_of_second_order_semidifferentiability hs).out 2 0
    have htw : TwiceSemidifferentiableAt f x :=
      h31.1 ⟨fun w ↦ ⟪w, A w⟫_ℝ, hHc, hHs, hv.2.2.1, ho'⟩
    exact ⟨⟨_, hv⟩, htw, fun w ↦ congrFun
      (eq_secondSubderivativeAt_of_secondOrder_isLittleO hs hHc hHs hv.2.2.1 ho') w⟩
  · rintro ⟨⟨L, hL⟩, htw, hq⟩
    set v := (InnerProductSpace.toDual ℝ E).symm L
    have hLv : innerSL ℝ v = L := by
      ext u
      rw [innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
    rw [← hLv] at hL
    obtain ⟨-, ho⟩ := htw.isLittleO
    refine ⟨v, hL, ho.congr_left fun y ↦ ?_⟩
    rw [(hL.hasSemiderivative (y - x)).subderivative_eq, hq, EReal.toReal_coe, EReal.toReal_coe,
      innerSL_apply_apply]

/-- **Example 13.8**: a function twice differentiable at `x̄` in the extended sense is twice
semidifferentiable at `x̄` and twice epi-differentiable at `x̄` for `v = ∇f(x̄)`, with
`d²f(x̄ | v)(w) = d²f(x̄)(w) = f''(x̄; w) = ⟪w, ∇²f(x̄) w⟫`; here `f''(x̄; w)` is the limit of the
quotients `Δ²_τ f(x̄)(w')` as `τ ↘ 0`, `w' → w`. -/
theorem HasExtendedHessianAt.twiceSemi_twiceEpi {f : E → EReal} {x : E} {A : E →L[ℝ] E}
    (h : HasExtendedHessianAt f x A) :
    TwiceSemidifferentiableAt f x ∧
      TwiceEpiDifferentiableAt f x (gradient (fun z ↦ (f z).toReal) x) ∧
      ∀ w, secondSubderivative f x (gradient (fun z ↦ (f z).toReal) x) w =
          ((⟪w, A w⟫_ℝ : ℝ) : EReal) ∧
        secondSubderivativeAt f x w = ((⟪w, A w⟫_ℝ : ℝ) : EReal) ∧
        Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
          (𝓝 ((⟪w, A w⟫_ℝ : ℝ) : EReal)) := by
  obtain ⟨-, htw, hq⟩ := hasQuadraticExpansionAt_iff.1 h.hasQuadraticExpansionAt
  set v := gradient (fun z ↦ (f z).toReal) x
  have hgr := h.hasERealGradientAt
  have heq : secondSubderivativeAt f x = secondSubderivative f x v :=
    secondSubderivativeAt_eq_secondSubderivative_of_hasERealGradientAt hgr
  have hlim : ∀ w, Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((⟪w, A w⟫_ℝ : ℝ) : EReal)) := fun w ↦ by
    rw [← hq w]
    exact htw.2 w
  have hsub : ∀ w, subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) := fun w ↦ by
    rw [(hgr.hasSemiderivative w).subderivative_eq, innerSL_apply_apply]
  have hlim' : ∀ w, Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((⟪w, A w⟫_ℝ : ℝ) : EReal)) := fun w ↦
    (hlim w).congr fun p ↦ secondDifferenceQuotientAt_eq_of_subderivative_eq (hsub p.2)
  have hd2 : ∀ w, secondSubderivative f x v w = ((⟪w, A w⟫_ℝ : ℝ) : EReal) := fun w ↦ by
    rw [← heq]
    exact hq w
  refine ⟨htw, twiceEpiDifferentiableAt_iff_subset.2 ⟨hgr.1, hgr.2.1, ?_⟩,
    fun w ↦ ⟨hd2 w, hq w, hlim w⟩⟩
  rw [show secondSubderivative f x v = fun w ↦ ((⟪w, A w⟫_ℝ : ℝ) : EReal) from funext hd2]
  exact epigraph_subset_innerSetLimitAlong_of_tendsto fun w ↦ by
    have h2 := (hlim' w).comp (tendsto_pair_const w)
    exact h2

/-- **Example 13.8** (connections with second-order differentiability). -/
theorem connections_with_second_order_differentiability {f : E → EReal} {x : E}
    {A : E →L[ℝ] E} :
    ((HasClassicalHessianAt f x A ∨ HasExtendedHessianAt f x A) →
      TwiceSemidifferentiableAt f x ∧
      TwiceEpiDifferentiableAt f x (gradient (fun z ↦ (f z).toReal) x) ∧
      ∀ w, secondSubderivative f x (gradient (fun z ↦ (f z).toReal) x) w =
          ((⟪w, A w⟫_ℝ : ℝ) : EReal) ∧
        secondSubderivativeAt f x w = ((⟪w, A w⟫_ℝ : ℝ) : EReal) ∧
        Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
          (𝓝 ((⟪w, A w⟫_ℝ : ℝ) : EReal))) ∧
    (HasQuadraticExpansionAt f x A ↔ ERealDifferentiableAt f x ∧ TwiceSemidifferentiableAt f x ∧
      ∀ w, secondSubderivativeAt f x w = ((⟪w, A w⟫_ℝ : ℝ) : EReal)) :=
  ⟨fun h ↦ (h.elim HasClassicalHessianAt.hasExtendedHessianAt id).twiceSemi_twiceEpi,
    hasQuadraticExpansionAt_iff⟩

end Example138

end RW
