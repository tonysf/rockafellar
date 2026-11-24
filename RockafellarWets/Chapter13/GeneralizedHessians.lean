/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Generalized second-derivative symmetry for C¹⁺ functions

Theorem 13.52 (`generalization_of_second_derivative_symmetry`).  For `f` of class `C¹⁺` on an open
set `O`, the points where `f` is twice differentiable in the classical or the extended sense are the
points where `∇f` is differentiable (`IsC1PlusOn.twice_differentiable_iff`), and the generalized
Hessians `∇̄²f(x̄)` are the reachable Jacobians of `∇f` (9.62) over that set `D`, or over any
`D' ⊂ D` with `D \ D'` negligible.  Everything except the first equation in 13(34) comes from
9.62 applied to `F = ∇f` together with the symmetry of the Hessians where they exist
(`hessian_inner_comm`, from the symmetry of second derivatives); the first equation is the
mean-value argument of the book (`limsup_mixedSecondDifference`), and the upper limits taken also
over `w' → w`, `z' → z` reduce to the others by the Lipschitz continuity of `∇f`
(`limsup_gradientDifferenceQuotient_perturb`). -/

import RockafellarWets.Chapter13.TwiceDifferentiability
import RockafellarWets.Chapter13.C1PlusFunctions
import RockafellarWets.Chapter9.ReachableJacobianDuality
import RockafellarWets.Chapter9.LipschitzSubderivatives
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Filter Set Topology Metric MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The Hessian `∇²f(x) = D(∇f)(x)` of a function differentiable near `x` is symmetric. -/
theorem hessian_inner_comm [CompleteSpace E] {f : E → ℝ} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ (gradient f) x)
    (u v : E) : ⟪fderiv ℝ (gradient f) x u, v⟫_ℝ = ⟪u, fderiv ℝ (gradient f) x v⟫_ℝ := by
  have h1 : ∀ᶠ y in 𝓝 x, HasFDerivAt f (innerSL ℝ (gradient f y)) y := by
    filter_upwards [hf] with y hy
    have := hy.hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt] at this
    convert this using 1
  have h2 : HasFDerivAt (fun y ↦ innerSL ℝ (gradient f y))
      ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp (fderiv ℝ (gradient f) x)) x :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp x hg.hasFDerivAt
  have h3 := second_derivative_symmetric_of_eventually_of_real h1 h2 u v
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h3
  rw [h3, real_inner_comm]

/-- The reachable Jacobians of `∇f` over points where `∇f` is differentiable are symmetric. -/
theorem reachableJacobians_gradient_inner_comm {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, DifferentiableAt ℝ f y)
    (hD : D ⊆ {y ∈ O | DifferentiableAt ℝ (gradient f) y}) {x : E} {A : E →L[ℝ] E}
    (hA : A ∈ reachableJacobians (gradient f) D x) (u v : E) : ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ := by
  obtain ⟨y, hyD, -, hlim⟩ := mem_clusterValuesWithin_iff.1 hA
  have hsym : ∀ n, ⟪fderiv ℝ (gradient f) (y n) u, v⟫_ℝ = ⟪u, fderiv ℝ (gradient f) (y n) v⟫_ℝ :=
    fun n ↦ hessian_inner_comm (Filter.mem_of_superset (hO.mem_nhds (hD (hyD n)).1)
      fun z hz ↦ hf z hz) (hD (hyD n)).2 u v
  have hu : Tendsto (fun n ↦ fderiv ℝ (gradient f) (y n) u) atTop (𝓝 (A u)) :=
    ((ContinuousLinearMap.apply ℝ E u).continuous.tendsto A).comp hlim
  have hv : Tendsto (fun n ↦ fderiv ℝ (gradient f) (y n) v) atTop (𝓝 (A v)) :=
    ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto A).comp hlim
  have h1 : Tendsto (fun n ↦ ⟪fderiv ℝ (gradient f) (y n) u, v⟫_ℝ) atTop (𝓝 ⟪A u, v⟫_ℝ) :=
    hu.inner tendsto_const_nhds
  have h2 : Tendsto (fun n ↦ ⟪u, fderiv ℝ (gradient f) (y n) v⟫_ℝ) atTop (𝓝 ⟪u, A v⟫_ℝ) :=
    tendsto_const_nhds.inner hv
  exact tendsto_nhds_unique h1 (h2.congr fun n ↦ (hsym n).symm)

/-! ### The mixed second differences -/

/-- The mixed second difference `[f(x + τw + σz) - f(x + τw) - f(x + σz) + f(x)]/(τσ)`. -/
noncomputable def mixedSecondDifference (f : E → ℝ) (x w z : E) (τ σ : ℝ) : ℝ :=
  (f (x + τ • w + σ • z) - f (x + τ • w) - f (x + σ • z) + f x) / (τ * σ)

omit [FiniteDimensional ℝ E] in
/-- The mean-value step in the proof of 13.52: a mixed second difference is a difference quotient
of `⟪z, ∇f(·)⟫` in the direction `w` at some point of `[x, x + σz]`. -/
theorem mixedSecondDifference_eq_mvt [CompleteSpace E] {f : E → ℝ} {O : Set E}
    (hf : ∀ y ∈ O, DifferentiableAt ℝ f y) {x w z : E} {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (hseg : ∀ s ∈ Icc (0 : ℝ) σ, x + s • z ∈ O ∧ x + s • z + τ • w ∈ O) :
    ∃ s ∈ Ioo (0 : ℝ) σ, mixedSecondDifference f x w z τ σ =
      (⟪z, gradient f (x + s • z + τ • w)⟫_ℝ - ⟪z, gradient f (x + s • z)⟫_ℝ) / τ := by
  set θ : ℝ → ℝ := fun s ↦ (f (x + s • z + τ • w) - f (x + s • z)) / τ with hθ
  set θ' : ℝ → ℝ := fun s ↦
    (⟪gradient f (x + s • z + τ • w), z⟫_ℝ - ⟪gradient f (x + s • z), z⟫_ℝ) / τ with hθ'
  have hpath : ∀ (c : E) (s : ℝ), HasDerivAt (fun s : ℝ ↦ c + s • z) z s := by
    intro c s
    simpa using ((hasDerivAt_id s).smul_const z).const_add c
  have hderiv : ∀ s ∈ Icc (0 : ℝ) σ, HasDerivAt θ (θ' s) s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hseg s hs
    have hd1 : HasDerivAt (fun s : ℝ ↦ f (x + s • z + τ • w))
        (⟪gradient f (x + s • z + τ • w), z⟫_ℝ) s := by
      have hg := (hf _ h2).hasGradientAt
      rw [hasGradientAt_iff_hasFDerivAt] at hg
      have hp : HasDerivAt (fun s : ℝ ↦ x + s • z + τ • w) z s := by
        have := hpath (x + τ • w) s
        convert this using 1
        funext t; abel
      have := hg.comp_hasDerivAt s hp
      simpa [InnerProductSpace.toDual_apply_apply] using this
    have hd2 : HasDerivAt (fun s : ℝ ↦ f (x + s • z)) (⟪gradient f (x + s • z), z⟫_ℝ) s := by
      have hg := (hf _ h1).hasGradientAt
      rw [hasGradientAt_iff_hasFDerivAt] at hg
      have := hg.comp_hasDerivAt s (hpath x s)
      simpa [InnerProductSpace.toDual_apply_apply] using this
    exact (hd1.sub hd2).div_const τ
  obtain ⟨s, hs, hseq⟩ := exists_hasDerivAt_eq_slope θ θ' hσ
    (fun s hs ↦ (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ hderiv s (Ioo_subset_Icc_self hs))
  refine ⟨s, hs, ?_⟩
  have e1 : mixedSecondDifference f x w z τ σ = (θ σ - θ 0) / (σ - 0) := by
    simp only [mixedSecondDifference, hθ, zero_smul, add_zero, sub_zero]
    rw [show x + σ • z + τ • w = x + τ • w + σ • z by abel]
    field_simp
    ring
  rw [e1, ← hseq, hθ', real_inner_comm (gradient f (x + s • z + τ • w)),
    real_inner_comm (gradient f (x + s • z))]

omit [FiniteDimensional ℝ E] in
/-- At a point where `∇f` is differentiable, the mixed second differences with `σ = τ` tend to
`⟪z, ∇²f(x)w⟫`, by the quadratic expansion and the symmetry of `∇²f(x)`. -/
theorem tendsto_mixedSecondDifference_diag [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ (gradient f) x)
    (w z : E) :
    Tendsto (fun τ : ℝ ↦ mixedSecondDifference f x w z τ τ) (𝓝[>] 0)
      (𝓝 ⟪z, fderiv ℝ (gradient f) x w⟫_ℝ) := by
  set B := fderiv ℝ (gradient f) x with hB
  have hcl : HasClassicalHessianAt (fun y ↦ (f y : EReal)) x B := by
    refine ⟨?_, ?_⟩
    · filter_upwards [hf] with y hy
      simpa using hy
    · simpa using hg.hasFDerivAt
  have ho := hcl.hasExtendedHessianAt.isLittleO_quadratic
  simp only [EReal.toReal_coe] at ho
  set R : E → ℝ := fun y ↦ f y - f x - ⟪gradient f x, y - x⟫_ℝ - 1 / 2 * ⟪y - x, B (y - x)⟫_ℝ
    with hR
  have hsym : ⟪B w, z⟫_ℝ = ⟪w, B z⟫_ℝ := hessian_inner_comm hf hg w z
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  set K := ‖w + z‖ ^ 2 + ‖w‖ ^ 2 + ‖z‖ ^ 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  have hε := ho.def (show 0 < η / (2 * K) by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hε
  set S := ‖w‖ + ‖z‖ + 1 with hS
  refine ⟨r / S, by positivity, fun τ hτ hτr ↦ ?_⟩
  have hτ0 : (0 : ℝ) < τ := hτ
  rw [Real.dist_eq, sub_zero, abs_of_pos hτ0] at hτr
  have hτS : τ * S < r := by rwa [lt_div_iff₀ (by positivity)] at hτr
  have hmem : ∀ v : E, ‖v‖ ≤ ‖w‖ + ‖z‖ → x + τ • v ∈ ball x r := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le]
    nlinarith [norm_nonneg v]
  have hb : ∀ v : E, ‖v‖ ≤ ‖w‖ + ‖z‖ → |R (x + τ • v)| ≤ η / (2 * K) * (τ ^ 2 * ‖v‖ ^ 2) := by
    intro v hv
    have h := hball (hmem v hv)
    simp only [mem_setOf_eq, Real.norm_eq_abs, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hτ0.le] at h
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (τ * ‖v‖) ^ 2)] at h
    calc |R (x + τ • v)| ≤ η / (2 * K) * (τ * ‖v‖) ^ 2 := h
      _ = η / (2 * K) * (τ ^ 2 * ‖v‖ ^ 2) := by ring
  have h1 := hb (w + z) (norm_add_le w z)
  have h2 := hb w (by linarith [norm_nonneg z])
  have h3 := hb z (by linarith [norm_nonneg w])
  have hexp : mixedSecondDifference f x w z τ τ - ⟪z, B w⟫_ℝ =
      (R (x + τ • (w + z)) - R (x + τ • w) - R (x + τ • z)) / τ ^ 2 := by
    have hsym' : ⟪w, B z⟫_ℝ = ⟪z, B w⟫_ℝ := by rw [← hsym, real_inner_comm]
    simp only [mixedSecondDifference, hR, add_sub_cancel_left, smul_add, map_add, map_smul,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [show x + τ • w + τ • z = x + (τ • w + τ • z) by abel, hsym']
    field_simp
    ring
  rw [Real.dist_eq, hexp, abs_div, abs_of_pos (by positivity : (0 : ℝ) < τ ^ 2),
    div_lt_iff₀ (by positivity)]
  have htri : |R (x + τ • (w + z)) - R (x + τ • w) - R (x + τ • z)| ≤
      |R (x + τ • (w + z))| + |R (x + τ • w)| + |R (x + τ • z)| := by
    have := abs_sub (R (x + τ • (w + z)) - R (x + τ • w)) (R (x + τ • z))
    have := abs_sub (R (x + τ • (w + z))) (R (x + τ • w))
    linarith
  have hsum : |R (x + τ • (w + z))| + |R (x + τ • w)| + |R (x + τ • z)| ≤
      η / (2 * K) * (τ ^ 2 * K) := by
    have : η / (2 * K) * (τ ^ 2 * ‖w + z‖ ^ 2) + η / (2 * K) * (τ ^ 2 * ‖w‖ ^ 2) +
        η / (2 * K) * (τ ^ 2 * ‖z‖ ^ 2) ≤ η / (2 * K) * (τ ^ 2 * K) := by
      rw [← mul_add, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hK]; nlinarith [sq_nonneg τ]
    linarith
  have hfin : η / (2 * K) * (τ ^ 2 * K) < η * τ ^ 2 := by
    field_simp
    nlinarith [sq_pos_of_pos hτ0]
  linarith

/-! ### Difference quotients of the gradient -/

/-- The difference quotient `[⟪z, ∇f(x + τw)⟫ - ⟪z, ∇f(x)⟫]/τ` of the second and third expressions
in 13(34). -/
noncomputable def gradientDifferenceQuotient (f : E → ℝ) (z w x : E) (τ : ℝ) : ℝ :=
  (⟪z, gradient f (x + τ • w)⟫_ℝ - ⟪z, gradient f x⟫_ℝ) / τ

/-- Upper limits can only grow when the filter is enlarged through a map. -/
theorem ereal_limsup_le_of_tendsto {α β : Type*} {l₁ : Filter α} {l₂ : Filter β} {g : α → β}
    (hg : Tendsto g l₁ l₂) {u : β → EReal} {v : α → EReal} (huv : ∀ a, v a = u (g a)) :
    limsup v l₁ ≤ limsup u l₂ := by
  have h : v = u ∘ g := funext huv
  rw [h, limsup_comp]
  exact limsup_le_limsup_of_le hg

/-- The upper limits of the difference quotients of `∇f` are unchanged if taken also over `w' → w`
and `z' → z`, by the Lipschitz continuity of `∇f` around `x̄`. -/
theorem limsup_gradientDifferenceQuotient_perturb {f : E → ℝ} {x : E}
    (hg : StrictlyContinuousAt (gradient f) x) (z w : E) :
    limsup (fun p : E × ℝ × E × E ↦
        ((gradientDifferenceQuotient f p.2.2.2 p.2.2.1 p.1 p.2.1 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ (𝓝 w ×ˢ 𝓝 z))) =
      limsup (fun q : E × ℝ ↦ ((gradientDifferenceQuotient f z w q.1 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) := by
  have hπ : Tendsto (fun p : E × ℝ × E × E ↦ (p.1, p.2.1))
      (𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ (𝓝 w ×ˢ 𝓝 z))) (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) :=
    tendsto_fst.prodMk (tendsto_fst.comp tendsto_snd)
  have hι : Tendsto (fun q : E × ℝ ↦ (q.1, q.2, w, z)) (𝓝 x ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ (𝓝 w ×ˢ 𝓝 z))) :=
    tendsto_fst.prodMk (tendsto_snd.prodMk (tendsto_const_nhds.prodMk tendsto_const_nhds))
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
    obtain ⟨a, hβa, hac⟩ := EReal.exists_between_coe_real hc
    obtain ⟨b, hab, hbc⟩ := EReal.exists_between_coe_real hac
    have hab' : a < b := EReal.coe_lt_coe_iff.1 hab
    have hev : ∀ᶠ p in 𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ (𝓝 w ×ˢ 𝓝 z)),
        gradientDifferenceQuotient f z w p.1 p.2.1 < a :=
      (hπ.eventually (eventually_lt_of_limsup_lt hβa)).mono fun p hp ↦ EReal.coe_lt_coe_iff.1 hp
    obtain ⟨L, U, hU, hL⟩ := strictlyContinuousAt_iff.1 hg
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
    set K : ℝ := ((L : ℝ) + 1) * (‖w‖ + ‖z‖ + 1) with hK
    have hKpos : 0 < K := by positivity
    set η : ℝ := (b - a) / (2 * K) with hη
    have hη0 : 0 < η := div_pos (by linarith) (by positivity)
    have hset : ball x (r / 2) ×ˢ (Ioo 0 (r / (2 * (‖w‖ + 1))) ×ˢ
        (ball w (min η 1) ×ˢ ball z η)) ∈ 𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ (𝓝 w ×ˢ 𝓝 z)) :=
      prod_mem_prod (ball_mem_nhds _ (by positivity)) (prod_mem_prod
        (Ioo_mem_nhdsGT (by positivity)) (prod_mem_prod (ball_mem_nhds _ (by positivity))
          (ball_mem_nhds _ hη0)))
    refine (limsup_le_of_le (h := ?_)).trans hbc.le
    filter_upwards [hev, hset] with p hp hps
    obtain ⟨y, τ, w', z'⟩ := p
    obtain ⟨hy, ⟨hτ0, hτ1⟩, hw', hz'⟩ := hps
    simp only at hp ⊢
    rw [mem_ball, dist_eq_norm] at hy hw' hz'
    have hw'η : ‖w' - w‖ < η := lt_of_lt_of_le hw' (min_le_left _ _)
    have hw'1 : ‖w' - w‖ < 1 := lt_of_lt_of_le hw' (min_le_right _ _)
    have hnw' : ‖w'‖ ≤ ‖w‖ + 1 := by have := norm_sub_norm_le w' w; linarith
    have hτw : τ * (‖w‖ + 1) < r / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hτ1; linarith
    have hmem : ∀ v : E, ‖v‖ ≤ ‖w‖ + 1 → y + τ • v ∈ U := by
      intro v hv
      apply hball
      rw [mem_ball, dist_eq_norm]
      have := mul_le_mul_of_nonneg_left hv hτ0.le
      calc ‖y + τ • v - x‖ = ‖(y - x) + τ • v‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖τ • v‖ := norm_add_le _ _
        _ = ‖y - x‖ + τ * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hτ0.le]
        _ < r := by linarith
    have hyU : y ∈ U := hball (by rw [mem_ball, dist_eq_norm]; linarith)
    have h1 := hL.norm_sub_le (hmem w' hnw') hyU
    have h2 := hL.norm_sub_le (hmem w' hnw') (hmem w (by linarith))
    rw [show y + τ • w' - y = τ • w' by abel, norm_smul, Real.norm_of_nonneg hτ0.le] at h1
    rw [show y + τ • w' - (y + τ • w) = τ • (w' - w) by rw [smul_sub]; abel, norm_smul,
      Real.norm_of_nonneg hτ0.le] at h2
    have hkey : gradientDifferenceQuotient f z' w' y τ =
        gradientDifferenceQuotient f z w y τ + (⟪z' - z, gradient f (y + τ • w') - gradient f y⟫_ℝ +
          ⟪z, gradient f (y + τ • w') - gradient f (y + τ • w)⟫_ℝ) / τ := by
      simp only [gradientDifferenceQuotient, inner_sub_left, inner_sub_right]
      field_simp
      ring
    have hX : ⟪z' - z, gradient f (y + τ • w') - gradient f y⟫_ℝ ≤
        η * (L * (τ * (‖w‖ + 1))) := by
      refine (real_inner_le_norm _ _).trans (mul_le_mul hz'.le ?_ (norm_nonneg _) hη0.le)
      calc ‖gradient f (y + τ • w') - gradient f y‖ ≤ L * (τ * ‖w'‖) := h1
        _ ≤ L * (τ * (‖w‖ + 1)) := by gcongr
    have hY : ⟪z, gradient f (y + τ • w') - gradient f (y + τ • w)⟫_ℝ ≤ ‖z‖ * (L * (τ * η)) := by
      refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      calc ‖gradient f (y + τ • w') - gradient f (y + τ • w)‖ ≤ L * (τ * ‖w' - w‖) := h2
        _ ≤ L * (τ * η) := by gcongr
    have hsmall : (⟪z' - z, gradient f (y + τ • w') - gradient f y⟫_ℝ +
        ⟪z, gradient f (y + τ • w') - gradient f (y + τ • w)⟫_ℝ) / τ ≤
        L * η * (‖w‖ + ‖z‖ + 1) := by
      rw [div_le_iff₀ hτ0]
      calc _ ≤ η * (L * (τ * (‖w‖ + 1))) + ‖z‖ * (L * (τ * η)) := add_le_add hX hY
        _ = L * η * (‖w‖ + ‖z‖ + 1) * τ := by ring
    have hLη : (L : ℝ) * η * (‖w‖ + ‖z‖ + 1) ≤ (b - a) / 2 := by
      have h3 : (L : ℝ) * η * (‖w‖ + ‖z‖ + 1) ≤ K * η := by
        rw [hK]
        nlinarith [mul_nonneg hη0.le (by positivity : (0 : ℝ) ≤ ‖w‖ + ‖z‖ + 1)]
      have h4 : K * η = (b - a) / 2 := by rw [hη]; field_simp
      linarith
    rw [hkey, EReal.coe_le_coe_iff]
    linarith
  · exact ereal_limsup_le_of_tendsto hι fun _ ↦ rfl

/-- The first equation in 13(34): when the upper limit of the difference quotients of
`⟪z, ∇f(·)⟫` in the direction `w`, taken also over `w' → w` and `z' → z`, is the value `⟪z, Aw⟫`
at a generalized Hessian `A`, the upper limit of the mixed second differences has the same value,
whether taken over `w' → w`, `z' → z` or with `w, z` fixed, and with `τ, σ` independent or `σ = τ`.
-/
theorem limsup_mixedSecondDifference {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, DifferentiableAt ℝ f y)
    (hD : D ⊆ {y ∈ O | DifferentiableAt ℝ (gradient f) y}) {x : E} (hx : x ∈ O) {w z : E}
    {A : E →L[ℝ] E} (hA : A ∈ reachableJacobians (gradient f) D x)
    (hE2 : limsup (fun p : E × ℝ × E × E ↦
      ((gradientDifferenceQuotient f p.2.2.2 p.2.2.1 p.1 p.2.1 : ℝ) : EReal))
      (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ (𝓝 w ×ˢ 𝓝 z))) = ((⟪z, A w⟫_ℝ : ℝ) : EReal)) :
    limsup (fun p : E × (ℝ × ℝ) × E × E ↦
        ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1.1 p.2.1.2 : ℝ) : EReal))
        (𝓝 x ×ˢ ((𝓝[>] 0 ×ˢ 𝓝[>] 0) ×ˢ (𝓝 w ×ˢ 𝓝 z))) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
    limsup (fun p : E × ℝ × E × E ↦
        ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1 p.2.1 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ (𝓝 w ×ˢ 𝓝 z))) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
    limsup (fun p : E × ℝ × ℝ ↦ ((mixedSecondDifference f p.1 w z p.2.1 p.2.2 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
    limsup (fun q : E × ℝ ↦ ((mixedSecondDifference f q.1 w z q.2 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) := by
  set α := ⟪z, A w⟫_ℝ with hα
  -- the upper bound through the mean value theorem
  have hup : limsup (fun p : E × (ℝ × ℝ) × E × E ↦
      ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1.1 p.2.1.2 : ℝ) : EReal))
      (𝓝 x ×ˢ ((𝓝[>] 0 ×ˢ 𝓝[>] 0) ×ˢ (𝓝 w ×ˢ 𝓝 z))) ≤ (α : EReal) := by
    refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
    have hev := eventually_lt_of_limsup_lt (hE2 ▸ hc)
    obtain ⟨t₁, ht₁, t', ht', hsub⟩ := mem_prod_iff.1 hev
    obtain ⟨t₂, ht₂, t'', ht'', hsub'⟩ := mem_prod_iff.1 ht'
    obtain ⟨t₃, ht₃, t₄, ht₄, hsub''⟩ := mem_prod_iff.1 ht''
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 ht₁
    obtain ⟨r₂, hr₂, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht₂
    obtain ⟨r₀, hr₀, hball₀⟩ := Metric.mem_nhds_iff.1 (hO.mem_nhds hx)
    set ρ := min r₁ r₀ / 3 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hρ1 : 3 * ρ ≤ r₁ := by rw [hρ]; linarith [min_le_left r₁ r₀]
    have hρ2 : 3 * ρ ≤ r₀ := by rw [hρ]; linarith [min_le_right r₁ r₀]
    have hr₂' : (0 : ℝ) < r₂ := hr₂
    have hU : ball x ρ ×ˢ ((Ioo 0 (min r₂ (ρ / (‖w‖ + 2))) ×ˢ Ioo 0 (ρ / (‖z‖ + 2))) ×ˢ
        ((t₃ ∩ ball w 1) ×ˢ (t₄ ∩ ball z 1))) ∈
        𝓝 x ×ˢ ((𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ (𝓝 w ×ˢ 𝓝 z)) :=
      prod_mem_prod (ball_mem_nhds _ hρ0) (prod_mem_prod (prod_mem_prod
        (Ioo_mem_nhdsGT (by positivity)) (Ioo_mem_nhdsGT (by positivity)))
        (prod_mem_prod (inter_mem ht₃ (ball_mem_nhds _ one_pos))
          (inter_mem ht₄ (ball_mem_nhds _ one_pos))))
    refine limsup_le_of_le (h := ?_)
    filter_upwards [hU] with p hp
    obtain ⟨y, ⟨τ, σ⟩, w', z'⟩ := p
    obtain ⟨hy, ⟨⟨hτ0, hτ1⟩, ⟨hσ0, hσ1⟩⟩, ⟨hw't, hw'b⟩, ⟨hz't, hz'b⟩⟩ := hp
    rw [mem_ball, dist_eq_norm] at hy hw'b hz'b
    have hnw : ‖w'‖ ≤ ‖w‖ + 1 := by have := norm_sub_norm_le w' w; linarith
    have hnz : ‖z'‖ ≤ ‖z‖ + 1 := by have := norm_sub_norm_le z' z; linarith
    have hτw : τ * ‖w'‖ < ρ := by
      have h1 : τ < ρ / (‖w‖ + 2) := lt_of_lt_of_le hτ1 (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at h1
      have := mul_le_mul_of_nonneg_left hnw hτ0.le
      nlinarith
    have hσz : σ * ‖z'‖ < ρ := by
      rw [lt_div_iff₀ (by positivity)] at hσ1
      have := mul_le_mul_of_nonneg_left hnz hσ0.le
      nlinarith
    have hnorm : ∀ s ∈ Icc (0 : ℝ) σ, ‖y + s • z' - x‖ < 2 * ρ := by
      intro s hs
      have := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg z')
      calc ‖y + s • z' - x‖ = ‖(y - x) + s • z'‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖s • z'‖ := norm_add_le _ _
        _ = ‖y - x‖ + s * ‖z'‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1]
        _ < 2 * ρ := by linarith
    have hseg : ∀ s ∈ Icc (0 : ℝ) σ, y + s • z' ∈ O ∧ y + s • z' + τ • w' ∈ O := by
      intro s hs
      refine ⟨hball₀ ?_, hball₀ ?_⟩
      · rw [mem_ball, dist_eq_norm]; linarith [hnorm s hs]
      · rw [mem_ball, dist_eq_norm]
        calc ‖y + s • z' + τ • w' - x‖ = ‖(y + s • z' - x) + τ • w'‖ := by congr 1; abel
          _ ≤ ‖y + s • z' - x‖ + ‖τ • w'‖ := norm_add_le _ _
          _ = ‖y + s • z' - x‖ + τ * ‖w'‖ := by rw [norm_smul, Real.norm_of_nonneg hτ0.le]
          _ < r₀ := by linarith [hnorm s hs]
    obtain ⟨s, hs, heq⟩ := mixedSecondDifference_eq_mvt hf hτ0 hσ0 hseg
    have hmem : (y + s • z', τ, w', z') ∈ t₁ ×ˢ t' := by
      refine ⟨hball₁ ?_, hsub' ⟨hIoo ⟨hτ0, lt_of_lt_of_le hτ1 (min_le_left _ _)⟩,
        hsub'' ⟨hw't, hz't⟩⟩⟩
      rw [mem_ball, dist_eq_norm]
      linarith [hnorm s (Ioo_subset_Icc_self hs)]
    have h := hsub hmem
    simp only [mem_setOf_eq] at h
    rw [heq]
    exact h.le
  -- the lower bound along `σ = τ` at second-order points
  have hlow : (α : EReal) ≤ limsup (fun q : E × ℝ ↦
      ((mixedSecondDifference f q.1 w z q.2 q.2 : ℝ) : EReal)) (𝓝 x ×ˢ 𝓝[>] 0) := by
    refine le_of_forall_lt fun c hc ↦ ?_
    obtain ⟨c', hcc', hc'α⟩ := EReal.exists_between_coe_real hc
    refine lt_of_lt_of_le hcc' (le_limsup_of_frequently_le' ?_)
    have hc'α' : c' < α := EReal.coe_lt_coe_iff.1 hc'α
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_prod_iff.1 hU
    obtain ⟨y, hyD, hyx, hBlim⟩ := mem_clusterValuesWithin_iff.1 hA
    have hconv : Tendsto (fun n ↦ ⟪z, fderiv ℝ (gradient f) (y n) w⟫_ℝ) atTop (𝓝 α) :=
      tendsto_const_nhds.inner (((ContinuousLinearMap.apply ℝ E w).continuous.tendsto A).comp hBlim)
    obtain ⟨n, hn1, hn2⟩ := ((hyx.eventually ht₁).and
      (hconv.eventually (lt_mem_nhds (show (c' + α) / 2 < α by linarith)))).exists
    have hloc : ∀ᶠ y' in 𝓝 (y n), DifferentiableAt ℝ f y' :=
      Filter.mem_of_superset (hO.mem_nhds (hD (hyD n)).1) fun y' hy' ↦ hf y' hy'
    have hdiag := tendsto_mixedSecondDifference_diag hloc (hD (hyD n)).2 w z
    obtain ⟨τ, hτ1, hτ2⟩ := ((hdiag.eventually (lt_mem_nhds hn2)).and ht₂).exists
    refine ⟨(y n, τ), hsub ⟨hn1, hτ2⟩, EReal.coe_le_coe_iff.2 ?_⟩
    linarith
  -- comparisons between the four upper limits
  have h1 : limsup (fun q : E × ℝ ↦ ((mixedSecondDifference f q.1 w z q.2 q.2 : ℝ) : EReal))
      (𝓝 x ×ˢ 𝓝[>] 0) ≤ limsup (fun p : E × ℝ × ℝ ↦
        ((mixedSecondDifference f p.1 w z p.2.1 p.2.2 : ℝ) : EReal)) (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) :=
    ereal_limsup_le_of_tendsto (g := fun q : E × ℝ ↦ (q.1, q.2, q.2))
      (tendsto_fst.prodMk (tendsto_snd.prodMk tendsto_snd)) fun _ ↦ rfl
  have h2 : limsup (fun p : E × ℝ × ℝ ↦ ((mixedSecondDifference f p.1 w z p.2.1 p.2.2 : ℝ) :
      EReal)) (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) ≤ limsup (fun p : E × (ℝ × ℝ) × E × E ↦
        ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1.1 p.2.1.2 : ℝ) : EReal))
        (𝓝 x ×ˢ ((𝓝[>] 0 ×ˢ 𝓝[>] 0) ×ˢ (𝓝 w ×ˢ 𝓝 z))) :=
    ereal_limsup_le_of_tendsto (g := fun p : E × ℝ × ℝ ↦ (p.1, p.2, w, z))
      (tendsto_fst.prodMk (tendsto_snd.prodMk (tendsto_const_nhds.prodMk tendsto_const_nhds)))
      fun _ ↦ rfl
  have h3 : limsup (fun q : E × ℝ ↦ ((mixedSecondDifference f q.1 w z q.2 q.2 : ℝ) : EReal))
      (𝓝 x ×ˢ 𝓝[>] 0) ≤ limsup (fun p : E × ℝ × E × E ↦
        ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1 p.2.1 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ (𝓝 w ×ˢ 𝓝 z))) :=
    ereal_limsup_le_of_tendsto (g := fun q : E × ℝ ↦ (q.1, q.2, w, z))
      (tendsto_fst.prodMk (tendsto_snd.prodMk (tendsto_const_nhds.prodMk tendsto_const_nhds)))
      fun _ ↦ rfl
  have h4 : limsup (fun p : E × ℝ × E × E ↦
        ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1 p.2.1 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ (𝓝 w ×ˢ 𝓝 z))) ≤ limsup (fun p : E × (ℝ × ℝ) × E × E ↦
        ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1.1 p.2.1.2 : ℝ) : EReal))
        (𝓝 x ×ˢ ((𝓝[>] 0 ×ˢ 𝓝[>] 0) ×ˢ (𝓝 w ×ˢ 𝓝 z))) :=
    ereal_limsup_le_of_tendsto (g := fun p : E × ℝ × E × E ↦ (p.1, (p.2.1, p.2.1), p.2.2))
      (tendsto_fst.prodMk (((tendsto_fst.comp tendsto_snd).prodMk
        (tendsto_fst.comp tendsto_snd)).prodMk (tendsto_snd.comp tendsto_snd))) fun _ ↦ rfl
  exact ⟨le_antisymm hup (hlow.trans (h1.trans h2)), le_antisymm (h4.trans hup) (hlow.trans h3),
    le_antisymm (h2.trans hup) (hlow.trans h1), le_antisymm (h1.trans (h2.trans hup)) hlow⟩

/-! ### Points of twice differentiability of a `C¹` function -/

/-- For `f` differentiable around `x`, twice differentiability at `x` in the classical sense means
that `∇f` is differentiable at `x`, the Hessian being its derivative. -/
theorem hasClassicalHessianAt_coe_iff {f : E → ℝ} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) {A : E →L[ℝ] E} :
    HasClassicalHessianAt (fun y ↦ (f y : EReal)) x A ↔ HasFDerivAt (gradient f) A x := by
  simp only [HasClassicalHessianAt, EReal.toReal_coe]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hf.mono fun y hy ↦ ⟨trivial, hy⟩, h⟩⟩

/-- For `f` differentiable around `x`, twice differentiability at `x` in the extended sense means
that `∇f` is differentiable at `x`, the Hessian being its derivative. -/
theorem hasExtendedHessianAt_coe_iff {f : E → ℝ} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) {A : E →L[ℝ] E} :
    HasExtendedHessianAt (fun y ↦ (f y : EReal)) x A ↔ HasFDerivAt (gradient f) A x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ((hasClassicalHessianAt_coe_iff hf).2 h).hasExtendedHessianAt⟩
  obtain ⟨-, -, ho⟩ := h
  simp only [EReal.toReal_coe] at ho
  rw [nhdsWithin_eq_nhds.2 hf] at ho
  exact HasFDerivAtFilter.of_isLittleO ho

/-- For `f` of class `C¹⁺` on an open set `O` and `x ∈ O`, twice differentiability of `f` at `x` in
the classical sense, or in the extended sense, with Hessian `A` means `∇(∇f)(x) = A`; so the points
of `O` where `f` is twice differentiable in either sense are those where `∇f` is differentiable. -/
theorem IsC1PlusOn.twice_differentiable_iff {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : IsC1PlusOn f O) {x : E} (hx : x ∈ O) {A : E →L[ℝ] E} :
    (HasClassicalHessianAt (fun y ↦ (f y : EReal)) x A ↔ HasFDerivAt (gradient f) A x) ∧
    (HasExtendedHessianAt (fun y ↦ (f y : EReal)) x A ↔ HasFDerivAt (gradient f) A x) := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    Filter.mem_of_superset (hO.mem_nhds hx) fun y hy ↦ (hf y hy).1
  exact ⟨hasClassicalHessianAt_coe_iff hev, hasExtendedHessianAt_coe_iff hev⟩

variable [MeasurableSpace E] [BorelSpace E]


/-- The parts of **Theorem 13.52** that come from 9.62: for `f` of class `C¹⁺` on `O` and an
approach set `D` of points where `∇f` is differentiable, with negligible complement in the set of
all such points of `O`, the generalized Hessians `∇̄²f(x̄)` form a nonempty compact set of symmetric
maps, 13(33) holds, and the maxima in 13(34) as well as its second and third upper limits are all
equal to `max {⟪z, Aw⟫ ∣ A ∈ ∇̄²f(x̄)}`. -/
theorem generalized_hessians_first_order {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, DifferentiableAt ℝ f y) (hg : ∀ y ∈ O, StrictlyContinuousAt (gradient f) y)
    (hD : D ⊆ {y ∈ O | DifferentiableAt ℝ (gradient f) y})
    (hnull : volume ({y ∈ O | DifferentiableAt ℝ (gradient f) y} \ D) = 0) {x : E} (hx : x ∈ O) :
    (reachableJacobians (gradient f) D x).Nonempty ∧
    IsCompact (reachableJacobians (gradient f) D x) ∧
    (∀ A ∈ reachableJacobians (gradient f) D x, ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ) ∧
    (∀ w, convexHull ℝ (strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) w) =
        convexHull ℝ (coderivative (svSingleton (gradient f)) x (gradient f x) w) ∧
      convexHull ℝ (coderivative (svSingleton (gradient f)) x (gradient f x) w) =
        convexHull ℝ ((fun A : E →L[ℝ] E ↦ A w) '' reachableJacobians (gradient f) D x)) ∧
    ∀ z w, ∃ A ∈ reachableJacobians (gradient f) D x,
      (∀ B ∈ reachableJacobians (gradient f) D x, ⟪z, B w⟫_ℝ ≤ ⟪z, A w⟫_ℝ) ∧
      (∃ ζ ∈ strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) w,
        (∀ ζ' ∈ strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) w,
          ⟪z, ζ'⟫_ℝ ≤ ⟪z, ζ⟫_ℝ) ∧ ⟪z, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
      (∃ ζ ∈ strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) z,
        (∀ ζ' ∈ strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) z,
          ⟪w, ζ'⟫_ℝ ≤ ⟪w, ζ⟫_ℝ) ∧ ⟪w, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
      limsup (fun q : E × ℝ ↦ ((gradientDifferenceQuotient f z w q.1 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun q : E × ℝ ↦ ((gradientDifferenceQuotient f w z q.1 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) := by
  have hsym : ∀ A ∈ reachableJacobians (gradient f) D x, ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
    fun A hA u v ↦ reachableJacobians_gradient_inner_comm hO hf hD hA u v
  have hDdiff : ∀ y ∈ D, DifferentiableAt ℝ (gradient f) y := fun y hy ↦ (hD hy).2
  have hxD := subset_closure_differentiability_set_of_null_complement volume hO hg hnull hx
  obtain ⟨hne, hcpt⟩ := reachableJacobians_nonempty_compact (hg x hx) hxD
  -- the Clarke derivative of `⟪y, ∇f(·)⟫` as an upper limit
  have hclarke : ∀ y w, limsup (fun q : E × ℝ ↦
      ((gradientDifferenceQuotient f y w q.1 q.2 : ℝ) : EReal)) (𝓝 x ×ˢ 𝓝[>] 0) =
      supportFunction (strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) w)
        y := by
    intro y w
    have hsc : ERealStrictlyContinuousAt (fun a ↦ ((⟪y, gradient f a⟫_ℝ : ℝ) : EReal)) x :=
      ⟨by simp, by simpa only [EReal.toReal_coe] using (hg x hx).inner_const y⟩
    rw [← (hg x hx).regularSubderivative_scalar_eq_support_strictGraphicalDerivative w y,
      hsc.regularSubderivative_eq_limsup_differenceQuotient]
    apply limsup_congr
    filter_upwards [tendsto_snd.eventually self_mem_nhdsWithin] with q hq
    rw [gradientDifferenceQuotient, differenceQuotient, ← EReal.coe_sub, ← EReal.coe_mul,
      div_eq_inv_mul]
  refine ⟨hne, hcpt, hsym, fun w ↦ ?_, fun z w ↦ ?_⟩
  · -- 13(33)
    have h1 :=
      (convexHull_strictGraphicalDerivative_eq_reachableJacobians hO hg hDdiff hnull hx w).1
    have h2 := (convexHull_coderivative_eq_reachableJacobians hO hg hDdiff hnull hx w).1
    have himg : (fun A : E →L[ℝ] E ↦ A.adjoint w) '' reachableJacobians (gradient f) D x =
        (fun A : E →L[ℝ] E ↦ A w) '' reachableJacobians (gradient f) D x := by
      apply image_congr
      intro A hA
      apply ext_inner_right ℝ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hsym A hA w u]
    rw [himg] at h2
    exact ⟨h1.trans h2.symm, h2⟩
  · obtain ⟨ζ, hζ, v, -, A, hA, hζv, hζA, hζmax, -, hAmax⟩ :=
      strictGraphicalDerivative_coderivative_reachableJacobian_maxima hO hg hDdiff hnull hx w z
    obtain ⟨ζ', hζ', v', -, A', hA', -, hζA', hζ'max, -, hA'max⟩ :=
      strictGraphicalDerivative_coderivative_reachableJacobian_maxima hO hg hDdiff hnull hx z w
    -- the two maxima over the generalized Hessians agree by symmetry
    have hAA' : ⟪w, A' z⟫_ℝ = ⟪z, A w⟫_ℝ := by
      apply le_antisymm
      · have h1 := hAmax A' hA'
        have h2 := hsym A' hA' w z
        have h3 : ⟪A' w, z⟫_ℝ = ⟪z, A' w⟫_ℝ := real_inner_comm _ _
        linarith
      · have h1 := hA'max A hA
        have h2 := hsym A hA w z
        have h3 : ⟪A w, z⟫_ℝ = ⟪z, A w⟫_ℝ := real_inner_comm _ _
        linarith
    refine ⟨A, hA, hAmax, ⟨ζ, hζ, hζmax, hζA⟩, ⟨ζ', hζ', hζ'max, hζA'.trans hAA'⟩, ?_, ?_⟩
    · rw [hclarke]
      apply le_antisymm
      · refine (supportFunction_le_iff _ _ _).2 fun a ha ↦ EReal.coe_le_coe_iff.2 ?_
        have h1 := hζmax a ha
        have h2 : ⟪a, z⟫_ℝ = ⟪z, a⟫_ℝ := real_inner_comm _ _
        linarith
      · have h : ⟪ζ, z⟫_ℝ = ⟪z, A w⟫_ℝ := by rw [real_inner_comm]; exact hζA
        rw [← h]
        exact inner_le_supportFunction hζ z
    · rw [hclarke]
      apply le_antisymm
      · refine (supportFunction_le_iff _ _ _).2 fun a ha ↦ EReal.coe_le_coe_iff.2 ?_
        have h1 := hζ'max a ha
        have h2 : ⟪a, w⟫_ℝ = ⟪w, a⟫_ℝ := real_inner_comm _ _
        linarith
      · have h : ⟪ζ', w⟫_ℝ = ⟪z, A w⟫_ℝ := by rw [real_inner_comm]; linarith
        rw [← h]
        exact inner_le_supportFunction hζ' w

/-- **Theorem 13.52** (generalization of second-derivative symmetry).  Let `f` be of class `C¹⁺` on
an open set `O`, and let `D ⊆ O` consist of points where `f` is twice differentiable in the
classical or extended sense — equivalently, where `∇f` is differentiable
(`IsC1PlusOn.twice_differentiable_iff`) — such that the set of all such points of `O` minus `D` is
negligible (`D` may be the set of all such points, or any subset of it with negligible complement).
For `x̄ ∈ O`, the generalized Hessians `∇̄²f(x̄) = {A ∣ ∃ xν → x̄, xν ∈ D, ∇²f(xν) → A}`
(`reachableJacobians (∇f) D x̄`) form a nonempty compact set of symmetric maps, 13(33) holds with
the strict derivative `D_*(∇f)(x̄)` of 9.53, and for all `z, w` the maximum
`α = max {⟪z, Aw⟫ ∣ A ∈ ∇̄²f(x̄)}` (attained at `A`) satisfies
`α = max ⟪z, D_*(∇f)(x̄)(w)⟫ = max ⟪w, D_*(∇f)(x̄)(z)⟫`, and the three upper limits in 13(34) equal
`α`; they are unchanged if taken also over `w' → w` and `z' → z`, or with `σ = τ`. -/
theorem generalization_of_second_derivative_symmetry {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : IsC1PlusOn f O) (hD : D ⊆ {y ∈ O | DifferentiableAt ℝ (gradient f) y})
    (hnull : volume ({y ∈ O | DifferentiableAt ℝ (gradient f) y} \ D) = 0) {x : E} (hx : x ∈ O) :
    (reachableJacobians (gradient f) D x).Nonempty ∧
    IsCompact (reachableJacobians (gradient f) D x) ∧
    (∀ A ∈ reachableJacobians (gradient f) D x, ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ) ∧
    (∀ w, convexHull ℝ (strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) w) =
        convexHull ℝ (coderivative (svSingleton (gradient f)) x (gradient f x) w) ∧
      convexHull ℝ (coderivative (svSingleton (gradient f)) x (gradient f x) w) =
        convexHull ℝ ((fun A : E →L[ℝ] E ↦ A w) '' reachableJacobians (gradient f) D x)) ∧
    ∀ z w, ∃ A ∈ reachableJacobians (gradient f) D x,
      (∀ B ∈ reachableJacobians (gradient f) D x, ⟪z, B w⟫_ℝ ≤ ⟪z, A w⟫_ℝ) ∧
      (∃ ζ ∈ strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) w,
        (∀ ζ' ∈ strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) w,
          ⟪z, ζ'⟫_ℝ ≤ ⟪z, ζ⟫_ℝ) ∧ ⟪z, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
      (∃ ζ ∈ strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) z,
        (∀ ζ' ∈ strictGraphicalDerivative (svSingleton (gradient f)) x (gradient f x) z,
          ⟪w, ζ'⟫_ℝ ≤ ⟪w, ζ⟫_ℝ) ∧ ⟪w, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
      limsup (fun p : E × ℝ × ℝ ↦ ((mixedSecondDifference f p.1 w z p.2.1 p.2.2 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun q : E × ℝ ↦ ((gradientDifferenceQuotient f z w q.1 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun q : E × ℝ ↦ ((gradientDifferenceQuotient f w z q.1 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun q : E × ℝ ↦ ((mixedSecondDifference f q.1 w z q.2 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun p : E × (ℝ × ℝ) × E × E ↦
        ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1.1 p.2.1.2 : ℝ) : EReal))
        (𝓝 x ×ˢ ((𝓝[>] 0 ×ˢ 𝓝[>] 0) ×ˢ (𝓝 w ×ˢ 𝓝 z))) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun p : E × ℝ × E × E ↦
        ((mixedSecondDifference f p.1 p.2.2.1 p.2.2.2 p.2.1 p.2.1 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ (𝓝 w ×ˢ 𝓝 z))) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun p : E × ℝ × E × E ↦
        ((gradientDifferenceQuotient f p.2.2.2 p.2.2.1 p.1 p.2.1 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ (𝓝 w ×ˢ 𝓝 z))) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun p : E × ℝ × E × E ↦
        ((gradientDifferenceQuotient f p.2.2.2 p.2.2.1 p.1 p.2.1 : ℝ) : EReal))
        (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ (𝓝 z ×ˢ 𝓝 w))) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) := by
  have hdiff : ∀ y ∈ O, DifferentiableAt ℝ f y := fun y hy ↦ (hf y hy).1
  have hg : ∀ y ∈ O, StrictlyContinuousAt (gradient f) y := fun y hy ↦ (hf y hy).2
  obtain ⟨hne, hcpt, hsym, h33, h34⟩ := generalized_hessians_first_order hO hdiff hg hD hnull hx
  refine ⟨hne, hcpt, hsym, h33, fun z w ↦ ?_⟩
  obtain ⟨A, hA, hmax, hζ1, hζ2, hE2, hE3⟩ := h34 z w
  have hE2' := (limsup_gradientDifferenceQuotient_perturb (hg x hx) z w).trans hE2
  have hE3' := (limsup_gradientDifferenceQuotient_perturb (hg x hx) w z).trans hE3
  obtain ⟨h1, h2, h3, h4⟩ := limsup_mixedSecondDifference hO hdiff hD hx hA hE2'
  exact ⟨A, hA, hmax, hζ1, hζ2, h3, hE2, hE3, h4, h1, h2, hE2', hE3'⟩

end RW
