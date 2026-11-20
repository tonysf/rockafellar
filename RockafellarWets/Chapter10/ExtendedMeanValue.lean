/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: the extended mean-value theorem

**Theorem 10.48**: if `f` is strictly continuous on an open convex set `O` and `x₀, x₁ ∈ O`,
then for some `τ ∈ (0, 1)` and `x_τ = (1 - τ)x₀ + τx₁` there is `v` with
`f(x₁) - f(x₀) = ⟪v, x₁ - x₀⟫` and `v ∈ ∂f(x_τ)` or `-v ∈ ∂(-f)(x_τ)`
(`exists_mean_value_subgradient`); if `f` is regular on `O`, `v ∈ ∂f(x_τ)`
(`exists_mean_value_subgradient_of_regular`).

As in the book, `φ(t) = f(x_t) - (1 - t)f(x₀) - t f(x₁)` vanishes at `0` and `1`, so it has a
local minimum or maximum at some `τ ∈ (0, 1)`, and Fermat's rule 10.1, the chain rule 10.6 for
`t ↦ x₀ + t(x₁ - x₀)` (with `∂^∞ f = {0}` by strict continuity) and the sum rule 10.10 for the
affine part give the conclusion.  Because the library chain rule asks for a globally lsc outer
function, `f` is first replaced by a globally Lipschitz McShane extension of its restriction to a
compact convex neighborhood of the segment; subgradients at points of the segment are
unaffected.  In the regular case, `-∂(-f)(x_τ)` consists of limits of gradients at points of
differentiability (9.21), which are limits of regular subgradients, so `-∂(-f)(x_τ) ⊂ ∂f(x_τ)`.
-/

import RockafellarWets.Chapter10.FermatRule
import RockafellarWets.Chapter10.LipschitzSums
import RockafellarWets.Chapter10.BasicChainRule
import RockafellarWets.Chapter9.RegularStrictContinuity
import RockafellarWets.Chapter9.StrictDifferentiability
import RockafellarWets.Chapter9.LipschitzSubgradientLimits
import RockafellarWets.Chapter9.SmoothnessCriteria
import RockafellarWets.Chapter8.SubderivativeFormulas
import Mathlib.Topology.Order.Rolle

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem real_inner_eq (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  simp [RCLike.inner_apply, mul_comm]

/-- The mean-value inclusion for a globally Lipschitz `g` along the line through `x₀` in
direction `d`, at an interior local extremum of `t ↦ g(x₀ + t d) - a(t)` with affine `a`. -/
private theorem chain_line {g : E → ℝ} {k : ℝ≥0} (hg : LipschitzWith k g) (x₀ d : E) (α β : ℝ)
    {τ : ℝ} (hmin : IsLocalMin (fun t ↦ g (x₀ + t • d) - (α + t * β)) τ) :
    ∃ v ∈ subdifferential (fun y ↦ (g y : EReal)) (x₀ + τ • d), ⟪v, d⟫_ℝ = β := by
  set G : ℝ → E := fun t ↦ x₀ + t • d with hG
  have hGc : ContDiff ℝ 1 G := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hGd : ∀ t, HasFDerivAt G (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d) t := fun t ↦ by
    have := (((hasDerivAt_id t).smul_const d).const_add x₀).hasFDerivAt
    simpa [hG] using this
  have hadj : ∀ v, (fderiv ℝ G τ).adjoint v = ⟪d, v⟫_ℝ := by
    intro v
    rw [(hGd τ).fderiv]
    have h1 := ContinuousLinearMap.adjoint_inner_left (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d) 1 v
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul,
      real_inner_eq, mul_one] at h1
    rw [h1, real_inner_comm]
  -- the outer function and its horizon subgradients
  have hgc : Continuous fun y ↦ (g y : EReal) := continuous_coe_real_ereal.comp hg.continuous
  have hgsc : ∀ y, ERealStrictlyContinuousAt (fun z ↦ (g z : EReal)) y := fun y ↦
    eRealStrictlyContinuousAt_coe_of_lipschitz hg
  have hhor : horizonSubdifferential (fun z ↦ (g z : EReal)) (G τ) = {0} :=
    (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero
      (f := fun z ↦ (g z : EReal)) (x := G τ) (c := g (G τ)) rfl
      (hgsc (G τ)).isLocallyLscAt).1 (hgsc (G τ))
  have hQ : ∀ y ∈ horizonSubdifferential (fun z ↦ (g z : EReal)) (G τ),
      (fderiv ℝ G τ).adjoint y = 0 → y = 0 := fun y hy _ ↦ by
    rw [hhor] at hy
    exact hy
  have hchain := subdifferential_comp_subset (g := fun z ↦ (g z : EReal)) hGc
    hgc.lowerSemicontinuous (c := g (G τ)) rfl hQ
  -- the affine part
  set A : ℝ → EReal := fun t ↦ ((-(α + t * β) : ℝ) : EReal) with hA
  have hAL : LipschitzWith ⟨|β|, abs_nonneg β⟩ (fun t : ℝ ↦ -(α + t * β)) := by
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mk,
      show -(α + s * β) - -(α + t * β) = β * (t - s) by ring, abs_mul, abs_sub_comm]
  have hAsc : ERealStrictlyContinuousAt A τ := eRealStrictlyContinuousAt_coe_of_lipschitz hAL
  have hAgrad : HasStrictGradientAt A (-β) τ := by
    refine ⟨Eventually.of_forall fun _ ↦
      (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm, ?_⟩
    have h1 : HasStrictDerivAt (fun t : ℝ ↦ -(α + t * β)) (-β) τ := by
      have := (((hasStrictDerivAt_id τ).mul_const β).const_add α).neg
      exact this.congr_deriv (by ring)
    have h2 : innerSL ℝ (-β) = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-β) := by
      ext
      simp [mul_comm]
    simp only [hA, EReal.toReal_coe]
    rw [h2]
    exact h1.hasStrictFDerivAt
  have hAsub : subdifferential A τ = {-β} := hAgrad.subdifferential_eq
  -- Fermat at the local minimum
  set Ψ : ℝ → EReal := fun t ↦ (g (G t) : EReal) with hΨ
  have hΨl : LowerSemicontinuous Ψ := (hgc.comp (hGc.continuous)).lowerSemicontinuous
  have hΨp : IsProper Ψ := ⟨⟨0, EReal.coe_lt_top _⟩, fun t ↦ EReal.bot_lt_coe _⟩
  have hsumfun : A + Ψ = fun t ↦ ((g (x₀ + t • d) - (α + t * β) : ℝ) : EReal) := by
    funext t
    simp only [Pi.add_apply, hA, hΨ, hG]
    rw [← EReal.coe_add]
    ring_nf
  have hloc : IsLocalMin (A + Ψ) τ := by
    rw [hsumfun]
    exact hmin.comp_mono (fun a b h ↦ EReal.coe_le_coe_iff.2 h)
  have hval : (A + Ψ) τ = ((g (x₀ + τ • d) - (α + τ * β) : ℝ) : EReal) := by rw [hsumfun]
  have h0 := IsLocalMin.zero_mem_subdifferential hloc hval
  obtain ⟨a, ha, s, hs, has⟩ :=
    subdifferential_add_subset_of_strictlyContinuous hAsc hΨl hΨp (c := g (G τ)) rfl h0
  rw [hAsub, mem_singleton_iff] at ha
  have hs' : s ∈ subdifferential ((fun z ↦ (g z : EReal)) ∘ G) τ := hs
  obtain ⟨v, hv, hvs⟩ := hchain hs'
  refine ⟨v, hv, ?_⟩
  rw [hadj] at hvs
  rw [real_inner_comm]
  have : s = β := by rw [ha] at has; linarith
  rw [hvs, this]

/-- **Theorem 10.48** (mean-value theorem, extended). -/
theorem exists_mean_value_subgradient {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hOc : Convex ℝ O) (hf : ∀ y ∈ O, StrictlyContinuousAt f y) {x₀ x₁ : E} (h₀ : x₀ ∈ O)
    (h₁ : x₁ ∈ O) :
    ∃ τ ∈ Ioo (0 : ℝ) 1, ∃ v : E, f x₁ - f x₀ = ⟪v, x₁ - x₀⟫_ℝ ∧
      (v ∈ subdifferential (fun y ↦ (f y : EReal)) ((1 - τ) • x₀ + τ • x₁) ∨
        -v ∈ subdifferential (fun y ↦ -((f y : ℝ) : EReal)) ((1 - τ) • x₀ + τ • x₁)) := by
  set d := x₁ - x₀ with hd
  set S := segment ℝ x₀ x₁ with hS
  have hSO : S ⊆ O := hOc.segment_subset h₀ h₁
  have hSc : IsCompact S := by
    rw [hS, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨r, hr, hrO⟩ := hSc.exists_cthickening_subset_open hO hSO
  set K := cthickening r S with hK
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded isClosed_cthickening
    hSc.isBounded.cthickening
  have hll : LocallyLipschitzOn K f := fun y hy ↦ by
    obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 (hf y (hrO hy))
    exact ⟨k, U, nhdsWithin_le_nhds hU, hL⟩
  obtain ⟨k, hk⟩ := hll.exists_lipschitzOnWith_of_compact hKc
  obtain ⟨g, hgL, hgeq⟩ := hk.extend_real
  -- `f = g` near the segment
  have hnear : ∀ y ∈ S, (fun z ↦ (f z : EReal)) =ᶠ[𝓝 y] fun z ↦ (g z : EReal) := by
    intro y hy
    have hth : thickening r S ∈ 𝓝 y := isOpen_thickening.mem_nhds (self_subset_thickening hr S hy)
    filter_upwards [hth] with z hz
    rw [hgeq (thickening_subset_cthickening r S hz)]
  have hnear' : ∀ y ∈ S, (fun z ↦ -((f z : ℝ) : EReal)) =ᶠ[𝓝 y] fun z ↦ -((g z : ℝ) : EReal) := by
    intro y hy
    filter_upwards [hnear y hy] with z hz
    rw [hz]
  have hsub : ∀ y ∈ S, subdifferential (fun z ↦ (f z : EReal)) y =
      subdifferential (fun z ↦ (g z : EReal)) y := fun y hy ↦
    subdifferential_congr_nhds_of_finite (c := f y) rfl (hnear y hy)
  have hsub' : ∀ y ∈ S, subdifferential (fun z ↦ -((f z : ℝ) : EReal)) y =
      subdifferential (fun z ↦ -((g z : ℝ) : EReal)) y := fun y hy ↦
    subdifferential_congr_nhds_of_finite (c := -f y) (by simp) (hnear' y hy)
  have hgx₀ : g x₀ = f x₀ := (hgeq (self_subset_cthickening S (left_mem_segment ℝ x₀ x₁))).symm
  have hgx₁ : g x₁ = f x₁ := (hgeq (self_subset_cthickening S (right_mem_segment ℝ x₀ x₁))).symm
  -- the function `φ`
  set φ : ℝ → ℝ := fun t ↦ g (x₀ + t • d) - (f x₀ + t * (f x₁ - f x₀)) with hφ
  have hφc : Continuous φ :=
    (hgL.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
      (continuous_const.add (continuous_id.mul continuous_const))
  have hφ01 : φ 0 = φ 1 := by
    simp only [hφ, zero_smul, add_zero, zero_mul, one_smul, one_mul, hd, add_sub_cancel, hgx₀, hgx₁]
    ring
  obtain ⟨τ, hτ, hext⟩ := exists_Ioo_extr_on_Icc zero_lt_one hφc.continuousOn hφ01
  have hlext := hext.isLocalExtr (Icc_mem_nhds hτ.1 hτ.2)
  have hxτ : x₀ + τ • d = (1 - τ) • x₀ + τ • x₁ := by rw [hd, smul_sub, sub_smul, one_smul]; abel
  have hτS : x₀ + τ • d ∈ S := by
    rw [hxτ]
    exact ⟨1 - τ, τ, by linarith [hτ.2], hτ.1.le, by ring, rfl⟩
  refine ⟨τ, hτ, ?_⟩
  rcases hlext with hmin | hmax
  · obtain ⟨v, hv, hvd⟩ := chain_line hgL x₀ d (f x₀) (f x₁ - f x₀) hmin
    refine ⟨v, by rw [hvd], Or.inl ?_⟩
    rw [← hxτ, hsub _ hτS]
    exact hv
  · have hfeq : (fun t ↦ (-g) (x₀ + t • d) - (-f x₀ + t * (f x₀ - f x₁))) = fun t ↦ -φ t := by
      funext t
      simp only [hφ, Pi.neg_apply]
      ring
    have hmin' : IsLocalMin (fun t ↦ (-g) (x₀ + t • d) - (-f x₀ + t * (f x₀ - f x₁))) τ := by
      rw [hfeq]
      exact hmax.neg
    obtain ⟨u, hu, hud⟩ := chain_line hgL.neg x₀ d (-f x₀) (f x₀ - f x₁) hmin'
    refine ⟨-u, ?_, Or.inr ?_⟩
    · rw [inner_neg_left, hud]
      ring
    · rw [neg_neg, ← hxτ, hsub' _ hτS]
      have hfun : (fun y ↦ ((-g y : ℝ) : EReal)) = fun z ↦ -((g z : ℝ) : EReal) :=
        funext fun z ↦ EReal.coe_neg _
      simpa [Pi.neg_apply, hfun] using hu

/-- **Theorem 10.48**, regular case: if `f` is also regular on `O`, the subgradient can be taken
in `∂f(x_τ)`. -/
theorem exists_mean_value_subgradient_of_regular {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hOc : Convex ℝ O) (hf : ∀ y ∈ O, StrictlyContinuousAt f y)
    (hreg : ∀ y ∈ O, IsSubdifferentiallyRegularAt (fun z ↦ (f z : EReal)) y) {x₀ x₁ : E}
    (h₀ : x₀ ∈ O) (h₁ : x₁ ∈ O) :
    ∃ τ ∈ Ioo (0 : ℝ) 1, ∃ v ∈ subdifferential (fun y ↦ (f y : EReal)) ((1 - τ) • x₀ + τ • x₁),
      f x₁ - f x₀ = ⟪v, x₁ - x₀⟫_ℝ := by
  obtain ⟨τ, hτ, v, hv, hor⟩ := exists_mean_value_subgradient hO hOc hf h₀ h₁
  refine ⟨τ, hτ, v, ?_, hv⟩
  set xτ := (1 - τ) • x₀ + τ • x₁ with hxτ
  have hxτO : xτ ∈ O := hOc h₀ h₁ (by linarith [hτ.2]) hτ.1.le (by ring)
  rcases hor with hv' | hv'
  · exact hv'
  -- `-∂(-f)(x_τ) ⊂ ∂f(x_τ)` for regular `f`
  have hsc : ∀ y ∈ O, ERealStrictlyContinuousAt (fun z ↦ (f z : EReal)) y := fun y hy ↦
    ⟨by simp, by simpa only [EReal.toReal_coe] using hf y hy⟩
  have h := neg_subdifferential_neg_eq hO (fun y hy ↦ ⟨hsc y hy, hreg y hy⟩) hxτO
  have hf' : (fun y ↦ ((f y : EReal)).toReal) = f := funext fun y ↦ EReal.toReal_coe _
  simp only [hf'] at h
  have hmem : v ∈ -subdifferential (fun y ↦ -((f y : ℝ) : EReal)) xτ := by
    rw [Set.mem_neg]
    exact hv'
  rw [h] at hmem
  obtain ⟨xs, hxs, hdiff, hgrad⟩ := hmem
  have hfc : ContinuousAt f xτ := by
    obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 (hf xτ hxτO)
    exact hL.continuousOn.continuousAt hU
  refine mem_subdifferential_iff_exists_seq.2 ⟨⟨f xτ, rfl⟩, xs, fun n ↦ gradient f (xs n), hxs,
    (continuous_coe_real_ereal.tendsto _).comp (hfc.tendsto.comp hxs), fun n ↦ ?_, hgrad⟩
  exact (mem_regularSubdifferential_iff_exists_hasGradientAt (f := fun y ↦ (f y : EReal))
    (c := f (xs n)) rfl).2 ⟨f, Eventually.of_forall fun _ ↦ le_rfl, rfl,
      (hdiff n).hasGradientAt⟩

end RW
