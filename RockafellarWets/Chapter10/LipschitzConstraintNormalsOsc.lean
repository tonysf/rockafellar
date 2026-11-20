/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: outer semicontinuity of the normal estimate for Lipschitzian constraints

**Corollary 10.50**, remaining clause: for `C = F⁻¹(D)` with `F` strictly continuous at `x̄ ∈ C`,
under the qualification that the only `y ∈ N_D(F(x̄))` with `0 ∈ ∂(yF)(x̄)` is `y = 0`, the mapping
`x ↦ K(x) = ⋃ {∂(yF)(x) | y ∈ N_D(F(x))}` is outer semicontinuous at `x̄`
(`constraintNormalEstimate_osc`, stated with sequences).  Bounded multipliers pass to the limit
by 6.6 and the estimate `∂(y'F)(x) ⊂ ∂(yF)(x) + κ|y' - y|IB`; unbounded ones, after
normalization, would give `y ≠ 0` violating the qualification.
-/

import RockafellarWets.Chapter10.NonsmoothMultiplierCompactness

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The normal estimate `K(x) = ⋃ {∂(yF)(x) | y ∈ N_D(F(x))}` of **Corollary 10.50**. -/
def constraintNormalEstimate (D : Set F) (G : E → F) (x : E) : Set E :=
  {u | ∃ y ∈ normalCone D (G x), u ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Subgradients of scalarizations are closed under limits `xᵛ → x̄` when `F` is continuous at
`x̄`. -/
theorem mem_subdifferential_inner_of_tendsto {G : E → F} {x : E} (hG : ContinuousAt G x) (y : F)
    {xs ps : ℕ → E} {p : E} (hxs : Tendsto xs atTop (𝓝 x))
    (hps : ∀ n, ps n ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) (xs n))
    (hpl : Tendsto ps atTop (𝓝 p)) :
    p ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  apply outerSetLimitAlong_subdifferential_subset (f := fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal))
    (x := x) (c := ⟪y, G x⟫_ℝ) rfl
  refine mem_outerSetLimitAlong_iff_exists_seq.2 ⟨xs, ps, ?_, hps, hpl⟩
  refine tendsto_attentiveNhds_iff.2 ⟨hxs, ?_⟩
  have hc : ContinuousAt (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x :=
    continuous_coe_real_ereal.continuousAt.comp (continuousAt_const.inner hG)
  exact hc.tendsto.comp hxs

/-- **Corollary 10.50**: under the qualification, `x ↦ K(x)` is outer semicontinuous at `x̄`:
`xᵛ → x̄`, `vᵛ ∈ K(xᵛ)`, `vᵛ → v` imply `v ∈ K(x̄)`. -/
theorem constraintNormalEstimate_osc {D : Set F} {G : E → F} {x : E}
    (hG : StrictlyContinuousAt G x) (hx : G x ∈ D)
    (hQ : ∀ y ∈ normalCone D (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0)
    {xs vs : ℕ → E} {v : E} (hxs : Tendsto xs atTop (𝓝 x))
    (hvs : ∀ n, vs n ∈ constraintNormalEstimate D G (xs n)) (hv : Tendsto vs atTop (𝓝 v)) :
    v ∈ constraintNormalEstimate D G x := by
  obtain ⟨κ, U, hU, hGL⟩ := strictlyContinuousAt_iff.1 hG
  have hGc : ContinuousAt G x := hG.continuousAt
  -- shift the sequences into the interior of `U`
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (isOpen_interior.mem_nhds
    (mem_interior_iff_mem_nhds.2 hU)))
  set xs' : ℕ → E := fun n ↦ xs (n + N)
  set vs' : ℕ → E := fun n ↦ vs (n + N)
  have hxs' : Tendsto xs' atTop (𝓝 x) := (tendsto_add_atTop_iff_nat N).2 hxs
  have hv' : Tendsto vs' atTop (𝓝 v) := (tendsto_add_atTop_iff_nat N).2 hv
  have hUn : ∀ n, U ∈ 𝓝 (xs' n) := fun n ↦
    mem_interior_iff_mem_nhds.1 (hN (n + N) (Nat.le_add_left N n))
  have hscn : ∀ n, StrictlyContinuousAt G (xs' n) := fun n ↦
    strictlyContinuousAt_iff.2 ⟨κ, U, hUn n, hGL⟩
  have hsci : ∀ (y : F) n, StrictlyContinuousAt (fun a ↦ ⟪y, G a⟫_ℝ) (xs' n) := fun y n ↦
    strictlyContinuousAt_iff.2 ⟨_, U, hUn n, lipschitzOnWith_inner hGL y⟩
  choose ys hys hvy using fun n ↦ hvs (n + N)
  have hnorm : ∀ w : F, ((‖innerSL ℝ w‖₊ : ℝ≥0) : ℝ) = ‖w‖ := fun w ↦ by
    rw [coe_nnnorm, innerSL_apply_norm]
  have hGD : ∀ n, G (xs' n) ∈ D := fun n ↦ (hys n).1
  -- the estimate `∂(y'F) ⊂ ∂(yF) + κ|y' - y|IB` at the points `xᵛ`
  have happ : ∀ (y : F) n (y' : F) (u : E),
      u ∈ subdifferential (fun a ↦ ((⟪y', G a⟫_ℝ : ℝ) : EReal)) (xs' n) →
      ∃ p ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) (xs' n),
        ‖u - p‖ ≤ ‖y' - y‖ * κ := by
    intro y n y' u hu
    have hfun : (fun a ↦ ((⟪y', G a⟫_ℝ : ℝ) : EReal)) =
        fun a ↦ ((⟪y, G a⟫_ℝ + ⟪y' - y, G a⟫_ℝ : ℝ) : EReal) := by
      funext a
      rw [inner_sub_left]
      congr 1
      ring
    rw [hfun] at hu
    obtain ⟨p, hp, hpd⟩ := exists_near_subgradient (hUn n) (hsci y n)
      (lipschitzOnWith_inner hGL (y' - y)) hu
    refine ⟨p, hp, hpd.trans (le_of_eq ?_)⟩
    rw [NNReal.coe_mul, hnorm]
  -- compactness of the normalized multipliers
  set w : ℕ → F × ℝ := fun n ↦ ((1 + ‖ys n‖)⁻¹ • ys n, (1 + ‖ys n‖)⁻¹) with hw
  have hpos : ∀ n, 0 < 1 + ‖ys n‖ := fun n ↦ by positivity
  have hwK : ∀ n, w n ∈ closedBall (0 : F) 1 ×ˢ Icc (0 : ℝ) 1 := fun n ↦ by
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (hpos n).le,
        inv_mul_le_iff₀ (hpos n)]
      linarith
    · exact (inv_pos.2 (hpos n)).le
    · exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (ys n)])
  obtain ⟨⟨z, τ⟩, hzτ, φ, hφ, hwl⟩ :=
    ((isCompact_closedBall (0 : F) 1).prod isCompact_Icc).tendsto_subseq hwK
  have hzl : Tendsto (fun n ↦ (1 + ‖ys (φ n)‖)⁻¹ • ys (φ n)) atTop (𝓝 z) :=
    (continuous_fst.tendsto _).comp hwl
  have hτl : Tendsto (fun n ↦ (1 + ‖ys (φ n)‖)⁻¹) atTop (𝓝 τ) :=
    (continuous_snd.tendsto _).comp hwl
  have hxφ : Tendsto (fun n ↦ xs' (φ n)) atTop (𝓝 x) := hxs'.comp hφ.tendsto_atTop
  have hvφ : Tendsto (fun n ↦ vs' (φ n)) atTop (𝓝 v) := hv'.comp hφ.tendsto_atTop
  have hGφ : Tendsto (fun n ↦ G (xs' (φ n))) atTop (𝓝 (G x)) := hGc.tendsto.comp hxφ
  rcases (hzτ.2.1 : (0 : ℝ) ≤ τ).lt_or_eq with hτ | hτ
  · -- bounded multipliers
    have hyl : Tendsto (fun n ↦ ys (φ n)) atTop (𝓝 (τ⁻¹ • z)) := by
      have h := (hτl.inv₀ hτ.ne').smul hzl
      refine h.congr fun n ↦ ?_
      rw [inv_inv, smul_smul, mul_inv_cancel₀ (hpos _).ne', one_smul]
    have hyD : τ⁻¹ • z ∈ normalCone D (G x) :=
      mem_normalCone_of_tendsto hx (fun n ↦ hGD (φ n)) hGφ (fun n ↦ hys (φ n)) hyl
    choose ps hps hpd using fun n ↦ happ (τ⁻¹ • z) (φ n) (ys (φ n)) (vs' (φ n)) (hvy (φ n))
    have hpl : Tendsto ps atTop (𝓝 v) := by
      have hd : Tendsto (fun n ↦ ‖ys (φ n) - τ⁻¹ • z‖ * κ) atTop (𝓝 0) := by
        have h := (tendsto_iff_norm_sub_tendsto_zero.1 hyl).mul_const (κ : ℝ)
        rwa [zero_mul] at h
      have h1 : Tendsto (fun n ↦ vs' (φ n) - ps n) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n ↦ hpd n) hd
      have h2 := hvφ.sub h1
      simp only [sub_sub_cancel, sub_zero] at h2
      exact h2
    exact ⟨τ⁻¹ • z, hyD, mem_subdifferential_inner_of_tendsto hGc _ hxφ hps hpl⟩
  · -- unbounded multipliers contradict the qualification
    subst hτ
    have hz1 : ‖z‖ = 1 := by
      have h1 : Tendsto (fun n ↦ ‖(1 + ‖ys (φ n)‖)⁻¹ • ys (φ n)‖) atTop (𝓝 (1 - 0)) := by
        refine (tendsto_const_nhds.sub hτl).congr fun n ↦ ?_
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (hpos _).le]
        field_simp
        ring
      rw [sub_zero] at h1
      exact tendsto_nhds_unique hzl.norm h1
    have hzD : z ∈ normalCone D (G x) :=
      mem_normalCone_of_tendsto hx (fun n ↦ hGD (φ n)) hGφ
        (fun n ↦ (isCone_normalCone (hGD (φ n))).2 (hys (φ n)) (inv_pos.2 (hpos _))) hzl
    have hsv : ∀ n, (1 + ‖ys (φ n)‖)⁻¹ • vs' (φ n) ∈
        subdifferential (fun a ↦ ((⟪(1 + ‖ys (φ n)‖)⁻¹ • ys (φ n), G a⟫_ℝ : ℝ) : EReal))
          (xs' (φ n)) := fun n ↦ by
      rw [subdifferential_inner_smul (hscn _) _ (inv_pos.2 (hpos _))]
      exact smul_mem_smul_set (hvy (φ n))
    choose ps hps hpd using fun n ↦ happ z (φ n) _ _ (hsv n)
    have hpl : Tendsto ps atTop (𝓝 0) := by
      have hd : Tendsto (fun n ↦ ‖(1 + ‖ys (φ n)‖)⁻¹ • ys (φ n) - z‖ * κ) atTop (𝓝 0) := by
        have h := (tendsto_iff_norm_sub_tendsto_zero.1 hzl).mul_const (κ : ℝ)
        rwa [zero_mul] at h
      have h1 : Tendsto (fun n ↦ (1 + ‖ys (φ n)‖)⁻¹ • vs' (φ n) - ps n) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n ↦ hpd n) hd
      have h3 : Tendsto (fun n ↦ (1 + ‖ys (φ n)‖)⁻¹ • vs' (φ n)) atTop (𝓝 0) := by
        simpa using hτl.smul hvφ
      have h2 := h3.sub h1
      simp only [sub_sub_cancel, sub_zero] at h2
      exact h2
    have h0 := mem_subdifferential_inner_of_tendsto hGc z hxφ hps hpl
    have hz0 := hQ z hzD h0
    rw [hz0, norm_zero] at hz1
    exact absurd hz1 zero_ne_one

end RW
