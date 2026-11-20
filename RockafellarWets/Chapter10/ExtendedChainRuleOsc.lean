/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: cosmic outer semicontinuity in the extended chain rule

**Theorem 10.49**, remaining clause: for `f = g ∘ F` with `g` lsc, `F` strictly continuous at `x̄`,
`f(x̄)` finite and the qualification that the only `y ∈ ∂^∞g(F(x̄))` with `0 ∈ ∂(yF)(x̄)` is
`y = 0`, the mapping `x ↦ C(x) ∪ dir K(x)` with `C(x) = ⋃ {∂(yF)(x) | y ∈ ∂g(F(x))}` and
`K(x) = ⋃ {∂(yF)(x) | y ∈ ∂^∞g(F(x))}` is cosmically osc at `x̄` for `f`-attentive convergence.
In sequential form, along `xᵛ →_f x̄`:

* `vᵛ ∈ C(xᵛ)`, `vᵛ → v` give `v ∈ C(x̄)` (`chainRuleEstimate_osc`);
* `vᵛ ∈ C(xᵛ)`, `tᵛ ↘ 0`, `tᵛvᵛ → v` give `v ∈ K(x̄)` (`chainRuleEstimate_horizon_osc`);
* `vᵛ ∈ K(xᵛ)`, `vᵛ → v` give `v ∈ K(x̄)` (`chainRuleHorizonEstimate_osc`); since each `K(x)`
  is a cone, this also covers directions of `K(xᵛ)`.

As in the book, multipliers `yᵛ` are normalized: bounded ones converge to multipliers at `x̄`
(8.7), unbounded ones would give a nonzero `y ∈ ∂^∞g(F(x̄))` with `0 ∈ ∂(yF)(x̄)`, using the
estimate `∂(y'F)(x) ⊂ ∂(yF)(x) + κ|y' - y|IB`.
-/

import RockafellarWets.Chapter10.LipschitzConstraintNormalsOsc
import RockafellarWets.Chapter10.ExtendedChainRule

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Normalization of an arbitrary sequence: along a subsequence `(1 + |yᵛ|)⁻¹yᵛ → z` and
`(1 + |yᵛ|)⁻¹ → τ`; if `τ > 0` then `yᵛ → τ⁻¹z`, and if `τ = 0` then `|z| = 1`. -/
theorem exists_normalized_subseq (ys : ℕ → F) :
    ∃ (φ : ℕ → ℕ) (z : F) (τ : ℝ), StrictMono φ ∧ 0 ≤ τ ∧
      Tendsto (fun n ↦ (1 + ‖ys (φ n)‖)⁻¹ • ys (φ n)) atTop (𝓝 z) ∧
      Tendsto (fun n ↦ (1 + ‖ys (φ n)‖)⁻¹) atTop (𝓝 τ) ∧
      (0 < τ → Tendsto (fun n ↦ ys (φ n)) atTop (𝓝 (τ⁻¹ • z))) ∧ (τ = 0 → ‖z‖ = 1) := by
  have hpos : ∀ n, 0 < 1 + ‖ys n‖ := fun n ↦ by positivity
  have hwK : ∀ n, ((1 + ‖ys n‖)⁻¹ • ys n, (1 + ‖ys n‖)⁻¹) ∈
      closedBall (0 : F) 1 ×ˢ Icc (0 : ℝ) 1 := fun n ↦ by
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
  refine ⟨φ, z, τ, hφ, hzτ.2.1, hzl, hτl, fun hτ ↦ ?_, fun hτ ↦ ?_⟩
  · have h := (hτl.inv₀ hτ.ne').smul hzl
    refine h.congr fun n ↦ ?_
    rw [inv_inv, smul_smul, mul_inv_cancel₀ (hpos _).ne', one_smul]
  · subst hτ
    have h1 : Tendsto (fun n ↦ ‖(1 + ‖ys (φ n)‖)⁻¹ • ys (φ n)‖) atTop (𝓝 (1 - 0)) := by
      refine (tendsto_const_nhds.sub hτl).congr fun n ↦ ?_
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (hpos _).le]
      have := hpos (φ n)
      field_simp
      ring
    rw [sub_zero] at h1
    exact tendsto_nhds_unique hzl.norm h1

omit [FiniteDimensional ℝ F] in
/-- Limits of `uᵛ ∈ ∂(yᵛF)(xᵛ)` with `xᵛ → x̄`, `yᵛ → y`, `uᵛ → u` satisfy `u ∈ ∂(yF)(x̄)` when `F`
is strictly continuous at `x̄`. -/
theorem mem_subdifferential_inner_of_tendsto₂ {G : E → F} {x : E} (hG : StrictlyContinuousAt G x)
    {xs us : ℕ → E} {ys : ℕ → F} {y : F} {u : E} (hxs : Tendsto xs atTop (𝓝 x))
    (hys : Tendsto ys atTop (𝓝 y))
    (hus : ∀ n, us n ∈ subdifferential (fun a ↦ ((⟪ys n, G a⟫_ℝ : ℝ) : EReal)) (xs n))
    (hul : Tendsto us atTop (𝓝 u)) :
    u ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨κ, U, hU, hGL⟩ := strictlyContinuousAt_iff.1 hG
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (isOpen_interior.mem_nhds
    (mem_interior_iff_mem_nhds.2 hU)))
  have hUn : ∀ n, U ∈ 𝓝 (xs (n + N)) := fun n ↦
    mem_interior_iff_mem_nhds.1 (hN (n + N) (Nat.le_add_left N n))
  have hnorm : ∀ w : F, ((‖innerSL ℝ w‖₊ : ℝ≥0) : ℝ) = ‖w‖ := fun w ↦ by
    rw [coe_nnnorm, innerSL_apply_norm]
  have happ : ∀ n, ∃ p ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) (xs (n + N)),
      ‖us (n + N) - p‖ ≤ ‖ys (n + N) - y‖ * κ := by
    intro n
    have hu := hus (n + N)
    have hfun : (fun a ↦ ((⟪ys (n + N), G a⟫_ℝ : ℝ) : EReal)) =
        fun a ↦ ((⟪y, G a⟫_ℝ + ⟪ys (n + N) - y, G a⟫_ℝ : ℝ) : EReal) := by
      funext a
      rw [inner_sub_left]
      congr 1
      ring
    rw [hfun] at hu
    obtain ⟨p, hp, hpd⟩ := exists_near_subgradient (hUn n)
      (strictlyContinuousAt_iff.2 ⟨_, U, hUn n, lipschitzOnWith_inner hGL y⟩)
      (lipschitzOnWith_inner hGL (ys (n + N) - y)) hu
    exact ⟨p, hp, hpd.trans (le_of_eq (by rw [NNReal.coe_mul, hnorm]))⟩
  choose ps hps hpd using happ
  have hpl : Tendsto ps atTop (𝓝 u) := by
    have hd : Tendsto (fun n ↦ ‖ys (n + N) - y‖ * κ) atTop (𝓝 0) := by
      have h := ((tendsto_iff_norm_sub_tendsto_zero.1 hys).comp (tendsto_add_atTop_nat N)).mul_const
        (κ : ℝ)
      rw [zero_mul] at h
      exact h
    have h1 : Tendsto (fun n ↦ us (n + N) - ps n) atTop (𝓝 0) := squeeze_zero_norm hpd hd
    have h2 := ((tendsto_add_atTop_iff_nat N).2 hul).sub h1
    simp only [sub_sub_cancel, sub_zero] at h2
    exact h2
  exact mem_subdifferential_inner_of_tendsto hG.continuousAt y
    ((tendsto_add_atTop_iff_nat N).2 hxs) hps hpl

section Osc

variable {g : F → EReal} {G : E → F} {x : E} {c : ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] in
theorem tendsto_attentiveNhds_comp (hG : StrictlyContinuousAt G x) {xs : ℕ → E}
    (hxs : Tendsto xs atTop (attentiveNhds (fun a ↦ g (G a)) x)) :
    Tendsto xs atTop (𝓝 x) ∧ Tendsto (fun n ↦ G (xs n)) atTop (attentiveNhds g (G x)) := by
  obtain ⟨hx1, hx2⟩ := tendsto_attentiveNhds_iff.1 hxs
  exact ⟨hx1, tendsto_attentiveNhds_iff.2 ⟨hG.continuousAt.tendsto.comp hx1, hx2⟩⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] in
theorem exists_shift_strictlyContinuousAt (hG : StrictlyContinuousAt G x) {xs : ℕ → E}
    (hx1 : Tendsto xs atTop (𝓝 x)) : ∃ N, ∀ n, StrictlyContinuousAt G (xs (n + N)) := by
  obtain ⟨κ, U, hU, hGL⟩ := strictlyContinuousAt_iff.1 hG
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hx1.eventually (isOpen_interior.mem_nhds
    (mem_interior_iff_mem_nhds.2 hU)))
  exact ⟨N, fun n ↦ strictlyContinuousAt_iff.2
    ⟨κ, U, mem_interior_iff_mem_nhds.1 (hN (n + N) (Nat.le_add_left N n)), hGL⟩⟩

theorem chainRuleEstimate_osc_core (hG : StrictlyContinuousAt G x) (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0)
    {xs vs : ℕ → E} {ys : ℕ → F} {v : E} (hx1 : Tendsto xs atTop (𝓝 x))
    (hGx : Tendsto (fun n ↦ G (xs n)) atTop (attentiveNhds g (G x)))
    (hscn : ∀ n, StrictlyContinuousAt G (xs n)) (hys : ∀ n, ys n ∈ subdifferential g (G (xs n)))
    (hvy : ∀ n, vs n ∈ subdifferential (fun a ↦ ((⟪ys n, G a⟫_ℝ : ℝ) : EReal)) (xs n))
    (hv : Tendsto vs atTop (𝓝 v)) :
    ∃ y ∈ subdifferential g (G x), v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨φ, z, τ, hφ, hτ0, hzl, hτl, hpc, hzc⟩ := exists_normalized_subseq ys
  have hxφ := hx1.comp hφ.tendsto_atTop
  have hGφ : Tendsto (fun n ↦ G (xs (φ n))) atTop (attentiveNhds g (G x)) :=
    hGx.comp hφ.tendsto_atTop
  have hvφ := hv.comp hφ.tendsto_atTop
  have hpos : ∀ n, 0 < 1 + ‖ys n‖ := fun n ↦ by positivity
  rcases hτ0.lt_or_eq with hτ | hτ
  · have hyl := hpc hτ
    refine ⟨τ⁻¹ • z, ?_, mem_subdifferential_inner_of_tendsto₂ hG hxφ hyl
      (fun n ↦ hvy (φ n)) hvφ⟩
    apply outerSetLimitAlong_subdifferential_subset hc
    exact mem_outerSetLimitAlong_iff_exists_seq.2 ⟨_, _, hGφ, fun n ↦ hys (φ n), hyl⟩
  · exfalso
    have hz1 := hzc hτ.symm
    rw [← hτ] at hτl
    have hzH : z ∈ horizonSubdifferential g (G x) :=
      mem_horizonSubdifferential_of_scaled_subgradients hc hGφ (fun n ↦ hys (φ n))
        (fun n ↦ inv_pos.2 (hpos _)) hτl hzl
    have hsv : ∀ n, (1 + ‖ys (φ n)‖)⁻¹ • vs (φ n) ∈ subdifferential
        (fun a ↦ ((⟪(1 + ‖ys (φ n)‖)⁻¹ • ys (φ n), G a⟫_ℝ : ℝ) : EReal)) (xs (φ n)) := fun n ↦ by
      rw [subdifferential_inner_smul (hscn _) _ (inv_pos.2 (hpos _))]
      exact smul_mem_smul_set (hvy (φ n))
    have h3 : Tendsto (fun n ↦ (1 + ‖ys (φ n)‖)⁻¹ • vs (φ n)) atTop (𝓝 0) := by
      simpa using hτl.smul hvφ
    have hz0 := hQ z hzH (mem_subdifferential_inner_of_tendsto₂ hG hxφ hzl hsv h3)
    rw [hz0, norm_zero] at hz1
    exact zero_ne_one hz1

/-- **Theorem 10.49**, cosmic osc, finite part: `xᵛ →_f x̄`, `vᵛ ∈ C(xᵛ)`, `vᵛ → v` give
`v ∈ C(x̄)`. -/
theorem chainRuleEstimate_osc (hG : StrictlyContinuousAt G x) (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0)
    {xs vs : ℕ → E} {v : E} (hxs : Tendsto xs atTop (attentiveNhds (fun a ↦ g (G a)) x))
    (hvs : ∀ n, ∃ y ∈ subdifferential g (G (xs n)),
      vs n ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) (xs n))
    (hv : Tendsto vs atTop (𝓝 v)) :
    ∃ y ∈ subdifferential g (G x), v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨hx1, hGx⟩ := tendsto_attentiveNhds_comp hG hxs
  obtain ⟨N, hscn⟩ := exists_shift_strictlyContinuousAt hG hx1
  choose ys hys hvy using hvs
  exact chainRuleEstimate_osc_core hG hc hQ ((tendsto_add_atTop_iff_nat N).2 hx1)
    ((tendsto_add_atTop_iff_nat N).2 hGx) hscn (fun n ↦ hys (n + N)) (fun n ↦ hvy (n + N))
    ((tendsto_add_atTop_iff_nat N).2 hv)

theorem chainRuleEstimate_horizon_osc_core (hG : StrictlyContinuousAt G x) (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0)
    {xs vs : ℕ → E} {ys : ℕ → F} {ts : ℕ → ℝ} {v : E} (hx1 : Tendsto xs atTop (𝓝 x))
    (hGx : Tendsto (fun n ↦ G (xs n)) atTop (attentiveNhds g (G x)))
    (hscn : ∀ n, StrictlyContinuousAt G (xs n)) (hys : ∀ n, ys n ∈ subdifferential g (G (xs n)))
    (hvy : ∀ n, vs n ∈ subdifferential (fun a ↦ ((⟪ys n, G a⟫_ℝ : ℝ) : EReal)) (xs n))
    (ht0 : ∀ n, 0 < ts n) (ht : Tendsto ts atTop (𝓝 0))
    (hv : Tendsto (fun n ↦ ts n • vs n) atTop (𝓝 v)) :
    ∃ y ∈ horizonSubdifferential g (G x),
      v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  have hsv0 : ∀ n, ts n • vs n ∈ subdifferential
      (fun a ↦ ((⟪ts n • ys n, G a⟫_ℝ : ℝ) : EReal)) (xs n) := fun n ↦ by
    rw [subdifferential_inner_smul (hscn _) _ (ht0 n)]
    exact smul_mem_smul_set (hvy n)
  obtain ⟨φ, z, τ, hφ, hτ0, hzl, hτl, hpc, hzc⟩ := exists_normalized_subseq (fun n ↦ ts n • ys n)
  have hxφ := hx1.comp hφ.tendsto_atTop
  have hGφ : Tendsto (fun n ↦ G (xs (φ n))) atTop (attentiveNhds g (G x)) :=
    hGx.comp hφ.tendsto_atTop
  have hvφ : Tendsto (fun n ↦ ts (φ n) • vs (φ n)) atTop (𝓝 v) := hv.comp hφ.tendsto_atTop
  have htφ : Tendsto (fun n ↦ ts (φ n)) atTop (𝓝 0) := ht.comp hφ.tendsto_atTop
  have hpos : ∀ n, 0 < 1 + ‖ts n • ys n‖ := fun n ↦ by positivity
  rcases hτ0.lt_or_eq with hτ | hτ
  · have hyl := hpc hτ
    refine ⟨τ⁻¹ • z, ?_, mem_subdifferential_inner_of_tendsto₂ hG hxφ hyl
      (fun n ↦ hsv0 (φ n)) hvφ⟩
    exact mem_horizonSubdifferential_of_scaled_subgradients hc hGφ (fun n ↦ hys (φ n))
      (fun n ↦ ht0 _) htφ hyl
  · exfalso
    have hz1 := hzc hτ.symm
    rw [← hτ] at hτl
    have hzH : z ∈ horizonSubdifferential g (G x) := by
      refine mem_horizonSubdifferential_of_scaled_subgradients hc hGφ (fun n ↦ hys (φ n))
        (ts := fun n ↦ (1 + ‖ts (φ n) • ys (φ n)‖)⁻¹ * ts (φ n))
        (fun n ↦ mul_pos (inv_pos.2 (hpos _)) (ht0 _)) (by simpa using hτl.mul htφ) ?_
      refine hzl.congr fun n ↦ ?_
      rw [smul_smul]
    have hsv : ∀ n, (1 + ‖ts (φ n) • ys (φ n)‖)⁻¹ • (ts (φ n) • vs (φ n)) ∈ subdifferential
        (fun a ↦ ((⟪(1 + ‖ts (φ n) • ys (φ n)‖)⁻¹ • (ts (φ n) • ys (φ n)), G a⟫_ℝ : ℝ) : EReal))
          (xs (φ n)) := fun n ↦ by
      rw [subdifferential_inner_smul (hscn _) _ (inv_pos.2 (hpos _))]
      exact smul_mem_smul_set (hsv0 (φ n))
    have h3 : Tendsto (fun n ↦ (1 + ‖ts (φ n) • ys (φ n)‖)⁻¹ • (ts (φ n) • vs (φ n))) atTop
        (𝓝 0) := by
      simpa using hτl.smul hvφ
    have hz0 := hQ z hzH (mem_subdifferential_inner_of_tendsto₂ hG hxφ hzl hsv h3)
    rw [hz0, norm_zero] at hz1
    exact zero_ne_one hz1

/-- **Theorem 10.49**, cosmic osc, direction part: `xᵛ →_f x̄`, `vᵛ ∈ C(xᵛ)`, `tᵛ ↘ 0`,
`tᵛvᵛ → v` give `v ∈ K(x̄)`. -/
theorem chainRuleEstimate_horizon_osc (hG : StrictlyContinuousAt G x) (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0)
    {xs vs : ℕ → E} {ts : ℕ → ℝ} {v : E}
    (hxs : Tendsto xs atTop (attentiveNhds (fun a ↦ g (G a)) x))
    (hvs : ∀ n, ∃ y ∈ subdifferential g (G (xs n)),
      vs n ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) (xs n))
    (ht0 : ∀ n, 0 < ts n) (ht : Tendsto ts atTop (𝓝 0))
    (hv : Tendsto (fun n ↦ ts n • vs n) atTop (𝓝 v)) :
    ∃ y ∈ horizonSubdifferential g (G x),
      v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨hx1, hGx⟩ := tendsto_attentiveNhds_comp hG hxs
  obtain ⟨N, hscn⟩ := exists_shift_strictlyContinuousAt hG hx1
  choose ys hys hvy using hvs
  exact chainRuleEstimate_horizon_osc_core hG hc hQ ((tendsto_add_atTop_iff_nat N).2 hx1)
    ((tendsto_add_atTop_iff_nat N).2 hGx) hscn (fun n ↦ hys (n + N)) (fun n ↦ hvy (n + N))
    (fun n ↦ ht0 (n + N)) ((tendsto_add_atTop_iff_nat N).2 ht)
    ((tendsto_add_atTop_iff_nat N).2 hv)

theorem chainRuleHorizonEstimate_osc_core (hG : StrictlyContinuousAt G x) (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0)
    {xs vs : ℕ → E} {ys : ℕ → F} {v : E} (hx1 : Tendsto xs atTop (𝓝 x))
    (hGx : Tendsto (fun n ↦ G (xs n)) atTop (attentiveNhds g (G x)))
    (hscn : ∀ n, StrictlyContinuousAt G (xs n))
    (hys : ∀ n, ys n ∈ horizonSubdifferential g (G (xs n)))
    (hvy : ∀ n, vs n ∈ subdifferential (fun a ↦ ((⟪ys n, G a⟫_ℝ : ℝ) : EReal)) (xs n))
    (hv : Tendsto vs atTop (𝓝 v)) :
    ∃ y ∈ horizonSubdifferential g (G x),
      v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨φ, z, τ, hφ, hτ0, hzl, hτl, hpc, hzc⟩ := exists_normalized_subseq ys
  have hxφ := hx1.comp hφ.tendsto_atTop
  have hGφ : Tendsto (fun n ↦ G (xs (φ n))) atTop (attentiveNhds g (G x)) :=
    hGx.comp hφ.tendsto_atTop
  have hvφ := hv.comp hφ.tendsto_atTop
  have hpos : ∀ n, 0 < 1 + ‖ys n‖ := fun n ↦ by positivity
  have hcone : ∀ n, (1 + ‖ys n‖)⁻¹ • ys n ∈ horizonSubdifferential g (G (xs n)) := fun n ↦ by
    obtain ⟨cn, hcn⟩ := (hys n).1
    exact (subdifferential_properties hcn).2.2.2.2.1.2 (hys n) (inv_pos.2 (hpos n))
  rcases hτ0.lt_or_eq with hτ | hτ
  · have hyl := hpc hτ
    refine ⟨τ⁻¹ • z, ?_, mem_subdifferential_inner_of_tendsto₂ hG hxφ hyl
      (fun n ↦ hvy (φ n)) hvφ⟩
    apply outerSetLimitAlong_horizonSubdifferential_subset hc
    exact mem_outerSetLimitAlong_iff_exists_seq.2 ⟨_, _, hGφ, fun n ↦ hys (φ n), hyl⟩
  · exfalso
    have hz1 := hzc hτ.symm
    rw [← hτ] at hτl
    have hzH : z ∈ horizonSubdifferential g (G x) := by
      apply outerSetLimitAlong_horizonSubdifferential_subset hc
      exact mem_outerSetLimitAlong_iff_exists_seq.2 ⟨_, _, hGφ, fun n ↦ hcone (φ n), hzl⟩
    have hsv : ∀ n, (1 + ‖ys (φ n)‖)⁻¹ • vs (φ n) ∈ subdifferential
        (fun a ↦ ((⟪(1 + ‖ys (φ n)‖)⁻¹ • ys (φ n), G a⟫_ℝ : ℝ) : EReal)) (xs (φ n)) := fun n ↦ by
      rw [subdifferential_inner_smul (hscn _) _ (inv_pos.2 (hpos _))]
      exact smul_mem_smul_set (hvy (φ n))
    have h3 : Tendsto (fun n ↦ (1 + ‖ys (φ n)‖)⁻¹ • vs (φ n)) atTop (𝓝 0) := by
      simpa using hτl.smul hvφ
    have hz0 := hQ z hzH (mem_subdifferential_inner_of_tendsto₂ hG hxφ hzl hsv h3)
    rw [hz0, norm_zero] at hz1
    exact zero_ne_one hz1

/-- **Theorem 10.49**, cosmic osc, horizon part: `xᵛ →_f x̄`, `vᵛ ∈ K(xᵛ)`, `vᵛ → v` give
`v ∈ K(x̄)`. -/
theorem chainRuleHorizonEstimate_osc (hG : StrictlyContinuousAt G x) (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0)
    {xs vs : ℕ → E} {v : E} (hxs : Tendsto xs atTop (attentiveNhds (fun a ↦ g (G a)) x))
    (hvs : ∀ n, ∃ y ∈ horizonSubdifferential g (G (xs n)),
      vs n ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) (xs n))
    (hv : Tendsto vs atTop (𝓝 v)) :
    ∃ y ∈ horizonSubdifferential g (G x),
      v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨hx1, hGx⟩ := tendsto_attentiveNhds_comp hG hxs
  obtain ⟨N, hscn⟩ := exists_shift_strictlyContinuousAt hG hx1
  choose ys hys hvy using hvs
  exact chainRuleHorizonEstimate_osc_core hG hc hQ ((tendsto_add_atTop_iff_nat N).2 hx1)
    ((tendsto_add_atTop_iff_nat N).2 hGx) hscn (fun n ↦ hys (n + N)) (fun n ↦ hvy (n + N))
    ((tendsto_add_atTop_iff_nat N).2 hv)

end Osc

end RW
