/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: compactness of nonsmooth Lagrange multipliers

**Exercise 10.52**, final assertion: under the constraint qualification
`0 ∈ ∂(yF)(x̄) + N_X(x̄), y ∈ N_D(F(x̄)) ⟹ y = 0`, the set of multipliers
`{ȳ ∈ ∂θ(F(x̄)) | 0 ∈ ∂(f₀ + ȳF)(x̄) + N_X(x̄)}` is compact
(`isCompact_nonsmooth_multipliers`).  The book derives this from the cosmic outer semicontinuity
in 10.49; the proof here is the direct version of that argument at the single point `x̄`:
closedness from the estimate `∂(f₀ + y'F)(x̄) ⊂ ∂(f₀ + yF)(x̄) + κ|y' - y|IB` (sum rule 10.9 for
functions strictly continuous at `x̄`, `subdifferential_add_subset_of_strictlyContinuousAt`, and
the Lipschitz bound 9.13), and boundedness because a normalized unbounded sequence of multipliers
would produce `y ∈ N_D(F(x̄))`, `|y| = 1`, with `0 ∈ ∂(yF)(x̄) + N_X(x̄)` (8.7, 8.12).
-/

import RockafellarWets.Chapter10.NonsmoothMultipliers
import RockafellarWets.Chapter10.EpsilonRegularSubgradients
import RockafellarWets.Chapter9.LipschitzSubgradientLimits

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem lipschitzOnWith_inner {G : E → F} {k : ℝ≥0} {U : Set E} (hL : LipschitzOnWith k G U)
    (w : F) : LipschitzOnWith (‖innerSL ℝ w‖₊ * k) (fun a ↦ ⟪w, G a⟫_ℝ) U :=
  (innerSL ℝ w).lipschitz.comp_lipschitzOnWith hL

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A subgradient of a function `k`-Lipschitz on a neighborhood has norm at most `k` (9.13). -/
theorem norm_le_of_mem_subdifferential_of_lipschitzOnWith_nhds {h : E → ℝ} {x v : E} {k : ℝ≥0}
    {U : Set E} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith k h U)
    (hv : v ∈ subdifferential (fun a ↦ ((h a : ℝ) : EReal)) x) : ‖v‖ ≤ k :=
  norm_le_of_mem_subdifferential_of_lipschitzOnWith isOpen_interior
    (fun _ _ ↦ by rw [EReal.toReal_coe])
    (by simpa only [EReal.toReal_coe] using hL.mono interior_subset)
    (mem_interior_iff_mem_nhds.2 hU) hv

omit [FiniteDimensional ℝ F] in
/-- **Corollary 10.9** for two real functions strictly continuous at `x̄`. -/
theorem subdifferential_add_subset_of_strictlyContinuousAt {h₁ h₂ : E → ℝ} {x : E}
    (hc₁ : StrictlyContinuousAt h₁ x) (hc₂ : StrictlyContinuousAt h₂ x) :
    subdifferential (fun a ↦ ((h₁ a + h₂ a : ℝ) : EReal)) x ⊆
      subdifferential (fun a ↦ ((h₁ a : ℝ) : EReal)) x +
        subdifferential (fun a ↦ ((h₂ a : ℝ) : EReal)) x := by
  obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 hc₂
  obtain ⟨H, hHL, hHeq⟩ := hL.extend_real
  have he : (fun a ↦ ((h₂ a : ℝ) : EReal)) =ᶠ[𝓝 x] fun a ↦ ((H a : ℝ) : EReal) :=
    Filter.mem_of_superset hU fun a ha ↦ by
      show ((h₂ a : ℝ) : EReal) = ((H a : ℝ) : EReal)
      rw [hHeq ha]
  have he' : (fun a ↦ ((h₁ a + h₂ a : ℝ) : EReal)) =ᶠ[𝓝 x]
      ((fun a ↦ ((h₁ a : ℝ) : EReal)) + fun a ↦ ((H a : ℝ) : EReal)) :=
    Filter.mem_of_superset hU fun a ha ↦ by
      show ((h₁ a + h₂ a : ℝ) : EReal) = ((h₁ a : ℝ) : EReal) + ((H a : ℝ) : EReal)
      rw [hHeq ha, EReal.coe_add]
  have hE₁ : ERealStrictlyContinuousAt (fun a ↦ ((h₁ a : ℝ) : EReal)) x := by
    have h := hc₁.eRealStrictlyContinuousAt_inner (1 : ℝ)
    simpa only [real_inner_one_left'] using h
  rw [subdifferential_congr_nhds_of_finite (f := fun a ↦ ((h₁ a + h₂ a : ℝ) : EReal))
      (c := h₁ x + h₂ x) rfl he',
    subdifferential_congr_nhds_of_finite (f := fun a ↦ ((h₂ a : ℝ) : EReal)) (c := h₂ x) rfl he]
  exact subdifferential_add_subset_of_strictlyContinuous (c := H x) hE₁
    (continuous_coe_real_ereal.comp hHL.continuous).lowerSemicontinuous
    ⟨⟨x, EReal.coe_lt_top _⟩, fun a ↦ EReal.bot_lt_coe _⟩ rfl

omit [FiniteDimensional ℝ F] in
/-- Subgradients of `h₁ + h₂` lie within `L` of those of `h₁` when `h₂` is `L`-Lipschitz near
`x̄`. -/
theorem exists_near_subgradient {h₁ h₂ : E → ℝ} {x u : E} {L : ℝ≥0} {U : Set E} (hU : U ∈ 𝓝 x)
    (hc₁ : StrictlyContinuousAt h₁ x) (hL : LipschitzOnWith L h₂ U)
    (hu : u ∈ subdifferential (fun a ↦ ((h₁ a + h₂ a : ℝ) : EReal)) x) :
    ∃ p ∈ subdifferential (fun a ↦ ((h₁ a : ℝ) : EReal)) x, ‖u - p‖ ≤ L := by
  have hc₂ : StrictlyContinuousAt h₂ x := strictlyContinuousAt_iff.2 ⟨L, U, hU, hL⟩
  obtain ⟨p, hp, e, he, rfl⟩ := subdifferential_add_subset_of_strictlyContinuousAt hc₁ hc₂ hu
  exact ⟨p, hp, by
    rw [add_sub_cancel_left]
    exact norm_le_of_mem_subdifferential_of_lipschitzOnWith_nhds hU hL he⟩

omit [FiniteDimensional ℝ F] in
theorem isCompact_subdifferential_of_strictlyContinuousAt {h : E → ℝ} {x : E}
    (hh : StrictlyContinuousAt h x) : IsCompact (subdifferential (fun a ↦ ((h a : ℝ) : EReal)) x) := by
  have h' := hh.eRealStrictlyContinuousAt_inner (1 : ℝ)
  simp only [real_inner_one_left'] at h'
  exact h'.subdifferential_nonempty_compact.2

/-- Limits of positive multiples `tᵛvᵛ`, `tᵛ ↘ 0`, of subgradients `vᵛ ∈ ∂f(xᵛ)` along
`xᵛ →_f x̄` are horizon subgradients (8.7). -/
theorem mem_horizonSubdifferential_of_scaled_subgradients {f : E → EReal} {x v : E} {c : ℝ}
    (hx : f x = c) {xs : ℕ → E} {ws : ℕ → E} {ts : ℕ → ℝ}
    (hxs : Tendsto xs atTop (attentiveNhds f x)) (hws : ∀ n, ws n ∈ subdifferential f (xs n))
    (ht0 : ∀ n, 0 < ts n) (ht : Tendsto ts atTop (𝓝 0))
    (hwl : Tendsto (fun n ↦ ts n • ws n) atTop (𝓝 v)) : v ∈ horizonSubdifferential f x := by
  have hmem : v ∈ horizonOuterSetLimitAlong (attentiveNhds f x) (subdifferential f) :=
    mem_horizonOuterSetLimitAlong_iff_zero_or_scaledSeq.2
      (Or.inr ⟨xs, ws, ts, hxs, hws, ht0, ht, hwl⟩)
  have hK : IsCone (horizonSubdifferential f x) := (subdifferential_properties hx).2.2.2.2.1
  rw [← cosmicDirectionCone_cosmicSet (C := subdifferential f x) hK]
  refine cosmicDirectionCone_mono ?_ hmem
  refine (outerSetLimitAlong_mono fun y ↦ ?_).trans (outerSetLimitAlong_cosmicSubdifferential_subset hx)
  show cosmicSet (subdifferential f y) {0} ⊆
    cosmicSet (subdifferential f y) (horizonSubdifferential f y)
  simp only [cosmicSet, cosmicDirections_zero, union_empty]
  exact subset_union_left

/-- **Exercise 10.52**, compactness: under the constraint qualification, the set of multipliers
`{ȳ ∈ ∂θ(F(x̄)) | 0 ∈ ∂(f₀ + ȳF)(x̄) + N_X(x̄)}` is compact. -/
theorem isCompact_nonsmooth_multipliers {X : Set E} {f₀ : E → ℝ} {G : E → F} {θ : F → EReal}
    {x : E} {c : ℝ} (hf₀ : StrictlyContinuousAt f₀ x) (hG : StrictlyContinuousAt G x)
    (hθp : IsProper θ) (hθc : Convex ℝ (epigraph θ)) (hxX : x ∈ X) (hc : θ (G x) = c)
    (hQ : ∀ y ∈ normalCone (effectiveDomain θ) (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x + normalCone X x →
        y = 0) :
    IsCompact {y | y ∈ subdifferential θ (G x) ∧
      (0 : E) ∈ subdifferential (fun a ↦ ((f₀ a + ⟪y, G a⟫_ℝ : ℝ) : EReal)) x +
        normalCone X x} := by
  set M := {y | y ∈ subdifferential θ (G x) ∧
      (0 : E) ∈ subdifferential (fun a ↦ ((f₀ a + ⟪y, G a⟫_ℝ : ℝ) : EReal)) x +
        normalCone X x} with hM
  obtain ⟨κ, U, hU, hGL⟩ := strictlyContinuousAt_iff.1 hG
  obtain ⟨κ₀, U₀, hU₀, hfL⟩ := strictlyContinuousAt_iff.1 hf₀
  have hNX : IsClosed (normalCone X x) := isClosed_normalCone X x
  have hcone := isCone_normalCone hxX
  have hsc : ∀ y : F, StrictlyContinuousAt (fun a ↦ ⟪y, G a⟫_ℝ) x := fun y ↦
    strictlyContinuousAt_iff.2 ⟨_, U, hU, lipschitzOnWith_inner hGL y⟩
  have hsc0 : ∀ y : F, StrictlyContinuousAt (fun a ↦ f₀ a + ⟪y, G a⟫_ℝ) x := fun y ↦
    strictlyContinuousAt_iff.2 ⟨_, U₀ ∩ U, inter_mem hU₀ hU,
      (hfL.mono inter_subset_left).add ((lipschitzOnWith_inner hGL y).mono inter_subset_right)⟩
  have hsplit : ∀ y ∈ M, ∃ u ∈ subdifferential (fun a ↦ ((f₀ a + ⟪y, G a⟫_ℝ : ℝ) : EReal)) x,
      -u ∈ normalCone X x := by
    rintro y ⟨-, u, hu, w, hw, huw⟩
    refine ⟨u, hu, ?_⟩
    rw [neg_eq_of_add_eq_zero_right huw]
    exact hw
  have hnorm : ∀ w : F, ((‖innerSL ℝ w‖₊ : ℝ≥0) : ℝ) = ‖w‖ := fun w ↦ by
    rw [coe_nnnorm, innerSL_apply_norm]
  -- closedness
  have hclosed : IsClosed M := by
    refine IsSeqClosed.isClosed fun ys y hys hy ↦ ?_
    refine ⟨(subdifferential_properties hc).2.2.1.mem_of_tendsto hy
      (Eventually.of_forall fun n ↦ (hys n).1), ?_⟩
    choose us hus hun using fun n ↦ hsplit (ys n) (hys n)
    have happ : ∀ n, ∃ p ∈ subdifferential (fun a ↦ ((f₀ a + ⟪y, G a⟫_ℝ : ℝ) : EReal)) x,
        ‖us n - p‖ ≤ ‖innerSL ℝ (ys n - y)‖₊ * κ := by
      intro n
      have h := hus n
      have hfun : (fun a ↦ ((f₀ a + ⟪ys n, G a⟫_ℝ : ℝ) : EReal)) =
          fun a ↦ (((f₀ a + ⟪y, G a⟫_ℝ) + ⟪ys n - y, G a⟫_ℝ : ℝ) : EReal) := by
        funext a
        rw [inner_sub_left]
        congr 1
        ring
      rw [hfun] at h
      exact exists_near_subgradient hU (hsc0 y) (lipschitzOnWith_inner hGL (ys n - y)) h
    choose ps hps hpd using happ
    obtain ⟨p, hp, φ, hφ, hpl⟩ :=
      (isCompact_subdifferential_of_strictlyContinuousAt (hsc0 y)).tendsto_subseq hps
    have hd : Tendsto (fun n ↦ ((‖innerSL ℝ (ys n - y)‖₊ * κ : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_iff_norm_sub_tendsto_zero.1 hy).mul_const (κ : ℝ)
      rw [zero_mul] at h
      refine h.congr fun n ↦ ?_
      rw [NNReal.coe_mul, hnorm]
    have hul : Tendsto (fun n ↦ us (φ n)) atTop (𝓝 p) := by
      have h1 : Tendsto (fun n ↦ us (φ n) - ps (φ n)) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n ↦ hpd (φ n)) (hd.comp hφ.tendsto_atTop)
      have h2 := hpl.add h1
      simp only [Function.comp_apply, add_sub_cancel, add_zero] at h2
      exact h2
    have hmem : -p ∈ normalCone X x :=
      hNX.mem_of_tendsto hul.neg (Eventually.of_forall fun n ↦ hun (φ n))
    exact ⟨p, hp, -p, hmem, add_neg_cancel p⟩
  -- boundedness
  have hbdd : Bornology.IsBounded M := by
    by_contra hb
    have hex : ∀ n : ℕ, ∃ y ∈ M, (n : ℝ) < ‖y‖ := by
      intro n
      by_contra hn
      push_neg at hn
      exact hb (isBounded_iff_forall_norm_le.2 ⟨n, hn⟩)
    choose ys hys hyn using hex
    have hpos : ∀ n, 0 < ‖ys n‖ := fun n ↦ lt_of_le_of_lt (Nat.cast_nonneg n) (hyn n)
    have hzs : ∀ n, ‖ys n‖⁻¹ • ys n ∈ sphere (0 : F) 1 := fun n ↦ by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hpos n).ne']
    obtain ⟨z, hz, φ, hφ, hzl⟩ := (isCompact_sphere (0 : F) 1).tendsto_subseq hzs
    have hts : Tendsto (fun n ↦ ‖ys (φ n)‖⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n ↦ ‖ys (φ n)‖) atTop atTop :=
        tendsto_atTop_mono (fun n ↦ le_trans (Nat.cast_le.2 (hφ.id_le n)) (hyn (φ n)).le)
          tendsto_natCast_atTop_atTop
      exact tendsto_inv_atTop_zero.comp h1
    have hzD : z ∈ normalCone (effectiveDomain θ) (G x) := by
      apply horizonSubdifferential_subset_normalCone_domain hθc hθp hc
      exact mem_horizonSubdifferential_of_scaled_subgradients hc (xs := fun _ ↦ G x)
        (ws := fun n ↦ ys (φ n)) (ts := fun n ↦ ‖ys (φ n)‖⁻¹)
        (tendsto_attentiveNhds_iff.2 ⟨tendsto_const_nhds, tendsto_const_nhds⟩)
        (fun n ↦ (hys (φ n)).1) (fun n ↦ inv_pos.2 (hpos _)) hts hzl
    choose us hus hun using fun n ↦ hsplit (ys n) (hys n)
    have hscaled : ∀ n, ∃ p ∈ subdifferential (fun a ↦ ((⟪z, G a⟫_ℝ : ℝ) : EReal)) x,
        ‖‖ys (φ n)‖⁻¹ • us (φ n) - p‖ ≤
          ‖innerSL ℝ ‖ys (φ n)‖⁻¹‖₊ * κ₀ + ‖innerSL ℝ (‖ys (φ n)‖⁻¹ • ys (φ n) - z)‖₊ * κ := by
      intro n
      have ht : 0 < ‖ys (φ n)‖⁻¹ := inv_pos.2 (hpos _)
      have h1 : ‖ys (φ n)‖⁻¹ • us (φ n) ∈ subdifferential
          (fun a ↦ ((‖ys (φ n)‖⁻¹ * (f₀ a + ⟪ys (φ n), G a⟫_ℝ) : ℝ) : EReal)) x := by
        rw [subdifferential_const_mul (hsc0 _) ht]
        exact smul_mem_smul_set (hus _)
      have hfun : (fun a ↦ ((‖ys (φ n)‖⁻¹ * (f₀ a + ⟪ys (φ n), G a⟫_ℝ) : ℝ) : EReal)) =
          fun a ↦ ((⟪z, G a⟫_ℝ + (⟪‖ys (φ n)‖⁻¹, f₀ a⟫_ℝ +
            ⟪‖ys (φ n)‖⁻¹ • ys (φ n) - z, G a⟫_ℝ) : ℝ) : EReal) := by
        funext a
        rw [inner_sub_left, real_inner_smul_left, real_inner_eq_mul']
        congr 1
        ring
      rw [hfun] at h1
      exact exists_near_subgradient (inter_mem hU₀ hU) (hsc z)
        (((lipschitzOnWith_inner hfL ‖ys (φ n)‖⁻¹).mono inter_subset_left).add
          ((lipschitzOnWith_inner hGL (‖ys (φ n)‖⁻¹ • ys (φ n) - z)).mono inter_subset_right)) h1
    choose ps hps hpd using hscaled
    obtain ⟨p, hp, ψ, hψ, hpl⟩ :=
      (isCompact_subdifferential_of_strictlyContinuousAt (hsc z)).tendsto_subseq hps
    have hd : Tendsto (fun n ↦ ((‖innerSL ℝ ‖ys (φ n)‖⁻¹‖₊ * κ₀ +
        ‖innerSL ℝ (‖ys (φ n)‖⁻¹ • ys (φ n) - z)‖₊ * κ : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
      have h1 := (hts.norm.mul_const (κ₀ : ℝ)).add
        ((tendsto_iff_norm_sub_tendsto_zero.1 hzl).mul_const (κ : ℝ))
      rw [norm_zero, zero_mul, zero_mul, add_zero] at h1
      refine h1.congr fun n ↦ ?_
      rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, hnorm, coe_nnnorm, innerSL_apply_norm]
      rfl
    have hul : Tendsto (fun n ↦ ‖ys (φ (ψ n))‖⁻¹ • us (φ (ψ n))) atTop (𝓝 p) := by
      have h1 : Tendsto (fun n ↦ ‖ys (φ (ψ n))‖⁻¹ • us (φ (ψ n)) - ps (ψ n)) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n ↦ hpd (ψ n)) (hd.comp hψ.tendsto_atTop)
      have h2 := hpl.add h1
      simp only [Function.comp_apply, add_sub_cancel, add_zero] at h2
      exact h2
    have hmem : -p ∈ normalCone X x := by
      refine hNX.mem_of_tendsto hul.neg (Eventually.of_forall fun n ↦ ?_)
      rw [← smul_neg]
      exact hcone.2 (hun _) (inv_pos.2 (hpos _))
    have hz0 := hQ z hzD ⟨p, hp, -p, hmem, add_neg_cancel p⟩
    rw [hz0, mem_sphere_zero_iff_norm, norm_zero] at hz
    exact zero_ne_one hz
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

end RW
