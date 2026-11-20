/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: a subgradient criterion for constancy

**Exercise 9.22.** For `f` lsc and proper and `x̄ ∈ dom f`, the following are
equivalent (`tfae_eventually_const`):
(a) `f` is constant on a neighborhood of `x̄`;
(b) `∂f(x) = {0}` for all `x` in a neighborhood of `x̄` relative to `dom f`;
(c) there is `ε > 0` such that `∂̂f(x) = {0}` whenever `|x - x̄| ≤ ε`,
`|f(x) - f(x̄)| ≤ ε` and `∂̂f(x) ≠ ∅`.

As the guide suggests, each condition is identified with strict
differentiability of `f` with zero gradient near `x̄`: (b) makes `∂f` locally
bounded (9.13(d)); (c) kills every horizon subgradient (8.3(c)), giving strict
continuity (9.13), after which the `f`-attentive restriction in (c) is automatic
near `x̄`.  Constancy then follows from the mean value inequality.
-/

import RockafellarWets.Chapter9.SmoothnessCriteria
import RockafellarWets.Chapter8.HorizonSubgradientSequences

open Filter Set Topology Metric
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Strict continuity at `x̄` propagates to all nearby points. -/
theorem ERealStrictlyContinuousAt.eventually_eRealStrictlyContinuousAt {f : E → EReal} {x : E}
    (h : ERealStrictlyContinuousAt f x) : ∀ᶠ y in 𝓝 x, ERealStrictlyContinuousAt f y := by
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
  obtain ⟨U, hU, hUo, hfin, hL⟩ := h.exists_lipschitzOnWith hk
  filter_upwards [hU] with y hy
  exact ⟨Filter.mem_of_superset (hUo.mem_nhds hy) fun z hz ↦ hfin z hz,
    strictlyContinuousAt_iff.2 ⟨k, U, hUo.mem_nhds hy, hL⟩⟩

/-- A function that is constant near `y` is strictly differentiable there with
gradient `0`. -/
theorem hasStrictGradientAt_zero_of_eventually_eq {f : E → EReal} {y : E} {c : ℝ}
    (h : ∀ᶠ z in 𝓝 y, f z = c) : HasStrictGradientAt f 0 y := by
  refine ⟨h.mono fun z hz ↦ by rw [hz, EReal.toReal_coe], ?_⟩
  have h1 : (fun _ : E ↦ c) =ᶠ[𝓝 y] fun z ↦ (f z).toReal :=
    h.mono fun z hz ↦ by simp [hz]
  rw [map_zero]
  exact (hasStrictFDerivAt_const c y).congr_of_eventuallyEq h1

/-- Strict differentiability with gradient `0` on a ball makes `f` constant there. -/
theorem eq_of_hasStrictGradientAt_zero_on_ball {f : E → EReal} {x : E} {r : ℝ} (hr : 0 < r)
    (h : ∀ y ∈ ball x r, HasStrictGradientAt f 0 y) : ∀ y ∈ ball x r, f y = f x := by
  intro y hy
  have h1 := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z ↦ (f z).toReal) (f' := fun _ ↦ (0 : E →L[ℝ] ℝ)) (C := 0)
    (fun z hz ↦ by
      have h2 := ((h z hz).2.hasFDerivAt).hasFDerivWithinAt (s := ball x r)
      rwa [map_zero] at h2)
    (fun z _ ↦ by simp) (convex_ball x r) (mem_ball_self hr) hy
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h1
  have h1' : (f y).toReal = (f x).toReal := h1
  rw [(h y hy).eRealStrictlyContinuousAt.finite, (h x (mem_ball_self hr)).eRealStrictlyContinuousAt.finite,
    h1']

/-- Points outside the effective domain carry no limiting subgradients. -/
theorem subdifferential_eq_empty_of_not_mem_effectiveDomain {f : E → EReal} {y : E}
    (hy : y ∉ effectiveDomain f) : subdifferential f y = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv ↦ ?_
  obtain ⟨⟨c, hc⟩, -⟩ := hv
  exact hy (show f y < ⊤ by rw [hc]; exact EReal.coe_lt_top c)

/-- (b) ⇒ (a) of 9.22, via strict differentiability with gradient `0` near `x̄`. -/
theorem eventually_eq_of_subdifferential_eq_zero [FiniteDimensional ℝ E] {f : E → EReal}
    {x : E} (hl : LowerSemicontinuous f) (hx1 : f x ≠ ⊥) (hx2 : f x ≠ ⊤)
    (hb : ∀ᶠ y in 𝓝[effectiveDomain f] x, subdifferential f y = {0}) :
    ∀ᶠ y in 𝓝 x, f y = f x := by
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx2 hx1).symm
  have hloc : IsLocallyLscAt f x :=
    isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ (hl.lowerSemicontinuousOn univ) (mem_univ x)
      hx1 hx2
  have hb' : ∀ᶠ y in 𝓝 x, subdifferential f y ⊆ {0} := by
    filter_upwards [eventually_nhdsWithin_iff.1 hb] with y hy
    by_cases hdom : y ∈ effectiveDomain f
    · rw [hy hdom]
    · rw [subdifferential_eq_empty_of_not_mem_effectiveDomain hdom]
      exact empty_subset _
  have hlb : SvLocallyBoundedAt (subdifferential f) x := by
    refine ⟨{y | subdifferential f y ⊆ {0}}, hb', (Bornology.isBounded_singleton (x := (0 : E))).subset ?_⟩
    intro u hu
    obtain ⟨y, hy, hu⟩ := mem_svImage.1 hu
    exact hy hu
  have hsc := (eRealStrictlyContinuousAt_iff_locallyBoundedAt_subdifferential hxc hloc).2 hlb
  have hgrad : ∀ᶠ y in 𝓝 x, HasStrictGradientAt f 0 y := by
    filter_upwards [hsc.eventually_eRealStrictlyContinuousAt, hb'] with y hy hsub
    obtain ⟨⟨u, hu⟩, -⟩ := hy.subdifferential_nonempty_compact
    have hu0 : u = 0 := hsub hu
    exact hasStrictGradientAt_of_subdifferential_eq hy
      (Subset.antisymm hsub (singleton_subset_iff.2 (hu0 ▸ hu)))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hgrad
  exact Filter.mem_of_superset (ball_mem_nhds x hr)
    (eq_of_hasStrictGradientAt_zero_on_ball hr fun y hy ↦ hrsub hy)

/-- **Exercise 9.22**: for `f` lsc and proper and `x̄ ∈ dom f`, constancy of `f` near
`x̄`, `∂f = {0}` near `x̄` relative to `dom f`, and the attentive regular-subgradient
condition (c) are equivalent. -/
theorem tfae_eventually_const [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hx : x ∈ effectiveDomain f) :
    List.TFAE [∀ᶠ y in 𝓝 x, f y = f x,
      ∀ᶠ y in 𝓝[effectiveDomain f] x, subdifferential f y = {0},
      ∃ ε > 0, ∀ y, ‖y - x‖ ≤ ε → (((f x).toReal - ε : ℝ) : EReal) ≤ f y →
        f y ≤ (((f x).toReal + ε : ℝ) : EReal) → (regularSubdifferential f y).Nonempty →
          regularSubdifferential f y = {0}] := by
  have hx1 : f x ≠ ⊥ := (hp.2 x).ne'
  have hx2 : f x ≠ ⊤ := hx.ne
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx2 hx1).symm
  have hloc : IsLocallyLscAt f x :=
    isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ (hl.lowerSemicontinuousOn univ) (mem_univ x)
      hx1 hx2
  -- (a) gives strict differentiability with gradient `0` near `x̄`
  have hconst_grad : (∀ᶠ y in 𝓝 x, f y = f x) → ∀ᶠ y in 𝓝 x, HasStrictGradientAt f 0 y := by
    intro ha
    filter_upwards [ha.eventually_nhds] with y hy
    exact hasStrictGradientAt_zero_of_eventually_eq (c := (f x).toReal)
      (hy.mono fun z hz ↦ hz.trans hxc)
  tfae_have 1 → 2 := fun ha ↦ by
    filter_upwards [nhdsWithin_le_nhds (hconst_grad ha)] with y hy
    exact hy.subdifferential_eq
  tfae_have 2 → 1 := eventually_eq_of_subdifferential_eq_zero hl hx1 hx2
  tfae_have 1 → 3 := fun ha ↦ by
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 (hconst_grad ha)
    refine ⟨r / 2, half_pos hr, fun y hy _ _ hne ↦ ?_⟩
    have hyr : y ∈ ball x r := by
      rw [mem_ball, dist_eq_norm]
      linarith
    have h0 := (hrsub hyr).subdifferential_eq
    exact Subset.antisymm (fun u hu ↦ h0 ▸ regularSubdifferential_subset_subdifferential f y hu)
      (by
        obtain ⟨u, hu⟩ := hne
        have hu0 : u = 0 := by
          have := regularSubdifferential_subset_subdifferential f y hu
          rwa [h0, mem_singleton_iff] at this
        exact singleton_subset_iff.2 (hu0 ▸ hu))
  tfae_have 3 → 2 := fun ⟨ε, hε, hc⟩ ↦ by
    -- condition (c) at points close to `x̄` in argument and value
    have hzero : ∀ y, ‖y - x‖ ≤ ε → (((f x).toReal - ε : ℝ) : EReal) < f y →
        f y < (((f x).toReal + ε : ℝ) : EReal) → ∀ u ∈ regularSubdifferential f y, u = 0 := by
      intro y hy h1 h2 u hu
      have h3 := hc y hy h1.le h2.le ⟨u, hu⟩
      rw [h3] at hu
      exact hu
    -- horizon subgradients vanish, so `f` is strictly continuous at `x̄`
    have hband : Ioo (((f x).toReal - ε : ℝ) : EReal) (((f x).toReal + ε : ℝ) : EReal) ∈ 𝓝 (f x) := by
      have h := Ioo_mem_nhds
        (EReal.coe_lt_coe_iff.2 (show (f x).toReal - ε < (f x).toReal by linarith))
        (EReal.coe_lt_coe_iff.2 (show (f x).toReal < (f x).toReal + ε by linarith))
      rwa [← hxc] at h
    have hh : horizonSubdifferential f x = {0} := by
      refine Subset.antisymm (fun v hv ↦ ?_) (singleton_subset_iff.2
        ((mem_horizonSubdifferential_iff_zero_or_scaledSeq hxc).2 (Or.inl rfl)))
      rcases (mem_horizonSubdifferential_iff_zero_or_scaledSeq hxc).1 hv with h0 | ⟨y, w, t, hy, hw, -, -, hlim⟩
      · exact h0
      · obtain ⟨hy1, hy2⟩ := tendsto_attentiveNhds_iff.1 hy
        have hev : ∀ᶠ n in atTop, t n • w n = 0 := by
          filter_upwards [hy1.eventually (closedBall_mem_nhds x hε), hy2.eventually hband] with n hn1 hn2
          have hn1' : ‖y n - x‖ ≤ ε := by rw [← dist_eq_norm]; exact hn1
          rw [hzero (y n) hn1' hn2.1 hn2.2 (w n) (hw n), smul_zero]
        exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun n hn ↦ hn.symm))
    have hsc := (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hxc hloc).2 hh
    -- near `x̄`, limiting subgradients vanish
    have hband2 : Ioo (((f x).toReal - ε / 2 : ℝ) : EReal) (((f x).toReal + ε / 2 : ℝ) : EReal) ∈
        𝓝 (f x) := by
      have h := Ioo_mem_nhds
        (EReal.coe_lt_coe_iff.2 (show (f x).toReal - ε / 2 < (f x).toReal by linarith))
        (EReal.coe_lt_coe_iff.2 (show (f x).toReal < (f x).toReal + ε / 2 by linarith))
      rwa [← hxc] at h
    have hnear : ∀ᶠ y in 𝓝 x, subdifferential f y = {0} := by
      filter_upwards [hsc.eventually_eRealStrictlyContinuousAt,
        hsc.continuousAt.eventually hband2, ball_mem_nhds x (half_pos hε)] with y hy hfy hyx
      have hsub : subdifferential f y ⊆ {0} := by
        intro v hv
        obtain ⟨-, zs, us, hzs, hfz, hus, hulim⟩ := mem_subdifferential_iff_exists_seq.1 hv
        have hband3 : Ioo (((f x).toReal - ε : ℝ) : EReal) (((f x).toReal + ε : ℝ) : EReal) ∈
            𝓝 (f y) := by
          refine Ioo_mem_nhds (lt_trans (EReal.coe_lt_coe_iff.2 (by linarith)) hfy.1)
            (lt_trans hfy.2 (EReal.coe_lt_coe_iff.2 (by linarith)))
        have hev : ∀ᶠ n in atTop, us n = 0 := by
          filter_upwards [hzs.eventually (ball_mem_nhds y (half_pos hε)), hfz.eventually hband3]
            with n hn1 hn2
          have hn1' : ‖zs n - x‖ ≤ ε := by
            have h1 : dist (zs n) y < ε / 2 := hn1
            have h2 : dist y x < ε / 2 := hyx
            rw [← dist_eq_norm]
            linarith [dist_triangle (zs n) y x]
          exact hzero (zs n) hn1' hn2.1 hn2.2 (us n) (hus n)
        exact mem_singleton_iff.2
          (tendsto_nhds_unique hulim (tendsto_const_nhds.congr' (hev.mono fun n hn ↦ hn.symm)))
      obtain ⟨⟨u, hu⟩, -⟩ := hy.subdifferential_nonempty_compact
      exact Subset.antisymm hsub (singleton_subset_iff.2 ((mem_singleton_iff.1 (hsub hu)) ▸ hu))
    exact nhdsWithin_le_nhds hnear
  tfae_finish

end RW
