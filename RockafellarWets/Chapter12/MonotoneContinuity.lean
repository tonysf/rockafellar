/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Continuity properties of maximal monotone mappings

Theorem 12.63.  A sequence `xν → x̄` converges from the direction `dir w` when
`(xν - x̄)/τν → w` for some `τν ↘ 0` (Chapter 6); here `τν > 0`, `τν → 0` is
enough and `w` may be any vector.  For maximal monotone `T`:

* (a) if `lim sup T(xν) ≠ ∅`, then `x̄ ∈ dom T` and every cluster point of
  `T(xν)` maximizes `⟪·, w⟫` over `T(x̄)`, the face `{v ∈ T(x̄) | w ∈ N_{T(x̄)}(v)}`;
  the hypothesis `xν ∈ dom T` of the book is not needed;
* (b) if `xν ∈ dom T`, `x̄ ∈ dom T` and `w ∈ int T_{dom T}(x̄)`, the sets `T(xν)`
  are eventually nonempty and uniformly bounded, so `lim sup T(xν) ≠ ∅`;
* (c) `T` is continuous at `x̄ ∈ dom T` exactly when `T(x̄)` is a singleton, and
  then `x̄ ∈ int(dom T)`.

Part (b) follows the book with Proposition 12.37 (`D = cl(dom T)` is convex),
the description of `int T_D(x̄)` in 6.9 and 12.41 (`int D ⊂ dom T`); the uniform
bound comes from normalizing an unbounded sequence `vν ∈ T(xν)`, whose limit
`u` satisfies `⟪u, a - x̄⟫ ≤ 0` on `D` and `⟪u, w⟫ ≥ 0`, which is impossible when
`x̄ + εw ∈ int D`.  In (c), inner semicontinuity at `x̄` with `v₀, v₁ ∈ T(x̄)`
gives `⟪v₀ - v₁, v₁ - v₀⟫ ≥ 0` along `x̄ + t(v₁ - v₀)`, and conversely a singleton
`T(x̄)` makes `T` locally bounded at `x̄` by 12.38, so `x̄ ∈ int(dom T)` by 12.41
and inner semicontinuity follows from the closedness of `gph T`.
-/

import RockafellarWets.Chapter12.MonotoneDomains
import RockafellarWets.Chapter6.ChangeOfCoordinates
import RockafellarWets.Chapter8.SubderivativeFormulas

open Set Filter Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `x ν → x̄` from the direction `w`: `(x ν - x̄)/τ ν → w` for some `τ ν > 0`
tending to `0` (Chapter 6, before Definition 6.1). -/
def ConvergesFromDirection (x : ℕ → E) (xbar w : E) : Prop :=
  ∃ τ : ℕ → ℝ, (∀ n, 0 < τ n) ∧ Tendsto τ atTop (𝓝 0) ∧
    Tendsto (fun n ↦ (τ n)⁻¹ • (x n - xbar)) atTop (𝓝 w)

theorem ConvergesFromDirection.tendsto {x : ℕ → E} {xbar w : E}
    (h : ConvergesFromDirection x xbar w) : Tendsto x atTop (𝓝 xbar) := by
  obtain ⟨τ, hτ, hτ0, hw⟩ := h
  have h1 : Tendsto (fun n ↦ τ n • ((τ n)⁻¹ • (x n - xbar))) atTop (𝓝 ((0 : ℝ) • w)) :=
    hτ0.smul hw
  rw [zero_smul] at h1
  have h2 : Tendsto (fun n ↦ (x n - xbar) + xbar) atTop (𝓝 (0 + xbar)) := by
    refine (h1.congr fun n ↦ ?_).add tendsto_const_nhds
    rw [smul_smul, mul_inv_cancel₀ (hτ n).ne', one_smul]
  simpa using h2

/-- The face of `T(x̄)` in the direction `w` is the argmax of `⟪·, w⟫`, which by
Theorem 6.9 is `{v ∈ T(x̄) | w ∈ N_{T(x̄)}(v)}` for convex `T(x̄)`. -/
theorem argmax_inner_eq_normalCone {C : Set E} (hC : Convex ℝ C) (w : E) :
    {v ∈ C | ∀ v' ∈ C, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} = {v ∈ C | w ∈ normalCone C v} := by
  ext v
  simp only [mem_setOf_eq]
  refine and_congr_right fun hv ↦ ?_
  rw [normalCone_eq_of_convex hC hv]
  simp only [mem_setOf_eq]
  refine forall₂_congr fun v' _ ↦ ?_
  rw [inner_sub_right, real_inner_comm w v', real_inner_comm w v, sub_nonpos]

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **Theorem 12.63(a)**: if `xν → x̄` from the direction `w` and
`lim sup T(xν) ≠ ∅`, then `x̄ ∈ dom T` and `lim sup T(xν)` lies in the argmax of
`⟪·, w⟫` over `T(x̄)`, which is `{v ∈ T(x̄) | w ∈ N_{T(x̄)}(v)}`. -/
theorem SvMaximalMonotone.limsup_subset_argmax {T : E → Set E} (hT : SvMaximalMonotone T)
    {x : ℕ → E} {xbar w : E} (hx : ConvergesFromDirection x xbar w)
    (hne : (outerSetLimit fun n ↦ T (x n)).Nonempty) :
    xbar ∈ svDom T ∧
      outerSetLimit (fun n ↦ T (x n)) ⊆ {v ∈ T xbar | ∀ v' ∈ T xbar, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} ∧
      {v ∈ T xbar | ∀ v' ∈ T xbar, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} =
        {v ∈ T xbar | w ∈ normalCone (T xbar) v} := by
  have hxt := hx.tendsto
  obtain ⟨τ, hτ, -, hw⟩ := hx
  have hsub : outerSetLimit (fun n ↦ T (x n)) ⊆
      {v ∈ T xbar | ∀ v' ∈ T xbar, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} := by
    intro vb hvb
    rw [← outerSetLimitAlong_atTop] at hvb
    obtain ⟨ns, vs, hns, hvs, hvlim⟩ := mem_outerSetLimitAlong_iff_exists_seq.1 hvb
    have hxns : Tendsto (fun k ↦ x (ns k)) atTop (𝓝 xbar) := hxt.comp hns
    have hmem : vb ∈ T xbar :=
      hT.isClosed_svGraph.mem_of_tendsto (hxns.prodMk_nhds hvlim) (Eventually.of_forall hvs)
    refine ⟨hmem, fun v hv ↦ ?_⟩
    have hlim : Tendsto (fun k ↦ ⟪vs k - v, (τ (ns k))⁻¹ • (x (ns k) - xbar)⟫_ℝ) atTop
        (𝓝 ⟪vb - v, w⟫_ℝ) :=
      (hvlim.sub tendsto_const_nhds).inner (hw.comp hns)
    have hge : 0 ≤ ⟪vb - v, w⟫_ℝ := by
      refine ge_of_tendsto hlim (Eventually.of_forall fun k ↦ ?_)
      rw [real_inner_smul_right]
      exact mul_nonneg (inv_nonneg.2 (hτ _).le) (hT.1 hv (hvs k))
    rw [inner_sub_left] at hge
    linarith
  obtain ⟨vb, hvb⟩ := hne
  exact ⟨⟨vb, (hsub hvb).1⟩, hsub, argmax_inner_eq_normalCone (hT.convex_apply xbar) w⟩

/-- Interior points of the closure of the domain lie in the domain (12.41). -/
theorem SvMaximalMonotone.interior_closure_svDom_subset {T : E → Set E}
    (hT : SvMaximalMonotone T) : interior (closure (svDom T)) ⊆ svDom T :=
  interior_subset_intrinsicInterior.trans hT.intrinsicInterior_closure_svDom_subset

/-- **Theorem 12.63(b)**, with the direction described by `x̄ + εw ∈ int(cl(dom T))`
for some `ε > 0`; by 6.9 these `w` form `int T_{dom T}(x̄)`.  If `xν ∈ dom T`
converges to `x̄ ∈ dom T` from such a direction `w`, then the sets `T(xν)` are
eventually nonempty and uniformly bounded, so `lim sup T(xν) ≠ ∅`. -/
theorem SvMaximalMonotone.bounded_of_convergesFromDirection_of_mem_radialCone {T : E → Set E}
    (hT : SvMaximalMonotone T) {x : ℕ → E} {xbar w : E} (hdom : ∀ n, x n ∈ svDom T)
    (hxbar : xbar ∈ svDom T) (hx : ConvergesFromDirection x xbar w)
    (hw : w ∈ radialCone (interior (closure (svDom T))) xbar) :
    (∀ᶠ n in atTop, (T (x n)).Nonempty) ∧ (∃ R, ∀ᶠ n in atTop, T (x n) ⊆ closedBall 0 R) ∧
      (outerSetLimit fun n ↦ T (x n)).Nonempty := by
  set D := closure (svDom T) with hDdef
  have hxt := hx.tendsto
  obtain ⟨τ, hτ, hτ0, hwlim⟩ := hx
  -- `x̄ + εw ∈ int D`
  obtain ⟨ε, hε, hεD⟩ := hw
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hεD
  -- uniform bound
  have hbound : ∃ R, ∀ᶠ n in atTop, T (x n) ⊆ closedBall 0 R := by
    by_contra hcon
    push_neg at hcon
    have hfreq : ∀ k : ℕ, ∃ n ≥ k, ∃ v ∈ T (x n), (k : ℝ) < ‖v‖ := by
      intro k
      have := hcon k
      rw [frequently_atTop] at this
      obtain ⟨n, hn, hns⟩ := this k
      rw [not_subset] at hns
      obtain ⟨v, hv, hvn⟩ := hns
      rw [mem_closedBall_zero_iff, not_le] at hvn
      exact ⟨n, hn, v, hv, hvn⟩
    choose ns hns vs hvs hvsn using hfreq
    have hnsto : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
    have hvnorm : Tendsto (fun k ↦ ‖vs k‖) atTop atTop :=
      tendsto_atTop_mono (fun k ↦ (hvsn k).le) tendsto_natCast_atTop_atTop
    obtain ⟨φ, u, hφ, hu1, hu⟩ := exists_subseq_tendsto_normalize hvnorm
    have hφto : Tendsto (fun k ↦ ns (φ k)) atTop atTop := hnsto.comp hφ.tendsto_atTop
    -- `⟪u, a - x̄⟫ ≤ 0` on `D`
    have hnormal : ∀ a ∈ D, ⟪u, a - xbar⟫_ℝ ≤ 0 := by
      have hdomle : ∀ a ∈ svDom T, ⟪u, a - xbar⟫_ℝ ≤ 0 := by
        rintro a ⟨b, hb⟩
        exact inner_nonpos_of_inner_sub_nonneg (x := fun k ↦ x (ns (φ k)))
          (a := fun _ ↦ a) (b := fun _ ↦ b) (v := fun k ↦ vs (φ k))
          (Eventually.of_forall fun k ↦ hT.1 hb (hvs (φ k))) (hxt.comp hφto)
          tendsto_const_nhds tendsto_const_nhds (hvnorm.comp hφ.tendsto_atTop) hu
      have hcl : IsClosed {a : E | ⟪u, a - xbar⟫_ℝ ≤ 0} :=
        isClosed_le (by fun_prop) continuous_const
      exact closure_minimal hdomle hcl
    -- `⟪u, w⟫ ≥ 0`
    obtain ⟨v₀, hv₀⟩ := hxbar
    have huw : 0 ≤ ⟪u, w⟫_ℝ := by
      have hc : Tendsto (fun k ↦ ‖vs (φ k)‖⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (hvnorm.comp hφ.tendsto_atTop)
      have hlim : Tendsto (fun k ↦ ⟪‖vs (φ k)‖⁻¹ • vs (φ k) - ‖vs (φ k)‖⁻¹ • v₀,
          (τ (ns (φ k)))⁻¹ • (x (ns (φ k)) - xbar)⟫_ℝ) atTop
          (𝓝 ⟪u - (0 : ℝ) • v₀, w⟫_ℝ) :=
        (hu.sub (hc.smul tendsto_const_nhds)).inner (hwlim.comp hφto)
      rw [zero_smul, sub_zero] at hlim
      refine ge_of_tendsto hlim (Eventually.of_forall fun k ↦ ?_)
      rw [← smul_sub, real_inner_smul_left, real_inner_smul_right]
      exact mul_nonneg (inv_nonneg.2 (norm_nonneg _))
        (mul_nonneg (inv_nonneg.2 (hτ _).le) (hT.1 hv₀ (hvs (φ k))))
    -- contradiction with `x̄ + εw ∈ int D`
    have hmemD : xbar + ε • w + (r / 2) • u ∈ D := by
      apply interior_subset
      apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, Real.norm_of_nonneg
        (by linarith : (0 : ℝ) ≤ r / 2)]
      linarith
    have h := hnormal _ hmemD
    rw [show xbar + ε • w + (r / 2) • u - xbar = ε • w + (r / 2) • u by abel, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu1] at h
    have : 0 ≤ ε * ⟪u, w⟫_ℝ := mul_nonneg hε.le huw
    nlinarith
  obtain ⟨R, hR⟩ := hbound
  refine ⟨Eventually.of_forall hdom, ⟨R, hR⟩, ?_⟩
  -- a cluster point of a bounded selection
  choose vs hvs using hdom
  have hvsR : ∀ᶠ n in atTop, vs n ∈ closedBall (0 : E) R := by
    filter_upwards [hR] with n hn using hn (hvs n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hvsR
  obtain ⟨vb, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : E))
    (r := R)) (x := fun k ↦ vs (k + N)) (fun k ↦ hN _ (Nat.le_add_left N k))
  refine ⟨vb, fun V hV ↦ ?_⟩
  have hev : ∀ᶠ k in atTop, vs (φ k + N) ∈ V := hlim.eventually_mem hV
  have hto : Tendsto (fun k ↦ φ k + N) atTop atTop :=
    (tendsto_add_atTop_nat N).comp hφ.tendsto_atTop
  exact hto.frequently (hev.frequently.mono fun k hk ↦ ⟨_, hvs _, hk⟩)

/-- **Theorem 12.63(b)**: if `xν ∈ dom T` converges to `x̄ ∈ dom T` from a direction
`w ∈ int T_{dom T}(x̄)`, then the sets `T(xν)` are eventually nonempty and
uniformly bounded, so `lim sup T(xν) ≠ ∅`. -/
theorem SvMaximalMonotone.bounded_of_convergesFromDirection {T : E → Set E}
    (hT : SvMaximalMonotone T) {x : ℕ → E} {xbar w : E} (hdom : ∀ n, x n ∈ svDom T)
    (hxbar : xbar ∈ svDom T) (hx : ConvergesFromDirection x xbar w)
    (hw : w ∈ interior (tangentCone (svDom T) xbar)) :
    (∀ᶠ n in atTop, (T (x n)).Nonempty) ∧ (∃ R, ∀ᶠ n in atTop, T (x n) ⊆ closedBall 0 R) ∧
      (outerSetLimit fun n ↦ T (x n)).Nonempty := by
  have hwD : w ∈ interior (tangentCone (closure (svDom T)) xbar) :=
    interior_mono (tangentCone_mono subset_closure xbar) hw
  rw [interior_tangentCone_of_convex hT.convex_closure_svDom (subset_closure hxbar)] at hwD
  exact hT.bounded_of_convergesFromDirection_of_mem_radialCone hdom hxbar hx hwD

/-- **Theorem 12.63(c)**: a maximal monotone `T` is continuous at `x̄ ∈ dom T` if
and only if it is single-valued there, and then `x̄ ∈ int(dom T)`. -/
theorem SvMaximalMonotone.svContinuousAt_iff_singleton {T : E → Set E}
    (hT : SvMaximalMonotone T) {xbar : E} (hxbar : xbar ∈ svDom T) :
    (SvContinuousAt T xbar ↔ ∃ v, T xbar = {v}) ∧
      (SvContinuousAt T xbar → xbar ∈ interior (svDom T)) := by
  -- continuity forces `x̄ ∈ int(dom T)`
  have hint : SvContinuousAt T xbar → xbar ∈ interior (svDom T) := by
    rintro ⟨-, hisc⟩
    obtain ⟨v₀, hv₀⟩ := hxbar
    have h := hisc hv₀
    rw [svInnerLimit, mem_innerSetLimitAlong] at h
    have := h univ univ_mem
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [this] with y hy
    obtain ⟨v, hv, -⟩ := hy
    exact ⟨v, hv⟩
  refine ⟨⟨fun hc ↦ ?_, fun ⟨vb, hvb⟩ ↦ ?_⟩, hint⟩
  · -- continuity ⇒ single-valuedness
    obtain ⟨v₀, hv₀⟩ := hxbar
    refine ⟨v₀, Subset.antisymm (fun v₁ hv₁ ↦ ?_) (singleton_subset_iff.2 hv₀)⟩
    rw [mem_singleton_iff]
    set w := v₁ - v₀ with hwdef
    have hkey : ∀ ε > 0, -(ε * ‖w‖) ≤ ⟪v₀ - v₁, w⟫_ℝ := by
      intro ε hε
      have h := hc.2 hv₀
      rw [svInnerLimit, mem_innerSetLimitAlong] at h
      have hev := h (ball v₀ ε) (ball_mem_nhds _ hε)
      have hpath : Tendsto (fun t : ℝ ↦ xbar + t • w) (𝓝[>] 0) (𝓝 xbar) := by
        have hc : Continuous fun t : ℝ ↦ xbar + t • w := by fun_prop
        have := hc.tendsto 0
        simp only [zero_smul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      obtain ⟨t, ht, ht0⟩ := ((hpath.eventually hev).and self_mem_nhdsWithin).exists
      obtain ⟨v, hv, hvball⟩ := ht
      have hmono := hT.1 hv₁ hv
      rw [show xbar + t • w - xbar = t • w by abel, real_inner_smul_right] at hmono
      have hvw : 0 ≤ ⟪v - v₁, w⟫_ℝ := nonneg_of_mul_nonneg_right (by linarith) ht0
      have hcs : |⟪v₀ - v, w⟫_ℝ| ≤ ‖v₀ - v‖ * ‖w‖ := abs_real_inner_le_norm _ _
      have hd : ‖v₀ - v‖ < ε := by rw [norm_sub_rev, ← dist_eq_norm]; exact hvball
      have e : ⟪v₀ - v₁, w⟫_ℝ = ⟪v - v₁, w⟫_ℝ + ⟪v₀ - v, w⟫_ℝ := by
        rw [← inner_add_left]; congr 1; abel
      rw [e]
      have := neg_abs_le ⟪v₀ - v, w⟫_ℝ
      nlinarith [norm_nonneg w]
    have hle : ⟪v₀ - v₁, w⟫_ℝ ≥ 0 := by
      by_contra hneg
      push_neg at hneg
      by_cases hw0 : ‖w‖ = 0
      · have := hkey 1 one_pos
        rw [hw0, mul_zero, neg_zero] at this
        linarith
      · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
        have hpos : 0 < -⟪v₀ - v₁, w⟫_ℝ / (2 * ‖w‖) := div_pos (by linarith) (by positivity)
        have h1 := hkey _ hpos
        have e : -⟪v₀ - v₁, w⟫_ℝ / (2 * ‖w‖) * ‖w‖ = -⟪v₀ - v₁, w⟫_ℝ / 2 := by
          field_simp
        rw [e] at h1
        linarith
    rw [show v₀ - v₁ = -w by rw [hwdef]; abel, inner_neg_left, real_inner_self_eq_norm_sq] at hle
    have hw0 : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact (sub_eq_zero.1 (norm_eq_zero.1 hw0))
  · -- single-valuedness ⇒ continuity
    have hlb : SvLocallyBoundedAt T xbar :=
      (hT.svLocallyBoundedAt_iff_isBounded hxbar).2 (hvb ▸ Bornology.isBounded_singleton)
    have hxint : xbar ∈ interior (svDom T) := by
      have hfr := (hT.svLocallyBoundedAt_iff_notMem_frontier).1 hlb
      have hcl : xbar ∈ closure (closure (svDom T)) := subset_closure (subset_closure hxbar)
      have : xbar ∈ interior (closure (svDom T)) := by
        rw [← closure_diff_frontier]
        exact ⟨hcl, hfr⟩
      exact interior_maximal hT.interior_closure_svDom_subset isOpen_interior this
    refine ⟨hT.svOsc xbar, fun v hv ↦ ?_⟩
    rw [hvb, mem_singleton_iff] at hv
    subst hv
    rw [svInnerLimit, mem_innerSetLimitAlong]
    intro V hV
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨xs, hxs, hxsV⟩ := frequently_iff_seq_forall.1 hcon
    obtain ⟨U, hU, hUb⟩ := hlb
    obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
    have hev : ∀ᶠ n in atTop, xs n ∈ interior (svDom T) ∩ U :=
      hxs (inter_mem (isOpen_interior.mem_nhds hxint) hU)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have hne : ∀ n, (T (xs (n + N))).Nonempty := fun n ↦ by
      have : xs (n + N) ∈ svDom T := interior_subset (hN _ (Nat.le_add_left N n)).1
      exact this
    choose ws hws using hne
    have hwsR : ∀ n, ws n ∈ closedBall (0 : E) R := fun n ↦
      hR (mem_svImage.2 ⟨xs (n + N), (hN _ (Nat.le_add_left N n)).2, hws n⟩)
    obtain ⟨v', -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hwsR
    have hxsφ : Tendsto (fun k ↦ xs (φ k + N)) atTop (𝓝 xbar) :=
      hxs.comp ((tendsto_add_atTop_nat N).comp hφ.tendsto_atTop)
    have hv' : v' ∈ T xbar :=
      hT.isClosed_svGraph.mem_of_tendsto (hxsφ.prodMk_nhds hlim)
        (Eventually.of_forall fun k ↦ hws (φ k))
    rw [hvb, mem_singleton_iff] at hv'
    subst hv'
    obtain ⟨k, hk⟩ := (hlim.eventually_mem hV).exists
    exact hxsV (φ k + N) ⟨ws (φ k), hws (φ k), hk⟩

/-- **Theorem 12.63 (continuity properties)**, collected. -/
theorem continuity_properties {T : E → Set E} (hT : SvMaximalMonotone T) :
    (∀ (x : ℕ → E) (xbar w : E), ConvergesFromDirection x xbar w →
      (outerSetLimit fun n ↦ T (x n)).Nonempty →
        xbar ∈ svDom T ∧
          outerSetLimit (fun n ↦ T (x n)) ⊆ {v ∈ T xbar | ∀ v' ∈ T xbar, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} ∧
          {v ∈ T xbar | ∀ v' ∈ T xbar, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} =
            {v ∈ T xbar | w ∈ normalCone (T xbar) v}) ∧
      (∀ (x : ℕ → E) (xbar w : E), (∀ n, x n ∈ svDom T) → xbar ∈ svDom T →
        ConvergesFromDirection x xbar w → w ∈ interior (tangentCone (svDom T) xbar) →
          (∀ᶠ n in atTop, (T (x n)).Nonempty) ∧
            (∃ R, ∀ᶠ n in atTop, T (x n) ⊆ closedBall 0 R) ∧
            (outerSetLimit fun n ↦ T (x n)).Nonempty) ∧
      (∀ xbar ∈ svDom T, (SvContinuousAt T xbar ↔ ∃ v, T xbar = {v}) ∧
        (SvContinuousAt T xbar → xbar ∈ interior (svDom T))) :=
  ⟨fun _ _ _ hx hne ↦ hT.limsup_subset_argmax hx hne,
    fun _ _ _ hdom hxbar hx hw ↦ hT.bounded_of_convergesFromDirection hdom hxbar hx hw,
    fun _ hxbar ↦ hT.svContinuousAt_iff_singleton hxbar⟩

end RW
