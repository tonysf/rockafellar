/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Prox-regularity and subdifferential continuity

Definitions 13.27 and 13.28, Exercise 13.29, Example 13.30 and Exercise 13.31.

**Correction to Exercise 13.29.**  Sufficiency holds as printed: continuity of
`f` at `x̄` relative to every set `(∂f)⁻¹(B) ∋ x̄` with `B` compact gives
subdifferential continuity at `x̄`.  Necessity fails: for `f(x) = x` on
`x ≤ 0` and `f(x) = 1 - x` on `x > 0`, `∂f(0) = [1, ∞)`, every sequence
`(xν, vν) → (0, v̄)` with `v̄ ≥ 1` and `vν ∈ ∂f(xν)` has `xν ≤ 0`, so `f` is
subdifferentially continuous at `0`; but for the compact set `B = {-1, 1}`
one has `(∂f)⁻¹(B) = ℝ`, and `f` jumps at `0`
(`jumpExample_counterexample`).  Necessity does hold for compact
`B ⊂ ∂f(x̄)`, in any inner product space, and more generally for compact `B`
whose subgradient limits at `x̄` stay in `∂f(x̄)`
(`IsSubdifferentiallyContinuousAtPoint.continuousWithinAt_of_limits_mem`).
Subdifferential continuity for `v̄` is exactly continuity of `(x, v) ↦ f(x)` at
`(x̄, v̄)` relative to `gph ∂f` (`isSubdifferentiallyContinuousAt_iff_tendsto`),
and the printed condition characterizes something stronger: when
`∂f(x̄) ≠ ∅`, it holds if and only if `f` is subdifferentially continuous at
`x̄` and `∂f` is outer semicontinuous at `x̄` (Definition 5.4: `xν → x̄`,
`vν ∈ ∂f(xν)`, `vν → v` imply `v ∈ ∂f(x̄)`, with no condition on `f(xν)`)
(`forall_continuousWithinAt_subdifferentialPreimage_iff`).  The jump example
fails the second condition along `(1/ν, -1) → (0, -1)`
(`not_svOscAt_subdifferential_jumpExample`).
-/

import RockafellarWets.Chapter13.SecondSubderivatives
import RockafellarWets.Chapter8.IndicatorSubgradients
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.SubgradientsAndGradients
import RockafellarWets.Chapter9.SmoothnessCriteria

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Definition 13.27 -/

/-- **Definition 13.27**: `f` is prox-regular at `x̄` for `v̄` when `f` is finite and locally
lsc at `x̄` with `v̄ ∈ ∂f(x̄)`, and there are `ε > 0` and `ρ ≥ 0` with
`f(x') ≥ f(x) + ⟪v, x' - x⟫ - (ρ/2)‖x' - x‖²` for all `x' ∈ IB(x̄, ε)` whenever
`v ∈ ∂f(x)`, `‖v - v̄‖ < ε`, `‖x - x̄‖ < ε` and `f(x) < f(x̄) + ε`. -/
def IsProxRegularAt (f : E → EReal) (x v : E) : Prop :=
  IsLocallyLscAt f x ∧ v ∈ subdifferential f x ∧ ∃ ε > 0, ∃ ρ ≥ 0,
    ∀ y v', v' ∈ subdifferential f y → ‖v' - v‖ < ε → ‖y - x‖ < ε → f y < f x + ε →
      ∀ x' ∈ closedBall x ε, f y + ((⟪v', x' - y⟫_ℝ - ρ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x'

/-- **Definition 13.27**: `f` is prox-regular at `x̄` when it is prox-regular at `x̄` for every
`v̄ ∈ ∂f(x̄)`. -/
def IsProxRegularAtPoint (f : E → EReal) (x : E) : Prop :=
  ∀ v ∈ subdifferential f x, IsProxRegularAt f x v

/-- The remark after Definition 13.27: prox-regularity makes every nearby subgradient with
nearby function value a proximal subgradient, with a uniform constant and neighborhood. -/
theorem IsProxRegularAt.proximal {f : E → EReal} {x v : E} (h : IsProxRegularAt f x v) :
    ∃ ε > 0, ∃ ρ ≥ 0, ∀ y v', v' ∈ subdifferential f y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      f y < f x + ε → ∀ᶠ x' in 𝓝 y,
        f y + ((⟪v', x' - y⟫_ℝ - ρ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x' := by
  obtain ⟨-, -, ε, hε, ρ, hρ, hprox⟩ := h
  refine ⟨ε, hε, ρ, hρ, fun y v' hv' hvv hyx hfy ↦ ?_⟩
  have hball : closedBall x ε ∈ 𝓝 y :=
    mem_of_superset (isOpen_ball.mem_nhds (by rwa [mem_ball, dist_eq_norm]))
      ball_subset_closedBall
  filter_upwards [hball] with x' hx'
  exact hprox y v' hv' hvv hyx hfy x' hx'

/-! ### Definition 13.28 -/

/-- **Definition 13.28**: `f` is subdifferentially continuous at `x̄` for `v̄` when
`v̄ ∈ ∂f(x̄)` and `f(xν) → f(x̄)` whenever `(xν, vν) → (x̄, v̄)` with `vν ∈ ∂f(xν)`. -/
def IsSubdifferentiallyContinuousAt (f : E → EReal) (x v : E) : Prop :=
  v ∈ subdifferential f x ∧ ∀ xs vs : ℕ → E, Tendsto xs atTop (𝓝 x) →
    Tendsto vs atTop (𝓝 v) → (∀ n, vs n ∈ subdifferential f (xs n)) →
      Tendsto (fun n ↦ f (xs n)) atTop (𝓝 (f x))

/-- **Definition 13.28**: subdifferential continuity at `x̄` for every `v̄ ∈ ∂f(x̄)`. -/
def IsSubdifferentiallyContinuousAtPoint (f : E → EReal) (x : E) : Prop :=
  ∀ v ∈ subdifferential f x, IsSubdifferentiallyContinuousAt f x v

/-! ### Exercise 13.29 -/

section Exercise1329

/-- The set `(∂f)⁻¹(B)` of points having a subgradient in `B`. -/
def subdifferentialPreimage (f : E → EReal) (B : Set E) : Set E :=
  {y | (subdifferential f y ∩ B).Nonempty}

/-- **Exercise 13.29**, sufficiency: if `f` is continuous at `x̄` relative to every set
`(∂f)⁻¹(B)` containing `x̄` with `B` compact, then `f` is subdifferentially continuous at `x̄`. -/
theorem isSubdifferentiallyContinuousAtPoint_of_continuousWithinAt {f : E → EReal} {x : E}
    (h : ∀ B : Set E, IsCompact B → x ∈ subdifferentialPreimage f B →
      ContinuousWithinAt f (subdifferentialPreimage f B) x) :
    IsSubdifferentiallyContinuousAtPoint f x := by
  intro v hv
  refine ⟨hv, fun xs vs hxs hvs hsub ↦ ?_⟩
  set B : Set E := insert v (range vs)
  have hB : IsCompact B := hvs.isCompact_insert_range
  have hxB : x ∈ subdifferentialPreimage f B := ⟨v, hv, mem_insert v _⟩
  have hxsB : ∀ n, xs n ∈ subdifferentialPreimage f B :=
    fun n ↦ ⟨vs n, hsub n, mem_insert_of_mem v (mem_range_self n)⟩
  exact (h B hB hxB).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hxs, Eventually.of_forall hxsB⟩)

/-- **Exercise 13.29**, the particular case: `f` is subdifferentially continuous at any point
where it is continuous relative to `dom f`. -/
theorem isSubdifferentiallyContinuousAtPoint_of_continuousWithinAt_dom {f : E → EReal}
    {x : E} (h : ContinuousWithinAt f (effectiveDomain f) x) :
    IsSubdifferentiallyContinuousAtPoint f x := by
  refine isSubdifferentiallyContinuousAtPoint_of_continuousWithinAt fun B _ _ ↦
    h.mono fun y ⟨v, hv, _⟩ ↦ ?_
  obtain ⟨⟨c, hc⟩, -⟩ := hv
  change f y < ⊤
  rw [hc]
  exact EReal.coe_lt_top c

/-- **Exercise 13.29**, corrected necessity: subdifferential continuity at `x̄` gives continuity
at `x̄` relative to `(∂f)⁻¹(B)` for every compact `B ⊂ ∂f(x̄)` (in any inner product space). -/
theorem IsSubdifferentiallyContinuousAtPoint.continuousWithinAt
    {f : E → EReal} {x : E} (h : IsSubdifferentiallyContinuousAtPoint f x) {B : Set E}
    (hB : IsCompact B) (hBsub : B ⊆ subdifferential f x) :
    ContinuousWithinAt f (subdifferentialPreimage f B) x := by
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro xs hxs
  obtain ⟨hx, hxS⟩ := tendsto_nhdsWithin_iff.1 hxs
  -- every subsequence has a further subsequence along which `f` converges
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hmem : ∀ᶠ k in atTop, xs (ns k) ∈ subdifferentialPreimage f B := hns.eventually hxS
  obtain ⟨K, hK⟩ := eventually_atTop.1 hmem
  choose vs hvs using fun k ↦ hK (k + K) (Nat.le_add_left K k)
  obtain ⟨v, hvB, φ, hφ, hlim⟩ := hB.tendsto_subseq (fun k ↦ (hvs k).2)
  refine ⟨fun k ↦ φ k + K, ?_⟩
  have := (h v (hBsub hvB)).2 (fun k ↦ xs (ns (φ k + K))) (fun k ↦ vs (φ k))
    (hx.comp (hns.comp (tendsto_atTop_mono (fun k ↦ Nat.le_add_right (φ k) K)
      hφ.tendsto_atTop)))
    hlim (fun k ↦ (hvs (φ k)).1)
  exact this

/-- Outer semicontinuity of `∂f` at `x̄` (Definition 5.4) in sequential form: limits of
subgradients at points converging to `x̄` are subgradients at `x̄`. -/
theorem svOscAt_subdifferential_iff {f : E → EReal} {x : E} :
    SvOscAt (subdifferential f) x ↔ ∀ (xs vs : ℕ → E) (v : E), Tendsto xs atTop (𝓝 x) →
      Tendsto vs atTop (𝓝 v) → (∀ n, vs n ∈ subdifferential f (xs n)) →
        v ∈ subdifferential f x := by
  constructor
  · intro h xs vs v hxs hvs hsub
    exact h (mem_outerSetLimitAlong_iff_exists_seq.2 ⟨xs, vs, hxs, hsub, hvs⟩)
  · intro h v hv
    obtain ⟨xs, vs, hxs, hsub, hvs⟩ := mem_outerSetLimitAlong_iff_exists_seq.1 hv
    exact h xs vs v hxs hvs hsub

/-- **Exercise 13.29**, necessity for every compact `B` whose subgradient limits at `x̄` stay in
`∂f(x̄)`: if `xν → x̄`, `vν ∈ ∂f(xν) ∩ B` and `vν → v` force `v ∈ ∂f(x̄)`, then subdifferential
continuity at `x̄` gives continuity at `x̄` relative to `(∂f)⁻¹(B)`.  Both `B ⊆ ∂f(x̄)` and the
outer semicontinuity of `∂f` at `x̄` give this hypothesis. -/
theorem IsSubdifferentiallyContinuousAtPoint.continuousWithinAt_of_limits_mem {f : E → EReal}
    {x : E} (h : IsSubdifferentiallyContinuousAtPoint f x) {B : Set E} (hB : IsCompact B)
    (hB' : ∀ (xs vs : ℕ → E) (v : E), Tendsto xs atTop (𝓝 x) → Tendsto vs atTop (𝓝 v) →
      (∀ n, vs n ∈ subdifferential f (xs n) ∩ B) → v ∈ subdifferential f x) :
    ContinuousWithinAt f (subdifferentialPreimage f B) x := by
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro xs hxs
  obtain ⟨hx, hxS⟩ := tendsto_nhdsWithin_iff.1 hxs
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hmem : ∀ᶠ k in atTop, xs (ns k) ∈ subdifferentialPreimage f B := hns.eventually hxS
  obtain ⟨K, hK⟩ := eventually_atTop.1 hmem
  choose vs hvs using fun k ↦ hK (k + K) (Nat.le_add_left K k)
  obtain ⟨v, -, φ, hφ, hlim⟩ := hB.tendsto_subseq (fun k ↦ (hvs k).2)
  refine ⟨fun k ↦ φ k + K, ?_⟩
  have hxlim : Tendsto (fun k ↦ xs (ns (φ k + K))) atTop (𝓝 x) :=
    hx.comp (hns.comp (tendsto_atTop_mono (fun k ↦ Nat.le_add_right (φ k) K) hφ.tendsto_atTop))
  have hvx : v ∈ subdifferential f x :=
    hB' (fun k ↦ xs (ns (φ k + K))) (fun k ↦ vs (φ k)) v hxlim hlim (fun k ↦ hvs (φ k))
  exact (h v hvx).2 (fun k ↦ xs (ns (φ k + K))) (fun k ↦ vs (φ k)) hxlim hlim
    (fun k ↦ (hvs (φ k)).1)

/-- **Exercise 13.29**, exact form.  When `∂f(x̄) ≠ ∅`, `f` is continuous at `x̄` relative to every
set `(∂f)⁻¹(B) ∋ x̄` with `B` compact (the printed condition) if and only if `f` is
subdifferentially continuous at `x̄` and `∂f` is outer semicontinuous at `x̄`. -/
theorem forall_continuousWithinAt_subdifferentialPreimage_iff {f : E → EReal} {x : E}
    (hne : (subdifferential f x).Nonempty) :
    (∀ B : Set E, IsCompact B → x ∈ subdifferentialPreimage f B →
      ContinuousWithinAt f (subdifferentialPreimage f B) x) ↔
    IsSubdifferentiallyContinuousAtPoint f x ∧ SvOscAt (subdifferential f) x := by
  rw [svOscAt_subdifferential_iff]
  constructor
  · intro h
    refine ⟨isSubdifferentiallyContinuousAtPoint_of_continuousWithinAt h, ?_⟩
    intro xs vs v hxs hvs hsub
    obtain ⟨v₀, hv₀⟩ := hne
    obtain ⟨c, hc⟩ := hv₀.1
    have hB : IsCompact (insert v₀ (insert v (range vs))) := hvs.isCompact_insert_range.insert v₀
    have hxB : x ∈ subdifferentialPreimage f (insert v₀ (insert v (range vs))) :=
      ⟨v₀, hv₀, mem_insert _ _⟩
    have hxsB : ∀ n, xs n ∈ subdifferentialPreimage f (insert v₀ (insert v (range vs))) :=
      fun n ↦ ⟨vs n, hsub n, mem_insert_of_mem _ (mem_insert_of_mem _ (mem_range_self n))⟩
    have hf : Tendsto (f ∘ xs) atTop (𝓝 (f x)) :=
      (h _ hB hxB).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hxs, Eventually.of_forall hxsB⟩)
    refine outerSetLimitAlong_subdifferential_subset hc ?_
    rw [mem_outerSetLimitAlong]
    intro V hV
    have hatt : Tendsto xs atTop (attentiveNhds f x) := tendsto_attentiveNhds_iff.2 ⟨hxs, hf⟩
    refine hatt.frequently (Eventually.frequently ?_)
    filter_upwards [hvs.eventually hV] with n hn
    exact ⟨vs n, hsub n, hn⟩
  · rintro ⟨hsc, hcl⟩ B hB _
    exact hsc.continuousWithinAt_of_limits_mem hB
      (fun xs vs v hxs hvs hsub ↦ hcl xs vs v hxs hvs fun n ↦ (hsub n).1)

/-- **Definition 13.28** in filter form: subdifferential continuity at `x̄` for `v̄` is continuity
of `(x, v) ↦ f(x)` at `(x̄, v̄)` relative to `gph ∂f`. -/
theorem isSubdifferentiallyContinuousAt_iff_tendsto {f : E → EReal} {x v : E} :
    IsSubdifferentiallyContinuousAt f x v ↔ v ∈ subdifferential f x ∧
      Tendsto (fun p : E × E ↦ f p.1) (𝓝[{p | p.2 ∈ subdifferential f p.1}] (x, v)) (𝓝 (f x)) := by
  refine and_congr_right fun _ ↦ ?_
  rw [tendsto_iff_seq_tendsto]
  constructor
  · intro h ps hps
    obtain ⟨hp, hpS⟩ := tendsto_nhdsWithin_iff.1 hps
    obtain ⟨K, hK⟩ := eventually_atTop.1 hpS
    have h1 : Tendsto (fun n ↦ ps (n + K)) atTop (𝓝 (x, v)) :=
      hp.comp (tendsto_add_atTop_nat K)
    have := h (fun n ↦ (ps (n + K)).1) (fun n ↦ (ps (n + K)).2)
      ((continuous_fst.tendsto _).comp h1) ((continuous_snd.tendsto _).comp h1)
      (fun n ↦ hK (n + K) (Nat.le_add_left K n))
    exact (tendsto_add_atTop_iff_nat K).1 this
  · intro h xs vs hxs hvs hsub
    exact h (fun n ↦ (xs n, vs n)) (tendsto_nhdsWithin_iff.2
      ⟨hxs.prodMk_nhds hvs, Eventually.of_forall hsub⟩)

end Exercise1329

/-! ### The counterexample to necessity in Exercise 13.29 -/

section JumpExample

/-- `f(x) = x` for `x ≤ 0` and `f(x) = 1 - x` for `x > 0`. -/
noncomputable def jumpExample (x : ℝ) : EReal := ((if x ≤ 0 then x else 1 - x : ℝ) : EReal)

theorem jumpExample_of_nonpos {x : ℝ} (hx : x ≤ 0) : jumpExample x = (x : EReal) := by
  simp [jumpExample, hx]

theorem jumpExample_of_pos {x : ℝ} (hx : 0 < x) : jumpExample x = ((1 - x : ℝ) : EReal) := by
  simp [jumpExample, not_le.2 hx]

theorem one_le_of_mem_regularSubdifferential_jumpExample {x v : ℝ} (hx : x ≤ 0)
    (hv : v ∈ regularSubdifferential jumpExample x) : 1 ≤ v := by
  obtain ⟨c, hc, h⟩ := hv
  rw [jumpExample_of_nonpos hx, EReal.coe_eq_coe_iff] at hc
  rw [← hc] at h
  by_contra hlt
  push_neg at hlt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h ((1 - v) / 2) (by linarith))
  have hy := hball (y := x - δ / 2) (by
    rw [Real.dist_eq, show x - δ / 2 - x = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)]
    linarith)
  rw [jumpExample_of_nonpos (by linarith), EReal.coe_le_coe_iff] at hy
  simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs,
    show x - δ / 2 - x = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)] at hy
  nlinarith

theorem eq_neg_one_of_mem_regularSubdifferential_jumpExample {x v : ℝ} (hx : 0 < x)
    (hv : v ∈ regularSubdifferential jumpExample x) : v = -1 := by
  obtain ⟨c, hc, h⟩ := hv
  rw [jumpExample_of_pos hx, EReal.coe_eq_coe_iff] at hc
  rw [← hc] at h
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ ?_)
    (le_of_forall_pos_lt_add fun ε hε ↦ ?_)
  · obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h (ε / 2) (half_pos hε))
    have hy := hball (y := x + δ / 2) (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
      linarith)
    rw [jumpExample_of_pos (by positivity), EReal.coe_le_coe_iff] at hy
    simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, add_sub_cancel_left,
      abs_of_pos (half_pos hδ)] at hy
    nlinarith
  · obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h (ε / 2) (half_pos hε))
    set t := min (δ / 2) (x / 2) with ht
    have htpos : 0 < t := lt_min (half_pos hδ) (half_pos hx)
    have htx : t ≤ x / 2 := min_le_right _ _
    have hy := hball (y := x - t) (by
      rw [Real.dist_eq, show x - t - x = -t by ring, abs_neg, abs_of_pos htpos]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ))
    rw [jumpExample_of_pos (by linarith), EReal.coe_le_coe_iff] at hy
    simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, show x - t - x = -t by ring,
      abs_neg, abs_of_pos htpos] at hy
    nlinarith

theorem one_mem_regularSubdifferential_jumpExample :
    (1 : ℝ) ∈ regularSubdifferential jumpExample 0 := by
  refine ⟨0, by rw [jumpExample_of_nonpos le_rfl, EReal.coe_zero], fun ε hε ↦ ?_⟩
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
  change y < 1 / 2 at hy
  simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sub_zero, zero_add, mul_one]
  by_cases hy0 : y ≤ 0
  · rw [jumpExample_of_nonpos hy0, EReal.coe_le_coe_iff]
    nlinarith [abs_nonneg y]
  · rw [jumpExample_of_pos (lt_of_not_ge hy0), EReal.coe_le_coe_iff]
    nlinarith [abs_nonneg y]

theorem neg_one_mem_regularSubdifferential_jumpExample {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ∈ regularSubdifferential jumpExample x := by
  refine ⟨1 - x, jumpExample_of_pos hx, fun ε hε ↦ ?_⟩
  filter_upwards [Ioi_mem_nhds hx] with y hy
  change 0 < y at hy
  rw [jumpExample_of_pos hy, EReal.coe_le_coe_iff]
  simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs]
  nlinarith [abs_nonneg (y - x)]

theorem eq_neg_one_of_mem_subdifferential_jumpExample {x v : ℝ} (hx : 0 < x)
    (hv : v ∈ subdifferential jumpExample x) : v = -1 := by
  obtain ⟨-, xs, vs, hxs, -, hvs, hlim⟩ := mem_subdifferential_iff_exists_seq.1 hv
  have hev : ∀ᶠ n in atTop, vs n = -1 := by
    filter_upwards [hxs.eventually (Ioi_mem_nhds hx)] with n hn
    exact eq_neg_one_of_mem_regularSubdifferential_jumpExample hn (hvs n)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun n h ↦ h.symm))

theorem one_le_of_mem_subdifferential_jumpExample_zero {v : ℝ}
    (hv : v ∈ subdifferential jumpExample 0) : 1 ≤ v := by
  obtain ⟨-, xs, vs, hxs, hfxs, hvs, hlim⟩ := mem_subdifferential_iff_exists_seq.1 hv
  rw [jumpExample_of_nonpos le_rfl] at hfxs
  have hev : ∀ᶠ n in atTop, xs n ≤ 0 := by
    filter_upwards [hxs.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
      hfxs.eventually (Iio_mem_nhds (show ((0 : ℝ) : EReal) < ((1 / 2 : ℝ) : EReal) by
        norm_num))] with n hn hfn
    by_contra hpos
    push_neg at hpos
    change jumpExample (xs n) < ((1 / 2 : ℝ) : EReal) at hfn
    rw [jumpExample_of_pos hpos, EReal.coe_lt_coe_iff] at hfn
    change xs n < 1 / 2 at hn
    linarith
  exact ge_of_tendsto hlim (hev.mono fun n hn ↦
    one_le_of_mem_regularSubdifferential_jumpExample hn (hvs n))

/-- **Exercise 13.29**: the counterexample to necessity.  `jumpExample` is subdifferentially
continuous at `0`, and `0 ∈ (∂f)⁻¹(B)` for the compact set `B = {-1, 1}`, but `f` is not
continuous at `0` relative to `(∂f)⁻¹(B)`. -/
theorem jumpExample_counterexample :
    IsSubdifferentiallyContinuousAtPoint jumpExample 0 ∧ IsCompact ({-1, 1} : Set ℝ) ∧
      (0 : ℝ) ∈ subdifferentialPreimage jumpExample {-1, 1} ∧
      ¬ ContinuousWithinAt jumpExample (subdifferentialPreimage jumpExample {-1, 1}) 0 := by
  refine ⟨fun v hv ↦ ⟨hv, fun xs vs hxs hvs hsub ↦ ?_⟩, (Set.toFinite _).isCompact,
    ⟨1, regularSubdifferential_subset_subdifferential _ _
      one_mem_regularSubdifferential_jumpExample, by simp⟩, fun hcont ↦ ?_⟩
  · have hv1 := one_le_of_mem_subdifferential_jumpExample_zero hv
    have hev : ∀ᶠ n in atTop, xs n ≤ 0 := by
      filter_upwards [hvs.eventually (Ioi_mem_nhds (show (0 : ℝ) < v by linarith))] with n hn
      by_contra hpos
      push_neg at hpos
      have := eq_neg_one_of_mem_subdifferential_jumpExample hpos (hsub n)
      change 0 < vs n at hn
      linarith
    rw [jumpExample_of_nonpos le_rfl]
    refine (EReal.tendsto_coe.2 hxs).congr' ?_
    filter_upwards [hev] with n hn
    rw [jumpExample_of_nonpos hn]
  · have hsub : Ioi (0 : ℝ) ⊆ subdifferentialPreimage jumpExample {-1, 1} := fun y hy ↦
      ⟨-1, regularSubdifferential_subset_subdifferential _ _
        (neg_one_mem_regularSubdifferential_jumpExample hy), by simp⟩
    have h0 : Tendsto jumpExample (𝓝[>] (0 : ℝ)) (𝓝 (jumpExample 0)) :=
      (hcont.mono hsub).tendsto
    have h1 : Tendsto jumpExample (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℝ) : EReal)) := by
      have : Tendsto (fun y : ℝ ↦ ((1 - y : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 ((1 - 0 : ℝ) : EReal)) :=
        (EReal.tendsto_coe.2 ((continuous_const.sub continuous_id).tendsto 0)).mono_left
          nhdsWithin_le_nhds
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [jumpExample_of_pos hy]
    have := tendsto_nhds_unique h0 h1
    rw [jumpExample_of_nonpos le_rfl, EReal.coe_eq_coe_iff] at this
    norm_num at this

/-- **Exercise 13.29**: `jumpExample` fails the printed condition because `∂f` is not outer
semicontinuous at `0` (the subgradients `-1 ∈ ∂f(1/ν)` converge to `-1 ∉ ∂f(0)`), although `f` is
subdifferentially continuous there (`forall_continuousWithinAt_subdifferentialPreimage_iff`). -/
theorem not_svOscAt_subdifferential_jumpExample : ¬ SvOscAt (subdifferential jumpExample) 0 := by
  intro hosc
  have h := (forall_continuousWithinAt_subdifferentialPreimage_iff (f := jumpExample) (x := 0)
    ⟨1, regularSubdifferential_subset_subdifferential _ _
      one_mem_regularSubdifferential_jumpExample⟩).2 ⟨jumpExample_counterexample.1, hosc⟩
  exact jumpExample_counterexample.2.2.2
    (h _ jumpExample_counterexample.2.1 jumpExample_counterexample.2.2.1)

end JumpExample

/-! ### Example 13.30 -/

section Example1330

/-- **Example 13.30**: a proper, lsc, convex function is prox-regular (with `ρ = 0`) and
subdifferentially continuous at every point of its domain. -/
theorem prox_regularity_from_convexity [FiniteDimensional ℝ E] {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {x : E}
    (hx : x ∈ effectiveDomain f) :
    IsProxRegularAtPoint f x ∧ IsSubdifferentiallyContinuousAtPoint f x := by
  have hxt : f x ≠ ⊤ := ne_of_lt hx
  have hxb : f x ≠ ⊥ := ne_of_gt (hp.2 x)
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hxt hxb).symm
  set c := (f x).toReal
  -- the subgradient inequality of convex analysis
  have hineq : ∀ y v, v ∈ subdifferential f y → ∀ z,
      f y + ((⟪v, z - y⟫_ℝ : ℝ) : EReal) ≤ f z := by
    intro y v hv z
    obtain ⟨cy, hcy⟩ := hv.1
    have := (mem_subdifferential_iff_of_convex hc hp hcy).1 hv z
    rwa [hcy, ← EReal.coe_add]
  refine ⟨fun v hv ↦ ⟨isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ
    (hl.lowerSemicontinuousOn univ) (mem_univ x) hxb hxt, hv, 1, one_pos, 0, le_rfl,
    fun y v' hv' _ _ _ x' _ ↦ ?_⟩, fun v hv ↦ ⟨hv, fun xs vs hxs hvs hsub ↦ ?_⟩⟩
  · simpa using hineq y v' hv' x'
  · rw [hxc]
    refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
    · rw [← hxc] at ha
      exact hxs.eventually (hl x a ha)
    · have hg : Tendsto (fun n ↦ c - ⟪vs n, x - xs n⟫_ℝ) atTop (𝓝 c) := by
        have h1 : Tendsto (fun n ↦ ⟪vs n, x - xs n⟫_ℝ) atTop (𝓝 ⟪v, x - x⟫_ℝ) :=
          hvs.inner (tendsto_const_nhds.sub hxs)
        rw [sub_self, inner_zero_right] at h1
        simpa using tendsto_const_nhds.sub h1
      filter_upwards [(EReal.tendsto_coe.2 hg).eventually (Iio_mem_nhds ha)] with n hn
      refine lt_of_le_of_lt ?_ hn
      obtain ⟨⟨cn, hcn⟩, -⟩ := hsub n
      have h2 := hineq (xs n) (vs n) (hsub n) x
      rw [hcn, hxc, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
      rw [hcn, EReal.coe_le_coe_iff]
      linarith

end Example1330

/-! ### Exercise 13.31 -/

section Exercise1331

/-- **Exercise 13.31**, property (b): `C` is prox-regular at `x̄` for `v̄` when it is locally
closed at `x̄` with `v̄ ∈ N_C(x̄)` and there are `ε > 0`, `ρ ≥ 0` with
`⟪v, x' - x⟫ ≤ ½ρ‖x' - x‖²` for all `x' ∈ C ∩ IB(x̄, ε)` whenever `v ∈ N_C(x)`,
`‖v - v̄‖ < ε` and `‖x - x̄‖ < ε`. -/
def IsProxRegularSetAt (C : Set E) (x v : E) : Prop :=
  IsLocallyClosedAt C x ∧ v ∈ normalCone C x ∧ ∃ ε > 0, ∃ ρ ≥ 0,
    ∀ y v', v' ∈ normalCone C y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ C ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ ρ / 2 * ‖x' - y‖ ^ 2

/-- `C` is prox-regular at `x̄` when it is prox-regular at `x̄` for every `v̄ ∈ N_C(x̄)`. -/
def IsProxRegularSetAtPoint (C : Set E) (x : E) : Prop :=
  ∀ v ∈ normalCone C x, IsProxRegularSetAt C x v

/-- **Exercise 13.31**: the indicator of a set is subdifferentially continuous at each point of
the set. -/
theorem isSubdifferentiallyContinuousAtPoint_indicatorVA {C : Set E} {x : E} (hx : x ∈ C) :
    IsSubdifferentiallyContinuousAtPoint (indicatorVA C) x := by
  refine fun v hv ↦ ⟨hv, fun xs vs _ _ hsub ↦ ?_⟩
  have hmem : ∀ n, xs n ∈ C := by
    intro n
    obtain ⟨⟨c, hc⟩, -⟩ := hsub n
    by_contra h
    rw [indicatorVA_apply_not_mem h] at hc
    exact EReal.coe_ne_top c hc.symm
  rw [indicatorVA_apply_mem hx]
  exact tendsto_const_nhds.congr fun n ↦ (indicatorVA_apply_mem (hmem n)).symm

/-- **Exercise 13.31**: `δ_C` is prox-regular at `x̄` for `v̄` exactly when `C` satisfies (b). -/
theorem isProxRegularAt_indicatorVA_iff [FiniteDimensional ℝ E] {C : Set E} {x v : E}
    (hx : x ∈ C) : IsProxRegularAt (indicatorVA C) x v ↔ IsProxRegularSetAt C x v := by
  unfold IsProxRegularAt IsProxRegularSetAt
  rw [isLocallyLscAt_indicatorVA_iff hx, subdifferential_indicatorVA]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  simp only [subdifferential_indicatorVA]
  constructor
  · rintro ⟨ε, hε, ρ, hρ, h⟩
    refine ⟨ε, hε, ρ, hρ, fun y v' hv' hvv hyx x' hx' ↦ ?_⟩
    have hy : y ∈ C := hv'.1
    have h1 := h y v' hv' hvv hyx (by
      rw [indicatorVA_apply_mem hy, indicatorVA_apply_mem hx, zero_add]
      exact_mod_cast hε) x' hx'.2
    rw [indicatorVA_apply_mem hy, indicatorVA_apply_mem hx'.1, zero_add,
      ← EReal.coe_zero, EReal.coe_le_coe_iff] at h1
    linarith
  · rintro ⟨ε, hε, ρ, hρ, h⟩
    refine ⟨ε, hε, ρ, hρ, fun y v' hv' hvv hyx _ x' hx' ↦ ?_⟩
    have hy : y ∈ C := hv'.1
    by_cases hx'C : x' ∈ C
    · have h1 := h y v' hv' hvv hyx x' ⟨hx'C, hx'⟩
      rw [indicatorVA_apply_mem hy, indicatorVA_apply_mem hx'C, zero_add, ← EReal.coe_zero,
        EReal.coe_le_coe_iff]
      linarith
    · rw [indicatorVA_apply_not_mem hx'C]
      exact le_top

/-- **Exercise 13.31**, both assertions together. -/
theorem prox_regularity_of_sets [FiniteDimensional ℝ E] {C : Set E} {x v : E} (hx : x ∈ C) :
    IsSubdifferentiallyContinuousAtPoint (indicatorVA C) x ∧
      (IsProxRegularAt (indicatorVA C) x v ↔ IsProxRegularSetAt C x v) :=
  ⟨isSubdifferentiallyContinuousAtPoint_indicatorVA hx, isProxRegularAt_indicatorVA_iff hx⟩

/-- The remark after 13.31: closed convex sets are prox-regular at each of their points. -/
theorem isProxRegularSetAtPoint_of_convex [FiniteDimensional ℝ E] {C : Set E} {x : E}
    (hconv : Convex ℝ C) (hcl : IsClosed C) (hx : x ∈ C) : IsProxRegularSetAtPoint C x := by
  intro v hv
  have hp : IsProper (indicatorVA C) :=
    ⟨⟨x, by rw [indicatorVA_apply_mem hx]; exact EReal.zero_lt_top⟩, fun y ↦ by
      unfold indicatorVA
      split_ifs <;> simp⟩
  have hc : Convex ℝ (epigraph (indicatorVA C)) := by
    rw [epigraph_indicatorVA]
    exact hconv.prod (convex_Ici 0)
  have hdom : x ∈ effectiveDomain (indicatorVA C) := by
    change indicatorVA C x < ⊤
    rw [indicatorVA_apply_mem hx]
    exact EReal.zero_lt_top
  have := (prox_regularity_from_convexity hp (lowerSemicontinuous_indicatorVA hcl) hc hdom).1 v
    (by rwa [subdifferential_indicatorVA])
  exact (isProxRegularAt_indicatorVA_iff hx).1 this

end Exercise1331

end RW
