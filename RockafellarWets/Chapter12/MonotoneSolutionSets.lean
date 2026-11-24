/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Nonempty bounded solution sets of monotone generalized equations

Theorem 12.51(b) and Exercise 12.52(b), completing the parts (a) proved in
`MonotoneVariationalInequalities`.

For maximal monotone `T`, the solution set `T⁻¹(0)` is nonempty and bounded if
and only if every nonzero `w ∈ (dom T)∞` admits `v ∈ rge T` with `⟪v, w⟫ > 0`;
here `(dom T)∞` is the horizon cone of Chapter 3, and for any `a ∈ rint(dom T)`
it consists of the `w` with `a + τw ∈ dom T` for all `τ > 0`
(`SvMaximalMonotone.horizonCone_svDom_eq`, from 12.37, 12.41 and 3.6).

The necessity uses 12.38 and 12.41 for `T⁻¹`: `T⁻¹(0)` is bounded and nonempty
exactly when `0 ∈ int(rge T)`.  For the sufficiency the book appeals to 12.38,
8.29, 12.47 and 12.9; here a direct argument is used instead.  The points
`xν = (I + νT)⁻¹(a)` carry `vν = ν⁻¹(a - xν) ∈ T(xν)`.  If they have a bounded
subsequence, a cluster point solves `T(x) ∋ 0`.  Otherwise the normalized
directions `(xν - a)/|xν - a|` cluster at a unit `w ∈ (cl dom T)∞ = (dom T)∞`,
and the monotonicity inequality against a pair `(x̂, v̂)` with `⟪v̂, w⟫ > 0` fails in
the limit.  Boundedness follows from a nonzero horizon direction of the closed
convex set `T⁻¹(0)`, which would lie in `(dom T)∞`.
-/

import RockafellarWets.Chapter12.MonotoneVariationalInequalities
import RockafellarWets.Chapter12.MonotoneContinuity
import RockafellarWets.Chapter3.HorizonCones

open Set Filter Topology Metric Bornology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 12.51**, the description of `(dom T)∞`: for any `a ∈ rint(dom T)`,
`(dom T)∞` consists of the vectors `w` with `a + τw ∈ dom T` for all `τ > 0`. -/
theorem SvMaximalMonotone.horizonCone_svDom_eq {T : E → Set E} (hT : SvMaximalMonotone T)
    {a : E} (ha : a ∈ intrinsicInterior ℝ (svDom T)) :
    horizonCone (svDom T) = {w | ∀ τ : ℝ, 0 < τ → a + τ • w ∈ svDom T} := by
  have hD := hT.convex_closure_svDom
  have ha' : a ∈ intrinsicInterior ℝ (closure (svDom T)) := hT.intrinsicInterior_svDom ▸ ha
  have haD : a ∈ closure (svDom T) := intrinsicInterior_subset ha'
  ext w
  constructor
  · intro hw τ hτ
    have hw' : w ∈ horizonCone (closure (svDom T)) := by rwa [horizonCone_closure]
    have h2 : (2 * τ) • w + a ∈ closure (svDom T) := by
      have := smul_add_mem_closure_of_mem_horizonCone hD (by rwa [closure_closure]) hw'
        (by positivity : (0 : ℝ) ≤ 2 * τ)
      rwa [closure_closure] at this
    have hmid := RW.Convex.add_smul_sub_mem_intrinsicInterior hD (by rwa [closure_closure]) ha'
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    have e : (2 * τ) • w + a + (1 / 2 : ℝ) • (a - ((2 * τ) • w + a)) = a + τ • w := by module
    rw [e] at hmid
    exact hT.intrinsicInterior_closure_svDom_subset hmid
  · intro hw
    refine mem_horizonCone_of_forall_smul_add_mem (x := a) fun τ hτ ↦ ?_
    rcases hτ.eq_or_lt with rfl | hτ
    · rw [zero_smul, zero_add]
      exact intrinsicInterior_subset ha
    · rw [add_comm]
      exact hw τ hτ

/-- Necessity in **Theorem 12.51(b)**: a nonempty bounded `T⁻¹(0)` forces
`0 ∈ int(rge T)` (12.38 and 12.41 for `T⁻¹`), so every nonzero `w` has
`⟪v, w⟫ > 0` for some `v ∈ rge T`. -/
theorem SvMaximalMonotone.exists_inner_pos_of_isBounded {T : E → Set E}
    (hT : SvMaximalMonotone T) (hne : (svInv T 0).Nonempty) (hb : IsBounded (svInv T 0))
    {w : E} (hw : w ≠ 0) : ∃ v ∈ svRange T, 0 < ⟪v, w⟫_ℝ := by
  have hTi := hT.inv
  have h0 : (0 : E) ∈ svDom (svInv T) := hne
  have hlb : SvLocallyBoundedAt (svInv T) 0 := (hTi.svLocallyBoundedAt_iff_isBounded h0).2 hb
  have hfr := (hTi.svLocallyBoundedAt_iff_notMem_frontier).1 hlb
  have hint : (0 : E) ∈ interior (svDom (svInv T)) := by
    have hcl : (0 : E) ∈ closure (closure (svDom (svInv T))) :=
      subset_closure (subset_closure h0)
    have : (0 : E) ∈ interior (closure (svDom (svInv T))) := by
      rw [← closure_diff_frontier]
      exact ⟨hcl, hfr⟩
    exact interior_maximal hTi.interior_closure_svDom_subset isOpen_interior this
  rw [svDom_svInv] at hint
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 hint
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  refine ⟨(r / (2 * ‖w‖)) • w, interior_subset (hball ?_), ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
    linarith
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    positivity

/-- Sufficiency in **Theorem 12.51(b)**, nonemptiness. -/
theorem SvMaximalMonotone.solutions_nonempty_of_forall_horizon {T : E → Set E}
    (hT : SvMaximalMonotone T)
    (h : ∀ w ∈ horizonCone (svDom T), w ≠ 0 → ∃ v ∈ svRange T, 0 < ⟪v, w⟫_ℝ) :
    (svInv T 0).Nonempty := by
  obtain ⟨a, ha⟩ := hT.svDom_nonempty
  set D := closure (svDom T) with hDdef
  have hD : Convex ℝ D := hT.convex_closure_svDom
  have haD : a ∈ D := subset_closure ha
  let lam : ℕ → ℝ := fun n ↦ n + 1
  have hlam : ∀ n, 0 < lam n := fun n ↦ by positivity
  let xs : ℕ → E := fun n ↦ resolventMap T (lam n) a
  let vs : ℕ → E := fun n ↦ (lam n)⁻¹ • (a - xs n)
  have hvs : ∀ n, vs n ∈ T (xs n) := by
    intro n
    obtain ⟨v, hv, hxv⟩ := (hT.resolventMap_eq_iff (z := a) (x := xs n) (hlam n)).1 rfl
    have e : vs n = v := by
      simp only [vs]
      rw [← hxv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (hlam n).ne', one_smul]
    rw [e]
    exact hv
  have hxsD : ∀ n, xs n ∈ D := fun n ↦ subset_closure ⟨_, hvs n⟩
  by_cases hbdd : ∃ R, ∃ᶠ n in atTop, ‖xs n‖ ≤ R
  · -- a bounded subsequence gives a solution
    obtain ⟨R, hR⟩ := hbdd
    obtain ⟨ψ, hψ, hψR⟩ := extraction_of_frequently_atTop hR
    obtain ⟨xb, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : E))
      (r := R)) (x := fun k ↦ xs (ψ k)) (fun k ↦ by
        rw [mem_closedBall_zero_iff]; exact hψR k)
    have hidx : Tendsto (fun k ↦ ψ (φ k)) atTop atTop :=
      hψ.tendsto_atTop.comp hφ.tendsto_atTop
    have hv0 : Tendsto (fun k ↦ vs (ψ (φ k))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hbound : ∀ k, ‖vs (ψ (φ k))‖ ≤ (‖a‖ + R) * (1 / ((ψ (φ k) : ℝ) + 1)) := by
        intro k
        simp only [vs, lam]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (by positivity)), one_div, mul_comm]
        gcongr
        exact (norm_sub_le _ _).trans (by linarith [hψR (φ k)])
      refine squeeze_zero (fun _ ↦ norm_nonneg _) hbound ?_
      have : Tendsto (fun k ↦ (‖a‖ + R) * (1 / ((ψ (φ k) : ℝ) + 1))) atTop
          (𝓝 ((‖a‖ + R) * 0)) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hidx).const_mul _
      rwa [mul_zero] at this
    exact ⟨xb, hT.isClosed_svGraph.mem_of_tendsto (hlim.prodMk_nhds hv0)
      (Eventually.of_forall fun k ↦ hvs (ψ (φ k)))⟩
  · -- otherwise the normalized directions produce a contradiction
    push_neg at hbdd
    exfalso
    have hxinf : Tendsto (fun n ↦ ‖xs n‖) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro R
      exact (hbdd R).mono fun n hn ↦ hn.le
    have hdinf : Tendsto (fun n ↦ ‖xs n - a‖) atTop atTop := by
      refine tendsto_atTop_mono (fun n ↦ ?_) (tendsto_atTop_add_const_right _ (-‖a‖) hxinf)
      have := norm_sub_norm_le (xs n) a
      linarith
    obtain ⟨φ, w, hφ, hw1, hwlim⟩ := exists_subseq_tendsto_normalize hdinf
    have hφto : Tendsto φ atTop atTop := hφ.tendsto_atTop
    set d : ℕ → ℝ := fun k ↦ ‖xs (φ k) - a‖ with hd
    have hdto : Tendsto d atTop atTop := hdinf.comp hφto
    -- `w` is a horizon direction of `dom T`
    have hwD : w ∈ horizonCone (svDom T) := by
      rw [← horizonCone_closure]
      refine mem_horizonCone_of_forall_smul_add_mem (x := a) fun τ hτ ↦ ?_
      have hconv : Tendsto (fun k ↦ τ • ((d k)⁻¹ • (xs (φ k) - a)) + a) atTop
          (𝓝 (τ • w + a)) := (hwlim.const_smul τ).add_const a
      refine isClosed_closure.mem_of_tendsto hconv ?_
      filter_upwards [hdto.eventually_ge_atTop (max τ 1)] with k hk
      have hdpos : 0 < d k := lt_of_lt_of_le one_pos ((le_max_right τ 1).trans hk)
      have ht1 : τ / d k ≤ 1 := (div_le_one hdpos).2 ((le_max_left τ 1).trans hk)
      have ht0 : 0 ≤ τ / d k := div_nonneg hτ hdpos.le
      have hmem := hD haD (hxsD (φ k)) (sub_nonneg.2 ht1) ht0 (by ring)
      convert hmem using 1
      rw [smul_smul, ← div_eq_mul_inv, smul_sub, sub_smul, one_smul]
      abel
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hw1
      exact zero_ne_one hw1
    obtain ⟨vh, ⟨xh, hvh⟩, hpos⟩ := h w hwD hw0
    -- the monotonicity inequality in the limit
    have hev : ∀ᶠ k in atTop, ⟪vh, (d k)⁻¹ • (xs (φ k) - xh)⟫_ℝ ≤ 0 := by
      filter_upwards [hdto.eventually_ge_atTop (max ‖a - xh‖ 1)] with k hk
      have hdpos : 0 < d k := lt_of_lt_of_le one_pos ((le_max_right _ 1).trans hk)
      have hdge : ‖a - xh‖ ≤ d k := (le_max_left _ 1).trans hk
      have hmono := hT.1 hvh (hvs (φ k))
      have hx : ⟪xs (φ k) - a, xs (φ k) - xh⟫_ℝ ≥ 0 := by
        have e : xs (φ k) - xh = (xs (φ k) - a) + (a - xh) := by abel
        rw [e, inner_add_right, real_inner_self_eq_norm_sq]
        have := real_inner_le_norm (xs (φ k) - a) (a - xh)
        have h' := neg_le_of_abs_le (abs_real_inner_le_norm (xs (φ k) - a) (a - xh))
        change ‖xs (φ k) - a‖ ^ 2 + _ ≥ 0
        nlinarith [norm_nonneg (xs (φ k) - a)]
      have hvsk : ⟪vs (φ k), xs (φ k) - xh⟫_ℝ ≤ 0 := by
        simp only [vs]
        rw [real_inner_smul_left, ← neg_sub (xs (φ k)) a, inner_neg_left]
        have := (inv_pos.2 (hlam (φ k)))
        nlinarith
      rw [inner_sub_left] at hmono
      rw [real_inner_smul_right]
      have : ⟪vh, xs (φ k) - xh⟫_ℝ ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hdpos.le) this
    have hlim : Tendsto (fun k ↦ ⟪vh, (d k)⁻¹ • (xs (φ k) - xh)⟫_ℝ) atTop (𝓝 ⟪vh, w⟫_ℝ) := by
      have hinv : Tendsto (fun k ↦ (d k)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hdto
      have : Tendsto (fun k ↦ (d k)⁻¹ • (xs (φ k) - a) + (d k)⁻¹ • (a - xh)) atTop
          (𝓝 (w + (0 : ℝ) • (a - xh))) := hwlim.add (hinv.smul tendsto_const_nhds)
      rw [zero_smul, add_zero] at this
      refine tendsto_const_nhds.inner (this.congr fun k ↦ ?_)
      rw [← smul_add]
      congr 1
      abel
    have := le_of_tendsto hlim hev
    linarith

/-- Sufficiency in **Theorem 12.51(b)**, boundedness. -/
theorem SvMaximalMonotone.solutions_bounded_of_forall_horizon {T : E → Set E}
    (hT : SvMaximalMonotone T)
    (h : ∀ w ∈ horizonCone (svDom T), w ≠ 0 → ∃ v ∈ svRange T, 0 < ⟪v, w⟫_ℝ) :
    IsBounded (svInv T 0) := by
  by_contra hb
  obtain ⟨xb, hxb⟩ := hT.solutions_nonempty_of_forall_horizon h
  have hcl := hT.isClosed_svInv_apply 0
  have hcv := hT.convex_svInv_apply 0
  rw [isBounded_iff_horizonCone_eq_singleton_zero] at hb
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ horizonCone (svInv T 0), w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hb (Subset.antisymm (fun w hw ↦ hcon w hw) (by simp))
  have hray : ∀ τ : ℝ, 0 ≤ τ → τ • w + xb ∈ svInv T 0 := fun τ hτ ↦
    smul_add_mem_of_mem_horizonCone hcv hcl hxb hw hτ
  have hwD : w ∈ horizonCone (svDom T) :=
    mem_horizonCone_of_forall_smul_add_mem (x := xb) fun τ hτ ↦ ⟨0, hray τ hτ⟩
  obtain ⟨vh, ⟨xh, hvh⟩, hpos⟩ := h w hwD hw0
  set τ := (|⟪vh, xb - xh⟫_ℝ| + 1) / ⟪vh, w⟫_ℝ with hτdef
  have hτ : 0 ≤ τ := by positivity
  have hmono := hT.1 hvh (hray τ hτ)
  rw [zero_sub, inner_neg_left, show τ • w + xb - xh = τ • w + (xb - xh) by abel,
    inner_add_right, real_inner_smul_right] at hmono
  have hτw : τ * ⟪vh, w⟫_ℝ = |⟪vh, xb - xh⟫_ℝ| + 1 := by
    rw [hτdef]; field_simp
  have := neg_abs_le ⟪vh, xb - xh⟫_ℝ
  linarith

/-- **Theorem 12.51(b)**: for maximal monotone `T`, the solution set `T⁻¹(0)`
is nonempty and bounded if and only if every nonzero `w ∈ (dom T)∞` admits some
`v ∈ rge T` with `⟪v, w⟫ > 0`. -/
theorem SvMaximalMonotone.solutions_nonempty_bounded_iff {T : E → Set E}
    (hT : SvMaximalMonotone T) :
    ((svInv T 0).Nonempty ∧ IsBounded (svInv T 0)) ↔
      ∀ w ∈ horizonCone (svDom T), w ≠ 0 → ∃ v ∈ svRange T, 0 < ⟪v, w⟫_ℝ :=
  ⟨fun ⟨hne, hb⟩ _ _ hw ↦ hT.exists_inner_pos_of_isBounded hne hb hw,
    fun h ↦ ⟨hT.solutions_nonempty_of_forall_horizon h, hT.solutions_bounded_of_forall_horizon h⟩⟩

/-- **Theorem 12.51 (solutions to a monotone generalized equation)**,
collected: for maximal monotone `T`, the solution set `T⁻¹(0)` is closed and
convex; (a) `T⁻¹(0) ∩ ρB ≠ ∅` if `⟪v, x⟫ ≥ 0` whenever `v ∈ T(x)`, `|x| > ρ`;
(b) `T⁻¹(0)` is nonempty and bounded if and only if every nonzero
`w ∈ (dom T)∞` has some `v ∈ rge T` with `⟪v, w⟫ > 0`, where for any
`a ∈ rint(dom T)` the cone `(dom T)∞` consists of the `w` with `a + τw ∈ dom T`
for all `τ > 0`. -/
theorem solutions_to_monotone_generalized_equation {T : E → Set E} (hT : SvMaximalMonotone T) :
    IsClosed (svInv T 0) ∧ Convex ℝ (svInv T 0) ∧
      (∀ ρ : ℝ, 0 ≤ ρ → (∀ x v, v ∈ T x → ρ < ‖x‖ → 0 ≤ ⟪v, x⟫_ℝ) →
        (svInv T 0 ∩ closedBall 0 ρ).Nonempty) ∧
      (((svInv T 0).Nonempty ∧ IsBounded (svInv T 0)) ↔
        ∀ w ∈ horizonCone (svDom T), w ≠ 0 → ∃ v ∈ svRange T, 0 < ⟪v, w⟫_ℝ) ∧
      ∀ a ∈ intrinsicInterior ℝ (svDom T),
        horizonCone (svDom T) = {w | ∀ τ : ℝ, 0 < τ → a + τ • w ∈ svDom T} :=
  ⟨(hT.solutions_generalized_equation).1, (hT.solutions_generalized_equation).2.1,
    (hT.solutions_generalized_equation).2.2, hT.solutions_nonempty_bounded_iff,
    fun _ ha ↦ hT.horizonCone_svDom_eq ha⟩

omit [FiniteDimensional ℝ E] in
/-- The domain of `F + N_C` is `C`. -/
theorem svDom_viMapping (C : Set E) (F : E → E) : svDom (viMapping C F) = C := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    exact mem_of_mem_viMapping hv
  · intro hx
    exact ⟨F x, apply_mem_viMapping hx⟩

/-- **Exercise 12.52 (existence of solutions to variational inequalities)**:
for a nonempty closed convex `C`, `F` continuous and monotone relative to `C`, and
`a ∈ C`, with `X_{C,F}` the solution set of the variational inequality: (a)
`X_{C,F} ∩ B(a, ρ) ≠ ∅` if `⟪F(x), x - a⟫ ≥ 0` for `x ∈ C`, `|x - a| > ρ`; (b)
`X_{C,F}` is nonempty and bounded if and only if every nonzero `w ∈ C∞` has some
`x ∈ C` with `⟪F(x), w⟫ > 0`. -/
theorem existence_of_solutions_to_variational_inequalities {C : Set E} {F : E → E}
    (hCc : IsClosed C) (hC : Convex ℝ C) (hCne : C.Nonempty) (hFc : ContinuousOn F C)
    (hFm : MonotoneRelativeTo F C) {a : E} (ha : a ∈ C) :
    (∀ ρ : ℝ, 0 ≤ ρ → (∀ x ∈ C, ρ < ‖x - a‖ → 0 ≤ ⟪F x, x - a⟫_ℝ) →
        ∃ x ∈ closedBall a ρ, IsVariationalSolution C F x) ∧
      (({x | IsVariationalSolution C F x}.Nonempty ∧ IsBounded {x | IsVariationalSolution C F x}) ↔
        ∀ w ∈ horizonCone C, w ≠ 0 → ∃ x ∈ C, 0 < ⟪F x, w⟫_ℝ) := by
  have hT := svMaximalMonotone_viMapping hCc hC hCne hFc hFm
  have hsol : {x | IsVariationalSolution C F x} = svInv (viMapping C F) 0 := by
    ext x
    exact isVariationalSolution_iff_zero_mem_viMapping
  refine ⟨fun ρ hρ h ↦ exists_isVariationalSolution_mem_closedBall hCc hC hFc hFm ha hρ h, ?_⟩
  rw [hsol, hT.solutions_nonempty_bounded_iff, svDom_viMapping]
  refine forall₂_congr fun w hw ↦ imp_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨v, ⟨x, hv⟩, hpos⟩
    have hx := mem_of_mem_viMapping hv
    refine ⟨x, hx, ?_⟩
    -- `w` is tangent to `C` at `x`, so normals have `⟪n, w⟫ ≤ 0`
    have hn := (mem_normalCone_iff_of_convex hC hx).1 (mem_viMapping.1 hv) (x + w)
      (by simpa [add_comm] using smul_add_mem_of_mem_horizonCone hC hCc hx hw zero_le_one)
    rw [add_sub_cancel_left] at hn
    have e : ⟪v, w⟫_ℝ = ⟪F x, w⟫_ℝ + ⟪v - F x, w⟫_ℝ := by
      rw [← inner_add_left]; congr 1; abel
    linarith
  · rintro ⟨x, hx, hpos⟩
    exact ⟨F x, ⟨x, apply_mem_viMapping hx⟩, hpos⟩

end RW
