/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Structure of maximal monotone mappings

Theorem 12.67.

`E` is `singleValuedLocus T`, the points of `int(dom T)` where `T` is
single-valued, and `T₀` is `limitMappingOn T E₀`.  The first assertions follow the
book: `T` is continuous on `E` (12.63(c)), and `cl E₀ = cl(dom T)` because the
differentiability points are dense in `int(dom T)` (12.66) and a convex set with
nonempty interior is the closure of its interior.

For `T(x̄) ⊂ cl con T₀(x̄) + N_D(x̄)`, `D = cl(dom T)`, the key step is: whenever
`x̄ + tw ∈ int D` for some `t > 0`, points `xν ∈ E₀` close to `x̄ + τν w` converge
to `x̄` from the direction `w`, so by 12.63(b) `T(xν)` has a cluster point, which
lies in `T₀(x̄)` and, by 12.63(a), maximizes `⟪·, w⟫` over `T(x̄)`.  The book
uses this only at directions `w` where the support function `σ_{T(x̄)}` is
differentiable, found by Rademacher's theorem (9.60); since 12.63(a) puts every
cluster point in the argmax, the step holds at every interior tangent direction,
and neither Rademacher's theorem nor the support function calculus (8.24, 8.25,
11.4, 11.5, 2.36) is needed.  The sum `cl con T₀(x̄) + N_D(x̄)` is closed (as with
3.12) because `N_D(x̄)` is pointed when `int D ≠ ∅`; the recession direction of
an unbounded sequence in `cl con T₀(x̄) ⊂ T(x̄)` is a normal to `D` by the
monotonicity inequality.  A vector separating a point of `T(x̄)` from the sum lies
in `N_D(x̄)* = T_D(x̄)` (6.9), and a small perturbation into `int T_D(x̄)` together
with the key step gives a contradiction.
-/

import RockafellarWets.Chapter12.GenericSingleValuedness

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set `E` of Theorem 12.67: the points of `int(dom T)` at which `T` is
single-valued. -/
def singleValuedLocus (T : E → Set E) : Set E :=
  {x ∈ interior (svDom T) | ∃ v, T x = {v}}

/-- The mapping `T₀` of Theorem 12.67: `v ∈ T₀(x)` when `T(xν) ∋ vν → v` for some
`xν → x` with `xν ∈ E₀`. -/
def limitMappingOn (T : E → Set E) (E0 : Set E) (x : E) : Set E :=
  {v | ∃ xs vs : ℕ → E, (∀ n, xs n ∈ E0) ∧ (∀ n, vs n ∈ T (xs n)) ∧
    Tendsto xs atTop (𝓝 x) ∧ Tendsto vs atTop (𝓝 v)}

omit [InnerProductSpace ℝ E] in
/-- `T₀ ⊂ T` when the graph of `T` is closed. -/
theorem limitMappingOn_subset {T : E → Set E} (hT : IsClosed (svGraph T)) (E0 : Set E) (x : E) :
    limitMappingOn T E0 x ⊆ T x := by
  rintro v ⟨xs, vs, -, hvs, hxs, hvl⟩
  exact hT.mem_of_tendsto (hxs.prodMk_nhds hvl) (Eventually.of_forall hvs)

omit [InnerProductSpace ℝ E] in
theorem svDom_limitMappingOn_subset_closure (T : E → Set E) (E0 : Set E) :
    svDom (limitMappingOn T E0) ⊆ closure E0 := by
  rintro x ⟨v, xs, vs, hxs, -, hxl, -⟩
  exact mem_closure_of_tendsto hxl (Eventually.of_forall hxs)

variable [FiniteDimensional ℝ E]

/-- The differentiability points of `T` lie in `E`. -/
theorem setOf_svDifferentiableAt_subset_singleValuedLocus (T : E → Set E) :
    {x | SvDifferentiableAt T x} ⊆ singleValuedLocus T :=
  fun _ hx ↦ ⟨SvDifferentiableAt.mem_interior_svDom hx, SvDifferentiableAt.exists_eq_singleton hx⟩

/-- The differentiability points of a maximal monotone `T` are dense in `E`
(12.66), so they qualify as `E₀` in 12.67. -/
theorem SvMaximalMonotone.singleValuedLocus_subset_closure_svDifferentiableAt {T : E → Set E}
    (hT : SvMaximalMonotone T) : singleValuedLocus T ⊆ closure {x | SvDifferentiableAt T x} :=
  fun _ hx ↦ closure_mono (fun _ hy ↦ hy.2)
    (hT.interior_svDom_subset_closure_svDifferentiableAt hx.1)

/-- A dense subset `E₀` of `E` is dense in `int(dom T)` (12.66). -/
theorem SvMaximalMonotone.interior_svDom_subset_closure {T : E → Set E}
    (hT : SvMaximalMonotone T) {E0 : Set E} (hdense : singleValuedLocus T ⊆ closure E0) :
    interior (svDom T) ⊆ closure E0 := by
  refine (hT.interior_svDom_subset_closure_svDifferentiableAt).trans
    (closure_minimal (fun x hx ↦ hdense ⟨hx.1, hx.2.exists_eq_singleton⟩) isClosed_closure)

/-- **Theorem 12.67**: `T₀` agrees with `T` on `E`, by the continuity of `T` at the
points of `E` (12.63(c)). -/
theorem SvMaximalMonotone.limitMappingOn_eq {T : E → Set E} (hT : SvMaximalMonotone T)
    {E0 : Set E} (hE0 : E0 ⊆ singleValuedLocus T) (hdense : singleValuedLocus T ⊆ closure E0)
    {x : E} (hx : x ∈ singleValuedLocus T) : limitMappingOn T E0 x = T x := by
  refine Subset.antisymm (limitMappingOn_subset hT.isClosed_svGraph E0 x) ?_
  obtain ⟨v, hTx⟩ := hx.2
  have hcont : SvContinuousAt T x :=
    (hT.svContinuousAt_iff_singleton ⟨v, hTx ▸ mem_singleton v⟩).1.2 ⟨v, hTx⟩
  rw [hTx, singleton_subset_iff]
  obtain ⟨xs, hxs, hxl⟩ := mem_closure_iff_seq_limit.1 (hdense hx)
  have hsv : ∀ n, ∃ w, T (xs n) = {w} := fun n ↦ (hE0 (hxs n)).2
  choose ws hws using hsv
  refine ⟨xs, ws, hxs, fun n ↦ (hws n).symm ▸ mem_singleton _, hxl, ?_⟩
  have hinner := hcont.2 (hTx ▸ mem_singleton v)
  refine tendsto_def.2 fun V hV ↦ ?_
  filter_upwards [hxl.eventually (hinner V hV)] with n hn
  obtain ⟨w, hw, hwV⟩ := hn
  rw [hws n, mem_singleton_iff] at hw
  rw [mem_preimage, ← hw]
  exact hwV

/-- **Theorem 12.67**: `cl E₀ = cl(dom T)`, a convex set with nonempty interior
being the closure of its interior. -/
theorem SvMaximalMonotone.closure_eq_closure_svDom {T : E → Set E} (hT : SvMaximalMonotone T)
    (hint : (interior (svDom T)).Nonempty) {E0 : Set E} (hE0 : E0 ⊆ singleValuedLocus T)
    (hdense : singleValuedLocus T ⊆ closure E0) : closure E0 = closure (svDom T) := by
  refine Subset.antisymm (closure_mono fun x hx ↦ interior_subset (hE0 hx).1) ?_
  have hconv := hT.convex_closure_svDom
  have hintD : (interior (closure (svDom T))).Nonempty :=
    hint.mono (interior_mono subset_closure)
  have hcl := hconv.closure_interior_eq_closure_of_nonempty_interior hintD
  rw [closure_closure] at hcl
  rw [← hcl]
  refine closure_minimal (fun x hx ↦ hT.interior_svDom_subset_closure hdense ?_) isClosed_closure
  exact interior_maximal (hT.interior_closure_svDom_subset) isOpen_interior hx

/-- The key step in the proof of 12.67: if `x̄ ∈ dom T` and `x̄ + tw ∈ int(cl(dom T))`
for some `t > 0`, then the maximum of `⟪·, w⟫` over `T(x̄)` is attained at a point
of `T₀(x̄)`.  Points `xν ∈ E₀` approximating `x̄ + τν w` converge to `x̄` from the
direction `w`, and a cluster point of `T(xν)` exists by 12.63(b) and lies in the
argmax by 12.63(a).  (The book uses this only at points `w` where `σ_{T(x̄)}` is
differentiable; it holds for every such `w`.) -/
theorem SvMaximalMonotone.exists_mem_limitMappingOn_argmax {T : E → Set E}
    (hT : SvMaximalMonotone T) {E0 : Set E} (hE0 : E0 ⊆ singleValuedLocus T)
    (hdense : singleValuedLocus T ⊆ closure E0) {xbar w : E} (hxbar : xbar ∈ svDom T)
    (hw : w ∈ radialCone (interior (closure (svDom T))) xbar) :
    ∃ vbar ∈ limitMappingOn T E0 xbar, ∀ v ∈ T xbar, ⟪v, w⟫_ℝ ≤ ⟪vbar, w⟫_ℝ := by
  set D := closure (svDom T) with hDdef
  have hconv : Convex ℝ D := hT.convex_closure_svDom
  obtain ⟨t, ht, htD⟩ := hw
  set τ : ℕ → ℝ := fun n ↦ t / ((n : ℝ) + 2) with hτdef
  have hτ0 : ∀ n, 0 < τ n := fun n ↦ by positivity
  have hτl : Tendsto τ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop)
  -- the points `x̄ + τν w` lie in `int D ⊆ cl E₀`
  have hy : ∀ n, xbar + τ n • w ∈ closure E0 := by
    intro n
    have hseg := hconv.openSegment_closure_interior_subset_interior
      (subset_closure (subset_closure hxbar)) htD
    have hmem : xbar + τ n • w ∈ interior D := by
      apply hseg
      refine ⟨1 - 1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 2), ?_, by positivity, by ring, ?_⟩
      · have : 1 / ((n : ℝ) + 2) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith [n.cast_nonneg (α := ℝ)]
        linarith
      · simp only [τ, smul_add, smul_smul, ← add_assoc, ← add_smul]
        congr 1
        · rw [show 1 - 1 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 2) = 1 by ring, one_smul]
        · congr 1
          ring
    exact hT.interior_svDom_subset_closure hdense
      (interior_maximal hT.interior_closure_svDom_subset isOpen_interior hmem)
  -- approximations from `E₀`
  have happrox : ∀ n, ∃ z ∈ E0, dist (xbar + τ n • w) z < τ n / ((n : ℝ) + 1) :=
    fun n ↦ Metric.mem_closure_iff.1 (hy n) _ (by have := hτ0 n; positivity)
  choose xs hxs hdist using happrox
  have hdir : ConvergesFromDirection xs xbar w := by
    refine ⟨τ, hτ0, hτl, ?_⟩
    have herr : Tendsto (fun n ↦ (τ n)⁻¹ • (xs n - (xbar + τ n • w))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hτ0 n).le), ← dist_eq_norm, dist_comm,
        inv_mul_le_iff₀ (hτ0 n)]
      have := hdist n
      rw [lt_div_iff₀ (by positivity)] at this
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      exact this.le
    have heq : ∀ n, (τ n)⁻¹ • (xs n - xbar) = (τ n)⁻¹ • (xs n - (xbar + τ n • w)) + w := by
      intro n
      rw [← sub_sub, smul_sub (τ n)⁻¹ (xs n - xbar), inv_smul_smul₀ (hτ0 n).ne']
      abel
    simp only [heq]
    simpa using herr.add_const w
  have hdom : ∀ n, xs n ∈ svDom T := fun n ↦ interior_subset (hE0 (hxs n)).1
  obtain ⟨-, -, hne⟩ := hT.bounded_of_convergesFromDirection_of_mem_radialCone hdom hxbar hdir
    ⟨t, ht, htD⟩
  obtain ⟨-, hsub, -⟩ := hT.limsup_subset_argmax hdir hne
  obtain ⟨vbar, hvbar⟩ := hne
  obtain ⟨φ, vs, hφ, hvs, hvl⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hvbar
  exact ⟨vbar, ⟨xs ∘ φ, vs, fun k ↦ hxs _, hvs, hdir.tendsto.comp hφ.tendsto_atTop, hvl⟩,
    (hsub hvbar).2⟩

omit [FiniteDimensional ℝ E] in
/-- The normal cone to a convex set with nonempty interior is pointed. -/
theorem eq_zero_of_mem_normalCone_of_neg_mem {D : Set E} (hD : Convex ℝ D)
    (hint : (interior D).Nonempty) {x e : E} (hx : x ∈ D) (he : e ∈ normalCone D x)
    (hne : -e ∈ normalCone D x) : e = 0 := by
  rw [normalCone_eq_of_convex hD hx] at he hne
  obtain ⟨a, ha⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior a ha
  have hzero : ∀ y ∈ D, ⟪e, y - x⟫_ℝ = 0 := fun y hy ↦ by
    have h1 := he y hy
    have h2 := hne y hy
    rw [inner_neg_left] at h2
    linarith
  set s := r / (2 * (‖e‖ + 1)) with hs
  have hs0 : 0 < s := by positivity
  have hmem : a + s • e ∈ D := by
    apply interior_subset
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le, hs,
      div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg e]
  have h1 := hzero _ hmem
  rw [show a + s • e - x = (a - x) + s • e by abel, inner_add_right, hzero a (interior_subset ha),
    zero_add, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖e‖ ^ 2 = 0 := (mul_eq_zero.1 h1).resolve_left hs0.ne'
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

omit [FiniteDimensional ℝ E] in
/-- `cl con T₀(x) ⊂ T(x)`, the values of a maximal monotone mapping being closed and
convex (12.8). -/
theorem SvMaximalMonotone.closure_convexHull_limitMappingOn_subset {T : E → Set E}
    (hT : SvMaximalMonotone T) (E0 : Set E) (x : E) :
    closure (convexHull ℝ (limitMappingOn T E0 x)) ⊆ T x :=
  closure_minimal (convexHull_min (limitMappingOn_subset hT.isClosed_svGraph E0 x)
    (hT.convex_apply x)) (hT.isClosed_apply x)

/-- **Theorem 12.67**, the easy inclusion `cl con T₀(x) + N_D(x) ⊂ T(x)` with
`D = cl(dom T)`: adding a normal vector to `D` keeps the monotonicity inequality
against `gph T`, so maximality applies. -/
theorem SvMaximalMonotone.closure_convexHull_add_normalCone_subset {T : E → Set E}
    (hT : SvMaximalMonotone T) (E0 : Set E) (x : E) :
    closure (convexHull ℝ (limitMappingOn T E0 x)) + normalCone (closure (svDom T)) x ⊆ T x := by
  rintro _ ⟨s, hs, n, hn, rfl⟩
  have hsT : s ∈ T x := hT.closure_convexHull_limitMappingOn_subset E0 x hs
  have hxD : x ∈ closure (svDom T) := subset_closure ⟨s, hsT⟩
  rw [normalCone_eq_of_convex hT.convex_closure_svDom hxD] at hn
  refine hT.mem_of_forall_inner_nonneg fun a b hb ↦ ?_
  have h1 := hT.1 hb hsT
  have h2 := hn a (subset_closure ⟨b, hb⟩)
  have h3 : ⟪n, x - a⟫_ℝ = -⟪n, a - x⟫_ℝ := by rw [← inner_neg_right, neg_sub]
  rw [show s + n - b = (s - b) + n by abel, inner_add_left]
  linarith

/-- In the proof of 12.67, `cl con T₀(x̄) + N_D(x̄)` is closed (the criterion 3.12):
a sequence `sν + nν → y` with `|sν| → ∞` would give, after normalization, a unit
vector `e` with `e, -e ∈ N_D(x̄)`, which is impossible since `int D ≠ ∅`. -/
theorem SvMaximalMonotone.isClosed_closure_convexHull_add_normalCone {T : E → Set E}
    (hT : SvMaximalMonotone T) (hint : (interior (svDom T)).Nonempty) (E0 : Set E) {x : E}
    (hxD : x ∈ closure (svDom T)) :
    IsClosed (closure (convexHull ℝ (limitMappingOn T E0 x)) +
      normalCone (closure (svDom T)) x) := by
  set S := closure (convexHull ℝ (limitMappingOn T E0 x)) with hSdef
  set D := closure (svDom T) with hDdef
  have hDconv : Convex ℝ D := hT.convex_closure_svDom
  have hintD : (interior D).Nonempty := hint.mono (interior_mono subset_closure)
  have hN : normalCone D x = {v | ∀ y ∈ D, ⟪v, y - x⟫_ℝ ≤ 0} := normalCone_eq_of_convex hDconv hxD
  have hST : S ⊆ T x := hT.closure_convexHull_limitMappingOn_subset E0 x
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  obtain ⟨ys, hys, hyl⟩ := mem_closure_iff_seq_limit.1 hy
  choose s hs n hn hsn using fun k ↦ Set.mem_add.1 (hys k)
  rw [hN] at hn
  by_cases hb : ∃ R, ∃ᶠ k in atTop, ‖s k‖ ≤ R
  · obtain ⟨R, hR⟩ := hb
    obtain ⟨s₀, -, φ, hφ, hsl⟩ := tendsto_subseq_of_frequently_bounded
      (isBounded_closedBall (x := (0 : E)) (r := R))
      (hR.mono fun k hk ↦ mem_closedBall_zero_iff.2 hk)
    have hs₀ : s₀ ∈ S := isClosed_closure.mem_of_tendsto hsl (Eventually.of_forall fun k ↦ hs _)
    have hnl : Tendsto (fun k ↦ n (φ k)) atTop (𝓝 (y - s₀)) :=
      ((hyl.comp hφ.tendsto_atTop).sub hsl).congr fun k ↦ by
        simp only [Function.comp_apply, ← hsn (φ k), add_sub_cancel_left]
    have hn₀ : y - s₀ ∈ normalCone D x := by
      rw [hN]
      exact fun z hz ↦ le_of_tendsto (hnl.inner tendsto_const_nhds)
        (Eventually.of_forall fun k ↦ hn (φ k) z hz)
    exact ⟨s₀, hs₀, y - s₀, hn₀, add_sub_cancel _ _⟩
  · push_neg at hb
    have hsto : Tendsto (fun k ↦ ‖s k‖) atTop atTop :=
      tendsto_atTop.2 fun R ↦ (hb R).mono fun k hk ↦ hk.le
    obtain ⟨φ, e, hφ, he1, hel⟩ := exists_subseq_tendsto_normalize hsto
    have hsφ : Tendsto (fun k ↦ ‖s (φ k)‖) atTop atTop := hsto.comp hφ.tendsto_atTop
    have heN : e ∈ normalCone D x := by
      rw [hN]
      have hdom : ∀ z ∈ svDom T, ⟪e, z - x⟫_ℝ ≤ 0 := by
        rintro z ⟨b, hb⟩
        exact inner_nonpos_of_inner_sub_nonneg (x := fun _ ↦ x) (a := fun _ ↦ z) (b := fun _ ↦ b)
          (v := fun k ↦ s (φ k)) (Eventually.of_forall fun k ↦ hT.1 hb (hST (hs (φ k))))
          tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds hsφ hel
      have hcl : IsClosed {z : E | ⟪e, z - x⟫_ℝ ≤ 0} := isClosed_le (by fun_prop) continuous_const
      exact fun z hz ↦ closure_minimal hdom hcl hz
    have hneN : -e ∈ normalCone D x := by
      rw [hN]
      intro z hz
      have h1 : Tendsto (fun k ↦ ‖s (φ k)‖⁻¹ • ys (φ k)) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp hsφ).smul (hyl.comp hφ.tendsto_atTop)
      have hlim : Tendsto (fun k ↦ ‖s (φ k)‖⁻¹ • n (φ k)) atTop (𝓝 (-e)) := by
        have h2 := h1.sub hel
        rw [zero_sub] at h2
        refine h2.congr fun k ↦ ?_
        rw [← smul_sub, ← hsn (φ k), add_sub_cancel_left]
      refine le_of_tendsto (hlim.inner tendsto_const_nhds) (Eventually.of_forall fun k ↦ ?_)
      rw [real_inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _)) (hn (φ k) z hz)
    have he0 := eq_zero_of_mem_normalCone_of_neg_mem hDconv hintD hxD heN hneN
    rw [he0, norm_zero] at he1
    exact absurd he1 zero_ne_one

/-- **Theorem 12.67**, the main inclusion `T(x̄) ⊂ cl con T₀(x̄) + N_D(x̄)` for
`x̄ ∈ dom T`.  Otherwise a separating vector `w₀` lies in `N_D(x̄)* = T_D(x̄)` (6.9),
and for `d = a - x̄` with `a ∈ int D` and small `ε > 0` the direction `w₀ + εd`
lies in `int T_D(x̄)`.  There the maximum of `⟪·, w₀ + εd⟫` over `T(x̄)` is
attained at a point of `T₀(x̄)` (the key step), which contradicts the separation
as `ε ↘ 0`.  In place of the book's support functions and Rademacher's theorem,
the key step is used at every interior tangent direction. -/
theorem SvMaximalMonotone.subset_closure_convexHull_add_normalCone {T : E → Set E}
    (hT : SvMaximalMonotone T) (hint : (interior (svDom T)).Nonempty) {E0 : Set E}
    (hE0 : E0 ⊆ singleValuedLocus T) (hdense : singleValuedLocus T ⊆ closure E0) {x : E}
    (hx : x ∈ svDom T) :
    T x ⊆ closure (convexHull ℝ (limitMappingOn T E0 x)) + normalCone (closure (svDom T)) x := by
  set D := closure (svDom T) with hDdef
  set S := closure (convexHull ℝ (limitMappingOn T E0 x)) with hSdef
  have hDconv : Convex ℝ D := hT.convex_closure_svDom
  have hxD : x ∈ D := subset_closure hx
  obtain ⟨a₀, ha₀⟩ := hint.mono (interior_mono (subset_closure : svDom T ⊆ D))
  set d := a₀ - x with hd
  have hdrad : d ∈ radialCone (interior D) x :=
    ⟨1, one_pos, by rw [one_smul, hd, add_sub_cancel]; exact ha₀⟩
  obtain ⟨vd, hvdT0, hvd⟩ := hT.exists_mem_limitMappingOn_argmax hE0 hdense hx hdrad
  have hN : normalCone D x = {v | ∀ y ∈ D, ⟪v, y - x⟫_ℝ ≤ 0} := normalCone_eq_of_convex hDconv hxD
  have h0N : (0 : E) ∈ normalCone D x := by
    rw [hN]
    intro y _
    simp
  have hNconv : Convex ℝ (normalCone D x) := by
    rw [hN]
    intro v₁ hv₁ v₂ hv₂ a b ha hb _ y hy
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    nlinarith [hv₁ y hy, hv₂ y hy]
  have hclosed := hT.isClosed_closure_convexHull_add_normalCone hint E0 hxD
  have hconvK : Convex ℝ (S + normalCone D x) := (convex_convexHull ℝ _).closure.add hNconv
  intro u hu
  by_contra huK
  obtain ⟨f, c, hfu, hfK⟩ := geometric_hahn_banach_point_closed hconvK hclosed huK
  set g := (InnerProductSpace.toDual ℝ E).symm f with hg
  have hfg : ∀ z, f z = ⟪g, z⟫_ℝ := fun z ↦ by rw [hg, InnerProductSpace.toDual_symm_apply]
  set w₀ := -g with hw₀
  have hK : ∀ b ∈ S + normalCone D x, ⟪b, w₀⟫_ℝ < -c := fun b hb ↦ by
    have h := hfK b hb
    rw [hfg, real_inner_comm] at h
    rw [hw₀, inner_neg_right]
    linarith
  have huw : -c < ⟪u, w₀⟫_ℝ := by
    rw [hfg, real_inner_comm] at hfu
    rw [hw₀, inner_neg_right]
    linarith
  have hvdS : vd ∈ S := subset_closure (subset_convexHull ℝ _ hvdT0)
  -- `w₀` is polar to the normal cone
  have hpolar : w₀ ∈ polarCone (normalCone D x) := by
    intro m hm
    by_contra hpos
    push_neg at hpos
    set lam := |-c - ⟪vd, w₀⟫_ℝ| / ⟪w₀, m⟫_ℝ with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (abs_nonneg _) hpos.le
    have hm' : lam • m ∈ normalCone D x := by
      rw [hN] at hm ⊢
      intro y hy
      rw [real_inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos hlam0 (hm y hy)
    have h := hK _ ⟨vd, hvdS, lam • m, hm', rfl⟩
    rw [inner_add_left, real_inner_smul_left, real_inner_comm w₀ m, hlam,
      div_mul_cancel₀ _ hpos.ne'] at h
    linarith [le_abs_self (-c - ⟪vd, w₀⟫_ℝ)]
  -- perturbed directions are interior tangent directions
  have hTD : tangentCone D x = polarCone (normalCone D x) :=
    tangentCone_eq_polarCone_normalCone hDconv hxD
  have hintTD : interior (tangentCone D x) = radialCone (interior D) x :=
    interior_tangentCone_of_convex hDconv hxD
  have hpert : ∀ ε : ℝ, 0 < ε → w₀ + ε • d ∈ radialCone (interior D) x := by
    intro ε hε
    rw [← hintTD, hTD]
    have hεd : ε • d ∈ interior (polarCone (normalCone D x)) := by
      rw [← hTD, hintTD]
      refine ⟨ε⁻¹, inv_pos.2 hε, ?_⟩
      rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul, hd, add_sub_cancel]
      exact ha₀
    have hsub : (fun z ↦ z - w₀) ⁻¹' interior (polarCone (normalCone D x)) ⊆
        polarCone (normalCone D x) := by
      intro z hz m hm
      have h1 := interior_subset hz m hm
      have h2 := hpolar m hm
      rw [inner_sub_left] at h1
      linarith
    exact interior_maximal hsub (isOpen_interior.preimage (continuous_id.sub continuous_const))
      (by simpa using hεd)
  -- the contradiction
  set M := ⟪vd, d⟫_ℝ with hM
  have hgap : 0 < ⟪u, w₀⟫_ℝ + c := by linarith
  set ε := (⟪u, w₀⟫_ℝ + c) / (2 * (|M - ⟪u, d⟫_ℝ| + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨v, hvT0, hv⟩ := hT.exists_mem_limitMappingOn_argmax hE0 hdense hx (hpert ε hε0)
  have hvT : v ∈ T x := limitMappingOn_subset hT.isClosed_svGraph E0 x hvT0
  have h1 := hv u hu
  have h2 : ⟪v, w₀⟫_ℝ < -c :=
    hK v ⟨v, subset_closure (subset_convexHull ℝ _ hvT0), 0, h0N, add_zero v⟩
  have h3 : ε * ⟪v, d⟫_ℝ ≤ ε * M := mul_le_mul_of_nonneg_left (hvd v hvT) hε0.le
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right] at h1
  have h4 : ε * M - ε * ⟪u, d⟫_ℝ ≤ ε * |M - ⟪u, d⟫_ℝ| := by
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hε0.le
  have h5 : ε * |M - ⟪u, d⟫_ℝ| < (⟪u, w₀⟫_ℝ + c) / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg (M - ⟪u, d⟫_ℝ)]
  linarith

/-- **Theorem 12.67 (structure of maximal monotone mappings)**.  Let `T` be maximal
monotone with `int(dom T) ≠ ∅`, let `E` be the set of points of `int(dom T)` where
`T` is single-valued, and let `E₀ ⊂ E` be dense in `E`.  For the mapping `T₀`,
`T₀(x) = {v | ∃ xν →_{E₀} x with T(xν) ∋ vν → v}`: `T₀` agrees with `T` on `E`
(where `T` is single-valued); `dom T = dom T₀ ⊂ cl E₀ = cl(dom T)`; and
`T(x) = cl con T₀(x) + N_{cl E₀}(x)` for all `x`.  The choices `E₀ = E` and `E₀` the
set of differentiability points of `T` qualify (12.66). -/
theorem structure_of_maximal_monotone_mappings {T : E → Set E} (hT : SvMaximalMonotone T)
    (hint : (interior (svDom T)).Nonempty) {E0 : Set E} (hE0 : E0 ⊆ singleValuedLocus T)
    (hdense : singleValuedLocus T ⊆ closure E0) :
    (∀ x ∈ singleValuedLocus T, limitMappingOn T E0 x = T x) ∧
    svDom T = svDom (limitMappingOn T E0) ∧ svDom (limitMappingOn T E0) ⊆ closure E0 ∧
    closure E0 = closure (svDom T) ∧
    (∀ x, T x = closure (convexHull ℝ (limitMappingOn T E0 x)) + normalCone (closure E0) x) ∧
    (singleValuedLocus T ⊆ closure (singleValuedLocus T) ∧
      {x | SvDifferentiableAt T x} ⊆ singleValuedLocus T ∧
      singleValuedLocus T ⊆ closure {x | SvDifferentiableAt T x}) := by
  have hcl := hT.closure_eq_closure_svDom hint hE0 hdense
  refine ⟨fun x hx ↦ hT.limitMappingOn_eq hE0 hdense hx, ?_,
    svDom_limitMappingOn_subset_closure T E0, hcl, fun x ↦ ?_,
    subset_closure, setOf_svDifferentiableAt_subset_singleValuedLocus T,
    hT.singleValuedLocus_subset_closure_svDifferentiableAt⟩
  · refine Subset.antisymm (fun x hx ↦ ?_)
      (fun x ⟨v, hv⟩ ↦ ⟨v, limitMappingOn_subset hT.isClosed_svGraph E0 x hv⟩)
    obtain ⟨a₀, ha₀⟩ := hint
    have hrad : a₀ - x ∈ radialCone (interior (closure (svDom T))) x :=
      ⟨1, one_pos, by rw [one_smul, add_sub_cancel]; exact interior_mono subset_closure ha₀⟩
    obtain ⟨v, hv, -⟩ := hT.exists_mem_limitMappingOn_argmax hE0 hdense hx hrad
    exact ⟨v, hv⟩
  · rw [hcl]
    by_cases hx : x ∈ svDom T
    · exact Subset.antisymm (hT.subset_closure_convexHull_add_normalCone hint hE0 hdense hx)
        (hT.closure_convexHull_add_normalCone_subset E0 x)
    · have hTx : T x = ∅ := not_nonempty_iff_eq_empty.1 hx
      have hT0 : limitMappingOn T E0 x = ∅ :=
        subset_empty_iff.1 (hTx ▸ limitMappingOn_subset hT.isClosed_svGraph E0 x)
      rw [hTx, hT0, convexHull_empty, closure_empty, Set.empty_add]

end RW
