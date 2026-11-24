/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second subderivatives of piecewise linear-quadratic functions

Proposition 13.9.  Around a point `x̄` of its domain, a piecewise linear-quadratic function `f`
has a *local conical model* (`PLQLocalModel`): on a ball of radius `δ` around `x̄`, the domain of
`f` is `x̄ + ⋃ᵢ Kᵢ` for finitely many polyhedral cones `Kᵢ`, and `f` agrees with a
linear-quadratic expression `qᵢ` on `x̄ + Kᵢ`.  Writing `aᵢ = ∇qᵢ(x̄)` and `Aᵢ` for the matrix
of `qᵢ`, this gives `df(x̄)(w) = ⟪aᵢ, w⟫` on `Kᵢ` (and `∞` off `⋃ Kᵢ`), and for `τ‖w‖ < δ`

* `Δ²_τ f(x̄)(w) = ⟪w, Aᵢ w⟫` on `Kᵢ` and `∞` off `⋃ Kᵢ` (`secondDifferenceQuotientAt_eq`),
* `Δ²_τ f(x̄ | v)(w) = ⟪w, Aᵢ w⟫ + (2/τ)(⟪aᵢ, w⟫ - ⟪v, w⟫)` on `Kᵢ`.

So the quotients are eventually constant along every half-line, `d²f(x̄)` is the piecewise
linear-quadratic `secondForm`, and for every `v` with `⟪v, ·⟫ ≤ df(x̄)` one has
`d²f(x̄ | v) = d²f(x̄) + δ_K` with `K = {w | df(x̄)(w) = ⟪v, w⟫}`, attained along half-lines.
These formulas do not need convexity; convexity gives `d²f(x̄) ≥ 0`, convexity of
`d²f(x̄ | v)` and polyhedrality of `K`.
-/

import RockafellarWets.Chapter13.ConvexSecondSubderivatives
import RockafellarWets.Chapter10.PLQSubderivatives
import RockafellarWets.Chapter10.ConvexPolyhedralUnions
import RockafellarWets.Chapter6.PolyhedralCones
import RockafellarWets.Chapter12.PiecewiseLinearQuadraticSubgradients

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Local conical models -/

/-- A local conical model of `f` around `x̄`: on the open ball of radius `δ` around `x̄`, the
domain of `f` is `x̄ + ⋃ᵢ Kᵢ` for finitely many polyhedral cones (or empty sets) `Kᵢ`, and `f`
agrees with the linear-quadratic expression `qᵢ` on `x̄ + Kᵢ`. -/
structure PLQLocalModel (f : E → EReal) (x : E) where
  m : ℕ
  cone : Fin m → Set E
  piece : Fin m → QuadraticPiece E
  radius : ℝ
  radius_pos : 0 < radius
  polyhedral : ∀ i, IsPolyhedral (cone i)
  isCone : ∀ i, (cone i).Nonempty → IsCone (cone i)
  dom_iff : ∀ h, ‖h‖ < radius → (x + h ∈ effectiveDomain f ↔ ∃ i, h ∈ cone i)
  eq_eval : ∀ i h, ‖h‖ < radius → h ∈ cone i → f (x + h) = (piece i).eval (x + h)

/-- Every piecewise linear-quadratic function has a local conical model around each point of its
domain: the cones are the tangent cones of the pieces containing `x̄`. -/
theorem IsPiecewiseLinearQuadratic.nonempty_localModel [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (x : E) : Nonempty (PLQLocalModel f x) := by
  classical
  obtain ⟨m, C, q, hC, hdom, hfq⟩ := hf
  have hev : ∀ᶠ y in 𝓝 x, ∀ i, (x ∈ C i → (y ∈ C i ↔ y - x ∈ tangentCone (C i) x)) ∧
      (x ∉ C i → y ∉ C i) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : x ∈ C i
    · filter_upwards [(hC i).eventually_mem_iff_sub_mem_tangentCone hi] with y hy
      exact ⟨fun _ ↦ hy, fun h ↦ absurd hi h⟩
    · filter_upwards [(hC i).isClosed.isOpen_compl.mem_nhds hi] with y hy
      exact ⟨fun h ↦ absurd h hi, fun _ ↦ hy⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hy : ∀ h : E, ‖h‖ < δ → ∀ i, (x ∈ C i → (x + h ∈ C i ↔ h ∈ tangentCone (C i) x)) ∧
      (x ∉ C i → x + h ∉ C i) := by
    intro h hh i
    have := hball (show dist (x + h) x < δ by rwa [dist_eq_norm, add_sub_cancel_left]) i
    rwa [add_sub_cancel_left] at this
  refine ⟨⟨m, fun i ↦ if x ∈ C i then tangentCone (C i) x else ∅, q, δ, hδ, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    dsimp only
    split_ifs with hi
    · exact (hC i).isPolyhedral_tangentCone hi
    · exact IsPolyhedral.empty
  · intro i hne
    dsimp only at hne ⊢
    split_ifs at hne ⊢ with hi
    · exact isCone_tangentCone hi
    · simp at hne
  · intro h hh
    rw [hdom, mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hxi : x ∈ C i
      · exact ⟨i, by simpa only [if_pos hxi] using ((hy h hh i).1 hxi).1 hi⟩
      · exact absurd hi ((hy h hh i).2 hxi)
    · rintro ⟨i, hi⟩
      by_cases hxi : x ∈ C i
      · simp only [if_pos hxi] at hi
        exact ⟨i, ((hy h hh i).1 hxi).2 hi⟩
      · simp [hxi] at hi
  · intro i h hh hi
    by_cases hxi : x ∈ C i
    · simp only [if_pos hxi] at hi
      exact hfq i _ (((hy h hh i).1 hxi).2 hi)
    · simp [hxi] at hi

namespace PLQLocalModel

variable {f : E → EReal} {x : E} (M : PLQLocalModel f x)

/-- The gradient `aᵢ = ∇qᵢ(x̄)` of the `i`-th piece at the base point. -/
def grad (i : Fin M.m) : E := (M.piece i).matrix x + (M.piece i).linear

/-- The union `⋃ᵢ Kᵢ`, the tangent cone of the domain. -/
def coneUnion : Set E := ⋃ i, M.cone i

theorem mem_coneUnion {u : E} : u ∈ M.coneUnion ↔ ∃ i, u ∈ M.cone i := mem_iUnion

theorem zero_mem_cone {i : Fin M.m} (h : (M.cone i).Nonempty) : (0 : E) ∈ M.cone i :=
  (M.isCone i h).1

theorem smul_mem_cone {i : Fin M.m} {u : E} (hu : u ∈ M.cone i) {τ : ℝ} (hτ : 0 < τ) :
    τ • u ∈ M.cone i :=
  (M.isCone i ⟨u, hu⟩).2 hu hτ

theorem mem_cone_of_smul_mem {i : Fin M.m} {u : E} {τ : ℝ} (hτ : 0 < τ)
    (hu : τ • u ∈ M.cone i) : u ∈ M.cone i := by
  have := M.smul_mem_cone hu (inv_pos.2 hτ)
  rwa [smul_smul, inv_mul_cancel₀ hτ.ne', one_smul] at this

theorem smul_mem_coneUnion_iff {u : E} {τ : ℝ} (hτ : 0 < τ) :
    τ • u ∈ M.coneUnion ↔ u ∈ M.coneUnion := by
  simp only [mem_coneUnion]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨i, M.mem_cone_of_smul_mem hτ hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, M.smul_mem_cone hi hτ⟩⟩

theorem norm_smul_lt {u : E} {τ : ℝ} (hτ : 0 < τ) (hτu : τ * ‖u‖ < M.radius) :
    ‖τ • u‖ < M.radius := by
  rwa [norm_smul, Real.norm_of_nonneg hτ.le]

theorem exists_mem_cone_zero (hx : x ∈ effectiveDomain f) : ∃ i, (0 : E) ∈ M.cone i := by
  have := (M.dom_iff 0 (by simpa using M.radius_pos)).1 (by simpa using hx)
  exact this

/-- `f(x̄) = qᵢ(x̄)` for every nonempty piece. -/
theorem eq_eval_base {i : Fin M.m} (h : (M.cone i).Nonempty) : f x = (M.piece i).eval x := by
  have := M.eq_eval i 0 (by simpa using M.radius_pos) (M.zero_mem_cone h)
  simpa using this

/-- The expansion `f(x̄ + τu) = f(x̄) + τ⟪aᵢ, u⟫ + (τ²/2)⟪u, Aᵢu⟫` for `u ∈ Kᵢ`, `τ‖u‖ < δ`. -/
theorem eq_expansion {i : Fin M.m} {u : E} (hu : u ∈ M.cone i) {τ : ℝ} (hτ : 0 < τ)
    (hτu : τ * ‖u‖ < M.radius) :
    f (x + τ • u) = (((M.piece i).eval x + τ * ⟪M.grad i, u⟫_ℝ +
      τ ^ 2 / 2 * ⟪u, (M.piece i).matrix u⟫_ℝ : ℝ) : EReal) := by
  rw [M.eq_eval i _ (M.norm_smul_lt hτ hτu) (M.smul_mem_cone hu hτ)]
  congr 1
  have h := (M.piece i).eval_add_sub x (τ • u)
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h
  rw [grad]
  linarith

/-- Off `⋃ Kᵢ`, small steps leave the domain. -/
theorem eq_top_of_not_mem {u : E} (hu : u ∉ M.coneUnion) {τ : ℝ} (hτ : 0 < τ)
    (hτu : τ * ‖u‖ < M.radius) : f (x + τ • u) = ⊤ := by
  have hnot : x + τ • u ∉ effectiveDomain f := by
    rw [M.dom_iff _ (M.norm_smul_lt hτ hτu), ← mem_coneUnion, M.smul_mem_coneUnion_iff hτ]
    exact hu
  simpa [effectiveDomain] using hnot

/-- Eventually along `τ ↓ 0`, uniformly for `w'` near `w`, the step `τ‖w'‖` is below `δ`. -/
theorem eventually_small (w : E) :
    ∀ᶠ p : ℝ × E in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 ∧ p.1 * ‖p.2‖ < M.radius := by
  have hpos : (0 : ℝ) < M.radius / (‖w‖ + 1) := div_pos M.radius_pos (by positivity)
  have h1 : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ < M.radius / (‖w‖ + 1) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hpos)] with τ h h'
    exact ⟨h, h'⟩
  have h2 : ∀ᶠ w' : E in 𝓝 w, ‖w'‖ < ‖w‖ + 1 := by
    have : Tendsto (fun w' : E ↦ ‖w'‖) (𝓝 w) (𝓝 ‖w‖) := continuous_norm.tendsto w
    exact this.eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1.prod_mk h2] with p hp
  refine ⟨hp.1.1, ?_⟩
  calc p.1 * ‖p.2‖ ≤ p.1 * (‖w‖ + 1) := mul_le_mul_of_nonneg_left hp.2.le hp.1.1.le
    _ < M.radius / (‖w‖ + 1) * (‖w‖ + 1) := by
        exact mul_lt_mul_of_pos_right hp.1.2 (by positivity)
    _ = M.radius := by field_simp

/-- Along a half-line, eventually `τ‖w‖ < δ`. -/
theorem eventually_small_ray (w : E) :
    ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ * ‖w‖ < M.radius := by
  have ht : Tendsto (fun τ : ℝ ↦ (τ, w)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
    tendsto_id.prodMk tendsto_const_nhds
  exact ht.eventually (M.eventually_small w)

/-! #### First order -/

/-- `df(x̄)(u) = ⟪aᵢ, u⟫` for `u ∈ Kᵢ`. -/
theorem subderivative_eq [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f)
    {i : Fin M.m} {u : E} (hu : u ∈ M.cone i) :
    subderivative f x u = ((⟪M.grad i, u⟫_ℝ : ℝ) : EReal) := by
  have hc := M.eq_eval_base ⟨u, hu⟩
  have hlim := (hf.hasOneSidedDirDeriv hx u).2.2
  have hlim2 : Tendsto (fun τ : ℝ ↦ differenceQuotient f x τ u) (𝓝[>] (0 : ℝ))
      (𝓝 ((⟪M.grad i, u⟫_ℝ : ℝ) : EReal)) := by
    have hr : Tendsto (fun τ : ℝ ↦ ⟪M.grad i, u⟫_ℝ + τ / 2 * ⟪u, (M.piece i).matrix u⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 ⟪M.grad i, u⟫_ℝ) := by
      have : Tendsto (fun τ : ℝ ↦ ⟪M.grad i, u⟫_ℝ + τ / 2 * ⟪u, (M.piece i).matrix u⟫_ℝ)
          (𝓝 (0 : ℝ)) (𝓝 (⟪M.grad i, u⟫_ℝ + 0 / 2 * ⟪u, (M.piece i).matrix u⟫_ℝ)) :=
        (continuous_const.add ((continuous_id.div_const 2).mul continuous_const)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine (continuous_coe_real_ereal.tendsto _ |>.comp hr).congr' ?_
    filter_upwards [M.eventually_small_ray u] with τ ⟨hτ, hτu⟩
    rw [Function.comp_apply, differenceQuotient_eq_coe hc (M.eq_expansion hu hτ hτu)]
    congr 1
    field_simp
    ring
  exact tendsto_nhds_unique hlim hlim2

/-- `df(x̄)(u) = ∞` for `u ∉ ⋃ Kᵢ`. -/
theorem subderivative_eq_top [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f)
    {u : E} (hu : u ∉ M.coneUnion) : subderivative f x u = ⊤ := by
  obtain ⟨i, hi⟩ := M.exists_mem_cone_zero hx
  have hc := M.eq_eval_base ⟨0, hi⟩
  have hlim := (hf.hasOneSidedDirDeriv hx u).2.2
  have hlim2 : Tendsto (fun τ : ℝ ↦ differenceQuotient f x τ u) (𝓝[>] (0 : ℝ)) (𝓝 ⊤) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [M.eventually_small_ray u] with τ ⟨hτ, hτu⟩
    rw [differenceQuotient_eq_top hτ hc (M.eq_top_of_not_mem hu hτ hτu)]
  exact tendsto_nhds_unique hlim hlim2

/-- The first-order data agree on overlapping pieces. -/
theorem inner_grad_eq [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f)
    {i j : Fin M.m} {u : E} (hi : u ∈ M.cone i) (hj : u ∈ M.cone j) :
    ⟪M.grad i, u⟫_ℝ = ⟪M.grad j, u⟫_ℝ := by
  have h := (M.subderivative_eq hf hx hi).symm.trans (M.subderivative_eq hf hx hj)
  exact_mod_cast h

/-- The second-order data agree on overlapping pieces. -/
theorem inner_matrix_eq [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f)
    {i j : Fin M.m} {u : E} (hi : u ∈ M.cone i) (hj : u ∈ M.cone j) :
    ⟪u, (M.piece i).matrix u⟫_ℝ = ⟪u, (M.piece j).matrix u⟫_ℝ := by
  obtain ⟨τ, hτ, hτu⟩ := (M.eventually_small_ray u).exists
  have h := (M.eq_expansion hi hτ hτu).symm.trans (M.eq_expansion hj hτ hτu)
  have hb : (M.piece i).eval x = (M.piece j).eval x := by
    have := (M.eq_eval_base ⟨u, hi⟩).symm.trans (M.eq_eval_base ⟨u, hj⟩)
    exact_mod_cast this
  have hg := M.inner_grad_eq hf hx hi hj
  have h' : (M.piece i).eval x + τ * ⟪M.grad i, u⟫_ℝ + τ ^ 2 / 2 * ⟪u, (M.piece i).matrix u⟫_ℝ =
      (M.piece j).eval x + τ * ⟪M.grad j, u⟫_ℝ + τ ^ 2 / 2 * ⟪u, (M.piece j).matrix u⟫_ℝ := by
    exact_mod_cast h
  rw [hb, hg] at h'
  have hτ2 : τ ^ 2 / 2 ≠ 0 := by positivity
  exact mul_left_cancel₀ hτ2 (by linarith)

end PLQLocalModel

end RW

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Lower limits along half-lines -/

omit [InnerProductSpace ℝ E] in
/-- A lower limit over `l ×ˢ 𝓝 w` dominates `g(w)` when it dominates eventually a function `g`
of the second variable that is lsc at `w`. -/
theorem le_liminf_prod_of_lowerSemicontinuousAt {l : Filter ℝ} {g : E → EReal} {w : E}
    (hg : LowerSemicontinuousAt g w) {u : ℝ × E → EReal}
    (hu : ∀ᶠ p in l ×ˢ 𝓝 w, g p.2 ≤ u p) : g w ≤ liminf u (l ×ˢ 𝓝 w) := by
  refine le_of_forall_lt fun y hy ↦ ?_
  obtain ⟨z, hyz, hzw⟩ := exists_between hy
  have h1 : ∀ᶠ p : ℝ × E in l ×ˢ 𝓝 w, z < g p.2 := tendsto_snd.eventually (hg z hzw)
  have h2 : z ≤ liminf u (l ×ˢ 𝓝 w) := by
    refine le_liminf_of_le (h := ?_)
    filter_upwards [h1, hu] with p hp hp'
    exact hp.le.trans hp'
  exact hyz.trans_le h2

omit [InnerProductSpace ℝ E] in
/-- A lower limit over `𝓝[>] 0 ×ˢ 𝓝 w` is at most an eventual bound along the half-line
`τ ↦ (τ, w)`. -/
theorem liminf_le_of_eventually_ray {u : ℝ × E → EReal} {w : E} {a : EReal}
    (h : ∀ᶠ τ in 𝓝[>] (0 : ℝ), u (τ, w) ≤ a) : liminf u (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) ≤ a := by
  have ht : Tendsto (fun τ : ℝ ↦ (τ, w)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
    tendsto_id.prodMk tendsto_const_nhds
  exact liminf_le_of_frequently_le' (ht.frequently h.frequently)

namespace PLQLocalModel

variable {f : E → EReal} {x : E} (M : PLQLocalModel f x)

/-! #### Second order -/

/-- The quadratic piece `u ↦ ⟪u, Aᵢ u⟫`. -/
noncomputable def hessPiece (i : Fin M.m) : QuadraticPiece E where
  matrix := (2 : ℝ) • (M.piece i).matrix
  symmetric u w := by
    simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
      (M.piece i).symmetric u w]
  linear := 0
  constant := 0

theorem hessPiece_eval (i : Fin M.m) (u : E) :
    (M.hessPiece i).eval u = ⟪u, (M.piece i).matrix u⟫_ℝ := by
  simp only [QuadraticPiece.eval, hessPiece, ContinuousLinearMap.smul_apply, real_inner_smul_right,
    inner_zero_left, add_zero]
  ring

open Classical in
/-- The second subderivative `d²f(x̄)` of the model: `⟪u, Aᵢu⟫` on `Kᵢ`, `∞` off `⋃ Kᵢ`. -/
noncomputable def secondForm (u : E) : EReal :=
  if h : ∃ i, u ∈ M.cone i then ((⟪u, (M.piece h.choose).matrix u⟫_ℝ : ℝ) : EReal) else ⊤

theorem secondForm_eq [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {i : Fin M.m} {u : E} (hu : u ∈ M.cone i) :
    M.secondForm u = ((⟪u, (M.piece i).matrix u⟫_ℝ : ℝ) : EReal) := by
  have h : ∃ i, u ∈ M.cone i := ⟨i, hu⟩
  rw [secondForm, dif_pos h, M.inner_matrix_eq hf hx h.choose_spec hu]

theorem secondForm_eq_top {u : E} (hu : u ∉ M.coneUnion) : M.secondForm u = ⊤ := by
  rw [secondForm, dif_neg (by rwa [← mem_coneUnion])]

theorem secondForm_ne_bot (u : E) : M.secondForm u ≠ ⊥ := by
  unfold secondForm
  split_ifs
  · exact EReal.coe_ne_bot _
  · exact top_ne_bot

theorem effectiveDomain_secondForm [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) : effectiveDomain M.secondForm = M.coneUnion := by
  ext u
  rw [mem_effectiveDomain_iff]
  constructor
  · intro h
    by_contra hu
    rw [M.secondForm_eq_top hu] at h
    exact lt_irrefl _ h
  · intro hu
    obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
    rw [M.secondForm_eq hf hx hi]
    exact EReal.coe_lt_top _

/-- `d²f(x̄)` is piecewise linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_secondForm [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f) :
    IsPiecewiseLinearQuadratic M.secondForm := by
  refine ⟨M.m, M.cone, M.hessPiece, M.polyhedral, ?_, fun i u hu ↦ ?_⟩
  · rw [M.effectiveDomain_secondForm hf hx]
    rfl
  · rw [M.secondForm_eq hf hx hu, hessPiece_eval]

theorem isClosed_coneUnion [FiniteDimensional ℝ E] : IsClosed M.coneUnion :=
  isClosed_iUnion_of_finite fun i ↦ (M.polyhedral i).isClosed

theorem secondForm_zero [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) : M.secondForm 0 = 0 := by
  obtain ⟨i, hi⟩ := M.exists_mem_cone_zero hx
  rw [M.secondForm_eq hf hx hi]
  simp

/-- **Proposition 13.9**: for `τ‖u‖ < δ`, `Δ²_τ f(x̄)(u)` is the model value `d²f(x̄)(u)`. -/
theorem secondDifferenceQuotientAt_eq [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {u : E} {τ : ℝ} (hτ : 0 < τ) (hτu : τ * ‖u‖ < M.radius) :
    secondDifferenceQuotientAt f x τ u = M.secondForm u := by
  by_cases hu : u ∈ M.coneUnion
  · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
    rw [secondDifferenceQuotientAt_eq_of_subderivative_eq (M.subderivative_eq hf hx hi),
      secondDifferenceQuotient_of_coe (M.eq_eval_base ⟨u, hi⟩) (M.eq_expansion hi hτ hτu),
      M.secondForm_eq hf hx hi]
    congr 1
    field_simp
    ring
  · obtain ⟨i, hi⟩ := M.exists_mem_cone_zero hx
    rw [M.secondForm_eq_top hu, secondDifferenceQuotientAt, M.eq_top_of_not_mem hu hτ hτu,
      M.eq_eval_base ⟨0, hi⟩, M.subderivative_eq_top hf hx hu, EReal.top_sub_coe, infAddition,
      if_pos (Or.inl rfl)]
    exact EReal.coe_mul_top_of_pos (by positivity)

/-- **Proposition 13.9**: `d²f(x̄)` is the model value. -/
theorem secondSubderivativeAt_eq [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) (w : E) : secondSubderivativeAt f x w = M.secondForm w := by
  have hlsc := (M.isPiecewiseLinearQuadratic_secondForm hf hx).lowerSemicontinuous
  have hev : (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2) =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 w]
      (fun p ↦ M.secondForm p.2) := by
    filter_upwards [M.eventually_small w] with p ⟨h1, h2⟩
    exact M.secondDifferenceQuotientAt_eq hf hx h1 h2
  rw [secondSubderivativeAt, liminf_congr hev]
  refine le_antisymm (liminf_le_of_eventually_ray (.of_forall fun _ ↦ le_rfl)) ?_
  exact le_liminf_prod_of_lowerSemicontinuousAt (hlsc w) (.of_forall fun _ ↦ le_rfl)

/-- **Proposition 13.9**: along half-lines `Δ²_τ f(x̄)(w)` is eventually constant, equal to
`d²f(x̄)(w)`. -/
theorem eventually_secondDifferenceQuotientAt_eq [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f) (w : E) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), secondDifferenceQuotientAt f x τ w = M.secondForm w := by
  filter_upwards [M.eventually_small_ray w] with τ ⟨hτ, hτw⟩
  rw [M.secondDifferenceQuotientAt_eq hf hx hτ hτw]

/-! #### Second order for a vector `v` -/

/-- `Δ²_τ f(x̄ | v)(u) = ⟪u, Aᵢu⟫ + (2/τ)(⟪aᵢ, u⟫ - ⟪v, u⟫)` for `u ∈ Kᵢ` and `τ‖u‖ < δ`. -/
theorem secondDifferenceQuotient_eq_of_mem {i : Fin M.m} {u v : E} (hu : u ∈ M.cone i) {τ : ℝ}
    (hτ : 0 < τ) (hτu : τ * ‖u‖ < M.radius) :
    secondDifferenceQuotient f x v τ u = ((⟪u, (M.piece i).matrix u⟫_ℝ +
      2 / τ * (⟪M.grad i, u⟫_ℝ - ⟪v, u⟫_ℝ) : ℝ) : EReal) := by
  rw [secondDifferenceQuotient_of_coe (M.eq_eval_base ⟨u, hu⟩) (M.eq_expansion hu hτ hτu)]
  congr 1
  field_simp
  ring

theorem secondDifferenceQuotient_eq_top_of_not_mem (hx : x ∈ effectiveDomain f) {u v : E}
    (hu : u ∉ M.coneUnion) {τ : ℝ} (hτ : 0 < τ) (hτu : τ * ‖u‖ < M.radius) :
    secondDifferenceQuotient f x v τ u = ⊤ := by
  obtain ⟨i, hi⟩ := M.exists_mem_cone_zero hx
  exact secondDifferenceQuotient_of_top hτ.ne' (M.eq_eval_base ⟨0, hi⟩)
    (M.eq_top_of_not_mem hu hτ hτu)

/-- For `⟪v, ·⟫ ≤ df(x̄)`, the quotients `Δ²_τ f(x̄ | v)` dominate `d²f(x̄)` for small `τ`. -/
theorem secondForm_le_secondDifferenceQuotient [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f) {v : E}
    (hv : ∀ u, ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u) {u : E} {τ : ℝ} (hτ : 0 < τ)
    (hτu : τ * ‖u‖ < M.radius) : M.secondForm u ≤ secondDifferenceQuotient f x v τ u := by
  by_cases hu : u ∈ M.coneUnion
  · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
    rw [M.secondDifferenceQuotient_eq_of_mem hi hτ hτu, M.secondForm_eq hf hx hi,
      EReal.coe_le_coe_iff]
    have h := hv u
    rw [M.subderivative_eq hf hx hi, EReal.coe_le_coe_iff] at h
    have : 0 ≤ 2 / τ * (⟪M.grad i, u⟫_ℝ - ⟪v, u⟫_ℝ) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  · rw [M.secondDifferenceQuotient_eq_top_of_not_mem hx hu hτ hτu]
    exact le_top

/-- **Proposition 13.9**: for `⟪v, ·⟫ ≤ df(x̄)`, `d²f(x̄ | v)(w) = d²f(x̄)(w) + δ_K(w)` with
`K = {w | df(x̄)(w) = ⟪v, w⟫}`. -/
theorem secondSubderivative_eq [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {v : E} (hv : ∀ u, ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u)
    (w : E) : secondSubderivative f x v w =
      if subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) then M.secondForm w else ⊤ := by
  have hlsc := (M.isPiecewiseLinearQuadratic_secondForm hf hx).lowerSemicontinuous
  have hge : M.secondForm w ≤ secondSubderivative f x v w := by
    refine le_liminf_prod_of_lowerSemicontinuousAt (hlsc w) ?_
    filter_upwards [M.eventually_small w] with p ⟨h1, h2⟩
    exact M.secondForm_le_secondDifferenceQuotient hf hx hv h1 h2
  split_ifs with hw
  · refine le_antisymm (liminf_le_of_eventually_ray ?_) hge
    by_cases hu : w ∈ M.coneUnion
    · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
      filter_upwards [M.eventually_small_ray w] with τ ⟨hτ, hτw⟩
      rw [M.secondDifferenceQuotient_eq_of_mem hi hτ hτw, M.secondForm_eq hf hx hi]
      rw [M.subderivative_eq hf hx hi, EReal.coe_eq_coe_iff] at hw
      rw [hw, sub_self, mul_zero, add_zero]
    · rw [M.subderivative_eq_top hf hx hu] at hw
      exact absurd hw.symm (EReal.coe_ne_top _)
  · by_cases hu : w ∈ M.coneUnion
    · obtain ⟨j, hj⟩ := M.mem_coneUnion.1 hu
      have hdj := M.subderivative_eq hf hx hj
      have hlt : ⟪v, w⟫_ℝ < ⟪M.grad j, w⟫_ℝ := by
        have h := hv w
        rw [hdj, EReal.coe_le_coe_iff] at h
        rw [hdj, EReal.coe_eq_coe_iff] at hw
        exact lt_of_le_of_ne h (Ne.symm hw)
      set c := ⟪M.grad j, w⟫_ℝ - ⟪v, w⟫_ℝ with hc
      have hcpos : 0 < c := by rw [hc]; linarith
      -- lower semicontinuity of `df(x̄)` and of the model at `w`
      have hdlsc :=
        (hf.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic.lowerSemicontinuous
      have hs := M.secondForm_eq hf hx hj
      set s := ⟪w, (M.piece j).matrix w⟫_ℝ with hs_def
      have h1 : ∀ᶠ u in 𝓝 w, (((⟪v, w⟫_ℝ + 3 / 4 * c : ℝ)) : EReal) < subderivative f x u :=
        hdlsc w _ (by show _ < subderivative f x w; rw [hdj, EReal.coe_lt_coe_iff]; linarith)
      have h2 : ∀ᶠ u in 𝓝 w, (((s - 1 : ℝ)) : EReal) < M.secondForm u :=
        hlsc w _ (by show _ < M.secondForm w; rw [hs, EReal.coe_lt_coe_iff]; linarith)
      have h3 : ∀ᶠ u in 𝓝 w, ⟪v, u⟫_ℝ < ⟪v, w⟫_ℝ + c / 4 := by
        have : Tendsto (fun u ↦ ⟪v, u⟫_ℝ) (𝓝 w) (𝓝 ⟪v, w⟫_ℝ) :=
          (continuous_const.inner continuous_id).tendsto w
        exact this.eventually (gt_mem_nhds (by linarith))
      rw [EReal.eq_top_iff_forall_lt]
      intro N
      have hpos : 0 < c / (2 * (|N - s| + 2)) := by positivity
      have h4 : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), τ < c / (2 * (|N - s| + 2)) :=
        nhdsWithin_le_nhds (Iio_mem_nhds hpos)
      have hN : (((N + 1 : ℝ)) : EReal) ≤ secondSubderivative f x v w := by
        refine le_liminf_of_le (h := ?_)
        filter_upwards [M.eventually_small w, tendsto_fst.eventually h4,
          tendsto_snd.eventually (h1.and (h2.and h3))] with p ⟨hp1, hp2⟩ hp4 ⟨hq1, hq2, hq3⟩
        by_cases hpu : p.2 ∈ M.coneUnion
        · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hpu
          rw [M.secondDifferenceQuotient_eq_of_mem hi hp1 hp2, EReal.coe_le_coe_iff]
          rw [M.subderivative_eq hf hx hi, EReal.coe_lt_coe_iff] at hq1
          rw [M.secondForm_eq hf hx hi, EReal.coe_lt_coe_iff] at hq2
          have hgap : c / 2 < ⟪M.grad i, p.2⟫_ℝ - ⟪v, p.2⟫_ℝ := by linarith
          have hτ2 : 2 * (|N - s| + 2) / c < 1 / p.1 := by
            rw [div_lt_div_iff₀ hcpos hp1]
            rw [lt_div_iff₀ (by positivity)] at hp4
            linarith
          have hbig : (|N - s| + 2) < 2 / p.1 * (c / 2) := by
            have := mul_lt_mul_of_pos_right hτ2 (show 0 < c / 2 by positivity)
            have e1 : 2 * (|N - s| + 2) / c * (c / 2) = |N - s| + 2 := by field_simp
            have e2 : 1 / p.1 * (c / 2) = 2 / p.1 * (c / 2) / 2 := by ring
            rw [e1] at this
            nlinarith [this, show 0 < 2 / p.1 * (c / 2) by positivity]
          have hmul : 2 / p.1 * (c / 2) ≤ 2 / p.1 * (⟪M.grad i, p.2⟫_ℝ - ⟪v, p.2⟫_ℝ) :=
            mul_le_mul_of_nonneg_left hgap.le (by positivity)
          have habs : N - s ≤ |N - s| := le_abs_self _
          linarith
        · rw [M.secondDifferenceQuotient_eq_top_of_not_mem hx hpu hp1 hp2]
          exact le_top
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) hN
    · -- off `⋃ Kᵢ`, the quotients are eventually `∞`
      have hopen : ∀ᶠ u in 𝓝 w, u ∉ M.coneUnion := M.isClosed_coneUnion.isOpen_compl.mem_nhds hu
      rw [eq_top_iff]
      refine le_liminf_of_le (h := ?_)
      filter_upwards [M.eventually_small w, tendsto_snd.eventually hopen] with p ⟨hp1, hp2⟩ hp
      rw [M.secondDifferenceQuotient_eq_top_of_not_mem hx hp hp1 hp2]

/-- On `K = {w | df(x̄)(w) = ⟪v, w⟫}`, the quotients `Δ²_τ f(x̄ | v)(w)` are eventually equal to
`d²f(x̄)(w)` along the half-line. -/
theorem eventually_secondDifferenceQuotient_eq [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f) {v w : E}
    (hw : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), secondDifferenceQuotient f x v τ w = M.secondForm w := by
  by_cases hu : w ∈ M.coneUnion
  · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
    filter_upwards [M.eventually_small_ray w] with τ ⟨hτ, hτw⟩
    rw [M.secondDifferenceQuotient_eq_of_mem hi hτ hτw, M.secondForm_eq hf hx hi]
    rw [M.subderivative_eq hf hx hi, EReal.coe_eq_coe_iff] at hw
    rw [hw, sub_self, mul_zero, add_zero]
  · rw [M.subderivative_eq_top hf hx hu] at hw
    exact absurd hw.symm (EReal.coe_ne_top _)

include M in
/-- **Proposition 13.9**: `d²f(x̄ | v)(w)` is the limit of `Δ²_τ f(x̄ | v)(w)` along the
half-line. -/
theorem tendsto_secondDifferenceQuotient [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f) {v : E}
    (hv : ∀ u, ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u) (w : E) :
    Tendsto (fun τ ↦ secondDifferenceQuotient f x v τ w) (𝓝[>] (0 : ℝ))
      (𝓝 (secondSubderivative f x v w)) := by
  rw [M.secondSubderivative_eq hf hx hv w]
  split_ifs with hw
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [M.eventually_secondDifferenceQuotient_eq hf hx hw] with τ hτ
    exact hτ.symm
  · by_cases hu : w ∈ M.coneUnion
    · obtain ⟨j, hj⟩ := M.mem_coneUnion.1 hu
      have hdj := M.subderivative_eq hf hx hj
      have hlt : ⟪v, w⟫_ℝ < ⟪M.grad j, w⟫_ℝ := by
        have h := hv w
        rw [hdj, EReal.coe_le_coe_iff] at h
        rw [hdj, EReal.coe_eq_coe_iff] at hw
        exact lt_of_le_of_ne h (Ne.symm hw)
      set c := ⟪M.grad j, w⟫_ℝ - ⟪v, w⟫_ℝ with hc
      have hcpos : 0 < c := by rw [hc]; linarith
      set s := ⟪w, (M.piece j).matrix w⟫_ℝ with hs
      rw [EReal.tendsto_nhds_top_iff_real]
      intro N
      have hpos : 0 < c / (|N - s| + 1) := by positivity
      filter_upwards [M.eventually_small_ray w, nhdsWithin_le_nhds (Iio_mem_nhds hpos)]
        with τ ⟨hτ, hτw⟩ hτc
      rw [M.secondDifferenceQuotient_eq_of_mem hj hτ hτw, EReal.coe_lt_coe_iff]
      have h1 : τ * (|N - s| + 1) < c := by
        have h := hτc
        rw [mem_Iio, lt_div_iff₀ (by positivity)] at h
        linarith
      have h2 : |N - s| + 1 < c / τ := by rw [lt_div_iff₀ hτ]; linarith
      have h3 : 2 / τ * c = 2 * (c / τ) := by ring
      have habs : N - s ≤ |N - s| := le_abs_self _
      have habs2 : 0 ≤ |N - s| := abs_nonneg _
      rw [← hc, h3, ← hs]
      linarith
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [M.eventually_small_ray w] with τ ⟨hτ, hτw⟩
      rw [M.secondDifferenceQuotient_eq_top_of_not_mem hx hu hτ hτw]

include M in
/-- **Proposition 13.9**: `f` is twice epi-differentiable at `x̄` for every `v` with
`⟪v, ·⟫ ≤ df(x̄)`. -/
theorem twiceEpiDifferentiableAt [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {v : E}
    (hv : ∀ u, ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u) :
    TwiceEpiDifferentiableAt f x v := by
  obtain ⟨i, hi⟩ := M.exists_mem_cone_zero hx
  have hc := M.eq_eval_base ⟨0, hi⟩
  rw [twiceEpiDifferentiableAt_iff_subset]
  refine ⟨by rw [hc]; exact EReal.coe_ne_bot _, by rw [hc]; exact EReal.coe_ne_top _, ?_⟩
  rintro ⟨w, β⟩ hp
  have hp' : secondSubderivative f x v w ≤ (β : EReal) := hp
  rw [M.secondSubderivative_eq hf hx hv w] at hp'
  split_ifs at hp' with hw
  · rw [mem_innerSetLimitAlong]
    intro V hV
    filter_upwards [M.eventually_secondDifferenceQuotient_eq hf hx hw] with τ hτ
    refine ⟨(w, β), ?_, mem_of_mem_nhds hV⟩
    show (β : EReal) ≥ secondDifferenceQuotient f x v τ w
    rw [hτ]
    exact hp'
  · exact absurd hp' (not_le.2 (EReal.coe_lt_top β))

/-- **Formula 13(9)**: `f(x) = f(x̄) + df(x̄)(x - x̄) + ½d²f(x̄)(x - x̄)` on `IB(x̄, δ) ∩ dom f`. -/
theorem eq_expansion_secondForm [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {y : E} (hy : ‖y - x‖ < M.radius)
    (hyd : y ∈ effectiveDomain f) :
    f y = f x + subderivative f x (y - x) + ((1 / 2 : ℝ) : EReal) * M.secondForm (y - x) := by
  have hyd' : x + (y - x) ∈ effectiveDomain f := by rwa [add_sub_cancel]
  obtain ⟨i, hi⟩ := (M.dom_iff (y - x) hy).1 hyd'
  have he := M.eq_expansion hi one_pos (by rwa [one_mul])
  rw [one_smul, add_sub_cancel] at he
  rw [he, M.eq_eval_base ⟨_, hi⟩, M.subderivative_eq hf hx hi, M.secondForm_eq hf hx hi,
    ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add]
  congr 1
  ring

/-- The domain of `df(x̄)` is `⋃ Kᵢ`. -/
theorem effectiveDomain_subderivative [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) : effectiveDomain (subderivative f x) = M.coneUnion := by
  ext u
  rw [mem_effectiveDomain_iff]
  constructor
  · intro h
    by_contra hu
    rw [M.subderivative_eq_top hf hx hu] at h
    exact lt_irrefl _ h
  · intro hu
    obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
    rw [M.subderivative_eq hf hx hi]
    exact EReal.coe_lt_top _

/-- A point is interior to the domain exactly when `⋃ Kᵢ` is the whole space. -/
theorem mem_interior_iff [FiniteDimensional ℝ E] :
    x ∈ interior (effectiveDomain f) ↔ M.coneUnion = univ := by
  constructor
  · intro hint
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hint
    refine eq_univ_of_forall fun u ↦ ?_
    set t := min r M.radius / (2 * (‖u‖ + 1)) with ht
    have htpos : 0 < t := by have := M.radius_pos; positivity
    have htu : t * ‖u‖ < min r M.radius := by
      have h1 : t * ‖u‖ ≤ t * (‖u‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) htpos.le
      have h2 : t * (‖u‖ + 1) = min r M.radius / 2 := by rw [ht]; field_simp
      have h3 : 0 < min r M.radius := lt_min hr M.radius_pos
      linarith
    have hnorm : ‖t • u‖ < min r M.radius := by rwa [norm_smul, Real.norm_of_nonneg htpos.le]
    have hmem : x + t • u ∈ effectiveDomain f := by
      refine interior_subset (hball ?_)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hnorm.trans_le (min_le_left _ _)
    obtain ⟨i, hi⟩ := (M.dom_iff (t • u) (hnorm.trans_le (min_le_right _ _))).1 hmem
    exact M.mem_coneUnion.2 ⟨i, M.mem_cone_of_smul_mem htpos hi⟩
  · intro huniv
    refine mem_interior.2 ⟨ball x M.radius, fun y hy ↦ ?_, isOpen_ball, mem_ball_self M.radius_pos⟩
    have hy' : ‖y - x‖ < M.radius := by rwa [mem_ball, dist_eq_norm] at hy
    have hmem : y - x ∈ M.coneUnion := huniv ▸ mem_univ _
    obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hmem
    have := (M.dom_iff (y - x) hy').2 ⟨i, hi⟩
    rwa [add_sub_cancel] at this

include M in
/-- **Proposition 13.9**: at an interior point of the domain, `f` is twice semidifferentiable. -/
theorem twiceSemidifferentiableAt_of_mem_interior [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hint : x ∈ interior (effectiveDomain f)) :
    TwiceSemidifferentiableAt f x := by
  have hx : x ∈ effectiveDomain f := interior_subset hint
  have huniv := M.mem_interior_iff.1 hint
  obtain ⟨i₀, hi₀⟩ := M.exists_mem_cone_zero hx
  have hc := M.eq_eval_base ⟨0, hi₀⟩
  have hq := M.isPiecewiseLinearQuadratic_secondForm hf hx
  have hqcont : Continuous M.secondForm := by
    rw [← continuousOn_univ, ← huniv, ← M.effectiveDomain_secondForm hf hx]
    exact hq.continuousOn
  have hd := (hf.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic
  have hdcont : Continuous (subderivative f x) := by
    rw [← continuousOn_univ, ← huniv, ← M.effectiveDomain_subderivative hf hx]
    exact hd.continuousOn
  have hfinq : ∀ u, M.secondForm u = ((M.secondForm u).toReal : EReal) := fun u ↦ by
    obtain ⟨i, hi⟩ := M.mem_coneUnion.1 (huniv ▸ mem_univ u)
    rw [M.secondForm_eq hf hx hi, EReal.toReal_coe]
  have hfind : ∀ u, subderivative f x u = ((subderivative f x u).toReal : EReal) := fun u ↦ by
    obtain ⟨i, hi⟩ := M.mem_coneUnion.1 (huniv ▸ mem_univ u)
    rw [M.subderivative_eq hf hx hi, EReal.toReal_coe]
  refine ⟨fun w ↦ ⟨subderivative f x w, by rw [hc]; exact EReal.coe_ne_bot _,
    by rw [hc]; exact EReal.coe_ne_top _, ?_⟩, fun w ↦ ?_⟩
  · -- first order: `Δ_τ f(x̄)(w') = df(x̄)(w') + (τ/2) d²f(x̄)(w')`
    have hreal : Tendsto (fun p : ℝ × E ↦ (subderivative f x p.2).toReal +
        p.1 / 2 * (M.secondForm p.2).toReal) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
        (𝓝 ((subderivative f x w).toReal + 0 / 2 * (M.secondForm w).toReal)) := by
      have h1 : Tendsto (fun p : ℝ × E ↦ (subderivative f x p.2).toReal) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
          (𝓝 (subderivative f x w).toReal) := by
        refine ((EReal.tendsto_toReal ?_ ?_).comp (hdcont.tendsto w)).comp tendsto_snd
        · rw [hfind w]; exact EReal.coe_ne_top _
        · rw [hfind w]; exact EReal.coe_ne_bot _
      have h2 : Tendsto (fun p : ℝ × E ↦ (M.secondForm p.2).toReal) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
          (𝓝 (M.secondForm w).toReal) := by
        refine ((EReal.tendsto_toReal ?_ ?_).comp (hqcont.tendsto w)).comp tendsto_snd
        · rw [hfinq w]; exact EReal.coe_ne_top _
        · rw [hfinq w]; exact EReal.coe_ne_bot _
      have h3 : Tendsto (fun p : ℝ × E ↦ p.1 / 2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (0 / 2)) :=
        ((tendsto_id.mono_left nhdsWithin_le_nhds).comp tendsto_fst).div_const 2
      exact h1.add (h3.mul h2)
    rw [zero_div, zero_mul, add_zero] at hreal
    rw [hfind w]
    refine ((continuous_coe_real_ereal.tendsto _).comp hreal).congr' ?_
    filter_upwards [M.eventually_small w] with p ⟨hp1, hp2⟩
    obtain ⟨i, hi⟩ := M.mem_coneUnion.1 (huniv ▸ mem_univ p.2)
    rw [Function.comp_apply, differenceQuotient_eq_coe (M.eq_eval_base ⟨p.2, hi⟩)
      (M.eq_expansion hi hp1 hp2),
      M.subderivative_eq hf hx hi, M.secondForm_eq hf hx hi, EReal.toReal_coe, EReal.toReal_coe]
    congr 1
    field_simp
    ring
  · rw [M.secondSubderivativeAt_eq hf hx w]
    refine ((hqcont.tendsto w).comp tendsto_snd).congr' ?_
    filter_upwards [M.eventually_small w] with p ⟨hp1, hp2⟩
    rw [Function.comp_apply, M.secondDifferenceQuotientAt_eq hf hx hp1 hp2]

include M in
/-- **Proposition 13.9**: at a boundary point of the domain `f` is not even semidifferentiable,
so it is not twice semidifferentiable. -/
theorem not_semidifferentiableAt_of_not_mem_interior [FiniteDimensional ℝ E]
    (hx : x ∈ effectiveDomain f) (hint : x ∉ interior (effectiveDomain f)) :
    ¬ SemidifferentiableAt f x := by
  intro hsd
  obtain ⟨u, hu⟩ : ∃ u, u ∉ M.coneUnion := by
    by_contra h
    push_neg at h
    exact hint (M.mem_interior_iff.2 (eq_univ_of_forall h))
  obtain ⟨i₀, hi₀⟩ := M.exists_mem_cone_zero hx
  have hc := M.eq_eval_base ⟨0, hi₀⟩
  obtain ⟨β, -, -, hβ⟩ := hsd 0
  have hray : Tendsto (fun τ : ℝ ↦ (τ, (0 : E))) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) :=
    tendsto_id.prodMk tendsto_const_nhds
  have hβ0 : β = 0 := by
    refine tendsto_nhds_unique (hβ.comp hray) (tendsto_const_nhds.congr' ?_)
    filter_upwards with τ
    rw [Function.comp_apply, differenceQuotient_zero_right hc]
  have hpar : Tendsto (fun τ : ℝ ↦ (τ, τ • u)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) := by
    refine tendsto_id.prodMk ?_
    have : Tendsto (fun τ : ℝ ↦ τ • u) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) • u)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hβtop : β = ⊤ := by
    refine tendsto_nhds_unique (hβ.comp hpar) (tendsto_const_nhds.congr' ?_)
    have hsq : Tendsto (fun τ : ℝ ↦ τ * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun τ : ℝ ↦ τ * τ) (𝓝 (0 : ℝ)) (𝓝 (0 * 0)) :=
          (continuous_id.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        exact mul_pos (mem_Ioi.1 hτ) (mem_Ioi.1 hτ)
    filter_upwards [hsq.eventually (M.eventually_small_ray u), self_mem_nhdsWithin]
      with τ ⟨h1, h2⟩ hτ
    rw [Function.comp_apply, differenceQuotient_eq_top hτ hc (by
      rw [smul_smul]; exact M.eq_top_of_not_mem hu h1 h2)]
  rw [hβ0] at hβtop
  exact EReal.zero_ne_top hβtop

/-! #### Convex functions -/

/-- **Proposition 13.9**: for convex `f`, `d²f(x̄) ≥ 0` (midpoint convexity along rays). -/
theorem secondForm_nonneg [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) (hc : Convex ℝ (epigraph f)) (u : E) : 0 ≤ M.secondForm u := by
  by_cases hu : u ∈ M.coneUnion
  · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
    rw [M.secondForm_eq hf hx hi, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    obtain ⟨τ, hτ, hτu⟩ := (M.eventually_small_ray ((2 : ℝ) • u)).exists
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hτu
    set c := (M.piece i).eval x
    set a := ⟪M.grad i, u⟫_ℝ
    set b := ⟪u, (M.piece i).matrix u⟫_ℝ
    have h1 := M.eq_expansion hi hτ (by nlinarith [norm_nonneg u])
    have h2 := M.eq_expansion hi (show 0 < 2 * τ by positivity) (by nlinarith [norm_nonneg u])
    have hx0 : f x = c := M.eq_eval_base ⟨u, hi⟩
    have hp : ((x, c) : E × ℝ) ∈ epigraph f := by
      show (c : EReal) ≥ f x
      rw [hx0]
    have hq : ((x + (2 * τ) • u, c + 2 * τ * a + (2 * τ) ^ 2 / 2 * b) : E × ℝ) ∈ epigraph f := by
      show ((c + 2 * τ * a + (2 * τ) ^ 2 / 2 * b : ℝ) : EReal) ≥ f (x + (2 * τ) • u)
      rw [h2]
    have hmid := hc hp hq (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have e : (1 / 2 : ℝ) • ((x, c) : E × ℝ) +
        (1 / 2 : ℝ) • ((x + (2 * τ) • u, c + 2 * τ * a + (2 * τ) ^ 2 / 2 * b) : E × ℝ) =
        (x + τ • u, c + τ * a + τ ^ 2 * b) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_add, smul_smul]
        rw [← add_assoc, ← add_smul]
        norm_num
        congr 1
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        ring
    rw [e] at hmid
    have hmid' : f (x + τ • u) ≤ ((c + τ * a + τ ^ 2 * b : ℝ) : EReal) := hmid
    rw [h1, EReal.coe_le_coe_iff] at hmid'
    have hτ2 : 0 < τ ^ 2 := by positivity
    nlinarith
  · rw [M.secondForm_eq_top hu]
    exact le_top

/-- The cone `K = {w | df(x̄)(w) = ⟪v, w⟫}` is the union of the polyhedral cones
`Kᵢ ∩ {⟪aᵢ - v, ·⟫ ≤ 0}`. -/
theorem setOf_subderivative_eq_inner [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {v : E}
    (hv : ∀ u, ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u) :
    {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} =
      ⋃ i, (M.cone i ∩ {w | ⟪M.grad i - v, w⟫_ℝ ≤ 0}) := by
  ext w
  simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
  constructor
  · intro hw
    by_cases hu : w ∈ M.coneUnion
    · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
      refine ⟨i, hi, ?_⟩
      rw [M.subderivative_eq hf hx hi, EReal.coe_eq_coe_iff] at hw
      rw [inner_sub_left, hw, sub_self]
    · rw [M.subderivative_eq_top hf hx hu] at hw
      exact absurd hw.symm (EReal.coe_ne_top _)
  · rintro ⟨i, hi, hle⟩
    have h := hv w
    rw [M.subderivative_eq hf hx hi, EReal.coe_le_coe_iff] at h
    rw [M.subderivative_eq hf hx hi, EReal.coe_eq_coe_iff]
    rw [inner_sub_left] at hle
    linarith

theorem isPolyhedral_piece_K [FiniteDimensional ℝ E] (v : E) (i : Fin M.m) :
    IsPolyhedral (M.cone i ∩ {w | ⟪M.grad i - v, w⟫_ℝ ≤ 0}) :=
  (M.polyhedral i).inter (isPolyhedral_linearHalfspace (innerSL ℝ (M.grad i - v)) 0)

include M in
/-- **Proposition 13.9**: `d²f(x̄ | v)` is piecewise linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_secondSubderivative [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f) {v : E}
    (hv : ∀ u, ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u) :
    IsPiecewiseLinearQuadratic (secondSubderivative f x v) := by
  refine ⟨M.m, fun i ↦ M.cone i ∩ {w | ⟪M.grad i - v, w⟫_ℝ ≤ 0}, M.hessPiece,
    M.isPolyhedral_piece_K v, ?_, fun i w hw ↦ ?_⟩
  · rw [← M.setOf_subderivative_eq_inner hf hx hv]
    ext w
    rw [mem_effectiveDomain_iff, M.secondSubderivative_eq hf hx hv, mem_setOf_eq]
    split_ifs with hw
    · simp only [hw, iff_true]
      by_cases hu : w ∈ M.coneUnion
      · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
        rw [M.secondForm_eq hf hx hi]
        exact EReal.coe_lt_top _
      · rw [M.subderivative_eq_top hf hx hu] at hw
        exact absurd hw.symm (EReal.coe_ne_top _)
    · simp [hw]
  · have hK : w ∈ {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} := by
      rw [M.setOf_subderivative_eq_inner hf hx hv]
      exact mem_iUnion.2 ⟨i, hw⟩
    have hK' : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) := hK
    rw [M.secondSubderivative_eq hf hx hv, if_pos hK', M.secondForm_eq hf hx hw.1, hessPiece_eval]

include M in
/-- `d²f(x̄ | v)(0) = 0`. -/
theorem secondSubderivative_zero [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {v : E}
    (hv : ∀ u, ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u) :
    secondSubderivative f x v 0 = 0 := by
  obtain ⟨i, hi⟩ := M.exists_mem_cone_zero hx
  have h0 : subderivative f x 0 = ((⟪v, (0 : E)⟫_ℝ : ℝ) : EReal) := by
    rw [M.subderivative_eq hf hx hi, inner_zero_right, inner_zero_right]
  rw [M.secondSubderivative_eq hf hx hv, if_pos h0, M.secondForm_zero hf hx]

include M in
theorem secondSubderivative_ne_bot [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {v : E}
    (hv : ∀ u, ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u) (w : E) :
    secondSubderivative f x v w ≠ ⊥ := by
  rw [M.secondSubderivative_eq hf hx hv]
  split_ifs
  · exact M.secondForm_ne_bot w
  · exact top_ne_bot

/-! #### Formula 13(10) -/

/-- **Formula 13(10)**: for `w ∈ ⋃ Kᵢ = T_{dom f}(x̄)` with `‖w‖ ≤ 1` and `0 < τ < δ`, and every
`z`, `df(x̄ + τw)(z) = dh₁(w)(z) + ½τ dh₂(w)(z)` with `h₁ = df(x̄)` and `h₂ = d²f(x̄)`. -/
theorem subderivative_add_smul_eq [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {w : E} (hw : w ∈ M.coneUnion) (hw1 : ‖w‖ ≤ 1) {τ : ℝ}
    (hτ : 0 < τ) (hτδ : τ < M.radius) (z : E) :
    subderivative f (x + τ • w) z = subderivative (subderivative f x) w z +
      ((τ / 2 : ℝ) : EReal) * subderivative (secondSubderivativeAt f x) w z := by
  have hh₂ : secondSubderivativeAt f x = M.secondForm := funext (M.secondSubderivativeAt_eq hf hx)
  rw [hh₂]
  have hplq₁ : IsPiecewiseLinearQuadratic (subderivative f x) :=
    (hf.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic
  have hplq₂ := M.isPiecewiseLinearQuadratic_secondForm hf hx
  have hw₁ : w ∈ effectiveDomain (subderivative f x) := by
    rw [M.effectiveDomain_subderivative hf hx]; exact hw
  have hw₂ : w ∈ effectiveDomain M.secondForm := by
    rw [M.effectiveDomain_secondForm hf hx]; exact hw
  have hτw : τ * ‖w‖ < M.radius := lt_of_le_of_lt (mul_le_of_le_one_right hτ.le hw1) hτδ
  obtain ⟨j, hj⟩ := M.mem_coneUnion.1 hw
  have hy : x + τ • w ∈ effectiveDomain f :=
    (M.dom_iff _ (M.norm_smul_lt hτ hτw)).2 ⟨j, M.smul_mem_cone hj hτ⟩
  have L₀ := (hf.hasOneSidedDirDeriv hy z).2.2
  have hs : Tendsto (fun σ : ℝ ↦ τ⁻¹ * σ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_const_mul_nhdsGT_zero (inv_pos.2 hτ)
  have L₁ := (hplq₁.hasOneSidedDirDeriv hw₁ z).2.2.comp hs
  have L₂ := (hplq₂.hasOneSidedDirDeriv hw₂ z).2.2.comp hs
  have hne₁ : subderivative (subderivative f x) w z ≠ ⊥ :=
    (hplq₁.subderivative_piecewiseLinear hw₁).1.isPiecewiseLinearQuadratic.ne_bot z
  have hne₂ : subderivative M.secondForm w z ≠ ⊥ :=
    (hplq₂.subderivative_piecewiseLinear hw₂).1.isPiecewiseLinearQuadratic.ne_bot z
  have L₂' := EReal.Tendsto.const_mul (a := ((τ / 2 : ℝ) : EReal)) L₂
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hne₂' : ((τ / 2 : ℝ) : EReal) * subderivative M.secondForm w z ≠ ⊥ := by
    rcases ereal_trichotomy (subderivative M.secondForm w z) with h | h | ⟨r, h⟩
    · exact absurd h hne₂
    · rw [h, EReal.coe_mul_top_of_pos (by positivity)]; exact top_ne_bot
    · rw [h, ← EReal.coe_mul]; exact EReal.coe_ne_bot _
  have hsum := (EReal.continuousAt_add (Or.inr hne₂') (Or.inl hne₁)).tendsto.comp
    (L₁.prodMk_nhds L₂')
  refine tendsto_nhds_unique L₀ (hsum.congr' ?_)
  -- the eventual identity `Δ_σ f(x̄ + τw)(z) = Δ_s h₁(w)(z) + (τ/2) Δ_s h₂(w)(z)`, `s = σ/τ`
  have hnear : ∀ᶠ σ : ℝ in 𝓝[>] (0 : ℝ), τ * ‖w + (τ⁻¹ * σ) • z‖ < M.radius := by
    have h : Tendsto (fun σ : ℝ ↦ τ * ‖w + (τ⁻¹ * σ) • z‖) (𝓝 (0 : ℝ))
        (𝓝 (τ * ‖w + (τ⁻¹ * 0) • z‖)) := by
      have hc : Continuous (fun σ : ℝ ↦ τ * ‖w + (τ⁻¹ * σ) • z‖) := by fun_prop
      exact hc.tendsto 0
    rw [mul_zero, zero_smul, add_zero] at h
    exact (h.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hτw)
  filter_upwards [hnear, self_mem_nhdsWithin] with σ hσu hσ
  have hσ' : (0 : ℝ) < σ := hσ
  have htpos : 0 < τ⁻¹ * σ := mul_pos (inv_pos.2 hτ) hσ'
  have hstep : x + τ • w + σ • z = x + τ • (w + (τ⁻¹ * σ) • z) := by
    rw [smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul, add_assoc]
  have hcj := M.eq_expansion hj hτ hτw
  have hdj := M.subderivative_eq hf hx hj
  have hqj := M.secondForm_eq hf hx hj
  simp only [Function.comp_apply]
  by_cases hU : w + (τ⁻¹ * σ) • z ∈ M.coneUnion
  · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hU
    have hci := M.eq_expansion hi hτ hσu
    have hbase : (M.piece i).eval x = (M.piece j).eval x := by
      have := (M.eq_eval_base ⟨_, hi⟩).symm.trans (M.eq_eval_base ⟨w, hj⟩)
      exact_mod_cast this
    rw [differenceQuotient_eq_coe hcj (by rw [hstep]; exact hci),
      differenceQuotient_eq_coe hdj (M.subderivative_eq hf hx hi),
      differenceQuotient_eq_coe hqj (M.secondForm_eq hf hx hi), ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_eq_coe_iff, hbase]
    generalize ⟪M.grad i, w + (τ⁻¹ * σ) • z⟫_ℝ = A
    generalize ⟪w + (τ⁻¹ * σ) • z, (M.piece i).matrix (w + (τ⁻¹ * σ) • z)⟫_ℝ = B
    field_simp
    ring
  · have htop : f (x + τ • w + σ • z) = ⊤ := by
      rw [hstep]; exact M.eq_top_of_not_mem hU hτ hσu
    rw [differenceQuotient_eq_top hσ' hcj htop,
      differenceQuotient_eq_top htpos hdj (M.subderivative_eq_top hf hx hU),
      differenceQuotient_eq_top htpos hqj (M.secondForm_eq_top hU),
      EReal.coe_mul_top_of_pos (by positivity), EReal.top_add_top]

end PLQLocalModel

/-- For a convex function with finite value at `x̄`, subgradients are minorized by `df(x̄)`. -/
theorem inner_le_subderivative_of_convex [FiniteDimensional ℝ E] {f : E → EReal} {x v : E}
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) {c : ℝ} (hx : f x = c)
    (hv : v ∈ subdifferential f x) (u : E) :
    ((⟪v, u⟫_ℝ : ℝ) : EReal) ≤ subderivative f x u := by
  rw [subdifferential_eq_regularSubdifferential_of_convex hc hp hx] at hv
  exact (mem_regularSubdifferential_iff_inner_le_subderivative hx).1 hv u

/-! ### Proposition 13.9 -/

/-- **Proposition 13.9** (piecewise linear-quadratic functions).  Let `f` be proper, convex and
piecewise linear-quadratic, and `x̄ ∈ dom f`.

* `d²f(x̄)` is proper, piecewise linear-quadratic and nonnegative, and its values are limits
  along half-lines: `d²f(x̄)(w) = lim_{τ ↓ 0} Δ²_τ f(x̄)(w)`.
* For every `v ∈ ∂f(x̄)`, `d²f(x̄ | v)` is proper, convex and piecewise linear-quadratic, the set
  `K(x̄, v) = {w | df(x̄)(w) = ⟪v, w⟫}` is a polyhedral cone, and
  `d²f(x̄ | v)(w) = lim_{τ ↓ 0} Δ²_τ f(x̄ | v)(w) = d²f(x̄)(w) + δ_K(w)`; `f` is twice
  epi-differentiable at `x̄` for `v`.
* `f` is twice semidifferentiable at `x̄` exactly when `x̄ ∈ int(dom f)`.
* Formula 13(9): `f(x) = f(x̄) + df(x̄)(x - x̄) + ½d²f(x̄)(x - x̄)` for `x ∈ V ∩ dom f`.
* Formula 13(10): for some `ε > 0`, `df(x̄ + τw)(z) = dh₁(w)(z) + ½τ dh₂(w)(z)` with
  `h₁ = df(x̄)`, `h₂ = d²f(x̄)`, whenever `w ∈ T_{dom f}(x̄)`, `‖w‖ ≤ 1` and `τ ∈ (0, ε)`. -/
theorem piecewise_linear_quadratic_second_order [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hc : Convex ℝ (epigraph f)) {x : E}
    (hx : x ∈ effectiveDomain f) :
    (IsProper (secondSubderivativeAt f x) ∧
      IsPiecewiseLinearQuadratic (secondSubderivativeAt f x) ∧
      ∀ w, 0 ≤ secondSubderivativeAt f x w ∧
        Tendsto (fun τ ↦ secondDifferenceQuotientAt f x τ w) (𝓝[>] (0 : ℝ))
          (𝓝 (secondSubderivativeAt f x w))) ∧
    (∀ v ∈ subdifferential f x,
      IsProper (secondSubderivative f x v) ∧ Convex ℝ (epigraph (secondSubderivative f x v)) ∧
      IsPiecewiseLinearQuadratic (secondSubderivative f x v) ∧
      IsPolyhedral {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} ∧
      IsCone {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} ∧
      (∀ w, secondSubderivative f x v w = secondSubderivativeAt f x w +
          indicatorVA {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} w ∧
        Tendsto (fun τ ↦ secondDifferenceQuotient f x v τ w) (𝓝[>] (0 : ℝ))
          (𝓝 (secondSubderivative f x v w))) ∧
      TwiceEpiDifferentiableAt f x v) ∧
    (TwiceSemidifferentiableAt f x ↔ x ∈ interior (effectiveDomain f)) ∧
    (∃ V ∈ 𝓝 x, ∀ y ∈ V ∩ effectiveDomain f,
      f y = f x + subderivative f x (y - x) +
        ((1 / 2 : ℝ) : EReal) * secondSubderivativeAt f x (y - x)) ∧
    (∃ ε > 0, ∀ w ∈ tangentCone (effectiveDomain f) x, ‖w‖ ≤ 1 → ∀ τ, 0 < τ → τ < ε → ∀ z,
      subderivative f (x + τ • w) z = subderivative (subderivative f x) w z +
        ((τ / 2 : ℝ) : EReal) * subderivative (secondSubderivativeAt f x) w z) := by
  obtain ⟨M⟩ := hf.nonempty_localModel x
  have hh₂ : secondSubderivativeAt f x = M.secondForm := funext (M.secondSubderivativeAt_eq hf hx)
  have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (hf.ne_bot x)).symm
  have hp : IsProper f := ⟨⟨x, hx⟩, fun y ↦ lt_of_le_of_ne bot_le (hf.ne_bot y).symm⟩
  have htan : tangentCone (effectiveDomain f) x = M.coneUnion := by
    rw [← (hf.subderivative_piecewiseLinear hx).2, M.effectiveDomain_subderivative hf hx]
  refine ⟨⟨?_, ?_, fun w ↦ ⟨?_, ?_⟩⟩, fun v hv ↦ ?_, ?_, ?_, ?_⟩
  · rw [hh₂, isProper_iff]
    exact ⟨⟨0, by rw [mem_effectiveDomain_iff, M.secondForm_zero hf hx]; exact EReal.zero_lt_top⟩,
      fun u ↦ lt_of_le_of_ne bot_le (M.secondForm_ne_bot u).symm⟩
  · rw [hh₂]
    exact M.isPiecewiseLinearQuadratic_secondForm hf hx
  · rw [hh₂]
    exact M.secondForm_nonneg hf hx hc w
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [M.eventually_secondDifferenceQuotientAt_eq hf hx w] with τ hτ
    rw [hτ, hh₂]
  · have hv' := inner_le_subderivative_of_convex hp hc hfin hv
    have hepi := M.twiceEpiDifferentiableAt hf hx hv'
    have hconv : Convex ℝ (epigraph (secondSubderivative f x v)) :=
      convex_epigraph_secondSubderivative_of_convex hc hfin hepi
    have hK := M.setOf_subderivative_eq_inner hf hx hv'
    have hdomK : effectiveDomain (secondSubderivative f x v) =
        {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} := by
      ext w
      rw [mem_effectiveDomain_iff, M.secondSubderivative_eq hf hx hv', mem_setOf_eq]
      split_ifs with hw
      · simp only [hw, iff_true]
        by_cases hu : w ∈ M.coneUnion
        · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
          rw [M.secondForm_eq hf hx hi]
          exact EReal.coe_lt_top _
        · rw [M.subderivative_eq_top hf hx hu] at hw
          exact absurd hw.symm (EReal.coe_ne_top _)
      · simp [hw]
    refine ⟨?_, hconv, M.isPiecewiseLinearQuadratic_secondSubderivative hf hx hv', ?_, ?_,
      fun w ↦ ⟨?_, M.tendsto_secondDifferenceQuotient hf hx hv' w⟩, hepi⟩
    · have h0 : (0 : E) ∈ effectiveDomain (secondSubderivative f x v) := by
        rw [mem_effectiveDomain_iff, M.secondSubderivative_zero hf hx hv']
        exact EReal.zero_lt_top
      rw [isProper_iff]
      exact ⟨⟨0, h0⟩, fun u ↦ lt_of_le_of_ne bot_le (M.secondSubderivative_ne_bot hf hx hv' u).symm⟩
    · rw [hK]
      refine isPolyhedral_iUnion_of_convex (M.isPolyhedral_piece_K v) ?_
      rw [← hK, ← hdomK]
      exact convex_effectiveDomain_of_convex_epigraph hconv
    · rw [hK]
      obtain ⟨i₀, hi₀⟩ := M.exists_mem_cone_zero hx
      refine ⟨mem_iUnion.2 ⟨i₀, hi₀, by simp⟩, fun w hw c hcpos ↦ ?_⟩
      obtain ⟨i, hi, hle⟩ := mem_iUnion.1 hw
      refine mem_iUnion.2 ⟨i, M.smul_mem_cone hi hcpos, ?_⟩
      have hle' : ⟪M.grad i - v, w⟫_ℝ ≤ 0 := hle
      show ⟪M.grad i - v, c • w⟫_ℝ ≤ 0
      rw [real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos hcpos.le hle'
    · rw [M.secondSubderivative_eq hf hx hv', hh₂]
      split_ifs with hw
      · rw [indicatorVA_apply_mem (show w ∈ {w | subderivative f x w =
          ((⟪v, w⟫_ℝ : ℝ) : EReal)} from hw), add_zero]
      · rw [indicatorVA_apply_not_mem (show w ∉ {w | subderivative f x w =
          ((⟪v, w⟫_ℝ : ℝ) : EReal)} from hw), EReal.add_top_of_ne_bot (M.secondForm_ne_bot w)]
  · constructor
    · intro h
      by_contra hint
      exact M.not_semidifferentiableAt_of_not_mem_interior hx hint h.1
    · exact M.twiceSemidifferentiableAt_of_mem_interior hf
  · refine ⟨ball x M.radius, ball_mem_nhds x M.radius_pos, fun y ⟨hy, hyd⟩ ↦ ?_⟩
    rw [hh₂]
    exact M.eq_expansion_secondForm hf hx (by rwa [mem_ball, dist_eq_norm] at hy) hyd
  · refine ⟨M.radius, M.radius_pos, fun w hw hw1 τ hτ hτε z ↦ ?_⟩
    rw [htan] at hw
    exact M.subderivative_add_smul_eq hf hx hw hw1 hτ hτε z

end RW
