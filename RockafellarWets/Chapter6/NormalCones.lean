/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Normal Cones and Clarke Regularity

Section B of Chapter 6 is Definitions 6.3 and 6.4 and Propositions 6.5 and
6.6: the regular normal cone `N̂_C(x̄)`, the normal cone `N_C(x̄)` obtained
from it by a limit, Clarke regularity, and the outer semicontinuity of
`N_C` relative to `C`.
-/

import RockafellarWets.Chapter6.TangentCones

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section OuterLimitAux

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- The relative outer limit of formula 5(1) absorbs a second application of
itself. -/
theorem svOuterLimitWithin_svOuterLimitWithin_subset (S : E → Set F) (X : Set E)
    (x : E) :
    svOuterLimitWithin (fun z ↦ svOuterLimitWithin S X z) X x ⊆
      svOuterLimitWithin S X x := by
  intro v hv V hV
  rw [Filter.frequently_iff]
  intro A hA
  obtain ⟨U, hUopen, hxU, hUA⟩ := mem_nhdsWithin.1 hA
  obtain ⟨W, hWV, hWopen, hvW⟩ := mem_nhds_iff.1 hV
  obtain ⟨z, hzU, u, huz, huW⟩ :=
    Filter.frequently_iff.1 (hv W (hWopen.mem_nhds hvW))
      (mem_nhdsWithin.2 ⟨U, hUopen, hxU, Subset.rfl⟩)
  obtain ⟨y, hyU, t, hty, htW⟩ :=
    Filter.frequently_iff.1 (huz W (hWopen.mem_nhds huW))
      (mem_nhdsWithin.2 ⟨U, hUopen, hzU.1, Subset.rfl⟩)
  exact ⟨y, hUA hyU, t, hty, hWV htW⟩

/-- A sequence in `X` tending to `x` along which points of `S` converge puts
the limit in the relative outer limit of formula 5(1). -/
theorem mem_svOuterLimitWithin_of_tendsto {S : E → Set F} {X : Set E} {x : E}
    {xs : ℕ → E} {us : ℕ → F} {u : F} (hxX : ∀ n, xs n ∈ X)
    (hxto : Tendsto xs atTop (nhds x)) (hus : ∀ n, us n ∈ S (xs n))
    (huto : Tendsto us atTop (nhds u)) : u ∈ svOuterLimitWithin S X x := by
  intro V hV
  rw [Filter.frequently_iff]
  intro A hA
  have h1 : ∀ᶠ n in atTop, xs n ∈ A :=
    (tendsto_nhdsWithin_of_forall_mem hxX hxto) hA
  obtain ⟨n, hnA, hnV⟩ := (h1.and (huto hV)).exists
  exact ⟨xs n, hnA, us n, hus n, hnV⟩

/-- A mapping that is empty off `X` cannot tell the relative outer limit from
the full one. -/
theorem svOuterLimitWithin_eq_svOuterLimit_of_eq_empty {S : E → Set F} {X : Set E}
    (hS : ∀ y, y ∉ X → S y = ∅) (x : E) :
    svOuterLimitWithin S X x = svOuterLimit S x := by
  refine Subset.antisymm (outerSetLimitAlong_mono_filter nhdsWithin_le_nhds S) ?_
  intro v hv V hV
  rw [Filter.frequently_iff]
  intro A hA
  obtain ⟨U, hUopen, hxU, hUA⟩ := mem_nhdsWithin.1 hA
  obtain ⟨y, hyU, u, huy, huV⟩ :=
    Filter.frequently_iff.1 (hv V hV) (hUopen.mem_nhds hxU)
  have hyX : y ∈ X := by
    by_contra hy
    rw [hS y hy] at huy
    exact huy
  exact ⟨y, hUA ⟨hyU, hyX⟩, u, huy, huV⟩

end OuterLimitAux

section LocallyClosed

variable {E : Type*} [TopologicalSpace E]

/-- The book's local closedness, from the paragraph opening Chapter 1I*:
`C ∩ V` is closed for some closed neighborhood `V` of `x̄`, which need not
belong to `C`.  This is *not* Mathlib's `IsLocallyClosed`, which asks a set to
be the intersection of an open set with a closed one. -/
def IsLocallyClosedAt (C : Set E) (x : E) : Prop :=
  ∃ V ∈ nhds x, IsClosed V ∧ IsClosed (C ∩ V)

/-- A closed set is locally closed at every point; the book notes that the
converse is the test for global closedness. -/
theorem IsClosed.isLocallyClosedAt {C : Set E} (hC : IsClosed C) (x : E) :
    IsLocallyClosedAt C x :=
  ⟨univ, univ_mem, isClosed_univ, by simpa using hC⟩

end LocallyClosed

section NormalCones

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Definition 6.3**, formula 6(4) read as 6(5): `v` is a *regular normal*
to `C` at `x̄`. -/
def regularNormalCone (C : Set E) (x : E) : Set E :=
  {v | x ∈ C ∧ ∀ ε > 0, ∀ᶠ y in nhdsWithin x C, ⟪v, y - x⟫_ℝ ≤ ε * ‖y - x‖}

theorem mem_regularNormalCone {C : Set E} {x v : E} :
    v ∈ regularNormalCone C x ↔
      x ∈ C ∧ ∀ ε > 0, ∀ᶠ y in nhdsWithin x C, ⟪v, y - x⟫_ℝ ≤ ε * ‖y - x‖ :=
  Iff.rfl

/-- Formula 6(8) for the regular normals. -/
theorem regularNormalCone_eq_empty {C : Set E} {x : E} (hx : x ∉ C) :
    regularNormalCone C x = ∅ :=
  eq_empty_of_forall_notMem fun _ hv ↦ hx hv.1

theorem mem_of_mem_regularNormalCone {C : Set E} {x v : E}
    (hv : v ∈ regularNormalCone C x) : x ∈ C := hv.1

/-- The `ε`-`δ` reading of 6(4). -/
theorem mem_regularNormalCone_iff {C : Set E} {x v : E} :
    v ∈ regularNormalCone C x ↔ x ∈ C ∧ ∀ ε > 0, ∃ δ > 0, ∀ y ∈ C,
      ‖y - x‖ < δ → ⟪v, y - x⟫_ℝ ≤ ε * ‖y - x‖ := by
  rw [mem_regularNormalCone]
  refine and_congr_right fun _ ↦ forall₂_congr fun ε _ ↦ ?_
  rw [Metric.nhdsWithin_basis_ball.eventually_iff]
  constructor
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun y hyC hyd ↦ h ⟨mem_ball.2 (by rwa [dist_eq_norm]), hyC⟩⟩
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hy ↦ h y hy.2 ?_⟩
    rw [← dist_eq_norm]
    exact mem_ball.1 hy.1

/-- **Definition 6.3**: `v` is a normal vector to `C` at `x̄` when it is a
limit of regular normals at points of `C` approaching `x̄`. -/
def normalCone (C : Set E) (x : E) : Set E :=
  {v | x ∈ C ∧ ∃ (xs : ℕ → E) (vs : ℕ → E), (∀ n, xs n ∈ C) ∧
    Tendsto xs atTop (nhds x) ∧ (∀ n, vs n ∈ regularNormalCone C (xs n)) ∧
    Tendsto vs atTop (nhds v)}

/-- Formula 6(8) for the normal cone. -/
theorem normalCone_eq_empty {C : Set E} {x : E} (hx : x ∉ C) :
    normalCone C x = ∅ :=
  eq_empty_of_forall_notMem fun _ hv ↦ hx hv.1

/-- The convergence `xν →_C x̄` printed in 6.3 asks `xν ∈ C` separately, but
that is already carried by `vν ∈ N̂_C(xν)`: the regular normal cone is empty
off `C`. -/
theorem mem_normalCone_of_forall {C : Set E} {x v : E} (hx : x ∈ C) {xs vs : ℕ → E}
    (hxto : Tendsto xs atTop (nhds x)) (hvs : ∀ n, vs n ∈ regularNormalCone C (xs n))
    (hvto : Tendsto vs atTop (nhds v)) : v ∈ normalCone C x :=
  ⟨hx, xs, vs, fun n ↦ (hvs n).1, hxto, hvs, hvto⟩

/-- **Proposition 6.5**, formula 6(7): every regular normal is a normal
vector, the constant sequence at `x̄` being admissible in 6.3. -/
theorem regularNormalCone_subset_normalCone (C : Set E) (x : E) :
    regularNormalCone C x ⊆ normalCone C x := fun _ hv ↦
  mem_normalCone_of_forall hv.1 (xs := fun _ ↦ x) (vs := fun _ ↦ _)
    tendsto_const_nhds (fun _ ↦ hv) tendsto_const_nhds

/-- **Proposition 6.5**, formula 6(7): the normal cone is the outer limit of
the regular normal cones as `x →_C x̄`.  This is the identification of
Definition 6.3 with the relative outer limit of formula 5(1) applied to the
set-valued mapping `x ↦ N̂_C(x)`. -/
theorem normalCone_eq_svOuterLimitWithin {C : Set E} {x : E} (hx : x ∈ C) :
    normalCone C x = svOuterLimitWithin (regularNormalCone C) C x := by
  refine Subset.antisymm ?_ ?_
  · rintro v ⟨-, xs, vs, hxC, hxto, hvs, hvto⟩
    exact mem_svOuterLimitWithin_of_tendsto hxC hxto hvs hvto
  · intro v hv
    have hpick : ∀ n : ℕ, ∃ y : E, ∃ u : E, y ∈ C ∧ dist y x < 1 / ((n : ℝ) + 1) ∧
        u ∈ regularNormalCone C y ∧ dist u v < 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨y, hyA, u, huy, huV⟩ :=
        Filter.frequently_iff.1 (hv (ball v (1 / ((n : ℝ) + 1))) (ball_mem_nhds v hpos))
          (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hpos))
            self_mem_nhdsWithin)
      exact ⟨y, u, hyA.2, mem_ball.1 hyA.1, huy, mem_ball.1 huV⟩
    choose xs vs hxC hxd hvs hvd using hpick
    refine mem_normalCone_of_forall hx ?_ hvs ?_
    · rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hxd n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    · rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hvd n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Proposition 6.5**: the regular normal cone is a cone.  The zero vector
satisfies 6(4) trivially, and rescaling `v` by `c > 0` is rescaling the `ε` of
6(5) by `1/c`. -/
theorem isCone_regularNormalCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (regularNormalCone C x) := by
  constructor
  · refine ⟨hx, fun ε hε ↦ Filter.Eventually.of_forall fun y ↦ ?_⟩
    rw [inner_zero_left]
    exact mul_nonneg hε.le (norm_nonneg _)
  · rintro v ⟨-, hv⟩ c hc
    refine ⟨hx, fun ε hε ↦ ?_⟩
    filter_upwards [hv (ε / c) (by positivity)] with y hy
    rw [real_inner_smul_left]
    calc c * ⟪v, y - x⟫_ℝ ≤ c * (ε / c * ‖y - x‖) :=
          mul_le_mul_of_nonneg_left hy hc.le
      _ = ε * ‖y - x‖ := by field_simp

/-- **Proposition 6.5**: the regular normal cone is convex.  The book obtains
this from 6(6), as an intersection of half-spaces; 6(5) gives it directly,
because a convex combination of two vectors satisfying the `ε` inequality
satisfies it with the same `ε`. -/
theorem convex_regularNormalCone (C : Set E) (x : E) :
    Convex ℝ (regularNormalCone C x) := by
  by_cases hx : x ∈ C
  · rintro v₁ ⟨-, h₁⟩ v₂ ⟨-, h₂⟩ a b ha hb hab
    refine ⟨hx, fun ε hε ↦ ?_⟩
    filter_upwards [h₁ ε hε, h₂ ε hε] with y hy₁ hy₂
    have hexp : ⟪a • v₁ + b • v₂, y - x⟫_ℝ
        = a * ⟪v₁, y - x⟫_ℝ + b * ⟪v₂, y - x⟫_ℝ := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have hsum : a * (ε * ‖y - x‖) + b * (ε * ‖y - x‖) = ε * ‖y - x‖ := by
      rw [← add_mul, hab, one_mul]
    rw [hexp]
    linarith [mul_le_mul_of_nonneg_left hy₁ ha, mul_le_mul_of_nonneg_left hy₂ hb]
  · rw [regularNormalCone_eq_empty hx]
    exact convex_empty

/-- **Proposition 6.5**: the regular normal cone is closed.  Again this is
direct from 6(5) rather than through 6(6): a vector within `ε/2` of one
satisfying the `ε/2` inequality satisfies the `ε` inequality, by
Cauchy--Schwarz. -/
theorem isClosed_regularNormalCone (C : Set E) (x : E) :
    IsClosed (regularNormalCone C x) := by
  by_cases hx : x ∈ C
  · rw [← closure_subset_iff_isClosed]
    intro v hv
    refine ⟨hx, fun ε hε ↦ ?_⟩
    obtain ⟨v₀, hv₀ball, hv₀⟩ :=
      mem_closure_iff_nhds.1 hv (ball v (ε / 2)) (ball_mem_nhds v (by linarith))
    filter_upwards [hv₀.2 (ε / 2) (by linarith)] with y hy
    have hnorm : ‖v - v₀‖ ≤ ε / 2 := by
      rw [← dist_eq_norm, dist_comm]
      exact (mem_ball.1 hv₀ball).le
    have hmul : ‖v - v₀‖ * ‖y - x‖ ≤ ε / 2 * ‖y - x‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    have hsplit : ⟪v, y - x⟫_ℝ = ⟪v₀, y - x⟫_ℝ + ⟪v - v₀, y - x⟫_ℝ := by
      have hv₀v : v₀ + (v - v₀) = v := by abel
      rw [← inner_add_left, hv₀v]
    have hcs : ⟪v - v₀, y - x⟫_ℝ ≤ ‖v - v₀‖ * ‖y - x‖ := real_inner_le_norm _ _
    linarith
  · rw [regularNormalCone_eq_empty hx]
    exact isClosed_empty

/-- **Proposition 6.5**: the normal cone is a cone. -/
theorem isCone_normalCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (normalCone C x) := by
  constructor
  · exact regularNormalCone_subset_normalCone C x (isCone_regularNormalCone hx).1
  · rintro v ⟨-, xs, vs, hxC, hxto, hvs, hvto⟩ c hc
    exact ⟨hx, xs, fun n ↦ c • vs n, hxC, hxto,
      fun n ↦ (isCone_regularNormalCone (hvs n).1).2 (hvs n) hc, hvto.const_smul c⟩

/-- **Proposition 6.5**: the normal cone is closed.  With 6(7) this is the
closedness of an outer limit, `isClosed_outerSetLimitAlong`. -/
theorem isClosed_normalCone (C : Set E) (x : E) : IsClosed (normalCone C x) := by
  by_cases hx : x ∈ C
  · rw [normalCone_eq_svOuterLimitWithin hx]
    exact isClosed_outerSetLimitAlong _ _
  · rw [normalCone_eq_empty hx]
    exact isClosed_empty

/-- **Proposition 6.5**, the implication `⇒` of formula 6(6): a regular normal
makes a nonpositive inner product with every tangent vector.  Only this half
is dimension-free. -/
theorem inner_nonpos_of_mem_regularNormalCone {C : Set E} {x v : E}
    (hv : v ∈ regularNormalCone C x) {w : E} (hw : w ∈ tangentCone C x) :
    ⟪v, w⟫_ℝ ≤ 0 := by
  obtain ⟨xs, τs, hxC, hxto, hτpos, -, hq⟩ := hw
  have key : ∀ ε > 0, ⟪v, w⟫_ℝ ≤ ε * ‖w‖ := by
    intro ε hε
    have hev : ∀ᶠ n in atTop, ⟪v, (τs n)⁻¹ • (xs n - x)⟫_ℝ
        ≤ ε * ‖(τs n)⁻¹ • (xs n - x)‖ := by
      have hin : Tendsto xs atTop (nhdsWithin x C) :=
        tendsto_nhdsWithin_of_forall_mem hxC hxto
      filter_upwards [hin (hv.2 ε hε)] with n hn
      have hτ : (0 : ℝ) < τs n := hτpos n
      rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hτ)]
      calc (τs n)⁻¹ * ⟪v, xs n - x⟫_ℝ ≤ (τs n)⁻¹ * (ε * ‖xs n - x‖) :=
            mul_le_mul_of_nonneg_left hn (inv_pos.2 hτ).le
        _ = ε * ((τs n)⁻¹ * ‖xs n - x‖) := by ring
    exact le_of_tendsto_of_tendsto (Filter.Tendsto.inner tendsto_const_nhds hq)
      (hq.norm.const_mul ε) hev
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  have hbound : δ / (‖w‖ + 1) * ‖w‖ ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have := key (δ / (‖w‖ + 1)) (by positivity)
  linarith

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Proposition 6.5**, the implication `⇐` of formula 6(6).  This is the one
place in Section B where the ambient finite-dimensionality of the book's
`IRⁿ` is used: the printed proof normalizes the difference quotients to unit
length and passes to a convergent subsequence, which is compactness of the
unit ball. -/
theorem mem_regularNormalCone_of_forall_inner_nonpos {C : Set E} {x : E}
    (hx : x ∈ C) {v : E} (h : ∀ w ∈ tangentCone C x, ⟪v, w⟫_ℝ ≤ 0) :
    v ∈ regularNormalCone C x := by
  refine ⟨hx, fun ε hε ↦ ?_⟩
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hpick : ∀ n : ℕ, ∃ y : E, y ∈ C ∧ ‖y - x‖ < 1 / ((n : ℝ) + 1) ∧
      ε * ‖y - x‖ < ⟪v, y - x⟫_ℝ := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨y, hyA, hy⟩ := Filter.frequently_iff.1 hcon
      (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hpos))
        self_mem_nhdsWithin)
    refine ⟨y, hyA.2, ?_, not_le.1 hy⟩
    rw [← dist_eq_norm]
    exact mem_ball.1 hyA.1
  choose ys hyC hyd hyi using hpick
  have hτpos : ∀ n, 0 < ‖ys n - x‖ := by
    intro n
    rcases (norm_nonneg (ys n - x)).eq_or_lt with hzero | hpos
    · exfalso
      have hz : ys n - x = 0 := by rwa [eq_comm, norm_eq_zero] at hzero
      have hcon' := hyi n
      rw [hz, inner_zero_right, norm_zero, mul_zero] at hcon'
      exact lt_irrefl _ hcon'
    · exact hpos
  have hwball : ∀ n, ‖ys n - x‖⁻¹ • (ys n - x) ∈ closedBall (0 : E) 1 := by
    intro n
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hτpos n)), inv_mul_cancel₀ (hτpos n).ne']
  obtain ⟨w, -, φ, hφ, hwto⟩ :=
    (isCompact_closedBall (0 : E) 1).tendsto_subseq hwball
  have hinner : ∀ n, ε < ⟪v, ‖ys n - x‖⁻¹ • (ys n - x)⟫_ℝ := by
    intro n
    have hne : ‖ys n - x‖ ≠ 0 := (hτpos n).ne'
    rw [real_inner_smul_right]
    calc ε = ‖ys n - x‖⁻¹ * (ε * ‖ys n - x‖) := by field_simp
      _ < ‖ys n - x‖⁻¹ * ⟪v, ys n - x⟫_ℝ :=
          mul_lt_mul_of_pos_left (hyi n) (inv_pos.2 (hτpos n))
  have hwmem : w ∈ tangentCone C x := by
    refine mem_tangentCone_of_forall (xs := fun n ↦ ys (φ n))
      (τs := fun n ↦ ‖ys (φ n) - x‖) (fun n ↦ hyC (φ n)) (fun n ↦ hτpos (φ n))
      ?_ hwto
    have h1 : Tendsto (fun n ↦ ‖ys n - x‖) atTop (nhds 0) :=
      squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (hyd n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop
  have hge : ε ≤ ⟪v, w⟫_ℝ :=
    ge_of_tendsto (Filter.Tendsto.inner tendsto_const_nhds hwto)
      (Filter.Eventually.of_forall fun n ↦ (hinner (φ n)).le)
  have := h w hwmem
  linarith

/-- **Proposition 6.5**, formula 6(6): the regular normals are exactly the
vectors making a nonpositive inner product with every tangent vector. -/
theorem mem_regularNormalCone_iff_inner_nonpos {C : Set E} {x : E} (hx : x ∈ C)
    {v : E} :
    v ∈ regularNormalCone C x ↔ ∀ w ∈ tangentCone C x, ⟪v, w⟫_ℝ ≤ 0 :=
  ⟨fun hv _ hw ↦ inner_nonpos_of_mem_regularNormalCone hv hw,
    mem_regularNormalCone_of_forall_inner_nonpos hx⟩

/-- **Proposition 6.5**, formula 6(6) as a set identity: the regular normal
cone is the intersection of the closed half-spaces determined by the tangent
cone. -/
theorem regularNormalCone_eq_iInter {C : Set E} {x : E} (hx : x ∈ C) :
    regularNormalCone C x = ⋂ w ∈ tangentCone C x, {v : E | ⟪v, w⟫_ℝ ≤ 0} := by
  ext v
  rw [mem_regularNormalCone_iff_inner_nonpos hx, mem_iInter₂]
  rfl

end FiniteDimensional

/-! ### Definition 6.4: Clarke regularity -/

/-- **Definition 6.4**: `C` is *regular at `x̄` in the sense of Clarke* when it
is locally closed at `x̄` and every normal vector there is a regular normal. -/
def IsClarkeRegularAt (C : Set E) (x : E) : Prop :=
  IsLocallyClosedAt C x ∧ normalCone C x = regularNormalCone C x

/-- One inclusion in Definition 6.4 is free, by 6(7). -/
theorem isClarkeRegularAt_iff {C : Set E} {x : E} :
    IsClarkeRegularAt C x ↔
      IsLocallyClosedAt C x ∧ normalCone C x ⊆ regularNormalCone C x :=
  and_congr_right fun _ ↦
    ⟨fun h ↦ h.subset,
      fun h ↦ Subset.antisymm h (regularNormalCone_subset_normalCone C x)⟩

/-! ### Proposition 6.6: limits of normal vectors -/

/-- **Proposition 6.6**: `N_C` is outer semicontinuous at `x̄` relative to `C`.
With 6(7) this is the statement that the relative outer limit of formula 5(1)
absorbs a second application of itself. -/
theorem svOscWithinAt_normalCone {C : Set E} {x : E} (hx : x ∈ C) :
    SvOscWithinAt (normalCone C) C x := by
  have hcongr : normalCone C =ᶠ[nhdsWithin x C]
      fun z ↦ svOuterLimitWithin (regularNormalCone C) C z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
      using normalCone_eq_svOuterLimitWithin hz
  have hstep : svOuterLimitWithin (normalCone C) C x =
      svOuterLimitWithin (fun z ↦ svOuterLimitWithin (regularNormalCone C) C z) C x :=
    outerSetLimitAlong_congr hcongr
  have key : svOuterLimitWithin (normalCone C) C x ⊆ normalCone C x := by
    rw [hstep, normalCone_eq_svOuterLimitWithin hx]
    exact svOuterLimitWithin_svOuterLimitWithin_subset _ _ _
  exact key

/-- **Proposition 6.6**: `N_C` is outer semicontinuous relative to `C` at every
point of `C`. -/
theorem svOscOn_normalCone (C : Set E) : SvOscOn (normalCone C) C :=
  fun _ hx ↦ svOscWithinAt_normalCone hx

/-- **Proposition 6.6** as printed: if `xν →_C x̄`, `vν ∈ N_C(xν)` and
`vν → v`, then `v ∈ N_C(x̄)`. -/
theorem mem_normalCone_of_tendsto {C : Set E} {x : E} (hx : x ∈ C) {xs vs : ℕ → E}
    (hxC : ∀ n, xs n ∈ C) (hxto : Tendsto xs atTop (nhds x))
    (hvs : ∀ n, vs n ∈ normalCone C (xs n)) {v : E}
    (hvto : Tendsto vs atTop (nhds v)) : v ∈ normalCone C x :=
  svOscWithinAt_normalCone hx
    (mem_svOuterLimitWithin_of_tendsto hxC hxto hvs hvto)

/-- The paragraph after 6.6: with the convention 6(8), `C` is the domain of the
regular normal cone mapping. -/
theorem svDom_regularNormalCone (C : Set E) : svDom (regularNormalCone C) = C := by
  ext x
  exact ⟨fun ⟨_, hv⟩ ↦ hv.1, fun hx ↦ ⟨0, (isCone_regularNormalCone hx).1⟩⟩

/-- The paragraph after 6.6: with the convention 6(8), `C` is the domain of the
normal cone mapping. -/
theorem svDom_normalCone (C : Set E) : svDom (normalCone C) = C := by
  ext x
  exact ⟨fun ⟨_, hv⟩ ↦ hv.1,
    fun hx ↦ ⟨0, regularNormalCone_subset_normalCone C x (isCone_regularNormalCone hx).1⟩⟩

/-- The paragraph after 6.6: the relative outer limit of 6(7) may be taken
along the full neighborhood filter, at every point of `C`.  Closedness of `C`
is not needed here, only that the regular normal cone is empty off `C`. -/
theorem normalCone_eq_svOuterLimit_of_mem {C : Set E} {x : E} (hx : x ∈ C) :
    normalCone C x = svOuterLimit (regularNormalCone C) x := by
  rw [normalCone_eq_svOuterLimitWithin hx,
    svOuterLimitWithin_eq_svOuterLimit_of_eq_empty
      (fun _ hy ↦ regularNormalCone_eq_empty hy)]

/-- The paragraph after 6.6: for a closed set `C` the identity holds at every
point of the space, the two sides being empty off `C`. -/
theorem normalCone_eq_svOuterLimit {C : Set E} (hC : IsClosed C) (x : E) :
    normalCone C x = svOuterLimit (regularNormalCone C) x := by
  by_cases hx : x ∈ C
  · exact normalCone_eq_svOuterLimit_of_mem hx
  · have hempty : svOuterLimit (regularNormalCone C) x = ∅ := by
      refine eq_empty_of_forall_notMem fun v hv ↦ ?_
      obtain ⟨y, hy, u, huy, -⟩ :=
        Filter.frequently_iff.1 (hv univ univ_mem) (hC.isOpen_compl.mem_nhds hx)
      rw [regularNormalCone_eq_empty hy] at huy
      exact huy
    rw [normalCone_eq_empty hx, hempty]

/-- The paragraph after 6.6: for a closed set `C`, the graph of `N_C` is the
closure of the graph of `N̂_C`, so that `N_C` is the osc hull of `N̂_C` in the
sense of 5(2). -/
theorem svGraph_normalCone {C : Set E} (hC : IsClosed C) :
    svGraph (normalCone C) = closure (svGraph (regularNormalCone C)) := by
  refine Subset.antisymm ?_ ?_
  · rintro ⟨x, v⟩ ⟨-, xs, vs, -, hxto, hvs, hvto⟩
    exact mem_closure_of_tendsto (hxto.prodMk_nhds hvto)
      (Filter.Eventually.of_forall fun n ↦ hvs n)
  · rintro ⟨x, v⟩ hp
    have hxC : x ∈ C := by
      rw [← hC.closure_eq, mem_closure_iff_nhds]
      intro U hU
      have hUmem : U ×ˢ (univ : Set E) ∈ nhds ((x, v) : E × E) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod hU univ_mem
      obtain ⟨q, hqmem, hqgraph⟩ := mem_closure_iff_nhds.1 hp _ hUmem
      exact ⟨q.1, hqmem.1, hqgraph.1⟩
    have hmem : v ∈ svOuterLimitWithin (regularNormalCone C) C x := by
      intro V hV
      rw [Filter.frequently_iff]
      intro A hA
      obtain ⟨U, hUopen, hxU, hUA⟩ := mem_nhdsWithin.1 hA
      obtain ⟨W, hWV, hWopen, hvW⟩ := _root_.mem_nhds_iff.1 hV
      obtain ⟨q, hqmem, hqgraph⟩ :=
        mem_closure_iff_nhds.1 hp (U ×ˢ W) ((hUopen.prod hWopen).mem_nhds ⟨hxU, hvW⟩)
      exact ⟨q.1, hUA ⟨hqmem.1, hqgraph.1⟩, q.2, hqgraph, hWV hqmem.2⟩
    rw [← normalCone_eq_svOuterLimitWithin hxC] at hmem
    exact hmem

end NormalCones

end RW
