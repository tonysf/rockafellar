/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Uniformity in Graphical Convergence

Exercise 5.34.  Clause (a): graphical convergence is uniform approximation of
values on bounded regions, in the two directions the book displays.  Clause
(b): connected values that stay within reach of the origin cannot spread out,
so near a point they all fit in one bounded set.

The Guide says to derive this from 4.10, and that is exactly what happens:
the two displayed inclusions are 4.10's `EventuallyInnerApproximates` and
`EventuallyOuterApproximates` for the graphs, read through the sup norm on
`IRⁿ × IRᵐ`.  Under that norm a product ball is a pair of balls, so
`(x, u) ∈ gph S ∩ ρIB` says `u ∈ S(x) ∩ ρIB` with `|x| ≤ ρ`, and
`(x, u) ∈ gph T + εIB` says `u ∈ T(IB(x, ε)) + εIB`.  Nothing else is needed.

The printed hypothesis is that `S` be **closed-valued**.  That is not enough:
`closedValued_not_enough_in_534` exhibits a closed-valued `S` on `IR` for
which the constant sequence `Sν ≡ S` satisfies both inclusions for every `ε`
and `ρ`, yet does not converge graphically to `S`.  What 4.10 needs, and what
is assumed here, is that `gph S` be closed, i.e. that `S` be outer
semicontinuous.  The forward half needs no hypothesis at all, since a
graphical limit is automatically outer semicontinuous.

Clause (b) follows the Guide: the bivariate description 5(9) of the graphical
outer limit lets an escaping selection be turned into an ordinary sequence of
connected sets whose outer limit is bounded, and 4.12 confines those sets to a
single bounded set.  The book adds that the distance hypothesis "is certainly
satisfied when `S = g-limν Sν` and `S(x̄) ≠ ∅`"; that is false under the
convention `d(u, ∅) = ∞` which Chapter 5 uses throughout, and
`graphicalLimit_nonempty_not_enough_in_534b` gives the counterexample.
-/

import RockafellarWets.Chapter4.ConnectedLimits
import RockafellarWets.Chapter4.EscapeToHorizon
import RockafellarWets.Chapter4.UniformApproximation
import RockafellarWets.Chapter5.GraphicalLimitFormulas

open Filter Metric Set Topology

namespace RW

section Uniformity

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The book's displayed inclusion in 5.34(a): on the ball of radius `ρ` the
values of `S` are within `ε` of the values `T` takes near the same point.
Following Chapter 4, `+ εIB` is the open thickening; the `∀ ε > 0` in front
makes this equivalent to the closed one. -/
def SvUniformlyApproximates (S T : E → Set F) (ρ ε : ℝ) : Prop :=
  ∀ x ∈ closedBall (0 : E) ρ,
    S x ∩ closedBall (0 : F) ρ ⊆ thickening ε (svImage T (ball x ε))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The sup norm turns a thickening of a graph into a thickening of the
images of a ball. -/
theorem mem_thickening_svGraph_iff {T : E → Set F} {x : E} {u : F} {ε : ℝ} :
    (x, u) ∈ thickening ε (svGraph T) ↔ u ∈ thickening ε (svImage T (ball x ε)) := by
  simp only [mem_thickening_iff, mem_svImage, mem_ball, Prod.exists, mem_svGraph,
    Prod.dist_eq, max_lt_iff]
  constructor
  · rintro ⟨y, v, hv, hxy, huv⟩
    exact ⟨v, ⟨y, by rwa [dist_comm], hv⟩, huv⟩
  · rintro ⟨v, ⟨y, hxy, hv⟩, huv⟩
    exact ⟨y, v, hv, by rwa [dist_comm], huv⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The sup norm turns a ball of the product into a pair of balls. -/
theorem mem_svGraph_inter_closedBall_iff {S : E → Set F} {x : E} {u : F} {ρ : ℝ} :
    (x, u) ∈ svGraph S ∩ closedBall (0 : E × F) ρ ↔
      x ∈ closedBall (0 : E) ρ ∧ u ∈ S x ∩ closedBall (0 : F) ρ := by
  simp only [mem_inter_iff, mem_svGraph, mem_closedBall_zero_iff, Prod.norm_def,
    max_le_iff]
  tauto

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- 5.34(a), pointwise: the graph inclusion of 4.10 is the book's inclusion. -/
theorem svGraph_approximation_iff (S T : E → Set F) (ρ ε : ℝ) :
    svGraph S ∩ closedBall (0 : E × F) ρ ⊆ thickening ε (svGraph T) ↔
      SvUniformlyApproximates S T ρ ε := by
  constructor
  · intro h x hx u hu
    exact mem_thickening_svGraph_iff.1
      (h (mem_svGraph_inter_closedBall_iff.2 ⟨hx, hu⟩))
  · rintro h ⟨x, u⟩ hxu
    obtain ⟨hx, hu⟩ := mem_svGraph_inter_closedBall_iff.1 hxu
    exact mem_thickening_svGraph_iff.2 (h x hx hu)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The Chapter 4 uniform inner approximation of the graphs, transcribed. -/
theorem eventuallyInnerApproximates_svGraph_iff (Sseq : ℕ → E → Set F)
    (S : E → Set F) :
    EventuallyInnerApproximates (svGraph S) (fun n ↦ svGraph (Sseq n)) ↔
      ∀ ρ > 0, ∀ ε > 0, ∀ᶠ n in atTop, SvUniformlyApproximates S (Sseq n) ρ ε := by
  simp only [EventuallyInnerApproximates, svGraph_approximation_iff]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The Chapter 4 uniform outer approximation of the graphs, transcribed. -/
theorem eventuallyOuterApproximates_svGraph_iff (Sseq : ℕ → E → Set F)
    (S : E → Set F) :
    EventuallyOuterApproximates (fun n ↦ svGraph (Sseq n)) (svGraph S) ↔
      ∀ ρ > 0, ∀ ε > 0, ∀ᶠ n in atTop, SvUniformlyApproximates (Sseq n) S ρ ε := by
  simp only [EventuallyOuterApproximates, svGraph_approximation_iff]

/-- **Exercise 5.34(a)**, necessity.  This half needs no hypothesis: a
graphical limit is outer semicontinuous, so 4.10 applies to its graph. -/
theorem GraphicalConverges.uniformlyApproximates {Sseq : ℕ → E → Set F}
    {S : E → Set F} (h : GraphicalConverges Sseq S) :
    ∀ ρ > 0, ∀ ε > 0, ∀ᶠ n in atTop,
      SvUniformlyApproximates S (Sseq n) ρ ε ∧
        SvUniformlyApproximates (Sseq n) S ρ ε := by
  obtain ⟨hin, hout⟩ :=
    (pkConverges_iff_eventuallyInnerApproximates_and_eventuallyOuterApproximates
      (isClosed_svGraph_iff_svOsc.2 h.svOsc)).1 h
  intro ρ hρ ε hε
  exact ((eventuallyInnerApproximates_svGraph_iff Sseq S).1 hin ρ hρ ε hε).and
    ((eventuallyOuterApproximates_svGraph_iff Sseq S).1 hout ρ hρ ε hε)

/-- **Exercise 5.34(a)**, sufficiency.  Here the graph of `S` must be closed;
closed-valuedness alone does not suffice, as `closedValued_not_enough_in_534`
shows. -/
theorem graphicalConverges_of_uniformlyApproximates {Sseq : ℕ → E → Set F}
    {S : E → Set F} (hS : SvOsc S)
    (h : ∀ ρ > 0, ∀ ε > 0, ∀ᶠ n in atTop,
      SvUniformlyApproximates S (Sseq n) ρ ε ∧
        SvUniformlyApproximates (Sseq n) S ρ ε) :
    GraphicalConverges Sseq S :=
  (pkConverges_iff_eventuallyInnerApproximates_and_eventuallyOuterApproximates
      (isClosed_svGraph_iff_svOsc.2 hS)).2
    ⟨(eventuallyInnerApproximates_svGraph_iff Sseq S).2
        fun ρ hρ ε hε ↦ (h ρ hρ ε hε).mono fun _ hn ↦ hn.1,
      (eventuallyOuterApproximates_svGraph_iff Sseq S).2
        fun ρ hρ ε hε ↦ (h ρ hρ ε hε).mono fun _ hn ↦ hn.2⟩

/-- **Exercise 5.34(a)**, for an outer semicontinuous `S`. -/
theorem graphicalConverges_iff_uniformlyApproximates {Sseq : ℕ → E → Set F}
    {S : E → Set F} (hS : SvOsc S) :
    GraphicalConverges Sseq S ↔
      ∀ ρ > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        SvUniformlyApproximates S (Sseq n) ρ ε ∧
          SvUniformlyApproximates (Sseq n) S ρ ε :=
  ⟨GraphicalConverges.uniformlyApproximates,
    graphicalConverges_of_uniformlyApproximates hS⟩

end Uniformity

section ClosedValuedCounterexample

/-- A closed-valued mapping on `IR` whose graph is not closed: the constant
value `{0}` on the open half-line. -/
noncomputable def openHalfLineMapping : ℝ → Set ℝ :=
  fun x ↦ if 0 < x then {(0 : ℝ)} else ∅

theorem isClosed_openHalfLineMapping (x : ℝ) : IsClosed (openHalfLineMapping x) := by
  unfold openHalfLineMapping
  split
  · exact isClosed_singleton
  · exact isClosed_empty

/-- The uniform inclusions of 5.34(a) hold trivially for a constant sequence:
the point `x` is itself in `IB(x, ε)`. -/
theorem svUniformlyApproximates_self {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (S : E → Set F) {ρ ε : ℝ}
    (hε : 0 < ε) : SvUniformlyApproximates S S ρ ε := by
  intro x _ u hu
  exact self_subset_thickening hε _
    (subset_svImage (mem_ball_self hε) hu.1)

/-- `(0, 0)` is in the closure of the graph but not in the graph. -/
theorem notMem_svGraph_openHalfLineMapping :
    ((0 : ℝ), (0 : ℝ)) ∉ svGraph openHalfLineMapping := by
  simp [svGraph, openHalfLineMapping]

theorem mem_closure_svGraph_openHalfLineMapping :
    ((0 : ℝ), (0 : ℝ)) ∈ closure (svGraph openHalfLineMapping) := by
  have h1 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (nhds (0 : ℝ)) := by
    simpa only [one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds (0 : ℝ)) := tendsto_const_nhds
  have hmem : ∀ᶠ n : ℕ in atTop,
      (((n : ℝ) + 1)⁻¹, (0 : ℝ)) ∈ svGraph openHalfLineMapping := by
    filter_upwards with n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    simp [svGraph, openHalfLineMapping, hpos]
  exact mem_closure_of_tendsto (h1.prodMk_nhds h2) hmem

/-- **Closed-valuedness is not enough in 5.34(a).**  The constant sequence at
`openHalfLineMapping` satisfies both displayed inclusions for every `ε > 0`
and `ρ`, and the mapping is closed-valued, yet the sequence does not converge
graphically to it: the graph is not closed, and graphical limits always are.
The hypothesis 4.10 actually requires is closedness of `gph S`. -/
theorem closedValued_not_enough_in_534 :
    (∀ x, IsClosed (openHalfLineMapping x)) ∧
      (∀ ρ > 0, ∀ ε > 0, ∀ᶠ _n : ℕ in atTop,
        SvUniformlyApproximates openHalfLineMapping openHalfLineMapping ρ ε ∧
          SvUniformlyApproximates openHalfLineMapping openHalfLineMapping ρ ε) ∧
      ¬ GraphicalConverges (fun _ : ℕ ↦ openHalfLineMapping) openHalfLineMapping := by
  refine ⟨isClosed_openHalfLineMapping, fun ρ _ ε hε ↦ Eventually.of_forall fun _ ↦
    ⟨svUniformlyApproximates_self _ hε, svUniformlyApproximates_self _ hε⟩, ?_⟩
  intro hcon
  have hclosed : IsClosed (svGraph openHalfLineMapping) :=
    isClosed_svGraph_iff_svOsc.2 hcon.svOsc
  exact notMem_svGraph_openHalfLineMapping
    (hclosed.closure_eq ▸ mem_closure_svGraph_openHalfLineMapping)

end ClosedValuedCounterexample

section ConnectedValued

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {x : E}

/-- The book's hypothesis `lim sup_{x→x̄, ν→∞} d(0, Sν(x)) < ∞` in the form it
is used: some fixed ball is met by all the nearby values. -/
def SvEventuallyMeetsBall (Sseq : ℕ → E → Set F) (x : E) : Prop :=
  ∃ M > 0, ∀ᶠ p : ℕ × E in atTop ×ˢ nhds x,
    (Sseq p.1 p.2 ∩ closedBall (0 : F) M).Nonempty

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The condition is what `lim sup d(0, Sν(x)) < ∞` says: a finite `limsup`
of distances to the origin is a uniform bound on those distances. -/
theorem svEventuallyMeetsBall_of_infEDist {M : ℝ} (hM : 0 < M)
    (h : ∀ᶠ p : ℕ × E in atTop ×ˢ nhds x,
      Metric.infEDist (0 : F) (Sseq p.1 p.2) < ENNReal.ofReal M) :
    SvEventuallyMeetsBall Sseq x := by
  refine ⟨M, hM, h.mono fun p hp ↦ ?_⟩
  obtain ⟨v, hvS, hv⟩ := Metric.infEDist_lt_iff.1 hp
  refine ⟨v, hvS, ?_⟩
  rw [mem_closedBall_zero_iff]
  have := (edist_dist (0 : F) v) ▸ hv
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg] at this
  simpa [dist_zero_left] using this.le

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The core of **Exercise 5.34(b)**: the values near `x̄` and far along the
sequence all lie in one ball.

The argument is by contradiction along the lines of 4.12.  If no ball works,
one can pick `nk ≥ k` and `xk → x̄` with a value of `S^{nk}(xk)` of norm
above `k`.  Those value sets are connected, they all meet a fixed ball by the
distance hypothesis, and their outer limit lies inside `g-limsup Sν(x̄)` by
5(9), which is bounded -- so 4.12 confines them to a single bounded set,
contradicting the divergence of the chosen values. -/
theorem exists_closedBall_of_connected_of_isBounded
    (hconn : ∀ n y, IsPreconnected (Sseq n y))
    (hbdd : Bornology.IsBounded (graphicalOuterLimit Sseq x))
    (hmeets : SvEventuallyMeetsBall Sseq x) :
    ∃ ρ : ℝ, ∃ V ∈ nhds x, ∃ N : ℕ,
      ∀ n ≥ N, ∀ y ∈ V, Sseq n y ⊆ closedBall (0 : F) ρ := by
  obtain ⟨M, hM, hmeetsM⟩ := hmeets
  by_contra hcon
  push_neg at hcon
  -- Extract the escaping data.
  have hpick : ∀ k : ℕ, ∃ (n : ℕ) (y : E) (v : F),
      k ≤ n ∧ y ∈ ball x ((k : ℝ) + 1)⁻¹ ∧ v ∈ Sseq n y ∧ (k : ℝ) < ‖v‖ := by
    intro k
    obtain ⟨n, hn, y, hy, hsub⟩ :=
      hcon k (ball x ((k : ℝ) + 1)⁻¹) (ball_mem_nhds x (by positivity)) k
    obtain ⟨v, hvS, hv⟩ := not_subset.1 hsub
    exact ⟨n, y, v, hn, hy, hvS, by simpa [mem_closedBall_zero_iff] using hv⟩
  choose ns ys vs hns hys hvsS hvsNorm using hpick
  -- The chosen arguments run along the product filter.
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hysTo : Tendsto ys atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ (mem_ball.1 (hys k)).le) ?_
    simpa only [one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hprod : Tendsto (fun k ↦ (ns k, ys k)) atTop (atTop ×ˢ nhds x) :=
    hnsTop.prodMk hysTo
  set C : ℕ → Set F := fun k ↦ Sseq (ns k) (ys k) with hC
  -- The three hypotheses of 4.12.
  have hCconn : ∀ k, IsConnected (C k) := fun k ↦ ⟨⟨vs k, hvsS k⟩, hconn _ _⟩
  have hCouter : Bornology.IsBounded (outerSetLimit C) := by
    refine hbdd.subset ?_
    rw [graphicalOuterLimit_eq_outerSetLimitAlong]
    exact outerSetLimit_comp_subset (C := fun p : ℕ × E ↦ Sseq p.1 p.2) hprod
  have hCmeets : ∀ᶠ k in atTop, (C k ∩ closedBall (0 : F) M).Nonempty :=
    hprod.eventually hmeetsM
  have hCescape : NoSubsequenceEscapesToHorizon C := by
    intro φ hφ
    rw [nonempty_iff_ne_empty]
    intro hempty
    have hmiss := (outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero
      (C ∘ φ)).1 hempty M hM
    obtain ⟨k, hdisj, hhit⟩ :=
      (hmiss.and (hφ.tendsto_atTop.eventually hCmeets)).exists
    exact (Set.not_disjoint_iff_nonempty_inter.2 hhit) hdisj
  obtain ⟨B, hB, hBsub⟩ :=
    eventually_bounded_of_connected_of_bounded_outerSetLimit hCconn hCouter hCescape
  obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : F)
  obtain ⟨k, hk, hkR⟩ := (hBsub.and (eventually_ge_atTop ⌈R⌉₊)).exists
  have hnorm : ‖vs k‖ ≤ R := by
    simpa [mem_closedBall_zero_iff] using hR (hk (hvsS k))
  have hkle : R ≤ (k : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hkR)
  exact absurd (hvsNorm k) (not_lt.2 (hnorm.trans hkle))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exercise 5.34(b)**.  A common bounded set holds all the nearby values,
those of the graphical outer limit included. -/
theorem exists_bounded_of_connected_of_isBounded
    (hconn : ∀ n y, IsPreconnected (Sseq n y))
    (hbdd : Bornology.IsBounded (graphicalOuterLimit Sseq x))
    (hmeets : SvEventuallyMeetsBall Sseq x) :
    ∃ (B : Set F) (V : Set E) (N : ℕ), Bornology.IsBounded B ∧ V ∈ nhds x ∧
      (∀ y ∈ V, graphicalOuterLimit Sseq y ⊆ B) ∧
        (∀ n ≥ N, ∀ y ∈ V, Sseq n y ⊆ B) := by
  obtain ⟨ρ, V, hV, N, hsub⟩ :=
    exists_closedBall_of_connected_of_isBounded hconn hbdd hmeets
  refine ⟨closedBall (0 : F) ρ, interior V, N, isBounded_closedBall,
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hV), fun y hy u hu ↦ ?_,
    fun n hn y hy ↦ hsub n hn y (interior_subset hy)⟩
  -- Values of the graphical outer limit are limits of nearby values.
  rw [mem_closedBall_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [graphicalOuterLimit_eq_outerSetLimitAlong] at hu
  obtain ⟨p, hp, w, hwS, hw⟩ :=
    Filter.frequently_iff.1 (hu (ball u ε) (ball_mem_nhds u hε))
      (Filter.prod_mem_prod (mem_atTop N) (isOpen_interior.mem_nhds hy))
  have hwρ : ‖w‖ ≤ ρ := by
    simpa [mem_closedBall_zero_iff] using hsub p.1 hp.1 p.2 (interior_subset hp.2) hwS
  have htri : ‖u‖ ≤ ‖u - w‖ + ‖w‖ := by simpa using norm_add_le (u - w) w
  have hdist : ‖u - w‖ < ε := by
    simpa [dist_eq_norm, norm_sub_rev] using mem_ball.1 hw
  linarith

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exercise 5.34(b)**, for a genuine graphical limit. -/
theorem GraphicalConverges.exists_bounded_of_connected {S : E → Set F}
    (hlim : GraphicalConverges Sseq S) (hconn : ∀ n y, IsPreconnected (Sseq n y))
    (hbdd : Bornology.IsBounded (S x)) (hmeets : SvEventuallyMeetsBall Sseq x) :
    ∃ (B : Set F) (V : Set E) (N : ℕ), Bornology.IsBounded B ∧ V ∈ nhds x ∧
      (∀ y ∈ V, graphicalOuterLimit Sseq y ⊆ B) ∧
        (∀ n ≥ N, ∀ y ∈ V, Sseq n y ⊆ B) := by
  refine exists_bounded_of_connected_of_isBounded hconn (hbdd.subset ?_) hmeets
  exact (graphicalConverges_iff.1 hlim).1 x

end ConnectedValued

section MeetsBallCounterexample

/-- The closed half-line version of `openHalfLineMapping`: this one *does*
have a closed graph, so the constant sequence converges graphically to it. -/
noncomputable def closedHalfLineMapping : ℝ → Set ℝ :=
  fun x ↦ if 0 ≤ x then {(0 : ℝ)} else ∅

theorem svGraph_closedHalfLineMapping :
    svGraph closedHalfLineMapping = Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
  ext ⟨x, u⟩
  by_cases hx : 0 ≤ x <;> simp [svGraph, closedHalfLineMapping, hx, mem_prod]

theorem graphicalConverges_closedHalfLineMapping :
    GraphicalConverges (fun _ : ℕ ↦ closedHalfLineMapping) closedHalfLineMapping := by
  have hclosed : IsClosed (svGraph closedHalfLineMapping) := by
    rw [svGraph_closedHalfLineMapping]
    exact isClosed_Ici.prod isClosed_singleton
  exact pkConverges_const_of_isClosed hclosed

/-- **The parenthetical sufficient condition in 5.34(b) fails.**  The book
says the distance hypothesis "is certainly satisfied when `S = g-limν Sν` and
`S(x̄) ≠ ∅`".  It is not: with the convention `d(u, ∅) = ∞` that Chapter 5
uses throughout (see 5.11), a single empty value arbitrarily close to `x̄`
already makes `lim sup_{x→x̄, ν→∞} d(0, Sν(x)) = ∞`.  Here `S` is its own
graphical limit and `S(0) = {0}` is nonempty and bounded, yet every
neighborhood of `0` contains negative points where `S` is empty. -/
theorem graphicalLimit_nonempty_not_enough_in_534b :
    GraphicalConverges (fun _ : ℕ ↦ closedHalfLineMapping) closedHalfLineMapping ∧
      (closedHalfLineMapping 0).Nonempty ∧
      ¬ SvEventuallyMeetsBall (fun _ : ℕ ↦ closedHalfLineMapping) 0 := by
  refine ⟨graphicalConverges_closedHalfLineMapping, ⟨0, by simp [closedHalfLineMapping]⟩, ?_⟩
  rintro ⟨M, -, hev⟩
  obtain ⟨A, hA, V, hV, hsub⟩ := Filter.mem_prod_iff.1 hev
  obtain ⟨n, hn⟩ := (Filter.nonempty_of_mem hA)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hneg : -(δ / 2) ∈ V := by
    refine hball ?_
    simp only [mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have := hsub (show (⟨n, -(δ / 2)⟩ : ℕ × ℝ) ∈ A ×ˢ V from ⟨hn, hneg⟩)
  simp only [mem_setOf_eq, closedHalfLineMapping,
    if_neg (by linarith : ¬ (0 : ℝ) ≤ -(δ / 2))] at this
  simp at this

end MeetsBallCounterexample

end RW
