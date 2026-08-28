/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Generic Continuity

Theorem 5.55 says that a semicontinuous mapping is "mostly" continuous: if
`S` is osc relative to `X`, or isc relative to `X`, then the points of `X`
where `S` fails to be continuous relative to `X` form a meager subset of `X`.

The book's *nowhere dense in `X`* and *meager in `X`* are defined through the
relative operators `intₓ` and `clₓ`.  Here everything is instead stated in
the subspace `↥X`, where `intₓ` and `clₓ` are the ordinary interior and
closure, so that Mathlib's `IsNowhereDense` and `IsMeagre` apply directly.
The translation is `preimage_val_mem_nhds_iff` and `mem_closure_preimage_val`
in `SemicontinuityCriteria.lean`; the two 5.7 preimage criteria are already
stated in the same subtype form.

The book's countable family is that of the closed balls with rational centre
and rational radius, of which the interiors are used in one half of the
argument and the balls themselves in the other.  Here the two halves use the
open ball and the closed ball of the *same* centre and radius, which is the
same family and avoids needing `int IB(u, ρ) = B(u, ρ)`; a single selection
lemma `exists_ball_closedBall_subset` then serves both.
-/

import RockafellarWets.Chapter5.ProfileMappings
import Mathlib.Topology.GDelta.Basic

open Filter Set Topology Metric

open scoped Set.Notation

namespace RW

section NowhereDense

variable {E : Type*} [TopologicalSpace E]

/-- A closed set less its interior is nowhere dense: it is the frontier of a
closed set.  This is the first of the two elementary examples the book lists
when introducing the terminology of Section J. -/
theorem isNowhereDense_sdiff_interior {C : Set E} (hC : IsClosed C) :
    IsNowhereDense (C \ interior C) := by
  rw [← hC.frontier_eq]
  exact isClosed_frontier.isNowhereDense_iff.2 (interior_frontier hC)

/-- The closure of an open set less the set itself is nowhere dense: it is the
frontier of an open set.  This is the second of the book's two examples. -/
theorem isNowhereDense_closure_sdiff {U : Set E} (hU : IsOpen U) :
    IsNowhereDense (closure U \ U) := by
  rw [← hU.frontier_eq]
  refine isClosed_frontier.isNowhereDense_iff.2 ?_
  rw [← frontier_compl]
  exact interior_frontier (isClosed_compl_iff.2 hU)

end NowhereDense

section Balls

variable {F : Type*} [PseudoMetricSpace F]

/-- The selection lemma behind the book's countable family of rational closed
balls: from a dense set `D` the balls centred in `D` with radius `1/(n+1)`
generate the neighborhoods, in the strong sense that the *closed* ball is
still inside the given neighborhood while the *open* ball already contains
the point.

Since `D` may be taken countable in a separable space, the balls are indexed
by the countable set `D × ℕ`. -/
theorem exists_ball_closedBall_subset {D : Set F} (hD : Dense D) {u : F}
    {W : Set F} (hW : W ∈ nhds u) :
    ∃ d ∈ D, ∃ n : ℕ, u ∈ ball d ((n : ℝ) + 1)⁻¹ ∧
      closedBall d ((n : ℝ) + 1)⁻¹ ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hr : ((n : ℝ) + 1)⁻¹ < ε / 2 := by
    rw [inv_lt_comm₀ hnpos (by linarith)]
    calc (ε / 2)⁻¹ = 2 / ε := by rw [inv_div]
    _ < (n : ℝ) + 1 := by linarith
  obtain ⟨d, hdD, hdu⟩ :=
    hD.exists_dist_lt u (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)
  refine ⟨d, hdD, n, by simpa [Metric.mem_ball, dist_comm] using hdu,
    fun y hy ↦ hball ?_⟩
  have htri : dist y u ≤ dist y d + dist d u := dist_triangle _ _ _
  have hyd : dist y d ≤ ((n : ℝ) + 1)⁻¹ := hy
  have hdu' : dist d u < ((n : ℝ) + 1)⁻¹ := by simpa [dist_comm] using hdu
  exact Metric.mem_ball.2 (by linarith)

end Balls

section GenericContinuity

variable {E : Type*} [TopologicalSpace E]
variable {F : Type*} [PseudoMetricSpace F] [ProperSpace F]

/-- **Theorem 5.55**, the outer semicontinuous case.  If `S` is osc relative
to `X`, then the points of `X` at which `S` fails to be *inner*
semicontinuous relative to `X` are meager in `X`.

The point `x̄` fails to be isc when some `ū ∈ S(x̄)` has a neighborhood `W`
that the nearby images repeatedly miss.  Choosing a ball `IB(d, r)` with
`ū ∈ B(d, r)` and `IB(d, r) ⊂ W` puts `x̄` in `Y := S⁻¹(IB(d, r)) ∩ X` but
outside `intₓ Y`, since a relative neighborhood inside `Y` would be a
relative neighborhood inside `S⁻¹(W)`.  Each `Y` is closed relative to `X` by
the forward half of 5.7(b), the ball being compact, so each `Y \ intₓ Y` is
nowhere dense.

Closed-valuedness is not assumed: outer semicontinuity relative to `X`
already makes `S(x̄)` closed at every `x̄ ∈ X`, and in any case this half of
the theorem never needs it. -/
theorem isMeagre_not_svIscWithinAt_of_svOscOn {S : E → Set F} {X : Set E}
    (h : SvOscOn S X) :
    IsMeagre {x : X | ¬ SvIscWithinAt S X (x : E)} := by
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense F
  have : Countable D := hDcount.to_subtype
  set Y : D × ℕ → Set X := fun p ↦
    X ↓∩ svPreimage S (closedBall (p.1 : F) ((p.2 : ℝ) + 1)⁻¹)
  have hYclosed : ∀ p, IsClosed (Y p) := fun p ↦
    h.isClosed_svPreimage (isCompact_closedBall _ _)
  refine IsMeagre.mono ?_ (isMeagre_iUnion (f := fun p ↦ Y p \ interior (Y p))
    fun p ↦ (isNowhereDense_sdiff_interior (hYclosed p)).isMeagre)
  rintro ⟨x, hx⟩ hxbad
  simp only [mem_setOf_eq] at hxbad
  -- Unpack the failure of inner semicontinuity at `x`.
  obtain ⟨u, huS, hunot⟩ := not_subset.1 hxbad
  simp only [svInnerLimitWithin, mem_innerSetLimitAlong, not_forall] at hunot
  obtain ⟨W, hWnhds, hWfail⟩ := hunot
  obtain ⟨d, hdD, n, hud, hball⟩ := exists_ball_closedBall_subset hDdense hWnhds
  refine mem_iUnion.2 ⟨(⟨d, hdD⟩, n), ⟨u, huS, ball_subset_closedBall hud⟩, ?_⟩
  -- If `x` were relatively interior to `Y`, the images would eventually meet `W`.
  intro hint
  refine hWfail ?_
  have hmem := (preimage_val_mem_nhds_iff hx).1 (mem_interior_iff_mem_nhds.1 hint)
  filter_upwards [hmem] with y hy
  exact hy.imp fun v hv ↦ ⟨hv.1, hball hv.2⟩

/-- **Theorem 5.55**, the inner semicontinuous case.  If `S` is closed-valued
on `X` and isc relative to `X`, then the points of `X` at which `S` fails to
be *outer* semicontinuous relative to `X` are meager in `X`.

The point `x̄` fails to be osc when some `ū ∉ S(x̄)` is repeatedly met by the
nearby images.  Closed-valuedness supplies a ball around `ū` missing `S(x̄)`;
choosing `IB(d, r)` inside it with `ū ∈ B(d, r)` puts `x̄` in
`clₓ Y \ Y` for `Y := S⁻¹(B(d, r)) ∩ X`, which is open relative to `X` by
5.7(c). -/
theorem isMeagre_not_svOscWithinAt_of_svIscOn {S : E → Set F} {X : Set E}
    (hval : ∀ x ∈ X, IsClosed (S x)) (h : SvIscOn S X) :
    IsMeagre {x : X | ¬ SvOscWithinAt S X (x : E)} := by
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense F
  have : Countable D := hDcount.to_subtype
  set Y : D × ℕ → Set X := fun p ↦
    X ↓∩ svPreimage S (ball (p.1 : F) ((p.2 : ℝ) + 1)⁻¹)
  have hYopen : ∀ p, IsOpen (Y p) := fun p ↦ h.isOpen_svPreimage isOpen_ball
  refine IsMeagre.mono ?_ (isMeagre_iUnion (f := fun p ↦ closure (Y p) \ Y p)
    fun p ↦ (isNowhereDense_closure_sdiff (hYopen p)).isMeagre)
  rintro ⟨x, hx⟩ hxbad
  simp only [mem_setOf_eq] at hxbad
  -- Unpack the failure of outer semicontinuity at `x`.
  obtain ⟨u, hulim, hunot⟩ := not_subset.1 hxbad
  rw [svOuterLimitWithin, mem_outerSetLimitAlong] at hulim
  obtain ⟨d, hdD, n, hud, hball⟩ :=
    exists_ball_closedBall_subset hDdense ((hval x hx).isOpen_compl.mem_nhds hunot)
  refine mem_iUnion.2 ⟨(⟨d, hdD⟩, n), ?_, ?_⟩
  · -- `x` is in the relative closure: the nearby images meet `B(d, r)` often.
    rw [mem_closure_preimage_val hx, mem_closure_iff_nhds]
    intro V hV
    obtain ⟨y, hyhit, hyX, hyV⟩ :=
      ((hulim _ (isOpen_ball.mem_nhds hud)).and_eventually
        ((Filter.eventually_mem_set.2 self_mem_nhdsWithin).and
          (Filter.eventually_mem_set.2 (nhdsWithin_le_nhds hV)))).exists
    exact ⟨y, hyV, hyX, hyhit⟩
  · -- but `S(x)` misses the whole ball, so `x` is not in the set itself.
    rintro ⟨v, hvS, hvB⟩
    exact hball (ball_subset_closedBall hvB) hvS

/-- **Theorem 5.55** as printed, outer semicontinuous case: the points of `X`
where a mapping osc relative to `X` fails to be *continuous* relative to `X`
are meager in `X`. -/
theorem isMeagre_not_svContinuousWithinAt_of_svOscOn {S : E → Set F}
    {X : Set E} (h : SvOscOn S X) :
    IsMeagre {x : X | ¬ SvContinuousWithinAt S X (x : E)} :=
  IsMeagre.mono (fun x hx hisc ↦ hx ⟨h x x.2, hisc⟩)
    (isMeagre_not_svIscWithinAt_of_svOscOn h)

/-- **Theorem 5.55** as printed, inner semicontinuous case. -/
theorem isMeagre_not_svContinuousWithinAt_of_svIscOn {S : E → Set F}
    {X : Set E} (hval : ∀ x ∈ X, IsClosed (S x)) (h : SvIscOn S X) :
    IsMeagre {x : X | ¬ SvContinuousWithinAt S X (x : E)} :=
  IsMeagre.mono (fun x hx hosc ↦ hx ⟨hosc, h x x.2⟩)
    (isMeagre_not_svOscWithinAt_of_svIscOn hval h)

end GenericContinuity

section ExtendedRealValued

variable {E : Type*} [TopologicalSpace E]

/-- **Corollary 5.56**, the lower semicontinuous case: if `f` is lsc relative
to `X`, the points of `X` where `f` fails to be continuous relative to `X`
are meager in `X`.

This is 5.55 applied to the epigraphical profile mapping `Ef` of 5.5, which
is osc relative to `X` exactly when `f` is lsc relative to `X`, and
continuous at a point relative to `X` exactly when `f` is. -/
theorem isMeagre_not_continuousWithinAt_of_lowerSemicontinuousOn
    {f : E → EReal} {X : Set E} (h : LowerSemicontinuousOn f X) :
    IsMeagre {x : X | ¬ ContinuousWithinAt f X (x : E)} := by
  have hset : {x : X | ¬ ContinuousWithinAt f X (x : E)}
      = {x : X | ¬ SvContinuousWithinAt (epiProfile f) X (x : E)} := by
    ext x
    simp only [mem_setOf_eq, svContinuousWithinAt_epiProfile_iff]
  rw [hset]
  exact isMeagre_not_svContinuousWithinAt_of_svOscOn
    ((svOscOn_epiProfile_iff f X).2 h)

/-- **Corollary 5.56**, the upper semicontinuous case.  Here `Ef` is isc
relative to `X`, and its values `Ef(x) = [f(x), ∞) ∩ IR` are closed, which is
the closed-valuedness that half of 5.55 requires. -/
theorem isMeagre_not_continuousWithinAt_of_upperSemicontinuousOn
    {f : E → EReal} {X : Set E} (h : UpperSemicontinuousOn f X) :
    IsMeagre {x : X | ¬ ContinuousWithinAt f X (x : E)} := by
  have hset : {x : X | ¬ ContinuousWithinAt f X (x : E)}
      = {x : X | ¬ SvContinuousWithinAt (epiProfile f) X (x : E)} := by
    ext x
    simp only [mem_setOf_eq, svContinuousWithinAt_epiProfile_iff]
  rw [hset]
  exact isMeagre_not_svContinuousWithinAt_of_svIscOn
    (fun x _ ↦ isClosed_epiProfile f x) ((svIscOn_epiProfile_iff f X).2 h)

end ExtendedRealValued

end RW
