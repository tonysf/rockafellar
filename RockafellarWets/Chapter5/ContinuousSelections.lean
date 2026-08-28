/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Continuous Selections

A *selection* of `S` is a single-valued `s` with `s(x) ∈ S(x)` on `dom S`.
This file covers the two results of Section J that precede Michael's theorem.

The unnumbered remark before 5.57 says that inner semicontinuity at a single
point already gives, for each `ū ∈ S(x̄)`, a selection continuous *at that one
point* with `s(x̄) = ū`.  The selection is built by choosing `s(x) ∈ S(x)`
within `d(ū, S(x)) + |x - x̄|` of `ū`, and the book's route through 5.11(b) is
the one taken here: inner semicontinuity is upper semicontinuity of
`x ↦ d(ū, S(x))`, whose value at `x̄` is `0`.

Example 5.57 is the much stronger statement available when `S` is continuous
and convex-valued: every `u` gives a selection `sᵤ(x) = P_{S(x)}(u)`
continuous on the whole of `dom S`.  Rather than a proof-carrying `nearestPoint`,
the results below are stated for an *arbitrary* function whose values are
projections, with existence proved separately; this keeps the hypotheses of
`S` out of the term `sᵤ` and lets the closure formula be stated with the
set-valued `projMapping` of 5.23.

Single-valuedness of `P_{S(x)}` needs uniqueness of the nearest point on a
convex set, which in a general normed space is `[StrictConvexSpace ℝ F]` --
the project's standing generalization boundary, already carried at 5.23 and
5.35.  The continuity argument itself does not use it: it is 5.19 relative to
`X` applied to the mapping `x ↦ P_{S(x)}(u)`, which is outer semicontinuous
and locally bounded relative to `X` by 5.11(c) alone.  Strict convexity enters
only to know that `P_{S(x̄)}(u)` is the single point `s(x̄)`, so that the ball
around it contains the whole image.
-/

import RockafellarWets.Chapter5.ProjectionGraphicalConvergence
import RockafellarWets.Chapter5.LocallyBoundedContinuity
import RockafellarWets.Chapter5.DistanceCriteria

open Bornology Filter Metric Set Topology

namespace RW

section PointwiseSelection

variable {E : Type*} [MetricSpace E]
variable {F : Type*} [PseudoMetricSpace F]

/-- The unnumbered remark preceding **Example 5.57**: if `S` is isc at `x̄`
relative to `X`, then each `ū ∈ S(x̄)` is the value at `x̄` of a selection that
is continuous at `x̄` relative to `X`.

The selection takes `s(x)` to be any point of `S(x)` within
`d(ū, S(x)) + |x - x̄|` of `ū`, which exists because `S(x)` is nonempty and the
allowance `|x - x̄|` is positive away from `x̄`; at `x̄` itself the allowance is
`0` and the only admissible choice is `ū`.  Continuity is then the book's
observation through 5.11(b) that `d(ū, S(x)) → d(ū, S(x̄)) = 0`.

Nothing here makes the selection continuous at any *other* point of `X`; the
book notes that even inner semicontinuity throughout a neighborhood of `x̄`
does not give that. -/
theorem exists_continuousWithinAt_selection_of_svIscWithinAt {S : E → Set F}
    {X : Set E} {x : E} (hx : x ∈ X) (hne : ∀ z ∈ X, (S z).Nonempty)
    (hisc : SvIscWithinAt S X x) {u : F} (hu : u ∈ S x) :
    ∃ s : E → F, (∀ z ∈ X, s z ∈ S z) ∧ s x = u ∧ ContinuousWithinAt s X x := by
  classical
  have key : ∀ z : E, ∃ v : F, (z ∈ X → v ∈ S z) ∧
      (z ∈ X → dist u v ≤ Metric.infDist u (S z) + dist z x) ∧ (z = x → v = u) := by
    intro z
    by_cases hzx : z = x
    · subst hzx
      exact ⟨u, fun _ ↦ hu, fun _ ↦ by
        simp [Metric.infDist_zero_of_mem hu], fun _ ↦ rfl⟩
    by_cases hzX : z ∈ X
    · have hd : 0 < dist z x := dist_pos.2 hzx
      obtain ⟨v, hvS, hvlt⟩ := (Metric.infDist_lt_iff (hne z hzX)).1
        (by linarith : Metric.infDist u (S z) < Metric.infDist u (S z) + dist z x)
      exact ⟨v, fun _ ↦ hvS, fun _ ↦ hvlt.le, fun h ↦ absurd h hzx⟩
    · exact ⟨u, fun h ↦ absurd h hzX, fun h ↦ absurd h hzX, fun h ↦ absurd h hzx⟩
  choose s hsS hsdist hsx using key
  refine ⟨s, hsS, hsx x rfl, ?_⟩
  -- The distance functions tend to `d(ū, S(x̄)) = 0` by 5.11(b).
  have husc := svIscWithinAt_iff_upperSemicontinuousWithinAt.1 hisc u
  rw [ContinuousWithinAt, hsx x rfl, Metric.tendsto_nhds]
  intro ε hε
  have hlt : Metric.infEDist u (S x) < ENNReal.ofReal (ε / 2) := by
    rw [Metric.infEDist_zero_of_mem hu]
    exact ENNReal.ofReal_pos.2 (by linarith)
  have hev := husc (ENNReal.ofReal (ε / 2)) hlt
  have hdist : ∀ᶠ z in nhdsWithin x X, dist z x < ε / 2 :=
    (Filter.eventually_mem_set.2
      (nhdsWithin_le_nhds (ball_mem_nhds x (by linarith : (0 : ℝ) < ε / 2)))).mono
      fun z hz ↦ mem_ball.1 hz
  filter_upwards [hev, hdist, self_mem_nhdsWithin] with z hz1 hz2 hzX
  have hinf : Metric.infDist u (S z) < ε / 2 := by
    rw [Metric.infDist]
    exact (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hz1)).1 hz1
  have := hsdist z hzX
  rw [dist_comm]
  linarith

end PointwiseSelection

section ProjectionSelections

variable {F : Type*} [NormedAddCommGroup F]

/-- The projections of `u` on `C` lie in `C`. -/
theorem projMapping_subset (C : Set F) (u : F) : projMapping C u ⊆ C :=
  fun _ hw ↦ hw.1

/-- The book's remark after 5.57 with `U = IRᵐ`: no closure is needed, since
`u` is its own projection whenever `u ∈ C`. -/
theorem iUnion_projMapping (C : Set F) : (⋃ u, projMapping C u) = C := by
  refine Subset.antisymm (iUnion_subset fun u ↦ projMapping_subset C u) fun w hw ↦ ?_
  exact mem_iUnion.2 ⟨w, mem_projMapping_self hw⟩

variable [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Example 5.57**, the closure formula, at a single set.  If `cl U ⊃ C`
then the projections of the points of `U` are dense in `C`: a point `w ∈ C`
is approximated by some `u ∈ U`, and the projection of that `u` is at least
as close to `u` as `w` is.

Neither convexity nor strict convexity is involved; the projections need not
be single points for this. -/
theorem closure_iUnion_projMapping {C : Set F} (hC : IsClosed C) {U : Set F}
    (hU : C ⊆ closure U) :
    closure (⋃ u ∈ U, projMapping C u) = C := by
  refine Subset.antisymm ?_ fun w hw ↦ ?_
  · exact hC.closure_subset_iff.2
      (iUnion₂_subset fun u _ ↦ projMapping_subset C u)
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨u, huU, hwu⟩ := Metric.mem_closure_iff.1 (hU hw) (ε / 2) (by linarith)
  obtain ⟨p, hp⟩ := nearestPoints_nonempty hC ⟨w, hw⟩ u
  rw [← projMapping_eq_nearestPoints] at hp
  have hpu : dist u p = Metric.infDist u C := (mem_projMapping_iff_dist.1 hp).2
  have hle : Metric.infDist u C ≤ dist u w := Metric.infDist_le_dist_of_mem hw
  refine ⟨p, mem_iUnion₂.2 ⟨u, huU, hp⟩, ?_⟩
  have htri : dist w p ≤ dist w u + dist u p := dist_triangle _ _ _
  rw [dist_comm u w] at hle
  linarith

end ProjectionSelections

section ContinuousProjectionSelections

variable {E : Type*} [TopologicalSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Proposition 5.11(c)** in real-valued form: on a nonempty closed value the
extended distance is finite, so continuity of `x ↦ d(u, S(x))` as an
`[0, ∞]`-valued function is continuity of the ordinary distance. -/
theorem continuousWithinAt_infDist_of_svContinuousWithinAt {S : E → Set F}
    {X : Set E} {x : E} (hne : (S x).Nonempty) (hclosed : IsClosed (S x))
    (hS : SvContinuousWithinAt S X x) (u : F) :
    ContinuousWithinAt (fun z ↦ Metric.infDist u (S z)) X x :=
  (ENNReal.tendsto_toReal (Metric.infEDist_ne_top hne)).comp
    ((svContinuousWithinAt_iff_continuousWithinAt hclosed).1 hS u)

/-- **Example 5.57**, outer semicontinuity of the projection mapping
`x ↦ P_{S(x)}(u)` relative to `X`.

A point of the outer limit lies in `S(x̄)` because the projections do, and it
realizes the distance `d(u, S(x̄))` because the nearby projections realize the
nearby distances, which converge to it by 5.11(c).  Neither convexity nor
strict convexity is used. -/
theorem svOscWithinAt_projMapping {S : E → Set F} {X : Set E} {x : E}
    (hx : x ∈ X) (hne : (S x).Nonempty) (hS : SvContinuousWithinAt S X x) (u : F) :
    SvOscWithinAt (fun z ↦ projMapping (S z) u) X x := by
  have hclosed : IsClosed (S x) := hS.1.isClosed hx
  have hcont := continuousWithinAt_infDist_of_svContinuousWithinAt hne hclosed hS u
  intro w hw
  have hwS : w ∈ S x :=
    hS.1 (outerSetLimitAlong_mono (fun z ↦ projMapping_subset (S z) u) hw)
  refine mem_projMapping_iff_dist.2
    ⟨hwS, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hwS)⟩
  refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hfreq := hw (ball w (ε / 2)) (ball_mem_nhds w (by linarith))
  have hev : ∀ᶠ z in nhdsWithin x X,
      Metric.infDist u (S z) < Metric.infDist u (S x) + ε / 2 :=
    hcont.eventually_lt_const (by linarith)
  obtain ⟨z, ⟨v, hvproj, hvball⟩, hzlt⟩ := (hfreq.and_eventually hev).exists
  have h1 : dist u v = Metric.infDist u (S z) := (mem_projMapping_iff_dist.1 hvproj).2
  have h2 : dist v w < ε / 2 := mem_ball.1 hvball
  have htri : dist u w ≤ dist u v + dist v w := dist_triangle _ _ _
  linarith

/-- **Example 5.57**, local boundedness of the projection mapping relative to
`X`: the projections of `u` on `S(z)` sit in the ball of radius `d(u, S(z))`
about `u`, and those radii are eventually bounded by 5.11(c). -/
theorem svLocallyBoundedWithinAt_projMapping {S : E → Set F} {X : Set E} {x : E}
    (hx : x ∈ X) (hne : (S x).Nonempty) (hS : SvContinuousWithinAt S X x) (u : F) :
    SvLocallyBoundedWithinAt (fun z ↦ projMapping (S z) u) X x := by
  have hclosed : IsClosed (S x) := hS.1.isClosed hx
  have hcont := continuousWithinAt_infDist_of_svContinuousWithinAt hne hclosed hS u
  have hev : ∀ᶠ z in nhdsWithin x X,
      Metric.infDist u (S z) < Metric.infDist u (S x) + 1 :=
    hcont.eventually_lt_const (by linarith)
  obtain ⟨V, hV, hVsub⟩ := eventually_nhdsWithin_iff_exists_nhds.1 hev
  refine ⟨V, hV, (isBounded_closedBall (x := u)
    (r := Metric.infDist u (S x) + 1)).subset ?_⟩
  intro w hw
  obtain ⟨z, hzXV, hwz⟩ := mem_svImage.1 hw
  rw [mem_closedBall, dist_comm]
  exact le_of_lt ((mem_projMapping_iff_dist.1 hwz).2 ▸ hVsub z hzXV)

variable [StrictConvexSpace ℝ F]

omit [FiniteDimensional ℝ F] in
/-- On a convex set in a strictly convex space the projection is the single
point named by any one of its members. -/
theorem projMapping_eq_singleton {C : Set F} (hconv : Convex ℝ C) {u w : F}
    (hw : w ∈ projMapping C u) : projMapping C u = {w} := by
  rw [projMapping_eq_nearestPoints] at hw ⊢
  exact eq_singleton_iff_unique_mem.2
    ⟨hw, fun y hy ↦ nearestPoints_subsingleton hconv u hy hw⟩

/-- **Example 5.57**: any function whose values are the projections of `u` on
the images of a continuous convex-valued mapping is continuous relative to
`X`, at every point of `X`.

This is 5.19 relative to `X` applied to `x ↦ P_{S(x)}(u)`, which the two
preceding results make outer semicontinuous and locally bounded relative to
`X`.  Strict convexity is used only to know that the image at the base point
is the single point `s(x̄)`, so that the `ε`-ball around it contains that whole
image and 5.19 pushes a relative neighborhood into the ball. -/
theorem continuousWithinAt_of_mem_projMapping {S : E → Set F} {X : Set E}
    {x : E} (hx : x ∈ X) (hne : (S x).Nonempty) (hconv : Convex ℝ (S x))
    (hS : SvContinuousWithinAt S X x) {u : F} {s : E → F}
    (hs : ∀ z ∈ X, s z ∈ projMapping (S z) u) :
    ContinuousWithinAt s X x := by
  have hsing : projMapping (S x) u = {s x} := projMapping_eq_singleton hconv (hs x hx)
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨V, hV, hVsub⟩ :=
    (svOscWithinAt_projMapping hx hne hS u).exists_nhds_svImage_inter_subset
      (svLocallyBoundedWithinAt_projMapping hx hne hS u) hx isOpen_ball
      (by rw [hsing]; exact singleton_subset_iff.2 (mem_ball_self hε))
  filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with z hzV hzX
  exact mem_ball.1 (hVsub (mem_svImage.2 ⟨z, ⟨hzX, hzV⟩, hs z hzX⟩))

/-- **Example 5.57**, existence: a mapping continuous relative to `X` and
convex-valued admits, for each `u`, a selection `sᵤ` continuous relative to
`X` whose values are the projections of `u`. -/
theorem exists_continuousOn_projMapping_selection {S : E → Set F} {X : Set E}
    (hne : ∀ z ∈ X, (S z).Nonempty) (hconv : ∀ z ∈ X, Convex ℝ (S z))
    (hS : SvContinuousOn S X) (u : F) :
    ∃ s : E → F, (∀ z ∈ X, s z ∈ S z ∧ s z ∈ projMapping (S z) u) ∧
      ContinuousOn s X := by
  classical
  have key : ∀ z : E, ∃ v : F, z ∈ X → v ∈ projMapping (S z) u := by
    intro z
    by_cases hzX : z ∈ X
    · obtain ⟨p, hp⟩ :=
        nearestPoints_nonempty ((hS z hzX).1.isClosed hzX) (hne z hzX) u
      exact ⟨p, fun _ ↦ by rwa [projMapping_eq_nearestPoints]⟩
    · exact ⟨u, fun h ↦ absurd h hzX⟩
  choose s hs using key
  exact ⟨s, fun z hz ↦ ⟨projMapping_subset (S z) u (hs z hz), hs z hz⟩,
    fun z hz ↦ continuousWithinAt_of_mem_projMapping hz (hne z hz) (hconv z hz)
      (hS z hz) hs⟩

/-- **Example 5.57** as printed, with `X = dom S`: nonemptiness of the values
is then automatic. -/
theorem exists_continuousOn_svDom_projMapping_selection {S : E → Set F}
    (hconv : ∀ z ∈ svDom S, Convex ℝ (S z)) (hS : SvContinuousOn S (svDom S))
    (u : F) :
    ∃ s : E → F, (∀ z ∈ svDom S, s z ∈ S z ∧ s z ∈ projMapping (S z) u) ∧
      ContinuousOn s (svDom S) :=
  exists_continuousOn_projMapping_selection (fun _ hz ↦ hz) hconv hS u

omit [StrictConvexSpace ℝ F] in
/-- **Example 5.57**, the concluding statement: if `cl U ⊃ rge S` then the
family of continuous selections `{sᵤ}` indexed by `u ∈ U` fully determines
`S`. -/
theorem closure_iUnion_projMapping_svRange {S : E → Set F} {X : Set E}
    {U : Set F} (hU : svRange S ⊆ closure U) {x : E} (hx : x ∈ X)
    (hS : SvContinuousWithinAt S X x) :
    closure (⋃ u ∈ U, projMapping (S x) u) = S x :=
  closure_iUnion_projMapping (hS.1.isClosed hx) fun _ hw ↦ hU ⟨x, hw⟩

/-- **Example 5.57**, the concluding statement in the book's literal
phrasing: with a family of selections `sᵤ` chosen so that `sᵤ(x)` is the
projection of `u`, the family determines `S` as `S(x) = cl {sᵤ(x) | u ∈ U}`.

Under convexity and strict convexity each `P_{S(x)}(u)` is the single point
`sᵤ(x)`, so the union of the projections is exactly the set of values. -/
theorem closure_image_projMapping_selection {S : E → Set F} {X : Set E}
    {U : Set F} (hU : svRange S ⊆ closure U) {x : E} (hx : x ∈ X)
    (hconv : Convex ℝ (S x)) (hS : SvContinuousWithinAt S X x)
    {s : F → E → F} (hs : ∀ u, s u x ∈ projMapping (S x) u) :
    closure ((fun u ↦ s u x) '' U) = S x := by
  have himage : (fun u ↦ s u x) '' U = ⋃ u ∈ U, projMapping (S x) u := by
    ext w
    simp only [mem_image, mem_iUnion₂]
    exact ⟨fun ⟨u, huU, hwu⟩ ↦ ⟨u, huU, hwu ▸ hs u⟩,
      fun ⟨u, huU, hwu⟩ ↦ ⟨u, huU, by
        have := projMapping_eq_singleton hconv (hs u)
        rw [this] at hwu
        exact (mem_singleton_iff.1 hwu).symm⟩⟩
  rw [himage]
  exact closure_iUnion_projMapping_svRange hU hx hS

end ContinuousProjectionSelections

end RW
