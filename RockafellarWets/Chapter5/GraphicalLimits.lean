/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Pointwise and Graphical Limits of Mappings

Definitions 5.31 and 5.32, with the remarks the book records alongside them
and the relations 5(10) and 5(11).

Section E leaves the neighborhood filters of Sections A--D behind.  The
pointwise limits are the Chapter 4 sequential limits applied to `Sν(x)` one
point at a time; the graphical limits are the Chapter 4 sequential limits
applied to the single sequence of sets `gph Sν` in `IRⁿ × IRᵐ`.  Nothing here
needs the filter-native machinery, so this file works with `atTop` throughout.
-/

import RockafellarWets.Chapter4.ConvexLimits
import RockafellarWets.Chapter4.SetLimitDistances
import RockafellarWets.Chapter5.ConvexSemicontinuity

open Filter Set Topology
open scoped ENNReal

namespace RW

section Selection

variable {E : Type*} [PseudoMetricSpace E]

/-- Membership in the inner limit is witnessed by a single sequence of points
of the sets, converging to the point.

The outer limit needs a subsequence (4.1), but the inner limit does not: the
extended distance to `C n` tends to `0` by 4.2, so choosing a point of `C n`
within `1/(n+1)` of that distance already produces the sequence. -/
theorem mem_innerSetLimit_iff_exists_seq {C : ℕ → Set E} {x : E} :
    x ∈ innerSetLimit C ↔
      ∃ y : ℕ → E, (∀ᶠ n in atTop, y n ∈ C n) ∧ Tendsto y atTop (nhds x) := by
  constructor
  · intro hx
    have hd : Tendsto (fun n ↦ Metric.infEDist x (C n)) atTop (nhds 0) :=
      mem_innerSetLimit_iff_tendsto_infEDist.1 hx
    have hpick : ∀ n : ℕ, ∃ z : E,
        (Metric.infEDist x (C n) ≠ ⊤ → z ∈ C n) ∧
          edist x z ≤ Metric.infEDist x (C n) + ENNReal.ofReal (1 / (n + 1)) := by
      intro n
      by_cases hfin : Metric.infEDist x (C n) = ⊤
      · exact ⟨x, fun h ↦ absurd hfin h, by simp⟩
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (n + 1)) := by
        simp only [ENNReal.ofReal_pos]
        positivity
      obtain ⟨z, hzC, hz⟩ := Metric.infEDist_lt_iff.1
        (ENNReal.lt_add_right hfin hpos.ne')
      exact ⟨z, fun _ ↦ hzC, hz.le⟩
    choose y hyC hyd using hpick
    refine ⟨y, ?_, ?_⟩
    · filter_upwards [hd.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1)] with n hn
      exact hyC n (by simpa using hn.ne_top)
    · rw [tendsto_iff_edist_tendsto_0]
      have hinv : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 1))) atTop (nhds 0) := by
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa only [add_zero] using hd.add hinv)
        (Eventually.of_forall fun _ ↦ zero_le _)
        (Eventually.of_forall fun n ↦ ?_)
      rw [edist_comm]
      exact hyd n
  · rintro ⟨y, hyC, hy⟩ V hV
    filter_upwards [hyC, hy.eventually_mem hV] with n hn hnV
    exact ⟨y n, hn, hnV⟩

end Selection

section PointwiseLimits

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Definition 5.31**: the pointwise outer limit. -/
def pointwiseOuterLimit (Sseq : ℕ → E → Set F) : E → Set F :=
  fun x ↦ outerSetLimit (fun n ↦ Sseq n x)

/-- **Definition 5.31**: the pointwise inner limit. -/
def pointwiseInnerLimit (Sseq : ℕ → E → Set F) : E → Set F :=
  fun x ↦ innerSetLimit (fun n ↦ Sseq n x)

/-- **Definition 5.31**: `Sν → S` pointwise. -/
def PointwiseConverges (Sseq : ℕ → E → Set F) (S : E → Set F) : Prop :=
  ∀ x, PKConverges (fun n ↦ Sseq n x) (S x)

omit [TopologicalSpace E] [TopologicalSpace F] in
/-- The book's ordering of mappings: `S₁ ⊂ S₂` means `gph S₁ ⊂ gph S₂`. -/
theorem svGraph_subset_svGraph_iff {S₁ S₂ : E → Set F} :
    svGraph S₁ ⊆ svGraph S₂ ↔ ∀ x, S₁ x ⊆ S₂ x :=
  ⟨fun h x u hu ↦ h (a := (x, u)) hu, fun h p hp ↦ h p.1 hp⟩

omit [TopologicalSpace E] in
theorem pointwiseInnerLimit_subset (Sseq : ℕ → E → Set F) (x : E) :
    pointwiseInnerLimit Sseq x ⊆ pointwiseOuterLimit Sseq x :=
  innerSetLimit_subset_outerSetLimit _

omit [TopologicalSpace E] in
/-- **Definition 5.31**: pointwise convergence is the two inclusions. -/
theorem pointwiseConverges_iff {Sseq : ℕ → E → Set F} {S : E → Set F} :
    PointwiseConverges Sseq S ↔
      (∀ x, pointwiseOuterLimit Sseq x ⊆ S x) ∧ (∀ x, S x ⊆ pointwiseInnerLimit Sseq x) := by
  constructor
  · intro h
    exact ⟨fun x ↦ ((h x).outer_eq).subset, fun x ↦ ((h x).inner_eq).ge⟩
  · rintro ⟨houter, hinner⟩ x
    exact ⟨Subset.antisymm
        ((innerSetLimit_subset_outerSetLimit _).trans (houter x)) (hinner x),
      Subset.antisymm (houter x)
        ((hinner x).trans (innerSetLimit_subset_outerSetLimit _))⟩

end PointwiseLimits

section GraphicalLimits

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Definition 5.32**: the graphical outer limit, the mapping whose graph is
the outer limit of the graphs. -/
def graphicalOuterLimit (Sseq : ℕ → E → Set F) : E → Set F :=
  fun x ↦ {u | (x, u) ∈ outerSetLimit (fun n ↦ svGraph (Sseq n))}

/-- **Definition 5.32**: the graphical inner limit. -/
def graphicalInnerLimit (Sseq : ℕ → E → Set F) : E → Set F :=
  fun x ↦ {u | (x, u) ∈ innerSetLimit (fun n ↦ svGraph (Sseq n))}

/-- **Definition 5.32**: `Sν → S` graphically, i.e. `gph Sν → gph S`. -/
def GraphicalConverges (Sseq : ℕ → E → Set F) (S : E → Set F) : Prop :=
  PKConverges (fun n ↦ svGraph (Sseq n)) (svGraph S)

@[simp]
theorem svGraph_graphicalOuterLimit (Sseq : ℕ → E → Set F) :
    svGraph (graphicalOuterLimit Sseq) = outerSetLimit (fun n ↦ svGraph (Sseq n)) := by
  ext ⟨x, u⟩
  rfl

@[simp]
theorem svGraph_graphicalInnerLimit (Sseq : ℕ → E → Set F) :
    svGraph (graphicalInnerLimit Sseq) = innerSetLimit (fun n ↦ svGraph (Sseq n)) := by
  ext ⟨x, u⟩
  rfl

theorem graphicalInnerLimit_subset (Sseq : ℕ → E → Set F) (x : E) :
    graphicalInnerLimit Sseq x ⊆ graphicalOuterLimit Sseq x :=
  fun _ hu ↦ innerSetLimit_subset_outerSetLimit _ hu

/-- **Definition 5.32**: graphical convergence is the two inclusions. -/
theorem graphicalConverges_iff {Sseq : ℕ → E → Set F} {S : E → Set F} :
    GraphicalConverges Sseq S ↔
      (∀ x, graphicalOuterLimit Sseq x ⊆ S x) ∧
        (∀ x, S x ⊆ graphicalInnerLimit Sseq x) := by
  have hout : (∀ x, graphicalOuterLimit Sseq x ⊆ S x) ↔
      outerSetLimit (fun n ↦ svGraph (Sseq n)) ⊆ svGraph S := by
    rw [← svGraph_subset_svGraph_iff, svGraph_graphicalOuterLimit]
  have hin : (∀ x, S x ⊆ graphicalInnerLimit Sseq x) ↔
      svGraph S ⊆ innerSetLimit (fun n ↦ svGraph (Sseq n)) := by
    rw [← svGraph_subset_svGraph_iff, svGraph_graphicalInnerLimit]
  rw [GraphicalConverges, hout, hin]
  constructor
  · intro h
    exact ⟨h.outer_eq.subset, h.inner_eq.ge⟩
  · rintro ⟨houter, hinner⟩
    exact ⟨Subset.antisymm
        ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
      Subset.antisymm houter
        (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- The remark after 5.32: graphical limits are outer semicontinuous, their
graphs being set limits and hence closed by 4.4. -/
theorem svOsc_graphicalOuterLimit (Sseq : ℕ → E → Set F) :
    SvOsc (graphicalOuterLimit Sseq) :=
  isClosed_svGraph_iff_svOsc.1 (by simpa using isClosed_outerSetLimit _)

theorem svOsc_graphicalInnerLimit (Sseq : ℕ → E → Set F) :
    SvOsc (graphicalInnerLimit Sseq) :=
  isClosed_svGraph_iff_svOsc.1 (by simpa using isClosed_innerSetLimit _)

/-- The remark after 5.32: a graphical limit is outer semicontinuous. -/
theorem GraphicalConverges.svOsc {Sseq : ℕ → E → Set F} {S : E → Set F}
    (h : GraphicalConverges Sseq S) : SvOsc S :=
  isClosed_svGraph_iff_svOsc.1 (h.outer_eq ▸ isClosed_outerSetLimit _)

end GraphicalLimits

section SequentialDescription

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- **Definition 5.32**, displayed formula for the graphical outer limit: its
values are the limits of values along subsequences. -/
theorem mem_graphicalOuterLimit_iff {Sseq : ℕ → E → Set F} {x : E} {u : F} :
    u ∈ graphicalOuterLimit Sseq x ↔
      ∃ (φ : ℕ → ℕ) (y : ℕ → E) (v : ℕ → F), StrictMono φ ∧
        (∀ n, v n ∈ Sseq (φ n) (y n)) ∧
        Tendsto y atTop (nhds x) ∧ Tendsto v atTop (nhds u) := by
  rw [graphicalOuterLimit, mem_setOf_eq, mem_outerSetLimit_iff_exists_subsequence]
  constructor
  · rintro ⟨φ, p, hφ, hp, hpu⟩
    exact ⟨φ, fun n ↦ (p n).1, fun n ↦ (p n).2, hφ, hp,
      (continuous_fst.tendsto _).comp hpu, (continuous_snd.tendsto _).comp hpu⟩
  · rintro ⟨φ, y, v, hφ, hv, hy, hvu⟩
    exact ⟨φ, fun n ↦ (y n, v n), hφ, hv, hy.prodMk_nhds hvu⟩

/-- **Definition 5.32**, displayed formula for the graphical inner limit: its
values are the limits of values along the whole sequence.  Unlike the outer
limit, no subsequence is needed, but the selection is only eventual. -/
theorem mem_graphicalInnerLimit_iff {Sseq : ℕ → E → Set F} {x : E} {u : F} :
    u ∈ graphicalInnerLimit Sseq x ↔
      ∃ (y : ℕ → E) (v : ℕ → F), (∀ᶠ n in atTop, v n ∈ Sseq n (y n)) ∧
        Tendsto y atTop (nhds x) ∧ Tendsto v atTop (nhds u) := by
  rw [graphicalInnerLimit, mem_setOf_eq, mem_innerSetLimit_iff_exists_seq]
  constructor
  · rintro ⟨p, hp, hpu⟩
    exact ⟨fun n ↦ (p n).1, fun n ↦ (p n).2, hp,
      (continuous_fst.tendsto _).comp hpu, (continuous_snd.tendsto _).comp hpu⟩
  · rintro ⟨y, v, hv, hy, hvu⟩
    exact ⟨fun n ↦ (y n, v n), hv, hy.prodMk_nhds hvu⟩

end SequentialDescription

section Inversion

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Formula 5(10)** for outer limits: graphical limits commute with
inversion, since inverting a graph is a homeomorphism of the product. -/
theorem graphicalOuterLimit_svInv (Sseq : ℕ → E → Set F) :
    graphicalOuterLimit (fun n ↦ svInv (Sseq n)) = svInv (graphicalOuterLimit Sseq) := by
  funext u
  ext x
  simp only [graphicalOuterLimit, mem_setOf_eq, mem_svInv]
  constructor
  · intro h V hV
    refine (h (Prod.swap ⁻¹' V) (continuous_swap.continuousAt hV)).mono ?_
    rintro n ⟨p, hp, hpV⟩
    exact ⟨p.swap, by simpa [svGraph_svInv] using hp, hpV⟩
  · intro h V hV
    refine (h (Prod.swap ⁻¹' V) (continuous_swap.continuousAt hV)).mono ?_
    rintro n ⟨p, hp, hpV⟩
    exact ⟨p.swap, by simpa [svGraph_svInv] using hp, hpV⟩

/-- **Formula 5(10)** for inner limits. -/
theorem graphicalInnerLimit_svInv (Sseq : ℕ → E → Set F) :
    graphicalInnerLimit (fun n ↦ svInv (Sseq n)) = svInv (graphicalInnerLimit Sseq) := by
  funext u
  ext x
  simp only [graphicalInnerLimit, mem_setOf_eq, mem_svInv]
  constructor
  · intro h V hV
    refine (h (Prod.swap ⁻¹' V) (continuous_swap.continuousAt hV)).mono ?_
    rintro n ⟨p, hp, hpV⟩
    exact ⟨p.swap, by simpa [svGraph_svInv] using hp, hpV⟩
  · intro h V hV
    refine (h (Prod.swap ⁻¹' V) (continuous_swap.continuousAt hV)).mono ?_
    rintro n ⟨p, hp, hpV⟩
    exact ⟨p.swap, by simpa [svGraph_svInv] using hp, hpV⟩

/-- **Formula 5(10)**: `Sν →g S` exactly when `(Sν)⁻¹ →g S⁻¹`. -/
theorem graphicalConverges_svInv_iff {Sseq : ℕ → E → Set F} {S : E → Set F} :
    GraphicalConverges (fun n ↦ svInv (Sseq n)) (svInv S) ↔
      GraphicalConverges Sseq S := by
  rw [graphicalConverges_iff, graphicalConverges_iff,
    graphicalOuterLimit_svInv, graphicalInnerLimit_svInv]
  constructor
  · rintro ⟨ho, hi⟩
    exact ⟨fun _ _ hu ↦ ho _ hu, fun _ _ hu ↦ hi _ hu⟩
  · rintro ⟨ho, hi⟩
    exact ⟨fun _ _ hx ↦ ho _ hx, fun _ _ hx ↦ hi _ hx⟩

end Inversion

section PointwiseVersusGraphical

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Formula 5(11)**, first inclusion: the pointwise inner limit sits inside
the graphical inner limit, via the constant sequence `xν ≡ x`. -/
theorem pointwiseInnerLimit_subset_graphicalInnerLimit (Sseq : ℕ → E → Set F)
    (x : E) : pointwiseInnerLimit Sseq x ⊆ graphicalInnerLimit Sseq x := by
  intro u hu W hW
  obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.1 hW
  filter_upwards [hu V₂ hV₂] with n hn
  obtain ⟨v, hvS, hvV⟩ := hn
  exact ⟨(x, v), hvS, hsub ⟨mem_of_mem_nhds hV₁, hvV⟩⟩

/-- **Formula 5(11)**, third inclusion: the pointwise outer limit sits inside
the graphical outer limit. -/
theorem pointwiseOuterLimit_subset_graphicalOuterLimit (Sseq : ℕ → E → Set F)
    (x : E) : pointwiseOuterLimit Sseq x ⊆ graphicalOuterLimit Sseq x := by
  intro u hu W hW
  obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.1 hW
  refine (hu V₂ hV₂).mono ?_
  rintro n ⟨v, hvS, hvV⟩
  exact ⟨(x, v), hvS, hsub ⟨mem_of_mem_nhds hV₁, hvV⟩⟩

/-- The book's "in particular": when both limits exist, `p-lim Sν ⊂ g-lim Sν`. -/
theorem PointwiseConverges.subset_of_graphicalConverges
    {Sseq : ℕ → E → Set F} {P G : E → Set F} (hP : PointwiseConverges Sseq P)
    (hG : GraphicalConverges Sseq G) (x : E) : P x ⊆ G x := by
  have hPin : P x ⊆ pointwiseInnerLimit Sseq x := ((hP x).inner_eq).ge
  exact (hPin.trans (pointwiseInnerLimit_subset_graphicalInnerLimit Sseq x)).trans
    (fun u hu ↦ (hG.inner_eq ▸ hu : (x, u) ∈ svGraph G))

end PointwiseVersusGraphical

section GraphConvexity

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The remark after 5.32: the graphical inner limit of graph-convex mappings
is graph-convex, by the inner-limit convexity of 4.15. -/
theorem svGraphConvex_graphicalInnerLimit {Sseq : ℕ → E → Set F}
    (h : ∀ n, SvGraphConvex (Sseq n)) : SvGraphConvex (graphicalInnerLimit Sseq) := by
  rw [SvGraphConvex, svGraph_graphicalInnerLimit]
  exact convex_innerSetLimit _ h

/-- The rest of that remark: the graphical inner limit is then inner
semicontinuous on the interior of its domain, by 5.9(b). -/
theorem svIscAt_graphicalInnerLimit {Sseq : ℕ → E → Set F}
    (h : ∀ n, SvGraphConvex (Sseq n)) {x : E}
    (hx : x ∈ interior (svDom (graphicalInnerLimit Sseq))) :
    SvIscAt (graphicalInnerLimit Sseq) x :=
  (svGraphConvex_graphicalInnerLimit h).svIscAt hx

end GraphConvexity

end RW
