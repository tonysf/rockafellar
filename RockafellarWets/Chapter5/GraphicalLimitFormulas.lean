/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Graphical Limit Formulas at a Point

Proposition 5.33, with formulas 5(7) and 5(9).

Each graphical limit at `x` has two descriptions: a union over all sequences
`xν → x` of the corresponding Chapter 4 limit of the values `Sν(xν)`, and an
intersection over `δ > 0` of the corresponding limit of the images
`Sν(x + δIB)`.  The second is the easier of the two, being a rearrangement of
quantifiers: a product neighborhood `IB(x, δ) × IB(u, ε)` meets `gph Sν`
exactly when `IB(u, ε)` meets `Sν(x + δIB)`.

The first is where the two limits part company.  For the inner limit the
witnessing sequence is already at hand, by the selection lemma of
[`GraphicalLimits.lean`](GraphicalLimits.lean).  For the outer limit only a
subsequence is available, and it has to be spread out to a full sequence,
which is what `Function.extend` does here: off the range of the subsequence
the constructed sequence sits at `x` itself, which costs nothing since only
frequent hits are being claimed.
-/

import RockafellarWets.Chapter5.GraphicalLimits
import RockafellarWets.Chapter5.LocalBoundedness

open Filter Metric Set Topology

namespace RW

section Extend

variable {E : Type*} [TopologicalSpace E]

/-- A subsequence of points converging to `x` extends to a full sequence
converging to `x`, by parking the sequence at `x` off the subsequence. -/
theorem tendsto_extend_of_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {y : ℕ → E} {x : E} (hy : Tendsto y atTop (nhds x)) :
    Tendsto (Function.extend φ y (fun _ ↦ x)) atTop (nhds x) := by
  have key : ∀ V ∈ nhds x, ∀ᶠ m in atTop, Function.extend φ y (fun _ ↦ x) m ∈ V := by
    intro V hV
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hy.eventually_mem hV)
    filter_upwards [eventually_ge_atTop (φ N)] with m hm
    by_cases hmem : ∃ n, φ n = m
    · obtain ⟨n, rfl⟩ := hmem
      rw [hφ.injective.extend_apply]
      exact hN n (hφ.le_iff_le.1 hm)
    · rw [Function.extend_apply' _ _ _ hmem]
      exact mem_of_mem_nhds hV
  exact fun V hV ↦ key V hV

end Extend

section SequenceFormulas

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- **Proposition 5.33**, inner formula: the graphical inner limit at `x` is
the union of the inner limits of `Sν(xν)` over all sequences `xν → x`. -/
theorem graphicalInnerLimit_eq_iUnion (Sseq : ℕ → E → Set F) (x : E) :
    graphicalInnerLimit Sseq x =
      ⋃ y ∈ {y : ℕ → E | Tendsto y atTop (nhds x)},
        innerSetLimit fun n ↦ Sseq n (y n) := by
  refine Subset.antisymm (fun u hu ↦ ?_) (iUnion₂_subset fun y hy u hu ↦ ?_)
  · obtain ⟨y, v, hv, hy, hvu⟩ := mem_graphicalInnerLimit_iff.1 hu
    refine mem_iUnion₂.2 ⟨y, hy, fun W hW ↦ ?_⟩
    filter_upwards [hv, hvu.eventually_mem hW] with n hn hnW
    exact ⟨v n, hn, hnW⟩
  · intro W hW
    obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.1 hW
    filter_upwards [hy hV₁, hu V₂ hV₂] with n hn hhit
    obtain ⟨v, hvS, hvV⟩ := hhit
    exact ⟨(y n, v), hvS, hsub ⟨hn, hvV⟩⟩

/-- **Proposition 5.33**, outer formula: the graphical outer limit at `x` is
the union of the outer limits of `Sν(xν)` over all sequences `xν → x`. -/
theorem graphicalOuterLimit_eq_iUnion (Sseq : ℕ → E → Set F) (x : E) :
    graphicalOuterLimit Sseq x =
      ⋃ y ∈ {y : ℕ → E | Tendsto y atTop (nhds x)},
        outerSetLimit fun n ↦ Sseq n (y n) := by
  refine Subset.antisymm (fun u hu ↦ ?_) (iUnion₂_subset fun y hy u hu ↦ ?_)
  · obtain ⟨φ, y, v, hφ, hv, hy, hvu⟩ := mem_graphicalOuterLimit_iff.1 hu
    refine mem_iUnion₂.2 ⟨Function.extend φ y (fun _ ↦ x),
      tendsto_extend_of_strictMono hφ hy, fun W hW ↦ ?_⟩
    have hev : ∀ᶠ n in atTop,
        (Sseq (φ n) (Function.extend φ y (fun _ ↦ x) (φ n)) ∩ W).Nonempty := by
      filter_upwards [hvu.eventually_mem hW] with n hn
      rw [hφ.injective.extend_apply]
      exact ⟨v n, hv n, hn⟩
    exact Frequently.filter_mono
      ((frequently_map (m := φ)).2 hev.frequently) hφ.tendsto_atTop
  · intro W hW
    obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.1 hW
    refine ((hu V₂ hV₂).and_eventually (hy hV₁)).mono ?_
    rintro n ⟨⟨v, hvS, hvV⟩, hn⟩
    exact ⟨(y n, v), hvS, hsub ⟨hn, hvV⟩⟩

end SequenceFormulas

section BallFormulas

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- A product ball meets the graph exactly when the value ball meets the
image of the argument ball.  This is the whole content of the second pair of
formulas in 5.33. -/
theorem graph_inter_prod_nonempty_iff (S : E → Set F) {x : E} {u : F}
    {δ ε : ℝ} :
    (svGraph S ∩ (closedBall x δ ×ˢ ball u ε)).Nonempty ↔
      (svImage S (closedBall x δ) ∩ ball u ε).Nonempty := by
  constructor
  · rintro ⟨⟨y, v⟩, hv, hyδ, hvε⟩
    exact ⟨v, mem_svImage.2 ⟨y, hyδ, hv⟩, hvε⟩
  · rintro ⟨v, hv, hvε⟩
    obtain ⟨y, hyδ, hvS⟩ := mem_svImage.1 hv
    exact ⟨(y, v), hvS, hyδ, hvε⟩

/-- **Proposition 5.33**, second inner formula:
`g-liminf Sν(x) = limδ↓0 liminfν Sν(x + δIB)`, the limit being the
intersection since the sets shrink with `δ`. -/
theorem graphicalInnerLimit_eq_iInter (Sseq : ℕ → E → Set F) (x : E) :
    graphicalInnerLimit Sseq x =
      ⋂ δ ∈ Ioi (0 : ℝ),
        innerSetLimit fun n ↦ svImage (Sseq n) (closedBall x δ) := by
  ext u
  simp only [mem_iInter₂, mem_Ioi]
  constructor
  · intro hu δ hδ
    rw [mem_innerSetLimit_iff_eventually_ball]
    intro ε hε
    have hW : closedBall x δ ×ˢ ball u ε ∈ nhds (x, u) :=
      mem_nhds_prod_iff.2 ⟨ball x δ, ball_mem_nhds x hδ, ball u ε,
        ball_mem_nhds u hε, prod_mono ball_subset_closedBall Subset.rfl⟩
    filter_upwards [hu _ hW] with n hn
    exact (graph_inter_prod_nonempty_iff (Sseq n)).1 hn
  · intro hu W hW
    obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.1 hW
    obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hV₁
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV₂
    have hball := (mem_innerSetLimit_iff_eventually_ball.1 (hu (δ / 2) (by positivity))) ε hε
    filter_upwards [hball] with n hn
    obtain ⟨p, hp, hpV⟩ := (graph_inter_prod_nonempty_iff (Sseq n)).2 hn
    exact ⟨p, hp, hsub ⟨hδV ((closedBall_subset_ball (by linarith)) hpV.1),
      hεV hpV.2⟩⟩

/-- **Proposition 5.33**, second outer formula:
`g-limsup Sν(x) = limδ↓0 limsupν Sν(x + δIB)`. -/
theorem graphicalOuterLimit_eq_iInter (Sseq : ℕ → E → Set F) (x : E) :
    graphicalOuterLimit Sseq x =
      ⋂ δ ∈ Ioi (0 : ℝ),
        outerSetLimit fun n ↦ svImage (Sseq n) (closedBall x δ) := by
  ext u
  simp only [mem_iInter₂, mem_Ioi]
  constructor
  · intro hu δ hδ
    rw [mem_outerSetLimit_iff_frequently_ball]
    intro ε hε
    have hW : closedBall x δ ×ˢ ball u ε ∈ nhds (x, u) :=
      mem_nhds_prod_iff.2 ⟨ball x δ, ball_mem_nhds x hδ, ball u ε,
        ball_mem_nhds u hε, prod_mono ball_subset_closedBall Subset.rfl⟩
    exact (hu _ hW).mono fun n hn ↦ (graph_inter_prod_nonempty_iff (Sseq n)).1 hn
  · intro hu W hW
    obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.1 hW
    obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hV₁
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV₂
    have hball := (mem_outerSetLimit_iff_frequently_ball.1 (hu (δ / 2) (by positivity))) ε hε
    refine hball.mono fun n hn ↦ ?_
    obtain ⟨p, hp, hpV⟩ := (graph_inter_prod_nonempty_iff (Sseq n)).2 hn
    exact ⟨p, hp, hsub ⟨hδV ((closedBall_subset_ball (by linarith)) hpV.1),
      hεV hpV.2⟩⟩

end BallFormulas

section Bivariate

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- **Formula 5(9)**: the graphical outer limit at `x̄` is the bivariate outer
limit of `Sν(x)` as `ν → ∞` and `x → x̄`, taken along the product filter.

The graphical inner limit has no such description; the book says so, and the
counterexample it alludes to is not formalized here. -/
theorem graphicalOuterLimit_eq_outerSetLimitAlong (Sseq : ℕ → E → Set F) (x : E) :
    graphicalOuterLimit Sseq x =
      outerSetLimitAlong (atTop ×ˢ nhds x) fun p : ℕ × E ↦ Sseq p.1 p.2 := by
  ext u
  constructor
  · intro hu V hV
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨A, hA, B, hB, hsub⟩ := Filter.mem_prod_iff.1 hU
    have hW : B ×ˢ V ∈ nhds (x, u) :=
      mem_nhds_prod_iff.2 ⟨B, hB, V, hV, Subset.rfl⟩
    obtain ⟨n, ⟨⟨p, hp, hpB, hpV⟩, hnA⟩⟩ :=
      ((hu _ hW).and_eventually (eventually_mem_set.2 hA)).exists
    exact ⟨(n, p.1), hsub ⟨hnA, hpB⟩, ⟨p.2, hp, hpV⟩⟩
  · intro hu W hW
    obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.1 hW
    rw [Filter.frequently_iff]
    intro A hA
    obtain ⟨q, hq, v, hvS, hvV⟩ :=
      Filter.frequently_iff.1 (hu V₂ hV₂) (Filter.prod_mem_prod hA hV₁)
    exact ⟨q.1, hq.1, ⟨(q.2, v), hvS, hsub ⟨hq.2, hvV⟩⟩⟩

end Bivariate

section AtAPoint

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- The book's pointwise reading of graphical convergence, taken from 5(7):
`Sν → S` graphically at `x̄`. -/
def GraphicalConvergesAt (Sseq : ℕ → E → Set F) (S : E → Set F) (x : E) : Prop :=
  graphicalOuterLimit Sseq x ⊆ S x ∧ S x ⊆ graphicalInnerLimit Sseq x

/-- Graphical convergence is graphical convergence at every point. -/
theorem graphicalConverges_iff_forall_graphicalConvergesAt
    {Sseq : ℕ → E → Set F} {S : E → Set F} :
    GraphicalConverges Sseq S ↔ ∀ x, GraphicalConvergesAt Sseq S x := by
  rw [graphicalConverges_iff]
  exact ⟨fun h x ↦ ⟨h.1 x, h.2 x⟩, fun h ↦ ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩⟩

/-- **Formula 5(7)**: graphical convergence at `x̄` in the book's displayed
form, as a two-sided condition on limits of values along sequences `xν → x̄`. -/
theorem graphicalConvergesAt_iff {Sseq : ℕ → E → Set F} {S : E → Set F} {x : E} :
    GraphicalConvergesAt Sseq S x ↔
      (⋃ y ∈ {y : ℕ → E | Tendsto y atTop (nhds x)},
          outerSetLimit fun n ↦ Sseq n (y n)) ⊆ S x ∧
        S x ⊆ ⋃ y ∈ {y : ℕ → E | Tendsto y atTop (nhds x)},
          innerSetLimit fun n ↦ Sseq n (y n) := by
  rw [GraphicalConvergesAt, graphicalOuterLimit_eq_iUnion,
    graphicalInnerLimit_eq_iUnion]

/-- **Formula 5(7)** for the whole sequence of mappings. -/
theorem graphicalConverges_iff_forall_iUnion {Sseq : ℕ → E → Set F}
    {S : E → Set F} :
    GraphicalConverges Sseq S ↔ ∀ x,
      (⋃ y ∈ {y : ℕ → E | Tendsto y atTop (nhds x)},
          outerSetLimit fun n ↦ Sseq n (y n)) ⊆ S x ∧
        S x ⊆ ⋃ y ∈ {y : ℕ → E | Tendsto y atTop (nhds x)},
          innerSetLimit fun n ↦ Sseq n (y n) := by
  rw [graphicalConverges_iff_forall_graphicalConvergesAt]
  exact forall_congr' fun _ ↦ graphicalConvergesAt_iff

end AtAPoint

end RW
