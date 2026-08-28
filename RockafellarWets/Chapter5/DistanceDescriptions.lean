/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Distance Function Descriptions of Convergence

Clauses (b) and (c) of Exercise 5.42, over a hub that is 4.7 and 4.10 fused
and stated along an arbitrary filter.

The observation that unlocks (b) is that the `ε`-`ρ` form of continuous
convergence recorded after 5.41 is *already* a statement along the product
filter: `∃ V ∈ N(x̄), ∀ᶠ ν, ∀ y ∈ V ∩ X` and `∀ᶠ (ν, y) in atTop ×ˢ N_X(x̄)`
are the same thing unfolded.  So what 5.42(b) asks for is exactly the passage
between those inclusions and the distance functions, for a family of sets
indexed along an arbitrary filter against one *fixed* closed target -- which
is what `eventually_inclusions_iff_tendsto_infEDist` provides, and which
specializes to 4.7-plus-4.10 when the filter is `atTop`.

No subsequence is extracted anywhere; the only compactness used is two finite
subcovers, of `C ∩ ρIB` and of `ρIB \ (C + εIB)`, in the direction that builds
inclusions out of distances.  This is the same device as in 5.12.

Clause (c) does not fit that hub, its target `S(x)` moving with `x`, and it is
proved directly.  Both directions turn on a single finite cover of the
*compact ball* `ρIB` -- not of any set built from `S` -- which is what makes
the estimate uniform over `x ∈ X`.  The truncation `min(d(u, ·), η)` is what
lets the statement survive empty values under a real-valued uniform limit:
without it the functions would take the value `∞` and could not converge
uniformly in any metric sense.
-/

import RockafellarWets.Chapter5.ContinuousUniformConvergence

open Filter Metric Set Topology
open scoped ENNReal

namespace RW

section FilterGeneral

variable {ι F : Type*} {l : Filter ι} [NormedAddCommGroup F] [ProperSpace F]
variable {A : ι → Set F} {C : Set F}

omit [ProperSpace F] in
/-- The `ε`-inclusions force the distances to converge.

The lower bound on `d(u, A i)` comes from the first inclusion: a point of
`A i` is either outside the ball `ρIB`, and then far from `u` because `ρ` was
chosen as `‖u‖ + t`, or inside it and hence within `ε` of `C`, where every
point is at distance at least `t` from `u`.  The upper bound comes from the
second inclusion applied to one point `w ∈ C` nearly realizing `d(u, C)`. -/
theorem tendsto_infEDist_of_eventually_inclusions
    (h : ∀ ε > 0, ∀ ρ > 0, ∀ᶠ i in l,
      A i ∩ closedBall 0 ρ ⊆ thickening ε C ∧
        C ∩ closedBall 0 ρ ⊆ thickening ε (A i)) (u : F) :
    Tendsto (fun i ↦ infEDist u (A i)) l (nhds (infEDist u C)) := by
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun c hc ↦ ?_⟩
  · -- `b < d(u, C)` stays below `d(u, A i)` eventually.
    have hbtop : b ≠ ⊤ := (hb.trans_le le_top).ne
    obtain ⟨t, hst, hle⟩ : ∃ t : ℝ, b.toReal < t ∧ ENNReal.ofReal t ≤ infEDist u C := by
      by_cases hd : infEDist u C = ⊤
      · exact ⟨b.toReal + 1, by linarith, hd ▸ le_top⟩
      · refine ⟨(infEDist u C).toReal, ?_, by rw [ENNReal.ofReal_toReal hd]⟩
        exact (ENNReal.toReal_lt_toReal hbtop hd).2 hb
    have hs0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
    have ht0 : 0 < t := lt_of_le_of_lt hs0 hst
    set ε : ℝ := (t - b.toReal) / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    have hρ : 0 < ‖u‖ + t := by positivity
    filter_upwards [h ε hε (‖u‖ + t) hρ] with i hi
    have hlow : ENNReal.ofReal (t - ε) ≤ infEDist u (A i) := by
      refine Metric.le_infEDist.2 fun v hv ↦ ?_
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hball : ‖v‖ ≤ ‖u‖ + t
      · obtain ⟨w, hwC, hvw⟩ :=
          mem_thickening_iff.1 (hi.1 ⟨hv, mem_closedBall_zero_iff.2 hball⟩)
        have huw : t ≤ dist u w := by
          have hle' : ENNReal.ofReal t ≤ edist u w :=
            hle.trans (Metric.infEDist_le_edist_of_mem hwC)
          rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hle'
        have htri := dist_triangle u v w
        linarith
      · push_neg at hball
        have h1 : ‖v‖ - ‖u‖ ≤ dist u v := by
          rw [dist_comm, dist_eq_norm]
          simpa using norm_sub_norm_le v u
        rw [hεdef]
        linarith
    refine lt_of_lt_of_le ((ENNReal.lt_ofReal_iff_toReal_lt hbtop).2 ?_) hlow
    rw [hεdef]
    linarith
  · -- `d(u, A i)` stays below any `c > d(u, C)` eventually.
    have hdtop : infEDist u C ≠ ⊤ := (hc.trans_le le_top).ne
    obtain ⟨η, hη, hlt⟩ : ∃ η : ℝ, 0 < η ∧
        ENNReal.ofReal ((infEDist u C).toReal + 2 * η) < c := by
      by_cases hctop : c = ⊤
      · exact ⟨1, one_pos, by rw [hctop]; exact ENNReal.ofReal_lt_top⟩
      · have hlt' : (infEDist u C).toReal < c.toReal :=
          (ENNReal.toReal_lt_toReal hdtop hctop).2 hc
        have hd0 : (0 : ℝ) ≤ (infEDist u C).toReal := ENNReal.toReal_nonneg
        refine ⟨(c.toReal - (infEDist u C).toReal) / 4, by linarith, ?_⟩
        calc ENNReal.ofReal
              ((infEDist u C).toReal + 2 * ((c.toReal - (infEDist u C).toReal) / 4))
            < ENNReal.ofReal c.toReal :=
              (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
          _ = c := ENNReal.ofReal_toReal hctop
    obtain ⟨w, hwC, hw⟩ : ∃ w ∈ C, edist u w < infEDist u C + ENNReal.ofReal η :=
      Metric.infEDist_lt_iff.1 (ENNReal.lt_add_right hdtop (ENNReal.ofReal_pos.2 hη).ne')
    have hwreal : dist u w < (infEDist u C).toReal + η := by
      have h1 : edist u w < ENNReal.ofReal ((infEDist u C).toReal + η) := by
        rwa [ENNReal.ofReal_add ENNReal.toReal_nonneg hη.le,
          ENNReal.ofReal_toReal hdtop]
      rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h1
    filter_upwards [h η hη (‖w‖ + 1) (by positivity)] with i hi
    obtain ⟨a, haA, hwa⟩ :=
      mem_thickening_iff.1 (hi.2 ⟨hwC, mem_closedBall_zero_iff.2 (by linarith)⟩)
    refine lt_of_le_of_lt (Metric.infEDist_le_edist_of_mem haA) (lt_of_lt_of_le ?_ hlt.le)
    rw [edist_dist]
    refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.2 ?_
    have := dist_triangle u w a
    linarith

/-- Conversely the distances force the inclusions.  This is where compactness
enters, twice: `C ∩ ρIB` is covered by finitely many `ε/2`-balls, and
`ρIB \ (C + εIB)` -- compact because a thickening is open -- by finitely many
`ε/4`-balls.  In each case control at the finitely many centres, which the
convergence of the distances supplies, is control at every point at once. -/
theorem eventually_inclusions_of_tendsto_infEDist (hC : IsClosed C)
    (h : ∀ u : F, Tendsto (fun i ↦ infEDist u (A i)) l (nhds (infEDist u C)))
    {ε : ℝ} (hε : 0 < ε) (ρ : ℝ) :
    ∀ᶠ i in l, A i ∩ closedBall 0 ρ ⊆ thickening ε C ∧
      C ∩ closedBall 0 ρ ⊆ thickening ε (A i) := by
  classical
  obtain ⟨t, htK, htcover⟩ :=
    ((isCompact_closedBall (0 : F) ρ).inter_left hC).elim_nhds_subcover
      (fun u ↦ ball u (ε / 2)) fun u _ ↦ ball_mem_nhds u (by linarith)
  obtain ⟨t', ht'K, ht'cover⟩ :=
    ((isCompact_closedBall (0 : F) ρ).diff isOpen_thickening).elim_nhds_subcover
      (fun u ↦ ball u (ε / 4)) fun u _ ↦ ball_mem_nhds u (by linarith)
  have hev₂ : ∀ᶠ i in l, ∀ u ∈ t, infEDist u (A i) < ENNReal.ofReal (ε / 2) :=
    (eventually_all_finset t).2 fun u hu ↦
      (h u).eventually_lt_const (by
        rw [Metric.infEDist_zero_of_mem (htK u hu).1]
        exact ENNReal.ofReal_pos.2 (by linarith))
  have hev₁ : ∀ᶠ i in l, ∀ u ∈ t', ENNReal.ofReal (3 * ε / 4) < infEDist u (A i) :=
    (eventually_all_finset t').2 fun u hu ↦
      (h u).eventually_const_lt (by
        have hfar : ENNReal.ofReal ε ≤ infEDist u C := by
          by_contra hlt
          push_neg at hlt
          exact (ht'K u hu).2 (Metric.mem_thickening_iff_infEDist_lt.2 hlt)
        exact lt_of_lt_of_le
          ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)) hfar)
  filter_upwards [hev₁, hev₂] with i h1 h2
  constructor
  · intro v hv
    by_contra hvnot
    obtain ⟨u, hu, hvu⟩ := mem_iUnion₂.1 (ht'cover ⟨hv.2, hvnot⟩)
    have hle : infEDist u (A i) ≤ edist u v := Metric.infEDist_le_edist_of_mem hv.1
    have hsmall : edist u v < ENNReal.ofReal (ε / 4) := by
      rw [edist_dist]
      refine (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ?_
      rw [dist_comm]
      exact mem_ball.1 hvu
    have hchain : ENNReal.ofReal (3 * ε / 4) < ENNReal.ofReal (ε / 4) :=
      lt_of_lt_of_le (h1 u hu) (hle.trans hsmall.le)
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)] at hchain
    linarith
  · intro w hw
    obtain ⟨u, hu, hwu⟩ := mem_iUnion₂.1 (htcover hw)
    obtain ⟨a, haA, hua⟩ := Metric.infEDist_lt_iff.1 (h2 u hu)
    refine mem_thickening_iff.2 ⟨a, haA, ?_⟩
    have h3 : dist u a < ε / 2 := by
      rw [edist_dist] at hua
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 hua
    have h4 : dist w u < ε / 2 := mem_ball.1 hwu
    have := dist_triangle w u a
    linarith

/-- **The hub for 5.42(b) and (c).**  For a family of sets indexed along an
arbitrary filter and a *fixed* closed target, the `ε`-`ρ` inclusions of 4.10
and the pointwise convergence of the extended distance functions of 4.7 say
the same thing.  Taking `l = atTop` recovers 4.7 and 4.10 together. -/
theorem eventually_inclusions_iff_tendsto_infEDist (hC : IsClosed C) :
    (∀ ε > 0, ∀ ρ > 0, ∀ᶠ i in l,
        A i ∩ closedBall 0 ρ ⊆ thickening ε C ∧
          C ∩ closedBall 0 ρ ⊆ thickening ε (A i)) ↔
      ∀ u : F, Tendsto (fun i ↦ infEDist u (A i)) l (nhds (infEDist u C)) :=
  ⟨tendsto_infEDist_of_eventually_inclusions,
    fun h _ hε ρ _ ↦ eventually_inclusions_of_tendsto_infEDist hC h hε ρ⟩

end FilterGeneral

section ProductFilter

variable {E : Type*} [PseudoMetricSpace E]

/-- The neighborhood form of a bivariate eventuality is the product-filter
form: `∃ V ∈ N(x̄), ∀ᶠ ν, ∀ y ∈ V ∩ X` and `∀ᶠ (ν, y) in atTop ×ˢ N_X(x̄)` are
the same statement unfolded. -/
theorem eventually_prod_atTop_nhdsWithin_iff {P : ℕ → E → Prop} {X : Set E}
    {x : E} :
    (∀ᶠ p in atTop ×ˢ nhdsWithin x X, P p.1 p.2) ↔
      ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V ∩ X, P n y := by
  constructor
  · intro hp
    obtain ⟨A, hA, B, hB, hsub⟩ := Filter.mem_prod_iff.1 hp
    obtain ⟨V, hV, hVB⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hB
    refine ⟨V, hV, (Filter.eventually_mem_set.2 hA).mono fun n hn y hy ↦ ?_⟩
    exact hsub (a := (n, y)) ⟨hn, hVB hy⟩
  · rintro ⟨V, hV, hN⟩
    exact Filter.mem_prod_iff.2 ⟨_, hN, V ∩ X,
      inter_mem (nhdsWithin_le_nhds hV) self_mem_nhdsWithin,
      fun p hp ↦ hp.1 p.2 hp.2⟩

end ProductFilter

section Clause_b

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E} {x : E}

/-- **Exercise 5.42(b)**, in the relative form the book records right after the
statement: `Sν` converges continuously to `S` at `x̄` relative to `X` exactly
when `d(u, Sν(x)) → d(u, S(x̄))` as `ν → ∞` and `x → x̄` in `X`, for every `u`.

The bivariate limit is taken along `atTop ×ˢ N_X(x̄)`, which is precisely the
filter along which the `ε`-`ρ` form of 5.41 already asserts its inclusions. -/
theorem svConvergesContinuouslyWithinAt_iff_tendsto_infEDist (hx : x ∈ X)
    (hS : IsClosed (S x)) :
    SvConvergesContinuouslyWithinAt Sseq S X x ↔
      ∀ u : F, Tendsto (fun p : ℕ × E ↦ infEDist u (Sseq p.1 p.2))
        (atTop ×ˢ nhdsWithin x X) (nhds (infEDist u (S x))) := by
  rw [svConvergesContinuouslyWithinAt_iff hx hS,
    ← eventually_inclusions_iff_tendsto_infEDist
      (l := atTop ×ˢ nhdsWithin x X) (A := fun p : ℕ × E ↦ Sseq p.1 p.2) hS]
  exact forall₂_congr fun _ _ ↦ forall₂_congr fun _ _ ↦
    eventually_prod_atTop_nhdsWithin_iff.symm

/-- **Exercise 5.42(b)** as printed, in the absolute case. -/
theorem svConvergesContinuouslyAt_iff_tendsto_infEDist (hS : IsClosed (S x)) :
    SvConvergesContinuouslyAt Sseq S x ↔
      ∀ u : F, Tendsto (fun p : ℕ × E ↦ infEDist u (Sseq p.1 p.2))
        (atTop ×ˢ nhds x) (nhds (infEDist u (S x))) := by
  rw [← nhdsWithin_univ]
  exact svConvergesContinuouslyWithinAt_iff_tendsto_infEDist (mem_univ x) hS

end Clause_b

section Truncation

variable {F : Type*} [NormedAddCommGroup F]

/-- The book's `min(d(u, C), η)` of 5.42(c): a bounded, real-valued function
of the set, which the truncation makes meaningful even when `C = ∅` and the
untruncated distance is `∞`. -/
noncomputable def truncInfDist (η : ℝ) (u : F) (C : Set F) : ℝ :=
  (min (infEDist u C) (ENNReal.ofReal η)).toReal

theorem truncInfDist_ne_top (η : ℝ) (u : F) (C : Set F) :
    min (infEDist u C) (ENNReal.ofReal η) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)

theorem truncInfDist_lt {η : ℝ} {u : F} {C : Set F} {r : ℝ}
    (h : infEDist u C < ENNReal.ofReal r) : truncInfDist η u C < r :=
  (ENNReal.lt_ofReal_iff_toReal_lt (truncInfDist_ne_top η u C)).1
    (lt_of_le_of_lt (min_le_left _ _) h)

theorem infEDist_lt_of_truncInfDist_lt {η : ℝ} {u : F} {C : Set F} {r : ℝ}
    (h : truncInfDist η u C < r) (hr : r ≤ η) :
    infEDist u C < ENNReal.ofReal r := by
  have hmin : min (infEDist u C) (ENNReal.ofReal η) < ENNReal.ofReal r :=
    (ENNReal.lt_ofReal_iff_toReal_lt (truncInfDist_ne_top η u C)).2 h
  rcases min_cases (infEDist u C) (ENNReal.ofReal η) with ⟨heq, -⟩ | ⟨heq, -⟩
  · rwa [heq] at hmin
  · rw [heq] at hmin
    exact absurd (hmin.trans_le (ENNReal.ofReal_le_ofReal hr)) (lt_irrefl _)

end Truncation

section Clause_c

variable {F : Type*} [NormedAddCommGroup F]

/-- One `ε`-inclusion bounds one truncated distance by the other.

The radius `‖u‖ + η + 1` is chosen once and works for every `x`: a point of
`B` nearly realizing `d(u, B)` lies inside that ball as soon as `d(u, B)` is
below the truncation level `η`, and if it is not, the bound is trivial because
the left side never exceeds `η`. -/
theorem min_infEDist_le_of_inter_closedBall_subset {η δ : ℝ} (hη : 0 < η)
    (hδ : 0 < δ) {u : F} {A B : Set F}
    (hAB : B ∩ closedBall 0 (‖u‖ + η + 1) ⊆ thickening (δ / 4) A) :
    min (infEDist u A) (ENNReal.ofReal η) ≤
      min (infEDist u B) (ENNReal.ofReal η) + ENNReal.ofReal (δ / 2) := by
  rcases le_or_gt (ENNReal.ofReal η) (infEDist u B) with hHB | hHB
  · exact le_trans (min_le_right _ _) (le_add_right (le_min hHB le_rfl))
  have hδ' : (0 : ℝ) < min 1 (δ / 4) := lt_min one_pos (by linarith)
  have hδ'le : min 1 (δ / 4) ≤ δ / 4 := min_le_right _ _
  have hδ'one : min 1 (δ / 4) ≤ 1 := min_le_left _ _
  obtain ⟨w, hwB, hw⟩ : ∃ w ∈ B,
      edist u w < infEDist u B + ENNReal.ofReal (min 1 (δ / 4)) :=
    Metric.infEDist_lt_iff.1
      (ENNReal.lt_add_right (ne_top_of_lt hHB) (ENNReal.ofReal_pos.2 hδ').ne')
  have hwball : w ∈ closedBall (0 : F) (‖u‖ + η + 1) := by
    have h1 : edist u w < ENNReal.ofReal (η + min 1 (δ / 4)) := by
      refine hw.trans_le ?_
      rw [ENNReal.ofReal_add hη.le hδ'.le]
      exact add_le_add hHB.le le_rfl
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith)] at h1
    refine mem_closedBall_zero_iff.2 ?_
    have h2 : ‖w‖ - ‖u‖ ≤ dist u w := by
      rw [dist_comm, dist_eq_norm]
      simpa using norm_sub_norm_le w u
    linarith
  obtain ⟨v, hvA, hwv⟩ := mem_thickening_iff.1 (hAB ⟨hwB, hwball⟩)
  refine le_trans (min_le_left _ _) ?_
  rw [min_eq_left hHB.le]
  refine le_trans ((Metric.infEDist_le_edist_of_mem hvA).trans
    (edist_triangle u w v)) ?_
  calc edist u w + edist w v
      ≤ (infEDist u B + ENNReal.ofReal (min 1 (δ / 4))) +
          ENNReal.ofReal (δ / 4) := by
        refine add_le_add hw.le ?_
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal hwv.le
    _ ≤ infEDist u B + ENNReal.ofReal (δ / 2) := by
        rw [add_assoc, ← ENNReal.ofReal_add hδ'.le (by linarith)]
        exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal (by linarith))

end Clause_c

section UniformTruncated

variable {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E}

omit [PseudoMetricSpace E] in
/-- **Exercise 5.42(c)**, necessity: the `ε`-inclusions of Definition 5.41
make the truncated distance functions converge uniformly on `X`. -/
theorem tendstoUniformlyOn_truncInfDist_of_svConvergesUniformlyOn
    (h : SvConvergesUniformlyOn Sseq S X) (u : F) {η : ℝ} (hη : 0 < η) :
    TendstoUniformlyOn (fun n x ↦ truncInfDist η u (Sseq n x))
      (fun x ↦ truncInfDist η u (S x)) atTop X := by
  refine Metric.tendstoUniformlyOn_iff.2 fun δ hδ ↦ ?_
  filter_upwards [h (δ / 4) (by linarith) (‖u‖ + η + 1) (by positivity)]
    with n hn x hx
  have hne1 := truncInfDist_ne_top η u (Sseq n x)
  have hne2 := truncInfDist_ne_top η u (S x)
  have hr1 : truncInfDist η u (Sseq n x) ≤ truncInfDist η u (S x) + δ / 2 := by
    have hle := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hne2, ENNReal.ofReal_ne_top⟩)
      (min_infEDist_le_of_inter_closedBall_subset hη hδ (hn x hx).2)
    rwa [ENNReal.toReal_add hne2 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at hle
  have hr2 : truncInfDist η u (S x) ≤ truncInfDist η u (Sseq n x) + δ / 2 := by
    have hle := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hne1, ENNReal.ofReal_ne_top⟩)
      (min_infEDist_le_of_inter_closedBall_subset hη hδ (hn x hx).1)
    rwa [ENNReal.toReal_add hne1 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at hle
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

variable [ProperSpace F]

omit [PseudoMetricSpace E] in
/-- **Exercise 5.42(c)**, sufficiency.  Both inclusions come from a single
finite cover of the *ball* `ρIB` -- not of any set built from `S` -- which is
what makes the estimate uniform over `x ∈ X`.  This is where the Guide's
appeal to the continuity of distance functions goes. -/
theorem svConvergesUniformlyOn_of_tendstoUniformlyOn_truncInfDist
    (h : ∀ u : F, ∀ η > 0, TendstoUniformlyOn
      (fun n x ↦ truncInfDist η u (Sseq n x))
      (fun x ↦ truncInfDist η u (S x)) atTop X) :
    SvConvergesUniformlyOn Sseq S X := by
  classical
  intro ε hε ρ _
  obtain ⟨t, -, htcover⟩ :=
    (isCompact_closedBall (0 : F) ρ).elim_nhds_subcover (fun u ↦ ball u (ε / 4))
      fun u _ ↦ ball_mem_nhds u (by linarith)
  have hev : ∀ᶠ n in atTop, ∀ u ∈ t, ∀ x ∈ X,
      dist (truncInfDist ε u (S x)) (truncInfDist ε u (Sseq n x)) < ε / 4 :=
    (eventually_all_finset t).2 fun u _ ↦
      Metric.tendstoUniformlyOn_iff.1 (h u ε hε) (ε / 4) (by linarith)
  filter_upwards [hev] with n hn x hx
  have hnear : ∀ (u : F) (D : Set F) (z : F), z ∈ D → dist z u < ε / 4 →
      truncInfDist ε u D < ε / 4 := by
    intro u D z hz hzu
    refine truncInfDist_lt (lt_of_le_of_lt (Metric.infEDist_le_edist_of_mem hz) ?_)
    rw [edist_dist]
    refine (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ?_
    rwa [dist_comm]
  constructor
  · intro v hv
    obtain ⟨u, hu, hvu⟩ := mem_iUnion₂.1 (htcover hv.2)
    have h1 : truncInfDist ε u (Sseq n x) < ε / 4 :=
      hnear u _ v hv.1 (mem_ball.1 hvu)
    have h2 : truncInfDist ε u (S x) < ε / 2 := by
      have hd := hn u hu x hx
      rw [Real.dist_eq, abs_lt] at hd
      linarith
    obtain ⟨w, hwS, huw⟩ := Metric.infEDist_lt_iff.1
      (infEDist_lt_of_truncInfDist_lt h2 (by linarith))
    refine mem_thickening_iff.2 ⟨w, hwS, ?_⟩
    have h3 : dist u w < ε / 2 := by
      rw [edist_dist] at huw
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 huw
    have h4 : dist v u < ε / 4 := mem_ball.1 hvu
    have := dist_triangle v u w
    linarith
  · intro w hw
    obtain ⟨u, hu, hwu⟩ := mem_iUnion₂.1 (htcover hw.2)
    have h1 : truncInfDist ε u (S x) < ε / 4 :=
      hnear u _ w hw.1 (mem_ball.1 hwu)
    have h2 : truncInfDist ε u (Sseq n x) < ε / 2 := by
      have hd := hn u hu x hx
      rw [Real.dist_eq, abs_lt] at hd
      linarith
    obtain ⟨v, hvS, huv⟩ := Metric.infEDist_lt_iff.1
      (infEDist_lt_of_truncInfDist_lt h2 (by linarith))
    refine mem_thickening_iff.2 ⟨v, hvS, ?_⟩
    have h3 : dist u v < ε / 2 := by
      rw [edist_dist] at huv
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 huv
    have h4 : dist w u < ε / 4 := mem_ball.1 hwu
    have := dist_triangle w u v
    linarith

omit [PseudoMetricSpace E] in
/-- **Exercise 5.42(c)**: uniform convergence on `X` is uniform convergence on
`X` of the truncated distance functions `min(d(u, ·), η)`, for every `u` and
every truncation level `η > 0`. -/
theorem svConvergesUniformlyOn_iff_tendstoUniformlyOn_truncInfDist :
    SvConvergesUniformlyOn Sseq S X ↔
      ∀ u : F, ∀ η > 0, TendstoUniformlyOn
        (fun n x ↦ truncInfDist η u (Sseq n x))
        (fun x ↦ truncInfDist η u (S x)) atTop X :=
  ⟨fun h u _ hη ↦ tendstoUniformlyOn_truncInfDist_of_svConvergesUniformlyOn h u hη,
    svConvergesUniformlyOn_of_tendstoUniformlyOn_truncInfDist⟩

end UniformTruncated

end RW
