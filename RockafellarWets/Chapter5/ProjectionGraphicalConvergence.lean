/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Graphical Convergence of Projection Mappings

Example 5.35: for closed sets, `P_{Cν} →g P_C` exactly when `Cν → C`.

The converse half is the cheap one and is proved first: a point of a set is
its own nearest point, so `(x, x) ∈ gph P_C` whenever `x ∈ C`, and both
set-limit inclusions for `Cν` are read straight off the corresponding
inclusions for the graphs.  It needs no closedness, no nonemptiness and no
strict convexity.

The forward half splits.  Its outer inclusion is a limit of the competitor
inequality `|wν - xν| ≤ |z - xν|`, the competitors `zν ∈ Cν` converging to a
given `z ∈ C` being supplied by the selection lemma for inner limits.  Its
inner inclusion is the book's argument through the point
`xε = x + ε(w - x)`, at which the projection collapses to the single point
`w`; the nearby projections are then bounded, and every cluster point of them
is a projection onto `C` at `xε`, hence equal to `w`.

That collapse is where the book's Euclidean `IRⁿ` is genuinely used.  In a
general finite-dimensional normed space it is false: with the sup norm on
`IR²` and `C = {1} × [0, 1]`, every point of `C` is nearest to the origin and
stays nearest all the way in.  What the argument needs, and what is assumed
here, is that the norm be strictly convex -- exactly the hypothesis Chapter 4
carries for the convex clause of 4.9, and automatic in the book's setting.

The book's Detail dismisses the case `C = ∅` and then says "we may as well
assume `Cν ≠ ∅` for all `ν`".  Neither step is taken here: the nonemptiness
that the inner half needs is produced from a point of `C` at the moment it is
needed, so the theorem is proved for arbitrary closed `Cν` and arbitrary `C`
in one piece.
-/

import RockafellarWets.Chapter4.ProjectionConvergence
import RockafellarWets.Chapter5.GraphicalLimitFormulas
import RockafellarWets.Chapter5.ProjectionMappings

open Bornology Filter Metric Set Topology

namespace RW

section Bridge

variable {E : Type*} [NormedAddCommGroup E]

/-- Chapter 5's `projMapping` and Chapter 4's `nearestPoints` are the same
mapping, written with a competitor condition and with a distance. -/
theorem projMapping_eq_nearestPoints (C : Set E) :
    projMapping C = nearestPoints C := by
  funext x
  ext w
  simp only [mem_projMapping, mem_nearestPoints]
  constructor
  · rintro ⟨hwC, hmin⟩
    refine ⟨hwC, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hwC)⟩
    refine (Metric.le_infDist ⟨w, hwC⟩).2 fun z hz ↦ ?_
    simpa only [dist_eq_norm, norm_sub_rev] using hmin z hz
  · rintro ⟨hwC, hw⟩
    refine ⟨hwC, fun z hz ↦ ?_⟩
    rw [norm_sub_rev w x, norm_sub_rev z x, ← dist_eq_norm, ← dist_eq_norm, hw]
    exact Metric.infDist_le_dist_of_mem hz

/-- The distance form of membership in `P_C(x)`. -/
theorem mem_projMapping_iff_dist {C : Set E} {x w : E} :
    w ∈ projMapping C x ↔ w ∈ C ∧ dist x w = Metric.infDist x C := by
  rw [projMapping_eq_nearestPoints]
  exact mem_nearestPoints

/-- A point of a set is its own nearest point. -/
theorem mem_projMapping_self {C : Set E} {x : E} (hx : x ∈ C) :
    x ∈ projMapping C x :=
  ⟨hx, fun _ _ ↦ by simp⟩

end Bridge

section SegmentUniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Moving from `x` toward a nearest point `w` keeps `w` nearest, and in a
strictly convex space makes it the *only* nearest point.

This is the fact that drives the inner half of 5.35, and it is where the
Euclidean geometry of the book's `IRⁿ` is used: strict convexity of the norm
is genuinely needed, not a convenience. -/
theorem projMapping_segment [StrictConvexSpace ℝ E] {C : Set E} {x w : E}
    (hw : w ∈ projMapping C x) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    projMapping C (x + ε • (w - x)) = {w} := by
  obtain ⟨hwC, hwmin⟩ := hw
  have hxy : x - (x + ε • (w - x)) = ε • (x - w) := by module
  have hyw : (x + ε • (w - x)) - w = (1 - ε) • (x - w) := by module
  have hxynorm : ‖x - (x + ε • (w - x))‖ = ε * ‖w - x‖ := by
    rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos hε, norm_sub_rev x w]
  have hywnorm : ‖(x + ε • (w - x)) - w‖ = (1 - ε) * ‖w - x‖ := by
    rw [hyw, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < 1 - ε), norm_sub_rev x w]
  have hlower : ∀ z ∈ C, (1 - ε) * ‖w - x‖ ≤ ‖z - (x + ε • (w - x))‖ := by
    intro z hz
    have h1 := norm_sub_norm_le (z - x) ((x + ε • (w - x)) - x)
    have h2 : (z - x) - ((x + ε • (w - x)) - x) = z - (x + ε • (w - x)) := by module
    rw [h2] at h1
    have h3 : ‖(x + ε • (w - x)) - x‖ = ε * ‖w - x‖ := by
      rw [norm_sub_rev]; exact hxynorm
    rw [h3] at h1
    have h4 : ‖w - x‖ ≤ ‖z - x‖ := hwmin z hz
    nlinarith [h1, h4]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hwC, fun z hz ↦ ?_⟩, ?_⟩
  · rw [norm_sub_rev w (x + ε • (w - x)), hywnorm]
    exact hlower z hz
  rintro z ⟨hzC, hzmin⟩
  have hznorm : ‖z - (x + ε • (w - x))‖ = (1 - ε) * ‖w - x‖ := by
    refine le_antisymm ?_ (hlower z hzC)
    have hle := hzmin w hwC
    rwa [norm_sub_rev w (x + ε • (w - x)), hywnorm] at hle
  rcases eq_or_lt_of_le (norm_nonneg (w - x)) with hr0 | hrpos
  · have hwx : w = x := by
      have h : ‖w - x‖ = 0 := hr0.symm
      rwa [norm_eq_zero, sub_eq_zero] at h
    have hz0 : ‖z - (x + ε • (w - x))‖ = 0 := by rw [hznorm, ← hr0]; ring
    rw [norm_eq_zero, sub_eq_zero] at hz0
    rw [hz0, hwx]
    simp
  have hxzr : ‖x - z‖ = ‖w - x‖ := by
    refine le_antisymm ?_ ?_
    · have heq : x - z = (x - (x + ε • (w - x))) + ((x + ε • (w - x)) - z) := by module
      rw [heq]
      calc ‖(x - (x + ε • (w - x))) + ((x + ε • (w - x)) - z)‖
          ≤ ‖x - (x + ε • (w - x))‖ + ‖(x + ε • (w - x)) - z‖ := norm_add_le _ _
        _ = ε * ‖w - x‖ + (1 - ε) * ‖w - x‖ := by
            rw [hxynorm, norm_sub_rev (x + ε • (w - x)) z, hznorm]
        _ = ‖w - x‖ := by ring
    · rw [norm_sub_rev x z]
      exact hwmin z hzC
  have hsum : ‖(x - (x + ε • (w - x))) + ((x + ε • (w - x)) - z)‖ =
      ‖x - (x + ε • (w - x))‖ + ‖(x + ε • (w - x)) - z‖ := by
    have heq : (x - (x + ε • (w - x))) + ((x + ε • (w - x)) - z) = x - z := by module
    rw [heq, hxzr, hxynorm, norm_sub_rev (x + ε • (w - x)) z, hznorm]
    ring
  have hsmul := (sameRay_iff_norm_add.2 hsum).norm_smul_eq
  rw [hxynorm, norm_sub_rev (x + ε • (w - x)) z, hznorm] at hsmul
  have hne : (ε * ‖w - x‖) ≠ 0 := ne_of_gt (mul_pos hε hrpos)
  have hkey : (ε * ‖w - x‖) • ((x + ε • (w - x)) - z) =
      (ε * ‖w - x‖) • ((1 - ε) • (x - w)) := by
    rw [hsmul, hxy]
    module
  have hyz : (x + ε • (w - x)) - z = (1 - ε) • (x - w) :=
    smul_right_injective E hne hkey
  have hfin : (x + ε • (w - x)) - z = (x + ε • (w - x)) - w := by rw [hyz, hyw]
  exact sub_right_injective hfin

end SegmentUniqueness

section OuterHalf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The outer half of **Example 5.35**: an outer limit of projections onto
converging sets is a projection onto the limit.  This needs no strict
convexity and no nonemptiness -- only the selection lemma for inner limits,
which supplies the competitors `zν ∈ Cν` converging to a given `z ∈ C`. -/
theorem outerSetLimit_svGraph_projMapping_subset {C : Set E} {Cseq : ℕ → Set E}
    (h : PKConverges Cseq C) :
    outerSetLimit (fun n ↦ svGraph (projMapping (Cseq n))) ⊆
      svGraph (projMapping C) := by
  rintro ⟨x, w⟩ hxw
  obtain ⟨φ, p, hφ, hp, hpxw⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hxw
  have hy : Tendsto (fun k ↦ (p k).1) atTop (nhds x) :=
    (continuous_fst.tendsto _).comp hpxw
  have hv : Tendsto (fun k ↦ (p k).2) atTop (nhds w) :=
    (continuous_snd.tendsto _).comp hpxw
  refine ⟨?_, fun z hz ↦ ?_⟩
  · rw [← h.outer_eq]
    exact mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ, fun k ↦ (p k).2, hφ, fun k ↦ (hp k).1, hv⟩
  · obtain ⟨zs, hzs, hzsto⟩ :=
      mem_innerSetLimit_iff_exists_seq.1 (h.inner_eq.symm.subset hz)
    have hineq : ∀ᶠ k in atTop, ‖(p k).2 - (p k).1‖ ≤ ‖zs (φ k) - (p k).1‖ :=
      (hφ.tendsto_atTop.eventually hzs).mono fun k hk ↦ (hp k).2 _ hk
    exact le_of_tendsto_of_tendsto (hv.sub hy).norm
      ((hzsto.comp hφ.tendsto_atTop).sub hy).norm hineq

end OuterHalf

section InnerHalf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The step in the inner half of 5.35 where the argument has been moved along
the segment so that the limit projection is a single point.  The nearby
projections are then bounded and have no cluster point other than that
point. -/
private theorem mem_innerSetLimit_of_projMapping_eq_singleton
    {C : Set E} {Cseq : ℕ → Set E} {y w : E}
    (hCseqClosed : ∀ n, IsClosed (Cseq n)) (h : PKConverges Cseq C)
    (hproj : projMapping C y = {w}) :
    ((y, w) : E × E) ∈ innerSetLimit (fun n ↦ svGraph (projMapping (Cseq n))) := by
  have hwproj : w ∈ projMapping C y := by rw [hproj]; rfl
  have hwinner : w ∈ innerSetLimit Cseq := h.inner_eq.symm.subset hwproj.1
  have hhit : ∀ᶠ n in atTop, (Cseq n ∩ ball w 1).Nonempty :=
    (mem_innerSetLimit_iff_eventually_ball.1 hwinner) 1 zero_lt_one
  have hne : ∀ᶠ n in atTop, (Cseq n).Nonempty :=
    hhit.mono fun n hn ↦ ⟨hn.choose, hn.choose_spec.1⟩
  have hbound : ∀ᶠ n in atTop, Metric.infDist y (Cseq n) ≤ dist y w + 1 := by
    filter_upwards [hhit] with n hn
    obtain ⟨v, hvC, hvball⟩ := hn
    calc Metric.infDist y (Cseq n) ≤ dist y v := Metric.infDist_le_dist_of_mem hvC
      _ ≤ dist y w + dist w v := dist_triangle _ _ _
      _ ≤ dist y w + 1 := by
          have := mem_ball.1 hvball
          rw [dist_comm] at this
          linarith
  rw [mem_innerSetLimit_iff_eventually_ball]
  intro ε hε
  by_contra hnot
  rw [not_eventually] at hnot
  obtain ⟨φ, hφ, hbad⟩ :=
    extraction_of_frequently_atTop (hnot.and_eventually (hne.and hbound))
  have hpick : ∀ k, (projMapping (Cseq (φ k)) y).Nonempty := fun k ↦ by
    rw [projMapping_eq_nearestPoints]
    exact nearestPoints_nonempty (hCseqClosed _) (hbad k).2.1 y
  choose q hq using hpick
  have hqball : ∀ k, q k ∈ closedBall y (dist y w + 1) := fun k ↦ by
    rw [mem_closedBall, dist_comm]
    have hd := (mem_projMapping_iff_dist.1 (hq k)).2
    rw [hd]
    exact (hbad k).2.2
  obtain ⟨qbar, -, ψ, hψ, hqto⟩ :=
    (isCompact_closedBall y (dist y w + 1)).tendsto_subseq hqball
  have hqbar : qbar ∈ projMapping C y :=
    outerSetLimit_svGraph_projMapping_subset h
      (mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ, fun k ↦ (y, q (ψ k)), hφ.comp hψ, fun k ↦ hq (ψ k),
          tendsto_const_nhds.prodMk_nhds hqto⟩)
  rw [hproj, mem_singleton_iff] at hqbar
  have hfar : ∀ k, ε ≤ dist (q k) w := by
    intro k
    by_contra hlt
    push_neg at hlt
    refine (hbad k).1 ⟨(y, q k), hq k, ?_⟩
    rw [mem_ball, Prod.dist_eq]
    simpa using hlt
  have hlim : ε ≤ dist qbar w :=
    ge_of_tendsto (hqto.dist (tendsto_const_nhds (α := ℕ) (x := w)))
      (Eventually.of_forall fun k ↦ hfar (ψ k))
  rw [hqbar, dist_self] at hlim
  linarith

/-- The inner half of **Example 5.35**.  Strict convexity enters here, through
the segment lemma: moving the argument toward a nearest point makes that point
the unique nearest point, so the nearby projections have nowhere else to go. -/
theorem svGraph_projMapping_subset_innerSetLimit [StrictConvexSpace ℝ E]
    {C : Set E} {Cseq : ℕ → Set E} (hCseqClosed : ∀ n, IsClosed (Cseq n))
    (h : PKConverges Cseq C) :
    svGraph (projMapping C) ⊆
      innerSetLimit (fun n ↦ svGraph (projMapping (Cseq n))) := by
  rintro ⟨x, w⟩ hxw
  have hseg : ∀ k : ℕ,
      ((x + ((k : ℝ) + 2)⁻¹ • (w - x), w) : E × E) ∈
        innerSetLimit (fun n ↦ svGraph (projMapping (Cseq n))) := by
    intro k
    refine mem_innerSetLimit_of_projMapping_eq_singleton hCseqClosed h ?_
    refine projMapping_segment hxw (by positivity) ?_
    rw [inv_lt_one₀ (by positivity)]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hto : Tendsto (fun k : ℕ ↦ ((x + ((k : ℝ) + 2)⁻¹ • (w - x), w) : E × E)) atTop
      (nhds ((x, w) : E × E)) := by
    refine Tendsto.prodMk_nhds ?_ (tendsto_const_nhds (α := ℕ) (x := w))
    have hzero : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2)⁻¹) atTop (nhds (0 : ℝ)) := by
      refine tendsto_inv_atTop_zero.comp ?_
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have := (tendsto_const_nhds (α := ℕ) (x := x)).add
      (hzero.smul (tendsto_const_nhds (α := ℕ) (x := w - x)))
    simpa using this
  exact (isClosed_innerSetLimit _).mem_of_tendsto hto (Eventually.of_forall hseg)

end InnerHalf

section Converse

variable {E : Type*} [NormedAddCommGroup E]

/-- The converse half of **Example 5.35**: graphical convergence of the
projections forces the sets to converge.  It uses only that a point of a set
is its own nearest point, so it needs neither closedness, nor nonemptiness,
nor strict convexity. -/
theorem pkConverges_of_graphicalConverges_projMapping {C : Set E} {Cseq : ℕ → Set E}
    (hg : GraphicalConverges (fun n ↦ projMapping (Cseq n)) (projMapping C)) :
    PKConverges Cseq C := by
  have houter : outerSetLimit Cseq ⊆ C := by
    intro w hw
    obtain ⟨φ, v, hφ, hvC, hvw⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hw
    have hmem : ((w, w) : E × E) ∈
        outerSetLimit (fun n ↦ svGraph (projMapping (Cseq n))) :=
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ, fun k ↦ ((v k, v k) : E × E), hφ,
          fun k ↦ mem_projMapping_self (hvC k), hvw.prodMk_nhds hvw⟩
    exact ((hg.outer_eq ▸ hmem : ((w, w) : E × E) ∈ svGraph (projMapping C))).1
  have hinner : C ⊆ innerSetLimit Cseq := by
    intro z hz
    rw [mem_innerSetLimit_iff_eventually_ball]
    intro ε hε
    have hmem : ((z, z) : E × E) ∈
        innerSetLimit (fun n ↦ svGraph (projMapping (Cseq n))) :=
      hg.inner_eq.symm.subset (mem_projMapping_self hz)
    filter_upwards [(mem_innerSetLimit_iff_eventually_ball.1 hmem) ε hε] with n hn
    obtain ⟨p, hp, hpball⟩ := hn
    refine ⟨p.2, hp.1, ?_⟩
    rw [mem_ball] at hpball ⊢
    exact lt_of_le_of_lt (by rw [Prod.dist_eq] at hpball ⊢; exact le_max_right _ _) hpball
  exact ⟨Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit Cseq).trans houter) hinner,
    Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit Cseq))⟩

end Converse

section Example535

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Example 5.35 (graphical convergence of projection mappings).**  For
closed sets, the projections converge graphically exactly when the sets
converge.

The book states this in Euclidean `IRⁿ`; here the norm is only assumed
strictly convex, which is what the segment argument of the inner half
actually needs.  Neither closedness of `C` nor nonemptiness of anything is
assumed: closedness of the limit is automatic, and nonemptiness of the `Cν`
is produced where it is needed from a point of `C`. -/
theorem graphicalConverges_projMapping_iff [StrictConvexSpace ℝ E]
    {C : Set E} {Cseq : ℕ → Set E} (hCseqClosed : ∀ n, IsClosed (Cseq n)) :
    GraphicalConverges (fun n ↦ projMapping (Cseq n)) (projMapping C) ↔
      PKConverges Cseq C := by
  refine ⟨pkConverges_of_graphicalConverges_projMapping, fun h ↦ ?_⟩
  have houter := outerSetLimit_svGraph_projMapping_subset h
  have hinner := svGraph_projMapping_subset_innerSetLimit hCseqClosed h
  exact ⟨Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
    Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

end Example535

end RW
