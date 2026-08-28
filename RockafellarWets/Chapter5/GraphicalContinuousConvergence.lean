/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Graphical versus Continuous Convergence

Theorem 5.44 and Corollary 5.45.  Continuous convergence at `x̄` relative to
`X` is graphical convergence there plus asymptotic equicontinuity.

Both directions run on the `ε`-`ρ` inclusions.  Continuous convergence at `x̄`
says, through 4.10, that `Sν(y)` and `S(x̄)` approximate each other on every
bounded ball, uniformly for `y ∈ X` near `x̄`; equicontinuity says the same of
`Sν(y)` and `Sν(x̄)`.  Passing between the two is a matter of routing through
the third set: two `ε/2`-inclusions compose into an `ε`-inclusion, provided
the middle radius is enlarged by `ε/2` to catch the intermediate point.  That
one step is isolated as `inter_closedBall_subset_thickening_trans` and is used
four times here, twice for each half of equicontinuity.

The book instead argues the equicontinuity half by contradiction, extracting a
cluster point of escaping values; the composition above replaces that, and it
is also what 5.43 and 5.46 need.

The converse direction is the book's: asymptotic equi-outer semicontinuity and
relative graphical convergence give pointwise convergence at `x̄` by 5.40, so a
value `ū ∈ S(x̄)` is the limit of values `uν ∈ Sν(x̄)`; those are bounded, so
asymptotic equi-inner semicontinuity moves them into `Sν(xν) + εIB` for every
approaching sequence `xν → x̄` in `X`.

Corollary 5.45 is the single-valued specialization, where asymptotic
equicontinuity of the singleton mappings reduces -- through 5.39 -- to
eventual local boundedness, graphical convergence supplying the rest.
-/

import RockafellarWets.Chapter4.SetLimitExamples
import RockafellarWets.Chapter5.ContinuousUniformConvergence
import RockafellarWets.Chapter5.GraphicalPointwise

open Bornology Filter Metric Set Topology

namespace RW

section Composition

variable {F : Type*} [NormedAddCommGroup F]

/-- Two `ε`-inclusions compose.  The point produced by the first inclusion sits
within `ε₁` of a ball of radius `ρ`, hence in the ball of radius `ρ + ε₁`, so
the second inclusion applies to it as soon as its radius is that large. -/
theorem inter_closedBall_subset_thickening_trans {A B C : Set F} {ρ ρ' ε₁ ε₂ : ℝ}
    (hρ' : ρ + ε₁ ≤ ρ')
    (h₁ : A ∩ closedBall 0 ρ ⊆ thickening ε₁ B)
    (h₂ : B ∩ closedBall 0 ρ' ⊆ thickening ε₂ C) :
    A ∩ closedBall 0 ρ ⊆ thickening (ε₁ + ε₂) C := by
  intro w hw
  obtain ⟨s, hsB, hws⟩ := mem_thickening_iff.1 (h₁ hw)
  have hsnorm : s ∈ closedBall (0 : F) ρ' := by
    rw [mem_closedBall_zero_iff]
    have h1 : ‖s‖ - ‖w‖ ≤ dist s w := by
      simpa only [dist_eq_norm] using norm_sub_norm_le s w
    have h2 : ‖w‖ ≤ ρ := mem_closedBall_zero_iff.1 hw.2
    rw [dist_comm] at h1
    linarith
  obtain ⟨t, htC, hst⟩ := mem_thickening_iff.1 (h₂ ⟨hsB, hsnorm⟩)
  refine mem_thickening_iff.2 ⟨t, htC, lt_of_le_of_lt (dist_triangle w s t) ?_⟩
  linarith

/-- Shrinking the radius of an `ε`-inclusion. -/
theorem inter_closedBall_subset_of_le {A T : Set F} {ρ ρ' : ℝ} (h : ρ ≤ ρ')
    (hsub : A ∩ closedBall 0 ρ' ⊆ T) : A ∩ closedBall 0 ρ ⊆ T :=
  fun _ hw ↦ hsub ⟨hw.1, closedBall_subset_closedBall h hw.2⟩

end Composition

section Elementary

variable {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E} {x : E}

/-- The constant sequence at `x̄ ∈ X` is admissible, so continuous convergence
relative to `X` at `x̄` entails pointwise convergence at `x̄`. -/
theorem SvConvergesContinuouslyWithinAt.pointwiseConvergesAt (hx : x ∈ X)
    (h : SvConvergesContinuouslyWithinAt Sseq S X x) :
    PointwiseConvergesAt Sseq S x :=
  h (fun _ ↦ x) (fun _ ↦ hx) tendsto_const_nhds

/-- A continuous limit is closed-valued at the points where the convergence
takes place, being an outer set limit there. -/
theorem SvConvergesContinuouslyWithinAt.isClosed_apply (hx : x ∈ X)
    (h : SvConvergesContinuouslyWithinAt Sseq S X x) : IsClosed (S x) := by
  rw [← (h.pointwiseConvergesAt hx).2]
  exact isClosed_outerSetLimit _

/-- **Theorem 5.44**, the graphical half of (a) ⟹ (b).  Every admissible
sequence has `Sν(xν) → S(x̄)`, which is both inclusions of 5(7) at once. -/
theorem SvConvergesContinuouslyWithinAt.graphicalConvergesWithinAt (hx : x ∈ X)
    (h : SvConvergesContinuouslyWithinAt Sseq S X x) :
    GraphicalConvergesWithinAt Sseq S X x :=
  ⟨iUnion₂_subset fun y hy ↦ (h y hy.1 hy.2).2.subset,
    ((h.pointwiseConvergesAt hx).1.ge).trans
      (pointwiseInnerLimit_subset_graphicalInnerLimitWithin Sseq hx)⟩

end Elementary

section Theorem544

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E} {x : E}

/-- **Theorem 5.44**, the equicontinuity half of (a) ⟹ (b).

Both clauses are the same composition, run in opposite directions: the
inclusion between `Sν(y)` and `Sν(x̄)` is obtained by passing through `S(x̄)`,
which continuous convergence approximates from both sides at once. -/
theorem SvConvergesContinuouslyWithinAt.svAsymptoticallyEquicontinuousWithinAt
    (hx : x ∈ X) (h : SvConvergesContinuouslyWithinAt Sseq S X x) :
    SvAsymptoticallyEquicontinuousWithinAt Sseq X x := by
  have hub := (svConvergesContinuouslyWithinAt_iff hx (h.isClosed_apply hx)).1 h
  constructor
  · intro ε hε ρ hρ
    obtain ⟨V₁, hV₁, hN₁⟩ := hub (ε / 2) (by linarith) ρ hρ
    obtain ⟨V₂, hV₂, hN₂⟩ := hub (ε / 2) (by linarith) (ρ + ε) (by linarith)
    refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
    filter_upwards [hN₁, hN₂] with n hn₁ hn₂ y hy
    have hstep := inter_closedBall_subset_thickening_trans
      (by linarith : ρ + ε / 2 ≤ ρ + ε)
      (hn₁ x ⟨mem_of_mem_nhds hV₁, hx⟩).1 (hn₂ y ⟨hy.1.2, hy.2⟩).2
    rwa [add_halves] at hstep
  · intro ε hε ρ hρ
    obtain ⟨V₁, hV₁, hN₁⟩ := hub (ε / 2) (by linarith) ρ hρ
    obtain ⟨V₂, hV₂, hN₂⟩ := hub (ε / 2) (by linarith) (ρ + ε) (by linarith)
    refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
    filter_upwards [hN₁, hN₂] with n hn₁ hn₂ y hy
    have hstep := inter_closedBall_subset_thickening_trans
      (by linarith : ρ + ε / 2 ≤ ρ + ε)
      (hn₁ y ⟨hy.1.1, hy.2⟩).1 (hn₂ x ⟨mem_of_mem_nhds hV₂, hx⟩).2
    rwa [add_halves] at hstep

end Theorem544

section Converse544

variable {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E} {x : E}

/-- **Theorem 5.44**, (b) ⟹ (a).

By 5.40 the two hypotheses give pointwise convergence at `x̄`, so a value
`ū ∈ S(x̄)` is a limit of values `uν ∈ Sν(x̄)`.  Those stay in a fixed ball, so
asymptotic equi-inner semicontinuity carries them into `Sν(xν) + (ε/2)IB` for
any approaching sequence in `X`, and `uν → ū` closes the remaining `ε/2`. -/
theorem svConvergesContinuouslyWithinAt_of_graphicalConvergesWithinAt (hx : x ∈ X)
    (hg : GraphicalConvergesWithinAt Sseq S X x)
    (he : SvAsymptoticallyEquicontinuousWithinAt Sseq X x) :
    SvConvergesContinuouslyWithinAt Sseq S X x := by
  intro y hyX hy
  have houter : outerSetLimit (fun n ↦ Sseq n (y n)) ⊆ S x := fun u hu ↦
    hg.1 (mem_graphicalOuterLimitWithin_iff.2 ⟨y, ⟨hyX, hy⟩, hu⟩)
  have hpw : PointwiseConvergesAt Sseq S x :=
    PointwiseConvergesAt.of_graphicalConvergesWithinAt hx he.2 hg
  have hinner : S x ⊆ innerSetLimit (fun n ↦ Sseq n (y n)) := by
    intro ubar hubar
    obtain ⟨us, hus, husto⟩ :=
      mem_innerSetLimit_iff_exists_seq.1 ((pointwiseConvergesAt_iff.1 hpw).2 hubar)
    refine mem_innerSetLimit_iff_eventually_ball.2 fun ε hε ↦ ?_
    obtain ⟨V, hV, hN⟩ := he.1 (ε / 2) (by linarith) (‖ubar‖ + 1) (by positivity)
    filter_upwards [hus, hN, hy.eventually_mem hV,
      husto.eventually_mem (ball_mem_nhds ubar one_pos),
      husto.eventually_mem (ball_mem_nhds ubar (half_pos hε))]
      with n husn hNn hyn hclose1 hclose
    have hnorm : us n ∈ closedBall (0 : F) (‖ubar‖ + 1) := by
      rw [mem_closedBall_zero_iff]
      have h1 : ‖us n‖ - ‖ubar‖ ≤ dist (us n) ubar := by
        simpa only [dist_eq_norm] using norm_sub_norm_le (us n) ubar
      have h2 : dist (us n) ubar < 1 := mem_ball.1 hclose1
      linarith
    obtain ⟨w, hwS, hwdist⟩ :=
      mem_thickening_iff.1 (hNn (y n) ⟨hyn, hyX n⟩ ⟨husn, hnorm⟩)
    refine ⟨w, hwS, ?_⟩
    rw [mem_ball, dist_comm]
    have h3 : dist ubar w ≤ dist ubar (us n) + dist (us n) w := dist_triangle _ _ _
    have h4 : dist ubar (us n) < ε / 2 := by
      rw [dist_comm]
      exact mem_ball.1 hclose
    linarith
  exact ⟨Subset.antisymm ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
    Subset.antisymm houter (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

end Converse544

section Statement544

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E} {x : E}

/-- **Theorem 5.44**: at a point `x̄ ∈ X`, continuous convergence relative to
`X` is exactly relative graphical convergence together with asymptotic
equicontinuity. -/
theorem svConvergesContinuouslyWithinAt_iff_graphicalConvergesWithinAt (hx : x ∈ X) :
    SvConvergesContinuouslyWithinAt Sseq S X x ↔
      GraphicalConvergesWithinAt Sseq S X x ∧
        SvAsymptoticallyEquicontinuousWithinAt Sseq X x :=
  ⟨fun h ↦ ⟨h.graphicalConvergesWithinAt hx,
      h.svAsymptoticallyEquicontinuousWithinAt hx⟩,
    fun h ↦ svConvergesContinuouslyWithinAt_of_graphicalConvergesWithinAt hx h.1 h.2⟩

/-- **Theorem 5.44** in the absolute case. -/
theorem svConvergesContinuouslyAt_iff_graphicalConvergesAt :
    SvConvergesContinuouslyAt Sseq S x ↔
      GraphicalConvergesAt Sseq S x ∧ SvAsymptoticallyEquicontinuousAt Sseq x := by
  rw [← graphicalConvergesWithinAt_univ_iff]
  exact svConvergesContinuouslyWithinAt_iff_graphicalConvergesWithinAt (mem_univ x)

end Statement544

section Corollary545

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {Fs : ℕ → E → F} {f : E → F} {x : E}

/-- **Corollary 5.45**, the boundedness half of (a) ⟹ (b).

Suppose the values escaped every ball on every neighborhood.  Then for each
`k` one could pick a late index and a point within `1/(k+1)` of `x̄` at which
the value exceeds the *fixed* bound `‖F(x̄)‖ + 1`.  Redistributing those points
into one sequence approaching `x̄` -- parking the unused indices at `x̄` --
contradicts `Fν(xν) → F(x̄)`, whose values are eventually within `1` of `F(x̄)`.
Keeping the bound fixed is what makes the redistribution work: the bad
property has to survive being reattached to a different `k` with the same
index. -/
theorem SvConvergesContinuouslyAt.svEventuallyLocallyBoundedAt
    (h : SvConvergesContinuouslyAt (fun n ↦ svSingleton (Fs n)) (svSingleton f) x) :
    SvEventuallyLocallyBoundedAt Fs x := by
  classical
  by_contra hcon
  rw [svEventuallyLocallyBoundedAt_iff] at hcon
  push_neg at hcon
  have hpick : ∀ k : ℕ, ∃ (n : ℕ) (y : E), k ≤ n ∧
      dist y x < ((k : ℝ) + 1)⁻¹ ∧ ‖f x‖ + 1 < ‖Fs n y‖ := by
    intro k
    have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    obtain ⟨n, hn, y, hyV, hybad⟩ := frequently_atTop.1
      (hcon (ball x ((k : ℝ) + 1)⁻¹) (ball_mem_nhds x hδ) (‖f x‖ + 1)) k
    exact ⟨n, y, hn, mem_ball.1 hyV, hybad⟩
  choose ms ys hms hys hbadk using hpick
  have hysTo : Tendsto ys atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ (hys k).le) ?_
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  set z : ℕ → E := Function.extend ms ys (fun _ ↦ x) with hz
  -- The values along the redistributed sequence are eventually near `F(x̄)`.
  have hnear : ∀ᶠ n in atTop, Fs n (z n) ∈ ball (f x) 1 := by
    have hmem : f x ∈ innerSetLimit fun n ↦ svSingleton (Fs n) (z n) := by
      rw [(h z (fun _ ↦ mem_univ _) (tendsto_extend_index hysTo)).1]
      exact rfl
    refine (hmem _ (ball_mem_nhds (f x) one_pos)).mono fun n hn ↦ ?_
    obtain ⟨w, hw, hwball⟩ := hn
    rwa [mem_svSingleton.1 hw] at hwball
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnear
  have hex : ∃ k, ms k = ms N := ⟨N, rfl⟩
  have hzval : z (ms N) = ys (Classical.choose hex) := by
    rw [hz, Function.extend_def, dif_pos hex]
  have hbig := hbadk (Classical.choose hex)
  rw [Classical.choose_spec hex, ← hzval] at hbig
  have hsmall : dist (Fs (ms N) (z (ms N))) (f x) < 1 := mem_ball.1 (hN (ms N) (hms N))
  have htri : ‖Fs (ms N) (z (ms N))‖ - ‖f x‖ ≤ dist (Fs (ms N) (z (ms N))) (f x) := by
    simpa only [dist_eq_norm] using norm_sub_norm_le (Fs (ms N) (z (ms N))) (f x)
  linarith

variable [ProperSpace F]

/-- **Corollary 5.45**, (b) ⟹ (a).

Eventual local boundedness traps every sequence `Fν(xν)` with `xν → x̄` in a
fixed ball.  A subsequence staying `ε` away from `F(x̄)` would then have a
cluster point at that distance, and the cluster point lies in the graphical
outer limit, which single-valuedness of the limit pins to `F(x̄)` itself. -/
theorem svConvergesContinuouslyAt_svSingleton_of_graphicalConvergesAt
    (hg : GraphicalConvergesAt (fun n ↦ svSingleton (Fs n)) (svSingleton f) x)
    (hb : SvEventuallyLocallyBoundedAt Fs x) :
    SvConvergesContinuouslyAt (fun n ↦ svSingleton (Fs n)) (svSingleton f) x := by
  obtain ⟨V, hV, ρ, hρ⟩ := hb
  intro y _ hy
  refine pkConverges_singleton_iff.2 ?_
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push_neg at hcon
  obtain ⟨ε, hε, hbad⟩ := hcon
  have hbdd : ∀ᶠ n in atTop, Fs n (y n) ∈ closedBall (0 : F) ρ := by
    filter_upwards [hρ, hy.eventually_mem hV] with n hn hyn
    exact mem_closedBall_zero_iff.2 (hn (y n) hyn)
  have hK : IsCompact (closedBall (0 : F) ρ ∩ {v | ε ≤ dist v (f x)}) :=
    (isCompact_closedBall 0 ρ).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  obtain ⟨w, ⟨-, hwfar⟩, φ, hφ, hwto⟩ :=
    hK.tendsto_subseq' (((frequently_atTop.2 hbad).and_eventually hbdd).mono
      fun n hn ↦ ⟨hn.2, hn.1⟩)
  have hwmem : w ∈ graphicalOuterLimit (fun n ↦ svSingleton (Fs n)) x :=
    mem_graphicalOuterLimit_iff.2 ⟨φ, fun k ↦ y (φ k), fun k ↦ Fs (φ k) (y (φ k)),
      hφ, fun _ ↦ rfl, hy.comp hφ.tendsto_atTop, hwto⟩
  rw [mem_svSingleton.1 (hg.1 hwmem), mem_setOf_eq, dist_self] at hwfar
  linarith

/-- **Corollary 5.45**: for single-valued mappings, continuous convergence at
`x̄` is graphical convergence there together with eventual local boundedness. -/
theorem svConvergesContinuouslyAt_svSingleton_iff :
    SvConvergesContinuouslyAt (fun n ↦ svSingleton (Fs n)) (svSingleton f) x ↔
      GraphicalConvergesAt (fun n ↦ svSingleton (Fs n)) (svSingleton f) x ∧
        SvEventuallyLocallyBoundedAt Fs x :=
  ⟨fun h ↦ ⟨graphicalConvergesWithinAt_univ_iff.1
      (h.graphicalConvergesWithinAt (mem_univ x)), h.svEventuallyLocallyBoundedAt⟩,
    fun h ↦ svConvergesContinuouslyAt_svSingleton_of_graphicalConvergesAt h.1 h.2⟩

end Corollary545

end RW
