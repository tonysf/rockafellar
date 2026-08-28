/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Total Continuity

Definition 5.28 and Proposition 5.29.

Total convergence, Definition 4.23, is restated along an arbitrary index
filter, and Proposition 4.24 is reproved there.  That proof is the Chapter 4
one word for word: it never touches the index, once the ordinary part of a
cosmic limit is available filter-natively.

Definition 5.28 is then total convergence along the neighborhood filter of
formula 5(1), and 5.29 is 4.24 read through the equality form of continuity.
The three automatic cases are proved separately.  The convex case is the only
one that needs real work; the sequential argument of 4.25(a) extracts a
diagonal subsequence, and the filter version replaces that by combining one
`∃ᶠ` with two `∀ᶠ`s.
-/

import Mathlib.Analysis.Convex.Basic
import RockafellarWets.Chapter4.TotalConvergence
import RockafellarWets.Chapter5.CosmicSemicontinuity
import RockafellarWets.Chapter5.LocalBoundedness

open Bornology Filter Metric Set Topology

namespace RW

section TotalConvergenceAlong

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Definition 4.23** along an arbitrary index filter: cosmic convergence
of the ordinary sets to the cosmic closure of a closed limit set. -/
def TotalConvergesAlong (l : Filter ι) (Cf : ι → Set E) (C : Set E) : Prop :=
  IsClosed C ∧
    PKConvergesAlong l (ordinaryCosmicFamily Cf)
      (closure (cosmicSet C ({0} : Set E)))

omit [FiniteDimensional ℝ E] in
/-- The Chapter 4 sequential notion is the `atTop` case. -/
theorem totalConvergesAlong_atTop (Cseq : ℕ → Set E) (C : Set E) :
    TotalConvergesAlong atTop Cseq C ↔ TotalConverges Cseq C := Iff.rfl

private theorem cosmicEmbed_mem_cosmicClosure_iff {C : Set E} {x : E} :
    cosmicEmbed x ∈ closure (cosmicSet C ({0} : Set E)) ↔ x ∈ closure C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  rw [closure_cosmicSet hzero, cosmicEmbed_mem_cosmicSet_iff]

private theorem cosmicDirection_mem_cosmicClosure_iff
    {C : Set E} {u : CosmicBoundary E} :
    cosmicDirection u ∈ closure (cosmicSet C ({0} : Set E)) ↔
      (u : E) ∈ horizonCone C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  rw [closure_cosmicSet hzero, mem_cosmicSet]
  constructor
  · rintro (⟨x, _, hxu⟩ | ⟨v, hv, hvu⟩)
    · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
    · have huv : v = u := injective_cosmicDirection hvu
      rcases hv with hv | hv
      · simpa [huv] using hv
      · have hv0 : (v : E) = 0 := by simpa using hv
        have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
        simp [hv0] at hvnorm
  · intro hu
    exact Or.inr ⟨u, Or.inl hu, rfl⟩

/-- Total convergence entails ordinary convergence. -/
theorem TotalConvergesAlong.pkConvergesAlong {l : Filter ι} {Cf : ι → Set E}
    {C : Set E} (h : TotalConvergesAlong l Cf C) : PKConvergesAlong l Cf C := by
  obtain ⟨hC, hcosmic⟩ := h
  constructor
  · ext x
    rw [← cosmicEmbed_mem_inner_ordinaryCosmicFamily_iff, hcosmic.inner_eq,
      cosmicEmbed_mem_cosmicClosure_iff, hC.closure_eq]
  · ext x
    rw [← cosmicEmbed_mem_outer_ordinaryCosmicFamily_iff, hcosmic.outer_eq,
      cosmicEmbed_mem_cosmicClosure_iff, hC.closure_eq]

/-- Total convergence forces the horizon outer limit into the horizon cone of
the limit. -/
theorem TotalConvergesAlong.horizonOuter_subset {l : Filter ι} {Cf : ι → Set E}
    {C : Set E} (h : TotalConvergesAlong l Cf C) :
    horizonOuterSetLimitAlong l Cf ⊆ horizonCone C := by
  rintro w (rfl | ⟨u, huOuter, r, hr, rfl⟩)
  · exact zero_mem_horizonCone C
  · refine (isCone_horizonCone C).2 ?_ hr
    apply cosmicDirection_mem_cosmicClosure_iff.1
    rw [← h.2.outer_eq]
    exact huOuter

omit [FiniteDimensional ℝ E] in
private theorem cosmicClosure_subset_inner_of_pkConvergesAlong {l : Filter ι}
    {Cf : ι → Set E} {C : Set E} (hlim : PKConvergesAlong l Cf C) :
    closure (cosmicSet C ({0} : Set E)) ⊆
      innerSetLimitAlong l (ordinaryCosmicFamily Cf) := by
  refine closure_minimal ?_ (isClosed_innerSetLimitAlong _ _)
  intro p hp
  rw [mem_cosmicSet] at hp
  rcases hp with ⟨x, hxC, rfl⟩ | ⟨u, hu0, rfl⟩
  · exact cosmicEmbed_mem_inner_ordinaryCosmicFamily_iff.2 (hlim.inner_eq ▸ hxC)
  · have huZero : (u : E) = 0 := by simpa using hu0
    have huNorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    simp [huZero] at huNorm

/-- **Proposition 4.24 (horizon criterion for total convergence)** along an
arbitrary index filter. -/
theorem totalConvergesAlong_iff {l : Filter ι} [l.NeBot] {Cf : ι → Set E}
    {C : Set E} :
    TotalConvergesAlong l Cf C ↔
      PKConvergesAlong l Cf C ∧ horizonOuterSetLimitAlong l Cf ⊆ horizonCone C := by
  refine ⟨fun h ↦ ⟨h.pkConvergesAlong, h.horizonOuter_subset⟩, ?_⟩
  rintro ⟨hlim, hhor⟩
  have hC : IsClosed C := hlim.isClosed
  have hTInner : closure (cosmicSet C ({0} : Set E)) ⊆
      innerSetLimitAlong l (ordinaryCosmicFamily Cf) :=
    cosmicClosure_subset_inner_of_pkConvergesAlong hlim
  have hOuterT : outerSetLimitAlong l (ordinaryCosmicFamily Cf) ⊆
      closure (cosmicSet C ({0} : Set E)) := by
    intro p hp
    rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
    · apply cosmicEmbed_mem_cosmicClosure_iff.2
      rw [hC.closure_eq, ← hlim.outer_eq]
      exact cosmicEmbed_mem_outer_ordinaryCosmicFamily_iff.1 hp
    · exact cosmicDirection_mem_cosmicClosure_iff.2
        (hhor (cosmicDirection_mem_outer_ordinaryCosmicFamily_iff.1 hp))
  exact ⟨hC, Subset.antisymm
      ((innerSetLimitAlong_subset_outerSetLimitAlong _).trans hOuterT) hTInner,
    Subset.antisymm hOuterT
      (hTInner.trans (innerSetLimitAlong_subset_outerSetLimitAlong _))⟩

/-- In the situation of 4.24 the horizon limit exists and equals the horizon
cone of the limit set. -/
theorem TotalConvergesAlong.horizonOuter_eq {l : Filter ι} [l.NeBot]
    {Cf : ι → Set E} {C : Set E} (h : TotalConvergesAlong l Cf C) :
    horizonOuterSetLimitAlong l Cf = horizonCone C := by
  refine Subset.antisymm h.horizonOuter_subset fun w hw ↦ ?_
  by_cases hw0 : w = 0
  · simpa [hw0] using (isCone_horizonOuterSetLimitAlong l Cf).1
  · have huHor : ((cosmicDirectionOf w hw0 : CosmicBoundary E) : E) ∈
        horizonCone C := by
      change NormedSpace.normalize w ∈ horizonCone C
      exact (isCone_horizonCone C).smul_mem hw (inv_nonneg.mpr (norm_nonneg w))
    have huOuter : ((cosmicDirectionOf w hw0 : CosmicBoundary E) : E) ∈
        horizonOuterSetLimitAlong l Cf :=
      cosmicDirection_mem_outer_ordinaryCosmicFamily_iff.1 <| by
        rw [h.2.outer_eq]
        exact cosmicDirection_mem_cosmicClosure_iff.2 huHor
    have hscaled := (isCone_horizonOuterSetLimitAlong l Cf).smul_mem huOuter
      (norm_nonneg w)
    simpa only [coe_cosmicDirectionOf, NormedSpace.norm_smul_normalize w]
      using hscaled

theorem TotalConvergesAlong.horizonInner_eq {l : Filter ι} [l.NeBot]
    {Cf : ι → Set E} {C : Set E} (h : TotalConvergesAlong l Cf C) :
    horizonInnerSetLimitAlong l Cf = horizonCone C := by
  refine Subset.antisymm ?_ ?_
  · exact (horizonInnerSetLimitAlong_subset_horizonOuterSetLimitAlong l Cf).trans
      h.horizonOuter_subset
  · exact horizonCone_subset_horizonInnerSetLimitAlong
      (h.pkConvergesAlong.inner_eq.ge)

end TotalConvergenceAlong

section Definition528

variable {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Definition 5.28**: `S` is totally continuous at `x̄` when `S(x)` converges
totally to `S(x̄)` as `x → x̄`. -/
def SvTotallyContinuousAt (S : E → Set F) (x : E) : Prop :=
  TotalConvergesAlong (nhds x) S (S x)

/-- **Definition 5.28**: `S` is totally outer semicontinuous at `x̄` when at
least `lim sup S(x) ⊂ S(x̄)` and `lim sup∞ S(x) ⊂ S(x̄)∞`. -/
def SvTotallyOscAt (S : E → Set F) (x : E) : Prop :=
  SvOscAt S x ∧ svHorizonOuterLimit S x ⊆ horizonCone (S x)

/-- **Definition 5.28** in its displayed equivalent form: both ordinary limits
and both horizon limits attain their prescribed values. -/
theorem svTotallyContinuousAt_iff_limits {S : E → Set F} {x : E} :
    SvTotallyContinuousAt S x ↔
      (svInnerLimit S x = S x ∧ svOuterLimit S x = S x) ∧
        (svHorizonInnerLimit S x = horizonCone (S x) ∧
          svHorizonOuterLimit S x = horizonCone (S x)) := by
  constructor
  · intro h
    exact ⟨⟨h.pkConvergesAlong.inner_eq, h.pkConvergesAlong.outer_eq⟩,
      ⟨h.horizonInner_eq, h.horizonOuter_eq⟩⟩
  · rintro ⟨⟨hi, ho⟩, _, hho⟩
    exact totalConvergesAlong_iff.2 ⟨⟨hi, ho⟩, hho.subset⟩

/-- **Definition 5.28**, final paragraph: total inner semicontinuity would be
no stronger than inner semicontinuity, since 4.21(c) supplies the horizon
inclusion for free. -/
theorem SvIscAt.horizonCone_subset_svHorizonInnerLimit {S : E → Set F} {x : E}
    (h : SvIscAt S x) : horizonCone (S x) ⊆ svHorizonInnerLimit S x :=
  horizonCone_subset_horizonInnerSetLimitAlong h

/-- The two conditions that "total inner semicontinuity" would ask for reduce
to the first one alone. -/
theorem svTotallyIscAt_iff {S : E → Set F} {x : E} :
    (S x ⊆ svInnerLimit S x ∧ horizonCone (S x) ⊆ svHorizonInnerLimit S x) ↔
      SvIscAt S x :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.horizonCone_subset_svHorizonInnerLimit⟩⟩

/-- **Proposition 5.29 (criteria for total continuity).**  Total continuity at
`x̄` is continuity at `x̄` together with `lim sup∞ S(x) ⊂ S(x̄)∞`. -/
theorem svTotallyContinuousAt_iff {S : E → Set F} {x : E} :
    SvTotallyContinuousAt S x ↔
      SvContinuousAt S x ∧ svHorizonOuterLimit S x ⊆ horizonCone (S x) := by
  rw [SvTotallyContinuousAt, totalConvergesAlong_iff]
  constructor
  · rintro ⟨⟨hi, ho⟩, hh⟩
    exact ⟨svContinuousAt_iff.2 ⟨ho, hi⟩, hh⟩
  · rintro ⟨hc, hh⟩
    obtain ⟨ho, hi⟩ := svContinuousAt_iff.1 hc
    exact ⟨⟨hi, ho⟩, hh⟩

/-- Total outer semicontinuity is outer semicontinuity plus the horizon
inclusion, so 5.29 says total continuity is continuity plus total outer
semicontinuity. -/
theorem svTotallyContinuousAt_iff_svTotallyOscAt {S : E → Set F} {x : E} :
    SvTotallyContinuousAt S x ↔ SvIscAt S x ∧ SvTotallyOscAt S x := by
  rw [svTotallyContinuousAt_iff, SvTotallyOscAt, SvContinuousAt]
  tauto

end Definition528

section AutomaticCases

variable {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Under local boundedness the horizon outer limit collapses to `{0}`: the
nearby values stay inside one bounded set, whose cosmic closure acquires no
direction points. -/
theorem svHorizonOuterLimit_eq_zero_of_svLocallyBoundedAt {S : E → Set F}
    {x : E} (h : SvLocallyBoundedAt S x) : svHorizonOuterLimit S x = {0} := by
  obtain ⟨V, hV, hB⟩ := h
  have hzero : IsCone ({0} : Set F) := ⟨by simp, by simp⟩
  have hsub : outerSetLimitAlong (nhds x) (ordinaryCosmicFamily S) ⊆
      cosmicSet (closure (svImage S V)) ({0} : Set F) := by
    refine outerSetLimitAlong_subset_of_eventually_subset ?_ ?_
    · rw [← closure_cosmicSet_zero_of_isBounded hB]
      exact isClosed_closure
    · filter_upwards [hV] with y hy
      exact cosmicSet_mono (fun z hz ↦ subset_closure (subset_svImage hy hz))
        Subset.rfl
  refine Subset.antisymm ?_ ?_
  · exact (cosmicDirectionCone_mono hsub).trans
      (cosmicDirectionCone_cosmicSet hzero).subset
  · simpa using (isCone_svHorizonOuterLimit S x).1

/-- **Proposition 5.29**: at a point of local boundedness, continuity is
automatically total. -/
theorem SvContinuousAt.svTotallyContinuousAt_of_svLocallyBoundedAt
    {S : E → Set F} {x : E} (hcont : SvContinuousAt S x)
    (hb : SvLocallyBoundedAt S x) : SvTotallyContinuousAt S x := by
  refine svTotallyContinuousAt_iff.2 ⟨hcont, ?_⟩
  rw [svHorizonOuterLimit_eq_zero_of_svLocallyBoundedAt hb]
  exact singleton_subset_iff.2 (zero_mem_horizonCone _)

/-- **Proposition 5.29**: for a mapping that is cone-valued near `x̄`,
continuity is automatically total.  For cones the horizon outer limit is the
ordinary outer limit, and a closed cone is its own horizon cone. -/
theorem SvContinuousAt.svTotallyContinuousAt_of_isCone {S : E → Set F} {x : E}
    (hcont : SvContinuousAt S x) (hK : ∀ᶠ y in nhds x, IsCone (S y)) :
    SvTotallyContinuousAt S x := by
  refine svTotallyContinuousAt_iff.2 ⟨hcont, ?_⟩
  rw [svHorizonOuterLimit, horizonOuterSetLimitAlong_of_eventually_isCone hK,
    horizonCone_eq_self_of_isClosed_isCone hcont.1.isClosed hK.self_of_nhds]
  exact hcont.1

/-- **Proposition 5.29**: for a mapping that is convex-valued near `x̄` and
nonempty-valued at `x̄`, continuity is automatically total.

The sequential proof of 4.25(a) extracts one subsequence carrying points that
escape in the direction `u` and a second carrying points near a fixed
`x₀ ∈ S(x̄)`, then diagonalizes.  Along a filter there is nothing to
diagonalize: escape is a `∃ᶠ` statement, nearness and convexity are `∀ᶠ`
statements, and `Filter.Frequently.and_eventually` combines them directly. -/
theorem SvContinuousAt.svTotallyContinuousAt_of_convex {S : E → Set F} {x : E}
    (hcont : SvContinuousAt S x) (hne : (S x).Nonempty)
    (hconv : ∀ᶠ y in nhds x, Convex ℝ (S y)) :
    SvTotallyContinuousAt S x := by
  refine svTotallyContinuousAt_iff.2 ⟨hcont, ?_⟩
  obtain ⟨x₀, hx₀⟩ := hne
  rintro w (rfl | ⟨u, hu, r, hr, rfl⟩)
  · exact zero_mem_horizonCone _
  · refine (isCone_horizonCone (S x)).smul_mem ?_ hr.le
    refine mem_horizonCone_of_forall_smul_add_mem (x := x₀) fun τ hτ ↦ ?_
    rw [← svOscAt_iff_svOuterLimit_eq.1 hcont.1]
    intro V hV
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
    have hcpos : (0 : ℝ) < ε / 3 := by positivity
    have hMpos : (0 : ℝ) < ‖x₀‖ + 1 := by positivity
    have hηpos : (0 : ℝ) < min 1 (ε / 3) := lt_min one_pos hcpos
    have hδpos : (0 : ℝ) < ε / 3 / (2 * (τ + 1)) := by positivity
    have hτM : (0 : ℝ) ≤ τ * (‖x₀‖ + 1) / (ε / 3) :=
      div_nonneg (mul_nonneg hτ hMpos.le) hcpos.le
    have hRpos : (0 : ℝ) < τ * (‖x₀‖ + 1) / (ε / 3) + τ + 1 := by linarith
    -- a cosmic neighborhood of `dir u` meeting no small ordinary points
    have hclosed : IsClosed (cosmicSet
        (closedBall (0 : F) (τ * (‖x₀‖ + 1) / (ε / 3) + τ + 1)) ({0} : Set F)) := by
      refine closure_eq_iff_isClosed.1 ?_
      rw [closure_cosmicSet_zero_of_isBounded isBounded_closedBall,
        isClosed_closedBall.closure_eq]
    have hnotmem : cosmicDirection u ∉ cosmicSet
        (closedBall (0 : F) (τ * (‖x₀‖ + 1) / (ε / 3) + τ + 1)) ({0} : Set F) := by
      intro hmem
      rcases mem_cosmicSet.1 hmem with ⟨z, _, hz⟩ | ⟨v, hv, _⟩
      · exact cosmicEmbed_ne_cosmicDirection z u hz
      · have hv0 : (v : F) = 0 := by simpa using hv
        have hvn : ‖(v : F)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
        simp [hv0] at hvn
    have hWmem : ball (cosmicDirection u) (ε / 3 / (2 * (τ + 1))) ∩
        (cosmicSet (closedBall (0 : F) (τ * (‖x₀‖ + 1) / (ε / 3) + τ + 1))
          ({0} : Set F))ᶜ ∈ nhds (cosmicDirection u) :=
      Filter.inter_mem (ball_mem_nhds _ hδpos)
        (hclosed.isOpen_compl.mem_nhds hnotmem)
    have hev1 : ∀ᶠ y in nhds x, (S y ∩ ball x₀ (min 1 (ε / 3))).Nonempty :=
      hcont.2 hx₀ _ (ball_mem_nhds _ hηpos)
    refine (((hu _ hWmem).and_eventually hev1).and_eventually hconv).mono ?_
    rintro y ⟨⟨⟨p, hpFam, hpW⟩, p₁, hp₁S, hp₁ball⟩, hconvy⟩
    obtain ⟨z, hzS, rfl⟩ : ∃ z ∈ S y, cosmicEmbed z = p := by
      rcases mem_cosmicSet.1 hpFam with h | ⟨v, hv, _⟩
      · exact h
      · have hv0 : (v : F) = 0 := by simpa using hv
        have hvn : ‖(v : F)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
        simp [hv0] at hvn
    have hzR : τ * (‖x₀‖ + 1) / (ε / 3) + τ + 1 < ‖z‖ := by
      have hz' := hpW.2
      rw [mem_compl_iff, cosmicEmbed_mem_cosmicSet_iff, mem_closedBall_zero_iff,
        not_le] at hz'
      exact hz'
    have hzpos : (0 : ℝ) < ‖z‖ := hRpos.trans hzR
    have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
    -- the normalized point is close to `u`
    have hd : dist (cosmicEmbed z) (cosmicDirection u) <
        ε / 3 / (2 * (τ + 1)) := mem_ball.1 hpW.1
    have hgap : 1 - ‖((cosmicEmbed z : CosmicSpace F) : F)‖ ≤
        dist (cosmicEmbed z) (cosmicDirection u) := by
      have h1 : dist ((cosmicDirection u : CosmicSpace F) : F)
          ((cosmicEmbed z : CosmicSpace F) : F) =
            dist (cosmicEmbed z) (cosmicDirection u) := by
        rw [← Subtype.dist_eq, dist_comm]
      have h2 := norm_sub_norm_le ((cosmicDirection u : CosmicSpace F) : F)
        ((cosmicEmbed z : CosmicSpace F) : F)
      rw [norm_cosmicDirection u, ← dist_eq_norm, h1] at h2
      exact h2
    have hnu : ‖‖z‖⁻¹ • z - (u : F)‖ < 2 * (ε / 3 / (2 * (τ + 1))) := by
      have hdir : dist (cosmicDirection (cosmicDirectionOf z hz0))
          (cosmicEmbed z) = 1 - ‖((cosmicEmbed z : CosmicSpace F) : F)‖ := by
        rw [dist_comm, dist_cosmicEmbed_cosmicDirectionOf hz0]
      have hval : dist (cosmicDirection (cosmicDirectionOf z hz0))
          (cosmicDirection u) = ‖‖z‖⁻¹ • z - (u : F)‖ := by
        rw [Subtype.dist_eq, coe_cosmicDirection, coe_cosmicDirection,
          coe_cosmicDirectionOf, NormedSpace.normalize, dist_eq_norm]
      have htri := dist_triangle (cosmicDirection (cosmicDirectionOf z hz0))
        (cosmicEmbed z) (cosmicDirection u)
      rw [hval, hdir] at htri
      linarith
    -- the convex combination
    have hanonneg : (0 : ℝ) ≤ τ / ‖z‖ := div_nonneg hτ hzpos.le
    have hale : τ / ‖z‖ ≤ 1 := by
      rw [div_le_one hzpos]
      linarith
    refine ⟨(1 - τ / ‖z‖) • p₁ + (τ / ‖z‖) • z,
      hconvy hp₁S hzS (by linarith) hanonneg (by ring), hball ?_⟩
    have hsplit : (1 - τ / ‖z‖) • p₁ + (τ / ‖z‖) • z - (τ • (u : F) + x₀) =
        (p₁ - x₀) + (-(τ / ‖z‖)) • p₁ + τ • (‖z‖⁻¹ • z - (u : F)) := by
      rw [div_eq_mul_inv, mul_smul, smul_sub]
      module
    have hp₁x₀ : ‖p₁ - x₀‖ < min 1 (ε / 3) := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hp₁ball
    have hp₁M : ‖p₁‖ ≤ ‖x₀‖ + 1 := by
      have := norm_add_le (p₁ - x₀) x₀
      have hmin : min 1 (ε / 3) ≤ 1 := min_le_left _ _
      simp only [sub_add_cancel] at this
      linarith
    have hbound : τ / ‖z‖ * ‖p₁‖ ≤ ε / 3 := by
      have h1 : τ / ‖z‖ * ‖p₁‖ ≤ τ / ‖z‖ * (‖x₀‖ + 1) :=
        mul_le_mul_of_nonneg_left hp₁M hanonneg
      have h2 : τ / ‖z‖ * (‖x₀‖ + 1) ≤
          τ / (τ * (‖x₀‖ + 1) / (ε / 3) + τ + 1) * (‖x₀‖ + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hMpos.le
        exact div_le_div_of_nonneg_left hτ hRpos hzR.le
      have h3 : τ / (τ * (‖x₀‖ + 1) / (ε / 3) + τ + 1) * (‖x₀‖ + 1) ≤ ε / 3 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
        have : ε / 3 * (τ * (‖x₀‖ + 1) / (ε / 3)) = τ * (‖x₀‖ + 1) := by
          field_simp
        nlinarith [mul_nonneg hcpos.le hτ]
      linarith
    have hbound2 : τ * ‖‖z‖⁻¹ • z - (u : F)‖ ≤ ε / 3 := by
      have h1 : τ * ‖‖z‖⁻¹ • z - (u : F)‖ ≤
          τ * (2 * (ε / 3 / (2 * (τ + 1)))) :=
        mul_le_mul_of_nonneg_left hnu.le hτ
      have h2 : τ * (2 * (ε / 3 / (2 * (τ + 1)))) ≤ ε / 3 := by
        have hpos : (0 : ℝ) < τ + 1 := by linarith
        have heq : τ * (2 * (ε / 3 / (2 * (τ + 1)))) = ε / 3 * (τ / (τ + 1)) := by
          field_simp
        rw [heq]
        exact mul_le_of_le_one_right hcpos.le ((div_le_one hpos).2 (by linarith))
      linarith
    rw [mem_ball, dist_eq_norm, hsplit]
    have htri : ‖(p₁ - x₀) + (-(τ / ‖z‖)) • p₁ + τ • (‖z‖⁻¹ • z - (u : F))‖ ≤
        ‖p₁ - x₀‖ + ‖(-(τ / ‖z‖)) • p₁‖ + ‖τ • (‖z‖⁻¹ • z - (u : F))‖ :=
      (norm_add_le _ _).trans (by
        have := norm_add_le (p₁ - x₀) ((-(τ / ‖z‖)) • p₁)
        linarith)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg hanonneg, abs_of_nonneg hτ] at htri
    have hmin : min 1 (ε / 3) ≤ ε / 3 := min_le_right _ _
    linarith

end AutomaticCases

section ConvexClauseHypothesis

/-- A convex-valued mapping on `IR`, continuous at the origin with empty value
there, which is not totally continuous at the origin: for `y > 0` its value is
a single point escaping to the direction `1`, and elsewhere it is empty. -/
noncomputable def escapingSingleton : ℝ → Set ℝ := fun y ↦
  if 0 < y then {cosmicRadialOrdinary cosmicUnitOne ⌊y⁻¹⌋₊} else ∅

theorem escapingSingleton_of_nonpos {y : ℝ} (hy : ¬ 0 < y) :
    escapingSingleton y = ∅ := by simp [escapingSingleton, hy]

theorem escapingSingleton_zero : escapingSingleton 0 = ∅ :=
  escapingSingleton_of_nonpos (lt_irrefl 0)

theorem escapingSingleton_of_pos {y : ℝ} (hy : 0 < y) :
    escapingSingleton y = {cosmicRadialOrdinary cosmicUnitOne ⌊y⁻¹⌋₊} := by
  simp [escapingSingleton, hy]

theorem convex_escapingSingleton (y : ℝ) : Convex ℝ (escapingSingleton y) := by
  unfold escapingSingleton
  split
  · exact convex_singleton _
  · exact convex_empty

/-- Everything the counterexample does in cosmic space happens at the single
direction point `dir 1`. -/
private theorem outer_escapingSingleton_subset :
    outerSetLimitAlong (nhds (0 : ℝ)) (ordinaryCosmicFamily escapingSingleton) ⊆
      {cosmicDirection cosmicUnitOne} := by
  intro p hp
  by_contra hne
  rw [mem_singleton_iff] at hne
  obtain ⟨W, W', hWopen, hW'open, hpW, hdW', hdisj⟩ := t2_separation hne
  refine absurd (hp W (hWopen.mem_nhds hpW)) (Filter.not_frequently.2 ?_)
  rw [← nhdsLE_sup_nhdsGT (0 : ℝ), Filter.eventually_sup]
  constructor
  · filter_upwards [self_mem_nhdsWithin] with y hy
    rw [not_nonempty_iff_eq_empty]
    have hy' : escapingSingleton y = ∅ :=
      escapingSingleton_of_nonpos (not_lt.2 hy)
    simp [ordinaryCosmicFamily, hy']
  · filter_upwards [tendsto_cosmicEmbed_radial_floor_inv.eventually
      (hW'open.mem_nhds hdW'), self_mem_nhdsWithin] with y hyW' hy
    rw [not_nonempty_iff_eq_empty]
    refine eq_empty_of_forall_notMem fun q hq ↦ ?_
    have hq1 : q ∈ cosmicSet (escapingSingleton y) ({0} : Set ℝ) := hq.1
    rw [escapingSingleton_of_pos (mem_Ioi.1 hy), cosmicSet_singleton_zero,
      mem_singleton_iff] at hq1
    exact hdisj.le_bot (show q ∈ W ⊓ W' from ⟨hq.2, hq1 ▸ hyW'⟩)

/-- The counterexample is continuous at the origin in the sense of 5.4. -/
theorem svContinuousAt_escapingSingleton :
    SvContinuousAt escapingSingleton 0 := by
  constructor
  · intro v hv
    exact absurd (outer_escapingSingleton_subset
      (cosmicEmbed_mem_outer_ordinaryCosmicFamily_iff.2 hv))
      (cosmicEmbed_ne_cosmicDirection v cosmicUnitOne)
  · rw [SvIscAt, escapingSingleton_zero]
    exact empty_subset _

/-- But its horizon outer limit at the origin contains the direction `1`,
whereas the horizon cone of its empty value there is just `{0}`. -/
theorem not_svTotallyContinuousAt_escapingSingleton :
    ¬ SvTotallyContinuousAt escapingSingleton 0 := by
  intro h
  have hdir : cosmicDirection cosmicUnitOne ∈
      outerSetLimitAlong (nhds (0 : ℝ))
        (ordinaryCosmicFamily escapingSingleton) := by
    intro V hV
    refine Filter.Frequently.filter_mono
      (f := nhdsWithin (0 : ℝ) (Ioi 0)) ?_ nhdsWithin_le_nhds
    refine Filter.Eventually.frequently ?_
    filter_upwards [tendsto_cosmicEmbed_radial_floor_inv.eventually hV,
      self_mem_nhdsWithin] with y hyV hy
    refine ⟨cosmicEmbed (cosmicRadialOrdinary cosmicUnitOne ⌊y⁻¹⌋₊), ?_, hyV⟩
    exact cosmicEmbed_mem_cosmicSet_iff.2
      (by rw [escapingSingleton_of_pos (mem_Ioi.1 hy)]; rfl)
  have hmem : (1 : ℝ) ∈ svHorizonOuterLimit escapingSingleton 0 := by
    simpa only [svHorizonOuterLimit, coe_cosmicUnitOne] using
      cosmicDirection_mem_outer_ordinaryCosmicFamily_iff.1 hdir
  have hsub := (svTotallyContinuousAt_iff.1 h).2 hmem
  rw [escapingSingleton_zero, horizonCone_empty, mem_singleton_iff] at hsub
  exact one_ne_zero hsub

/-- **The convex clause of 5.29 needs `S(x̄) ≠ ∅`.**  The printed statement
omits it, but Theorem 4.25, which 5.29 cites, assumes `C ≠ ∅` throughout. -/
theorem convex_clause_of_529_needs_nonempty :
    ∃ S : ℝ → Set ℝ, (∀ y, Convex ℝ (S y)) ∧ SvContinuousAt S 0 ∧
      ¬ SvTotallyContinuousAt S 0 :=
  ⟨escapingSingleton, convex_escapingSingleton, svContinuousAt_escapingSingleton,
    not_svTotallyContinuousAt_escapingSingleton⟩

end ConvexClauseHypothesis

end RW
