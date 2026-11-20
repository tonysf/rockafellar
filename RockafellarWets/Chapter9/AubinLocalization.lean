/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graphical localization of strict set-valued continuity
-/

import RockafellarWets.Chapter9.StrictSetValuedContinuity
import RockafellarWets.Chapter9.AubinProperty
import RockafellarWets.Chapter5.SequentialLimits
import RockafellarWets.Chapter5.GraphicalLimits

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {X : Set E} {x : E}

/-- A compact truncation of an outer semicontinuous mapping eventually lies
in any open set containing the corresponding part of its base fiber. -/
theorem SvOscWithinAt.eventually_trunc_subset (h : SvOscWithinAt S X x)
    {K W : Set F} (hK : IsCompact K) (hW : IsOpen W) (hsub : S x ∩ K ⊆ W) :
    ∀ᶠ a in 𝓝[X] x, S a ∩ K ⊆ W := by
  by_contra! hn
  have hf : ∃ᶠ a in 𝓝[X] x, (S a ∩ (K ∩ Wᶜ)).Nonempty := hn.mono fun a ha ↦ by
    obtain ⟨v,hv,hw⟩ := Set.not_subset.mp ha
    exact ⟨v,hv.1,hv.2,hw⟩
  obtain ⟨v,hv,hvK,hvW⟩ := outerSetLimitAlong_inter_nonempty_of_frequently (hK.inter_right hW.isClosed_compl) hf
  exact hvW (hsub ⟨h hv,hvK⟩)

/-- A local finite-radius transport bound gives each graphical estimate whose
output point lies strictly within the truncation ball. -/
theorem aubinEstimate_of_local_transport {u : F} {r k : ℝ≥0} (hu : ‖u‖ < r)
    {U : Set E} (hU : U ∈ 𝓝[X] x) (h : RhoTransport k r S U) : AubinEstimate S X x u k := by
  obtain ⟨V,hV,hVX⟩ := eventually_nhdsWithin_iff_exists_nhds.mp hU
  exact ⟨V,hV,ball (0:F) r,isOpen_ball.mem_nhds (by simpa using hu),
    fun a ha b hb v hv ↦ h a (hVX a ha) b (hVX b hb) v ⟨hv.1,ball_subset_closedBall hv.2⟩⟩

/-- **Theorem 9.38**, the lower modulus bound. Every graphical modulus at
an output in the open radius ball is bounded by the distance-profile modulus. -/
theorem graphicalLipschitzModulusWithin_le_svLipschitzModulusWithin
    (hS : NonemptyClosedValuedOn S X) {u : F} {r : ℝ≥0} (hu : ‖u‖ < r) :
    graphicalLipschitzModulusWithin S X x u ≤ svLipschitzModulusWithin S X r x := by
  unfold svLipschitzModulusWithin lipschitzModulusWithin
  refine le_iInf fun k ↦ ?_
  obtain ⟨U,hU,hk⟩ := k.property
  have ht : RhoTransport k.val r S (U ∩ X) := fun a ha b hb v hv ↦
    SvRhoLipschitzOnWith.transport (X := U ∩ X) (k := k.val) (ρ := r)
      (hk.mono inter_subset_left) (fun z hz ↦ hS z hz.2) ha hb hv
  exact (aubinEstimate_of_local_transport hu (inter_mem hU self_mem_nhdsWithin) ht).modulus_le

/-- The lower bound in supremum form, including an empty truncated fiber. -/
theorem iSup_graphicalLipschitzModulusWithin_le_svLipschitzModulusWithin
    (hS : NonemptyClosedValuedOn S X) (r : ℝ≥0) :
    (⨆ u ∈ S x ∩ ball (0:F) (r:ℝ), graphicalLipschitzModulusWithin S X x u) ≤
      svLipschitzModulusWithin S X r x := by
  refine iSup_le fun u ↦ iSup_le fun hu ↦ ?_
  exact graphicalLipschitzModulusWithin_le_svLipschitzModulusWithin hS (by simpa using hu.2)

/-- Strict continuity supplies an Aubin estimate at each output point. -/
theorem SvStrictlyContinuousWithinAt.exists_aubinEstimate (h : SvStrictlyContinuousWithinAt S X x)
    (hS : NonemptyClosedValuedOn S X) (u : F) : ∃ k, AubinEstimate S X x u k := by
  let r : ℝ≥0 := ‖u‖₊+1
  obtain ⟨k,U,hU,hk⟩ := (svStrictlyContinuousWithinAt_iff_local_transport h.1 hS).mp h r
  exact ⟨k,aubinEstimate_of_local_transport (by dsimp [r]; simp) hU hk⟩

/-- The graphical estimate only needs the eventual closed-valuedness
already present in strict continuity, even if distant fibers are empty. -/
theorem SvStrictlyContinuousWithinAt.exists_aubinEstimate_local
    (h : SvStrictlyContinuousWithinAt S X x) (u : F) :
    ∃ k, AubinEstimate S X x u k := by
  let r : ℝ≥0 := ‖u‖₊ + 1
  obtain ⟨k,U,hU,hk⟩ := (strictlyContinuousWithinAt_iff.mp ⟨h.1,h.2.2 r⟩).2
  let V := U ∩ {a | (S a).Nonempty ∧ IsClosed (S a)}
  have hV : V ∈ 𝓝[X] x := inter_mem hU h.2.1
  have ht : RhoTransport k r S V := fun a ha b hb v hv ↦
    SvRhoLipschitzOnWith.transport (X := V) (k := k) (ρ := r)
      (hk.mono inter_subset_left) (fun z hz ↦ hz.2) ha hb hv
  exact ⟨k,aubinEstimate_of_local_transport (by dsimp [r]; simp) hV ht⟩

/-- The absolute graphical estimate requires no assumptions on distant fibers. -/
theorem SvStrictlyContinuousAt.exists_aubinEstimate
    (h : SvStrictlyContinuousAt S x) (u : F) : ∃ k, AubinEstimate S univ x u k :=
  h.exists_aubinEstimate_local u

/-- Strict continuity entails relative outer semicontinuity. -/
theorem SvStrictlyContinuousWithinAt.svOscWithinAt (h : SvStrictlyContinuousWithinAt S X x)
    (hS : NonemptyClosedValuedOn S X) : SvOscWithinAt S X x := by
  intro u hu
  obtain ⟨a,ha,hinner⟩ := exists_seq_mem_innerSetLimit hu
  obtain ⟨v,hv,hvt⟩ := mem_innerSetLimit_iff_exists_seq.mp hinner
  have hax := tendsto_nhdsWithin_iff.mp ha
  let r : ℝ≥0 := ‖u‖₊+1
  obtain ⟨k,U,hU,hk⟩ := (svStrictlyContinuousWithinAt_iff_local_transport h.1 hS).mp h r
  have hxU := mem_of_mem_nhdsWithin h.1 hU
  have hvb : ∀ᶠ n in atTop, v n ∈ closedBall (0:F) (r:ℝ) :=
    hvt.eventually (closedBall_mem_nhds_of_mem (by dsimp [r]; simp))
  have hdist : ∀ᶠ n in atTop, infDist (v n) (S x) ≤ k * dist (a n) x := by
    filter_upwards [ha.eventually hU,hvb,hv] with n hn hnb hnv
    obtain ⟨w,hw,hd⟩ := hk (a n) hn x hxU (v n) ⟨hnv,hnb⟩
    exact (infDist_le_dist_of_mem hw).trans hd
  have hle := le_of_tendsto_of_tendsto ((continuous_infDist_pt (S x)).tendsto u |>.comp hvt)
    (show Tendsto (fun n ↦ (k:ℝ)*dist (a n) x) atTop (𝓝 0) by
      simpa using (hax.1.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x))).const_mul (k:ℝ)) hdist
  exact ((hS x h.1).2.mem_iff_infDist_zero (hS x h.1).1).mpr (le_antisymm hle infDist_nonneg)

/-- **Theorem 9.38**, the finite-cover step. Outer semicontinuity and an
Aubin estimate at every output point give one common estimate on each
bounded truncation. -/
theorem exists_local_transport_of_aubinEstimates (hx : x ∈ X) (hclosed : IsClosed (S x))
    (hosc : SvOscWithinAt S X x) (hA : ∀ u ∈ S x, ∃ k, AubinEstimate S X x u k) (r : ℝ≥0) :
    ∃ k : ℝ≥0, ∃ U ∈ 𝓝[X] x, RhoTransport k r S U := by
  classical
  let K := S x ∩ closedBall (0:F) (r:ℝ)
  have hK : IsCompact K := (isCompact_closedBall (0:F) (r:ℝ)).inter_left hclosed
  choose k V hV W hW hbound using fun u : K ↦ hA u u.property.1
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun u : K ↦ interior (W u)) (fun _ ↦ isOpen_interior)
    (fun u hu ↦ mem_iUnion.mpr ⟨⟨u,hu⟩,mem_interior_iff_mem_nhds.mpr (hW ⟨u,hu⟩)⟩)
  let B := ⋃ u ∈ s, interior (W u)
  have hB : IsOpen B := isOpen_biUnion fun _ _ ↦ isOpen_interior
  have he := hosc.eventually_trunc_subset (isCompact_closedBall (0:F) (r:ℝ)) hB hs
  let U := X ∩ (⋂ u ∈ s, V u) ∩ {a | S a ∩ closedBall (0:F) (r:ℝ) ⊆ B}
  have hU : U ∈ 𝓝[X] x := by
    refine inter_mem (inter_mem self_mem_nhdsWithin ?_) he
    apply (biInter_mem s.finite_toSet).mpr
    intro u hu
    exact mem_nhdsWithin_of_mem_nhds (hV u)
  refine ⟨s.sup k,U,hU,fun a ha b hb v hv ↦ ?_⟩
  obtain ⟨u,hu,hvu⟩ := mem_iUnion₂.mp (ha.2 hv)
  obtain ⟨z,hz,hd⟩ := hbound u a ⟨ha.1.1,mem_iInter₂.mp ha.1.2 u hu⟩
    b ⟨hb.1.1,mem_iInter₂.mp hb.1.2 u hu⟩ v ⟨hv.1,interior_subset hvu⟩
  exact ⟨z,hz,hd.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (Finset.le_sup hu)) dist_nonneg)⟩

/-- A common graphical constant survives the finite-cover argument. -/
theorem exists_local_transport_of_uniform_aubinEstimates (hclosed : IsClosed (S x))
    (hosc : SvOscWithinAt S X x) (r k : ℝ≥0)
    (hA : ∀ u ∈ S x ∩ closedBall (0:F) (r:ℝ), AubinEstimate S X x u k) :
    ∃ U ∈ 𝓝[X] x, RhoTransport k r S U := by
  classical
  let K := S x ∩ closedBall (0:F) (r:ℝ)
  have hK : IsCompact K := (isCompact_closedBall (0:F) (r:ℝ)).inter_left hclosed
  choose V hV W hW hbound using fun u : K ↦ hA u u.property
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun u : K ↦ interior (W u)) (fun _ ↦ isOpen_interior)
    (fun u hu ↦ mem_iUnion.mpr ⟨⟨u,hu⟩,mem_interior_iff_mem_nhds.mpr (hW ⟨u,hu⟩)⟩)
  let B := ⋃ u ∈ s, interior (W u)
  have hB : IsOpen B := isOpen_biUnion fun _ _ ↦ isOpen_interior
  have he := hosc.eventually_trunc_subset (isCompact_closedBall (0:F) (r:ℝ)) hB hs
  let U := X ∩ (⋂ u ∈ s, V u) ∩ {a | S a ∩ closedBall (0:F) (r:ℝ) ⊆ B}
  have hU : U ∈ 𝓝[X] x := by
    refine inter_mem (inter_mem self_mem_nhdsWithin ?_) he
    apply (biInter_mem s.finite_toSet).mpr
    intro u hu
    exact mem_nhdsWithin_of_mem_nhds (hV u)
  refine ⟨U,hU,fun a ha b hb v hv ↦ ?_⟩
  obtain ⟨u,hu,hvu⟩ := mem_iUnion₂.mp (ha.2 hv)
  exact hbound u a ⟨ha.1.1,mem_iInter₂.mp ha.1.2 u hu⟩
    b ⟨hb.1.1,mem_iInter₂.mp hb.1.2 u hu⟩ v ⟨hv.1,interior_subset hvu⟩

/-- **Theorem 9.38**, the upper modulus bound over the closed radius ball.
This extended-real formulation includes empty fibers and infinite moduli. -/
theorem svRhoHatLipschitzModulusWithin_le_iSup_graphicalLipschitzModulusWithin
    (hclosed : IsClosed (S x)) (hosc : SvOscWithinAt S X x) (r : ℝ≥0) :
    svRhoHatLipschitzModulusWithin S X r x ≤
      ⨆ u ∈ S x ∩ closedBall (0:F) (r:ℝ), graphicalLipschitzModulusWithin S X x u := by
  by_contra! h
  obtain ⟨k,hlo,hhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hA : ∀ u ∈ S x ∩ closedBall (0:F) (r:ℝ), AubinEstimate S X x u k := fun u hu ↦
    aubinEstimate_of_modulus_lt ((le_iSup₂ (f := fun u (_ : u ∈ S x ∩ closedBall (0:F) (r:ℝ)) ↦ graphicalLipschitzModulusWithin S X x u) u hu).trans_lt hlo)
  obtain ⟨U,hU,ht⟩ := exists_local_transport_of_uniform_aubinEstimates hclosed hosc r k hA
  apply hhi.not_ge (localPairModulusWithin_le hU ?_)
  intro a ha b hb
  rw [edist_dist,← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_mul (p := (k:ℝ)) (q := dist a b) k.2]
  apply (rhoHatEDistance_le_iff r (S a) (S b)).mpr
  constructor
  · intro v hv
    obtain ⟨z,hz,hd⟩ := ht a ha b hb v hv
    exact mem_cthickening_iff.mpr ((infEDist_le_edist_of_mem hz).trans (by
      rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hd))
  · intro v hv
    obtain ⟨z,hz,hd⟩ := ht b hb a ha v hv
    exact mem_cthickening_iff.mpr ((infEDist_le_edist_of_mem hz).trans (by
      rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm b a] using hd)))

/-- The supremum in the upper bound is attained on every nonempty compact
truncation, giving the maximum in the printed statement. -/
theorem exists_max_graphicalLipschitzModulusWithin (hclosed : IsClosed (S x)) (r : ℝ≥0)
    (hne : (S x ∩ closedBall (0:F) (r:ℝ)).Nonempty) :
    ∃ u ∈ S x ∩ closedBall (0:F) (r:ℝ),
      (⨆ v ∈ S x ∩ closedBall (0:F) (r:ℝ), graphicalLipschitzModulusWithin S X x v) =
        graphicalLipschitzModulusWithin S X x u := by
  have hupper : UpperSemicontinuous (fun u : F ↦ graphicalLipschitzModulusWithin S X x u) :=
    (upperSemicontinuous_graphicalLipschitzModulusWithin S X).comp (continuous_const.prodMk continuous_id)
  obtain ⟨u,hu,hm⟩ := UpperSemicontinuousOn.exists_isMaxOn hne
    ((isCompact_closedBall (0:F) (r:ℝ)).inter_left hclosed) (hupper.upperSemicontinuousOn _)
  exact ⟨u,hu,le_antisymm (iSup_le fun v ↦ iSup_le fun hv ↦ hm hv)
    (le_iSup₂ (f := fun v (_ : v ∈ S x ∩ closedBall (0:F) (r:ℝ)) ↦ graphicalLipschitzModulusWithin S X x v) u hu)⟩

/-- **Theorem 9.38**, the local transport characterization. The local
closedness of the full graph can be supplied separately when the input set
is restricted. -/
theorem svStrictlyContinuousWithinAt_iff_osc_aubinEstimates (hx : x ∈ X)
    (hS : NonemptyClosedValuedOn S X) :
    SvStrictlyContinuousWithinAt S X x ↔ SvOscWithinAt S X x ∧ ∀ u ∈ S x, ∃ k, AubinEstimate S X x u k := by
  exact ⟨fun h ↦ ⟨h.svOscWithinAt hS,fun u _ ↦ h.exists_aubinEstimate hS u⟩,
    fun ⟨ho,hA⟩ ↦ (svStrictlyContinuousWithinAt_iff_local_transport hx hS).mpr
      (exists_local_transport_of_aubinEstimates hx (hS x hx).2 ho hA)⟩

/-- The relative Aubin-property characterization with the local closedness
of the full graph made explicit. -/
theorem svStrictlyContinuousWithinAt_iff_osc_aubin (hx : x ∈ X) (hS : NonemptyClosedValuedOn S X)
    (hgraph : ∀ u ∈ S x, IsLocallyClosedAt (svGraph S) (x,u)) :
    SvStrictlyContinuousWithinAt S X x ↔ SvOscWithinAt S X x ∧ ∀ u ∈ S x, HasAubinPropertyWithinAt S X x u := by
  rw [svStrictlyContinuousWithinAt_iff_osc_aubinEstimates hx hS]
  exact ⟨fun ⟨ho,hA⟩ ↦ ⟨ho,fun u hu ↦ ⟨hx,hu,hgraph u hu,hA u hu⟩⟩,
    fun ⟨ho,hA⟩ ↦ ⟨ho,fun u hu ↦ (hA u hu).2.2.2⟩⟩

end RW
