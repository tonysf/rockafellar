/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Bounded fibers and local-to-global Lipschitz estimates
-/

import RockafellarWets.Chapter9.StrictSetValuedContinuity
import RockafellarWets.Chapter9.BoundedLipschitzModulus
import RockafellarWets.Chapter5.LocallyBoundedContinuity

open Filter Metric Set Topology Bornology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every bounded-radius distance is bounded by the full Hausdorff distance. -/
theorem ofReal_rhoDistance_le_hausdorffEDist (ρ : ℝ≥0) {C D : Set F} (hC : IsClosed C) (hD : IsClosed D)
    (hn : C.Nonempty) (hm : D.Nonempty) : ENNReal.ofReal (rhoDistance ρ C D) ≤ hausdorffEDist C D := by
  apply ge_of_tendsto (tendsto_ofReal_rhoDistance_atTop hC hD hn hm)
  filter_upwards [eventually_ge_atTop ρ] with r hr
  exact ENNReal.ofReal_le_ofReal (rhoDistance_mono hr C D)

variable {S : E → Set F} {X : Set E} {x : E}

/-- **Theorem 9.30.** A full Lipschitz constant simultaneously bounds every finite radius. -/
theorem SvLipschitzOnWith.svRhoLipschitzOnWith {k : ℝ≥0} (h : SvLipschitzOnWith k S X) (r : ℝ≥0) :
    SvRhoLipschitzOnWith k r S X := by
  apply svRhoLipschitzOnWith_iff_rhoDistance.2
  intro a ha b hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg k.2 dist_nonneg)).1
    ((ofReal_rhoDistance_le_hausdorffEDist r (h.1 a ha).2 (h.1 b hb).2 (h.1 a ha).1 (h.1 b hb).1).trans
      (h.2 a ha b hb))

theorem SvLipschitzOn.svSubLipschitzOn (h : SvLipschitzOn S X) : SvSubLipschitzOn S X := by
  obtain ⟨k,hk⟩ := h
  exact ⟨hk.1,fun r ↦ ⟨k,hk.svRhoLipschitzOnWith r⟩⟩

/-- A radius containing every image reduces the truncated geometric transport
to the full Hausdorff-Lipschitz condition. -/
theorem svLipschitzOnWith_of_bounded_rho_transport {r k : ℝ≥0} (hS : NonemptyClosedValuedOn S X)
    (hb : svImage S X ⊆ closedBall (0:F) (r:ℝ)) (ht : RhoTransport k r S X) :
    SvLipschitzOnWith k S X :=
  (svLipschitzOnWith_iff_transport hS).2 fun a ha b hbb v hv ↦ ht a ha b hbb v ⟨hv,hb (mem_svImage.2 ⟨a,ha,hv⟩)⟩

/-- **Theorem 9.30**, equivalence on a set with bounded image. -/
theorem svSubLipschitzOn_iff_svLipschitzOn_of_bounded (hb : IsBounded (svImage S X)) :
    SvSubLipschitzOn S X ↔ SvLipschitzOn S X := by
  refine ⟨fun ⟨hS,h⟩ ↦ ?_,SvLipschitzOn.svSubLipschitzOn⟩
  obtain ⟨r,hr,hb⟩ := hb.subset_closedBall_lt 0 (0:F)
  obtain ⟨k,hk⟩ := h ⟨r,hr.le⟩
  exact ⟨k,svLipschitzOnWith_of_bounded_rho_transport (r := ⟨r,hr.le⟩) hS hb (fun _ ha _ hb _ hv ↦ hk.transport hS ha hb hv)⟩

/-- At a strictly continuous point any local bound on the image yields full local Lipschitz continuity. -/
theorem SvStrictlyContinuousWithinAt.exists_svLipschitzOn (h : SvStrictlyContinuousWithinAt S X x)
    (hb : SvLocallyBoundedWithinAt S X x) : ∃ U ∈ 𝓝[X] x, SvLipschitzOn S U := by
  obtain ⟨V,hV,hvb⟩ := hb
  obtain ⟨r,hr,hball⟩ := hvb.subset_closedBall_lt 0 (0:F)
  obtain ⟨k,U,hU,hk⟩ := (strictlyContinuousWithinAt_iff.1 ⟨h.1,h.2.2 ⟨r,hr.le⟩⟩).2
  let Y := U ∩ (X ∩ V) ∩ {z | (S z).Nonempty ∧ IsClosed (S z)}
  have hY : Y ∈ 𝓝[X] x := inter_mem (inter_mem hU (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV))) h.2.1
  have hS : NonemptyClosedValuedOn S Y := fun _ hy ↦ hy.2
  have hbY : svImage S Y ⊆ closedBall (0:F) r := (svImage_mono (S := S) (show Y ⊆ X ∩ V from fun _ hy ↦ hy.1.2)).trans hball
  have hprof : SvRhoLipschitzOnWith k ⟨r,hr.le⟩ S Y := hk.mono (fun _ hy ↦ hy.1.1)
  exact ⟨Y,hY,k,svLipschitzOnWith_of_bounded_rho_transport (r := ⟨r,hr.le⟩) hS hbY
    (fun _ ha _ hb _ hv ↦ hprof.transport hS ha hb hv)⟩

theorem svStrictlyContinuousWithinAt_of_locally_svSubLipschitzOn (hx : x ∈ X)
    (h : ∃ U ∈ 𝓝[X] x, SvSubLipschitzOn S U) : SvStrictlyContinuousWithinAt S X x := by
  obtain ⟨U,hU,hS,hp⟩ := h
  refine ⟨hx,?_,fun r ↦ ?_⟩
  · filter_upwards [hU] with y hy using hS y hy
  · obtain ⟨k,hk⟩ := hp r
    exact (lipschitzModulusWithin_le hU hk).trans_lt ENNReal.coe_lt_top

/-- The three pointwise local equivalents in Theorem 9.30. Taking these
equivalences at every point of the relative set gives their set-wide forms. -/
theorem sv_local_lipschitz_iff_of_locallyBounded (hx : x ∈ X) (hb : SvLocallyBoundedWithinAt S X x) :
    (SvStrictlyContinuousWithinAt S X x ↔ ∃ U ∈ 𝓝[X] x, SvLipschitzOn S U) ∧
      (SvStrictlyContinuousWithinAt S X x ↔ ∃ U ∈ 𝓝[X] x, SvSubLipschitzOn S U) := by
  have imp : (∃ U ∈ 𝓝[X] x, SvLipschitzOn S U) → ∃ U ∈ 𝓝[X] x, SvSubLipschitzOn S U :=
    fun ⟨U,hU,h⟩ ↦ ⟨U,hU,h.svSubLipschitzOn⟩
  exact ⟨⟨fun h ↦ h.exists_svLipschitzOn hb,fun h ↦ svStrictlyContinuousWithinAt_of_locally_svSubLipschitzOn hx (imp h)⟩,
    ⟨fun h ↦ imp (h.exists_svLipschitzOn hb), svStrictlyContinuousWithinAt_of_locally_svSubLipschitzOn hx⟩⟩

/-- A uniform constant for all radii is a full Hausdorff-Lipschitz constant. -/
theorem svLipschitzOnWith_of_forall_rho {k : ℝ≥0} (hS : NonemptyClosedValuedOn S X)
    (h : ∀ r : ℝ≥0, SvRhoLipschitzOnWith k r S X) : SvLipschitzOnWith k S X := by
  refine ⟨hS,fun a ha b hb ↦ ?_⟩
  apply le_of_tendsto (tendsto_ofReal_rhoDistance_atTop (hS a ha).2 (hS b hb).2 (hS a ha).1 (hS b hb).1)
  exact Eventually.of_forall fun r ↦ ENNReal.ofReal_le_ofReal ((h r).dist_le_mul a ha b hb)

/-- Upper semicontinuity of each truncated modulus, the first clause of 9.31. -/
theorem upperSemicontinuous_svLipschitzModulusWithin (S : E → Set F) (X : Set E) (r : ℝ≥0) :
    UpperSemicontinuous (svLipschitzModulusWithin S X r) := upperSemicontinuous_lipschitzModulusWithin _ _

theorem svLipschitzModulusWithin_le_hausdorffModulus (hS : NonemptyClosedValuedOn S X) (r : ℝ≥0) (x : E) :
    svLipschitzModulusWithin S X r x ≤ svHausdorffLipschitzModulusWithin S X x := by
  refine le_iInf fun k ↦ ?_
  obtain ⟨U,hU,hu⟩ := k.2
  apply lipschitzModulusWithin_le (inter_mem hU self_mem_nhdsWithin)
  intro a ha b hb
  rw [edist_dist]
  exact (ofReal_rhoDistance_le_hausdorffEDist r (hS a ha.2).2 (hS b hb.2).2 (hS a ha.2).1 (hS b hb.2).1).trans
    (hu a ha.1 b hb.1)

end RW
