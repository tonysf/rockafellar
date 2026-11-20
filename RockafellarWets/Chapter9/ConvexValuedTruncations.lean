/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Strict continuity of convex-valued mappings by truncation
-/

import RockafellarWets.Chapter4.ConvexTruncationDistances
import RockafellarWets.Chapter9.ConvexMappingTruncations

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : E → Set F} {X : Set E} {x : E}

/-- **Theorem 9.33(a).** Strict continuity of a convex-valued mapping is
equivalent to local Hausdorff Lipschitz continuity of every sufficiently
large closed-ball truncation. -/
theorem svStrictlyContinuousWithinAt_iff_truncations (hx : x ∈ X)
    (hS : NonemptyClosedValuedOn S X) (hc : ∀ a ∈ X, Convex ℝ (S a))
    {R : ℝ≥0} (hR : svZeroRadius S X < R) :
    SvStrictlyContinuousWithinAt S X x ↔ ∀ r : ℝ≥0, 2*R < r →
      ∃ U ∈ 𝓝[X] x, SvLipschitzOn (svTrunc S (closedBall (0:F) (r:ℝ))) U := by
  have h0 (a : E) (ha : a ∈ X) : infEDist 0 (S a) < (R:ℝ≥0∞) :=
    (le_iSup (fun z : X ↦ infEDist 0 (S z)) ⟨a,ha⟩).trans_lt hR
  have hr0 (a : E) (ha : a ∈ X) : infDist 0 (S a) < (R:ℝ) := by
    simpa only [infDist,ENNReal.coe_toReal] using ENNReal.toReal_lt_toReal (infEDist_ne_top (hS a ha).1) ENNReal.coe_ne_top |>.2 (h0 a ha)
  have hn {r : ℝ≥0} (hr : 2*R < r) {a : E} (ha : a ∈ X) :
      (svTrunc S (closedBall (0:F) (r:ℝ)) a).Nonempty := by
    obtain ⟨u,hu,hur⟩ := (infDist_lt_iff (hS a ha).1).1 (hr0 a ha)
    have hRr : (R:ℝ) ≤ r := by
      have h2 : (2:ℝ)*R < r := by exact_mod_cast hr
      have hpos : 0 ≤ (R:ℝ) := R.2
      linarith
    exact ⟨u,hu,mem_closedBall_zero_iff.2 ((dist_zero_left u ▸ hur.le).trans hRr)⟩
  constructor
  · intro hs r hr
    obtain ⟨k,U,hU,hk⟩ := (svStrictlyContinuousWithinAt_iff_local_rhoHatDistance hx hS).1 hs r
    refine ⟨U∩X,inter_mem hU self_mem_nhdsWithin,4*k,fun a ha ↦ ⟨hn hr ha.2,(hS a ha.2).2.inter isClosed_closedBall⟩,
      fun a ha b hb ↦ ?_⟩
    have hcond : 2*max (infDist 0 (S a)) (infDist 0 (S b)) < (r:ℝ) := by
      have h2 : (2:ℝ)*R < r := by exact_mod_cast hr
      linarith [max_lt (hr0 a ha.2) (hr0 b hb.2)]
    have hest := (rhoHatDistance_le_hausdorffDist_truncations_le_four_mul r (hS a ha.2).2 (hS b hb.2).2
      (hS a ha.2).1 (hS b hb.2).1 (hc a ha.2) (hc b hb.2) hcond).2
    have hbdd (z : E) : Bornology.IsBounded (svTrunc S (closedBall (0:F) (r:ℝ)) z) :=
      isBounded_closedBall.subset inter_subset_right
    have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded (hn hr ha.2) (hn hr hb.2) (hbdd a) (hbdd b)
    apply (ENNReal.le_ofReal_iff_toReal_le hfin (by positivity)).2
    change hausdorffDist _ _ ≤ (↑(4*k : ℝ≥0) : ℝ)*dist a b
    rw [NNReal.coe_mul,NNReal.coe_ofNat]
    exact hest.trans (by nlinarith [hk a ha.1 b hb.1])
  · intro hs
    refine (svStrictlyContinuousWithinAt_iff_local_transport hx hS).2 fun r ↦ ?_
    let s : ℝ≥0 := 2*R+r+1
    have hRs : 2*R < s := by dsimp [s]; exact lt_add_of_le_of_pos (le_add_of_nonneg_right r.2) zero_lt_one
    have hrs : (r:ℝ) ≤ s := by dsimp [s]; linarith [show 0 ≤ (R:ℝ) from R.2]
    obtain ⟨U,hU,k,hk⟩ := hs s hRs
    refine ⟨k,U,hU,fun a ha b hb v hv ↦ ?_⟩
    have hv' : v ∈ svTrunc S (closedBall (0:F) (s:ℝ)) a := ⟨hv.1,closedBall_subset_closedBall hrs hv.2⟩
    obtain ⟨w,hw,hd⟩ := (svLipschitzOnWith_iff_transport hk.1).1 hk a ha b hb v hv'
    exact ⟨w,hw.1,hd⟩

end RW
