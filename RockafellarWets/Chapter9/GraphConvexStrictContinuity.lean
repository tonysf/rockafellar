/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict continuity of graph-convex mappings
-/

import RockafellarWets.Chapter9.ConvexValuedTruncations

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {x : E}

/-- **Corollary 9.34.** A closed-valued graph-convex mapping is strictly
continuous at every interior point of its domain. -/
theorem SvGraphConvex.svStrictlyContinuousAt (h : SvGraphConvex S)
    (hclosed : ∀ a, IsClosed (S a)) (hx : x ∈ interior (svDom S)) :
    SvStrictlyContinuousAt S x := by
  obtain ⟨d,hd,hdX⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_interior.mem_nhds hx)
  let X := closedBall x d
  have hxX : x ∈ X := mem_closedBall_self hd.le
  have hX : X ∈ 𝓝 x := closedBall_mem_nhds x hd
  have hne : NonemptyClosedValuedOn S X := fun a ha ↦ ⟨show a ∈ svDom S from interior_subset (hdX ha),hclosed a⟩
  let R : ℝ≥0 := (svZeroRadius S X).toNNReal + 1
  have hfin := h.svZeroRadius_lt_top (isCompact_closedBall x d) hdX
  have hR : svZeroRadius S X < (R:ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hfin.ne,ENNReal.coe_lt_coe]
    exact lt_add_of_pos_right _ zero_lt_one
  have hD := h.svBadFiberDistance_pos (isCompact_closedBall x d) hdX hR
  have hr : SvStrictlyContinuousWithinAt S X x := by
    apply (svStrictlyContinuousWithinAt_iff_truncations hxX hne (fun a _ ↦ h.svConvexValued a) hR).2
    intro r hr
    have hRr : R ≤ r :=
      (show R ≤ 2*R by simpa only [two_mul] using (show R ≤ R+R from le_add_of_nonneg_right (zero_le R))).trans hr.le
    refine ⟨X,self_mem_nhdsWithin,⟨⟨(2/(svBadFiberDistance S X R).toReal)*(r:ℝ),by positivity⟩,?_⟩⟩
    have htr (a : E) (ha : a ∈ X) (b : E) (v : F) (hv : v ∈ S b ∩ closedBall (0:F) (r:ℝ)) :=
      h.truncation_transport (fun a _ ↦ hclosed a) hD (ENNReal.coe_le_coe.2 hRr) ha b hv
    have hn (a : E) (ha : a ∈ X) : (svTrunc S (closedBall (0:F) (r:ℝ)) a).Nonempty := by
      have hinf : infEDist 0 (S a) < (r:ℝ≥0∞) :=
        (le_iSup (fun a : X ↦ infEDist 0 (S a)) ⟨a,ha⟩).trans_lt (hR.trans_le (ENNReal.coe_le_coe.2 hRr))
      obtain ⟨v,hv,hvr⟩ := infEDist_lt_iff.1 hinf
      rw [edist_nndist,ENNReal.coe_lt_coe] at hvr
      exact ⟨v,hv,by
        have hvnorm : ‖v‖₊ ≤ r := by simpa using hvr.le
        simpa only [mem_closedBall,dist_zero_right] using (show ‖v‖ ≤ (r:ℝ) by exact_mod_cast hvnorm)⟩
    apply (svLipschitzOnWith_iff_transport (fun a ha ↦ ⟨hn a ha,(hclosed a).inter isClosed_closedBall⟩)).2
    intro a ha b hb v hv
    simpa only [dist_comm b a] using htr b hb a v hv
  have hfilt : 𝓝[X] x = 𝓝[univ] x := by rw [nhdsWithin_eq_nhds.2 hX,nhdsWithin_univ]
  refine ⟨mem_univ x,hfilt ▸ hr.2.1,fun r ↦ ?_⟩
  obtain ⟨k,U,hU,hL⟩ := (strictlyContinuousWithinAt_iff.mp ⟨hxX,hr.2.2 r⟩).2
  exact (lipschitzModulusWithin_le (hfilt ▸ hU) hL).trans_lt ENNReal.coe_lt_top

/-- The graph-convex criterion yields uniform sub-Lipschitz bounds on
compact convex subsets of the interior domain. -/
theorem SvGraphConvex.svSubLipschitzOn (h : SvGraphConvex S) (hclosed : ∀ a, IsClosed (S a))
    {X : Set E} (hc : Convex ℝ X) (hX : IsCompact X) (hi : X ⊆ interior (svDom S)) :
    SvSubLipschitzOn S X :=
  svSubLipschitzOn_of_compact_convex hc hX fun a ha ↦ h.svStrictlyContinuousAt hclosed (hi ha)

end RW
