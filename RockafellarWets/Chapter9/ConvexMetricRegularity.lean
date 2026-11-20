/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Metric regularity and openness for convex graphs
-/

import RockafellarWets.Chapter9.InverseCoderivatives
import RockafellarWets.Chapter9.GraphConvexStrictContinuity
import RockafellarWets.Chapter9.AubinLocalization

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {S : E → Set F} {x : E} {u : F}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem inverse_graphConvex (h : SvGraphConvex S) : SvGraphConvex (svInv S) :=
  h.linear_preimage (ContinuousLinearEquiv.prodComm ℝ F E).toLinearMap

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem HasAubinPropertyAt.interior_domain (h : HasAubinPropertyAt S x u) :
    x ∈ interior (svDom S) := by
  obtain ⟨_,hu,_,k,V,hV,W,hW,H⟩ := h
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset hV
  intro a ha
  obtain ⟨z,hz,_⟩ := H x ⟨trivial,mem_of_mem_nhds hV⟩ a ⟨trivial,ha⟩ u ⟨hu,mem_of_mem_nhds hW⟩
  exact ⟨z,hz⟩

/-- **Example 9.45**: for a closed convex graph, metric regularity is
equivalent to the target being an interior point of the range. -/
theorem hasAubinProperty_inverse_iff_interior_range_of_graphConvex
    (hc : SvGraphConvex S) (ho : SvOsc S) (hu : u ∈ S x) :
    HasAubinPropertyAt (svInv S) u x ↔ u ∈ interior (svRange S) := by
  refine ⟨fun h ↦ h.interior_domain,?_⟩
  intro hi
  have hclosed (b : F) : IsClosed (svInv S b) :=
    (isClosed_svGraph_iff_svOsc.mpr ho).preimage (continuous_id.prodMk continuous_const)
  have hs := (inverse_graphConvex hc).svStrictlyContinuousAt hclosed hi
  exact ⟨trivial,hu,RW.IsClosed.isLocallyClosedAt (isClosed_svGraph_iff_svOsc.mpr (svOsc_svInv_iff.mpr ho)) _,
    hs.exists_aubinEstimate x⟩

/-- **Example 9.45**, the equivalent full-range derivative criterion. -/
theorem interior_range_iff_graphicalDerivative_full_range_of_graphConvex
    (hc : SvGraphConvex S) (ho : SvOsc S) (hu : u ∈ S x) :
    u ∈ interior (svRange S) ↔ svRange (graphicalDerivative S x u) = univ := by
  have hr := isGraphicallyRegularAt_of_graphConvex_of_osc hc ho hu
  have hl := RW.IsClosed.isLocallyClosedAt (isClosed_svGraph_iff_svOsc.mpr ho) (x,u)
  rw [← hasAubinProperty_inverse_iff_interior_range_of_graphConvex hc ho hu,
    hasAubinProperty_inverse_iff_regularGraphicalDerivative_full_range_of_regular hu hl hr,
    ← (isGraphicallyRegularAt_iff_graphicalDerivative_eq_regular hu hr.1).mp hr]

/-- The small-ball openness assertion in **Example 9.45**. -/
theorem exists_small_ball_openness_of_graphConvex (hc : SvGraphConvex S) (ho : SvOsc S)
    (hu : u ∈ S x) (hi : u ∈ interior (svRange S)) :
    ∃ k : ℝ≥0, ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∀ b, dist b u ≤ r → ∃ y, b ∈ S y ∧ dist x y ≤ k*r := by
  have ha := (hasAubinProperty_inverse_iff_interior_range_of_graphConvex hc ho hu).mpr hi
  obtain ⟨k,V,hV,W,hW,H⟩ := (hasAubinProperty_inverse_iff_linearOpen hu
    (RW.IsClosed.isLocallyClosedAt (isClosed_svGraph_iff_svOsc.mpr ho) (x,u))).mp ha
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨k,δ,hδ,fun r hr hrδ b hb ↦ ?_⟩
  exact H x (mem_of_mem_nhds hV) r hr u ⟨hu,trivial⟩ b (hδW (hb.trans_lt hrδ))
    (by simpa only [dist_comm] using hb)

/-- **Theorem 9.48 (Robinson–Ursescu)**. The regularity coefficient grows
at most affinely with the distance to the chosen base solution. The proof
only uses convexity and interiority of the range. -/
theorem exists_affine_metricRegularity_of_graphConvex (hc : SvGraphConvex S)
    (hu : u ∈ S x) (hi : u ∈ interior (svRange S)) :
    ∃ ε > 0, ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      ∀ y : E, ∀ b ∈ closedBall u ε,
        infEDist y (svInv S b) ≤ ENNReal.ofReal (α*‖y-x‖+β) * infEDist b (S y) := by
  have hci := inverse_graphConvex hc
  have hI := hci.svIscAt hi
  have hnear : ∀ᶠ a in 𝓝 u, (svInv S a ∩ ball x 1).Nonempty :=
    hI (show x ∈ svInv S u from hu) (ball x 1) (ball_mem_nhds x zero_lt_one)
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := d/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  let α := 2/ε
  let β := α*(2*‖x‖+1)
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  refine ⟨ε,hε,α,β,hα.le,hβ.le,fun y b hb ↦ ?_⟩
  let k : ℝ≥0 := ⟨α*‖y-x‖+β,by positivity⟩
  have hk : 0 < k := by change 0 < α*‖y-x‖+β; positivity
  have hT : InverseTransportEstimate S univ (closedBall u ε) {y} k := by
    intro a _ b' hb' z hz ha
    have hzy : z = y := hz
    subst z
    let R := ‖y‖+‖x‖+1
    have hR : 0 < R := by dsimp [R]; positivity
    have hcover : ∀ c ∈ closedBall b' ε, (svInv S c ∩ closedBall (0:E) R).Nonempty := by
      intro c hc'
      have hcu : dist c u < d := by
        have hh := (dist_triangle c b' u).trans (add_le_add hc' hb')
        dsimp [ε] at hh
        linarith
      obtain ⟨w,hw,hwb⟩ := hdsub hcu
      refine ⟨w,hw,mem_closedBall_zero_iff.mpr ?_⟩
      have hnorm : ‖w‖ ≤ ‖w-x‖+‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (w-x) x
      have hdw : ‖w-x‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hwb
      dsimp [R]
      linarith [norm_nonneg y]
    obtain ⟨w,hw,hwbound⟩ := hci.truncation_transport_step hε hcover
      (show y ∈ svInv S a ∩ closedBall (0:E) R from ⟨ha,mem_closedBall_zero_iff.mpr (by dsimp [R]; linarith [norm_nonneg x])⟩)
    refine ⟨w,hw.1,hwbound.trans ?_⟩
    have hnorm : ‖y‖ ≤ ‖y-x‖+‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (y-x) x
    have hcoeff : 2*R/ε ≤ (k:ℝ) := by
      calc 2*R/ε = α*R := by dsimp [α]; ring
        _ ≤ α*(‖y-x‖+2*‖x‖+1) := mul_le_mul_of_nonneg_left (by dsimp [R]; linarith) hα.le
        _ = k := by dsimp [k,β]; ring
    calc (2*R*dist b' a)/(ε+dist b' a)
        ≤ (2*R*dist b' a)/ε := div_le_div_of_nonneg_left (by positivity) hε (le_add_of_nonneg_right dist_nonneg)
      _ = (2*R/ε)*dist b' a := by ring
      _ ≤ k*dist b' a := mul_le_mul_of_nonneg_right hcoeff dist_nonneg
      _ = k*dist a b' := by rw [dist_comm]
  have hM := hT.metricEstimate hk y (mem_singleton y) b hb
  rw [ENNReal.ofReal_eq_coe_nnreal k.2]
  simpa only [inter_univ] using hM

end RW
