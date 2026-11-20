/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Bounded-region inverse estimates

The sound implications in Proposition 9.46(a'–c'). Distance-profile
sub-Lipschitz continuity implies the two geometric conditions, which are
equivalent to each other. Their converse to the distance-profile condition
needs a uniform bound on distances of inverse fibers from zero; the
unrestricted global converse in Definition 9.27 is false.
-/

import RockafellarWets.Chapter9.InverseEstimates
import RockafellarWets.Chapter9.StrictSetValuedContinuity

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace F] {S : E → Set F} {U : Set F}

/-- Condition 9.46(b'), with a constant for each bounded input region. -/
def BoundedInverseMetricEstimate (S : E → Set F) (U : Set F) : Prop :=
  ∀ ρ : ℝ≥0, ∃ k : ℝ≥0, InverseMetricEstimate S U U (closedBall 0 (ρ:ℝ)) k

/-- Condition 9.46(c'), with a constant for each bounded input region. -/
def BoundedInverseOpenEstimate (S : E → Set F) (U : Set F) : Prop :=
  ∀ ρ : ℝ≥0, ∃ k : ℝ≥0, InverseOpenEstimate S U U (closedBall 0 (ρ:ℝ)) k

private theorem rhoTransport_inverse_iff {k ρ : ℝ≥0} :
    RhoTransport k ρ (svInv S) U ↔
      InverseTransportEstimate S U U (closedBall 0 (ρ:ℝ)) k := by
  exact ⟨fun h a ha b hb x hx hax ↦ h a ha b hb x ⟨hax,hx⟩,
    fun h a ha b hb x hx ↦ h a ha b hb x hx.2 hx.1⟩

private theorem inverseTransport_mono_constant {A W : Set F} {V : Set E} {k l : ℝ≥0}
    (h : InverseTransportEstimate S A W V k) (hkl : k ≤ l) :
    InverseTransportEstimate S A W V l := by
  intro a ha b hb x hx hax
  obtain ⟨y,hy,hd⟩ := h a ha b hb x hx hax
  exact ⟨y,hy,hd.trans (mul_le_mul_of_nonneg_right (show (k:ℝ) ≤ l from hkl) dist_nonneg)⟩

/-- The geometric primed conditions are equivalent without any extra
boundedness assumption. Existence of a constant allows harmless enlargement. -/
theorem boundedInverseMetricEstimate_iff_open :
    BoundedInverseMetricEstimate S U ↔ BoundedInverseOpenEstimate S U := by
  constructor
  · intro h ρ
    obtain ⟨k,hk⟩ := h ρ
    exact ⟨k+1,inverseTransportEstimate_iff_openEstimate.mp
      (hk.transportEstimate_of_lt (by simp))⟩
  · intro h ρ
    obtain ⟨k,hk⟩ := h ρ
    have ht := inverseTransportEstimate_iff_openEstimate.mpr hk
    exact ⟨k+1,(inverseTransport_mono_constant ht (by simp)).metricEstimate (by positivity)⟩

/-- **Proposition 9.46(a'⇒b')**, using the distance-profile definition of
sub-Lipschitz continuity. -/
theorem SvSubLipschitzOn.boundedInverseMetricEstimate
    (h : SvSubLipschitzOn (svInv S) U) : BoundedInverseMetricEstimate S U := by
  intro ρ
  obtain ⟨k,hk⟩ := h.2 ρ
  have ht : InverseTransportEstimate S U U (closedBall 0 (ρ:ℝ)) k :=
    rhoTransport_inverse_iff.mp (fun a ha b hb v hv ↦ hk.transport h.1 ha hb hv)
  exact ⟨k+1,(inverseTransport_mono_constant ht (by simp)).metricEstimate (by positivity)⟩

/-- **Proposition 9.46(a'⇒c')**. -/
theorem SvSubLipschitzOn.boundedInverseOpenEstimate
    (h : SvSubLipschitzOn (svInv S) U) : BoundedInverseOpenEstimate S U :=
  boundedInverseMetricEstimate_iff_open.mp h.boundedInverseMetricEstimate

/-- A uniform bound on distances of inverse fibers from zero supplies the
missing hypothesis in the global converse. -/
theorem svSubLipschitzOn_inverse_iff_boundedMetric_of_bound
    (hS : NonemptyClosedValuedOn (svInv S) U) {B : ℝ≥0}
    (hB : ∀ u ∈ U, infDist (0:E) (svInv S u) ≤ (B:ℝ)) :
    SvSubLipschitzOn (svInv S) U ↔ BoundedInverseMetricEstimate S U := by
  refine ⟨SvSubLipschitzOn.boundedInverseMetricEstimate,fun h ↦ ⟨hS,fun ρ ↦ ?_⟩⟩
  let R : ℝ≥0 := 2*ρ+B
  obtain ⟨k,hk⟩ := h R
  have ht : RhoTransport k R (svInv S) U :=
    rhoTransport_inverse_iff.mpr (hk.transportEstimate hS)
  refine ⟨k,svRhoLipschitzOnWith_iff_rhoDistance.mpr (fun a ha b hb ↦ ?_)⟩
  have hcomp := rhoDistance_le_rhoHatDistance_of_two_mul (r := ρ) (s := R)
    (hS a ha).2 (hS b hb).2 (hS a ha).1 (hS b hb).1 (by
      have hh := max_le (hB a ha) (hB b hb)
      change 2*(ρ:ℝ)+max (infDist 0 (svInv S a)) (infDist 0 (svInv S b)) ≤ (R:ℝ)
      simpa [R] using add_le_add_left hh (2*(ρ:ℝ)))
  exact hcomp.trans ((rhoTransport_iff_rhoHatDistance hS).mp ht a ha b hb)

/-- With bounded inverse image, the geometric primed conditions reduce to
ordinary global Lipschitz continuity, as stated after 9.46. -/
theorem boundedInverseMetricEstimate_iff_lipschitz_of_bounded
    (hS : NonemptyClosedValuedOn (svInv S) U)
    (hb : Bornology.IsBounded (svImage (svInv S) U)) :
    BoundedInverseMetricEstimate S U ↔ SvLipschitzOn (svInv S) U := by
  obtain ⟨R,hR,hbound⟩ := hb.exists_pos_norm_le
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h ⟨R,hR.le⟩
    refine ⟨k,(svLipschitzOnWith_iff_transport hS).mpr (fun a ha b hb x hx ↦ ?_)⟩
    exact hk.transportEstimate hS a ha b hb x
      (mem_closedBall_zero_iff.mpr (hbound x (mem_svImage.mpr ⟨a,ha,hx⟩))) hx
  · rintro ⟨k,hk⟩ ρ
    have ht := (svLipschitzOnWith_iff_transport hS).mp hk
    have ht' : InverseTransportEstimate S U U (closedBall 0 (ρ:ℝ)) k :=
      fun a ha b hb x _ hx ↦ ht a ha b hb x hx
    exact ⟨k+1,(inverseTransport_mono_constant ht' (by simp)).metricEstimate (by positivity)⟩

end RW
