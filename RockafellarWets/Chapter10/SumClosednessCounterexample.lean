/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closedness missing from the unbounded strict-continuity sum rule

The sum of the closed exponential graph and the horizontal axis is the
open upper half-plane. Constant mappings with these fibers satisfy the
printed hypotheses of 10.42, including bounded decompositions at every
point of the sum, but the sum is not closed-valued.
-/

import RockafellarWets.Chapter10.CompositionClosednessCounterexample

open Bornology Filter Metric Set Topology
open scoped Pointwise

namespace RW

def exponentialGraphSet : Set (WithLp 2 (ℝ × ℝ)) := {p | p.snd = Real.exp p.fst}
def horizontalAxisSet : Set (WithLp 2 (ℝ × ℝ)) := {p | p.snd = 0}

theorem isClosed_exponentialGraphSet : IsClosed exponentialGraphSet :=
  isClosed_eq (WithLp.continuous_snd 2 ℝ ℝ) (Real.continuous_exp.comp (WithLp.continuous_fst 2 ℝ ℝ))

theorem isClosed_horizontalAxisSet : IsClosed horizontalAxisSet :=
  isClosed_eq (WithLp.continuous_snd 2 ℝ ℝ) continuous_const

theorem exponentialGraphSet_add_horizontalAxisSet :
    exponentialGraphSet+horizontalAxisSet = {p | 0 < p.snd} := by
  ext p
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change 0 < a.snd+b.snd
    rw [show b.snd = 0 from hb,add_zero,show a.snd = Real.exp a.fst from ha]
    exact Real.exp_pos _
  · intro hp
    let a : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (Real.log p.snd,p.snd)
    refine ⟨a,?_,p-a,?_,add_sub_cancel _ _⟩
    · exact (Real.exp_log hp).symm
    · change p.snd-p.snd = 0
      exact sub_self _

theorem exponentialSum_locallyBounded_decompositions {x : ℝ} {u : WithLp 2 (ℝ × ℝ)}
    (hu : 0 < u.snd) : SvLocallyBoundedAt
      (svAddAux (fun _ : ℝ ↦ exponentialGraphSet) (fun _ : ℝ ↦ horizontalAxisSet)) (x,u) := by
  let V : Set (WithLp 2 (ℝ × ℝ)) := {p | u.snd/2 < p.snd ∧ p.snd < 2*u.snd}
  have hV : V ∈ 𝓝 u := (WithLp.continuous_snd 2 ℝ ℝ).continuousAt.preimage_mem_nhds
    (Ioo_mem_nhds (by linarith) (by linarith))
  refine ⟨univ ×ˢ V,prod_mem_nhds univ_mem hV,?_⟩
  have hb := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.lipschitz.isBounded_image
    ((isBounded_Icc (a := Real.log (u.snd/2)) (b := Real.log (2*u.snd))).prod
      (isBounded_Icc (a := u.snd/2) (b := 2*u.snd)))
  apply hb.subset
  intro a ha
  obtain ⟨p,hp,ha⟩ := mem_svImage.mp ha
  obtain ⟨haA,haB⟩ := mem_svAddAux.mp ha
  have he : a.snd = p.2.snd := by
    have hz : p.2.snd-a.snd = 0 := haB
    exact (sub_eq_zero.mp hz).symm
  have hpos : 0 < a.snd := he ▸ (lt_trans (by linarith) hp.2.1)
  have hlog : a.fst = Real.log a.snd := by rw [show a.snd = Real.exp a.fst from haA,Real.log_exp]
  refine ⟨WithLp.ofLp a,⟨?_,?_⟩,rfl⟩
  · change Real.log (u.snd/2) ≤ a.fst ∧ a.fst ≤ Real.log (2*u.snd)
    rw [hlog,he]
    exact ⟨Real.log_le_log (by linarith) hp.2.1.le,Real.log_le_log (he ▸ hpos) hp.2.2.le⟩
  · change u.snd/2 ≤ a.snd ∧ a.snd ≤ 2*u.snd
    rw [he]
    exact ⟨hp.2.1.le,hp.2.2.le⟩

theorem not_isClosed_exponentialGraphSet_add_horizontalAxisSet :
    ¬ IsClosed (exponentialGraphSet+horizontalAxisSet) := by
  intro hc
  rw [exponentialGraphSet_add_horizontalAxisSet] at hc
  have hcont : Continuous (fun t : ℝ ↦ WithLp.toLp 2 ((0:ℝ),t)) :=
    (WithLp.prod_continuous_toLp 2 ℝ ℝ).comp (continuous_const.prodMk continuous_id)
  have hI : IsClosed (Ioi (0:ℝ)) := hc.preimage hcont
  have hz : (0:ℝ) ∈ closure (Ioi (0:ℝ)) := by rw [closure_Ioi]; exact (le_rfl : (0:ℝ) ≤ 0)
  rw [hI.closure_eq] at hz
  exact lt_irrefl (0:ℝ) hz

/-- A formal counterexample to the separate unbounded strict-continuity
assertion in 10.42. The graph-point Aubin conclusions remain valid. -/
theorem strict_continuity_sum_counterexample :
    SvOsc (fun _ : ℝ ↦ exponentialGraphSet) ∧ SvOsc (fun _ : ℝ ↦ horizontalAxisSet) ∧
    SvStrictlyContinuousAt (fun _ : ℝ ↦ exponentialGraphSet) 0 ∧
    SvStrictlyContinuousAt (fun _ : ℝ ↦ horizontalAxisSet) 0 ∧
    (∀ u ∈ svAdd (fun _ : ℝ ↦ exponentialGraphSet) (fun _ : ℝ ↦ horizontalAxisSet) 0,
      SvLocallyBoundedAt (svAddAux (fun _ : ℝ ↦ exponentialGraphSet) (fun _ : ℝ ↦ horizontalAxisSet)) (0,u)) ∧
    ¬ SvStrictlyContinuousAt (svAdd (fun _ : ℝ ↦ exponentialGraphSet) (fun _ : ℝ ↦ horizontalAxisSet)) 0 := by
  refine ⟨fun x ↦ svOscAt_const isClosed_exponentialGraphSet x,
    fun x ↦ svOscAt_const isClosed_horizontalAxisSet x,
    svStrictlyContinuousAt_const ⟨WithLp.toLp 2 ((0:ℝ),(1:ℝ)),by simp [exponentialGraphSet]⟩ isClosed_exponentialGraphSet 0,
    svStrictlyContinuousAt_const (C := horizontalAxisSet) ⟨(0 : WithLp 2 (ℝ × ℝ)),rfl⟩ isClosed_horizontalAxisSet (0:ℝ),?_,?_⟩
  · intro u hu
    apply exponentialSum_locallyBounded_decompositions
    change u ∈ exponentialGraphSet+horizontalAxisSet at hu
    simpa only [exponentialGraphSet_add_horizontalAxisSet] using hu
  · intro h
    have he : ∀ᶠ a in 𝓝 (0:ℝ),
        (svAdd (fun _ : ℝ ↦ exponentialGraphSet) (fun _ : ℝ ↦ horizontalAxisSet) a).Nonempty ∧
        IsClosed (svAdd (fun _ : ℝ ↦ exponentialGraphSet) (fun _ : ℝ ↦ horizontalAxisSet) a) := by
      simpa only [nhdsWithin_univ] using h.2.1
    exact not_isClosed_exponentialGraphSet_add_horizontalAxisSet (mem_of_mem_nhds he).2

end RW
