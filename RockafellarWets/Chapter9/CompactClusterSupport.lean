/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuous maxima over compact cluster sets
-/

import RockafellarWets.Chapter9.ReachableDerivatives
import RockafellarWets.Chapter8.SupportFunctions

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {ι F : Type*} [MetricSpace F] {l : Filter ι} {g : ι → F}

/-- A compact constraint on values makes the singleton outer limit compact
and nonempty. -/
theorem outerSetLimitAlong_singleton_nonempty_compact [NeBot l] {K : Set F}
    (hK : IsCompact K) (hbound : ∀ᶠ i in l, g i ∈ K) :
    (outerSetLimitAlong l (fun i ↦ {g i})).Nonempty ∧
      IsCompact (outerSetLimitAlong l (fun i ↦ {g i})) := by
  have hsub : outerSetLimitAlong l (fun i ↦ {g i}) ⊆ K :=
    outerSetLimitAlong_subset_of_eventually_subset hK.isClosed
      (hbound.mono fun i hi ↦ singleton_subset_iff.mpr hi)
  exact ⟨(outerSetLimitAlong_inter_nonempty_of_frequently hK
      (hbound.mono fun i hi ↦ ⟨g i,rfl,hi⟩).frequently).mono inter_subset_left,
    hK.of_isClosed_subset (isClosed_outerSetLimitAlong _ _) hsub⟩

theorem eventually_mem_of_outerSetLimitAlong_singleton_subset {K U : Set F}
    (hK : IsCompact K) (hbound : ∀ᶠ i in l, g i ∈ K) (hU : IsOpen U)
    (hsub : outerSetLimitAlong l (fun i ↦ {g i}) ⊆ U) : ∀ᶠ i in l, g i ∈ U := by
  by_contra hn
  have hfreq : ∃ᶠ i in l, ({g i} ∩ (K ∩ Uᶜ)).Nonempty :=
    ((not_eventually.mp hn).and_eventually hbound).mono fun i hi ↦
      ⟨g i,rfl,hi.2,hi.1⟩
  obtain ⟨v,hv,hvK,hvU⟩ := outerSetLimitAlong_inter_nonempty_of_frequently
    (hK.inter_right hU.isClosed_compl) hfreq
  exact hvU (hsub hv)

/-- The upper limit of a continuous scalar observation of a relatively
compact family equals its maximum over the cluster set. -/
theorem exists_max_outerSetLimitAlong_eq_limsup [NeBot l] {K : Set F}
    (hK : IsCompact K) (hbound : ∀ᶠ i in l, g i ∈ K) {H : F → ℝ} (hH : Continuous H) :
    ∃ v ∈ outerSetLimitAlong l (fun i ↦ {g i}),
      limsup (fun i ↦ (H (g i) : EReal)) l = (H v : EReal) ∧
      ∀ z ∈ outerSetLimitAlong l (fun i ↦ {g i}), H z ≤ H v := by
  obtain ⟨hne,hcomp⟩ := outerSetLimitAlong_singleton_nonempty_compact hK hbound
  obtain ⟨v,hv,hmax⟩ := hcomp.exists_isMaxOn hne hH.continuousOn
  refine ⟨v,hv,le_antisymm ?_ ?_,hmax⟩
  · apply (limsup_le_iff).mpr
    intro b hb
    apply eventually_mem_of_outerSetLimitAlong_singleton_subset hK hbound
      (isOpen_lt (continuous_coe_real_ereal.comp hH) continuous_const)
    intro z hz
    exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (hmax hz)) hb
  · apply (le_limsup_iff).mpr
    intro b hb
    have hU : {z | b < (H z : EReal)} ∈ 𝓝 v :=
      (isOpen_lt continuous_const (continuous_coe_real_ereal.comp hH)).mem_nhds hb
    exact (hv _ hU).mono fun i ⟨z,hz,hzi⟩ ↦ (mem_singleton_iff.mp hz) ▸ hzi

end RW
