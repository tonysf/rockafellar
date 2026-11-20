/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neighborhood formulas for epi-limits

Exercise 7.3 takes the infimum of each function on a neighborhood of the
argument before passing to a numerical lower or upper limit.
-/
import RockafellarWets.Chapter7.EpiLimitCharacterization

open Filter Set Topology

namespace RW

section Neighborhoods

variable {E : Type*} [TopologicalSpace E]

/-- Equation 7(4), using neighborhoods and the usual numerical liminf. -/
theorem epiLowerLimit_eq_iSup_liminf (f : ℕ → E → EReal) (x : E) :
    epiLowerLimit f x =
      ⨆ U ∈ 𝓝 x, liminf (fun n ↦ ⨅ y ∈ U, f n y) atTop := by
  apply le_antisymm
  · apply (epiLowerLimit_le_iff_frequently ..).2
    intro U hU b hb
    have hlt := lt_of_le_of_lt (le_iSup₂ (f := fun U (_ : U ∈ 𝓝 x) ↦
      liminf (fun n ↦ ⨅ y ∈ U, f n y) atTop) U hU) hb
    apply (frequently_lt_of_liminf_lt (h := hlt)).mono
    intro n hn
    obtain ⟨y, hy⟩ := iInf_lt_iff.1 hn
    obtain ⟨hyU, hy⟩ := iInf_lt_iff.1 hy
    exact ⟨y, hyU, hy.le⟩
  · refine iSup₂_le fun U hU ↦ ?_
    rw [liminf_le_iff]
    intro t ht
    obtain ⟨b, hab, hbt⟩ := EReal.exists_between_coe_real ht
    apply ((epiLowerLimit_le_iff_frequently f x _).1 le_rfl U hU b hab).mono
    rintro n ⟨y, hy, hfy⟩
    exact lt_of_le_of_lt (iInf₂_le y hy) (hfy.trans_lt hbt)

/-- Equation 7(5), using neighborhoods and the usual numerical limsup. -/
theorem epiUpperLimit_eq_iSup_limsup (f : ℕ → E → EReal) (x : E) :
    epiUpperLimit f x =
      ⨆ U ∈ 𝓝 x, limsup (fun n ↦ ⨅ y ∈ U, f n y) atTop := by
  apply le_antisymm
  · apply (epiUpperLimit_le_iff_eventually ..).2
    intro U hU b hb
    have hlt := lt_of_le_of_lt (le_iSup₂ (f := fun U (_ : U ∈ 𝓝 x) ↦
      limsup (fun n ↦ ⨅ y ∈ U, f n y) atTop) U hU) hb
    apply (eventually_lt_of_limsup_lt hlt).mono
    intro n hn
    obtain ⟨y, hy⟩ := iInf_lt_iff.1 hn
    obtain ⟨hyU, hy⟩ := iInf_lt_iff.1 hy
    exact ⟨y, hyU, hy.le⟩
  · refine iSup₂_le fun U hU ↦ ?_
    rw [limsup_le_iff]
    intro t ht
    obtain ⟨b, hab, hbt⟩ := EReal.exists_between_coe_real ht
    apply ((epiUpperLimit_le_iff_eventually f x _).1 le_rfl U hU b hab).mono
    rintro n ⟨y, hy, hfy⟩
    exact lt_of_le_of_lt (iInf₂_le y hy) (hfy.trans_lt hbt)

/-- The cofinite-index-set formula in 7(4). -/
theorem epiLowerLimit_eq_iSup_iSup_iInf (f : ℕ → E → EReal) (x : E) :
    epiLowerLimit f x = ⨆ U ∈ 𝓝 x, ⨆ N ∈ (atTop : Filter ℕ), ⨅ n ∈ N, ⨅ y ∈ U, f n y := by
  simp_rw [epiLowerLimit_eq_iSup_liminf, liminf_eq_iSup_iInf]

/-- The cofinite-index-set formula in 7(5). -/
theorem epiUpperLimit_eq_iSup_iInf_iSup (f : ℕ → E → EReal) (x : E) :
    epiUpperLimit f x = ⨆ U ∈ 𝓝 x, ⨅ N ∈ (atTop : Filter ℕ), ⨆ n ∈ N, ⨅ y ∈ U, f n y := by
  simp_rw [epiUpperLimit_eq_iSup_limsup, limsup_eq_iInf_iSup]

/-- Equation 7(6), the joint liminf as the index tends to infinity and the
argument tends to `x`. -/
theorem epiLowerLimit_eq_liminf_prod (f : ℕ → E → EReal) (x : E) :
    epiLowerLimit f x = liminf (fun p : ℕ × E ↦ f p.1 p.2) (atTop ×ˢ 𝓝 x) := by
  apply le_antisymm
  · apply (epiLowerLimit_le_iff_frequently ..).2
    intro U hU b hb
    have hh := frequently_lt_of_liminf_lt (h := hb)
    apply frequently_iff.2
    intro N hN
    obtain ⟨⟨n, y⟩, hn, hfy⟩ := frequently_iff.1 hh (prod_mem_prod hN hU)
    exact ⟨n, hn.1, y, hn.2, hfy.le⟩
  · rw [liminf_le_iff]
    intro t ht
    obtain ⟨b, hab, hbt⟩ := EReal.exists_between_coe_real ht
    apply frequently_iff.2
    intro W hW
    obtain ⟨N, hN, U, hU, hsub⟩ := Filter.mem_prod_iff.1 hW
    obtain ⟨n, hn, y, hy, hfy⟩ := frequently_iff.1
      ((epiLowerLimit_le_iff_frequently ..).1 le_rfl U hU b hab) hN
    exact ⟨(n, y), hsub ⟨hn, hy⟩, hfy.trans_lt hbt⟩

/-- The numerical duality in 7(8): the limsup is the supremum of infima
over infinite index sets. -/
theorem limsup_eq_iSup_infinite_iInf (u : ℕ → EReal) :
    limsup u atTop = ⨆ S : Set ℕ, ⨆ (_ : S.Infinite), ⨅ n ∈ S, u n := by
  apply le_antisymm
  · apply le_of_forall_lt_imp_le_of_dense
    intro b hb
    let S := {n | b < u n}
    have hS : S.Infinite := Nat.frequently_atTop_iff_infinite.1
      (frequently_lt_of_lt_limsup (h := hb))
    have hbound : b ≤ ⨅ n ∈ S, u n := le_iInf₂ fun n (hn : n ∈ S) ↦ hn.le
    exact hbound.trans (le_iSup₂ (κ := fun T : Set ℕ ↦ T.Infinite)
      (f := fun T _ ↦ ⨅ n ∈ T, u n) S hS)
  · refine iSup₂_le fun S hS ↦ ?_
    exact le_limsup_of_frequently_le ((Nat.frequently_atTop_iff_infinite.2 hS).mono
      fun n hn ↦ iInf₂_le (f := fun n (_ : n ∈ S) ↦ u n) n hn)

/-- The companion numerical identity in 7(8), by order duality. -/
theorem liminf_eq_iInf_infinite_iSup (u : ℕ → EReal) :
    liminf u atTop = ⨅ S : Set ℕ, ⨅ (_ : S.Infinite), ⨆ n ∈ S, u n := by
  apply le_antisymm
  · refine le_iInf₂ fun S hS ↦ ?_
    apply liminf_le_of_frequently_le'
    exact (Nat.frequently_atTop_iff_infinite.2 hS).mono fun n hn ↦ le_iSup₂ (f := fun n (_ : n ∈ S) ↦ u n) n hn
  · apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    let S := {n | u n < b}
    have hS : S.Infinite := Nat.frequently_atTop_iff_infinite.1
      (frequently_lt_of_liminf_lt (h := hb))
    exact (iInf₂_le S hS).trans (iSup₂_le fun n (hn : n ∈ S) ↦ hn.le)

/-- Equation 7(7), the upper epi-limit using arbitrary infinite index sets. -/
theorem epiUpperLimit_eq_iSup_infinite_iInf (f : ℕ → E → EReal) (x : E) :
    epiUpperLimit f x = ⨆ U ∈ 𝓝 x, ⨆ S : Set ℕ, ⨆ (_ : S.Infinite),
      ⨅ n ∈ S, ⨅ y ∈ U, f n y := by
  simp_rw [epiUpperLimit_eq_iSup_limsup, limsup_eq_iSup_infinite_iInf]

end Neighborhoods

section Balls

variable {E : Type*} [PseudoMetricSpace E]

/-- Evaluating an antitone neighborhood functional on shrinking closed
balls tends to its supremum over all neighborhoods. -/
private theorem tendsto_closedBall_iSup_nhds (x : E) (L : Set E → EReal) (hL : Antitone L) :
    Tendsto (fun δ ↦ L (Metric.closedBall x δ)) (𝓝[>] (0 : ℝ)) (𝓝 (⨆ U ∈ 𝓝 x, L U)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨U, hU⟩ := lt_iSup_iff.1 ha
    obtain ⟨hUn, haU⟩ := lt_iSup_iff.1 hU
    obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hUn
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with δ hδ
    exact haU.trans_le (hL ((Metric.closedBall_subset_closedBall (le_of_lt hδ)).trans hsub))
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact lt_of_le_of_lt (le_iSup₂ (f := fun U (_ : U ∈ 𝓝 x) ↦ L U)
      (Metric.closedBall x δ) (Metric.closedBall_mem_nhds x hδ)) hb

/-- The shrinking closed-ball limit in 7(4). -/
theorem tendsto_liminf_closedBall_epiLowerLimit (f : ℕ → E → EReal) (x : E) :
    Tendsto (fun δ ↦ liminf (fun n ↦ ⨅ y ∈ Metric.closedBall x δ, f n y) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 (epiLowerLimit f x)) := by
  rw [epiLowerLimit_eq_iSup_liminf]
  apply tendsto_closedBall_iSup_nhds
  intro U V hUV
  refine liminf_le_liminf (.of_forall ?_)
  exact fun n ↦ le_iInf₂ fun y hy ↦ iInf₂_le y (hUV hy)

/-- The shrinking closed-ball limit in 7(5). -/
theorem tendsto_limsup_closedBall_epiUpperLimit (f : ℕ → E → EReal) (x : E) :
    Tendsto (fun δ ↦ limsup (fun n ↦ ⨅ y ∈ Metric.closedBall x δ, f n y) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 (epiUpperLimit f x)) := by
  rw [epiUpperLimit_eq_iSup_limsup]
  apply tendsto_closedBall_iSup_nhds
  intro U V hUV
  refine limsup_le_limsup (.of_forall ?_)
  exact fun n ↦ le_iInf₂ fun y hy ↦ iInf₂_le y (hUV hy)

end Balls

end RW
