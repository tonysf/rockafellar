/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Neighborhood formula for regular subderivatives
-/

import RockafellarWets.Chapter8.RegularSubderivatives

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The upper epi-limit first takes the infimum over a neighborhood of the
direction and then the numerical limsup over the base point and scale. -/
theorem regularSubderivative_eq_iSup_limsup (f : E → EReal) (x w : E) :
    regularSubderivative f x w = ⨆ V ∈ 𝓝 w,
      limsup (fun p : E × ℝ ↦ ⨅ v ∈ V, differenceQuotient f p.1 p.2 v)
        ((attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ)) := by
  let L := (attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ)
  let q := fun (p : E × ℝ) ↦ differenceQuotient f p.1 p.2
  let H := fun V : Set E ↦ limsup (fun p ↦ ⨅ v ∈ V, q p v) L
  change regularSubderivative f x w = ⨆ V ∈ 𝓝 w, H V
  apply le_antisymm
  · by_contra! h
    obtain ⟨b, hb, hb'⟩ := EReal.exists_between_coe_real h
    apply hb'.not_ge
    change (w, b) ∈ epigraph (regularSubderivative f x)
    rw [epigraph_regularSubderivative]
    intro W hW
    obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.mp hW
    have hlt := (le_iSup₂ (f := fun U (_ : U ∈ 𝓝 w) ↦ H U) U hU).trans_lt hb
    filter_upwards [eventually_lt_of_limsup_lt hlt] with p hp
    obtain ⟨v, hv⟩ := iInf_lt_iff.mp hp
    obtain ⟨hvU, hvb⟩ := iInf_lt_iff.mp hv
    exact ⟨(v, b), hvb.le, hsub ⟨hvU, mem_of_mem_nhds hV⟩⟩
  · refine iSup₂_le fun V hV ↦ ?_
    change limsup _ L ≤ _
    rw [limsup_le_iff]
    intro b hb
    obtain ⟨a, ha, hab⟩ := EReal.exists_between_coe_real hb
    obtain ⟨r, hr, hra⟩ := EReal.exists_between_coe_real ha
    have hm : (w, r) ∈ epigraph (regularSubderivative f x) := hr.le
    rw [epigraph_regularSubderivative] at hm
    apply (hm (V ×ˢ Iio a) (prod_mem_nhds hV (Iio_mem_nhds (EReal.coe_lt_coe_iff.mp hra)))).mono
    rintro p ⟨⟨v, t⟩, hvt, hv, ht⟩
    exact (iInf₂_le v hv).trans_lt (hvt.trans_lt ((EReal.coe_lt_coe_iff.mpr ht).trans hab))

/-- **Formula 8(8)**, the limit over shrinking closed direction balls. -/
theorem tendsto_limsup_closedBall_regularSubderivative (f : E → EReal) (x w : E) :
    Tendsto (fun δ ↦ limsup (fun p : E × ℝ ↦ ⨅ v ∈ closedBall w δ, differenceQuotient f p.1 p.2 v)
      ((attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 (regularSubderivative f x w)) := by
  rw [regularSubderivative_eq_iSup_limsup]
  let H := fun V : Set E ↦ limsup (fun p : E × ℝ ↦ ⨅ v ∈ V, differenceQuotient f p.1 p.2 v)
    ((attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ))
  have hH : Antitone H := by
    intro U V hUV
    exact limsup_le_limsup (.of_forall fun p ↦ le_iInf₂ fun v hv ↦ iInf₂_le v (hUV hv))
  change Tendsto (fun δ ↦ H (closedBall w δ)) _ (𝓝 (⨆ V ∈ 𝓝 w, H V))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨V, ht⟩ := lt_iSup_iff.mp ha
    obtain ⟨hV, haV⟩ := lt_iSup_iff.mp ht
    obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hV
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with δ hδ
    exact haV.trans_le (hH ((closedBall_subset_closedBall hδ.le).trans hsub))
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (le_iSup₂ (f := fun V (_ : V ∈ 𝓝 w) ↦ H V) (closedBall w δ) (closedBall_mem_nhds w hδ)).trans_lt hb

end RW
