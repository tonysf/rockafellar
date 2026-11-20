/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Relationships between lower and regular subderivatives
-/

import RockafellarWets.Chapter7.EpigraphAddition
import RockafellarWets.Chapter7.SubdifferentialRegularity
import RockafellarWets.Chapter8.RegularSubderivatives

open Filter Function Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lowerSemicontinuous_regularSubderivative (f : E → EReal) (x : E) :
    LowerSemicontinuous (regularSubderivative f x) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [epigraph_regularSubderivative]
  exact isClosed_innerSetLimitAlong ..

/-- The positive homogeneity of the regular subderivative does not require
lower semicontinuity at its finite base point. -/
theorem positivelyHomogeneous_regularSubderivative {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    PositivelyHomogeneous (regularSubderivative f x) := by
  rw [positivelyHomogeneous_iff_isCone_epigraph, epigraph_regularSubderivative_eq_inner_blowUp hx]
  let A := attentiveNhds f x
  let T := 𝓝[>] (0 : ℝ)
  constructor
  · intro V hV
    filter_upwards [tendsto_fst.eventually (eventually_finite_attentiveNhds hx)] with p hp
    exact ⟨0, ⟨(p.1, (f p.1).toReal), hp.le, by simp⟩, mem_of_mem_nhds hV⟩
  · intro w hw r hr V hV
    have hmap : Tendsto (fun p : E × ℝ ↦ (p.1, r * p.2)) (A ×ˢ T) (A ×ˢ T) := by
      apply tendsto_fst.prodMk
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, tendsto_snd.eventually ((show ∀ᶠ s in T, 0 < s from self_mem_nhdsWithin).mono
        fun s hs ↦ mul_pos hr hs)⟩
      have ht : Tendsto Prod.snd (A ×ˢ T) (𝓝 0) := tendsto_snd.mono_right nhdsWithin_le_nhds
      simpa only [mul_zero] using ht.const_mul r
    have hV' : (fun z : E × ℝ ↦ r • z) ⁻¹' V ∈ 𝓝 w := (continuous_const_smul r).continuousAt hV
    filter_upwards [hmap.eventually (hw _ hV')] with p hhit
    obtain ⟨z, ⟨q, hq, rfl⟩, hqV⟩ := hhit
    exact ⟨r • ((r * p.2)⁻¹ • (q - (p.1, (f p.1).toReal))), ⟨q, hq, by
      rw [mul_inv, smul_smul, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]⟩, hqV⟩

/-- **Theorem 8.18**, the lower subderivative is bounded above by the
regular subderivative, even without lower semicontinuity. -/
theorem subderivative_le_regularSubderivative {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    subderivative f x ≤ regularSubderivative f x := by
  apply epigraph_subset_epigraph_iff.mp
  rw [epigraph_regularSubderivative, epigraph_subderivative_eq_tangentCone hx,
    ← outerSetLimitAlong_epigraph_differenceQuotient hx]
  have hbase : Tendsto (fun _ : ℝ ↦ x) (𝓝[>] (0 : ℝ)) (attentiveNhds f x) :=
    tendsto_attentiveNhds_iff.mpr ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  have hmap := hbase.prodMk (tendsto_id (x := 𝓝[>] (0 : ℝ)))
  exact (innerSetLimitAlong_mono_filter hmap _).trans (innerSetLimitAlong_subset_outerSetLimitAlong ..)

theorem lowerSemicontinuous_positivelyHomogeneous_subderivative {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) : LowerSemicontinuous (subderivative f x) ∧ PositivelyHomogeneous (subderivative f x) := by
  have hm : (x, c) ∈ epigraph f := hx.le
  constructor
  · apply lowerSemicontinuous_of_isClosed_epigraph_ereal
    rw [epigraph_subderivative_eq_tangentCone hx]
    exact isClosed_tangentCone ..
  · rw [positivelyHomogeneous_iff_isCone_epigraph, epigraph_subderivative_eq_tangentCone hx]
    exact isCone_tangentCone hm

theorem convex_epigraph_regularSubderivative {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (hl : LowerSemicontinuousAt f x) : Convex ℝ (epigraph (regularSubderivative f x)) := by
  rw [epigraph_regularSubderivative_eq_regularTangentCone hx hl]
  exact convex_regularTangentCone (show (x, c) ∈ epigraph f from hx.le)

/-- Subadditivity of the regular subderivative in the book's inf-addition
convention, including opposite infinite values. -/
theorem regularSubderivative_subadditive {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (hl : LowerSemicontinuousAt f x) (u v : E) :
    regularSubderivative f x (u + v) ≤ infAddition (regularSubderivative f x u) (regularSubderivative f x v) := by
  by_contra! h
  obtain ⟨b, hb, hb'⟩ := EReal.exists_between_coe_real h
  obtain ⟨r, s, hr, hs, rfl⟩ := (infAddition_le_coe_iff ..).mp hb.le
  have hcone := isCone_epigraph_of_positivelyHomogeneous (positivelyHomogeneous_regularSubderivative hx)
  exact hb'.not_ge ((hcone.convex_iff_add_mem.mp (convex_epigraph_regularSubderivative hx hl))
    (x := (u, r)) (y := (v, s)) hr hs)

omit [NormedSpace ℝ E] in
theorem IsLocallyLscAt.lowerSemicontinuousAt {f : E → EReal} {x : E} (h : IsLocallyLscAt f x) :
    LowerSemicontinuousAt f x := by
  obtain ⟨hbot, htop, δ, hδ, hlevel⟩ := h
  have hfx := EReal.coe_toReal htop hbot
  intro a ha
  obtain ⟨b, hab, hbx⟩ := EReal.exists_between_coe_real ha
  have hbc : b < (f x).toReal := EReal.coe_lt_coe_iff.mp (hfx.symm ▸ hbx)
  have hopen := (hlevel b (by linarith)).isOpen_compl
  have hxm : x ∈ (closedBall x δ ∩ {y | f y ≤ b})ᶜ := fun h' ↦ hbx.not_ge h'.2
  filter_upwards [hopen.mem_nhds hxm, closedBall_mem_nhds x hδ] with y hy hdy
  exact hab.trans (lt_of_not_ge fun hle ↦ hy ⟨hdy, hle⟩)

theorem tangentCone_epigraph_mono_base_height (f : E → EReal) (x : E) {a b : ℝ} (hab : a ≤ b) :
    tangentCone (epigraph f) (x, a) ⊆ tangentCone (epigraph f) (x, b) := by
  rw [tangentCone_eq_outerSetLimitAlong, tangentCone_eq_outerSetLimitAlong]
  exact outerSetLimitAlong_mono (blowUp_epigraph_mono_base_height f x hab)

/-- **Theorem 8.18**, formula 8(9) as the epigraph inner limit over
attentively approaching base points. -/
theorem epigraph_regularSubderivative_eq_inner_epigraph_subderivative [FiniteDimensional ℝ E]
    {f : E → EReal} {x : E} (h : IsLocallyLscAt f x) :
    epigraph (regularSubderivative f x) =
      innerSetLimitAlong (attentiveNhds f x) (fun y ↦ epigraph (subderivative f y)) := by
  have hx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal h.2.1 h.1).symm
  have hsub : (fun y ↦ epigraph (subderivative f y)) =ᶠ[attentiveNhds f x]
      (fun y ↦ tangentCone (epigraph f) (y, (f y).toReal)) :=
    (eventually_finite_attentiveNhds hx).mono fun _ hy ↦ epigraph_subderivative_eq_tangentCone hy
  rw [epigraph_regularSubderivative_eq_regularTangentCone hx h.lowerSemicontinuousAt,
    regularTangentCone_eq_svInnerLimitWithin_tangentCone (show (x, (f x).toReal) ∈ epigraph f from hx.le) h.isLocallyClosedAt_epigraph,
    innerSetLimitAlong_congr hsub]
  have hproj := tendsto_fst_epigraph_attentiveNhds hx h.lowerSemicontinuousAt
  apply Set.Subset.antisymm (innerSetLimitAlong_mono_filter (tendsto_graph_attentiveNhds hx) _)
  intro w hw V hV
  filter_upwards [hproj.eventually (hw V hV), hproj.eventually (eventually_finite_attentiveNhds hx),
    self_mem_nhdsWithin] with y hhit hy hep
  obtain ⟨z, hz, hzV⟩ := hhit
  have hle : (f y.1).toReal ≤ y.2 := EReal.coe_le_coe_iff.mp (hy ▸ (show f y.1 ≤ (y.2 : EReal) from hep))
  exact ⟨z, tangentCone_epigraph_mono_base_height f y.1 hle hz, hzV⟩

end RW
