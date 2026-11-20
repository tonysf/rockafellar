/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Regular subderivatives and regular epigraph tangents
-/

import RockafellarWets.Chapter6.RegularTangents
import RockafellarWets.Chapter7.EpiDerivatives
import RockafellarWets.Chapter8.Subgradients

open Filter Function Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 8.16.** The upper epi-limit of the difference quotients
as the base point approaches attentively and the positive scale tends to zero. -/
noncomputable def regularSubderivative (f : E → EReal) (x : E) : E → EReal :=
  epiBoundary (innerSetLimitAlong ((attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ))
    fun p ↦ epigraph (differenceQuotient f p.1 p.2))

theorem epigraph_regularSubderivative (f : E → EReal) (x : E) :
    epigraph (regularSubderivative f x) =
      innerSetLimitAlong ((attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ))
        (fun p ↦ epigraph (differenceQuotient f p.1 p.2)) :=
  epigraph_epiBoundary (isClosed_innerSetLimitAlong ..) fun _ _ _ ↦ innerSetLimitAlong_epigraph_upward _

omit [NormedSpace ℝ E] in
theorem eventually_finite_attentiveNhds {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    ∀ᶠ y in attentiveNhds f x, f y = (((f y).toReal : ℝ) : EReal) := by
  have ht : Tendsto f (attentiveNhds f x) (𝓝 (f x)) := (tendsto_attentiveNhds_iff.mp tendsto_id).2
  rw [hx] at ht
  filter_upwards [ht.eventually (Ioo_mem_nhds (EReal.bot_lt_coe c) (EReal.coe_lt_top c))] with y hy
  exact (EReal.coe_toReal hy.2.ne hy.1.ne').symm

omit [NormedSpace ℝ E] in
theorem tendsto_graph_attentiveNhds {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    Tendsto (fun y ↦ (y, (f y).toReal)) (attentiveNhds f x) (𝓝[epigraph f] (x, c)) := by
  obtain ⟨hy, hv⟩ := tendsto_attentiveNhds_iff.mp (show Tendsto id (attentiveNhds f x) (attentiveNhds f x) from tendsto_id)
  rw [hx] at hv
  have hreal := (EReal.tendsto_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).comp hv
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨hy.prodMk_nhds (by simpa only [EReal.toReal_coe] using hreal),
    (eventually_finite_attentiveNhds hx).mono fun _ h ↦ h.le⟩

omit [NormedSpace ℝ E] in
/-- Lower semicontinuity at a finite base point makes every convergent
epigraph selection approach attentively in its argument. -/
theorem tendsto_fst_epigraph_attentiveNhds {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (hl : LowerSemicontinuousAt f x) :
    Tendsto Prod.fst (𝓝[epigraph f] (x, c)) (attentiveNhds f x) := by
  have ht : Tendsto (id : E × ℝ → E × ℝ) (𝓝[epigraph f] (x, c)) (𝓝 (x, c)) := nhdsWithin_le_nhds
  have hu := (continuous_fst.tendsto (x, c)).comp ht
  have hv := EReal.tendsto_coe.mpr ((continuous_snd.tendsto (x, c)).comp ht)
  apply tendsto_attentiveNhds_iff.mpr
  refine ⟨hu, tendsto_order.mpr ⟨fun a ha ↦ hu.eventually (hl a ha), ?_⟩⟩
  intro b hb
  rw [hx] at hb
  filter_upwards [self_mem_nhdsWithin, hv.eventually_lt_const hb] with y hy ht
  exact (show f y.1 ≤ (y.2 : EReal) from hy).trans_lt ht

theorem epigraph_regularSubderivative_eq_inner_blowUp {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    epigraph (regularSubderivative f x) =
      innerSetLimitAlong ((attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ))
        (fun p ↦ blowUp (epigraph f) (p.1, (f p.1).toReal) p.2) := by
  rw [epigraph_regularSubderivative]
  apply innerSetLimitAlong_congr
  filter_upwards [tendsto_fst.eventually (eventually_finite_attentiveNhds hx),
    tendsto_snd.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp ht
  exact epigraph_differenceQuotient hp ht

/-- The inclusion from regular epigraph tangents to the epigraph of the
regular subderivative requires only a finite base value. -/
theorem regularTangentCone_epigraph_subset {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    regularTangentCone (epigraph f) (x, c) ⊆ epigraph (regularSubderivative f x) := by
  rw [epigraph_regularSubderivative_eq_inner_blowUp hx]
  let Q := fun p : E × ℝ ↦ ((p.1, (f p.1).toReal), p.2)
  have hmap : Tendsto Q ((attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝[epigraph f] (x, c) ×ˢ 𝓝[>] (0 : ℝ)) :=
    ((tendsto_graph_attentiveNhds hx).comp tendsto_fst).prodMk tendsto_snd
  exact innerSetLimitAlong_mono_filter hmap _

/-- Raising the height of an epigraph base point enlarges every blow-up
around it, since its entire vertical upward ray remains in the epigraph. -/
theorem blowUp_epigraph_mono_base_height (f : E → EReal) (x : E) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    blowUp (epigraph f) (x, a) t ⊆ blowUp (epigraph f) (x, b) t := by
  rintro w ⟨⟨y, d⟩, hy, rfl⟩
  refine ⟨(y, d + (b - a)), hy.trans (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right (sub_nonneg.mpr hab))), ?_⟩
  simp only [Prod.mk_sub_mk, show d + (b - a) - b = d - a by ring]

/-- **Theorem 8.17(a).** At a finite point of lower semicontinuity the
regular epigraph tangent is exactly the epigraph of the regular subderivative. -/
theorem epigraph_regularSubderivative_eq_regularTangentCone {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (hl : LowerSemicontinuousAt f x) :
    epigraph (regularSubderivative f x) = regularTangentCone (epigraph f) (x, c) := by
  apply Set.Subset.antisymm _ (regularTangentCone_epigraph_subset hx)
  rw [epigraph_regularSubderivative_eq_inner_blowUp hx]
  intro w hw V hV
  let Q := fun p : (E × ℝ) × ℝ ↦ (p.1.1, p.2)
  have hmap : Tendsto Q (𝓝[epigraph f] (x, c) ×ˢ 𝓝[>] (0 : ℝ))
      ((attentiveNhds f x) ×ˢ 𝓝[>] (0 : ℝ)) :=
    ((tendsto_fst_epigraph_attentiveNhds hx hl).comp tendsto_fst).prodMk tendsto_snd
  filter_upwards [hmap.eventually (hw V hV),
    tendsto_fst.eventually (self_mem_nhdsWithin : epigraph f ∈ 𝓝[epigraph f] (x, c)),
    (tendsto_fst.comp hmap).eventually (eventually_finite_attentiveNhds hx)] with p hhit hpm hfinite
  obtain ⟨z, hz, hzV⟩ := hhit
  have hh : (f p.1.1).toReal ≤ p.1.2 :=
    EReal.coe_le_coe_iff.mp (hfinite ▸ (show f p.1.1 ≤ (p.1.2 : EReal) from hpm))
  exact ⟨z, blowUp_epigraph_mono_base_height f p.1.1 hh p.2 hz, hzV⟩

end RW
