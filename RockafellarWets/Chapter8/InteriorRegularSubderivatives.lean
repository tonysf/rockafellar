/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Interior formula for regular subderivatives
-/

import RockafellarWets.Chapter6.InteriorTangents
import RockafellarWets.Chapter8.ConvexSubderivativeInteriors

open Filter Function Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The joint numerical upper limit in 8.22. The base converges attentively,
the scale tends to zero through positive reals, and the direction varies. -/
noncomputable def upperDirectionalSlope (f : E → EReal) (x w : E) : EReal :=
  limsup (fun q : (E × ℝ) × E ↦ differenceQuotient f q.1.1 q.1.2 q.2)
    ((attentiveNhds f x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w)

private def uniformForwardStep (C : Set E) (x w : E) : Prop :=
  ∀ᶠ q in ((𝓝[C] x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w), q.1.1 + q.1.2 • q.2 ∈ C

private theorem uniformForwardStep_preimage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E ≃L[ℝ] F) (C : Set F) (x w : E) (h : uniformForwardStep C (L x) (L w)) :
    uniformForwardStep (L ⁻¹' C) x w := by
  have hb : Tendsto L (𝓝[L ⁻¹' C] x) (𝓝[C] (L x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(L.continuous.tendsto x).mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
  have hd : Tendsto (fun q : (E × ℝ) × E ↦ ((L q.1.1, q.1.2), L q.2))
      ((𝓝[L ⁻¹' C] x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w) ((𝓝[C] (L x) ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 (L w)) :=
    ((hb.comp (tendsto_fst.comp tendsto_fst)).prodMk (tendsto_snd.comp tendsto_fst)).prodMk
      ((L.continuous.tendsto w).comp tendsto_snd)
  filter_upwards [hd.eventually h] with q hq
  simpa only [mem_preimage, map_add, map_smul] using hq

private theorem uniformForwardStep_iff {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {C : Set F} {x w : F} (hx : x ∈ C) (hl : IsLocallyClosedAt C x) :
    uniformForwardStep C x w ↔ w ∈ interior (regularTangentCone C x) := by
  rw [mem_interior_regularTangentCone_iff_uniform_recession hx hl]
  constructor
  · intro h
    obtain ⟨P, hP, W, hW, hPW⟩ := mem_prod_iff.mp h
    obtain ⟨U, hU, T, hT, hUT⟩ := mem_prod_iff.mp hP
    obtain ⟨V, hV, hVC⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
    obtain ⟨r, hr, hrT⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hT
    refine ⟨W, hW, V, hV, r/2, half_pos hr, ?_⟩
    intro y hy t ht z hz
    rcases eq_or_lt_of_le ht.1 with rfl | ht'
    · simpa using hy.1
    · exact hPW (a := ((y,t),z)) ⟨hUT ⟨hVC ⟨hy.2, hy.1⟩, hrT ⟨ht', ht.2.trans_lt (half_lt_self hr)⟩⟩, hz⟩
  · rintro ⟨W, hW, V, hV, r, hr, h⟩
    have hy : ∀ᶠ y in 𝓝[C] x, y ∈ C ∩ V :=
      (show ∀ᶠ y in 𝓝[C] x, y ∈ C from self_mem_nhdsWithin).and (mem_nhdsWithin_of_mem_nhds hV)
    have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Icc (0 : ℝ) r :=
      (show ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 r from Ioo_mem_nhdsGT hr).mono fun _ h ↦ ⟨h.1.le, h.2.le⟩
    exact (((tendsto_fst.comp tendsto_fst).eventually hy).and
      (((tendsto_snd.comp tendsto_fst).eventually ht).and (tendsto_snd.eventually hW))).mono
      fun q hq ↦ h q.1.1 hq.1 q.1.2 hq.2.1 q.2 hq.2.2

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private theorem uniformForwardStep_iff_epigraph {f : F → EReal} {x : F} {c : ℝ} {w : F × ℝ}
    (hx : f x = c) (hl : IsLocallyLscAt f x) :
    uniformForwardStep (epigraph f) (x,c) w ↔ w ∈ interior (epigraph (regularSubderivative f x)) := by
  let L := l2ProdEquiv F
  let C := epigraph f
  let p := WithLp.toLp 2 (x,c)
  let d := WithLp.toLp 2 w
  have hc : IsLocallyClosedAt C (x,c) := by simpa [C, hx] using hl.isLocallyClosedAt_epigraph
  have hp : L p ∈ C := hx.le
  have ht : regularTangentCone (L ⁻¹' C) p = L ⁻¹' regularTangentCone C (L p) :=
    regularTangentCone_preimage (Φ' := L) L.toContinuousLinearMap.hasStrictFDerivAt C hp
  have hi : L ⁻¹' interior (regularTangentCone C (L p)) = interior (L ⁻¹' regularTangentCone C (L p)) :=
    L.toHomeomorph.preimage_interior _
  have he := uniformForwardStep_iff (w := d) (show p ∈ L ⁻¹' C from hp)
    (IsLocallyClosedAt.preimage_continuousLinearEquiv L hc)
  rw [ht, ← hi] at he
  rw [epigraph_regularSubderivative_eq_regularTangentCone hx hl.lowerSemicontinuousAt]
  constructor
  · exact fun h ↦ he.mp (uniformForwardStep_preimage L C p d h)
  · intro h
    have hs := uniformForwardStep_preimage L.symm (L ⁻¹' C) (x,c) w (he.mpr h)
    simpa only [preimage_preimage, ContinuousLinearEquiv.self_comp_symm, preimage_id_eq] using hs

private theorem upperDirectionalSlope_le_of_interior_epigraph {f : F → EReal} {x w : F} {c a : ℝ}
    (hx : f x = c) (hl : IsLocallyLscAt f x) (h : (w,a) ∈ interior (epigraph (regularSubderivative f x))) :
    upperDirectionalSlope f x w ≤ (a : EReal) := by
  let A := (attentiveNhds f x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w
  have hs := (uniformForwardStep_iff_epigraph hx hl).mpr h
  have hm : Tendsto (fun q : (F × ℝ) × F ↦ (((q.1.1, (f q.1.1).toReal), q.1.2), (q.2, a))) A
      ((𝓝[epigraph f] (x,c) ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 (w,a)) :=
    (((tendsto_graph_attentiveNhds hx).comp (tendsto_fst.comp tendsto_fst)).prodMk
      (tendsto_snd.comp tendsto_fst)).prodMk (tendsto_snd.prodMk_nhds tendsto_const_nhds)
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hm.eventually hs, (tendsto_fst.comp tendsto_fst).eventually (eventually_finite_attentiveNhds hx),
    (tendsto_snd.comp tendsto_fst).eventually (show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin)]
    with q hq hfin ht
  exact (differenceQuotient_le_coe_iff hfin ht).mpr hq

/-- At any real test height the strict upper slope condition is equivalent
to an interior regular tangent direction of the epigraph. -/
theorem upperDirectionalSlope_lt_iff {f : F → EReal} {x w : F} {c a : ℝ} (hx : f x = c)
    (hl : IsLocallyLscAt f x) :
    upperDirectionalSlope f x w < (a : EReal) ↔
      w ∈ interior (effectiveDomain (regularSubderivative f x)) ∧ regularSubderivative f x w < (a : EReal) := by
  have hc := convex_epigraph_regularSubderivative hx hl.lowerSemicontinuousAt
  constructor
  · intro h
    obtain ⟨r, hr, hra⟩ := EReal.exists_between_coe_real h
    have hev := eventually_lt_of_limsup_lt hr
    apply (mem_interior_epigraph_iff_of_convex hc).mp
    apply (uniformForwardStep_iff_epigraph hx hl).mp
    let A := (𝓝[epigraph f] (x,c) ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 (w,a)
    have hb := tendsto_fst_epigraph_attentiveNhds hx hl.lowerSemicontinuousAt
    have hm : Tendsto (fun q : ((F × ℝ) × ℝ) × (F × ℝ) ↦ ((q.1.1.1, q.1.2), q.2.1)) A
        ((attentiveNhds f x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w) :=
      ((hb.comp (tendsto_fst.comp tendsto_fst)).prodMk (tendsto_snd.comp tendsto_fst)).prodMk
        ((continuous_fst.tendsto (w,a)).comp tendsto_snd)
    have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have hc' : ∀ᶠ y in 𝓝[epigraph f] (x,c), y ∈ epigraph f := self_mem_nhdsWithin
    have ha : ∀ᶠ z : F × ℝ in 𝓝 (w,a), r < z.2 := (continuous_snd.tendsto (w,a)).eventually (lt_mem_nhds (EReal.coe_lt_coe_iff.mp hra))
    filter_upwards [hm.eventually hev, (tendsto_fst.comp tendsto_fst).eventually (hb.eventually (eventually_finite_attentiveNhds hx)),
      (tendsto_fst.comp tendsto_fst).eventually hc', (tendsto_snd.comp tendsto_fst).eventually ht,
      tendsto_snd.eventually ha] with q hq hfin hy hpos hheight
    have hval := (differenceQuotient_le_coe_iff hfin hpos).mp hq.le
    have hyval : (f q.1.1.1).toReal ≤ q.1.1.2 := EReal.coe_le_coe_iff.mp (hfin ▸ hy)
    exact hval.trans (EReal.coe_le_coe_iff.mpr (add_le_add hyval (mul_le_mul_of_nonneg_left hheight.le hpos.le)))
  · intro ⟨hw, h⟩
    obtain ⟨r, hr, hra⟩ := EReal.exists_between_coe_real h
    exact (upperDirectionalSlope_le_of_interior_epigraph hx hl ((mem_interior_epigraph_iff_of_convex hc).mpr
      ⟨hw, hr⟩)).trans_lt hra

/-- **Theorem 8.22.** The directions of upper slope below infinity are
precisely the interior of the effective domain of the regular subderivative. -/
theorem interior_effectiveDomain_regularSubderivative {f : F → EReal} {x : F} {c : ℝ} (hx : f x = c)
    (hl : IsLocallyLscAt f x) :
    interior (effectiveDomain (regularSubderivative f x)) = effectiveDomain (upperDirectionalSlope f x) := by
  ext w
  constructor
  · intro hw
    obtain ⟨a, ha, -⟩ := EReal.exists_between_coe_real
      (show regularSubderivative f x w < ⊤ from interior_subset (s := effectiveDomain _) hw)
    exact ((upperDirectionalSlope_lt_iff hx hl).mpr ⟨hw, ha⟩).trans (EReal.coe_lt_top a)
  · intro hw
    obtain ⟨a, ha, -⟩ := EReal.exists_between_coe_real (show upperDirectionalSlope f x w < ⊤ from hw)
    exact ((upperDirectionalSlope_lt_iff hx hl).mp ha).1

theorem regularSubderivative_eq_upperDirectionalSlope {f : F → EReal} {x w : F} {c : ℝ} (hx : f x = c)
    (hl : IsLocallyLscAt f x) (hw : w ∈ effectiveDomain (upperDirectionalSlope f x)) :
    regularSubderivative f x w = upperDirectionalSlope f x w := by
  have hi := (interior_effectiveDomain_regularSubderivative hx hl).symm ▸ hw
  apply le_antisymm <;> by_contra! h
  · obtain ⟨a, ha, ha'⟩ := EReal.exists_between_coe_real h
    exact ha'.asymm ((upperDirectionalSlope_lt_iff hx hl).mp ha).2
  · obtain ⟨a, ha, ha'⟩ := EReal.exists_between_coe_real h
    exact ha'.asymm ((upperDirectionalSlope_lt_iff hx hl).mpr ⟨hi, ha⟩)

/-- Outside the closure of the nonempty set of interior directions, the
regular subderivative has value positive infinity. -/
theorem regularSubderivative_eq_top_off_closure {f : F → EReal} {x w : F} {c : ℝ} (hx : f x = c)
    (hl : IsLocallyLscAt f x) (hne : (effectiveDomain (upperDirectionalSlope f x)).Nonempty)
    (hw : w ∉ closure (effectiveDomain (upperDirectionalSlope f x))) : regularSubderivative f x w = ⊤ := by
  rw [← interior_effectiveDomain_regularSubderivative hx hl] at hne hw
  rw [(convex_effectiveDomain_of_convex_epigraph (convex_epigraph_regularSubderivative hx hl.lowerSemicontinuousAt)
    ).closure_interior_eq_closure_of_nonempty_interior hne] at hw
  exact top_unique (le_of_not_gt (fun h ↦ hw (subset_closure h)))

/-- Along a segment ending at any point of the effective domain, a closed
convex extended-real function converges radially to its value at the other endpoint. -/
theorem tendsto_radial_of_lsc_convex_epigraph {g : E → EReal} (hg : Convex ℝ (epigraph g))
    (hl : LowerSemicontinuous g) (w : E) {v : E} (hv : v ∈ effectiveDomain g) :
    Tendsto (fun t : ℝ ↦ g ((1-t) • w + t • v)) (𝓝[>] 0) (𝓝 (g w)) := by
  have hp : Continuous (fun t : ℝ ↦ (1-t) • w + t • v) :=
    ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ ↦ (1-t) • w + t • v) (𝓝[>] 0) (𝓝 w) := by
    simpa using (hp.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply tendsto_order.mpr
  refine ⟨fun a ha ↦ ht.eventually (hl w a ha), ?_⟩
  intro b hb
  obtain ⟨r, hr, hrb⟩ := EReal.exists_between_coe_real hb
  obtain ⟨s, hs, -⟩ := EReal.exists_between_coe_real (show g v < ⊤ from hv)
  have hline : Continuous (fun t : ℝ ↦ (1-t)*r + t*s) :=
    ((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.mul continuous_const)
  have hlim : Tendsto (fun t : ℝ ↦ (((1-t)*r + t*s : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (r : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa using (hline.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ), hlim.eventually_lt_const hrb] with t h01 htb
  exact (show g ((1-t) • w + t • v) ≤ (((1-t)*r + t*s : ℝ) : EReal) from
    hg (show (w,r) ∈ epigraph g from hr.le) (show (v,s) ∈ epigraph g from hs.le)
      (sub_nonneg.mpr h01.2.le) h01.1.le (sub_add_cancel 1 t)).trans_lt htb

/-- **Theorem 8.22**, the boundary formula. Along a segment entering the
interior the numerical upper slopes converge to the boundary value. -/
theorem tendsto_upperDirectionalSlope_at_boundary {f : F → EReal} {x w v : F} {c : ℝ} (hx : f x = c)
    (hl : IsLocallyLscAt f x) (hw : w ∈ frontier (effectiveDomain (upperDirectionalSlope f x)))
    (hv : v ∈ effectiveDomain (upperDirectionalSlope f x)) :
    Tendsto (fun t : ℝ ↦ upperDirectionalSlope f x ((1-t) • w + t • v)) (𝓝[>] 0) (𝓝 (regularSubderivative f x w)) := by
  let D := effectiveDomain (regularSubderivative f x)
  have he := interior_effectiveDomain_regularSubderivative hx hl
  have hwD : w ∈ closure D := closure_mono interior_subset (show w ∈ closure (interior D) from he.symm ▸ hw.1)
  have hvD : v ∈ interior D := he.symm ▸ hv
  have hc := convex_epigraph_regularSubderivative hx hl.lowerSemicontinuousAt
  apply (tendsto_radial_of_lsc_convex_epigraph hc (lowerSemicontinuous_regularSubderivative f x) w
    (interior_subset hvD)).congr'
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact regularSubderivative_eq_upperDirectionalSlope hx hl (he ▸ (convex_effectiveDomain_of_convex_epigraph hc
    ).combo_closure_interior_mem_interior hwD hvD (sub_nonneg.mpr ht.2.le) ht.1 (sub_add_cancel 1 t))

end Euclidean

end RW
