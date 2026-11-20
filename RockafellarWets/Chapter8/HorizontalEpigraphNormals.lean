/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Horizontal epigraph normals and horizon subgradients

First approximate normals to a closed epigraph by proximal normals. A
horizontal proximal normal above a finite fiber moves down to its graph
point, where downward projection perturbations approximate it by
negative-height normals. Local closedness transfers this construction from
the closed epigraph hull to the original epigraph.
-/

import RockafellarWets.Chapter8.NegativeHeightProjections
import RockafellarWets.Chapter8.SubderivativeRelationships
import RockafellarWets.Chapter6.NormalApproximation
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter7.EpiLimitCharacterization

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x v : E} {c : ℝ}

omit [FiniteDimensional ℝ E] in
private theorem horizontal_proximal_normal_lower_height {y u : E} {r d : ℝ}
    (hr : d ≤ r) (hd : f y = d)
    (hn : WithLp.toLp 2 (u,(0:ℝ)) ∈ proximalNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (y,r))) :
    WithLp.toLp 2 (u,(0:ℝ)) ∈ proximalNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (y,d)) := by
  obtain ⟨_,k,hk,h⟩ := mem_proximalNormalCone_iff_quadratic_support.mp hn
  apply mem_proximalNormalCone_iff_quadratic_support.mpr
  refine ⟨hd.le,k,hk,?_⟩
  rintro z hz
  obtain ⟨⟨w,s⟩,rfl⟩ := (WithLp.toLp_surjective 2) z
  have h' := h (WithLp.toLp 2 (w,s+(r-d))) (show f w ≤ _ from
    (show f w ≤ (s : EReal) from hz).trans (EReal.coe_le_coe_iff.mpr (by linarith)))
  have he : WithLp.toLp 2 (w,s+(r-d)) - WithLp.toLp 2 (y,r) =
      WithLp.toLp 2 (w,s) - WithLp.toLp 2 (y,d) := by
    apply WithLp.ofLp_injective
    ext <;> simp
    ring
  rwa [he] at h'

/-- Normals of the closed epigraph at a finite graph point are limits of
strictly negative-height regular normals. -/
theorem mem_closure_negativeNormalGraph_of_normal_of_lsc (hl : LowerSemicontinuous f)
    (hx : f x = c) {nrm : WithLp 2 (E × ℝ)}
    (hn : nrm ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c))) :
    (WithLp.toLp 2 (x,c),nrm) ∈ closure (negativeEpigraphNormalGraph f) := by
  have hf : IsClosed (euclideanEpigraph f) :=
    (isClosed_epigraph_of_lsc_ereal f hl).preimage (l2ProdEquiv E).continuous
  obtain ⟨p,q,hp,hq,hpl,hql⟩ := exists_seq_mem_proximalNormalCone_tendsto_of_mem_normalCone hf hn
  let y := fun i ↦ (p i).ofLp.1
  let r := fun i ↦ (p i).ofLp.2
  have hpr := ((l2ProdEquiv E).continuous.tendsto _).comp hpl
  change Tendsto (fun i ↦ (p i).ofLp) atTop (𝓝 (x,c)) at hpr
  rw [nhds_prod_eq] at hpr
  have hy : Tendsto y atTop (𝓝 x) := hpr.fst
  have hr : Tendsto r atTop (𝓝 c) := hpr.snd
  have hval : Tendsto (fun i ↦ f (y i)) atTop (𝓝 (c : EReal)) := by
    apply tendsto_order.mpr
    refine ⟨fun a ha ↦ hy.eventually (hl x a (show a < f x from hx.symm ▸ ha)), fun a ha ↦ ?_⟩
    exact (((continuous_coe_real_ereal.tendsto c).comp hr).eventually_lt_const ha).mono
      fun i hi ↦ (show f (y i) ≤ (r i : EReal) from hp i).trans_lt hi
  let d := fun i ↦ (f (y i)).toReal
  have hd : Tendsto d atTop (𝓝 c) := by
    simpa using (EReal.tendsto_toReal (EReal.coe_ne_top c) (EReal.coe_ne_bot c)).comp hval
  have hfin : ∀ᶠ i in atTop, f (y i) = (d i : EReal) := by
    filter_upwards [hval.eventually_mem (lt_mem_nhds (EReal.bot_lt_coe c))] with i hi
    exact (EReal.coe_toReal ((show f (y i) ≤ (r i : EReal) from hp i).trans_lt
      (EReal.coe_lt_top _)).ne hi.ne').symm
  let a := fun i ↦ WithLp.toLp 2 (y i,d i)
  have ha : Tendsto a atTop (𝓝 (WithLp.toLp 2 (x,c))) :=
    ((l2ProdEquiv E).symm.continuous.tendsto _).comp (hy.prodMk_nhds hd)
  apply isClosed_closure.mem_of_tendsto (ha.prodMk_nhds hql)
  filter_upwards [hfin] with i hi
  let b := (q i).ofLp.2
  let u := (q i).ofLp.1
  have hri : f (y i) ≤ (r i : EReal) := hp i
  have hni := proximalNormalCone_subset_regularNormalCone (hq i)
  have hb : b ≤ 0 := vertical_nonpos_of_mem_regularNormalCone_epigraph
    (v := u) (x := y i) (c := r i) hni
  rcases hb.lt_or_eq with hlt | heq
  · have hval' := value_eq_of_mem_regularNormalCone_epigraph_of_neg (x := y i) (v := u)
      (c := r i) hni hlt
    have hdi : d i = r i := EReal.coe_injective (hi.symm.trans hval')
    apply subset_closure
    refine ⟨?_, hlt⟩
    simpa only [a,hdi] using hni
  · have hq' : q i = WithLp.toLp 2 (u,(0:ℝ)) := by
      apply WithLp.ofLp_injective
      exact Prod.ext rfl heq
    have hh : WithLp.toLp 2 (u,(0:ℝ)) ∈ proximalNormalCone (euclideanEpigraph f)
        (WithLp.toLp 2 (y i,r i)) := hq' ▸ hq i
    exact hq'.symm ▸ horizontal_proximal_mem_closure_negativeNormalGraph hf hi
      (horizontal_proximal_normal_lower_height (EReal.coe_le_coe_iff.mp (hi ▸ hri)) hi hh)

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
/-- The closed epigraph hull has the original value at any point of lower
semicontinuity. -/
theorem epiClosure_eq_of_lowerSemicontinuousAt (hl : LowerSemicontinuousAt f x) :
    epiClosure f x = f x := by
  apply le_antisymm
  · simpa using epiLowerLimit_le_liminf (f := fun _ ↦ f) (x := x) tendsto_const_nhds
  · obtain ⟨y,hy,he⟩ := exists_tendsto_liminf_eq_epiLowerLimit (fun _ ↦ f) x
    exact hl.le_liminf.trans ((liminf_le_liminf_of_le (u := f) hy).trans_eq he)

private theorem locallyClosed_eventuallyEq_closure {P : Type*} [TopologicalSpace P]
    {S : Set P} {p : P} (hl : IsLocallyClosedAt S p) :
    S =ᶠ[𝓝 p] closure S := by
  obtain ⟨V,hV,_,hSV⟩ := hl
  filter_upwards [interior_mem_nhds.mpr hV] with y hy
  apply propext
  refine ⟨fun h ↦ subset_closure h, fun h ↦ ?_⟩
  have hmem := isOpen_interior.closure_inter (s := S) ⟨h,hy⟩
  exact ((closure_minimal (inter_subset_inter_right S interior_subset) hSV) hmem).1

omit [FiniteDimensional ℝ E] in
/-- Near a finite point of local lower semicontinuity, the epigraph and
its closed hull have the same germ. -/
theorem IsLocallyLscAt.euclideanEpigraph_eventuallyEq_epiClosure
    (hl : IsLocallyLscAt f x) (hx : f x = c) :
    euclideanEpigraph f =ᶠ[𝓝 (WithLp.toLp 2 (x,c))] euclideanEpigraph (epiClosure f) := by
  have hgg : euclideanEpigraph (epiClosure f) = closure (euclideanEpigraph f) := by
    change (l2ProdEquiv E) ⁻¹' epigraph (epiClosure f) = _
    rw [epigraph_epiClosure]
    exact (l2ProdEquiv E).toHomeomorph.preimage_closure _
  rw [hgg]
  apply locallyClosed_eventuallyEq_closure
  apply IsLocallyClosedAt.preimage_continuousLinearEquiv (l2ProdEquiv E)
  simpa [hx] using hl.isLocallyClosedAt_epigraph

/-- **Theorem 8.9.** At a locally lower semicontinuous finite point the
horizontal slice of the limiting normal cone is precisely the horizon
subdifferential. -/
theorem mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
    (hl : IsLocallyLscAt f x) (hx : f x = c) :
    v ∈ horizonSubdifferential f x ↔ WithLp.toLp 2 (v,(0:ℝ)) ∈
      normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
  refine ⟨horizontal_normal_of_mem_horizonSubdifferential hx, fun hn ↦ ?_⟩
  let g := epiClosure f
  let p := WithLp.toLp 2 (x,c)
  let d := WithLp.toLp 2 (v,(0:ℝ))
  have hgc : g x = c := (epiClosure_eq_of_lowerSemicontinuousAt hl.lowerSemicontinuousAt).trans hx
  have he := hl.euclideanEpigraph_eventuallyEq_epiClosure hx
  have hng : d ∈ normalCone (euclideanEpigraph g) p := normalCone_congr_nhds he ▸ hn
  have hpair := mem_closure_negativeNormalGraph_of_normal_of_lsc (lowerSemicontinuous_epiLowerLimit _)
    hgc hng
  obtain ⟨z,hz,hzlim⟩ := mem_closure_iff_seq_limit.mp hpair
  have hpos := (continuous_fst.tendsto _).comp hzlim
  have hneg : ∀ᶠ n in atTop, z n ∈ negativeEpigraphNormalGraph f :=
    (hpos.eventually (eventually_eventually_nhds.mpr he)).mono fun n hn ↦
      ⟨(regularNormalCone_congr_nhds hn).symm ▸ (hz n).1,(hz n).2⟩
  have hpairf : (p,d) ∈ closure (negativeEpigraphNormalGraph f) :=
    isClosed_closure.mem_of_tendsto hzlim (hneg.mono fun _ h ↦ subset_closure h)
  obtain ⟨z,hz,hzlim⟩ := mem_closure_iff_seq_limit.mp hpairf
  let y := fun n ↦ (z n).1.ofLp.1
  let r := fun n ↦ (z n).1.ofLp.2
  let u := fun n ↦ (z n).2.ofLp.1
  let b := fun n ↦ (z n).2.ofLp.2
  have hp' := ((l2ProdEquiv E).continuous.tendsto _).comp ((continuous_fst.tendsto _).comp hzlim)
  have hn' := ((l2ProdEquiv E).continuous.tendsto _).comp ((continuous_snd.tendsto _).comp hzlim)
  change Tendsto (fun n ↦ (y n,r n)) atTop (𝓝 (x,c)) at hp'
  change Tendsto (fun n ↦ (u n,b n)) atTop (𝓝 (v,(0:ℝ))) at hn'
  rw [nhds_prod_eq] at hp' hn'
  have hneg' (n : ℕ) : b n < 0 := (hz n).2
  have hnr (n : ℕ) : WithLp.toLp 2 (u n,b n) ∈ regularNormalCone (euclideanEpigraph f)
      (WithLp.toLp 2 (y n,r n)) := (hz n).1
  have hval (n : ℕ) := value_eq_of_mem_regularNormalCone_epigraph_of_neg (hnr n) (hneg' n)
  refine (mem_horizonSubdifferential_iff_zero_or_scaledSeq hx).mpr (Or.inr
    ⟨y,fun n ↦ (-(b n))⁻¹ • u n,fun n ↦ -(b n),tendsto_attentiveNhds_iff.mpr ⟨hp'.fst,?_⟩,
      fun n ↦ regularSubgradient_of_negative_height (hnr n) (hneg' n),fun n ↦ neg_pos.mpr (hneg' n),
      ?_,?_⟩)
  · simpa only [Function.comp_def,hval,hx] using (continuous_coe_real_ereal.tendsto c).comp hp'.snd
  · simpa using hn'.snd.neg
  · simpa [smul_smul, (hneg' _).ne] using hn'.fst

end RW
