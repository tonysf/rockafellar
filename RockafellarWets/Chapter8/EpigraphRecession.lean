/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Local recession of epigraphs
-/

import RockafellarWets.Chapter8.ProfileDerivatives
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion
import RockafellarWets.Chapter6.RecessionCharacterization

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} {x : E} {c : ℝ}

/-- The neighborhood and upper level cutoff in Proposition 8.50. -/
def EventuallyBelowLevel (f : E → EReal) (x : E) (c : ℝ) (P : E → Prop) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ δ > 0, ∀ y ∈ V, f y ≤ ((c+δ : ℝ) : EReal) → P y

omit [InnerProductSpace ℝ E] in
theorem eventuallyBelowLevel_iff_attentive {P : E → Prop} (hx : f x = c) (hl : LowerSemicontinuousAt f x) :
    EventuallyBelowLevel f x c P ↔ ∀ᶠ y in attentiveNhds f x, P y := by
  obtain ⟨hid,hf⟩ := tendsto_attentiveNhds_iff.mp (tendsto_id (x := attentiveNhds f x))
  constructor
  · rintro ⟨V,hV,δ,hδ,hP⟩
    have hlt : f x < ((c+δ : ℝ) : EReal) := by rw [hx,EReal.coe_lt_coe_iff]; linarith
    filter_upwards [hid.eventually hV,hf.eventually_lt_const hlt] with y hy hfy
    exact hP y hy hfy.le
  · intro h
    rw [attentiveNhds_eq_comap_graph] at h
    obtain ⟨U,hU,hUP⟩ := h
    rw [nhds_prod_eq] at hU
    obtain ⟨V,hV,W,hW,hVW⟩ := mem_prod_iff.mp hU
    rw [hx] at hW
    obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp ((continuous_coe_real_ereal.tendsto c).eventually hW)
    let δ := r/2
    have hδ : 0 < δ := half_pos hr
    have hlow : ∀ᶠ y in 𝓝 x, ((c-δ : ℝ):EReal) < f y := hl _ (by change ((c-δ : ℝ):EReal) < f x; rw [hx,EReal.coe_lt_coe_iff]; linarith)
    refine ⟨V ∩ {y | ((c-δ : ℝ):EReal) < f y},inter_mem hV hlow,δ,hδ,?_⟩
    intro y hy hfy
    have hfinite := EReal.coe_toReal (hfy.trans_lt (EReal.coe_lt_top _)).ne
      (((EReal.bot_lt_coe _).trans hy.2).ne')
    have h₁ := EReal.coe_lt_coe_iff.mp (hy.2.trans_eq hfinite.symm)
    have h₂ := EReal.coe_le_coe_iff.mp (hfinite.le.trans hfy)
    have hyW : f y ∈ W := by
      rw [← hfinite]
      apply hrW
      rw [mem_ball,Real.dist_eq,abs_lt]
      dsimp [δ] at h₁ h₂
      constructor <;> linarith
    exact hUP (hVW ⟨hy.1,hyW⟩)

omit [InnerProductSpace ℝ E] in
/-- Near a finite locally lsc graph point, all sufficiently close graph
points are themselves locally lsc in the truncated-sublevel sense. -/
theorem IsLocallyLscAt.eventually_attentive {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    (hl : IsLocallyLscAt f x) : ∀ᶠ y in attentiveNhds f x, IsLocallyLscAt f y := by
  have hC := hl.isLocallyClosedAt_epigraph
  rw [hx,EReal.toReal_coe] at hC
  obtain ⟨V,hV,hVc,hCV⟩ := hC
  have hT := (tendsto_graph_attentiveNhds hx).mono_right nhdsWithin_le_nhds
  filter_upwards [hT.eventually (interior_mem_nhds.mpr hV),eventually_finite_attentiveNhds hx] with y hy hfy
  exact isLocallyLscAt_of_isLocallyClosedAt_epigraph hfy ⟨V,mem_interior_iff_mem_nhds.mp hy,hVc,hCV⟩

private abbrev liftEpi (f : E → EReal) (y : E) := WithLp.toLp 2 (y,(f y).toReal)

private theorem tendsto_liftEpi_attentive [FiniteDimensional ℝ E] (hx : f x = c) :
    Tendsto (liftEpi f) (attentiveNhds f x) (𝓝[euclideanEpigraph f] (WithLp.toLp 2 (x,c))) := by
  have ht := tendsto_graph_attentiveNhds hx
  exact (tendsto_nhdsWithin_iff.mpr ⟨(l2ProdEquiv E).symm.continuous.tendsto _ |>.mono_left nhdsWithin_le_nhds,
    self_mem_nhdsWithin⟩).comp ht

private theorem tendsto_fst_euclideanEpigraph_attentive [FiniteDimensional ℝ E]
    (hx : f x = c) (hl : LowerSemicontinuousAt f x) :
    Tendsto (fun p : WithLp 2 (E × ℝ) ↦ p.fst) (𝓝[euclideanEpigraph f] (WithLp.toLp 2 (x,c)))
      (attentiveNhds f x) := by
  apply (tendsto_fst_epigraph_attentiveNhds hx hl).comp
  exact tendsto_nhdsWithin_iff.mpr ⟨(l2ProdEquiv E).continuous.tendsto _ |>.mono_left nhdsWithin_le_nhds,
    self_mem_nhdsWithin⟩

variable [FiniteDimensional ℝ E] {w : E} {b : ℝ}

omit [FiniteDimensional ℝ E] in
private theorem epi_local_closed (hx : f x = c) (hl : IsLocallyLscAt f x) :
    IsLocallyClosedAt (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
  have h := hl.isLocallyClosedAt_epigraph
  rw [hx,EReal.toReal_coe] at h
  exact IsLocallyClosedAt.preimage_continuousLinearEquiv (l2ProdEquiv E) h

omit [FiniteDimensional ℝ E] in
private theorem tangent_lower_height {q : WithLp 2 (E × ℝ)} {a : ℝ} (hy : f q.fst = a)
    (hq : q ∈ euclideanEpigraph f) (hw : subderivative f q.fst w ≤ (b:EReal)) :
    WithLp.toLp 2 (w,b) ∈ tangentCone (euclideanEpigraph f) q := by
  have hh : a ≤ q.snd := EReal.coe_le_coe_iff.mp (hy ▸ hq)
  change _ ∈ tangentCone (l2ProdEquiv E ⁻¹' epigraph f) q
  rw [tangentCone_preimage_continuousLinearEquiv]
  apply tangentCone_epigraph_mono_base_height f q.fst hh
  rw [← epigraph_subderivative_eq_tangentCone hy]
  exact hw

/-- **Proposition 8.50(a,b)**, the test with ordinary subderivatives. -/
theorem mem_localRecessionCone_epigraph_iff_subderivative (hx : f x = c) (hl : IsLocallyLscAt f x) :
    WithLp.toLp 2 (w,b) ∈ localRecessionCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      EventuallyBelowLevel f x c (fun y ↦ subderivative f y w ≤ (b:EReal)) := by
  rw [eventuallyBelowLevel_iff_attentive hx hl.lowerSemicontinuousAt]
  have hp : WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f := hx.le
  rw [mem_localRecessionCone_iff_exists_open_tangent hp (epi_local_closed hx hl)]
  constructor
  · rintro ⟨V,hVo,hpV,hV⟩
    have ht := tendsto_liftEpi_attentive hx
    filter_upwards [ht.eventually self_mem_nhdsWithin,(ht.mono_right nhdsWithin_le_nhds).eventually
      (hVo.mem_nhds hpV),eventually_finite_attentiveNhds hx] with y hy hyV hfin
    have hh := hV _ ⟨hy,hyV⟩
    exact (congrFun (graphicalDerivative_epiProfile hfin) w).le hh
  · intro hb
    have hf := tendsto_fst_euclideanEpigraph_attentive hx hl.lowerSemicontinuousAt
    have ht : ∀ᶠ q in 𝓝[euclideanEpigraph f] (WithLp.toLp 2 (x,c)),
        WithLp.toLp 2 (w,b) ∈ tangentCone (euclideanEpigraph f) q := by
      filter_upwards [hf.eventually (eventually_finite_attentiveNhds hx),self_mem_nhdsWithin,
        hf.eventually hb] with q hfin hq hder
      exact tangent_lower_height hfin hq hder
    obtain ⟨V,hVo,hpV,hV⟩ := mem_nhdsWithin.mp ht
    exact ⟨V,hVo,hpV,fun q hq ↦ hV ⟨hq.2,hq.1⟩⟩

/-- **Proposition 8.50(a,c)**, the test with regular subderivatives. -/
theorem mem_localRecessionCone_epigraph_iff_regularSubderivative (hx : f x = c) (hl : IsLocallyLscAt f x) :
    WithLp.toLp 2 (w,b) ∈ localRecessionCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      EventuallyBelowLevel f x c (fun y ↦ regularSubderivative f y w ≤ (b:EReal)) := by
  rw [eventuallyBelowLevel_iff_attentive hx hl.lowerSemicontinuousAt]
  constructor
  · intro h
    obtain ⟨V,hVo,hpV,hV⟩ := (mem_localRecessionCone_iff_exists_open_regularTangent
      (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le) (epi_local_closed hx hl)).mp h
    have ht := tendsto_liftEpi_attentive hx
    filter_upwards [ht.eventually self_mem_nhdsWithin,(ht.mono_right nhdsWithin_le_nhds).eventually
      (hVo.mem_nhds hpV),eventually_finite_attentiveNhds hx,hl.eventually_attentive hx] with y hy hyV hfin hly
    exact (congrFun (regularGraphicalDerivative_epiProfile hfin hly.lowerSemicontinuousAt) w).le
      (hV _ ⟨hy,hyV⟩)
  · intro hr
    apply (mem_localRecessionCone_epigraph_iff_subderivative hx hl).mpr
    apply (eventuallyBelowLevel_iff_attentive hx hl.lowerSemicontinuousAt).mpr
    filter_upwards [hr,eventually_finite_attentiveNhds hx] with y hy hf
    exact (subderivative_le_regularSubderivative hf w).trans hy

/-- **Proposition 8.50(a,f)**. The translated-value inequality agrees with
the difference-quotient bound at positive steps and includes the harmless
step zero without division. -/
theorem mem_localRecessionCone_epigraph_iff_increments (hx : f x = c) (hl : IsLocallyLscAt f x) :
    WithLp.toLp 2 (w,b) ∈ localRecessionCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      ∃ ε > 0, EventuallyBelowLevel f x c
        (fun y ↦ ∀ t ∈ Icc (0:ℝ) ε, f (y+t • w) ≤ f y + ((t*b : ℝ):EReal)) := by
  simp only [eventuallyBelowLevel_iff_attentive hx hl.lowerSemicontinuousAt]
  rw [mem_localRecessionCone_iff_eventually]
  constructor
  · rintro ⟨_,ε,hε,h⟩
    have ht := tendsto_liftEpi_attentive hx
    refine ⟨ε,hε,?_⟩
    filter_upwards [(ht.mono_right nhdsWithin_le_nhds).eventually h,ht.eventually self_mem_nhdsWithin,
      eventually_finite_attentiveNhds hx] with y hy hfy hfin t ht'
    have hh : f (y+t • w) ≤ ((((f y).toReal+t*b):ℝ):EReal) := hy hfy t ht'
    simpa only [EReal.coe_add,← hfin] using hh
  · rintro ⟨ε,hε,h⟩
    refine ⟨hx.le,ε,hε,eventually_nhdsWithin_iff.mp ?_⟩
    have hf := tendsto_fst_euclideanEpigraph_attentive hx hl.lowerSemicontinuousAt
    filter_upwards [hf.eventually h,self_mem_nhdsWithin] with q hq hmem t ht'
    change f (q.fst+t • w) ≤ (((q.snd+t*b):ℝ):EReal)
    rw [EReal.coe_add]
    exact (hq t ht').trans (add_le_add_left (show f q.fst ≤ (q.snd:EReal) from hmem) _)

private theorem regularNormal_lower_height {q : WithLp 2 (E × ℝ)} {a : ℝ} (hy : f q.fst = a)
    {n : WithLp 2 (E × ℝ)} (hn : n ∈ regularNormalCone (euclideanEpigraph f) q) :
    n ∈ regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (q.fst,a)) := by
  apply (mem_regularNormalCone_iff_inner_nonpos (show WithLp.toLp 2 (q.fst,a) ∈ euclideanEpigraph f from hy.le)).mpr
  intro z hz
  apply inner_nonpos_of_mem_regularNormalCone hn
  obtain ⟨⟨d,r⟩,rfl⟩ := (WithLp.toLp_surjective 2) z
  exact tangent_lower_height hy hn.1 ((congrFun (graphicalDerivative_epiProfile hy) d).le hz)

omit [FiniteDimensional ℝ E] in
private theorem horizon_nonpos_of_attentive_regular_bound {y v : E} {a : ℝ} (hy : f y = a)
    (hb : ∀ᶠ z in attentiveNhds f y, ∀ s ∈ regularSubdifferential f z, ⟪s,w⟫_ℝ ≤ b)
    (hv : v ∈ horizonSubdifferential f y) : ⟪v,w⟫_ℝ ≤ 0 := by
  rcases (mem_horizonSubdifferential_iff_zero_or_scaledSeq hy).mp hv with rfl |
    ⟨z,s,t,hz,hs,ht,ht₀,hv⟩
  · simp
  have hlim : Tendsto (fun n ↦ ⟪t n • s n,w⟫_ℝ) atTop (𝓝 ⟪v,w⟫_ℝ) := hv.inner tendsto_const_nhds
  have hbto : Tendsto (fun n ↦ t n*b) atTop (𝓝 0) := by simpa using ht₀.mul_const b
  apply le_of_tendsto_of_tendsto hlim hbto
  filter_upwards [hz.eventually hb] with n hn
  rw [real_inner_smul_left]
  exact mul_le_mul_of_nonneg_left (hn _ (hs n)) (ht n).le

private theorem localRecession_of_regularSubgradient_bound (hx : f x = c) (hl : IsLocallyLscAt f x)
    (h : ∀ᶠ y in attentiveNhds f x, ∀ v ∈ regularSubdifferential f y, ⟪v,w⟫_ℝ ≤ b) :
    WithLp.toLp 2 (w,b) ∈ localRecessionCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
  have hp : WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f := hx.le
  apply (mem_localRecessionCone_iff_exists_open_regularNormal_nonpos hp (epi_local_closed hx hl)).mpr
  have hf := tendsto_fst_euclideanEpigraph_attentive hx hl.lowerSemicontinuousAt
  have hnorm : ∀ᶠ q in 𝓝[euclideanEpigraph f] (WithLp.toLp 2 (x,c)),
      ∀ n ∈ regularNormalCone (euclideanEpigraph f) q, ⟪n,WithLp.toLp 2 (w,b)⟫_ℝ ≤ 0 := by
    filter_upwards [hf.eventually (eventually_finite_attentiveNhds hx),hf.eventually h,
      hf.eventually (eventually_eventually_attentiveNhds h),hf.eventually (hl.eventually_attentive hx)]
      with q hy hb hlocal hly n hn
    obtain ⟨⟨v,d⟩,rfl⟩ := (WithLp.toLp_surjective 2) n
    change ⟪v,w⟫_ℝ + b*d ≤ 0
    have hd : d ≤ 0 := vertical_nonpos_of_mem_regularNormalCone_epigraph hn
    rcases lt_or_eq_of_le hd with hneg | rfl
    · have hvg := regularSubgradient_of_negative_height hn hneg
      have htest := hb _ hvg
      rw [real_inner_smul_left,inv_mul_le_iff₀ (neg_pos.mpr hneg)] at htest
      linarith
    · have hn' := regularNormal_lower_height hy hn
      have hv := (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hly hy).mpr
        (regularNormalCone_subset_normalCone _ _ hn')
      simpa using horizon_nonpos_of_attentive_regular_bound hy hlocal hv
  obtain ⟨V,hVo,hpV,hV⟩ := mem_nhdsWithin.mp hnorm
  exact ⟨V,hVo,hpV,fun q hq ↦ hV ⟨hq.2,hq.1⟩⟩

/-- **Proposition 8.50(a,d,e)**. Either family of subgradient inequalities
near the reference level characterizes epigraph recession. -/
theorem localRecessionCone_epigraph_subgradient_criteria (hx : f x = c) (hl : IsLocallyLscAt f x) :
    (WithLp.toLp 2 (w,b) ∈ localRecessionCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      EventuallyBelowLevel f x c (fun y ↦ ∀ v ∈ subdifferential f y, ⟪v,w⟫_ℝ ≤ b)) ∧
    (WithLp.toLp 2 (w,b) ∈ localRecessionCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      EventuallyBelowLevel f x c (fun y ↦ ∀ v ∈ regularSubdifferential f y, ⟪v,w⟫_ℝ ≤ b)) := by
  simp only [eventuallyBelowLevel_iff_attentive hx hl.lowerSemicontinuousAt]
  have hp : WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f := hx.le
  have h₁ (hw : WithLp.toLp 2 (w,b) ∈ localRecessionCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c))) :
      ∀ᶠ y in attentiveNhds f x, ∀ v ∈ subdifferential f y, ⟪v,w⟫_ℝ ≤ b := by
    obtain ⟨V,hVo,hpV,hV⟩ :=
      (mem_localRecessionCone_iff_exists_open_normal_nonpos hp (epi_local_closed hx hl)).mp hw
    have ht := tendsto_liftEpi_attentive hx
    filter_upwards [ht.eventually self_mem_nhdsWithin,(ht.mono_right nhdsWithin_le_nhds).eventually
      (hVo.mem_nhds hpV),eventually_finite_attentiveNhds hx] with y hy hyV hfin v hv
    have hh := hV _ ⟨hy,hyV⟩ _ ((mem_subdifferential_iff_epigraph_normal hfin).mp hv)
    change ⟪v,w⟫_ℝ+b*(-1) ≤ 0 at hh
    linarith
  have weaken : (∀ᶠ y in attentiveNhds f x, ∀ v ∈ subdifferential f y, ⟪v,w⟫_ℝ ≤ b) →
      ∀ᶠ y in attentiveNhds f x, ∀ v ∈ regularSubdifferential f y, ⟪v,w⟫_ℝ ≤ b :=
    fun h ↦ h.mono fun y hy v hv ↦ hy v (regularSubdifferential_subset_subdifferential f y hv)
  exact ⟨⟨h₁,fun h ↦ localRecession_of_regularSubgradient_bound hx hl (weaken h)⟩,
    ⟨fun h ↦ weaken (h₁ h),localRecession_of_regularSubgradient_bound hx hl⟩⟩

/-- **Example 8.51.** A proper lower semicontinuous function decreases along
a cone exactly when every limiting subgradient belongs to its polar. -/
theorem nonincreasing_along_cone_iff_subdifferential_subset_polar {K : Set E}
    (hK : IsCone K) (hproper : IsProper f) (hf : LowerSemicontinuous f) :
    (∀ x, ∀ w ∈ K, f (x+w) ≤ f x) ↔
      ∀ x ∈ effectiveDomain f, subdifferential f x ⊆ polarCone K := by
  let C := euclideanEpigraph f
  have hclosed : IsClosed C := (isClosed_epigraph_of_lsc_ereal _ hf).preimage (l2ProdEquiv E).continuous
  have hloc {x : E} {c : ℝ} (hx : f x = c) : IsLocallyLscAt f x :=
    isLocallyLscAt_of_isLocallyClosedAt_epigraph hx
      (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _ hf) _)
  constructor
  · intro h x hx v hv w hw
    let c := (f x).toReal
    have hc : f x = (c:EReal) := (EReal.coe_toReal (show f x < ⊤ from hx).ne (hproper.2 x).ne').symm
    have hglob : WithLp.toLp 2 (w,(0:ℝ)) ∈ globalRecessionCone C := by
      intro q hq t ht
      have hb := (h q.fst (t • w) (hK.smul_mem hw ht)).trans (show f q.fst ≤ (q.snd:EReal) from hq)
      change f (q.fst+t • w) ≤ (((q.snd+t*0):ℝ):EReal)
      simpa only [mul_zero,add_zero] using hb
    have hrec := globalRecessionCone_subset_localRecessionCone
      (show WithLp.toLp 2 (x,c) ∈ C from hc.le) hglob
    have hh := ((localRecessionCone_epigraph_subgradient_criteria hc (hloc hc)).1.mp hrec)
    obtain ⟨V,hV,δ,hδ,hV'⟩ := hh
    exact hV' x (mem_of_mem_nhds hV) (by rw [hc,EReal.coe_le_coe_iff]; linarith) v hv
  · intro h x w hw
    by_cases hxt : f x = ⊤
    · simp [hxt]
    have hder {y : E} {r : ℝ} (hy : f y = r) : subderivative f y w ≤ (0:EReal) := by
      have hb : EventuallyBelowLevel f y r (fun z ↦ ∀ v ∈ subdifferential f z, ⟪v,w⟫_ℝ ≤ (0:ℝ)) := by
        refine ⟨univ,univ_mem,1,one_pos,fun z _ hz v hv ↦ ?_⟩
        exact h z (hz.trans_lt (EReal.coe_lt_top _)) hv w hw
      have hrec := (localRecessionCone_epigraph_subgradient_criteria hy (hloc hy)).1.mpr hb
      obtain ⟨V,hV,δ,hδ,hV'⟩ := (mem_localRecessionCone_epigraph_iff_subderivative hy (hloc hy)).mp hrec
      exact hV' y (mem_of_mem_nhds hV) (by rw [hy,EReal.coe_le_coe_iff]; linarith)
    have hglob : WithLp.toLp 2 (w,(0:ℝ)) ∈ globalRecessionCone C := by
      rw [globalRecessionCone_eq_iInter_localRecessionCone hclosed]
      apply mem_iInter₂.mpr
      intro q hq
      apply (mem_localRecessionCone_iff_exists_open_tangent hq (RW.IsClosed.isLocallyClosedAt hclosed q)).mpr
      refine ⟨univ,isOpen_univ,mem_univ _,fun p hp ↦ ?_⟩
      have hfin := (EReal.coe_toReal ((show f p.fst ≤ (p.snd:EReal) from hp.1).trans_lt (EReal.coe_lt_top _)).ne
        (hproper.2 _).ne').symm
      exact tangent_lower_height hfin hp.1 (hder hfin)
    have he := (EReal.coe_toReal hxt (hproper.2 x).ne').symm
    have hh := hglob (WithLp.toLp 2 (x,(f x).toReal)) he.le 1 zero_le_one
    change f (x+(1:ℝ) • w) ≤ ((((f x).toReal+1*0):ℝ):EReal) at hh
    simpa only [one_smul,mul_zero,add_zero,← he] using hh

end RW
