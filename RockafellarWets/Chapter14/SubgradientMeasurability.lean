/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Subderivatives and subgradient mappings of normal integrands

Theorem 14.56 of Rockafellar–Wets, for the subderivative functions and the subgradient
mappings along a measurable `x(t) ∈ D_f(t)`, and for the graphical mappings `t ↦ gph ∂f(t, ·)`
(in general) and `t ↦ gph ∂^∞f(t, ·)` when the σ-field is complete for an s-finite measure.  The
epigraphical mapping is moved to the Euclidean product `WithLp 2 (ℝⁿ × ℝ)` (`euclideanEpigraph`),
where Theorem 14.26 applies; the epigraph formulas 8.2, 8.9 and 8.17 then identify the
subderivatives and subgradients.  Without completeness `t ↦ gph ∂^∞f(t, ·)` need not be measurable
(`RW.HorizonGraph.horizon_graph_counterexample` in `HorizonGraphCounterexample`), although its graph
`{(t, x, v) ∣ v ∈ ∂^∞f(t, x)}` is `A ⊗ B`-measurable for every normal integrand
(`measurableSet_svGraph_svGraph_horizonSubdifferential`): only the projection step needs the
measure.
-/

import RockafellarWets.Chapter14.ConeMappings
import RockafellarWets.Chapter14.IntegrandExamples
import RockafellarWets.Chapter8.EpigraphNormals
import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter8.RegularSubderivatives
import RockafellarWets.Chapter8.ClarkeSubgradients
import RockafellarWets.Chapter9.SmoothnessCriteria
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace RW

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem euclideanEpigraph_eq_toLp_image (g : E → EReal) :
    euclideanEpigraph g = WithLp.toLp 2 '' epigraph g := by
  ext p
  constructor
  · intro hp
    exact ⟨WithLp.ofLp p, hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact hq

/-- The Euclidean epigraphical mapping of a normal integrand is closed-valued and measurable. -/
theorem IsNormalIntegrand.svMeasurable_euclideanEpigraph {f : T → E → EReal}
    (hf : IsNormalIntegrand f) :
    (∀ t, IsClosed (euclideanEpigraph (f t))) ∧ SvMeasurable (fun t ↦ euclideanEpigraph (f t)) := by
  refine ⟨fun t ↦ (hf.1 t).preimage (WithLp.prod_continuous_ofLp 2 E ℝ), ?_⟩
  have heq : (fun t ↦ euclideanEpigraph (f t)) = fun t ↦ WithLp.toLp 2 '' epiMapping f t :=
    funext fun t ↦ euclideanEpigraph_eq_toLp_image _
  rw [heq]
  exact hf.2.image (WithLp.prod_continuous_toLp 2 E ℝ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem image_l2ProdEquiv_of_preimage_eq {A : Set (E × ℝ)} {B : Set (WithLp 2 (E × ℝ))}
    (h : B = l2ProdEquiv E ⁻¹' A) : A = l2ProdEquiv E '' B := by
  rw [h, Set.image_preimage_eq A (l2ProdEquiv E).surjective]

/-- **Theorem 14.56 (subderivatives and subgradient mappings)**: for a proper normal integrand `f`
and a measurable `x(t) ∈ D_f(t)`, the subderivative functions `(t, w) ↦ df(t, x(t))(w)` and
`(t, w) ↦ d̂f(t, x(t))(w)` are normal integrands, and the subgradient mappings
`t ↦ ∂f(t, x(t))`, `∂̂f(t, x(t))`, `∂^∞f(t, x(t))` are closed-valued and measurable. -/
theorem subderivatives_and_subgradient_mappings {f : T → E → EReal} (hf : IsNormalIntegrand f)
    (hp : ∀ t, IsProper (f t)) {x : T → E} (hx : Measurable x)
    (hxD : ∀ t, x t ∈ domMapping f t) :
    IsNormalIntegrand (fun t ↦ subderivative (f t) (x t)) ∧
      IsNormalIntegrand (fun t ↦ regularSubderivative (f t) (x t)) ∧
      ((∀ t, IsClosed (subdifferential (f t) (x t))) ∧
        SvMeasurable (fun t ↦ subdifferential (f t) (x t))) ∧
      ((∀ t, IsClosed (regularSubdifferential (f t) (x t))) ∧
        SvMeasurable (fun t ↦ regularSubdifferential (f t) (x t))) ∧
      ((∀ t, IsClosed (horizonSubdifferential (f t) (x t))) ∧
        SvMeasurable (fun t ↦ horizonSubdifferential (f t) (x t))) := by
  set c : T → ℝ := fun t ↦ (f t (x t)).toReal with hcdef
  have hfin : ∀ t, f t (x t) = c t := fun t ↦
    (EReal.coe_toReal (hxD t).ne ((hp t).2 (x t)).ne').symm
  have hcm : Measurable c := (hf.measurable_comp hx).ereal_toReal
  set p : T → WithLp 2 (E × ℝ) := fun t ↦ WithLp.toLp 2 (x t, c t) with hpdef
  have hpm : Measurable p := (WithLp.measurable_toLp 2 (E × ℝ)).comp (hx.prodMk hcm)
  have hpS : ∀ t, p t ∈ euclideanEpigraph (f t) := fun t ↦ (hfin t).le
  obtain ⟨hSc, hSm⟩ := hf.svMeasurable_euclideanEpigraph
  obtain ⟨⟨hTc, hTm⟩, ⟨hRTc, hRTm⟩, ⟨hNc, hNm⟩, ⟨hRNc, hRNm⟩, -⟩ :=
    tangent_and_normal_cone_mappings hSm hSc hpm hpS
  have hlsc : ∀ t, LowerSemicontinuous (f t) := hf.lowerSemicontinuous
  -- slices of normal cones
  have hslice : ∀ (β : ℝ) {K : T → Set (WithLp 2 (E × ℝ))}, (∀ t, IsClosed (K t)) →
      SvMeasurable K → (∀ t, IsClosed {v : E | WithLp.toLp 2 (v, β) ∈ K t}) ∧
        SvMeasurable (fun t ↦ {v : E | WithLp.toLp 2 (v, β) ∈ K t}) := by
    intro β K hKc hKm
    have hΦ : IsCaratheodory (fun (_ : T) (v : E) ↦ WithLp.toLp 2 (v, β)) :=
      ⟨fun _ ↦ measurable_const, fun _ ↦ (WithLp.prod_continuous_toLp 2 E ℝ).comp
        (continuous_id.prodMk continuous_const)⟩
    exact hΦ.svMeasurable_preimage hKm hKc
  -- subgradients
  have hsub : ∀ t, subdifferential (f t) (x t) =
      {v : E | WithLp.toLp 2 (v, (-1 : ℝ)) ∈ normalCone (euclideanEpigraph (f t)) (p t)} :=
    fun t ↦ by ext v; exact mem_subdifferential_iff_epigraph_normal (hfin t)
  have hrsub : ∀ t, regularSubdifferential (f t) (x t) =
      {v : E | WithLp.toLp 2 (v, (-1 : ℝ)) ∈
        regularNormalCone (euclideanEpigraph (f t)) (p t)} :=
    fun t ↦ by ext v; exact mem_regularSubdifferential_iff_epigraph_normal (hfin t)
  have hloc : ∀ t, IsLocallyLscAt (f t) (x t) := fun t ↦
    isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ
      ((hlsc t).lowerSemicontinuousOn _) (mem_univ _) (by rw [hfin t]; exact EReal.coe_ne_bot _)
      (by rw [hfin t]; exact EReal.coe_ne_top _)
  have hhsub : ∀ t, horizonSubdifferential (f t) (x t) =
      {v : E | WithLp.toLp 2 (v, (0 : ℝ)) ∈ normalCone (euclideanEpigraph (f t)) (p t)} :=
    fun t ↦ by
      ext v
      exact mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc (hloc t) (hfin t)
  -- subderivatives
  have hepi_d : ∀ t, epigraph (subderivative (f t) (x t)) =
      l2ProdEquiv E '' tangentCone (euclideanEpigraph (f t)) (p t) := by
    intro t
    rw [epigraph_subderivative_eq_tangentCone (hfin t)]
    exact image_l2ProdEquiv_of_preimage_eq
      (tangentCone_preimage_continuousLinearEquiv (l2ProdEquiv E) (epigraph (f t)) (p t))
  have hepi_rd : ∀ t, epigraph (regularSubderivative (f t) (x t)) =
      l2ProdEquiv E '' regularTangentCone (euclideanEpigraph (f t)) (p t) := by
    intro t
    rw [epigraph_regularSubderivative_eq_regularTangentCone (hfin t) (hlsc t _)]
    exact image_l2ProdEquiv_of_preimage_eq
      (regularTangentCone_preimage_continuousLinearEquiv (l2ProdEquiv E) (hfin t).le)
  have hhom : ∀ A : Set (WithLp 2 (E × ℝ)), IsClosed A → IsClosed (l2ProdEquiv E '' A) :=
    fun A hA ↦ (l2ProdEquiv E).toHomeomorph.isClosedMap A hA
  refine ⟨⟨fun t ↦ by rw [hepi_d t]; exact hhom _ (hTc t), ?_⟩,
    ⟨fun t ↦ by rw [hepi_rd t]; exact hhom _ (hRTc t), ?_⟩, ?_, ?_, ?_⟩
  · rw [show epiMapping (fun t ↦ subderivative (f t) (x t)) = _ from funext hepi_d]
    exact hTm.image (l2ProdEquiv E).continuous
  · rw [show epiMapping (fun t ↦ regularSubderivative (f t) (x t)) = _ from funext hepi_rd]
    exact hRTm.image (l2ProdEquiv E).continuous
  · rw [show (fun t ↦ subdifferential (f t) (x t)) = _ from funext hsub]
    exact ⟨fun t ↦ by rw [hsub t]; exact (hslice (-1) hNc hNm).1 t, (hslice (-1) hNc hNm).2⟩
  · rw [show (fun t ↦ regularSubdifferential (f t) (x t)) = _ from funext hrsub]
    exact ⟨fun t ↦ by rw [hrsub t]; exact (hslice (-1) hRNc hRNm).1 t,
      (hslice (-1) hRNc hRNm).2⟩
  · rw [show (fun t ↦ horizonSubdifferential (f t) (x t)) = _ from funext hhsub]
    exact ⟨fun t ↦ by rw [hhsub t]; exact (hslice 0 hNc hNm).1 t, (hslice 0 hNc hNm).2⟩

/-- **Theorem 14.56**, graphical mappings, the part that needs no measure: for a normal integrand
`f` the graphs `{(t, x, v) ∣ v ∈ ∂f(t, x)}` and `{(t, x, v) ∣ v ∈ ∂^∞f(t, x)}` of
`t ↦ gph ∂f(t, ·)` and `t ↦ gph ∂^∞f(t, ·)` are `A ⊗ B`-measurable.  By 8.9 they are the slices
`α = f(t, x)` of the `A ⊗ B`-measurable graph of `t ↦ gph N_{S_f(t)}` (14.26, 14.8 (a) ⇒ (b)) at
heights `-1` and `0`, through the jointly measurable `f` (14.34).  Only the projection step of
14.8 needs completeness (`svMeasurable_svGraph_subdifferential_of_isComplete`). -/
theorem measurableSet_svGraph_svGraph_subgradients {f : T → E → EReal}
    (hf : IsNormalIntegrand f) :
    MeasurableSet (svGraph fun t ↦ svGraph (subdifferential (f t))) ∧
      MeasurableSet (svGraph fun t ↦ svGraph (horizonSubdifferential (f t))) := by
  obtain ⟨hSc, hSm⟩ := hf.svMeasurable_euclideanEpigraph
  obtain ⟨hGc, hGm⟩ := svMeasurable_svGraph_normalCone hSm hSc
  have hGr := hGm.measurableSet_svGraph hGc
  have hlsc : ∀ t, LowerSemicontinuous (f t) := hf.lowerSemicontinuous
  have hfm : Measurable fun q : T × (E × E) ↦ f q.1 q.2.1 :=
    hf.measurable_uncurry.comp (measurable_fst.prodMk measurable_snd.fst)
  set Fin : Set (T × (E × E)) := {q | f q.1 q.2.1 ≠ ⊥ ∧ f q.1 q.2.1 ≠ ⊤}
  have hFin : MeasurableSet Fin :=
    (hfm (measurableSet_singleton ⊥).compl).inter (hfm (measurableSet_singleton ⊤).compl)
  set Ψ : ℝ → T × (E × E) → T × (WithLp 2 (E × ℝ) × WithLp 2 (E × ℝ)) := fun β q ↦
    (q.1, (WithLp.toLp 2 (q.2.1, (f q.1 q.2.1).toReal), WithLp.toLp 2 (q.2.2, β)))
  have hΨ : ∀ β, Measurable (Ψ β) := fun β ↦
    measurable_fst.prodMk (((WithLp.measurable_toLp 2 (E × ℝ)).comp
      (measurable_snd.fst.prodMk hfm.ereal_toReal)).prodMk
      ((WithLp.measurable_toLp 2 (E × ℝ)).comp (measurable_snd.snd.prodMk measurable_const)))
  have hfin : ∀ q ∈ Fin, f q.1 q.2.1 = ((f q.1 q.2.1).toReal : EReal) := fun q hq ↦
    (EReal.coe_toReal hq.2 hq.1).symm
  have hfinite : ∀ {g : E → EReal} {x : E}, (∃ c : ℝ, g x = c) → g x ≠ ⊥ ∧ g x ≠ ⊤ := by
    rintro g x ⟨c, hc⟩
    rw [hc]
    exact ⟨EReal.coe_ne_bot c, EReal.coe_ne_top c⟩
  constructor
  · have heq : svGraph (fun t ↦ svGraph (subdifferential (f t))) = Fin ∩ Ψ (-1) ⁻¹'
        svGraph fun t ↦ svGraph (normalCone (euclideanEpigraph (f t))) := by
      ext ⟨t, x, v⟩
      simp only [mem_svGraph, mem_inter_iff, mem_preimage, Ψ]
      constructor
      · intro hv
        have hF : (t, (x, v)) ∈ Fin := hfinite hv.1
        exact ⟨hF, (mem_subdifferential_iff_epigraph_normal (hfin _ hF)).1 hv⟩
      · rintro ⟨hF, hN⟩
        exact (mem_subdifferential_iff_epigraph_normal (hfin _ hF)).2 hN
    rw [heq]
    exact hFin.inter (hΨ (-1) hGr)
  · have hloc : ∀ q ∈ Fin, IsLocallyLscAt (f q.1) q.2.1 := fun q hq ↦
      isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ
        ((hlsc q.1).lowerSemicontinuousOn _) (mem_univ _) hq.1 hq.2
    have heq : svGraph (fun t ↦ svGraph (horizonSubdifferential (f t))) = Fin ∩ Ψ 0 ⁻¹'
        svGraph fun t ↦ svGraph (normalCone (euclideanEpigraph (f t))) := by
      ext ⟨t, x, v⟩
      simp only [mem_svGraph, mem_inter_iff, mem_preimage, Ψ]
      constructor
      · intro hv
        have hF : (t, (x, v)) ∈ Fin := hfinite hv.1
        exact ⟨hF, (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
          (hloc _ hF) (hfin _ hF)).1 hv⟩
      · rintro ⟨hF, hN⟩
        exact (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
          (hloc _ hF) (hfin _ hF)).2 hN
    rw [heq]
    exact hFin.inter (hΨ 0 hGr)

/-- **Theorem 14.56**: for every normal integrand the graph `{(t, x, v) ∣ v ∈ ∂f(t, x)}` of
`t ↦ gph ∂f(t, ·)` is `A ⊗ B`-measurable (no measure involved). -/
theorem measurableSet_svGraph_svGraph_subdifferential {f : T → E → EReal}
    (hf : IsNormalIntegrand f) : MeasurableSet (svGraph fun t ↦ svGraph (subdifferential (f t))) :=
  (measurableSet_svGraph_svGraph_subgradients hf).1

/-- **Theorem 14.56**: for every normal integrand the graph `{(t, x, v) ∣ v ∈ ∂^∞f(t, x)}` of
`t ↦ gph ∂^∞f(t, ·)` is `A ⊗ B`-measurable (no measure involved), although the mapping itself
need not be measurable (`RW.HorizonGraph.horizon_graph_counterexample`). -/
theorem measurableSet_svGraph_svGraph_horizonSubdifferential {f : T → E → EReal}
    (hf : IsNormalIntegrand f) :
    MeasurableSet (svGraph fun t ↦ svGraph (horizonSubdifferential (f t))) :=
  (measurableSet_svGraph_svGraph_subgradients hf).2

/-- **Theorem 14.56**, graphical mappings, when the σ-field is complete for an s-finite measure:
`t ↦ gph ∂f(t, ·)` and `t ↦ gph ∂^∞f(t, ·)` are measurable.  Their graphs are `A ⊗ B`-measurable
(`measurableSet_svGraph_svGraph_subgradients`), and the corrected 14.8 concludes. -/
theorem svMeasurable_svGraph_subdifferential_of_isComplete (μ : MeasureTheory.Measure T)
    [MeasureTheory.SFinite μ] [μ.IsComplete] {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    SvMeasurable (fun t ↦ svGraph (subdifferential (f t))) ∧
      SvMeasurable (fun t ↦ svGraph (horizonSubdifferential (f t))) :=
  ⟨svMeasurable_of_measurableSet_svGraph μ (measurableSet_svGraph_svGraph_subdifferential hf),
    svMeasurable_of_measurableSet_svGraph μ
      (measurableSet_svGraph_svGraph_horizonSubdifferential hf)⟩

/-- **Theorem 14.56**, the graphical subgradient mapping `t ↦ gph ∂f(t, ·)` is measurable (no
completeness needed).  The attentive graph `Γ(t) = {((x, f(t, x)), v) ∣ v ∈ ∂f(t, x)}` has as
closure the slice `{((x, α), v) ∣ (v, -1) ∈ N_{S_f(t)}(x, α)}` of the normal cone graph
(non-vertical regular normals to an epigraph live on the graph, 8.9), which is closed-valued and
measurable by 14.26; `gph ∂f(t, ·)` is the projection of `Γ(t)`. -/
theorem svMeasurable_svGraph_subdifferential {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    SvMeasurable (fun t ↦ svGraph (subdifferential (f t))) := by
  obtain ⟨hSc, hSm⟩ := hf.svMeasurable_euclideanEpigraph
  obtain ⟨hGc, hGm⟩ := svMeasurable_svGraph_normalCone hSm hSc
  set Γ : T → Set ((E × ℝ) × E) := fun t ↦
    {q | f t q.1.1 = q.1.2 ∧ q.2 ∈ subdifferential (f t) q.1.1}
  set K : T → Set ((E × ℝ) × E) := fun t ↦
    {q | (WithLp.toLp 2 q.1, WithLp.toLp 2 (q.2, (-1 : ℝ))) ∈
      svGraph (normalCone (euclideanEpigraph (f t)))}
  have hΦ : IsCaratheodory fun (_ : T) (q : (E × ℝ) × E) ↦
      ((WithLp.toLp 2 q.1, WithLp.toLp 2 (q.2, (-1 : ℝ))) :
        WithLp 2 (E × ℝ) × WithLp 2 (E × ℝ)) :=
    ⟨fun _ ↦ measurable_const, fun _ ↦
      ((WithLp.prod_continuous_toLp 2 E ℝ).comp continuous_fst).prodMk
        ((WithLp.prod_continuous_toLp 2 E ℝ).comp (continuous_snd.prodMk continuous_const))⟩
  obtain ⟨hKc, hKm⟩ := hΦ.svMeasurable_preimage hGm hGc
  have hclosure : ∀ t, _root_.closure (Γ t) = K t := by
    intro t
    apply le_antisymm
    · refine closure_minimal (fun q hq ↦ ?_) (hKc t)
      exact (mem_subdifferential_iff_epigraph_normal hq.1).1 hq.2
    · rintro ⟨⟨x, α⟩, v⟩ hq
      obtain ⟨-, xs, vs, hxs, hxlim, hvs, hvlim⟩ := hq
      set a : ℕ → E × ℝ := fun n ↦ (xs n).ofLp
      set b : ℕ → E × ℝ := fun n ↦ (vs n).ofLp
      have hxs' : ∀ n, xs n = WithLp.toLp 2 (a n) := fun n ↦ (WithLp.toLp_ofLp 2 (xs n)).symm
      have hvs' : ∀ n, vs n = WithLp.toLp 2 (b n) := fun n ↦ (WithLp.toLp_ofLp 2 (vs n)).symm
      have ha : Tendsto a atTop (𝓝 (x, α)) := by
        have := ((l2ProdEquiv E).continuous.tendsto _).comp hxlim
        exact this
      have hb : Tendsto b atTop (𝓝 (v, (-1 : ℝ))) := by
        have := ((l2ProdEquiv E).continuous.tendsto _).comp hvlim
        exact this
      have hbneg : ∀ᶠ n in atTop, (b n).2 < 0 :=
        ((continuous_snd.tendsto _).comp hb).eventually (gt_mem_nhds (by norm_num))
      have hscale : Tendsto (fun n ↦ (-(b n).2)⁻¹ • (b n).1) atTop (𝓝 v) := by
        have h1 : Tendsto (fun n ↦ (-(b n).2)⁻¹) atTop (𝓝 ((-(-1 : ℝ))⁻¹)) :=
          (((continuous_snd.tendsto _).comp hb).neg).inv₀ (by norm_num)
        have h2 : Tendsto (fun n ↦ (b n).1) atTop (𝓝 v) := (continuous_fst.tendsto _).comp hb
        have := h1.smul h2
        simpa using this
      refine mem_closure_of_tendsto (ha.prodMk_nhds hscale) ?_
      filter_upwards [hbneg] with n hn
      have hreg : WithLp.toLp 2 ((b n).1, (b n).2) ∈ regularNormalCone (euclideanEpigraph (f t))
          (WithLp.toLp 2 ((a n).1, (a n).2)) := by
        have := hvs n
        rw [hxs' n, hvs' n] at this
        exact this
      have hval := value_eq_of_mem_regularNormalCone_epigraph_of_neg hreg hn
      refine ⟨hval, regularSubdifferential_subset_subdifferential _ _ ?_⟩
      exact regularSubgradient_of_negative_height hreg hn
  have hΓm : SvMeasurable Γ := fun O hO ↦ by
    rw [← svPreimage_closure_of_isOpen Γ hO]
    have : (fun t ↦ _root_.closure (Γ t)) = K := funext hclosure
    rw [this]
    exact hKm O hO
  have heq : (fun t ↦ svGraph (subdifferential (f t))) =
      fun t ↦ (fun q : (E × ℝ) × E ↦ (q.1.1, q.2)) '' Γ t := by
    funext t
    ext ⟨x, v⟩
    simp only [mem_svGraph, mem_image, Γ, mem_setOf_eq, Prod.exists, Prod.mk.injEq]
    constructor
    · intro hv
      obtain ⟨c, hc⟩ := hv.1
      exact ⟨x, c, v, ⟨hc, hv⟩, rfl, rfl⟩
    · rintro ⟨x', c, v', ⟨-, hv⟩, rfl, rfl⟩
      exact hv
  rw [heq]
  exact hΓm.image (continuous_fst.fst.prodMk continuous_snd)

end RW
