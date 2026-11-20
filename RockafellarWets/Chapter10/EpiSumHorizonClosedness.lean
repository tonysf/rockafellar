/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closedness of common horizon multipliers in finite epi-addition
-/

import RockafellarWets.Chapter10.FiniteEpiSumSubgradients
import RockafellarWets.Chapter10.FiniteAttentiveProjections

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isCompact_epiSumDecompositions {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hb : HasBoundedEpiSumDecompositions f) (x : E) : IsCompact (epiSumDecompositions f x) := by
  have hl := lowerSemicontinuous_finiteEpiSumIntegrand hp hf
  have hpr := isProper_finiteEpiSumIntegrand hp
  have hlev := isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb
  have hl' := hl.comp (WithLp.prodContinuousLinearEquiv 2 ℝ (PiLp 2 (fun _ : ι ↦ E)) E).symm.continuous
  have hp' : IsProper (fun q : PiLp 2 (fun _ : ι ↦ E) × E ↦ finiteEpiSumIntegrand f (WithLp.toLp 2 q)) := by
    refine ⟨?_,fun q ↦ hpr.2 _⟩
    obtain ⟨q,hq⟩ := hpr.1
    exact ⟨WithLp.ofLp q,hq⟩
  have hc := (paramArgmin_compact_and_dom hl' hp' hlev).1 x
  change IsCompact (parametricMinimizers (finiteEpiSumIntegrand f) x) at hc
  rwa [parametricMinimizers_finiteEpiSumIntegrand hp] at hc

/-- **Exercise 10.18**, the union of the common horizon subgradients over
optimal decompositions is closed, without a regularity assumption. -/
theorem isClosed_horizonEpiSumMultipliers {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hb : HasBoundedEpiSumDecompositions f) {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) :
    IsClosed (horizonEpiSumMultipliers f x) := by
  apply isSeqClosed_iff_isClosed.mp
  intro ys y hys hy
  choose as has hsub using hys
  obtain ⟨a,ha,φ,hφ,hato⟩ := (isCompact_epiSumDecompositions hp hf hb x).isSeqCompact has
  obtain ⟨c,hc⟩ := separablePi_finite_components (ha.2.1.trans hx)
  have hatt : Tendsto (as ∘ φ) atTop (attentiveNhds (separablePi f) a) := by
    apply tendsto_attentiveNhds_iff.mpr
    refine ⟨hato,?_⟩
    have he : separablePi f ∘ (as ∘ φ) = fun _ : ℕ ↦ (r:EReal) :=
      funext fun n ↦ (has (φ n)).2.1.trans hx
    rw [he,ha.2.1,hx]
    exact tendsto_const_nhds
  refine ⟨a,ha,?_⟩
  intro i
  have hati := (tendsto_separablePi_attentive_coordinate f hp hf a c hc i).comp hatt
  have hito := (tendsto_attentiveNhds_iff.mp hati).1
  have hfit := (tendsto_attentiveNhds_iff.mp hati).2
  have hreal : Tendsto (fun n ↦ (f i (as (φ n) i)).toReal) atTop (𝓝 (c i)) := by
    rw [hc i] at hfit
    simpa only [Function.comp_def,EReal.toReal_coe] using
      (EReal.tendsto_toReal (EReal.coe_ne_top (c i)) (EReal.coe_ne_bot (c i))).comp hfit
  have hfinite (n : ℕ) : f i (as n i) = ((f i (as n i)).toReal:EReal) := by
    obtain ⟨d,hd⟩ := separablePi_finite_components ((has n).2.1.trans hx)
    rw [hd i,EReal.toReal_coe]
  have hepi (n : ℕ) : WithLp.toLp 2 (as (φ n) i,(f i (as (φ n) i)).toReal) ∈ euclideanEpigraph (f i) :=
    (hfinite (φ n)).le
  have hn (n : ℕ) : WithLp.toLp 2 (ys (φ n),(0:ℝ)) ∈ normalCone (euclideanEpigraph (f i))
      (WithLp.toLp 2 (as (φ n) i,(f i (as (φ n) i)).toReal)) :=
    horizontal_normal_of_mem_horizonSubdifferential (hfinite (φ n)) (hsub (φ n) i)
  have hpt : Tendsto (fun n ↦ WithLp.toLp 2 (as (φ n) i,(f i (as (φ n) i)).toReal))
      atTop (𝓝 (WithLp.toLp 2 (a i,c i))) :=
    (l2ProdEquiv E).symm.continuous.continuousAt.tendsto.comp (hito.prodMk_nhds hreal)
  have hvt : Tendsto (fun n ↦ WithLp.toLp 2 (ys (φ n),(0:ℝ))) atTop (𝓝 (WithLp.toLp 2 (y,(0:ℝ)))) :=
    (l2ProdEquiv E).symm.continuous.continuousAt.tendsto.comp
      ((hy.comp hφ.tendsto_atTop).prodMk_nhds tendsto_const_nhds)
  exact (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
    (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hc i)) (hc i)).mpr
      (mem_normalCone_of_tendsto (show WithLp.toLp 2 (a i,c i) ∈ euclideanEpigraph (f i) from (hc i).le)
        hepi hpt hn hvt)

end

end RW
