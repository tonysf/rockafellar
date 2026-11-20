/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Directional bounds for finite epi-addition
-/

import RockafellarWets.Chapter10.FiniteEpiSumSubgradients
import RockafellarWets.Chapter10.FiniteSumSubderivatives

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

set_option maxHeartbeats 1000000

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A specified decomposition bounds the epi-sum from above. -/
theorem finiteEpiSumValue_le_separablePi (f : ι → E → EReal) (a : PiLp 2 (fun _ : ι ↦ E)) :
    finiteEpiSumValue f (∑ i, a i) ≤ separablePi f a := by
  have h := iInf_le (fun b : PiLp 2 (fun _ : ι ↦ E) ↦
    finiteEpiSumIntegrand f (WithLp.toLp 2 (b,∑ i, a i))) a
  change finiteEpiSumValue f (∑ i, a i) ≤ finiteEpiSumIntegrand f (WithLp.toLp 2 (a,∑ i, a i)) at h
  rw [finiteEpiSumIntegrand_apply,sub_self,indicatorVA_apply_mem (mem_singleton 0),add_zero] at h
  exact h

theorem epiSum_epigraph_image_subset (f : ι → E → EReal) :
    epigraphChainDerivative (l2CoordinateSum (ι := ι) (E := E)) '' euclideanEpigraph (separablePi f) ⊆
      euclideanEpigraph (finiteEpiSumValue f) := by
  rintro q ⟨p,hp,rfl⟩
  change finiteEpiSumValue f (l2CoordinateSum p.fst) ≤ (p.snd:EReal)
  rw [l2CoordinateSum_apply]
  exact (finiteEpiSumValue_le_separablePi f p.fst).trans hp

/-- The lower subderivative is bounded by that of the separable objective
at each optimal decomposition. -/
theorem subderivative_finiteEpiSumValue_le_at_decomposition {f : ι → E → EReal}
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) {a : PiLp 2 (fun _ : ι ↦ E)}
    (ha : a ∈ epiSumDecompositions f x) (w : PiLp 2 (fun _ : ι ↦ E)) :
    subderivative (finiteEpiSumValue f) x (∑ i, w i) ≤ subderivative (separablePi f) a w := by
  by_contra! h
  obtain ⟨b,hb,hb'⟩ := EReal.exists_between_coe_real h
  have ht : WithLp.toLp 2 (w,b) ∈ tangentCone (euclideanEpigraph (separablePi f)) (WithLp.toLp 2 (a,r)) :=
    (mem_tangentCone_euclideanEpigraph_iff (ha.2.1.trans hx)).mpr hb.le
  have him := image_tangentCone_subset
    (epigraphChainDerivative (l2CoordinateSum (ι := ι) (E := E))).hasFDerivAt
    (euclideanEpigraph (separablePi f)) ⟨_,ht,rfl⟩
  have hh := tangentCone_mono (epiSum_epigraph_image_subset f) _ him
  simp only [epigraphChainDerivative_apply,WithLp.toLp_fst,WithLp.toLp_snd,l2CoordinateSum_apply] at hh
  change WithLp.toLp 2 (∑ i, w i,b) ∈ tangentCone (euclideanEpigraph (finiteEpiSumValue f))
    (WithLp.toLp 2 (∑ i, a i,r)) at hh
  rw [ha.1] at hh
  exact hb'.not_ge ((mem_tangentCone_euclideanEpigraph_iff hx).mp hh)

/-- **Exercise 10.18**, the ordinary directional bound at any regular
optimal decomposition, with finite inf-addition for mixed infinite values. -/
theorem subderivative_finiteEpiSumValue_le_components {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) {a : PiLp 2 (fun _ : ι ↦ E)}
    (ha : a ∈ epiSumDecompositions f x) (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) (a i))
    (w : PiLp 2 (fun _ : ι ↦ E)) :
    subderivative (finiteEpiSumValue f) x (∑ i, w i) ≤
      finiteInfAddition (fun i ↦ subderivative (f i) (a i) (w i)) := by
  obtain ⟨c,hc⟩ := separablePi_finite_components (ha.2.1.trans hx)
  have he (i : ι) := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp (hr i)).2
  have hu := regularSubderivative_separablePi_le_finiteInfAddition hp hf a w c hc
  simp only [← he] at hu
  exact (subderivative_finiteEpiSumValue_le_at_decomposition hx ha w).trans
    ((subderivative_le_regularSubderivative (ha.2.1.trans hx) w).trans hu)

theorem subderivative_finiteEpiSumValue_le_iInf {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r)
    (hr : ∀ a ∈ epiSumDecompositions f x, ∀ i, IsSubdifferentiallyRegularAt (f i) (a i)) (w : E) :
    subderivative (finiteEpiSumValue f) x w ≤
      ⨅ a ∈ epiSumDecompositions f x, ⨅ v : {v : PiLp 2 (fun _ : ι ↦ E) // ∑ i, v i = w},
        finiteInfAddition (fun i ↦ subderivative (f i) (a i) (v.1 i)) := by
  refine le_iInf fun a ↦ le_iInf fun ha ↦ le_iInf fun v ↦ ?_
  simpa only [v.2] using subderivative_finiteEpiSumValue_le_components hp hf hx ha (hr a ha) v.1

/-- **Exercise 10.18**, the regular directional bound. The proof through
multiplier supports works without regularity of the individual summands. -/
theorem regularSubderivative_finiteEpiSumValue_le_iSup_iInf {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hb : HasBoundedEpiSumDecompositions f) {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) (w : E) :
    regularSubderivative (finiteEpiSumValue f) x w ≤
      ⨆ a ∈ epiSumDecompositions f x, ⨅ v : {v : PiLp 2 (fun _ : ι ↦ E) // ∑ i, v i = w},
        finiteInfAddition (fun i ↦ regularSubderivative (f i) (a i) (v.1 i)) := by
  by_contra! h
  obtain ⟨b,hb1,hb2⟩ := EReal.exists_between_coe_real h
  have hchoice (a : PiLp 2 (fun _ : ι ↦ E)) (ha : a ∈ epiSumDecompositions f x) :
      ∃ v : PiLp 2 (fun _ : ι ↦ E), (∑ i, v i) = w ∧ ∃ d : ι → ℝ,
        (∀ i, regularSubderivative (f i) (a i) (v i) ≤ (d i:EReal)) ∧ (∑ i, d i) < b := by
    have hi : (⨅ v : {v : PiLp 2 (fun _ : ι ↦ E) // ∑ i, v i = w},
        finiteInfAddition (fun i ↦ regularSubderivative (f i) (a i) (v.1 i))) < (b:EReal) :=
      (le_iSup₂ a ha).trans_lt hb1
    obtain ⟨v,hv⟩ := iInf_lt_iff.mp hi
    change (⨅ d : {d : ι → ℝ // ∀ i, regularSubderivative (f i) (a i) (v.1 i) ≤ (d i:EReal)},
      ((∑ i, d.1 i : ℝ):EReal)) < (b:EReal) at hv
    obtain ⟨d,hd⟩ := iInf_lt_iff.mp hv
    exact ⟨v.1,v.2,d.1,d.2,EReal.coe_lt_coe_iff.mp hd⟩
  have hl : LowerSemicontinuous (finiteEpiSumValue f) := lowerSemicontinuous_parametricValue (lowerSemicontinuous_finiteEpiSumIntegrand hp hf)
    (isProper_finiteEpiSumIntegrand hp) (isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb)
  have hloc : IsLocallyLscAt (finiteEpiSumValue f) x := locallyLscAt_of_lowerSemicontinuous_finite hl hx
  have hle : regularSubderivative (finiteEpiSumValue f) x w ≤ (b:EReal) := by
    apply (regularSubderivative_le_coe_iff_support_polar hx hloc).mpr
    constructor
    · apply (supportFunction_le_iff _ _ _).mpr
      intro y hy
      obtain ⟨a,ha,hy⟩ := (subdifferentials_finiteEpiSum_subset hp hf hb hx).2.1 hy
      obtain ⟨c,hc⟩ := separablePi_finite_components (ha.2.1.trans hx)
      obtain ⟨v,hv,d,hd,hdb⟩ := hchoice a ha
      apply EReal.coe_le_coe_iff.mpr
      rw [← hv,inner_sum]
      apply le_trans (Finset.sum_le_sum fun i _ ↦ ?_) hdb.le
      have hi := (regularSubderivative_le_coe_iff_support_polar (hc i)
        (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hc i))).mp (hd i)
      exact EReal.coe_le_coe_iff.mp ((supportFunction_le_iff _ _ _).mp hi.1 y (hy i))
    · intro y hy
      obtain ⟨a,ha,hy⟩ := (subdifferentials_finiteEpiSum_subset hp hf hb hx).2.2 hy
      obtain ⟨c,hc⟩ := separablePi_finite_components (ha.2.1.trans hx)
      obtain ⟨v,hv,d,hd,_⟩ := hchoice a ha
      rw [← hv,sum_inner]
      apply Finset.sum_nonpos
      intro i _
      have hi := (regularSubderivative_le_coe_iff_support_polar (hc i)
        (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hc i))).mp (hd i)
      exact hi.2 y (hy i)
  exact hb2.not_ge hle

end

end RW
