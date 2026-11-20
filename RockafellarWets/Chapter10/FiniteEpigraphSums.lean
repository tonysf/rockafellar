/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Euclidean epigraph sums for finite epi-addition
-/

import RockafellarWets.Chapter10.FiniteEpiSumDirections

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

set_option maxHeartbeats 1000000

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem l2CoordinateSum_image_epigraphs (f : ι → E → EReal) :
    (l2CoordinateSum (ι := ι) (E := WithLp 2 (E × ℝ))) '' l2PiSet (fun i ↦ euclideanEpigraph (f i)) =
      (l2ProdEquiv E) ⁻¹' finiteSetSum (fun i ↦ epigraph (f i)) := by
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨fun i ↦ (l2ProdEquiv E) (p i),hp,?_⟩
    rw [l2CoordinateSum_apply,map_sum]
  · rintro ⟨p,hp,he⟩
    refine ⟨WithLp.toLp 2 (fun i ↦ (l2ProdEquiv E).symm (p i)),hp,?_⟩
    apply (l2ProdEquiv E).injective
    rw [l2CoordinateSum_apply,map_sum]
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using he

theorem closure_euclideanEpigraph_finiteEpiSum [Nonempty ι] (f : ι → E → EReal) :
    closure (euclideanEpigraph (finiteEpiSum f)) =
      closure ((l2CoordinateSum (ι := ι) (E := WithLp 2 (E × ℝ))) ''
        l2PiSet (fun i ↦ euclideanEpigraph (f i))) := by
  change closure ((l2ProdEquiv E) ⁻¹' epigraph (finiteEpiSum f)) = _
  have hcl (S : Set (E × ℝ)) : (l2ProdEquiv E) ⁻¹' closure S = closure ((l2ProdEquiv E) ⁻¹' S) :=
    (l2ProdEquiv E).toHomeomorph.preimage_closure S
  rw [← hcl,closure_epigraph_finiteEpiSum,hcl,← l2CoordinateSum_image_epigraphs]

/-- Under the compactness hypothesis the epigraph sum is attained, including
all heights above the minimum. -/
theorem euclideanEpigraph_finiteEpiSumValue [Nonempty ι] {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hb : HasBoundedEpiSumDecompositions f) :
    euclideanEpigraph (finiteEpiSumValue f) =
      (l2CoordinateSum (ι := ι) (E := WithLp 2 (E × ℝ))) '' l2PiSet (fun i ↦ euclideanEpigraph (f i)) := by
  classical
  rw [l2CoordinateSum_image_epigraphs]
  have hproper : IsProper (finiteEpiSumValue f) := isProper_parametricValue (f := finiteEpiSumIntegrand f) (lowerSemicontinuous_finiteEpiSumIntegrand hp hf)
    (isProper_finiteEpiSumIntegrand hp) (isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb)
  ext q
  constructor
  · intro hq
    have hqtop : finiteEpiSumValue f q.fst < ⊤ := hq.trans_lt (EReal.coe_lt_top _)
    have hx : finiteEpiSumValue f q.fst = ((finiteEpiSumValue f q.fst).toReal:EReal) :=
      (EReal.coe_toReal hqtop.ne (hproper.2 q.fst).ne').symm
    obtain ⟨a,ha⟩ := parametricMinimizers_nonempty (f := finiteEpiSumIntegrand f) (u := q.fst) (lowerSemicontinuous_finiteEpiSumIntegrand hp hf)
      (isProper_finiteEpiSumIntegrand hp) (isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb) hqtop
    rw [parametricMinimizers_finiteEpiSumIntegrand hp] at ha
    obtain ⟨c,hc⟩ := separablePi_finite_components (ha.2.1.trans hx)
    have hsum : ∑ i, c i = (finiteEpiSumValue f q.fst).toReal :=
      EReal.coe_eq_coe_iff.mp ((separablePi_eq_coe hc).symm.trans (ha.2.1.trans hx))
    let j : ι := Classical.arbitrary ι
    let δ : ℝ := q.snd-(finiteEpiSumValue f q.fst).toReal
    have hδ : 0 ≤ δ := sub_nonneg.mpr (EReal.coe_le_coe_iff.mp (hx ▸ hq))
    refine ⟨fun i ↦ (a i,c i+if i=j then δ else 0),?_,?_⟩
    · intro i
      change f i (a i) ≤ ((c i+if i=j then δ else 0:ℝ):EReal)
      rw [hc i]
      apply EReal.coe_le_coe_iff.mpr
      exact le_add_of_nonneg_right (by split_ifs <;> positivity)
    · apply Prod.ext
      · simpa only [Prod.fst_sum] using ha.1
      · rw [Prod.snd_sum]
        change (∑ i, (c i+if i=j then δ else 0)) = q.snd
        simp [Finset.sum_add_distrib,hsum,δ]
  · intro hq
    have hh := finiteSetSum_epigraph_subset_epigraph_finiteEpiSum f hq
    rw [← finiteEpiSumValue_eq_finiteEpiSum hp] at hh
    exact hh

end

end RW
