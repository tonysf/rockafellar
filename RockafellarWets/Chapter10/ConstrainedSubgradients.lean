/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Constrained objectives and epigraph regularity
-/

import RockafellarWets.Chapter10.SumSubgradients
import RockafellarWets.Chapter8.IndicatorSubgradients
import RockafellarWets.Chapter8.SmoothSubderivativeRegularity

open Set
open scoped Pointwise InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Set E} {g : E → EReal} {x : E} {c : ℝ}

/-- A proper function restricted to a set has the intersected epigraph. -/
theorem euclideanEpigraph_indicator_add (hp : IsProper g) :
    euclideanEpigraph (indicatorVA X+g) = l2ProdSet X univ ∩ euclideanEpigraph g := by
  ext q
  by_cases hq : q.fst ∈ X
  · simp [euclideanEpigraph,epigraph,indicatorVA_apply_mem hq,l2ProdSet,hq]
  · simp [euclideanEpigraph,epigraph,indicatorVA_apply_not_mem hq,l2ProdSet,hq,
      EReal.top_add_of_ne_bot (hp.2 _).ne']

private theorem indicator_sum_qualification (hx : x ∈ X)
    (hQ : ∀ y ∈ horizonSubdifferential g x, -y ∈ normalCone X x → y = 0) :
    ∀ u ∈ horizonSubdifferential (indicatorVA X) x,
      ∀ v ∈ horizonSubdifferential g x, u+v = 0 → u = 0 ∧ v = 0 := by
  intro u hu v hv he
  rw [horizonSubdifferential_indicatorVA] at hu
  have hvu : -v = u := by rw [neg_eq_iff_add_eq_zero]; simpa only [add_comm] using he
  have hv0 := hQ v hv (hvu.symm ▸ hu)
  exact ⟨by simpa only [hv0,add_zero] using he,hv0⟩

theorem subdifferential_indicator_add_subset (hX : IsClosed X) (hl : LowerSemicontinuous g)
    (hp : IsProper g) (hx : x ∈ X) (hc : g x = c)
    (hQ : ∀ y ∈ horizonSubdifferential g x, -y ∈ normalCone X x → y = 0) :
    subdifferential (indicatorVA X+g) x ⊆ normalCone X x+subdifferential g x := by
  simpa only [subdifferential_indicatorVA] using subdifferential_add_subset
    (lowerSemicontinuous_indicatorVA hX) hl ((indicatorVA_isProper_iff X).mpr ⟨x,hx⟩)
    hp (indicatorVA_apply_mem hx) hc (indicator_sum_qualification hx hQ)

theorem horizonSubdifferential_indicator_add_subset (hX : IsClosed X) (hl : LowerSemicontinuous g)
    (hp : IsProper g) (hx : x ∈ X) (hc : g x = c)
    (hQ : ∀ y ∈ horizonSubdifferential g x, -y ∈ normalCone X x → y = 0) :
    horizonSubdifferential (indicatorVA X+g) x ⊆ normalCone X x+horizonSubdifferential g x := by
  simpa only [horizonSubdifferential_indicatorVA] using horizonSubdifferential_add_subset
    (lowerSemicontinuous_indicatorVA hX) hl ((indicatorVA_isProper_iff X).mpr ⟨x,hx⟩)
    hp (indicatorVA_apply_mem hx) hc (indicator_sum_qualification hx hQ)

/-- Restriction preserves regularity under the horizon-normal qualification,
without a calmness assumption on the function. -/
theorem IsSubdifferentiallyRegularAt.indicator_add (hr : IsSubdifferentiallyRegularAt g x)
    (hX : IsClosed X) (hl : LowerSemicontinuous g) (hp : IsProper g) (hx : x ∈ X)
    (hR : IsClarkeRegularAt X x)
    (hQ : ∀ y ∈ horizonSubdifferential g x, -y ∈ normalCone X x → y = 0) :
    IsSubdifferentiallyRegularAt (indicatorVA X+g) x := by
  let c := (g x).toReal
  have hc : g x = c := (EReal.coe_toReal hr.2.1 hr.1).symm
  have hval : (indicatorVA X+g) x = c := by
    change indicatorVA X x+g x = _
    rw [indicatorVA_apply_mem hx,zero_add]
    exact hc
  have hC : IsClosed (l2ProdSet X (univ : Set ℝ)) := isClosed_l2ProdSet hX isClosed_univ
  have hD : IsClosed (euclideanEpigraph g) := (isClosed_epigraph_of_lsc_ereal g hl).preimage (l2ProdEquiv E).continuous
  let I := ContinuousLinearMap.id ℝ (WithLp 2 (E × ℝ))
  have hqual : NormalConstraintQualification (l2ProdSet X univ) (euclideanEpigraph g)
      (fderiv ℝ I (WithLp.toLp 2 (x,c))) (WithLp.toLp 2 (x,c)) (I (WithLp.toLp 2 (x,c))) := by
    rw [I.fderiv]
    intro q hq hn
    simp only [I,ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] at hn
    rw [normalCone_l2ProdSet,normalCone_univ] at hn
    have hb : q.snd = 0 := neg_eq_zero.mp hn.2
    have hh : WithLp.toLp 2 (q.fst,(0:ℝ)) ∈ normalCone (euclideanEpigraph g) (WithLp.toLp 2 (x,c)) := by
      simpa only [← hb] using hq
    have hv := hQ q.fst ((mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hr.isLocallyLscAt hc).mpr hh) hn.1
    apply WithLp.ofLp_injective
    exact Prod.ext hv hb
  have hcr := (isClarkeRegularAt_l2ProdSet_iff hX isClosed_univ hx (mem_univ c)).mpr ⟨hR,isClarkeRegularAt_univ c⟩
  have hreg := (clarkeRegularity_constraints hC hD I.contDiff
    (show WithLp.toLp 2 (x,c) ∈ l2ProdSet X univ ∩ I ⁻¹' euclideanEpigraph g from ⟨⟨hx,mem_univ _⟩,hc.le⟩)
    hqual hcr hr.2.2).1
  refine ⟨hval ▸ EReal.coe_ne_bot _,hval ▸ EReal.coe_ne_top _,?_⟩
  rw [hval,EReal.toReal_coe]
  change IsClarkeRegularAt (euclideanEpigraph (indicatorVA X+g)) (WithLp.toLp 2 (x,c))
  rw [euclideanEpigraph_indicator_add hp]
  exact hreg

/-- Exact limiting subgradients for a regular constrained objective. -/
theorem subdifferential_indicator_add_eq (hr : IsSubdifferentiallyRegularAt g x)
    (hX : IsClosed X) (hl : LowerSemicontinuous g) (hp : IsProper g) (hx : x ∈ X)
    (hR : IsClarkeRegularAt X x)
    (hQ : ∀ y ∈ horizonSubdifferential g x, -y ∈ normalCone X x → y = 0) :
    subdifferential (indicatorVA X+g) x = normalCone X x+subdifferential g x := by
  have hc := (EReal.coe_toReal hr.2.1 hr.1).symm
  apply Subset.antisymm (subdifferential_indicator_add_subset hX hl hp hx hc hQ)
  rw [hR.2,hr.subdifferential_eq_regularSubdifferential,← regularSubdifferential_indicatorVA]
  exact (regularSubdifferential_add_superset (indicatorVA_apply_mem hx) hc).trans
    (regularSubdifferential_subset_subdifferential _ _)

/-- Exact horizon subgradients for a regular constrained objective. -/
theorem horizonSubdifferential_indicator_add_eq (hr : IsSubdifferentiallyRegularAt g x)
    (hX : IsClosed X) (hl : LowerSemicontinuous g) (hp : IsProper g) (hx : x ∈ X)
    (hR : IsClarkeRegularAt X x)
    (hQ : ∀ y ∈ horizonSubdifferential g x, -y ∈ normalCone X x → y = 0) :
    horizonSubdifferential (indicatorVA X+g) x = normalCone X x+horizonSubdifferential g x := by
  have hc := (EReal.coe_toReal hr.2.1 hr.1).symm
  have hval : (indicatorVA X+g) x = ((g x).toReal:EReal) := by
    change indicatorVA X x+g x = _
    rw [indicatorVA_apply_mem hx,zero_add]
    exact hc
  apply Subset.antisymm (horizonSubdifferential_indicator_add_subset hX hl hp hx hc hQ)
  rintro v ⟨a,ha,b,hb,rfl⟩
  apply ((hr.indicator_add hX hl hp hx hR hQ).mem_horizonSubdifferential_iff_regularNormal hval).mpr
  rw [euclideanEpigraph_indicator_add hp]
  have ha' : WithLp.toLp 2 (a,(0:ℝ)) ∈ regularNormalCone (l2ProdSet X univ) (WithLp.toLp 2 (x,(g x).toReal)) := by
    rw [regularNormalCone_l2ProdSet,regularNormalCone_univ]
    exact ⟨hR.2 ▸ ha,rfl⟩
  have hb' := (hr.mem_horizonSubdifferential_iff_regularNormal hc).mp hb
  have hh := adjoint_regularNormalCone_add_subset_constraints
    (show WithLp.toLp 2 (x,(g x).toReal) ∈ l2ProdSet X univ ∩
      (ContinuousLinearMap.id ℝ (WithLp 2 (E × ℝ))) ⁻¹' euclideanEpigraph g from ⟨⟨hx,mem_univ _⟩,hc.le⟩)
    (ContinuousLinearMap.id ℝ (WithLp 2 (E × ℝ))).hasFDerivAt
    ⟨WithLp.toLp 2 (b,(0:ℝ)),⟨_,hb',by simp only [ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply]⟩,WithLp.toLp 2 (a,(0:ℝ)),ha',rfl⟩
  change WithLp.toLp 2 (b+a,(0:ℝ)+0) ∈ regularNormalCone
    (l2ProdSet X univ ∩ euclideanEpigraph g) (WithLp.toLp 2 (x,(g x).toReal)) at hh
  simpa only [add_comm b a,add_zero] using hh

end RW
