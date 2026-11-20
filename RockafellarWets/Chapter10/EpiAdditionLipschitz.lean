/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict continuity and the sharp Lipschitz estimate for epi-addition
-/
import RockafellarWets.Chapter10.EpiAdditionMinimizers
import RockafellarWets.Chapter10.SeparableSubderivatives
import RockafellarWets.Chapter10.CoordinateSubgradients

open Set Filter Topology Metric
open scoped InnerProductSpace ENNReal NNReal

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private def epiAdditionCoordinates : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((WithLp.fstL 2 ℝ E E).prod ((WithLp.sndL 2 ℝ E E)-(WithLp.fstL 2 ℝ E E)))

private theorem epiAdditionCoordinates_apply (q : WithLp 2 (E × E)) :
    epiAdditionCoordinates q = WithLp.toLp 2 (q.fst,q.snd-q.fst) := rfl

private theorem epiAdditionCoordinates_surjective : Function.Surjective (epiAdditionCoordinates (E := E)) := by
  intro q
  refine ⟨WithLp.toLp 2 (q.fst,q.snd+q.fst),?_⟩
  apply WithLp.ofLp_injective
  change (q.fst,q.snd+q.fst-q.fst) = q.ofLp
  exact Prod.ext rfl (by change q.snd+q.fst-q.fst = q.snd; abel)

private theorem epiAdditionCoordinates_adjoint (q : WithLp 2 (E × E)) :
    epiAdditionCoordinates.adjoint q = WithLp.toLp 2 (q.fst-q.snd,q.snd) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,epiAdditionCoordinates_apply]
  simp only [WithLp.prod_inner_apply,WithLp.toLp_fst,WithLp.toLp_snd,inner_sub_right,inner_sub_left]
  change ⟪q.fst,v.fst⟫_ℝ+(⟪q.snd,v.snd⟫_ℝ-⟪q.snd,v.fst⟫_ℝ) =
    ⟪q.fst,v.fst⟫_ℝ-⟪q.snd,v.fst⟫_ℝ+⟪q.snd,v.snd⟫_ℝ
  ring

/-- The parameter component of an integrand subgradient is a subgradient
of the translated finite summand. -/
theorem epiAddition_subgradient_snd {g : E → EReal} {h : E → ℝ}
    (hl : LowerSemicontinuous g) (hh : Continuous h) {q v : WithLp 2 (E × E)} {a : ℝ}
    (hq : epiAdditionIntegrand g h q = a)
    (hv : v ∈ subdifferential (epiAdditionIntegrand g h) q) :
    v.snd ∈ subdifferential (fun z ↦ (h z:EReal)) (q.snd-q.fst) := by
  have he : epiAdditionIntegrand g h = separableSum g (fun z ↦ (h z:EReal)) ∘ epiAdditionCoordinates := rfl
  obtain ⟨c,d,hc,hd⟩ := exists_coe_components_of_add_eq_coe hq
  rw [he,subdifferential_comp_eq_of_surjective (G := epiAdditionCoordinates (E := E))
    (g := separableSum g (fun z ↦ (h z:EReal))) (x := q) (epiAdditionCoordinates (E := E)).contDiff hq
    (by rw [ContinuousLinearMap.fderiv]; exact epiAdditionCoordinates_surjective),ContinuousLinearMap.fderiv] at hv
  obtain ⟨z,hz,hzv⟩ := hv
  have hs := (mem_subdifferential_separableSum_iff (hl q.fst)
    ((continuous_coe_real_ereal.comp hh).lowerSemicontinuous _) hc hd z).mp hz
  have hsnd := congrArg WithLp.snd hzv
  rw [epiAdditionCoordinates_adjoint] at hsnd
  exact hsnd ▸ hs.2

/-- The same component inclusion holds for horizon subgradients. -/
theorem epiAddition_horizonSubgradient_snd {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h)
    {q v : WithLp 2 (E × E)} {a : ℝ}
    (hq : epiAdditionIntegrand g h q = a)
    (hv : v ∈ horizonSubdifferential (epiAdditionIntegrand g h) q) :
    v.snd ∈ horizonSubdifferential (fun z ↦ (h z:EReal)) (q.snd-q.fst) := by
  have he : epiAdditionIntegrand g h = separableSum g (fun z ↦ (h z:EReal)) ∘ epiAdditionCoordinates := rfl
  have hpH : IsProper (fun z ↦ (h z:EReal)) := ⟨⟨0,EReal.coe_lt_top _⟩,fun _ ↦ EReal.bot_lt_coe _⟩
  have hH := (continuous_coe_real_ereal.comp hh).lowerSemicontinuous
  obtain ⟨c,d,hc,hd⟩ := exists_coe_components_of_add_eq_coe hq
  rw [he,horizonSubdifferential_comp_eq_of_surjective (G := epiAdditionCoordinates (E := E))
    (g := separableSum g (fun z ↦ (h z:EReal))) (x := q) (epiAdditionCoordinates (E := E)).contDiff
    (lowerSemicontinuous_separableSum hl hH hp hpH) hq
    (by rw [ContinuousLinearMap.fderiv]; exact epiAdditionCoordinates_surjective),ContinuousLinearMap.fderiv] at hv
  obtain ⟨z,hz,hzv⟩ := hv
  have hs := horizonSubdifferential_separableSum_subset (hl q.fst) (hH _) hc hd hz
  have hsnd := congrArg WithLp.snd hzv
  rw [epiAdditionCoordinates_adjoint] at hsnd
  exact hsnd ▸ hs.2

private theorem strict_coe {h : E → ℝ} {x : E} (hh : StrictlyContinuousAt h x) :
    ERealStrictlyContinuousAt (fun z ↦ (h z:EReal)) x := by
  refine ⟨Filter.Eventually.of_forall (fun z ↦ by simp),?_⟩
  simpa only [EReal.toReal_coe] using hh

/-- The horizon multiplier qualification is automatic for a strictly
continuous finite summand. -/
theorem epiAddition_horizonMultipliers_eq_zero {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : ∀x,StrictlyContinuousAt h x)
    (hb : EpiAdditionLocallyBounded g h) (x : E) :
    horizonParametricMultipliers (epiAdditionIntegrand g h) x = {0} := by
  have hc : Continuous h := continuous_iff_continuousAt.mpr (fun z ↦ (hh z).continuousAt)
  have hval := epiAddition_value_finite hp hl hc hb x
  apply Subset.antisymm
  · rintro y ⟨w,hw,hy⟩
    have hwy := epiAddition_horizonSubgradient_snd hp hl hc ((mem_parametricMinimizers.mp hw).1.trans hval) hy
    change y ∈ horizonSubdifferential (fun z ↦ (h z:EReal)) (x-w) at hwy
    have hsc := strict_coe (hh (x-w))
    rw [(eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero (f := fun z : E ↦ (h z:EReal)) (x := x-w) hsc.finite hsc.isLocallyLscAt).mp hsc] at hwy
    exact hwy
  · intro y hy
    obtain rfl := mem_singleton_iff.mp hy
    obtain ⟨w,hw⟩ := (epiAddition_minimizers_properties hp hl hc hb).1 x
    refine ⟨w,hw,?_⟩
    exact (mem_horizonSubdifferential_iff_zero_or_scaledSeq ((mem_parametricMinimizers.mp hw).1.trans hval)).mpr (Or.inl rfl)

/-- **Theorem 10.56**, strict continuity of the epi-sum. -/
theorem eRealStrictlyContinuousAt_epiAdditionValue {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : ∀x,StrictlyContinuousAt h x)
    (hb : EpiAdditionLocallyBounded g h) (x : E) :
    ERealStrictlyContinuousAt (parametricValue (epiAdditionIntegrand g h)) x := by
  have hc : Continuous h := continuous_iff_continuousAt.mpr (fun z ↦ (hh z).continuousAt)
  exact eRealStrictlyContinuousAt_parametricValue (lowerSemicontinuous_epiAdditionIntegrand hp hl hc)
    (isProper_epiAdditionIntegrand hp h) hb.parametric (epiAddition_value_finite hp hl hc hb x)
    (epiAddition_horizonMultipliers_eq_zero hp hl hh hb x)

/-- **Theorem 10.56**, the sharp local modulus is bounded by an attained
maximum of the summand's moduli over the minimizing decompositions. -/
theorem epiAdditionValue_modulus_le_max {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : ∀x,StrictlyContinuousAt h x)
    (hb : EpiAdditionLocallyBounded g h) (x : E) :
    ∃w ∈ parametricMinimizers (epiAdditionIntegrand g h) x,
      lipschitzModulus (fun z ↦ (parametricValue (epiAdditionIntegrand g h) z).toReal) x ≤ lipschitzModulus h (x-w) ∧
      (∀v ∈ parametricMinimizers (epiAdditionIntegrand g h) x,
        lipschitzModulus h (x-v) ≤ lipschitzModulus h (x-w)) ∧ lipschitzModulus h (x-w) < ⊤ := by
  have hc : Continuous h := continuous_iff_continuousAt.mpr (fun z ↦ (hh z).continuousAt)
  have hval := epiAddition_value_finite hp hl hc hb x
  obtain ⟨y,hy,hbound,_⟩ := parametricValue_modulus_le_max_multiplier
    (lowerSemicontinuous_epiAdditionIntegrand hp hl hc) (isProper_epiAdditionIntegrand hp h)
    hb.parametric hval (epiAddition_horizonMultipliers_eq_zero hp hl hh hb x)
  obtain ⟨v,hv,hyv⟩ := hy
  have hsub := epiAddition_subgradient_snd hl hc ((mem_parametricMinimizers.mp hv).1.trans hval) hyv
  have hnorm := (strict_coe (hh (x-v))).nnnorm_le_modulus_of_mem_subdifferential hsub
  simp only [WithLp.toLp_snd,EReal.toReal_coe] at hnorm
  have hcomp := epiAddition_minimizers_compact hp hl hc hb x
  have husc : UpperSemicontinuous (fun w : E ↦ lipschitzModulus h (x-w)) :=
    (upperSemicontinuous_lipschitzModulusWithin h univ).comp (continuous_const.sub continuous_id)
  obtain ⟨w,hw,hm⟩ := (husc.upperSemicontinuousOn _).exists_isMaxOn ⟨v,hv⟩ hcomp
  exact ⟨w,hw,hbound.trans (hnorm.trans (hm hv)),fun z hz ↦ hm hz,hh (x-w)⟩

end RW
end
