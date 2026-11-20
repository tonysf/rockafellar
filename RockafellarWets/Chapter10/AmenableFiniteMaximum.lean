/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Amenability of finite smooth maxima
-/
import RockafellarWets.Chapter10.AmenableExamples
import RockafellarWets.Chapter7.MaxFunctionRegularity
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Classical
open scoped InnerProductSpace

noncomputable section
namespace RW
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def euclideanMaximum (v : EuclideanSpace ℝ ι) : ℝ := finiteMax (fun i (v : EuclideanSpace ℝ ι) ↦ v i) v

private theorem euclideanMaximum_piecewiseLinear :
    IsPiecewiseLinear (fun v : EuclideanSpace ℝ ι ↦ (euclideanMaximum v:EReal)) := by
  let e := (Fintype.equivFin ι).symm
  let C (i : Fin (Fintype.card ι)) : Set (EuclideanSpace ℝ ι) := {v | ∀j, v j ≤ v (e i)}
  have hC (i : Fin (Fintype.card ι)) : IsPolyhedral (C i) := by
    have hj (j : ι) : IsPolyhedral {v : EuclideanSpace ℝ ι | v j ≤ v (e i)} := by
      let L : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
        innerSL ℝ (EuclideanSpace.single j 1)-innerSL ℝ (EuclideanSpace.single (e i) 1)
      have he : {v : EuclideanSpace ℝ ι | v j ≤ v (e i)} = {v | L v ≤ 0} := by
        ext v
        change v j ≤ v (e i) ↔ _
        simp only [mem_setOf_eq,L,ContinuousLinearMap.sub_apply,innerSL_apply_apply,EuclideanSpace.inner_single_left,
          map_one,one_mul,sub_nonpos]
      rw [he]
      exact isPolyhedral_linearHalfspace L 0
    have hh := IsPolyhedral.iInter_finset (E := EuclideanSpace ℝ ι) Finset.univ
      (fun j : ι ↦ {v : EuclideanSpace ℝ ι | v j ≤ v (e i)}) (fun j _ ↦ hj j)
    convert hh using 1
    ext v
    simp only [C,mem_setOf_eq,mem_iInter,Finset.mem_univ,forall_const]
  refine ⟨Fintype.card ι,C,fun i ↦ EuclideanSpace.single (e i) 1,fun _ ↦ 0,hC,?_,?_⟩
  · ext v
    constructor
    · intro _
      obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ v i)
      refine mem_iUnion.mpr ⟨Fintype.equivFin ι i,?_⟩
      intro j
      change v j ≤ v (e (Fintype.equivFin ι i))
      rw [show e (Fintype.equivFin ι i) = i from (Fintype.equivFin ι).symm_apply_apply i]
      exact (le_finiteMax (fun i (v : EuclideanSpace ℝ ι) ↦ v i) v j).trans_eq hi
    · intro _
      exact EReal.coe_lt_top _
  · intro i v hv
    have he : euclideanMaximum v = v (e i) :=
      le_antisymm (finiteMax_le_iff.mpr hv) (le_finiteMax (fun i (v : EuclideanSpace ℝ ι) ↦ v i) v (e i))
    simp only [he,EuclideanSpace.inner_single_left,map_one,one_mul,add_zero]

private theorem convex_epigraph_euclideanMaximum :
    Convex ℝ (epigraph (fun v : EuclideanSpace ℝ ι ↦ (euclideanMaximum v:EReal))) := by
  intro p hp q hq a b ha hb hab
  change (euclideanMaximum (a • p.1+b • q.1):EReal) ≤ ((a*p.2+b*q.2:ℝ):EReal)
  rw [EReal.coe_le_coe_iff]
  apply finiteMax_le_iff.mpr
  intro i
  change (euclideanMaximum p.1:EReal) ≤ (p.2:EReal) at hp
  change (euclideanMaximum q.1:EReal) ≤ (q.2:EReal) at hq
  have hp' : p.1 i ≤ p.2 := (le_finiteMax (fun i (v : EuclideanSpace ℝ ι) ↦ v i) p.1 i).trans (EReal.coe_le_coe_iff.mp hp)
  have hq' : q.1 i ≤ q.2 := (le_finiteMax (fun i (v : EuclideanSpace ℝ ι) ↦ v i) q.1 i).trans (EReal.coe_le_coe_iff.mp hq)
  exact add_le_add (mul_le_mul_of_nonneg_left hp' ha) (mul_le_mul_of_nonneg_left hq' hb)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The maximum model uses a finite piecewise-linear convex outer function. -/
def finiteMaximumAmenableModel (f : ι → E → ℝ) (x : E) {r : ℕ} (full : Bool)
    (hf : ∀i, ContDiff ℝ r (f i)) :
    AmenableFunctionModel (fun y ↦ (finiteMax f y:EReal)) x r full where
  Target := EuclideanSpace ℝ ι
  outer := fun v ↦ (euclideanMaximum v:EReal)
  inner := fun y ↦ WithLp.toLp 2 (fun i ↦ f i y)
  neighborhood := univ
  isOpen := isOpen_univ
  mem := mem_univ x
  finite := ⟨EReal.coe_ne_bot _,EReal.coe_ne_top _⟩
  proper := ⟨⟨0,EReal.coe_lt_top _⟩,fun _ ↦ EReal.bot_lt_coe _⟩
  lsc := euclideanMaximum_piecewiseLinear.isPiecewiseLinearQuadratic.lowerSemicontinuous
  convex := convex_epigraph_euclideanMaximum
  smooth := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr hf)).contDiffOn
  eqOn := fun _ _ ↦ rfl
  qualification := by
    intro v hv _
    have he : effectiveDomain (fun v : EuclideanSpace ℝ ι ↦ (euclideanMaximum v:EReal)) = univ := by
      ext v
      simp [effectiveDomain]
    simpa only [he,closure_univ,normalCone_univ,mem_singleton_iff] using hv
  plq := fun _ ↦ euclideanMaximum_piecewiseLinear.isPiecewiseLinearQuadratic

/-- **Example 10.24(e)**, the maximum of finitely many C¹ functions is amenable. -/
theorem amenableAt_finiteMax (f : ι → E → ℝ) (x : E) (hf : ∀i, ContDiff ℝ 1 (f i)) :
    AmenableAt (fun y ↦ (finiteMax f y:EReal)) x := ⟨finiteMaximumAmenableModel f x false hf⟩

/-- **Example 10.24(e)**, the maximum of finitely many C² functions is fully amenable. -/
theorem fullyAmenableAt_finiteMax (f : ι → E → ℝ) (x : E) (hf : ∀i, ContDiff ℝ 2 (f i)) :
    FullyAmenableAt (fun y ↦ (finiteMax f y:EReal)) x := ⟨finiteMaximumAmenableModel f x true hf⟩

end RW
end
