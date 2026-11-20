/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Addition formulas that do not require a closed graph

Regular coderivatives transform under a strict derivative at the point.
Limiting coderivatives transform for arbitrary graphs under C¹ smoothness
on a neighborhood.
-/
import RockafellarWets.Chapter10.PerturbedCompositeObjectives
import RockafellarWets.Chapter10.GraphicalAddition

open Filter Set Topology
open scoped Pointwise

namespace RW
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {f : E → F} {x : E} {u : F} {A : E →L[ℝ] F}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hasStrictFDerivAt_parameterShift (hf : HasStrictFDerivAt f A x) (u : F) :
    HasStrictFDerivAt (parameterShift f) (parameterShiftDerivative A) (WithLp.toLp 2 (x,u)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.hasStrictFDerivAt.comp _
    ((WithLp.fstL 2 ℝ E F).hasStrictFDerivAt.prodMk
      ((hf.comp _ (WithLp.fstL 2 ℝ E F).hasStrictFDerivAt).add (WithLp.sndL 2 ℝ E F).hasStrictFDerivAt))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiffAt_parameterShift (hf : ContDiffAt ℝ 1 f x) (u : F) :
    ContDiffAt ℝ 1 (parameterShift f) (WithLp.toLp 2 (x,u)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.contDiff.contDiffAt.comp _
    ((WithLp.fstL 2 ℝ E F).contDiff.contDiffAt.prodMk
      ((hf.comp _ (WithLp.fstL 2 ℝ E F).contDiff.contDiffAt).add (WithLp.sndL 2 ℝ E F).contDiff.contDiffAt))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem euclideanSvGraph_svAdd_single_preimage :
    euclideanSvGraph (svAdd S (svSingleton f)) = parameterShift (fun a ↦ -f a) ⁻¹' euclideanSvGraph S := by
  ext p
  change (p.snd ∈ svAdd S (svSingleton f) p.fst) ↔ (-f p.fst+p.snd ∈ S p.fst)
  rw [mem_svAdd_single]
  simp only [sub_eq_add_neg,add_comm]

private theorem parameterShift_normal_fiber (D : Set (WithLp 2 (E × F))) (y : F) :
    {v : E | WithLp.toLp 2 (v,-y) ∈ (parameterShiftDerivative (-A)).adjoint '' D} =
      {v : E | WithLp.toLp 2 (v,-y) ∈ D}+{A.adjoint y} := by
  ext v
  constructor
  · rintro ⟨q,hq,he⟩
    rw [parameterShiftDerivative_adjoint] at he
    have hs : q.snd = -y := congrArg WithLp.snd he
    have hv : q.fst+A.adjoint y=v := by
      have hh := congrArg WithLp.fst he
      simpa only [hs,map_neg,ContinuousLinearMap.neg_apply,map_neg,neg_neg] using hh
    refine ⟨q.fst,?_,A.adjoint y,rfl,hv⟩
    simpa only [← hs] using hq
  · rintro ⟨z,hz,b,hb,rfl⟩
    have hb' : b=A.adjoint y := hb
    refine ⟨WithLp.toLp 2 (z,-y),hz,?_⟩
    rw [parameterShiftDerivative_adjoint]
    simp only [WithLp.toLp_fst,WithLp.toLp_snd,map_neg,
      ContinuousLinearMap.neg_apply,map_neg,neg_neg,hb']

/-- The regular coderivative identity is valid without any graph closedness. -/
theorem regularCoderivative_svAdd_single (hf : HasStrictFDerivAt f A x) (y : F) :
    regularCoderivative (svAdd S (svSingleton f)) x (u+f x) y =
      regularCoderivative S x u y+{A.adjoint y} := by
  have hd := hasStrictFDerivAt_parameterShift hf.neg (u+f x)
  change HasStrictFDerivAt (parameterShift (fun a ↦ -f a)) (parameterShiftDerivative (-A)) (WithLp.toLp 2 (x,u+f x)) at hd
  have he := regularNormalCone_preimage_of_surjective hd (parameterShiftDerivative_surjective (-A)) (euclideanSvGraph S)
  have hbase : parameterShift (fun a ↦ -f a) (WithLp.toLp 2 (x,u+f x)) = WithLp.toLp 2 (x,u) := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · rfl
    · change -f x+(u+f x)=u
      abel
  rw [← euclideanSvGraph_svAdd_single_preimage (S := S) (f := f),hbase] at he
  unfold regularCoderivative
  rw [he]
  exact parameterShift_normal_fiber _ y

/-- For arbitrary graphs, C¹ smoothness near the point supplies the limiting rule. -/
theorem coderivative_svAdd_single_of_contDiffAt (hf : ContDiffAt ℝ 1 f x) (y : F) :
    coderivative (svAdd S (svSingleton f)) x (u+f x) y =
      coderivative S x u y+{(fderiv ℝ f x).adjoint y} := by
  have hd := hasFDerivAt_parameterShift (hf.differentiableAt one_ne_zero).hasFDerivAt.neg (u+f x)
  change HasFDerivAt (parameterShift (fun a ↦ -f a)) (parameterShiftDerivative (-(fderiv ℝ f x))) (WithLp.toLp 2 (x,u+f x)) at hd
  have he := normalCone_preimage_of_surjective (contDiffAt_parameterShift hf.neg (u+f x))
    (hd.fderiv.symm ▸ parameterShiftDerivative_surjective (-(fderiv ℝ f x))) (euclideanSvGraph S)
  rw [hd.fderiv] at he
  have hbase : parameterShift (fun a ↦ -f a) (WithLp.toLp 2 (x,u+f x)) = WithLp.toLp 2 (x,u) := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · rfl
    · change -f x+(u+f x)=u
      abel
  rw [← euclideanSvGraph_svAdd_single_preimage (S := S) (f := f),hbase] at he
  unfold coderivative
  rw [he]
  exact parameterShift_normal_fiber _ y

end RW
