/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Perturbed composite objectives and their joint multipliers
-/

import RockafellarWets.Chapter10.SeparableRegularity
import RockafellarWets.Chapter10.CoordinateSubgradients
import RockafellarWets.Chapter8.SubgradientsAndGradients
import RockafellarWets.Chapter8.IndicatorSubgradients

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]

/-- The parameter shift that absorbs the smooth constraint mapping. -/
def parameterShift (F : E → P) (q : WithLp 2 (E × P)) : WithLp 2 (E × P) :=
  WithLp.toLp 2 (q.fst,F q.fst+q.snd)

def parameterShiftDerivative (A : E →L[ℝ] P) : WithLp 2 (E × P) →L[ℝ] WithLp 2 (E × P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.comp
    ((WithLp.fstL 2 ℝ E P).prod (A.comp (WithLp.fstL 2 ℝ E P)+(WithLp.sndL 2 ℝ E P)))

@[simp] theorem parameterShiftDerivative_apply (A : E →L[ℝ] P) (q : WithLp 2 (E × P)) :
    parameterShiftDerivative A q = WithLp.toLp 2 (q.fst,A q.fst+q.snd) := rfl

@[simp] theorem parameterShiftDerivative_adjoint (A : E →L[ℝ] P) (q : WithLp 2 (E × P)) :
    (parameterShiftDerivative A).adjoint q = WithLp.toLp 2 (q.fst+A.adjoint q.snd,q.snd) := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left,parameterShiftDerivative_apply,
    WithLp.prod_inner_apply,WithLp.prod_inner_apply,inner_add_right,inner_add_left,
    ContinuousLinearMap.adjoint_inner_left]
  change ⟪q.fst,w.fst⟫_ℝ+(⟪q.snd,A w.fst⟫_ℝ+⟪q.snd,w.snd⟫_ℝ) =
    (⟪q.fst,w.fst⟫_ℝ+⟪q.snd,A w.fst⟫_ℝ)+⟪q.snd,w.snd⟫_ℝ
  ring

theorem parameterShiftDerivative_surjective (A : E →L[ℝ] P) :
    Function.Surjective (parameterShiftDerivative A) := by
  intro q
  refine ⟨WithLp.toLp 2 (q.fst,q.snd-A q.fst),?_⟩
  simp only [parameterShiftDerivative_apply,WithLp.toLp_fst,WithLp.toLp_snd,add_sub_cancel]
  rfl

theorem contDiff_parameterShift {F : E → P} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (parameterShift F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.contDiff.comp
    ((WithLp.fstL 2 ℝ E P).contDiff.prodMk
      ((hF.comp (WithLp.fstL 2 ℝ E P).contDiff).add (WithLp.sndL 2 ℝ E P).contDiff))

theorem hasFDerivAt_parameterShift {F : E → P} {A : E →L[ℝ] P} {x : E}
    (hF : HasFDerivAt F A x) (u : P) :
    HasFDerivAt (parameterShift F) (parameterShiftDerivative A) (WithLp.toLp 2 (x,u)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.hasFDerivAt.comp _
    ((WithLp.fstL 2 ℝ E P).hasFDerivAt.prodMk
      ((hF.comp _ (WithLp.fstL 2 ℝ E P).hasFDerivAt).add (WithLp.sndL 2 ℝ E P).hasFDerivAt))

theorem gradient_comp_fst {k : E → ℝ} {x : E} (hk : DifferentiableAt ℝ k x) (u : P) :
    gradient (fun q : WithLp 2 (E × P) ↦ k q.fst) (WithLp.toLp 2 (x,u)) =
      WithLp.toLp 2 (gradient k x,0) := by
  have hd := hk.hasGradientAt.hasFDerivAt.comp (WithLp.toLp 2 (x,u)) (WithLp.fstL 2 ℝ E P).hasFDerivAt
  have he : (InnerProductSpace.toDual ℝ E (gradient k x)).comp (WithLp.fstL 2 ℝ E P) =
      InnerProductSpace.toDual ℝ (WithLp 2 (E × P)) (WithLp.toLp 2 (gradient k x,0)) := by
    ext q
    simp [InnerProductSpace.toDual_apply_apply,WithLp.prod_inner_apply]
  rw [he] at hd
  simpa only [LinearIsometryEquiv.symm_apply_apply] using (hd.hasGradientAt).gradient

/-- The perturbed constrained objective in Example 10.15. -/
def perturbedCompositeObjective (X : Set E) (k : E → ℝ) (F : E → P) (θ : P → EReal)
    (q : WithLp 2 (E × P)) : EReal :=
  separableSum (indicatorVA X) θ (parameterShift F q)+(k q.fst : EReal)

theorem lowerSemicontinuous_perturbedCompositeObjective {X : Set E} {k : E → ℝ} {F : E → P}
    {θ : P → EReal} (hX : IsClosed X) (hne : X.Nonempty) (hk : Continuous k)
    (hF : Continuous F) (hθ : LowerSemicontinuous θ) (hpθ : IsProper θ) :
    LowerSemicontinuous (perturbedCompositeObjective X k F θ) := by
  have hpi := (indicatorVA_isProper_iff X).mpr hne
  have hg := lowerSemicontinuous_separableSum (lowerSemicontinuous_indicatorVA hX) hθ hpi hpθ
  have hshift : Continuous (parameterShift F) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.continuous.comp
      ((WithLp.fstL 2 ℝ E P).continuous.prodMk
        ((hF.comp (WithLp.fstL 2 ℝ E P).continuous).add (WithLp.sndL 2 ℝ E P).continuous))
  apply LowerSemicontinuous.add' (hg.comp hshift)
    ((continuous_coe_real_ereal.comp (hk.comp (WithLp.fstL 2 ℝ E P).continuous)).lowerSemicontinuous)
  intro q
  exact EReal.continuousAt_add (.inr (EReal.coe_ne_bot _))
    (.inl (EReal.bot_lt_add_iff.mpr ⟨hpi.2 _,hpθ.2 _⟩).ne')

theorem isProper_perturbedCompositeObjective {X : Set E} {k : E → ℝ} {F : E → P}
    {θ : P → EReal} (hne : X.Nonempty) (hpθ : IsProper θ) :
    IsProper (perturbedCompositeObjective X k F θ) := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨z,hz⟩ := hpθ.1
  have hc : θ z = ((θ z).toReal : EReal) := (EReal.coe_toReal hz.ne (hpθ.2 z).ne').symm
  constructor
  · refine ⟨WithLp.toLp 2 (x,z-F x),?_⟩
    have hv : perturbedCompositeObjective X k F θ (WithLp.toLp 2 (x,z-F x)) =
        (((θ z).toReal+k x : ℝ) : EReal) := by
      simp only [perturbedCompositeObjective,separableSum,parameterShift,WithLp.toLp_fst,
        WithLp.toLp_snd,indicatorVA_apply_mem hx,zero_add]
      rw [show F x+(z-F x)=z by abel,hc,← EReal.coe_add]
      simp only [EReal.toReal_coe]
    rw [hv]
    exact EReal.coe_lt_top _
  · intro q
    apply EReal.bot_lt_add_iff.mpr
    refine ⟨EReal.bot_lt_add_iff.mpr ⟨?_,hpθ.2 _⟩,EReal.bot_lt_coe _⟩
    exact ((indicatorVA_isProper_iff X).mpr ⟨x,hx⟩).2 _

theorem perturbedCompositeObjective_finite_components {X : Set E} {k : E → ℝ} {F : E → P}
    {θ : P → EReal} {x : E} {u : P} {a : ℝ} (hpθ : IsProper θ)
    (ha : perturbedCompositeObjective X k F θ (WithLp.toLp 2 (x,u)) = a) :
    x ∈ X ∧ ∃ c : ℝ, θ (F x+u) = c := by
  have hx : x ∈ X := by
    by_contra h
    simp only [perturbedCompositeObjective,separableSum,parameterShift,WithLp.toLp_fst,
      WithLp.toLp_snd,indicatorVA_apply_not_mem h,EReal.top_add_of_ne_bot (hpθ.2 _).ne',
      EReal.top_add_coe] at ha
    exact EReal.coe_ne_top a ha.symm
  have htop : θ (F x+u) ≠ ⊤ := by
    intro h
    simp only [perturbedCompositeObjective,separableSum,parameterShift,WithLp.toLp_fst,
      WithLp.toLp_snd,indicatorVA_apply_mem hx,h,zero_add,EReal.top_add_coe] at ha
    exact EReal.coe_ne_top a ha.symm
  exact ⟨hx,⟨_,(EReal.coe_toReal htop (hpθ.2 _).ne').symm⟩⟩

/-- Joint limiting subgradients, before selecting the zero decision component. -/
theorem subdifferential_perturbedCompositeObjective {X : Set E} {k : E → ℝ} {F : E → P}
    {θ : P → EReal} {x : E} {u : P} {c : ℝ}
    (hX : IsClosed X) (hk : ContDiff ℝ 1 k) (hF : ContDiff ℝ 1 F)
    (hθ : LowerSemicontinuous θ) (hx : x ∈ X) (hc : θ (F x+u) = c) :
    subdifferential (perturbedCompositeObjective X k F θ) (WithLp.toLp 2 (x,u)) =
      {v | v.snd ∈ subdifferential θ (F x+u) ∧
        v.fst-gradient k x-(fderiv ℝ F x).adjoint v.snd ∈ normalCone X x} := by
  let g := separableSum (indicatorVA X) θ
  have hg : g (parameterShift F (WithLp.toLp 2 (x,u))) = c := by
    simp [g,separableSum,parameterShift,indicatorVA_apply_mem hx,hc]
  have hFd := hasFDerivAt_parameterShift ((hF.differentiable one_ne_zero x).hasFDerivAt) u
  have hs := subdifferential_comp_eq_of_surjective (contDiff_parameterShift hF) hg
    (hFd.fderiv.symm ▸ parameterShiftDerivative_surjective (fderiv ℝ F x))
  rw [hFd.fderiv] at hs
  have ha := (subdifferentials_add_smooth (g := g ∘ parameterShift F) (x := WithLp.toLp 2 (x,u)) hg
    ((hk.comp (WithLp.fstL 2 ℝ E P).contDiff).contDiffAt)).2.1
  change subdifferential (perturbedCompositeObjective X k F θ) (WithLp.toLp 2 (x,u)) = _ at ha
  have hgrad : gradient (k ∘ (WithLp.fstL 2 ℝ E P)) (WithLp.toLp 2 (x,u)) =
      WithLp.toLp 2 (gradient k x,0) := gradient_comp_fst (hk.differentiable one_ne_zero x) u
  rw [ha,hs,hgrad]
  ext v
  constructor
  · rintro ⟨w,⟨q,hq,rfl⟩,rfl⟩
    have hp := (mem_subdifferential_separableSum_iff
      (lowerSemicontinuous_indicatorVA hX x) (hθ (F x+u))
      (indicatorVA_apply_mem hx) hc q).mp hq
    rw [subdifferential_indicatorVA] at hp
    simp only [mem_setOf_eq,parameterShiftDerivative_adjoint,WithLp.add_fst,WithLp.add_snd,
      WithLp.toLp_fst,WithLp.toLp_snd,add_zero]
    exact ⟨hp.2,by convert hp.1 using 1 <;> abel⟩
  · intro hv
    refine ⟨WithLp.toLp 2 (v.fst-gradient k x,v.snd),?_,?_⟩
    · refine ⟨WithLp.toLp 2 (v.fst-gradient k x-(fderiv ℝ F x).adjoint v.snd,v.snd),?_,?_⟩
      · apply (mem_subdifferential_separableSum_iff
          (lowerSemicontinuous_indicatorVA hX x) (hθ (F x+u))
          (indicatorVA_apply_mem hx) hc _).mpr
        simpa only [subdifferential_indicatorVA,WithLp.toLp_fst,WithLp.toLp_snd] using ⟨hv.2,hv.1⟩
      · simp only [parameterShiftDerivative_adjoint,WithLp.toLp_fst,WithLp.toLp_snd,sub_add_cancel]
    · apply WithLp.ofLp_injective
      exact Prod.ext (sub_add_cancel _ _) (add_zero _)

/-- The horizon inclusion needed for the multiplier qualification. -/
theorem horizonSubdifferential_perturbedCompositeObjective_subset
    {X : Set E} {k : E → ℝ} {F : E → P} {θ : P → EReal} {x : E} {u : P} {c : ℝ}
    (hX : IsClosed X) (hk : ContDiff ℝ 1 k) (hF : ContDiff ℝ 1 F)
    (hθ : LowerSemicontinuous θ) (hpθ : IsProper θ) (hx : x ∈ X) (hc : θ (F x+u) = c) :
    horizonSubdifferential (perturbedCompositeObjective X k F θ) (WithLp.toLp 2 (x,u)) ⊆
      {v | v.snd ∈ horizonSubdifferential θ (F x+u) ∧
        v.fst-(fderiv ℝ F x).adjoint v.snd ∈ normalCone X x} := by
  let g := separableSum (indicatorVA X) θ
  have hg : g (parameterShift F (WithLp.toLp 2 (x,u))) = c := by
    simp [g,separableSum,parameterShift,indicatorVA_apply_mem hx,hc]
  have hgl : LowerSemicontinuous g := lowerSemicontinuous_separableSum
    (lowerSemicontinuous_indicatorVA hX) hθ ((indicatorVA_isProper_iff X).mpr ⟨x,hx⟩) hpθ
  have hFd := hasFDerivAt_parameterShift ((hF.differentiable one_ne_zero x).hasFDerivAt) u
  have hs := horizonSubdifferential_comp_eq_of_surjective (contDiff_parameterShift hF) hgl hg
    (hFd.fderiv.symm ▸ parameterShiftDerivative_surjective (fderiv ℝ F x))
  rw [hFd.fderiv] at hs
  have ha := (subdifferentials_add_smooth (g := g ∘ parameterShift F) (x := WithLp.toLp 2 (x,u)) hg
    ((hk.comp (WithLp.fstL 2 ℝ E P).contDiff).contDiffAt)).2.2
  change horizonSubdifferential (perturbedCompositeObjective X k F θ) (WithLp.toLp 2 (x,u)) = _ at ha
  rw [ha,hs]
  rintro v ⟨q,hq,rfl⟩
  have hp := horizonSubdifferential_separableSum_subset
    (lowerSemicontinuous_indicatorVA hX x) (hθ (F x+u)) (indicatorVA_apply_mem hx) hc hq
  rw [horizonSubdifferential_indicatorVA] at hp
  simp only [mem_setOf_eq,parameterShiftDerivative_adjoint,WithLp.toLp_fst,WithLp.toLp_snd,add_sub_cancel_right]
  exact ⟨hp.2,hp.1⟩

end

end RW
