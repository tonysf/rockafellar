/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Derivative formulas for upper subsmooth marginal functions

The concluding assertions of 10.58 on the neighborhood where its local
representation is valid. The representation is kept separate from its
construction by compact localization of the minimizer mapping.
-/

import RockafellarWets.Chapter10.SubsmoothReachableGradients
import RockafellarWets.Chapter7.EpiDerivativeCounterexample

open Filter Set Topology MeasureTheory InnerProductSpace
open scoped InnerProductSpace Pointwise

namespace RW

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Negation carries every gradient, including the default value at points
of nondifferentiability, to its negative. -/
theorem gradient_fun_neg (p : E → ℝ) (x : E) :
    gradient (fun y ↦ -p y) x = -gradient p x := by
  simp only [gradient,fderiv_fun_neg,map_neg]

/-- Negation commutes with the reachable-gradient construction. -/
theorem reachableGradients_fun_neg (p : E → ℝ) (D : Set E) (x : E) :
    reachableGradients (fun y ↦ -p y) D x = -reachableGradients p D x := by
  ext v
  rw [Set.mem_neg]
  change v ∈ clusterValuesWithin (gradient (fun y ↦ -p y)) D x ↔
    -v ∈ clusterValuesWithin (gradient p) D x
  rw [mem_clusterValuesWithin_iff,mem_clusterValuesWithin_iff]
  constructor
  · rintro ⟨xs,hD,hx,hv⟩
    refine ⟨xs,hD,hx,?_⟩
    simpa only [gradient_fun_neg,neg_neg] using hv.neg
  · rintro ⟨xs,hD,hx,hv⟩
    refine ⟨xs,hD,hx,?_⟩
    simpa only [gradient_fun_neg,neg_neg] using hv.neg

namespace LowerRepresentation

variable {p : E → ℝ} {O : Set E} (R : LowerRepresentation 1 (fun y ↦ -p y) O)
  (hO : IsOpen O)

include R hO

omit [FiniteDimensional ℝ E] in
/-- The upper-`C¹` property encoded by a representation of `-p`. -/
theorem isUpperCOn : IsUpperCOn 1 p O :=
  fun _ hx ↦ ⟨O,hO,hx,Subset.rfl,⟨R⟩⟩

/-- The joint directional limit of the upper subsmooth function. -/
theorem upper_hasSemiderivative {x : E} (hx : x ∈ O) (w : E) :
    HasSemiderivative (fun y ↦ (p y:EReal)) x w (-(R.dirMax x w):EReal) := by
  have h := hasSemiderivative_of_strictlyContinuous_regular
    (R.strictlyContinuous_regular le_rfl hO x hx).1
    (R.strictlyContinuous_regular le_rfl hO x hx).2 w
  rw [R.subderivative_eq le_rfl hO hx w] at h
  simpa only [EReal.coe_neg,neg_neg] using h.neg

omit hO in
/-- The active partial gradients form a nonempty compact set. -/
theorem upper_active_nonempty_compact {x : E} (hx : x ∈ O) {Y : Set E}
    (hY : R.gradSet x = -Y) : Y.Nonempty ∧ IsCompact Y := by
  have hne : (R.gradSet x).Nonempty := (R.active_nonempty hx).image _
  have hc := R.isCompact_gradSet le_rfl hx
  rw [hY] at hne hc
  exact ⟨by simpa using hne.neg,by simpa using hc.neg⟩

/-- **10.58**, the minimum formula over all minimizing partial gradients. -/
theorem upper_subderivative_min_active {x : E} (hx : x ∈ O) {Y : Set E}
    (hY : R.gradSet x = -Y) (w : E) :
    ∃ y ∈ Y, subderivative (fun z ↦ (p z:EReal)) x w = (⟪y,w⟫_ℝ:EReal) ∧
      ∀ z ∈ Y, ⟪y,w⟫_ℝ ≤ ⟪z,w⟫_ℝ := by
  obtain ⟨⟨t,ht,he⟩,hmax⟩ := R.isGreatest_dirMax le_rfl hx w
  change fderiv ℝ (R.F t) x w = R.dirMax x w at he
  have hmem : gradient (R.F t) x ∈ -Y := hY ▸ ⟨t,ht,rfl⟩
  refine ⟨-gradient (R.F t) x,hmem,?_,?_⟩
  · rw [(R.upper_hasSemiderivative hO hx w).subderivative_eq,inner_neg_left]
    simp only [gradient,toDual_symm_apply,he,EReal.coe_neg]
  · intro z hz
    have hz' : -z ∈ R.gradSet x := hY ▸ (show -z ∈ -Y by simpa)
    obtain ⟨s,hs,hse⟩ := hz'
    have hh : fderiv ℝ (R.F s) x w ≤ R.dirMax x w := hmax ⟨s,hs,rfl⟩
    have htinner : ⟪gradient (R.F t) x,w⟫_ℝ=R.dirMax x w := by
      rw [gradient,toDual_symm_apply,he]
    change gradient (R.F s) x = -z at hse
    have hsinner : fderiv ℝ (R.F s) x w = -⟪z,w⟫_ℝ := by
      have hh : ⟪gradient (R.F s) x,w⟫_ℝ = fderiv ℝ (R.F s) x w := by
        rw [gradient,toDual_symm_apply]
      rw [← hh,hse,inner_neg_left]
    rw [hsinner] at hh
    rw [inner_neg_left,htinner]
    linarith

/-- **10.58**, every limiting subgradient is an active minimizing partial gradient. -/
theorem upper_subdifferential_subset {x : E} (hx : x ∈ O) {Y : Set E}
    (hY : R.gradSet x = -Y) : subdifferential (fun y ↦ (p y:EReal)) x ⊆ Y := by
  have h := R.neg_subdifferential_neg_subset le_rfl hO hx
  simp only [EReal.coe_neg,neg_neg] at h
  rw [hY] at h
  intro v hv
  have hh := h (show -v ∈ -subdifferential (fun y ↦ (p y:EReal)) x by simpa)
  simpa using hh

/-- **10.58**, the limiting subgradients are exactly the reachable gradients. -/
theorem upper_subdifferential_eq_reachable {x : E} (hx : x ∈ O) :
    subdifferential (fun y ↦ (p y:EReal)) x =
      reachableGradients p {y | y ∈ O ∧ DifferentiableAt ℝ p y} x := by
  have h := (R.isUpperCOn hO).neg_subdifferential_neg_eq_reachable le_rfl hO hx
  simp only [EReal.coe_neg,neg_neg,differentiableAt_fun_neg_iff,reachableGradients_fun_neg] at h
  exact neg_injective h

/-- Differentiability is equivalent to a unique active minimizing gradient. -/
theorem upper_differentiable_iff_singleton {x : E} (hx : x ∈ O) {Y : Set E}
    (hY : R.gradSet x = -Y) : DifferentiableAt ℝ p x ↔ ∃ v, Y={v} := by
  constructor
  · intro hd
    have hsingle : ∀ v ∈ Y, v=gradient p x := by
      intro v hv
      have hmem : -v ∈ R.gradSet x := hY ▸ (show -v ∈ -Y by simpa)
      obtain ⟨t,ht,he⟩ := hmem
      have hh := R.gradient_eq_of_differentiableAt le_rfl hO hx hd.neg ht
      change gradient (R.F t) x = -v at he
      rw [he,gradient_fun_neg] at hh
      exact (neg_injective hh).symm
    obtain ⟨v,hv⟩ := (R.upper_active_nonempty_compact hx hY).1
    refine ⟨gradient p x,Subset.antisymm (fun z hz ↦ hsingle z hz) ?_⟩
    simpa only [singleton_subset_iff,← hsingle v hv] using hv
  · rintro ⟨v,hv⟩
    have hs : subdifferential (fun y ↦ ((-p y:ℝ):EReal)) x = {-v} := by
      rw [R.subdifferential_eq_convexHull le_rfl hO hx,hY,hv,neg_singleton,convexHull_singleton]
    have hz := hasStrictGradientAt_of_subdifferential_eq
      (R.strictlyContinuous_regular le_rfl hO x hx).1 hs
    have hd : DifferentiableAt ℝ (fun y ↦ -p y) x := by
      simpa only [EReal.toReal_coe] using hz.2.hasFDerivAt.differentiableAt
    exact differentiableAt_fun_neg_iff.mp hd

/-- Upper subsmooth functions are strictly differentiable at every point
where they are differentiable. -/
theorem upper_hasStrictFDerivAt {x : E} (hx : x ∈ O) (hd : DifferentiableAt ℝ p x) :
    HasStrictFDerivAt p (fderiv ℝ p x) x := by
  have hh := (R.strictlyContinuous_regular le_rfl hO x hx).2.hasStrictGradientAt_of_differentiableAt
    (Eventually.of_forall fun y ↦ by simp)
    (show DifferentiableAt ℝ (fun y ↦ (((-p y:ℝ):EReal)).toReal) x by simpa using hd.neg)
  have hr : HasStrictFDerivAt (fun y ↦ -p y) (fderiv ℝ (fun y ↦ -p y) x) x := by
    have he : innerSL ℝ (gradient (fun y ↦ -p y) x) = fderiv ℝ (fun y ↦ -p y) x := by
      ext w
      simp only [innerSL_apply_apply,gradient,toDual_symm_apply]
    simpa only [EReal.toReal_coe,he] using hh.2
  have hn : -(fun y ↦ -p y) = p := by funext y; exact neg_neg (p y)
  simpa only [hn,fderiv_fun_neg,neg_neg] using hr.neg

/-- **10.58**, strict differentiability holds exactly when `Y` is a singleton. -/
theorem upper_strictDifferentiable_iff_singleton {x : E} (hx : x ∈ O) {Y : Set E}
    (hY : R.gradSet x = -Y) :
    HasStrictFDerivAt p (fderiv ℝ p x) x ↔ ∃ v, Y={v} :=
  ⟨fun h ↦ (R.upper_differentiable_iff_singleton hO hx hY).mp h.hasFDerivAt.differentiableAt,
    fun h ↦ R.upper_hasStrictFDerivAt hO hx ((R.upper_differentiable_iff_singleton hO hx hY).mpr h)⟩

/-- At a point of differentiability, the limiting subdifferential equals `Y`. -/
theorem upper_subdifferential_eq_active_of_differentiable {x : E} (hx : x ∈ O) {Y : Set E}
    (hY : R.gradSet x = -Y) (hd : DifferentiableAt ℝ p x) :
    subdifferential (fun y ↦ (p y:EReal)) x = Y := by
  obtain ⟨v,hv⟩ := (R.upper_differentiable_iff_singleton hO hx hY).mp hd
  have hgrad : gradient p x ∈ subdifferential (fun y ↦ (p y:EReal)) x :=
    regularSubdifferential_subset_subdifferential _ _
      (by rw [(regularSubdifferential_of_hasGradientAt hd.hasGradientAt).1]; rfl)
  have hgv := R.upper_subdifferential_subset hO hx hY hgrad
  rw [hv] at hgv ⊢
  exact Subset.antisymm (by rw [← hv]; exact R.upper_subdifferential_subset hO hx hY)
    (singleton_subset_iff.mpr (hgv ▸ hgrad))

section Measure
variable [MeasurableSpace E] [BorelSpace E]

/-- **10.58**, the minimum is also attained over the reachable gradients. -/
theorem upper_subderivative_min_reachable {x : E} (hx : x ∈ O) (w : E) :
    ∃ y ∈ reachableGradients p {z | z ∈ O ∧ DifferentiableAt ℝ p z} x,
      subderivative (fun z ↦ (p z:EReal)) x w = (⟪y,w⟫_ℝ:EReal) ∧
      ∀ z ∈ reachableGradients p {z | z ∈ O ∧ DifferentiableAt ℝ p z} x,
        ⟪y,w⟫_ℝ ≤ ⟪z,w⟫_ℝ := by
  obtain ⟨v,hv,hval,hmax⟩ := (R.isUpperCOn hO).subderivative_eq_reachable le_rfl hO hx w
  simp only [differentiableAt_fun_neg_iff,reachableGradients_fun_neg] at hv hmax
  refine ⟨-v,hv,?_,?_⟩
  · rw [R.subderivative_eq le_rfl hO hx w] at hval
    rw [(R.upper_hasSemiderivative hO hx w).subderivative_eq,inner_neg_left]
    exact congrArg Neg.neg hval
  · intro z hz
    have hh := hmax (-z) (by simpa)
    simpa only [inner_neg_left,neg_neg] using neg_le_neg hh

/-- **10.58**, the two compact gradient sets have the same convex hull. -/
theorem upper_convexHull_reachable {x : E} (hx : x ∈ O) {Y : Set E}
    (hY : R.gradSet x = -Y) :
    convexHull ℝ (reachableGradients p {y | y ∈ O ∧ DifferentiableAt ℝ p y} x) =
      convexHull ℝ Y := by
  have h := (R.isUpperCOn hO).convexHull_reachableGradients_eq_subdifferential le_rfl hO hx
  rw [R.subdifferential_eq_convexHull le_rfl hO hx,hY] at h
  simp only [differentiableAt_fun_neg_iff,reachableGradients_fun_neg,convexHull_neg] at h
  exact neg_injective h

/-- The reachable-gradient set is nonempty and compact at every point. -/
theorem upper_reachable_nonempty_compact {x : E} (hx : x ∈ O) :
    (reachableGradients p {y | y ∈ O ∧ DifferentiableAt ℝ p y} x).Nonempty ∧
      IsCompact (reachableGradients p {y | y ∈ O ∧ DifferentiableAt ℝ p y} x) := by
  have hsc : ∀ y ∈ O, StrictlyContinuousAt p y := by
    intro y hy
    obtain ⟨L,V,hV,hL⟩ := strictlyContinuousAt_iff.mp (R.strictlyContinuousAt le_rfl hO hy)
    have hn : -(fun z ↦ -p z) = p := by funext z; exact neg_neg (p z)
    exact strictlyContinuousAt_iff.mpr ⟨L,V,hV,by simpa only [hn] using hL.neg⟩
  exact reachableGradients_nonempty_compact (hsc x hx)
    (subset_closure_differentiableAt_of_strictlyContinuousOn volume hO hsc hx)

/-- **10.58**, the exceptional set is negligible, and the gradient is
continuous relative to the differentiability set. -/
theorem upper_differentiability (μ : Measure E) [μ.IsAddHaarMeasure] :
    (∀ x ∈ O, DifferentiableAt ℝ p x → HasStrictFDerivAt p (fderiv ℝ p x) x) ∧
      ContinuousOn (gradient p) {x | x ∈ O ∧ DifferentiableAt ℝ p x} ∧
      μ (O \ {x | DifferentiableAt ℝ p x}) = 0 := by
  have hh := (R.isUpperCOn hO).differentiability le_rfl μ
  simp only [differentiableAt_fun_neg_iff] at hh
  refine ⟨fun _ hx hd ↦ R.upper_hasStrictFDerivAt hO hx hd,?_,hh.2.2⟩
  simpa only [gradient_fun_neg,neg_neg] using hh.2.1.neg

/-- The set characterized directly by singleton minimizing gradients has
negligible complement. -/
theorem upper_singleton_complement_null {Y : E → Set E}
    (hY : ∀ x ∈ O, R.gradSet x = -Y x) (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (O \ {x | ∃ v, Y x={v}}) = 0 := by
  have he : O \ {x | ∃ v, Y x={v}} = O \ {x | DifferentiableAt ℝ p x} := by
    ext x
    constructor
    · rintro ⟨hx,hn⟩
      exact ⟨hx,fun hd ↦ hn ((R.upper_differentiable_iff_singleton hO hx (hY x hx)).mp hd)⟩
    · rintro ⟨hx,hn⟩
      exact ⟨hx,fun hs ↦ hn ((R.upper_differentiable_iff_singleton hO hx (hY x hx)).mpr hs)⟩
  rw [he]
  exact (R.upper_differentiability hO μ).2.2

end Measure
end LowerRepresentation
end RW
