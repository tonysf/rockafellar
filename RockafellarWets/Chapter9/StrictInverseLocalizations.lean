/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strictly differentiable inverse localizations
-/

import RockafellarWets.Chapter9.SingleValuedLocalizations
import RockafellarWets.Chapter9.StrictDerivativeLinearity
import RockafellarWets.Chapter9.SmoothLipschitzModulus
import RockafellarWets.Chapter9.SemidifferentiabilityFromAubin
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Corollary 9.55**, the classical strict inverse theorem with its exact
Lipschitz modulus. The branch represents the entire inverse graph locally. -/
theorem HasStrictFDerivAt.exists_lipschitz_inverse_branch
    {f : E → F} {x : E} {A : E ≃L[ℝ] F} (hf : HasStrictFDerivAt f (A : E →L[ℝ] F) x) :
    ∃ (g : F → E) (r s : ℝ) (k : ℝ≥0), 0 < r ∧ 0 < s ∧ g (f x) = x ∧
      LipschitzOnWith k g (ball (f x) r) ∧
      (∀ y ∈ ball (f x) r, svInv (fun a ↦ {f a}) y ∩ ball x s = {g y}) ∧
      HasStrictFDerivAt g (A.symm : F →L[ℝ] E) (f x) ∧
      lipschitzModulus g (f x) = (‖(A.symm : F →L[ℝ] E)‖₊ : ℝ≥0∞) := by
  let g := hf.localInverse f A x
  have hg : HasStrictFDerivAt g (A.symm : F →L[ℝ] E) (f x) := hf.to_localInverse
  have hgx : g (f x) = x := hf.localInverse_apply_image
  have hmod := lipschitzModulus_eq_of_hasStrictFDerivAt hg
  have hstrict : StrictlyContinuousAt g (f x) := hmod.trans_lt ENNReal.coe_lt_top
  obtain ⟨k,U,hU,hLip⟩ := strictlyContinuousAt_iff.mp hstrict
  obtain ⟨s,hs,hsleft⟩ := Metric.mem_nhds_iff.mp hf.eventually_left_inverse
  have hgnear : ∀ᶠ y in 𝓝 (f x), g y ∈ ball x s := by
    simpa only [hgx] using hg.hasFDerivAt.continuousAt (ball_mem_nhds (g (f x)) hs)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hU (hf.eventually_right_inverse.and hgnear))
  refine ⟨g,r,s,k,hr,hs,hgx,hLip.mono (fun y hy ↦ (hrsub hy).1),?_,hg,hmod⟩
  intro y hy
  apply Subset.antisymm
  · intro a ha
    have hay : y = f a := ha.1
    have hleft : g (f a) = a := hsleft ha.2
    exact mem_singleton_iff.mpr (by rw [hay]; exact hleft.symm)
  · rintro a rfl
    exact ⟨mem_singleton_iff.mpr (hrsub hy).2.1.symm,(hrsub hy).2.2⟩

/-- The existential localization statement extracted from the explicit branch. -/
theorem HasStrictFDerivAt.hasLipschitzInverseLocalization [FiniteDimensional ℝ E]
    {f : E → F} {x : E} {A : E ≃L[ℝ] F} (hf : HasStrictFDerivAt f (A : E →L[ℝ] F) x) :
    HasLipschitzSingleValuedLocalization (svInv (fun a ↦ {f a})) (f x) x := by
  obtain ⟨g,r,s,k,hr,hs,hgx,hLip,hfiber,_,_⟩ := RW.HasStrictFDerivAt.exists_lipschitz_inverse_branch hf
  exact ⟨g,r,s,k,hr,hs,hgx,hLip,hfiber⟩

/-- For a square strictly differentiable mapping, nonsingularity of the
classical derivative is also necessary for a Lipschitz inverse localization. -/
theorem hasLipschitzInverseLocalization_iff_bijective_of_hasStrictFDerivAt
    [FiniteDimensional ℝ E] {f : E → E} {x : E} {A : E →L[ℝ] E}
    (hf : HasStrictFDerivAt f A x) :
    HasLipschitzSingleValuedLocalization (svInv (fun a ↦ {f a})) (f x) x ↔
      Function.Bijective A := by
  constructor
  · intro h
    have hmem : x ∈ svInv (fun a ↦ {f a}) (f x) := mem_singleton _
    have hz := (strictGraphicalDerivative_zero_iff_localGraphLipschitz hmem).mpr
      h.exists_localGraphLipschitzBound
    rw [strictGraphicalDerivative_svInv,strictGraphicalDerivative_singleton_of_hasStrictFDerivAt hf] at hz
    have hker (w : E) (hw : A w = 0) : w = 0 := by
      have hm : w ∈ svInv (fun v ↦ {A v}) 0 := mem_singleton_iff.mpr hw.symm
      exact mem_singleton_iff.mp (hz ▸ hm)
    have hinj : Function.Injective A := by
      intro a b hab
      exact sub_eq_zero.mp (hker (a-b) (by rw [map_sub,hab,sub_self]))
    exact ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩
  · intro hA
    let L := ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hA.1) (LinearMap.range_eq_top.mpr hA.2)
    have hfL : HasStrictFDerivAt f (L : E →L[ℝ] E) x := by
      simpa only [L,ContinuousLinearEquiv.coe_ofBijective] using hf
    exact RW.HasStrictFDerivAt.hasLipschitzInverseLocalization hfL

/-- Proto-differentiability passes to the inverse; an inverse Aubin estimate
upgrades this to the semiderivative with the inverse graphical derivative. -/
theorem HasAubinPropertyAt.hasMappingSemiderivative_inverse
    {S : E → Set F} {x : E} {u : F} (hu : u ∈ S x)
    (h : HasAubinPropertyAt (svInv S) u x) (hp : IsProtoDifferentiableAt S x u) :
    HasMappingSemiderivative (svInv S) u x (svInv (graphicalDerivative S x u)) := by
  rw [← graphicalDerivative_svInv]
  exact h.hasMappingSemiderivative ((isProtoDifferentiableAt_svInv_iff hu).mpr hp)

end RW
