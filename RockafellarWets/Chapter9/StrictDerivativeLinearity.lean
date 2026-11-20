/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict differentiability and linear strict derivatives
-/

import RockafellarWets.Chapter9.StrictDerivativeModulus
import RockafellarWets.Chapter9.SmoothLipschitzModulus
import RockafellarWets.Chapter9.SingleValuedGraphicalDerivatives

open Asymptotics Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A zero strict derivative is exactly a zero local Lipschitz modulus. -/
theorem hasStrictFDerivAt_zero_iff_lipschitzModulus_eq_zero {f : E → F} {x : E} :
    HasStrictFDerivAt f (0 : E →L[ℝ] F) x ↔ lipschitzModulus f x = 0 := by
  constructor
  · intro h
    simpa using lipschitzModulus_eq_of_hasStrictFDerivAt h
  · intro h
    apply HasStrictFDerivAt.of_isLittleO
    apply IsLittleO.of_bound
    intro ε hε
    obtain ⟨U,hU,hL⟩ := exists_lipschitzOnWith_of_modulus_lt (f := f) (x := x)
      (k := ⟨ε,hε.le⟩) (by rw [h]; exact ENNReal.coe_pos.mpr (by exact hε))
    filter_upwards [prod_mem_nhds hU hU] with p hp
    simpa only [ContinuousLinearMap.zero_apply,sub_zero,dist_eq_norm] using
      hL.dist_le_mul p.1 hp.1 p.2 hp.2

private def graphShear (L : E →L[ℝ] F) : (E × F) ≃L[ℝ] (E × F) where
  toFun p := (p.1,p.2 + L p.1)
  invFun p := (p.1,p.2 - L p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp [map_add] <;> abel
  map_smul' c p := by ext <;> simp [map_smul,smul_add]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (L.continuous.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (L.continuous.comp continuous_fst))

/-- Subtracting a linear map translates each strict derivative fiber by its
value on the input direction. -/
theorem mem_strictGraphicalDerivative_sub_linear_iff (L : E →L[ℝ] F) (f : E → F) (x w : E) (z : F) :
    z ∈ strictGraphicalDerivative (fun a ↦ {f a-L a}) x (f x-L x) w ↔
      z + L w ∈ strictGraphicalDerivative (fun a ↦ {f a}) x (f x) w := by
  have hgraph : svGraph (fun a ↦ {f a-L a}) = (graphShear L) ⁻¹' svGraph (fun a ↦ {f a}) := by
    ext p
    change p.2 = f p.1-L p.1 ↔ p.2 + L p.1 = f p.1
    exact eq_sub_iff_add_eq
  change (w,z) ∈ strictTangentCone (svGraph (fun a ↦ {f a-L a})) (x,f x-L x) ↔ _
  rw [hgraph,strictTangentCone_preimage_continuousLinearEquiv]
  change (w,z + L w) ∈ strictTangentCone (svGraph (fun a ↦ {f a})) (x,f x-L x+L x) ↔ _
  rw [sub_add_cancel]
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Definition 9.53**, the strict derivative of a strictly differentiable
single-valued mapping is its linear derivative. -/
theorem strictGraphicalDerivative_singleton_of_hasStrictFDerivAt {f : E → F} {x : E} {L : E →L[ℝ] F}
    (hf : HasStrictFDerivAt f L x) :
    strictGraphicalDerivative (fun a ↦ {f a}) x (f x) = fun w ↦ {L w} := by
  let g := fun a ↦ f a-L a
  have hg : HasStrictFDerivAt g (0 : E →L[ℝ] F) x := by
    simpa only [sub_self] using hf.sub (L.hasStrictFDerivAt (x := x))
  have hnorm : svOuterNorm (strictGraphicalDerivative (fun a ↦ {g a}) x (g x)) = 0 := by
    rw [svOuterNorm_strictGraphicalDerivative_singleton hg.hasFDerivAt.continuousAt,
      hasStrictFDerivAt_zero_iff_lipschitzModulus_eq_zero.mp hg]
  have hhom := svPositivelyHomogeneous_strictGraphicalDerivative (S := fun a ↦ {g a}) (mem_singleton (g x))
  have hzero (w : E) (z : F) (hz : z ∈ strictGraphicalDerivative (fun a ↦ {g a}) x (g x) w) : z = 0 := by
    have h := (hhom.svOuterNorm_le_iff (κ := 0)).mp hnorm.le w z hz
    simpa only [NNReal.coe_zero,zero_mul,norm_le_zero_iff] using h
  have hupper (w : E) (z : F) (hz : z ∈ strictGraphicalDerivative (fun a ↦ {f a}) x (f x) w) : z = L w := by
    have hz' : z-L w ∈ strictGraphicalDerivative (fun a ↦ {g a}) x (g x) w := by
      apply (mem_strictGraphicalDerivative_sub_linear_iff L f x w _).mpr
      simpa only [sub_add_cancel] using hz
    exact sub_eq_zero.mp (hzero w _ hz')
  have hstrict : StrictlyContinuousAt f x :=
    (lipschitzModulus_eq_of_hasStrictFDerivAt hf).trans_lt ENNReal.coe_lt_top
  funext w
  apply Subset.antisymm
  · exact fun z hz ↦ mem_singleton_iff.mpr (hupper w z hz)
  · obtain ⟨z,hz⟩ := (hstrict.graphicalDerivative_lipschitz.1 w (mem_univ w)).1
    have hzs := graphicalDerivative_subset_strictGraphicalDerivative (S := fun a : E ↦ {f a})
      (x := x) (mem_singleton (f x)) w hz
    rw [hupper w z hzs] at hzs
    exact singleton_subset_iff.mpr hzs

/-- The converse for a continuous mapping, completing the linearity
characterization following Definition9.53. -/
theorem hasStrictFDerivAt_iff_strictGraphicalDerivative_linear {f : E → F} {x : E} {L : E →L[ℝ] F}
    (hc : ContinuousAt f x) : HasStrictFDerivAt f L x ↔
      strictGraphicalDerivative (fun a ↦ {f a}) x (f x) = fun w ↦ {L w} := by
  refine ⟨strictGraphicalDerivative_singleton_of_hasStrictFDerivAt,fun h ↦ ?_⟩
  let g := fun a ↦ f a-L a
  have hgc : ContinuousAt g x := hc.sub L.continuous.continuousAt
  have hhom := svPositivelyHomogeneous_strictGraphicalDerivative (S := fun a ↦ {g a}) (mem_singleton (g x))
  have hnorm : svOuterNorm (strictGraphicalDerivative (fun a ↦ {g a}) x (g x)) = 0 := by
    apply le_antisymm _ (zero_le _)
    apply (hhom.svOuterNorm_le_iff (κ := 0)).mpr
    intro w z hz
    have hz' := (mem_strictGraphicalDerivative_sub_linear_iff L f x w z).mp hz
    rw [h] at hz'
    have he : z = 0 := add_right_cancel (show z + L w = 0 + L w by simpa using mem_singleton_iff.mp hz')
    simp only [he,norm_zero,NNReal.coe_zero,zero_mul,le_refl]
  have hg : HasStrictFDerivAt g (0 : E →L[ℝ] F) x :=
    hasStrictFDerivAt_zero_iff_lipschitzModulus_eq_zero.mpr
      ((svOuterNorm_strictGraphicalDerivative_singleton hgc).symm.trans hnorm)
  convert hg.add (L.hasStrictFDerivAt (x := x)) using 1
  · funext y
    simp [g]
  · simp

end RW
