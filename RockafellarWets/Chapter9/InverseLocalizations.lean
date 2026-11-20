/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Single-valued local inverses in equal dimension
-/

import RockafellarWets.Chapter9.SingleValuedLocalizations
import RockafellarWets.Chapter7.EuclideanChangeOfVariables

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → E} {O : Set E} {x : E}

/-- An injective local inverse estimate and domain invariance imply inner
semicontinuity of the inverse at the selected preimage. -/
theorem mem_svInnerLimit_inverse_of_localGraphLipschitz (hO : IsOpen O) (hx : x ∈ O)
    (hf : ContinuousOn f O) {k : ℝ≥0}
    (hk : LocalGraphLipschitzBound (svGraph (svInv (fun a ↦ {f a}))) (f x,x) k) :
    x ∈ svInnerLimit (svInv (fun a ↦ {f a})) (f x) := by
  obtain ⟨δ,hδ,hbound⟩ := hk
  let U := (O ∩ f ⁻¹' ball (f x) δ) ∩ ball x δ
  have hU : IsOpen U := (hf.isOpen_inter_preimage hO isOpen_ball).inter isOpen_ball
  have hxU : x ∈ U := ⟨⟨hx,mem_ball_self hδ⟩,mem_ball_self hδ⟩
  have hUO : U ⊆ O := fun _ h ↦ h.1.1
  have hgraph {a : E} (ha : a ∈ U) :
      (f a,a) ∈ svGraph (svInv (fun a ↦ {f a})) ∩ ball (f x,x) δ := by
    refine ⟨mem_singleton _,?_⟩
    rw [← ball_prod_same]
    exact ⟨ha.1.2,ha.2⟩
  have hinj : InjOn f U := by
    intro a ha b hb hab
    have hd := hbound (f a,a) (hgraph ha) (f b,b) (hgraph hb)
    simpa only [hab,dist_self,mul_zero,dist_le_zero] using hd
  intro V hV
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  have hW : IsOpen (U ∩ ball x ε) := hU.inter isOpen_ball
  have hWcont : ContinuousOn f (U ∩ ball x ε) := hf.mono (inter_subset_left.trans hUO)
  have hWimg := isOpen_image_of_continuousOn_injective_euclidean f _ hW hWcont
    (hinj.mono inter_subset_left)
  have hximg : f x ∈ f '' (U ∩ ball x ε) := ⟨x,⟨hxU,mem_ball_self hε⟩,rfl⟩
  filter_upwards [hWimg.mem_nhds hximg] with y hy
  obtain ⟨a,ha,hfa⟩ := hy
  exact ⟨a,mem_singleton_iff.mpr hfa.symm,hεV ha.2⟩

/-- **Corollary 9.55**, the strict inverse-kernel criterion. Domain and
codomain are the same finite-dimensional Euclidean space. -/
theorem hasLipschitzInverseLocalization_iff_strictKernel_zero (hO : IsOpen O) (hx : x ∈ O)
    (hf : ContinuousOn f O) :
    HasLipschitzSingleValuedLocalization (svInv (fun a ↦ {f a})) (f x) x ↔
      svInv (strictGraphicalDerivative (fun a ↦ {f a}) x (f x)) 0 = {0} := by
  have hmem : x ∈ svInv (fun a ↦ {f a}) (f x) := mem_singleton _
  rw [← strictGraphicalDerivative_svInv]
  constructor
  · intro h
    exact (strictGraphicalDerivative_zero_iff_localGraphLipschitz hmem).mpr
      h.exists_localGraphLipschitzBound
  · intro h
    obtain ⟨k,hk⟩ := (strictGraphicalDerivative_zero_iff_localGraphLipschitz hmem).mp h
    exact hasLipschitzSingleValuedLocalization_of_localGraphLipschitz hmem
      (mem_svInnerLimit_inverse_of_localGraphLipschitz hO hx hf hk) hk

end RW
