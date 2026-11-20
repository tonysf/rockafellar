/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The attained convex composition bound
-/

import RockafellarWets.Chapter10.CompositionModulusMax
import RockafellarWets.Chapter2.Separation

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise ENNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- From a relative interior point one can move a little farther away from
any other point of the set while remaining in the set. -/
theorem exists_extrapolation_of_mem_intrinsicInterior {K : Set E} {a b : E}
    (ha : a ∈ intrinsicInterior ℝ K) (hb : b ∈ K) :
    ∃ t : ℝ, 0 < t ∧ a+t • (a-b) ∈ K := by
  obtain ⟨a',ha',rfl⟩ := mem_intrinsicInterior.mp ha
  have hbA : b ∈ affineSpan ℝ K := subset_affineSpan ℝ K hb
  let p : ℝ → affineSpan ℝ K := fun t ↦
    ⟨AffineMap.lineMap (a':E) b (-t),AffineMap.lineMap_mem (-t) a'.property hbA⟩
  have hp : Continuous p := by
    apply Continuous.subtype_mk
    exact continuous_const.lineMap continuous_const continuous_neg
  have hp0 : p 0 = a' := by ext; simp [p]
  have hlim : Tendsto p (𝓝[>] 0) (𝓝 a') := hp0 ▸ (hp.tendsto 0).mono_left nhdsWithin_le_nhds
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hpK⟩ := (ht.and (hlim.eventually (mem_interior_iff_mem_nhds.mp ha'))).exists
  refine ⟨t,ht,?_⟩
  change AffineMap.lineMap (a':E) b (-t) ∈ K at hpK
  have he : AffineMap.lineMap (a':E) b (-t) = (a':E)+t • ((a':E)-b) := by
    rw [AffineMap.lineMap_apply_module']
    module
  exact he ▸ hpK

/-- A supporting normal at an interior point of a chord supports at the
chord's endpoint too. -/
theorem normalCone_subset_of_extrapolation {C : Set E} (hc : Convex ℝ C) {a b : E}
    (ha : a ∈ C) (hb : b ∈ C) {t : ℝ} (ht : 0 < t) (he : a+t • (a-b) ∈ C) :
    normalCone C a ⊆ normalCone C b := by
  rw [normalCone_eq_of_convex hc ha,normalCone_eq_of_convex hc hb]
  intro v hv y hy
  have h₁ := hv b hb
  have h₂ := hv _ he
  rw [add_sub_cancel_left,real_inner_smul_right] at h₂
  have h₂' := nonpos_of_mul_nonpos_right h₂ ht
  have hz : ⟪v,b-a⟫_ℝ = 0 := by
    have hh : ⟪v,a-b⟫_ℝ = -⟪v,b-a⟫_ℝ := by rw [← inner_neg_right,neg_sub]
    rw [hh] at h₂'
    linarith
  have hh : ⟪v,y-b⟫_ℝ = ⟪v,y-a⟫_ℝ-⟪v,b-a⟫_ℝ := by
    rw [← inner_sub_right]
    congr 1
    abel
  rw [hh,hz,sub_zero]
  exact hv y hy

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {T : F → Set G} {x : E} {u : G}

theorem convex_svCompAux (hcS : SvGraphConvex S) (hcT : SvGraphConvex T) :
    Convex ℝ (svCompAux T S (x,u)) := by
  have hInv : SvGraphConvex (svInv T) := hcT.linear_preimage (LinearEquiv.prodComm ℝ G F).toLinearMap
  exact (hcS.svConvexValued x).inter (hInv.svConvexValued u)

/-- At a relative interior point of the intermediate fiber both coderivatives
are pointwise smallest among those on that fiber. -/
theorem coderivatives_subset_of_intermediate_intrinsicInterior
    (hcS : SvGraphConvex S) (hcT : SvGraphConvex T) {w v : F}
    (hw : w ∈ intrinsicInterior ℝ (svCompAux T S (x,u))) (hv : v ∈ svCompAux T S (x,u)) :
    (∀ z, coderivative S x w z ⊆ coderivative S x v z) ∧
      (∀ y, coderivative T w u y ⊆ coderivative T v u y) := by
  have hwK := intrinsicInterior_subset hw
  obtain ⟨t,ht,hstep⟩ := exists_extrapolation_of_mem_intrinsicInterior hw hv
  have hcS' : Convex ℝ (euclideanSvGraph S) :=
    hcS.linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearEquiv.toLinearMap
  have hcT' : Convex ℝ (euclideanSvGraph T) :=
    hcT.linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ F G).toLinearEquiv.toLinearMap
  have heS : WithLp.toLp 2 (x,w)+t • (WithLp.toLp 2 (x,w)-WithLp.toLp 2 (x,v)) =
      WithLp.toLp 2 (x,w+t • (w-v)) := by
    apply WithLp.ofLp_injective
    simp
  have heT : WithLp.toLp 2 (w,u)+t • (WithLp.toLp 2 (w,u)-WithLp.toLp 2 (v,u)) =
      WithLp.toLp 2 (w+t • (w-v),u) := by
    apply WithLp.ofLp_injective
    simp
  have hnS := normalCone_subset_of_extrapolation hcS'
    (a := WithLp.toLp 2 (x,w)) (b := WithLp.toLp 2 (x,v)) hwK.1 hv.1 ht
    (by rw [heS]; exact hstep.1)
  have hnT := normalCone_subset_of_extrapolation hcT'
    (a := WithLp.toLp 2 (w,u)) (b := WithLp.toLp 2 (v,u)) hwK.2 hv.2 ht
    (by rw [heT]; exact hstep.2)
  exact ⟨fun _ _ hv ↦ hnS hv,fun _ _ hv ↦ hnT hv⟩

/-- **Corollary 10.38**, attainment of the convex minimum product bound.
Every relative interior point of the nonempty intermediate fiber minimizes
both graphical moduli simultaneously. -/
theorem exists_min_composition_modulus (hS : SvOsc S) (hT : SvOsc T)
    (hcS : SvGraphConvex S) (hcT : SvGraphConvex T)
    (hu : u ∈ svComp T S x) (hb : SvLocallyBoundedAt (svCompAux T S) (x,u))
    (haS : ∀ w ∈ svCompAux T S (x,u), HasAubinPropertyAt S x w)
    (haT : ∀ w ∈ svCompAux T S (x,u), HasAubinPropertyAt T w u) :
    ∃ w ∈ svCompAux T S (x,u),
      IsMinOn (fun w ↦ graphicalLipschitzModulus S x w * graphicalLipschitzModulus T w u)
        (svCompAux T S (x,u)) w ∧
      graphicalLipschitzModulus (svComp T S) x u ≤
        graphicalLipschitzModulus S x w * graphicalLipschitzModulus T w u := by
  have hne : (svCompAux T S (x,u)).Nonempty := by
    obtain ⟨w,hw,hu⟩ := mem_svComp.mp hu
    exact ⟨w,hw,hu⟩
  obtain ⟨w,hw⟩ := nonempty_relInterior_of_convex (convex_svCompAux hcS hcT) hne
  have hwK := intrinsicInterior_subset hw
  refine ⟨w,hwK,?_,graphicalLipschitzModulus_svComp_le_of_convex hS hT hcS hcT hb hwK (haS w hwK) (haT w hwK)⟩
  intro v hv
  obtain ⟨hnS,hnT⟩ := coderivatives_subset_of_intermediate_intrinsicInterior hcS hcT hw hv
  have h₁ : graphicalLipschitzModulus S x w ≤ graphicalLipschitzModulus S x v := by
    rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative hwK.1 (haS w hwK).2.2.1,
      graphicalLipschitzModulus_eq_svOuterNorm_coderivative hv.1 (haS v hv).2.2.1]
    exact svOuterNorm_le_iff_ball.mpr (fun z hz a ha ↦ coe_nnnorm_le_svOuterNorm hz (hnS z ha))
  have h₂ : graphicalLipschitzModulus T w u ≤ graphicalLipschitzModulus T v u := by
    rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative (S := T) hwK.2 (haT w hwK).2.2.1,
      graphicalLipschitzModulus_eq_svOuterNorm_coderivative (S := T) hv.2 (haT v hv).2.2.1]
    exact svOuterNorm_le_iff_ball.mpr (fun y hy a ha ↦ coe_nnnorm_le_svOuterNorm hy (hnT y ha))
  exact mul_le_mul' h₁ h₂

end RW
