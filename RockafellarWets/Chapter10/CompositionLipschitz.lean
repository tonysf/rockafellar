/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lipschitz properties under composition
-/

import RockafellarWets.Chapter10.CoderivativeComposition
import RockafellarWets.Chapter9.MordukhovichCriterion
import RockafellarWets.Chapter9.OuterNormRules
import RockafellarWets.Chapter9.AubinAbsoluteLocalization
import RockafellarWets.Chapter9.InverseCoderivatives

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise NNReal ENNReal

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {T : F → Set G} {x : E} {w : F} {u : G}

theorem compositionCoderivativeQualification_of_aubin_outer (h : HasAubinPropertyAt T w u) :
    CompositionCoderivativeQualification T S x w u := by
  intro z hz _
  rw [(hasAubinPropertyAt_iff_coderivative_zero h.2.1 h.2.2.1).mp h,mem_singleton_iff] at hz
  exact hz

theorem compositionCoderivativeQualification_of_aubin_inverse (h : HasAubinPropertyAt (svInv S) w x) :
    CompositionCoderivativeQualification T S x w u := by
  intro z _ hz
  have hh : -z ∈ coderivative (svInv S) w x 0 :=
    mem_coderivative_inverse_iff.mpr (by simpa using hz)
  rw [(hasAubinPropertyAt_iff_coderivative_zero h.2.1 h.2.2.1).mp h,mem_singleton_iff,neg_eq_zero] at hh
  exact hh

theorem svLocallyBoundedAt_svCompAux_left (h : SvLocallyBoundedAt S x) (u : G) :
    SvLocallyBoundedAt (svCompAux T S) (x,u) := by
  obtain ⟨V,hV,hb⟩ := h
  refine ⟨V ×ˢ univ,prod_mem_nhds hV univ_mem,hb.subset ?_⟩
  intro w hw
  obtain ⟨p,hp,hw⟩ := mem_svImage.mp hw
  exact mem_svImage.mpr ⟨p.1,hp.1,hw.1⟩

theorem svLocallyBoundedAt_svCompAux_right (h : SvLocallyBoundedAt (svInv T) u) (x : E) :
    SvLocallyBoundedAt (svCompAux T S) (x,u) := by
  obtain ⟨V,hV,hb⟩ := h
  refine ⟨univ ×ˢ V,prod_mem_nhds univ_mem hV,hb.subset ?_⟩
  intro w hw
  obtain ⟨p,hp,hw⟩ := mem_svImage.mp hw
  exact mem_svImage.mpr ⟨p.2,hp.2,hw.2⟩

theorem isLocallyClosedAt_svGraph_svComp (hS : SvOsc S) (hT : SvOsc T)
    (hb : SvLocallyBoundedAt (svCompAux T S) (x,u)) :
    IsLocallyClosedAt (svGraph (svComp T S)) (x,u) := by
  have hl := isLocallyClosedAt_graph_svComp hS hT hb
  exact hl.preimage_continuousLinearEquiv (WithLp.prodContinuousLinearEquiv 2 ℝ E G).symm

/-- **Corollary 10.38**, the Aubin property under composition. -/
theorem hasAubinPropertyAt_svComp (hS : SvOsc S) (hT : SvOsc T)
    (hu : u ∈ svComp T S x) (hb : SvLocallyBoundedAt (svCompAux T S) (x,u))
    (haS : ∀ w ∈ svCompAux T S (x,u), HasAubinPropertyAt S x w)
    (haT : ∀ w ∈ svCompAux T S (x,u), HasAubinPropertyAt T w u) :
    HasAubinPropertyAt (svComp T S) x u := by
  apply (hasAubinPropertyAt_iff_coderivative_zero hu (isLocallyClosedAt_svGraph_svComp hS hT hb)).mpr
  apply Subset.antisymm
  · intro v hv
    obtain ⟨w,hw,hv⟩ := mem_iUnion₂.mp (coderivative_svComp_subset hS hT hb
      (fun w hw ↦ compositionCoderivativeQualification_of_aubin_outer (haT w hw)) 0 hv)
    obtain ⟨z,hz,hvz⟩ := mem_svComp.mp hv
    have hz0 : z = 0 := by
      rw [(hasAubinPropertyAt_iff_coderivative_zero (S := T) hw.2 (haT w hw).2.2.1).mp (haT w hw),
        mem_singleton_iff] at hz
      exact hz
    rw [hz0,(hasAubinPropertyAt_iff_coderivative_zero hw.1 (haS w hw).2.2.1).mp (haS w hw)] at hvz
    exact hvz
  · exact singleton_subset_iff.mpr (graphicalDerivative_properties hu).2.2.1.2.1

/-- The full supremum version of the product modulus estimate in 10.38. -/
theorem graphicalLipschitzModulus_svComp_le_iSup (hS : SvOsc S) (hT : SvOsc T)
    (hu : u ∈ svComp T S x) (hb : SvLocallyBoundedAt (svCompAux T S) (x,u))
    (haS : ∀ w ∈ svCompAux T S (x,u), HasAubinPropertyAt S x w)
    (haT : ∀ w ∈ svCompAux T S (x,u), HasAubinPropertyAt T w u) :
    graphicalLipschitzModulus (svComp T S) x u ≤
      ⨆ w ∈ svCompAux T S (x,u), graphicalLipschitzModulus S x w * graphicalLipschitzModulus T w u := by
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative hu (isLocallyClosedAt_svGraph_svComp hS hT hb)]
  apply svOuterNorm_le_iff_ball.mpr
  intro y hy v hv
  obtain ⟨w,hw,hv⟩ := mem_iUnion₂.mp (coderivative_svComp_subset hS hT hb
    (fun w hw ↦ compositionCoderivativeQualification_of_aubin_outer (haT w hw)) y hv)
  have hsfin := (hasAubinPropertyAt_iff_svOuterNorm_coderivative_lt_top hw.1 (haS w hw).2.2.1).mp (haS w hw)
  have hbound := (coe_nnnorm_le_svOuterNorm hy hv).trans
    (svOuterNorm_svComp_le (graphicalDerivative_properties hw.1).2.2.1.2 (Or.inl hsfin.ne))
  rw [← graphicalLipschitzModulus_eq_svOuterNorm_coderivative hw.1 (haS w hw).2.2.1,
    ← graphicalLipschitzModulus_eq_svOuterNorm_coderivative (S := T) hw.2 (haT w hw).2.2.1] at hbound
  exact hbound.trans (le_iSup₂_of_le w hw le_rfl)

/-- **Corollary 10.38**, the sharper bound at every intermediate value in
the convex case. Taking the infimum gives the printed minimum bound. -/
theorem graphicalLipschitzModulus_svComp_le_of_convex (hS : SvOsc S) (hT : SvOsc T)
    (hcS : SvGraphConvex S) (hcT : SvGraphConvex T)
    (hb : SvLocallyBoundedAt (svCompAux T S) (x,u))
    (hw : w ∈ svCompAux T S (x,u))
    (haS : HasAubinPropertyAt S x w) (haT : HasAubinPropertyAt T w u) :
    graphicalLipschitzModulus (svComp T S) x u ≤
      graphicalLipschitzModulus S x w * graphicalLipschitzModulus T w u := by
  have hu := mem_svComp.mpr ⟨w,hw.1,hw.2⟩
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative hu (isLocallyClosedAt_svGraph_svComp hS hT hb),
    funext (coderivative_svComp_eq_of_convex hS hT hcS hcT hw (compositionCoderivativeQualification_of_aubin_outer haT)),
    graphicalLipschitzModulus_eq_svOuterNorm_coderivative hw.1 haS.2.2.1,
    graphicalLipschitzModulus_eq_svOuterNorm_coderivative (S := T) hw.2 haT.2.2.1]
  exact svOuterNorm_svComp_le (graphicalDerivative_properties hw.1).2.2.1.2
    (Or.inl ((hasAubinPropertyAt_iff_svOuterNorm_coderivative_lt_top hw.1 haS.2.2.1).mp haS).ne)

end RW
