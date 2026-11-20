/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The coderivative chain rule
-/

import RockafellarWets.Chapter10.CompositionGraphMaps
import RockafellarWets.Chapter5.ConvexSemicontinuity

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {T : F → Set G} {x : E} {w : F} {u : G}

/-- The zero-multiplier qualification in Theorem 10.37(b). -/
def CompositionCoderivativeQualification (T : F → Set G) (S : E → Set F)
    (x : E) (w : F) (u : G) : Prop :=
  ∀ z ∈ coderivative T w u 0, (0:E) ∈ coderivative S x w z → z = 0

theorem compositionGraph_constraintQualification
    (hQ : CompositionCoderivativeQualification T S x w u) :
    NormalConstraintQualification univ
      (l2ProdSet (euclideanSvGraph S) (euclideanSvGraph T))
      compositionGraphEmbedding (WithLp.toLp 2 (WithLp.toLp 2 (x,u),w))
      (WithLp.toLp 2 (WithLp.toLp 2 (x,w),WithLp.toLp 2 (w,u))) := by
  intro p hp hzero
  rw [normalCone_univ,mem_singleton_iff,neg_eq_zero,compositionGraphEmbedding_adjoint] at hzero
  rw [normalCone_l2ProdSet] at hp
  have hfst : p.fst.fst = 0 := congrArg (fun q ↦ q.fst.fst) hzero
  have hsnd : p.snd.snd = 0 := congrArg (fun q ↦ q.fst.snd) hzero
  have hsum : p.fst.snd+p.snd.fst = 0 := congrArg WithLp.snd hzero
  have he : p.fst.snd = -p.snd.fst := eq_neg_of_add_eq_zero_left hsum
  have hT : p.snd.fst ∈ coderivative T w u 0 := by
    change WithLp.toLp 2 (p.snd.fst,-(0:G)) ∈ normalCone _ _
    rw [neg_zero,← hsnd]
    exact hp.2
  have hS : (0:E) ∈ coderivative S x w p.snd.fst := by
    change WithLp.toLp 2 ((0:E),-p.snd.fst) ∈ normalCone _ _
    simpa only [← hfst,← he] using hp.1
  have hz := hQ _ hT hS
  have hb : p.fst.snd = 0 := by simpa only [hz,neg_zero] using he
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply WithLp.ofLp_injective
    exact Prod.ext hfst hb
  · apply WithLp.ofLp_injective
    exact Prod.ext hz hsnd

/-- A normal with zero intermediate component decomposes into the two
coderivatives. -/
theorem exists_coderivative_composition_multiplier
    (hS : SvOsc S) (hT : SvOsc T)
    (hQ : CompositionCoderivativeQualification T S x w u) {v : E} {y : G}
    (hv : WithLp.toLp 2 (WithLp.toLp 2 (v,-y),(0:F)) ∈
      normalCone (compositionGraphLift T S) (WithLp.toLp 2 (WithLp.toLp 2 (x,u),w))) :
    ∃ z ∈ coderivative T w u y, v ∈ coderivative S x w z := by
  let L := compositionGraphEmbedding (E := E) (F := F) (G := G)
  let D := l2ProdSet (euclideanSvGraph S) (euclideanSvGraph T)
  have hD : IsClosed D := isClosed_l2ProdSet
    ((isClosed_svGraph_iff_svOsc.mpr hS).preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous)
    ((isClosed_svGraph_iff_svOsc.mpr hT).preimage (WithLp.prodContinuousLinearEquiv 2 ℝ F G).continuous)
  have hCQ : NormalConstraintQualification univ D
      (fderiv ℝ L (WithLp.toLp 2 (WithLp.toLp 2 (x,u),w)))
      (WithLp.toLp 2 (WithLp.toLp 2 (x,u),w)) (L (WithLp.toLp 2 (WithLp.toLp 2 (x,u),w))) := by
    rw [ContinuousLinearMap.fderiv]
    exact compositionGraph_constraintQualification hQ
  have he : univ ∩ L ⁻¹' D = compositionGraphLift T S := by
    rw [univ_inter]
    rfl
  obtain ⟨p,hp,b,hb,hvb⟩ := exists_normal_multipliers_of_mem_normalCone
    isClosed_univ hD L.contDiff hCQ (he.symm ▸ hv)
  rw [normalCone_univ,mem_singleton_iff] at hb
  rw [hb,add_zero,ContinuousLinearMap.fderiv] at hvb
  change WithLp.toLp 2 (WithLp.toLp 2 (v,-y),(0:F)) = compositionGraphEmbedding.adjoint p at hvb
  rw [compositionGraphEmbedding_adjoint] at hvb
  have he₁ : v = p.fst.fst := congrArg (fun q ↦ q.fst.fst) hvb
  have he₂ : -y = p.snd.snd := congrArg (fun q ↦ q.fst.snd) hvb
  have he₃ : (0:F) = p.fst.snd+p.snd.fst := congrArg WithLp.snd hvb
  have he₄ : p.fst.snd = -p.snd.fst := eq_neg_of_add_eq_zero_left he₃.symm
  change p ∈ normalCone (l2ProdSet (euclideanSvGraph S) (euclideanSvGraph T))
    (WithLp.toLp 2 (WithLp.toLp 2 (x,w),WithLp.toLp 2 (w,u))) at hp
  rw [normalCone_l2ProdSet] at hp
  refine ⟨p.snd.fst,?_,?_⟩
  · change WithLp.toLp 2 (p.snd.fst,-y) ∈ normalCone _ _
    simpa only [he₂] using hp.2
  · change WithLp.toLp 2 (v,-p.snd.fst) ∈ normalCone _ _
    simpa only [he₁,← he₄] using hp.1

theorem compositionGraphProjection_adjoint (p : WithLp 2 (E × G)) :
    (WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F).adjoint p = WithLp.toLp 2 (p,(0:F)) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [WithLp.prod_inner_apply,WithLp.ofLp_toLp,inner_zero_left,add_zero]
  rfl

/-- **Theorem 10.37**, the coderivative chain inclusion over all
intermediate values. -/
theorem coderivative_svComp_subset (hS : SvOsc S) (hT : SvOsc T)
    (hb : SvLocallyBoundedAt (svCompAux T S) (x,u))
    (hQ : ∀ w ∈ svCompAux T S (x,u), CompositionCoderivativeQualification T S x w u)
    (y : G) :
    coderivative (svComp T S) x u y ⊆
      ⋃ w ∈ svCompAux T S (x,u), svComp (coderivative S x w) (coderivative T w u) y := by
  intro v hv
  change WithLp.toLp 2 (v,-y) ∈ normalCone (euclideanSvGraph (svComp T S)) (WithLp.toLp 2 (x,u)) at hv
  rw [euclideanSvGraph_svComp] at hv
  have hn := normalCone_image_subset_iUnion (isClosed_compositionGraphLift hS hT)
    (WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F).contDiff (compositionGraphProjection_bounded_inverse hb) hv
  obtain ⟨q,hq,hv⟩ := mem_iUnion₂.mp hn
  have hqfst : q.fst = WithLp.toLp 2 (x,u) := hq.2
  have hqw : q.snd ∈ svCompAux T S (x,u) := by
    have := hq.1
    change q.snd ∈ S q.fst.fst ∧ q.fst.snd ∈ T q.snd at this
    simpa only [hqfst] using this
  have hqeq : q = WithLp.toLp 2 (WithLp.toLp 2 (x,u),q.snd) := by
    apply WithLp.ofLp_injective
    exact Prod.ext hqfst rfl
  rw [ContinuousLinearMap.fderiv,mem_preimage,compositionGraphProjection_adjoint,hqeq] at hv
  obtain ⟨z,hz,hvz⟩ := exists_coderivative_composition_multiplier hS hT (hQ q.snd hqw) hv
  exact mem_iUnion₂.mpr ⟨q.snd,hqw,mem_svComp.mpr ⟨z,hz,hvz⟩⟩

theorem convex_compositionGraphLift (hS : SvGraphConvex S) (hT : SvGraphConvex T) :
    Convex ℝ (compositionGraphLift T S) := by
  intro p hp q hq a b ha hb hab
  exact ⟨hS (x := (p.fst.fst,p.snd)) (y := (q.fst.fst,q.snd)) hp.1 hq.1 ha hb hab,
    hT (x := (p.snd,p.fst.snd)) (y := (q.snd,q.fst.snd)) hp.2 hq.2 ha hb hab⟩

/-- Composition preserves graph convexity. -/
theorem SvGraphConvex.svComp (hS : SvGraphConvex S) (hT : SvGraphConvex T) :
    SvGraphConvex (svComp T S) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨z,hz,hpz⟩ := mem_svComp.mp hp
  obtain ⟨v,hv,hqv⟩ := mem_svComp.mp hq
  exact mem_svComp.mpr ⟨a • z+b • v,
    hS (x := (p.1,z)) (y := (q.1,v)) hz hv ha hb hab,
    hT (x := (z,p.2)) (y := (v,q.2)) hpz hqv ha hb hab⟩

/-- **Theorem 10.37**, exact chain rule at each intermediate value for
graph-convex mappings. Local boundedness is unnecessary in this specialization. -/
theorem coderivative_svComp_eq_of_convex (hS : SvOsc S) (hT : SvOsc T)
    (hcS : SvGraphConvex S) (hcT : SvGraphConvex T)
    (hw : w ∈ svCompAux T S (x,u))
    (hQ : CompositionCoderivativeQualification T S x w u) (y : G) :
    coderivative (svComp T S) x u y = svComp (coderivative S x w) (coderivative T w u) y := by
  let P := WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F
  have hp : WithLp.toLp 2 (WithLp.toLp 2 (x,u),w) ∈ compositionGraphLift T S := hw
  have he := normalCone_linear_image_of_convex P (convex_compositionGraphLift hcS hcT) hp
  change normalCone (P '' compositionGraphLift T S) (WithLp.toLp 2 (x,u)) =
    P.adjoint ⁻¹' normalCone (compositionGraphLift T S) (WithLp.toLp 2 (WithLp.toLp 2 (x,u),w)) at he
  ext v
  constructor
  · intro hv
    change WithLp.toLp 2 (v,-y) ∈ normalCone (euclideanSvGraph (svComp T S)) _ at hv
    rw [euclideanSvGraph_svComp,he] at hv
    change P.adjoint (WithLp.toLp 2 (v,-y)) ∈ normalCone (compositionGraphLift T S)
      (WithLp.toLp 2 (WithLp.toLp 2 (x,u),w)) at hv
    rw [compositionGraphProjection_adjoint] at hv
    exact mem_svComp.mpr (exists_coderivative_composition_multiplier hS hT hQ hv)
  · intro hv
    obtain ⟨z,hz,hvz⟩ := mem_svComp.mp hv
    have hcS' : Convex ℝ (euclideanSvGraph S) :=
      hcS.linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearEquiv.toLinearMap
    have hcT' : Convex ℝ (euclideanSvGraph T) :=
      hcT.linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ F G).toLinearEquiv.toLinearMap
    have hc : Convex ℝ (euclideanSvGraph (svComp T S)) :=
      (hcS.svComp hcT).linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E G).toLinearEquiv.toLinearMap
    change WithLp.toLp 2 (v,-z) ∈ normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,w)) at hvz
    change WithLp.toLp 2 (z,-y) ∈ normalCone (euclideanSvGraph T) (WithLp.toLp 2 (w,u)) at hz
    rw [normalCone_eq_of_convex hcS' hw.1] at hvz
    rw [normalCone_eq_of_convex hcT' hw.2] at hz
    change WithLp.toLp 2 (v,-y) ∈ normalCone (euclideanSvGraph (svComp T S)) _
    rw [normalCone_eq_of_convex hc (mem_svComp.mpr ⟨w,hw.1,hw.2⟩)]
    intro p hp'
    obtain ⟨r,hr,hpr⟩ := mem_svComp.mp hp'
    have h₁ := hvz (WithLp.toLp 2 (p.fst,r)) hr
    have h₂ := hz (WithLp.toLp 2 (r,p.snd)) hpr
    simp only [WithLp.prod_inner_apply,WithLp.ofLp_sub,WithLp.ofLp_toLp,Prod.fst_sub,Prod.snd_sub,
      inner_neg_left] at h₁ h₂ ⊢
    change ⟪v,p.fst-x⟫_ℝ + -⟪y,p.snd-u⟫_ℝ ≤ 0
    linarith

end RW
