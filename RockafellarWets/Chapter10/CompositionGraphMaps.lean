/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graph lifts for composition of set-valued mappings
-/

import RockafellarWets.Chapter6.ImageSetCones
import RockafellarWets.Chapter6.ConstraintNormals
import RockafellarWets.Chapter6.ProductCones
import RockafellarWets.Chapter8.GraphicalDerivatives
import RockafellarWets.Chapter5.MappingOperations

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- The lifted composition graph, in coordinates `((x,u),w)`. -/
def compositionGraphLift (T : F → Set G) (S : E → Set F) :
    Set (WithLp 2 (WithLp 2 (E × G) × F)) :=
  {q | q.snd ∈ S q.fst.fst ∧ q.fst.snd ∈ T q.snd}

/-- Duplicate the intermediate coordinate, giving the two separate graphs. -/
def compositionGraphEmbedding : WithLp 2 (WithLp 2 (E × G) × F) →L[ℝ]
    WithLp 2 (WithLp 2 (E × F) × WithLp 2 (F × G)) :=
  let P := WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F
  let Q := WithLp.sndL 2 ℝ (WithLp 2 (E × G)) F
  let X := (WithLp.fstL 2 ℝ E G).comp P
  let U := (WithLp.sndL 2 ℝ E G).comp P
  let A := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp (X.prod Q)
  let B := (WithLp.prodContinuousLinearEquiv 2 ℝ F G).symm.toContinuousLinearMap.comp (Q.prod U)
  (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (E × F)) (WithLp 2 (F × G))).symm.toContinuousLinearMap.comp
    (A.prod B)

@[simp] theorem compositionGraphEmbedding_apply (q : WithLp 2 (WithLp 2 (E × G) × F)) :
    compositionGraphEmbedding q = WithLp.toLp 2
      (WithLp.toLp 2 (q.fst.fst,q.snd),WithLp.toLp 2 (q.snd,q.fst.snd)) := rfl

@[simp] theorem compositionGraphEmbedding_adjoint
    (p : WithLp 2 (WithLp 2 (E × F) × WithLp 2 (F × G))) :
    (compositionGraphEmbedding (E := E) (F := F) (G := G)).adjoint p =
      WithLp.toLp 2 (WithLp.toLp 2 (p.fst.fst,p.snd.snd),p.fst.snd+p.snd.fst) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left,compositionGraphEmbedding_apply]
  simp only [WithLp.prod_inner_apply,WithLp.toLp_fst,WithLp.toLp_snd,inner_add_left]
  change (⟪p.fst.fst,q.fst.fst⟫_ℝ + ⟪p.fst.snd,q.snd⟫_ℝ) +
    (⟪p.snd.fst,q.snd⟫_ℝ + ⟪p.snd.snd,q.fst.snd⟫_ℝ) =
    (⟪p.fst.fst,q.fst.fst⟫_ℝ + ⟪p.snd.snd,q.fst.snd⟫_ℝ) +
    (⟪p.fst.snd,q.snd⟫_ℝ + ⟪p.snd.fst,q.snd⟫_ℝ)
  ring

@[simp] theorem compositionGraphLift_preimage (T : F → Set G) (S : E → Set F) :
    compositionGraphLift T S = compositionGraphEmbedding ⁻¹'
      l2ProdSet (euclideanSvGraph S) (euclideanSvGraph T) := rfl

/-- Forgetting the intermediate value gives exactly the composition graph. -/
theorem euclideanSvGraph_svComp (T : F → Set G) (S : E → Set F) :
    euclideanSvGraph (svComp T S) =
      (WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F) '' compositionGraphLift T S := by
  ext p
  constructor
  · intro hp
    obtain ⟨w,hw,hu⟩ := mem_svComp.mp hp
    exact ⟨WithLp.toLp 2 (p,w),⟨hw,hu⟩,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    exact mem_svComp.mpr ⟨q.snd,hq.1,hq.2⟩

theorem isClosed_compositionGraphLift {T : F → Set G} {S : E → Set F}
    (hS : SvOsc S) (hT : SvOsc T) : IsClosed (compositionGraphLift T S) := by
  rw [compositionGraphLift_preimage]
  apply IsClosed.preimage compositionGraphEmbedding.continuous
  apply isClosed_l2ProdSet
  · exact (isClosed_svGraph_iff_svOsc.mpr hS).preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous
  · exact (isClosed_svGraph_iff_svOsc.mpr hT).preimage (WithLp.prodContinuousLinearEquiv 2 ℝ F G).continuous

/-- Local boundedness of the intermediate values is precisely the compactness
needed to lift nearby graph points. -/
theorem compositionGraphProjection_bounded_inverse {T : F → Set G} {S : E → Set F}
    {x : E} {u : G} (hb : SvLocallyBoundedAt (svCompAux T S) (x,u)) :
    ∃ U ∈ 𝓝 (WithLp.toLp 2 (x,u)), Bornology.IsBounded
      (compositionGraphLift T S ∩ (WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F) ⁻¹' U) := by
  obtain ⟨V,hV,hbV⟩ := hb
  let W := (WithLp.prodContinuousLinearEquiv 2 ℝ E G) ⁻¹' V ∩ closedBall (WithLp.toLp 2 (x,u)) 1
  have hW : W ∈ 𝓝 (WithLp.toLp 2 (x,u)) := inter_mem
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E G).continuous.continuousAt.preimage_mem_nhds hV)
    (closedBall_mem_nhds _ one_pos)
  refine ⟨W,hW,?_⟩
  have hbW : Bornology.IsBounded W := (isBounded_closedBall (x := WithLp.toLp 2 (x,u)) (r := 1)).subset inter_subset_right
  have hprod := (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (E × G)) F).symm.toContinuousLinearMap.lipschitz.isBounded_image
    (hbW.prod hbV)
  apply hprod.subset
  rintro q ⟨hq,hqW⟩
  refine ⟨(q.fst,q.snd),⟨hqW,?_⟩,rfl⟩
  exact mem_svImage.mpr ⟨WithLp.ofLp q.fst,hqW.1,hq⟩

/-- The local closed-graph conclusion of Theorem 10.37. -/
theorem isLocallyClosedAt_graph_svComp {T : F → Set G} {S : E → Set F}
    (hS : SvOsc S) (hT : SvOsc T) {x : E} {u : G}
    (hb : SvLocallyBoundedAt (svCompAux T S) (x,u)) :
    IsLocallyClosedAt (euclideanSvGraph (svComp T S)) (WithLp.toLp 2 (x,u)) := by
  rw [euclideanSvGraph_svComp]
  exact isLocallyClosedAt_image_of_bounded_inverse (isClosed_compositionGraphLift hS hT)
    (WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F).continuous (compositionGraphProjection_bounded_inverse hb)

end
end RW
