/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graph representations for finite sums of mappings
-/

import RockafellarWets.Chapter10.CompositionGraphMaps
import RockafellarWets.Chapter6.SetAdditionCones

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def svFiniteSum (S : ι → E → Set F) : E → Set F := fun x ↦ finiteSetSum (fun i ↦ S i x)

def finiteSumGraphLift (S : ι → E → Set F) : Set (WithLp 2 (E × PiLp 2 (fun _ : ι ↦ F))) :=
  {q | ∀ i, q.snd i ∈ S i q.fst}

def finiteSumGraphEmbedding : WithLp 2 (E × PiLp 2 (fun _ : ι ↦ F)) →L[ℝ]
    PiLp 2 (fun _ : ι ↦ WithLp 2 (E × F)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q ↦ WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (q.fst,q.snd i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem finiteSumGraphEmbedding_apply (q : WithLp 2 (E × PiLp 2 (fun _ : ι ↦ F))) :
    finiteSumGraphEmbedding q = WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (q.fst,q.snd i)) := rfl

theorem finiteSumGraphEmbedding_adjoint (p : PiLp 2 (fun _ : ι ↦ WithLp 2 (E × F))) :
    (finiteSumGraphEmbedding (ι := ι) (E := E) (F := F)).adjoint p =
      WithLp.toLp 2 (∑ i, (p i).fst,WithLp.toLp 2 (fun i ↦ (p i).snd)) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left,finiteSumGraphEmbedding_apply]
  simp only [l2Pi_inner_apply,WithLp.prod_inner_apply,WithLp.ofLp_toLp]
  change (∑ i, (⟪(p i).fst,q.fst⟫_ℝ+⟪(p i).snd,q.snd i⟫_ℝ)) =
    ⟪∑ i, (p i).fst,q.fst⟫_ℝ+∑ i, ⟪(p i).snd,q.snd i⟫_ℝ
  rw [sum_inner,Finset.sum_add_distrib]

def finiteSumGraphProjection : WithLp 2 (E × PiLp 2 (fun _ : ι ↦ F)) →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    ((WithLp.fstL 2 ℝ E (PiLp 2 (fun _ : ι ↦ F))).prod
      (l2PiSum.comp (WithLp.sndL 2 ℝ E (PiLp 2 (fun _ : ι ↦ F)))))

@[simp] theorem finiteSumGraphProjection_apply (q : WithLp 2 (E × PiLp 2 (fun _ : ι ↦ F))) :
    finiteSumGraphProjection q = WithLp.toLp 2 (q.fst,∑ i, q.snd i) := by
  change WithLp.toLp 2 (q.fst,l2PiSum q.snd) = _
  rw [l2PiSum_apply]

theorem finiteSumGraphProjection_adjoint (p : WithLp 2 (E × F)) :
    (finiteSumGraphProjection (ι := ι)).adjoint p =
      WithLp.toLp 2 (p.fst,WithLp.toLp 2 (fun _ : ι ↦ p.snd)) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left,finiteSumGraphProjection_apply]
  simp only [WithLp.prod_inner_apply,WithLp.ofLp_toLp,l2Pi_inner_apply]
  change ⟪p.fst,q.fst⟫_ℝ+⟪p.snd,∑ i, q.snd i⟫_ℝ =
    ⟪p.fst,q.fst⟫_ℝ+∑ i, ⟪p.snd,q.snd i⟫_ℝ
  rw [inner_sum]

theorem finiteSumGraphLift_preimage (S : ι → E → Set F) :
    finiteSumGraphLift S = finiteSumGraphEmbedding ⁻¹' l2PiSet (fun i ↦ euclideanSvGraph (S i)) := rfl

theorem euclideanSvGraph_svFiniteSum (S : ι → E → Set F) :
    euclideanSvGraph (svFiniteSum S) = finiteSumGraphProjection '' finiteSumGraphLift S := by
  ext p
  constructor
  · rintro ⟨u,hu,he⟩
    refine ⟨WithLp.toLp 2 (p.fst,WithLp.toLp 2 u),hu,?_⟩
    rw [finiteSumGraphProjection_apply]
    change WithLp.toLp 2 (p.fst,∑ i, u i) = p
    rw [he]
    rfl
  · rintro ⟨q,hq,rfl⟩
    change ∃ u : ι → F, (∀ i, u i ∈ S i (finiteSumGraphProjection q).fst) ∧
      ∑ i, u i = (finiteSumGraphProjection q).snd
    rw [finiteSumGraphProjection_apply]
    exact ⟨fun i ↦ q.snd i,hq,rfl⟩

theorem isClosed_finiteSumGraphLift {S : ι → E → Set F} (hS : ∀ i, SvOsc (S i)) :
    IsClosed (finiteSumGraphLift S) := by
  rw [finiteSumGraphLift_preimage]
  apply IsClosed.preimage finiteSumGraphEmbedding.continuous
  exact isClosed_l2PiSet fun i ↦ (isClosed_svGraph_iff_svOsc.mpr (hS i)).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous

/-- The intermediate decompositions of a finite mapping sum. -/
def finiteSumMappingAux (S : ι → E → Set F) : E × F → Set (PiLp 2 (fun _ : ι ↦ F)) :=
  fun p ↦ {q | (∀ i, q i ∈ S i p.1) ∧ ∑ i, q i = p.2}

theorem finiteSumGraphProjection_bounded_inverse {S : ι → E → Set F} {x : E} {u : F}
    (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,u)) :
    ∃ U ∈ 𝓝 (WithLp.toLp 2 (x,u)), IsBounded
      (finiteSumGraphLift S ∩ finiteSumGraphProjection ⁻¹' U) := by
  obtain ⟨V,hV,hbV⟩ := hb
  let W := (WithLp.prodContinuousLinearEquiv 2 ℝ E F) ⁻¹' V ∩ closedBall (WithLp.toLp 2 (x,u)) 1
  have hW : W ∈ 𝓝 (WithLp.toLp 2 (x,u)) := inter_mem
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous.continuousAt.preimage_mem_nhds hV)
    (closedBall_mem_nhds _ one_pos)
  have hbW : IsBounded W := isBounded_closedBall.subset inter_subset_right
  have hbX := (WithLp.fstL 2 ℝ E F).lipschitz.isBounded_image hbW
  have hp := (WithLp.prodContinuousLinearEquiv 2 ℝ E (PiLp 2 (fun _ : ι ↦ F))).symm.toContinuousLinearMap.lipschitz.isBounded_image
    (hbX.prod hbV)
  refine ⟨W,hW,hp.subset ?_⟩
  rintro q ⟨hq,hqW⟩
  refine ⟨(q.fst,q.snd),⟨?_,?_⟩,rfl⟩
  · exact ⟨finiteSumGraphProjection q,hqW,by simp⟩
  · refine mem_svImage.mpr ⟨WithLp.ofLp (finiteSumGraphProjection q),hqW.1,?_⟩
    simp only [finiteSumMappingAux,finiteSumGraphProjection_apply,WithLp.ofLp_toLp,mem_setOf_eq]
    exact ⟨hq,trivial⟩

theorem isLocallyClosedAt_graph_svFiniteSum {S : ι → E → Set F} (hS : ∀ i, SvOsc (S i))
    {x : E} {u : F} (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,u)) :
    IsLocallyClosedAt (euclideanSvGraph (svFiniteSum S)) (WithLp.toLp 2 (x,u)) := by
  rw [euclideanSvGraph_svFiniteSum]
  exact isLocallyClosedAt_image_of_bounded_inverse (isClosed_finiteSumGraphLift hS)
    finiteSumGraphProjection.continuous (finiteSumGraphProjection_bounded_inverse hb)

end
end RW
