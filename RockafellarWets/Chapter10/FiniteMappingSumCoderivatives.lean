/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coderivatives of finite sums of mappings
-/

import RockafellarWets.Chapter10.FiniteMappingSumGraphs

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : ι → E → Set F} {x : E} {u : PiLp 2 (fun _ : ι ↦ F)}

def FiniteSumCoderivativeQualification (S : ι → E → Set F) (x : E)
    (u : PiLp 2 (fun _ : ι ↦ F)) : Prop :=
  ∀ v : ι → E, (∀ i, v i ∈ coderivative (S i) x (u i) 0) →
    ∑ i, v i = 0 → ∀ i, v i = 0

theorem finiteSumGraph_constraintQualification (hQ : FiniteSumCoderivativeQualification S x u) :
    NormalConstraintQualification univ (l2PiSet (fun i ↦ euclideanSvGraph (S i)))
      finiteSumGraphEmbedding (WithLp.toLp 2 (x,u))
      (finiteSumGraphEmbedding (WithLp.toLp 2 (x,u))) := by
  intro p hp hz
  rw [normalCone_univ,mem_singleton_iff,neg_eq_zero,finiteSumGraphEmbedding_adjoint] at hz
  rw [normalCone_l2PiSet] at hp
  have hsum : ∑ i, (p i).fst = 0 := congrArg WithLp.fst hz
  have hsnd (i : ι) : (p i).snd = 0 := congrArg (fun q ↦ q.snd i) hz
  have hp' (i : ι) : (p i).fst ∈ coderivative (S i) x (u i) 0 := by
    change WithLp.toLp 2 ((p i).fst,-(0:F)) ∈ normalCone _ _
    rw [neg_zero,← hsnd i]
    exact hp i
  have hfst := hQ (fun i ↦ (p i).fst) hp' hsum
  apply WithLp.ofLp_injective
  funext i
  apply WithLp.ofLp_injective
  exact Prod.ext (hfst i) (hsnd i)

theorem exists_finite_sum_coderivative_multipliers (hS : ∀ i, SvOsc (S i))
    (hQ : FiniteSumCoderivativeQualification S x u) {v : E} {y : F}
    (hv : WithLp.toLp 2 (v,WithLp.toLp 2 (fun _ : ι ↦ -y)) ∈
      normalCone (finiteSumGraphLift S) (WithLp.toLp 2 (x,u))) :
    v ∈ finiteSetSum (fun i ↦ coderivative (S i) x (u i) y) := by
  let L := finiteSumGraphEmbedding (ι := ι) (E := E) (F := F)
  let D := l2PiSet (fun i ↦ euclideanSvGraph (S i))
  have hD : IsClosed D := isClosed_l2PiSet fun i ↦
    (isClosed_svGraph_iff_svOsc.mpr (hS i)).preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous
  have hQ' : NormalConstraintQualification univ D (fderiv ℝ L (WithLp.toLp 2 (x,u)))
      (WithLp.toLp 2 (x,u)) (L (WithLp.toLp 2 (x,u))) := by
    rw [ContinuousLinearMap.fderiv]
    exact finiteSumGraph_constraintQualification hQ
  have he : univ ∩ L ⁻¹' D = finiteSumGraphLift S := by rw [univ_inter]; rfl
  obtain ⟨p,hp,b,hb,heq⟩ := exists_normal_multipliers_of_mem_normalCone
    isClosed_univ hD L.contDiff hQ' (he.symm ▸ hv)
  rw [normalCone_univ,mem_singleton_iff] at hb
  rw [hb,add_zero,ContinuousLinearMap.fderiv] at heq
  change WithLp.toLp 2 (v,WithLp.toLp 2 (fun _ : ι ↦ -y)) = finiteSumGraphEmbedding.adjoint p at heq
  rw [finiteSumGraphEmbedding_adjoint] at heq
  have hvsum : v = ∑ i, (p i).fst := congrArg WithLp.fst heq
  have hysnd (i : ι) : -y = (p i).snd := congrArg (fun q ↦ q.snd i) heq
  change p ∈ normalCone (l2PiSet (fun i ↦ euclideanSvGraph (S i)))
    (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (x,u i))) at hp
  rw [normalCone_l2PiSet] at hp
  refine ⟨fun i ↦ (p i).fst,fun i ↦ ?_,hvsum.symm⟩
  change WithLp.toLp 2 ((p i).fst,-y) ∈ normalCone _ _
  simpa only [hysnd i] using hp i

/-- **Theorem 10.41**, the full finite-family coderivative inclusion. -/
theorem coderivative_svFiniteSum_subset (hS : ∀ i, SvOsc (S i)) {b : F}
    (hb : SvLocallyBoundedAt (finiteSumMappingAux S) (x,b))
    (hQ : ∀ u ∈ finiteSumMappingAux S (x,b), FiniteSumCoderivativeQualification S x u)
    (y : F) : coderivative (svFiniteSum S) x b y ⊆
      ⋃ u ∈ finiteSumMappingAux S (x,b), finiteSetSum (fun i ↦ coderivative (S i) x (u i) y) := by
  intro v hv
  change WithLp.toLp 2 (v,-y) ∈ normalCone (euclideanSvGraph (svFiniteSum S)) (WithLp.toLp 2 (x,b)) at hv
  rw [euclideanSvGraph_svFiniteSum] at hv
  obtain ⟨q,hq,hv⟩ := mem_iUnion₂.mp (normalCone_image_subset_iUnion (F := finiteSumGraphProjection (ι := ι) (E := E) (F := F))
    (isClosed_finiteSumGraphLift hS)
    (finiteSumGraphProjection (ι := ι) (E := E) (F := F)).contDiff (finiteSumGraphProjection_bounded_inverse hb) hv)
  have hqe : finiteSumGraphProjection q = WithLp.toLp 2 (x,b) := hq.2
  rw [finiteSumGraphProjection_apply] at hqe
  have hqx : q.fst = x := congrArg WithLp.fst hqe
  have hqb : ∑ i, q.snd i = b := congrArg WithLp.snd hqe
  have hqu : q.snd ∈ finiteSumMappingAux S (x,b) := ⟨by simpa only [← hqx] using hq.1,hqb⟩
  have hqeq : q = WithLp.toLp 2 (x,q.snd) := by
    apply WithLp.ofLp_injective
    exact Prod.ext hqx rfl
  rw [ContinuousLinearMap.fderiv,mem_preimage,finiteSumGraphProjection_adjoint,hqeq] at hv
  exact mem_iUnion₂.mpr ⟨q.snd,hqu,exists_finite_sum_coderivative_multipliers hS (hQ q.snd hqu) hv⟩

theorem convex_finiteSumGraphLift (hS : ∀ i, SvGraphConvex (S i)) :
    Convex ℝ (finiteSumGraphLift S) := by
  intro p hp q hq a b ha hb hab i
  exact hS i (x := (p.fst,p.snd i)) (y := (q.fst,q.snd i)) (hp i) (hq i) ha hb hab

theorem svGraphConvex_svFiniteSum (hS : ∀ i, SvGraphConvex (S i)) : SvGraphConvex (svFiniteSum S) := by
  have hc := (convex_finiteSumGraphLift hS).linear_image finiteSumGraphProjection.toLinearMap
  change Convex ℝ (finiteSumGraphProjection '' finiteSumGraphLift S) at hc
  rw [← euclideanSvGraph_svFiniteSum] at hc
  exact hc.linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toLinearEquiv.toLinearMap

/-- In the graph-convex case every fixed decomposition gives equality. -/
theorem coderivative_svFiniteSum_eq_of_convex (hS : ∀ i, SvOsc (S i))
    (hc : ∀ i, SvGraphConvex (S i)) (hu : ∀ i, u i ∈ S i x)
    (hQ : FiniteSumCoderivativeQualification S x u) (y : F) :
    coderivative (svFiniteSum S) x (∑ i, u i) y =
      finiteSetSum (fun i ↦ coderivative (S i) x (u i) y) := by
  have hp : WithLp.toLp 2 (x,u) ∈ finiteSumGraphLift S := hu
  have he := normalCone_linear_image_of_convex finiteSumGraphProjection (convex_finiteSumGraphLift hc) hp
  rw [finiteSumGraphProjection_apply,← euclideanSvGraph_svFiniteSum] at he
  simp only [WithLp.toLp_fst,WithLp.toLp_snd] at he
  ext v
  constructor
  · intro hv
    change WithLp.toLp 2 (v,-y) ∈ normalCone (euclideanSvGraph (svFiniteSum S)) _ at hv
    rw [he,mem_preimage,finiteSumGraphProjection_adjoint] at hv
    exact exists_finite_sum_coderivative_multipliers hS hQ hv
  · rintro ⟨v,hv,rfl⟩
    change WithLp.toLp 2 (∑ i, v i,-y) ∈ normalCone (euclideanSvGraph (svFiniteSum S)) _
    have hc' : Convex ℝ (euclideanSvGraph (svFiniteSum S)) := (svGraphConvex_svFiniteSum hc).linear_preimage
      (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearEquiv.toLinearMap
    rw [normalCone_eq_of_convex hc' (show WithLp.toLp 2 (x,∑ i, u i) ∈
      euclideanSvGraph (svFiniteSum S) from ⟨fun i ↦ u i,hu,rfl⟩)]
    intro p hp
    obtain ⟨q,hq,hqsum⟩ := hp
    have hineq (i : ι) : ⟪v i,p.fst-x⟫_ℝ - ⟪y,q i-u i⟫_ℝ ≤ 0 := by
      have hci : Convex ℝ (euclideanSvGraph (S i)) := (hc i).linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearEquiv.toLinearMap
      have hi := hv i
      change WithLp.toLp 2 (v i,-y) ∈ normalCone (euclideanSvGraph (S i)) (WithLp.toLp 2 (x,u i)) at hi
      rw [normalCone_eq_of_convex hci (hu i)] at hi
      have hh := hi (WithLp.toLp 2 (p.fst,q i)) (hq i)
      simpa only [WithLp.prod_inner_apply,WithLp.ofLp_sub,WithLp.ofLp_toLp,
        Prod.fst_sub,Prod.snd_sub,inner_neg_left,sub_eq_add_neg] using hh
    have hs := Finset.sum_nonpos (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ hineq i)
    rw [Finset.sum_sub_distrib,← sum_inner,← inner_sum,Finset.sum_sub_distrib,hqsum] at hs
    simpa only [WithLp.prod_inner_apply,WithLp.ofLp_sub,WithLp.ofLp_toLp,
      Prod.fst_sub,Prod.snd_sub,inner_neg_left,sub_eq_add_neg] using hs

end
end RW
