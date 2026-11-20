/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Extremal principles for sums and nonoverlapping sets
-/

import RockafellarWets.Chapter9.ExtremalPrinciples

open Filter Metric Set Topology
open scoped BigOperators InnerProductSpace Pointwise

namespace RW

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Proposition 9.69(b).** At a boundary point of a finite sum, every
specified decomposition admits a common nonzero limiting normal. -/
theorem extremal_finiteSetSum {ι : Type*} [Fintype ι] {C : ι → Set E}
    (hC : ∀ i, IsClosed (C i)) (a : ι → E) (ha : ∀ i, a i ∈ C i)
    (hb : (∑ i, a i) ∉ interior (finiteSetSum C)) :
    ∃ v : E, v ≠ 0 ∧ ∀ i, v ∈ normalCone (C i) (a i) := by
  let p : PiLp 2 (fun _ : ι ↦ E) := WithLp.toLp 2 a
  have hp : p ∈ l2PiSet C := ha
  have hnot : l2PiSum p ∉ interior (l2PiSum '' l2PiSet C) := by
    rw [← finiteSetSum_eq_l2PiSum_image]
    simpa only [l2PiSum_apply,p] using hb
  obtain ⟨v,hv,hn⟩ := extremal_linear_image l2PiSum (isClosed_l2PiSet hC) hp hnot
  rw [normalCone_l2PiSet,l2PiSum_adjoint_apply] at hn
  exact ⟨-v,neg_ne_zero.mpr hv,fun i ↦ hn i⟩

private def l2Difference : WithLp 2 (E × E) →L[ℝ] E :=
  ((ContinuousLinearMap.fst ℝ E E).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap) -
    ((ContinuousLinearMap.snd ℝ E E).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap)

private theorem l2Difference_apply (p : WithLp 2 (E × E)) : l2Difference p = p.fst-p.snd := rfl

private theorem l2Difference_adjoint (v : E) :
    (l2Difference : WithLp 2 (E × E) →L[ℝ] E).adjoint v = WithLp.toLp 2 (v,-v) := by
  apply ext_inner_right ℝ
  intro p
  rw [ContinuousLinearMap.adjoint_inner_left,WithLp.prod_inner_apply,l2Difference_apply]
  change ⟪v,p.fst-p.snd⟫_ℝ = ⟪v,p.fst⟫_ℝ + ⟪-v,p.snd⟫_ℝ
  rw [inner_sub_right,inner_neg_left,sub_eq_add_neg]

private theorem l2Difference_image (C D : Set E) :
    l2Difference '' l2ProdSet C D = C-D := by
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨p.fst,hp.1,p.snd,hp.2,rfl⟩
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact ⟨WithLp.toLp 2 (a,b),⟨ha,hb⟩,rfl⟩

/-- **Proposition 9.69(c).** Local nonoverlap gives opposite nonzero limiting
normals. No convexity or regularity assumption is imposed. -/
theorem extremal_nonoverlap_normals {C D : Set E} {x : E}
    (hC : IsClosed C) (hD : IsClosed D) (hxC : x ∈ C) (hxD : x ∈ D)
    {δ : ℝ} (hδ : 0 < δ)
    (hb : (0:E) ∉ interior ((C ∩ closedBall x δ) - (D ∩ closedBall x δ))) :
    ∃ v : E, v ≠ 0 ∧ v ∈ normalCone C x ∧ -v ∈ normalCone D x := by
  let C₀ := C ∩ closedBall x δ
  let D₀ := D ∩ closedBall x δ
  let p := WithLp.toLp 2 (x,x)
  have hp : p ∈ l2ProdSet C₀ D₀ :=
    ⟨⟨hxC,mem_closedBall_self hδ.le⟩,⟨hxD,mem_closedBall_self hδ.le⟩⟩
  have hnot : l2Difference p ∉ interior (l2Difference '' l2ProdSet C₀ D₀) := by
    rw [l2Difference_image]
    simpa only [l2Difference_apply,p,WithLp.toLp_fst,WithLp.toLp_snd,sub_self] using hb
  have hclosed : IsClosed (l2ProdSet C₀ D₀) :=
    isClosed_l2ProdSet (hC.inter isClosed_closedBall) (hD.inter isClosed_closedBall)
  obtain ⟨y,hy,hn⟩ := extremal_linear_image (X := l2ProdSet C₀ D₀) (x := p)
    (l2Difference : WithLp 2 (E × E) →L[ℝ] E) hclosed hp hnot
  change -((l2Difference : WithLp 2 (E × E) →L[ℝ] E).adjoint y) ∈
    normalCone (l2ProdSet C₀ D₀) (WithLp.toLp 2 (x,x)) at hn
  rw [normalCone_l2ProdSet,l2Difference_adjoint] at hn
  have hNC : -y ∈ normalCone C x := by
    have h : -y ∈ normalCone C₀ x := hn.1
    rwa [normalCone_inter_nhds (closedBall_mem_nhds x hδ)] at h
  have hND : y ∈ normalCone D x := by
    have h : y ∈ normalCone D₀ x := by simpa only [WithLp.neg_snd,WithLp.toLp_snd,neg_neg] using hn.2
    rwa [normalCone_inter_nhds (closedBall_mem_nhds x hδ)] at h
  exact ⟨-y,neg_ne_zero.mpr hy,hNC,by simpa only [neg_neg] using hND⟩

/-- The hyperplane orthogonal to an extremal normal separates the regular
tangent cones. -/
theorem extremal_nonoverlap_separation {C D : Set E} {x : E}
    (hC : IsClosed C) (hD : IsClosed D) (hxC : x ∈ C) (hxD : x ∈ D)
    {δ : ℝ} (hδ : 0 < δ)
    (hb : (0:E) ∉ interior ((C ∩ closedBall x δ) - (D ∩ closedBall x δ))) :
    ∃ v : E, v ≠ 0 ∧ v ∈ normalCone C x ∧ -v ∈ normalCone D x ∧
      (∀ w ∈ regularTangentCone C x, ⟪v,w⟫_ℝ ≤ 0) ∧
      (∀ w ∈ regularTangentCone D x, 0 ≤ ⟪v,w⟫_ℝ) := by
  obtain ⟨v,hv,hvC,hvD⟩ := extremal_nonoverlap_normals hC hD hxC hxD hδ hb
  refine ⟨v,hv,hvC,hvD,?_,?_⟩
  · intro w hw
    exact inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone hxC
      (RW.IsClosed.isLocallyClosedAt hC x) hvC hw
  · intro w hw
    have h := inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone hxD
      (RW.IsClosed.isLocallyClosedAt hD x) hvD hw
    simpa only [inner_neg_left,neg_nonpos] using h

end
end RW
