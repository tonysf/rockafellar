/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Normals and tangents to level sets
-/

import RockafellarWets.Chapter8.ProfileDerivatives
import RockafellarWets.Chapter8.CalmSubgradients
import RockafellarWets.Chapter6.ConstraintTangents
import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter3.PositiveHulls

open Filter Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {c : ℝ}

/-- The linear part of the horizontal epigraph embedding. -/
noncomputable def levelEmbeddingLinear : E →L[ℝ] WithLp 2 (E × ℝ) :=
  (l2ProdEquiv E).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- The horizontal embedding that represents a level set as an epigraph preimage. -/
def levelEmbedding (c : ℝ) (x : E) : WithLp 2 (E × ℝ) := WithLp.toLp 2 (x,c)

@[simp] theorem levelEmbeddingLinear_apply (w : E) :
    levelEmbeddingLinear w = WithLp.toLp 2 (w,(0:ℝ)) := rfl

theorem levelEmbedding_contDiff (c : ℝ) : ContDiff ℝ 1 (levelEmbedding (E := E) c) :=
  (l2ProdEquiv E).symm.toContinuousLinearMap.contDiff.comp
    (contDiff_id.prodMk contDiff_const)

theorem levelEmbedding_hasFDerivAt (c : ℝ) (x : E) :
    HasFDerivAt (levelEmbedding c) levelEmbeddingLinear x := by
  exact (l2ProdEquiv E).symm.toContinuousLinearMap.hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const c x))

@[simp] theorem levelEmbedding_fderiv (c : ℝ) (x : E) :
    fderiv ℝ (levelEmbedding c) x = levelEmbeddingLinear :=
  (levelEmbedding_hasFDerivAt c x).fderiv

@[simp] theorem levelEmbeddingLinear_adjoint (p : WithLp 2 (E × ℝ)) :
    (levelEmbeddingLinear (E := E)).adjoint p = p.fst := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left,levelEmbeddingLinear_apply,WithLp.prod_inner_apply]
  simp only [inner_zero_right,add_zero]
  rfl

@[simp] theorem preimage_epigraph_levelEmbedding (f : E → EReal) (c : ℝ) :
    levelEmbedding c ⁻¹' euclideanEpigraph f = levelSet f c := rfl

/-- Projecting epigraph normals gives positive multiples of subgradients
and the horizon subgradients. -/
theorem fst_normalCone_epigraph (hx : f x = c) (hl : IsLocallyLscAt f x) :
    WithLp.fst '' normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) =
      positiveHull (subdifferential f x) ∪ horizonSubdifferential f x := by
  ext v
  constructor
  · rintro ⟨p,hp,rfl⟩
    have hpair : p = WithLp.toLp 2 (p.fst,p.snd) := rfl
    have hb := vertical_nonpos_of_mem_normalCone_epigraph (v := p.fst) (β := p.snd) hp
    rcases eq_or_lt_of_le hb with hb0 | hbneg
    · right
      apply (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx).mpr
      simpa only [← hb0] using hp
    · left
      have hm : p.fst ∈ coderivative (epiProfile f) x c (-p.snd) := by
        simpa only [coderivative,svOfEuclideanNormals,mem_setOf_eq,neg_neg] using hp
      rw [(coderivatives_epiProfile_of_pos hx (neg_pos.mpr hbneg)).1] at hm
      obtain ⟨z,hz,he⟩ := hm
      exact Or.inr ⟨-p.snd,neg_pos.mpr hbneg,z,hz,he.symm⟩
  · rintro (hv | hv)
    · rcases hv with rfl | ⟨a,ha,z,hz,rfl⟩
      · exact ⟨0,(isCone_normalCone (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le)).1,rfl⟩
      · have hn := (isCone_normalCone (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le)).2
          ((mem_subdifferential_iff_epigraph_normal hx).mp hz) ha
        exact ⟨a • WithLp.toLp 2 (z,(-1:ℝ)),hn,rfl⟩
    · exact ⟨WithLp.toLp 2 (v,(0:ℝ)),horizontal_normal_of_mem_horizonSubdifferential hx hv,rfl⟩

/-- The qualification for a horizontal epigraph slice is precisely the
absence of the zero limiting subgradient. -/
theorem normalConstraintQualification_levelEmbedding (hx : f x = c)
    (hzero : (0:E) ∉ subdifferential f x) :
    NormalConstraintQualification univ (euclideanEpigraph f) levelEmbeddingLinear x
      (levelEmbedding c x) := by
  intro p hp hz
  rw [levelEmbeddingLinear_adjoint,normalCone_univ,mem_singleton_iff,neg_eq_zero] at hz
  have hb := vertical_nonpos_of_mem_normalCone_epigraph (v := p.fst) (β := p.snd) hp
  have hb0 : p.snd = 0 := by
    by_contra hne
    have hneg : p.snd < 0 := lt_of_le_of_ne hb hne
    have hm : p.fst ∈ coderivative (epiProfile f) x c (-p.snd) := by
      simpa only [coderivative,svOfEuclideanNormals,mem_setOf_eq,neg_neg] using hp
    rw [(coderivatives_epiProfile_of_pos hx (neg_pos.mpr hneg)).1] at hm
    obtain ⟨z,hzsub,he⟩ := hm
    have he0 : z = 0 := (smul_eq_zero.mp (he.trans hz)).resolve_left (neg_ne_zero.mpr hne)
    exact hzero (he0 ▸ hzsub)
  apply WithLp.ofLp_injective
  exact Prod.ext hz hb0

/-- **Proposition 10.3**, the unconditional tangent inclusion. -/
theorem tangentCone_levelSet_subset (hx : f x = c) :
    tangentCone (levelSet f c) x ⊆ {w | subderivative f x w ≤ 0} := by
  intro w hw
  have he : univ ∩ levelEmbedding c ⁻¹' euclideanEpigraph f = levelSet f c := by simp
  have h := (tangentCone_constraints_subset (X := univ) (D := euclideanEpigraph f)
    (levelEmbedding_hasFDerivAt c x) (he.symm ▸ hw)).2
  change WithLp.toLp 2 (w,(0:ℝ)) ∈ tangentCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) at h
  rw [← euclideanEpigraph_subderivative hx] at h
  exact h

/-- **Proposition 10.3**, the unconditional regular-normal inclusion. -/
theorem positiveHull_regularSubdifferential_subset_normalCone_levelSet (hx : f x = c) :
    positiveHull (regularSubdifferential f x) ⊆ regularNormalCone (levelSet f c) x := by
  have hxC : x ∈ levelSet f c := hx.le
  rintro v (rfl | ⟨a,ha,z,hz,rfl⟩)
  · exact (isCone_regularNormalCone hxC).1
  · apply (isCone_regularNormalCone hxC).2 _ ha
    apply mem_regularNormalCone_of_forall_inner_nonpos hxC
    intro w hw
    have hd := (inner_le_subderivative_of_mem_regularSubdifferential hz w).trans
      (tangentCone_levelSet_subset hx hw)
    exact EReal.coe_le_coe_iff.mp hd

/-- **Proposition 10.3**, limiting normals to a nonstationary level set. -/
theorem normalCone_levelSet_subset (hl : LowerSemicontinuous f) (hx : f x = c)
    (hzero : (0:E) ∉ subdifferential f x) :
    normalCone (levelSet f c) x ⊆ positiveHull (subdifferential f x) ∪ horizonSubdifferential f x := by
  have hD : IsClosed (euclideanEpigraph f) :=
    (isClosed_epigraph_of_lsc_ereal f hl).preimage (l2ProdEquiv E).continuous
  have hloc : IsLocallyLscAt f x := isLocallyLscAt_of_isLocallyClosedAt_epigraph hx
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f hl) (x,c))
  have hCQ : NormalConstraintQualification univ (euclideanEpigraph f)
      (fderiv ℝ (levelEmbedding c) x) x (levelEmbedding c x) := by
    rw [levelEmbedding_fderiv]
    exact normalConstraintQualification_levelEmbedding hx hzero
  intro v hv
  have he : univ ∩ levelEmbedding c ⁻¹' euclideanEpigraph f = levelSet f c := by simp
  obtain ⟨p,hp,z,hz,hvz⟩ := exists_normal_multipliers_of_mem_normalCone
    isClosed_univ hD (levelEmbedding_contDiff c) hCQ (he.symm ▸ hv)
  rw [normalCone_univ,mem_singleton_iff] at hz
  rw [hz,add_zero,levelEmbedding_fderiv,levelEmbeddingLinear_adjoint] at hvz
  rw [hvz,← fst_normalCone_epigraph hx hloc]
  exact ⟨p,hp,rfl⟩

/-- **Proposition 10.3**, the reverse regular-tangent inclusion. -/
theorem regularTangentCone_levelSet_superset (hl : LowerSemicontinuous f) (hx : f x = c)
    (hzero : (0:E) ∉ subdifferential f x) :
    {w | regularSubderivative f x w ≤ 0} ⊆ regularTangentCone (levelSet f c) x := by
  have hD : IsClosed (euclideanEpigraph f) :=
    (isClosed_epigraph_of_lsc_ereal f hl).preimage (l2ProdEquiv E).continuous
  have hCQ : NormalConstraintQualification univ (euclideanEpigraph f)
      (fderiv ℝ (levelEmbedding c) x) x (levelEmbedding c x) := by
    rw [levelEmbedding_fderiv]
    exact normalConstraintQualification_levelEmbedding hx hzero
  have he : univ ∩ levelEmbedding c ⁻¹' euclideanEpigraph f = levelSet f c := by simp
  intro w hw
  rw [← he]
  apply regularTangentCone_constraints_superset isClosed_univ hD (levelEmbedding_contDiff c)
    (show x ∈ univ ∩ levelEmbedding c ⁻¹' euclideanEpigraph f from ⟨trivial,hx.le⟩) hCQ
  refine ⟨?_,?_⟩
  · rw [← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt (mem_univ x)
      (isClarkeRegularAt_univ x),tangentCone_univ]
    trivial
  · rw [levelEmbedding_fderiv]
    change (0:ℝ) ∈ regularGraphicalDerivative (epiProfile f) x c w
    rw [regularGraphicalDerivative_epiProfile hx (hl x)]
    exact hw

/-- **Proposition 10.3**, all equalities and regularity at a nonstationary
regular point. -/
theorem levelSet_geometry_of_regular (hl : LowerSemicontinuous f) (hx : f x = c)
    (hzero : (0:E) ∉ subdifferential f x) (hr : IsSubdifferentiallyRegularAt f x) :
    IsClarkeRegularAt (levelSet f c) x ∧
      tangentCone (levelSet f c) x = {w | subderivative f x w ≤ 0} ∧
      normalCone (levelSet f c) x = positiveHull (subdifferential f x) ∪ horizonSubdifferential f x := by
  have hD : IsClosed (euclideanEpigraph f) :=
    (isClosed_epigraph_of_lsc_ereal f hl).preimage (l2ProdEquiv E).continuous
  have hloc : IsLocallyLscAt f x := isLocallyLscAt_of_isLocallyClosedAt_epigraph hx
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f hl) (x,c))
  have hCQ : NormalConstraintQualification univ (euclideanEpigraph f)
      (fderiv ℝ (levelEmbedding c) x) x (levelEmbedding c x) := by
    rw [levelEmbedding_fderiv]
    exact normalConstraintQualification_levelEmbedding hx hzero
  have hregD : IsClarkeRegularAt (euclideanEpigraph f) (levelEmbedding c x) := by
    simpa only [levelEmbedding,hx,EReal.toReal_coe] using hr.2.2
  have he : univ ∩ levelEmbedding c ⁻¹' euclideanEpigraph f = levelSet f c := by simp
  have hc := clarkeRegularity_constraints isClosed_univ hD (levelEmbedding_contDiff c)
    (show x ∈ univ ∩ levelEmbedding c ⁻¹' euclideanEpigraph f from ⟨trivial,hx.le⟩)
    hCQ (isClarkeRegularAt_univ x) hregD
  rw [he] at hc
  refine ⟨hc.1,Subset.antisymm (tangentCone_levelSet_subset hx) ?_,?_⟩
  · rw [(isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative).mp hr |>.2]
    exact (regularTangentCone_levelSet_superset hl hx hzero).trans
      (regularTangentCone_subset_tangentCone (show x ∈ levelSet f c from hx.le))
  · rw [hc.2,levelEmbedding_fderiv,normalCone_univ]
    simpa only [Set.add_singleton,add_zero,Set.image_id',levelEmbedding,
      levelEmbeddingLinear_adjoint] using fst_normalCone_epigraph hx hloc

end RW
