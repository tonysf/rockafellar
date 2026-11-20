/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inverse coderivatives and nonsingularity
-/

import RockafellarWets.Chapter9.MordukhovichCriterion
import RockafellarWets.Chapter9.MetricRegularity
import RockafellarWets.Chapter6.LimitingNormalChangeOfCoordinates
import RockafellarWets.Chapter5.ClosedImages
import RockafellarWets.Chapter5.DistanceCriteria

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {S : E → Set F} {x : E} {u : F}

private theorem normalCone_preimage_isometry (L : E ≃ₗᵢ[ℝ] F) (C : Set F) (a : E) :
    normalCone (L ⁻¹' C) a = L ⁻¹' normalCone C (L a) := by
  have h := normalCone_preimage_of_surjective
    (G := (L : E →L[ℝ] F)) (x := a)
    (L.toContinuousLinearMap.contDiff.contDiffAt)
    (by simpa only [ContinuousLinearMap.fderiv] using L.surjective) C
  rw [ContinuousLinearMap.fderiv,LinearIsometryEquiv.adjoint_eq_symm] at h
  change normalCone (L ⁻¹' C) a = L.symm '' normalCone C (L a) at h
  rw [h]
  ext v
  constructor
  · rintro ⟨z,hz,rfl⟩
    simpa using hz
  · intro hv
    exact ⟨L v,hv,L.symm_apply_apply v⟩

/-- Interchanging graph coordinates interchanges the coderivative variables
and reverses their signs. -/
theorem mem_coderivative_inverse_iff {y : E} {v : F} :
    v ∈ coderivative (svInv S) u x y ↔ -y ∈ coderivative S x u (-v) := by
  let L := LinearIsometryEquiv.withLpProdComm 2 ℝ F E
  have he : euclideanSvGraph (svInv S) = L ⁻¹' euclideanSvGraph S := rfl
  change WithLp.toLp 2 (v,-y) ∈ normalCone (euclideanSvGraph (svInv S)) _ ↔ _
  rw [he,normalCone_preimage_isometry]
  simp only [mem_preimage]
  change WithLp.toLp 2 (-y,v) ∈ normalCone (euclideanSvGraph S) _ ↔
    WithLp.toLp 2 (-y,-(-v)) ∈ normalCone (euclideanSvGraph S) _
  simp only [neg_neg]
  rfl

/-- The regular graphical derivative commutes with inversion at graph points. -/
theorem regularGraphicalDerivative_inverse (hu : u ∈ S x) :
    regularGraphicalDerivative (svInv S) u x = svInv (regularGraphicalDerivative S x u) := by
  let L := (LinearIsometryEquiv.withLpProdComm 2 ℝ F E).toContinuousLinearEquiv
  have he : euclideanSvGraph (svInv S) = L ⁻¹' euclideanSvGraph S := rfl
  ext y v
  change WithLp.toLp 2 (y,v) ∈ regularTangentCone (euclideanSvGraph (svInv S)) _ ↔ _
  rw [he,regularTangentCone_preimage (Φ := L) (Φ' := L)
    L.toContinuousLinearMap.hasStrictFDerivAt _
      (show L (WithLp.toLp 2 (u,x)) ∈ euclideanSvGraph S from hu)]
  rfl

/-- **Theorem 9.43(a,d)**: inverse Aubin behavior is equivalent to the
absence of nonzero multipliers sent to zero by the coderivative. -/
theorem hasAubinProperty_inverse_iff_coderivative_nonsingular (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    HasAubinPropertyAt (svInv S) u x ↔ ∀ y, 0 ∈ coderivative S x u y → y = 0 := by
  rw [hasAubinPropertyAt_iff_coderivative_zero (show x ∈ svInv S u from hu) hl.inverseGraph]
  constructor
  · intro h y hy
    have hm : -y ∈ coderivative (svInv S) u x 0 := by
      rw [mem_coderivative_inverse_iff]
      simpa using hy
    rw [h,mem_singleton_iff] at hm
    exact neg_eq_zero.mp hm
  · intro h
    apply Subset.antisymm
    · intro y hy
      have hm := mem_coderivative_inverse_iff.mp hy
      simp only [neg_zero] at hm
      simpa only [mem_singleton_iff,neg_eq_zero] using h (-y) hm
    · exact singleton_subset_iff.mpr
        (graphicalDerivative_properties (show x ∈ svInv S u from hu)).2.2.1.2.1

/-- **Theorem 9.43**, full range of the regular graphical derivative suffices
for inverse Aubin behavior. -/
theorem hasAubinProperty_inverse_of_regularGraphicalDerivative_full_range (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u))
    (hR : svRange (regularGraphicalDerivative S x u) = univ) :
    HasAubinPropertyAt (svInv S) u x := by
  apply hasAubinPropertyAt_of_regularGraphicalDerivative_full_domain
    (show x ∈ svInv S u from hu) hl.inverseGraph
  rw [regularGraphicalDerivative_inverse hu,svDom_svInv]
  exact hR

/-- **Theorem 9.43**, the regular-derivative range condition is also necessary
under graphical regularity. -/
theorem hasAubinProperty_inverse_iff_regularGraphicalDerivative_full_range_of_regular
    (hu : u ∈ S x) (hl : IsLocallyClosedAt (svGraph S) (x,u))
    (hr : IsGraphicallyRegularAt S x u) :
    HasAubinPropertyAt (svInv S) u x ↔ svRange (regularGraphicalDerivative S x u) = univ := by
  rw [hasAubinPropertyAt_iff_regularGraphicalDerivative_full_domain_of_regular
    (show x ∈ svInv S u from hu) hl.inverseGraph ((isGraphicallyRegularAt_svInv_iff hu).mpr hr),
    regularGraphicalDerivative_inverse hu,svDom_svInv]

/-- The two sign reversals in the inverse coderivative preserve its outer norm. -/
theorem svOuterNorm_coderivative_inverse :
    svOuterNorm (coderivative (svInv S) u x) = svOuterNorm (svInv (coderivative S x u)) := by
  apply le_antisymm
  · apply svOuterNorm_le_iff_ball.mpr
    intro y hy v hv
    have hm : -v ∈ svInv (coderivative S x u) (-y) := mem_coderivative_inverse_iff.mp hv
    simpa only [nnnorm_neg] using coe_nnnorm_le_svOuterNorm (by simpa using hy) hm
  · apply svOuterNorm_le_iff_ball.mpr
    intro y hy v hv
    have hm : -v ∈ coderivative (svInv S) u x (-y) := by
      rw [mem_coderivative_inverse_iff]
      simpa only [neg_neg] using hv
    simpa only [nnnorm_neg] using coe_nnnorm_le_svOuterNorm (by simpa using hy) hm

/-- **Theorem 9.43**, the coderivative formula for the exact inverse modulus. -/
theorem graphicalLipschitzModulus_inverse_eq_svOuterNorm_inverseCoderivative
    (hu : u ∈ S x) (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    graphicalLipschitzModulus (svInv S) u x = svOuterNorm (svInv (coderivative S x u)) := by
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative (show x ∈ svInv S u from hu) hl.inverseGraph,
    svOuterNorm_coderivative_inverse]

/-- **Theorem 9.43**, attainment of the maximum formula for the finite exact
inverse modulus. -/
theorem exists_max_inverseCoderivative_norm (h : HasAubinPropertyAt (svInv S) u x) :
    ∃ y : F, (coderivative S x u y ∩ closedBall (0:E) 1).Nonempty ∧
      graphicalLipschitzModulus (svInv S) u x = (‖y‖₊ : ℝ≥0∞) := by
  have hu : u ∈ S x := h.2.1
  have hl : IsLocallyClosedAt (svGraph S) (x,u) := h.2.2.1.inverseGraph
  let H := svInv (coderivative S x u)
  have hEq : graphicalLipschitzModulus (svInv S) u x = svOuterNorm H :=
    graphicalLipschitzModulus_inverse_eq_svOuterNorm_inverseCoderivative hu hl
  have hfin : svOuterNorm H ≠ ⊤ := by
    obtain ⟨k,hk⟩ := h.2.2.2
    rw [← hEq]
    exact (hk.modulus_le.trans_lt ENNReal.coe_lt_top).ne
  have ho : SvOsc H := svOsc_svInv_iff.mpr (graphicalDerivative_properties hu).2.2.1.1
  have hc : IsClosed (svImage H (closedBall (0:E) 1)) :=
    ho.isClosed_svImage_of_isCompact (isCompact_closedBall _ _)
  have hsub : svImage H (closedBall (0:E) 1) ⊆ closedBall (0:F) (svOuterNorm H).toReal := by
    intro y hy
    obtain ⟨v,hv,hy⟩ := mem_svImage.mp hy
    rw [mem_closedBall_zero_iff]
    simpa using ENNReal.toReal_mono hfin
      (coe_nnnorm_le_svOuterNorm (mem_closedBall_zero_iff.mp hv) hy)
  have hcomp := (isCompact_closedBall (0:F) (svOuterNorm H).toReal).of_isClosed_subset hc hsub
  have hne : (svImage H (closedBall (0:E) 1)).Nonempty := by
    exact ⟨0,mem_svImage.mpr ⟨0,by simp,(graphicalDerivative_properties hu).2.2.1.2.1⟩⟩
  obtain ⟨y,hy,hm⟩ := hcomp.exists_isMaxOn hne continuous_norm.continuousOn
  obtain ⟨v,hv,hyv⟩ := mem_svImage.mp hy
  refine ⟨y,⟨v,hyv,hv⟩,hEq.trans (le_antisymm ?_ ?_)⟩
  · apply svOuterNorm_le_iff_ball.mpr
    intro a ha b hb
    exact_mod_cast hm (show b ∈ svImage H (closedBall (0:E) 1) from
      (mem_svImage.mpr ⟨a,mem_closedBall_zero_iff.mpr ha,hb⟩))
  · exact coe_nnnorm_le_svOuterNorm (mem_closedBall_zero_iff.mp hv) hyv

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem inverse_outerNorm_le_iff_sphere {H : F → Set E}
    (hH : SvPositivelyHomogeneous H) {k : ℝ≥0} (hk : 0 < k) :
    svOuterNorm (svInv H) ≤ k ↔
      (k : ℝ≥0∞)⁻¹ ≤ ⨅ y : {y : F // ‖y‖ = 1}, infEDist 0 (H y) := by
  have hi : SvPositivelyHomogeneous (svInv H) := by
    apply svPositivelyHomogeneous_iff_isCone_svGraph.mpr
    have hc := svPositivelyHomogeneous_iff_isCone_svGraph.mp hH
    exact ⟨hH.1,fun p hp c hc' ↦ hc.2 (x := p.swap) hp hc'⟩
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hinv (a : ℝ≥0∞) : (k : ℝ≥0∞)⁻¹ ≤ a ↔ 1 ≤ (k : ℝ≥0∞)*a :=
    ENNReal.inv_le_iff_le_mul (fun _ ↦ hk0) (fun h ↦ (ENNReal.coe_ne_top h).elim)
  rw [hi.svOuterNorm_le_iff]
  constructor
  · intro hb
    apply le_iInf
    intro y
    rw [infEDist]
    refine le_iInf fun v ↦ le_iInf fun hv ↦ ?_
    rw [hinv]
    have hh : 1 ≤ (k:ℝ)*‖v‖ := by simpa only [y.2] using hb v y hv
    simpa [edist_dist,dist_zero_left,ENNReal.ofReal_mul] using ENNReal.ofReal_le_ofReal hh
  · intro hb v y hy
    by_cases hy0 : y = 0
    · rw [hy0,norm_zero]
      positivity
    have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hs : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hyn).le,inv_mul_cancel₀ hyn.ne']
    have hm : ‖y‖⁻¹ • v ∈ H (‖y‖⁻¹ • y) := by
      rw [hH.2 y _ (inv_pos.mpr hyn)]
      exact smul_mem_smul_set hy
    have hb' := (hb.trans (iInf_le _ ⟨‖y‖⁻¹ • y,hs⟩)).trans (infEDist_le_edist_of_mem hm)
    have he := (hinv _).mp hb'
    have hh : 1 ≤ (k:ℝ)*(‖y‖⁻¹*‖v‖) := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      simpa [edist_dist,dist_zero_left,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hyn).le,
        ENNReal.ofReal_mul] using he
    calc ‖y‖ = 1*‖y‖ := by simp
      _ ≤ ((k:ℝ)*(‖y‖⁻¹*‖v‖))*‖y‖ := mul_le_mul_of_nonneg_right hh hyn.le
      _ = k*‖v‖ := by field_simp

/-- **Theorem 9.43**, the reciprocal distance formula. The infimum convention
also handles the zero-dimensional output space and empty coderivative fibers. -/
theorem graphicalLipschitzModulus_inverse_eq_reciprocal_sphere (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    graphicalLipschitzModulus (svInv S) u x =
      (⨅ y : {y : F // ‖y‖ = 1}, infEDist 0 (coderivative S x u y))⁻¹ := by
  rw [graphicalLipschitzModulus_inverse_eq_svOuterNorm_inverseCoderivative hu hl]
  have hH := (graphicalDerivative_properties hu).2.2.1.2
  apply le_antisymm
  · by_contra! hgt
    obtain ⟨k,hk₁,hk₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hgt
    have hk : 0 < k := ENNReal.coe_pos.mp (lt_of_le_of_lt bot_le hk₁)
    exact hk₂.not_ge ((inverse_outerNorm_le_iff_sphere hH hk).mpr
      (ENNReal.inv_le_iff_inv_le.mp hk₁.le))
  · by_contra! hgt
    obtain ⟨k,hk₁,hk₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hgt
    have hk : 0 < k := ENNReal.coe_pos.mp (lt_of_le_of_lt bot_le hk₁)
    exact hk₂.not_ge (ENNReal.inv_le_iff_inv_le.mp
      ((inverse_outerNorm_le_iff_sphere hH hk).mp hk₁.le))

/-- The minimum in the reciprocal formula is attained whenever the output
space has a unit vector; infinite distances to empty fibers are allowed. -/
theorem exists_min_coderivative_sphere [Nontrivial F] (hu : u ∈ S x) :
    ∃ y : F, ‖y‖ = 1 ∧
      (⨅ z : {z : F // ‖z‖ = 1}, infEDist 0 (coderivative S x u z)) =
        infEDist 0 (coderivative S x u y) := by
  have ho : SvOsc (coderivative S x u) := (graphicalDerivative_properties hu).2.2.1.1
  have hc : LowerSemicontinuous (fun y ↦ infEDist (0:E) (coderivative S x u y)) := by
    intro y
    have ho' : SvOscWithinAt (coderivative S x u) univ y := (ho y).svOscWithinAt univ
    have hh : LowerSemicontinuousWithinAt (fun z ↦ infEDist (0:E) (coderivative S x u z)) univ y :=
      lowerSemicontinuousWithinAt_of_svOscWithinAt ho' 0
    exact lowerSemicontinuousWithinAt_univ_iff.mp hh
  obtain ⟨y,hy,hm⟩ := LowerSemicontinuousOn.exists_isMinOn
    (f := fun y : F ↦ infEDist (0:E) (coderivative S x u y))
    ((NormedSpace.sphere_nonempty (x := (0:F)) (r := 1)).mpr zero_le_one)
    (isCompact_sphere (0:F) 1) (hc.lowerSemicontinuousOn _)
  have hyn : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
  let q : {z : F // ‖z‖ = 1} → ℝ≥0∞ := fun z ↦ infEDist 0 (coderivative S x u z)
  refine ⟨y,hyn,?_⟩
  change (⨅ z, q z) = q ⟨y,hyn⟩
  apply le_antisymm (iInf_le q ⟨y,hyn⟩)
  apply le_iInf
  intro z
  exact hm (mem_sphere_zero_iff_norm.mpr z.2)

end RW
