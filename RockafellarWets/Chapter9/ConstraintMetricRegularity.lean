/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Metric regularity of smooth constraint systems
-/

import RockafellarWets.Chapter9.InverseCoderivatives
import RockafellarWets.Chapter6.ConstraintQualifications
import RockafellarWets.Chapter6.ElementaryCones

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal ENNReal Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {g : E → F} {D : Set F} {x : E}

/-- The multifunction `g(x)-D` appearing in Example 9.44. -/
def constraintMapping (g : E → F) (D : Set F) (x : E) : Set F := {u | g x-u ∈ D}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The residual distance in Example 9.44. -/
theorem infEDist_constraintMapping (g : E → F) (D : Set F) (x : E) (u : F) :
    infEDist u (constraintMapping g D x) = infEDist (g x-u) D := by
  have he : constraintMapping g D x = (fun v ↦ g x-v) '' D := by
    ext v
    constructor
    · intro hv
      exact ⟨g x-v,hv,by abel⟩
    · rintro ⟨w,hw,rfl⟩
      change g x-(g x-w) ∈ D
      simpa only [sub_sub_cancel] using hw
  have hi : Isometry (fun v : F ↦ g x-v) := Isometry.of_dist_eq fun a b ↦ by
    rw [dist_eq_norm,dist_eq_norm,show (g x-a)-(g x-b) = -(a-b) by abel,norm_neg]
  have hh := infEDist_image (x := g x-u) (t := D) hi
  simpa only [← he,sub_sub_cancel] using hh

/-- The coderivative of a smooth constraint mapping is the adjoint
derivative restricted to the normal cone of the target set. -/
theorem mem_coderivative_constraintMapping (hg : ContDiffAt ℝ 1 g x) {u y : F} {v : E} :
    v ∈ coderivative (constraintMapping g D) x u y ↔
      y ∈ normalCone D (g x-u) ∧ v = (fderiv ℝ g x).adjoint y := by
  let P := WithLp.fstL 2 ℝ E F
  let Q := WithLp.sndL 2 ℝ E F
  let G : WithLp 2 (E × F) → F := fun p ↦ g (P p)-Q p
  let A : WithLp 2 (E × F) →L[ℝ] F := (fderiv ℝ g x).comp P-Q
  let p := WithLp.toLp 2 (x,u)
  have hG : ContDiffAt ℝ 1 G p := (hg.comp p P.contDiff.contDiffAt).sub Q.contDiff.contDiffAt
  have hA : HasFDerivAt G A p :=
    ((hg.differentiableAt (by norm_num)).hasFDerivAt.comp p P.hasFDerivAt).sub Q.hasFDerivAt
  have hs : Function.Surjective (fderiv ℝ G p) := by
    rw [hA.fderiv]
    intro y
    exact ⟨WithLp.toLp 2 (0,-y),by simp [A,P,Q]⟩
  have ha (y : F) : A.adjoint y = WithLp.toLp 2 ((fderiv ℝ g x).adjoint y,-y) := by
    apply ext_inner_right ℝ
    intro z
    rw [ContinuousLinearMap.adjoint_inner_left]
    change ⟪y,(fderiv ℝ g x) z.fst-z.snd⟫_ℝ = _
    rw [WithLp.prod_inner_apply,inner_sub_right,inner_neg_left,ContinuousLinearMap.adjoint_inner_left]
    rfl
  change WithLp.toLp 2 (v,-y) ∈ normalCone (G ⁻¹' D) p ↔ _
  rw [normalCone_preimage_of_surjective hG hs D,hA.fderiv]
  constructor
  · rintro ⟨z,hz,he⟩
    rw [ha] at he
    have hsnd : -z = -y := congrArg WithLp.snd he
    have hzy : z = y := neg_injective hsnd
    subst z
    exact ⟨hz,(congrArg WithLp.fst he).symm⟩
  · rintro ⟨hy,rfl⟩
    exact ⟨y,hy,ha y⟩

/-- **Example 9.44**: the normal-cone constraint qualification is necessary
and sufficient for the local residual error bound. -/
theorem constraint_metricRegularity_iff (hg : ContDiff ℝ 1 g) (hD : IsClosed D) (hx : g x ∈ D) :
    (∃ k : ℝ≥0, MetricRegularityEstimate (constraintMapping g D) x 0 k) ↔
      ∀ y ∈ normalCone D (g x), (fderiv ℝ g x).adjoint y = 0 → y = 0 := by
  have hu : (0:F) ∈ constraintMapping g D x := by simpa [constraintMapping] using hx
  have hc : IsClosed (svGraph (constraintMapping g D)) :=
    hD.preimage ((hg.continuous.comp continuous_fst).sub continuous_snd)
  have hl := RW.IsClosed.isLocallyClosedAt hc (x,0)
  rw [← hasAubinProperty_inverse_iff_metricRegularity hu hl,
    hasAubinProperty_inverse_iff_coderivative_nonsingular hu hl]
  simp only [mem_coderivative_constraintMapping hg.contDiffAt,sub_zero,and_imp,eq_comm (a := (0:E))]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **Example 9.44**, the metric inequality written directly in terms of
the residual `g(y)-u ∈ D`. -/
theorem metricRegularity_constraint_iff_residual {k : ℝ≥0} :
    MetricRegularityEstimate (constraintMapping g D) x 0 k ↔
      ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 (0:F), ∀ y ∈ V, ∀ u ∈ W,
        infEDist y {z | g z-u ∈ D} ≤ (k:ℝ≥0∞)*infEDist (g y-u) D := by
  simp only [MetricRegularityEstimate,InverseMetricEstimate,inter_univ,infEDist_constraintMapping]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **Example 9.44**, the error bound for the unperturbed feasible set,
obtained by setting the parameter to zero in the residual estimate. -/
theorem MetricRegularityEstimate.constraint_errorBound {k : ℝ≥0}
    (h : MetricRegularityEstimate (constraintMapping g D) x 0 k) :
    ∃ ε > 0, ∀ y ∈ closedBall x ε,
      infEDist y (g ⁻¹' D) ≤ (k:ℝ≥0∞)*infEDist (g y) D := by
  obtain ⟨V,hV,W,hW,h⟩ := metricRegularity_constraint_iff_residual.mp h
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨ε/2,by positivity,fun y hy ↦ ?_⟩
  have hyV : y ∈ V := hεV (by
    rw [mem_ball]
    have hdist := mem_closedBall.mp hy
    linarith)
  simpa only [sub_zero] using h y hyV 0 (mem_of_mem_nhds hW)

/-- **Example 9.44**, the tangent-cone form of the constraint qualification
when the target set is Clarke regular. -/
theorem constraint_metricRegularity_iff_tangent_range (hg : ContDiff ℝ 1 g)
    (hD : IsClosed D) (hx : g x ∈ D) (hr : IsClarkeRegularAt D (g x)) :
    (∃ k : ℝ≥0, MetricRegularityEstimate (constraintMapping g D) x 0 k) ↔
      tangentCone D (g x) + Set.range (fderiv ℝ g x) = univ := by
  rw [constraint_metricRegularity_iff hg hD hx]
  have h := regularTangentConstraintQualification_iff_normalConstraintQualification
    (A := fderiv ℝ g x) (mem_univ x) hx (isClarkeRegularAt_univ x) hr
  have hneg : -((fderiv ℝ g x) '' (univ : Set E)) = Set.range (fderiv ℝ g x) := by
    ext v
    simp only [Set.mem_neg,mem_image,mem_univ,true_and,mem_range]
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨-a,by simpa only [map_neg,neg_neg] using congrArg Neg.neg ha⟩
    · rintro ⟨a,rfl⟩
      exact ⟨-a,map_neg _ _⟩
  have hru : regularTangentCone (univ : Set E) x = univ := by
    rw [← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt (mem_univ x) (isClarkeRegularAt_univ x),tangentCone_univ]
  simpa only [RegularTangentConstraintQualification,NormalConstraintQualification,
    hru,normalCone_univ,hneg,mem_singleton_iff,neg_eq_zero,
    ← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hx hr] using h.symm

/-- **Example 9.44**, the exact bound in terms of unit normal multipliers.
The supremum uses the extended-real convention at a singular multiplier. -/
theorem graphicalLipschitzModulus_inverse_constraint_eq (hg : ContDiff ℝ 1 g)
    (hD : IsClosed D) (hx : g x ∈ D) :
    graphicalLipschitzModulus (svInv (constraintMapping g D)) 0 x =
      ⨆ y : {y : F // y ∈ normalCone D (g x) ∧ ‖y‖ = 1},
        ((‖(fderiv ℝ g x).adjoint y‖₊ : ℝ≥0∞))⁻¹ := by
  have hu : (0:F) ∈ constraintMapping g D x := by simpa [constraintMapping] using hx
  have hc : IsClosed (svGraph (constraintMapping g D)) :=
    hD.preimage ((hg.continuous.comp continuous_fst).sub continuous_snd)
  rw [graphicalLipschitzModulus_inverse_eq_reciprocal_sphere hu (RW.IsClosed.isLocallyClosedAt hc (x,0))]
  have he : (⨅ y : {y : F // ‖y‖ = 1}, infEDist (0:E) (coderivative (constraintMapping g D) x 0 y)) =
      ⨅ y : {y : F // y ∈ normalCone D (g x) ∧ ‖y‖ = 1}, (‖(fderiv ℝ g x).adjoint y‖₊ : ℝ≥0∞) := by
    have hf (y : F) (hy : y ∈ normalCone D (g x)) :
        coderivative (constraintMapping g D) x 0 y = {(fderiv ℝ g x).adjoint y} := by
      ext v
      simp only [mem_coderivative_constraintMapping hg.contDiffAt,sub_zero,hy,true_and,mem_singleton_iff]
    apply le_antisymm
    · apply le_iInf
      intro y
      apply iInf_le_of_le ⟨y.1,y.2.2⟩
      rw [hf y.1 y.2.1]
      simp only [infEDist_singleton,edist_nndist,nndist_zero_left]
      exact le_rfl
    · apply le_iInf
      intro y
      by_cases hy : y.1 ∈ normalCone D (g x)
      · rw [hf y.1 hy]
        simpa only [infEDist_singleton,edist_nndist,nndist_zero_left] using
          (iInf_le (fun z : {z : F // z ∈ normalCone D (g x) ∧ ‖z‖ = 1} ↦
            (‖(fderiv ℝ g x).adjoint z‖₊ : ℝ≥0∞)) ⟨y.1,hy,y.2⟩)
      · have hempty : coderivative (constraintMapping g D) x 0 y = ∅ := by
          ext v
          simp only [mem_coderivative_constraintMapping hg.contDiffAt,sub_zero,hy,false_and,mem_empty_iff_false]
        rw [hempty,infEDist_empty]
        exact le_top
  rw [he,ENNReal.inv_iInf]

/-- The reciprocal norm maximum in **Example 9.44** is attained whenever
there is a unit normal multiplier. The supremum formula above also covers
the empty unit-normal set, where its value is zero. -/
theorem exists_max_constraint_inverse_modulus (hg : ContDiff ℝ 1 g) (hD : IsClosed D)
    (hx : g x ∈ D) (hne : (normalCone D (g x) ∩ sphere (0:F) 1).Nonempty) :
    ∃ y : F, y ∈ normalCone D (g x) ∧ ‖y‖ = 1 ∧
      graphicalLipschitzModulus (svInv (constraintMapping g D)) 0 x =
        ((‖(fderiv ℝ g x).adjoint y‖₊ : ℝ≥0∞))⁻¹ := by
  have hc := (isCompact_sphere (0:F) 1).inter_left (isClosed_normalCone D (g x))
  obtain ⟨y,hy,hm⟩ := hc.exists_isMinOn hne (fderiv ℝ g x).adjoint.continuous.norm.continuousOn
  have hyn : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy.2
  refine ⟨y,hy.1,hyn,?_⟩
  rw [graphicalLipschitzModulus_inverse_constraint_eq hg hD hx]
  let q : {z : F // z ∈ normalCone D (g x) ∧ ‖z‖ = 1} → ℝ≥0∞ :=
    fun z ↦ (‖(fderiv ℝ g x).adjoint z‖₊ : ℝ≥0∞)⁻¹
  change (⨆ z, q z) = q ⟨y,hy.1,hyn⟩
  apply le_antisymm (iSup_le fun z ↦ ?_) (le_iSup q ⟨y,hy.1,hyn⟩)
  apply ENNReal.inv_le_inv.mpr
  exact_mod_cast hm (show z.1 ∈ normalCone D (g x) ∩ sphere (0:F) 1 from
    ⟨z.2.1,mem_sphere_zero_iff_norm.mpr z.2.2⟩)

end RW
