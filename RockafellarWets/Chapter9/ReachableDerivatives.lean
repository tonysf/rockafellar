/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reachable derivatives and gradients
-/

import RockafellarWets.Chapter9.Rademacher
import RockafellarWets.Chapter9.LipschitzSubgradientLimits
import RockafellarWets.Chapter8.SubgradientsAndGradients

open Filter Metric Set Topology MeasureTheory
open scoped NNReal InnerProductSpace

namespace RW

section ClusterValues

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- Limits of values along a prescribed approach set. -/
def clusterValuesWithin (g : E → F) (D : Set E) (x : E) : Set F :=
  outerSetLimitAlong (𝓝[D] x) (fun y ↦ {g y})

theorem mem_clusterValuesWithin_iff {g : E → F} {D : Set E} {x : E} {v : F} :
    v ∈ clusterValuesWithin g D x ↔ ∃ y : ℕ → E,
      (∀ n, y n ∈ D) ∧ Tendsto y atTop (𝓝 x) ∧ Tendsto (fun n ↦ g (y n)) atTop (𝓝 v) := by
  rw [clusterValuesWithin,mem_outerSetLimitAlong_iff_exists_seq]
  constructor
  · rintro ⟨y,w,hy,hw,hwt⟩
    have he : w = fun n ↦ g (y n) := funext fun n ↦ hw n
    rw [he] at hwt
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hy.eventually self_mem_nhdsWithin)
    exact ⟨fun n ↦ y (n+N),fun n ↦ hN _ (Nat.le_add_left N n),
      (hy.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N),
      hwt.comp (tendsto_add_atTop_nat N)⟩
  · rintro ⟨y,hy,hyt,hgt⟩
    exact ⟨y,fun n ↦ g (y n),tendsto_nhdsWithin_of_forall_mem hy hyt,fun _ ↦ rfl,hgt⟩

theorem isClosed_clusterValuesWithin (g : E → F) (D : Set E) (x : E) :
    IsClosed (clusterValuesWithin g D x) := isClosed_outerSetLimitAlong _ _

theorem clusterValuesWithin_congr {g h : E → F} {D : Set E} {x : E}
    (heq : ∀ᶠ y in 𝓝[D] x, g y = h y) :
    clusterValuesWithin g D x = clusterValuesWithin h D x :=
  outerSetLimitAlong_congr (heq.mono fun _ hy ↦ congrArg singleton hy)

/-- Continuous images commute with cluster values when the original values
remain in a compact set near the base point. -/
theorem clusterValuesWithin_comp {G : Type*} [MetricSpace G] {g : E → F}
    {D : Set E} {x : E} {H : F → G} (hH : Continuous H) {K : Set F}
    (hK : IsCompact K) (hbound : ∀ᶠ y in 𝓝[D] x, g y ∈ K) :
    clusterValuesWithin (H ∘ g) D x = H '' clusterValuesWithin g D x := by
  ext v
  constructor
  · intro hv
    obtain ⟨y,hy,hyt,hHt⟩ := mem_clusterValuesWithin_iff.mp hv
    have hKseq := (tendsto_nhdsWithin_of_forall_mem hy hyt).eventually hbound
    obtain ⟨a,ha,φ,hφ,hat⟩ := hK.tendsto_subseq' hKseq.frequently
    have hval : H a = v := tendsto_nhds_unique (hH.tendsto a |>.comp hat)
      (hHt.comp hφ.tendsto_atTop)
    refine ⟨a,mem_clusterValuesWithin_iff.mpr ⟨y ∘ φ,fun n ↦ hy _,
      hyt.comp hφ.tendsto_atTop,hat⟩,hval⟩
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨y,hy,hyt,hgt⟩ := mem_clusterValuesWithin_iff.mp ha
    exact mem_clusterValuesWithin_iff.mpr ⟨y,hy,hyt,(hH.tendsto a).comp hgt⟩

/-- If every cluster value lies in an open set and the values remain in a
compact set, then all sufficiently nearby values lie in that open set. -/
theorem eventually_mem_of_clusterValuesWithin_subset {g : E → F} {D : Set E} {x : E}
    {K U : Set F} (hK : IsCompact K) (hbound : ∀ᶠ y in 𝓝[D] x, g y ∈ K)
    (hU : IsOpen U) (hsub : clusterValuesWithin g D x ⊆ U) :
    ∀ᶠ y in 𝓝[D] x, g y ∈ U := by
  by_contra hn
  have hfreq : ∃ᶠ y in 𝓝[D] x, ({g y} ∩ (K ∩ Uᶜ)).Nonempty :=
    ((not_eventually.mp hn).and_eventually hbound).mono fun y hy ↦
      ⟨g y,rfl,hy.2,hy.1⟩
  obtain ⟨v,hv,hvK,hvU⟩ := outerSetLimitAlong_inter_nonempty_of_frequently
    (hK.inter_right hU.isClosed_compl) hfreq
  exact hvU (hsub hv)

/-- A locally relatively compact mapping converges whenever its cluster set
has only one possible value. -/
theorem tendsto_of_clusterValuesWithin_subset_singleton {g : E → F} {D : Set E} {x : E}
    {K : Set F} (hK : IsCompact K) (hbound : ∀ᶠ y in 𝓝[D] x, g y ∈ K) {v : F}
    (hsub : clusterValuesWithin g D x ⊆ {v}) : Tendsto g (𝓝[D] x) (𝓝 v) := by
  apply hK.tendsto_nhds_of_unique_mapClusterPt hbound
  intro z _ hz
  apply hsub
  intro U hU
  exact (hz.frequently hU).mono fun y hy ↦ ⟨g y,rfl,hy⟩

theorem clusterValuesWithin_nonempty_compact [ProperSpace F] {g : E → F} {D : Set E} {x : E}
    (hx : x ∈ closure D) {K : Set F} (hK : IsCompact K)
    (hbound : ∀ᶠ y in 𝓝[D] x, g y ∈ K) :
    (clusterValuesWithin g D x).Nonempty ∧ IsCompact (clusterValuesWithin g D x) := by
  haveI : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hsub : clusterValuesWithin g D x ⊆ K :=
    outerSetLimitAlong_subset_of_eventually_subset hK.isClosed
      (hbound.mono fun y hy ↦ singleton_subset_iff.mpr hy)
  exact ⟨(outerSetLimitAlong_inter_nonempty_of_frequently hK
      (hbound.mono fun y hy ↦ ⟨g y,rfl,hy⟩).frequently).mono inter_subset_left,
    hK.of_isClosed_subset (isClosed_clusterValuesWithin g D x) hsub⟩

end ClusterValues

section Derivatives

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The reachable Jacobians used in **Theorem 9.62**. -/
def reachableJacobians (f : E → F) (D : Set E) (x : E) : Set (E →L[ℝ] F) :=
  clusterValuesWithin (fderiv ℝ f) D x

/-- The reachable gradients used in **Theorem 9.61**. -/
def reachableGradients (f : E → ℝ) (D : Set E) (x : E) : Set E :=
  clusterValuesWithin (gradient f) D x

theorem StrictlyContinuousAt.eventually_norm_fderiv_le {f : E → F} {x : E}
    (hf : StrictlyContinuousAt f x) : ∃ k : ℝ≥0, ∀ᶠ y in 𝓝 x, ‖fderiv ℝ f y‖ ≤ k := by
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp hf
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨k,?_⟩
  filter_upwards [ball_mem_nhds x hr] with y hy
  exact norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hy) (hL.mono hball)

/-- The compactness and nonemptiness assertion in **Theorem 9.62**, valid
for every dense approach set, independently of any exceptional-set choice. -/
theorem reachableJacobians_nonempty_compact {f : E → F} {D : Set E} {x : E}
    (hf : StrictlyContinuousAt f x) (hx : x ∈ closure D) :
    (reachableJacobians f D x).Nonempty ∧ IsCompact (reachableJacobians f D x) := by
  obtain ⟨k,hk⟩ := hf.eventually_norm_fderiv_le
  apply clusterValuesWithin_nonempty_compact hx (isCompact_closedBall 0 k)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hk] with y hy
  simpa only [mem_closedBall,dist_zero_right] using hy

theorem reachableGradients_nonempty_compact {f : E → ℝ} {D : Set E} {x : E}
    (hf : StrictlyContinuousAt f x) (hx : x ∈ closure D) :
    (reachableGradients f D x).Nonempty ∧ IsCompact (reachableGradients f D x) := by
  obtain ⟨k,hk⟩ := hf.eventually_norm_fderiv_le
  apply clusterValuesWithin_nonempty_compact hx (isCompact_closedBall 0 k)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hk] with y hy
  simpa only [mem_closedBall,dist_zero_right,gradient,LinearIsometryEquiv.norm_map] using hy

/-- Reachable gradients are limiting subgradients. -/
theorem reachableGradients_subset_subdifferential {f : E → ℝ} {D : Set E} {x : E}
    (hf : ContinuousAt f x) (hD : ∀ y ∈ D, DifferentiableAt ℝ f y) :
    reachableGradients f D x ⊆ subdifferential (fun y ↦ (f y:EReal)) x := by
  intro v hv
  obtain ⟨y,hy,hyt,hgt⟩ := mem_clusterValuesWithin_iff.mp hv
  refine mem_subdifferential_iff_exists_seq.mpr ⟨⟨f x,rfl⟩,y,fun n ↦ gradient f (y n),hyt,
    EReal.tendsto_coe.mpr (hf.tendsto.comp hyt),fun n ↦ ?_,hgt⟩
  exact (regularSubdifferential_of_hasGradientAt (hD _ (hy n)).hasGradientAt).1.symm ▸ rfl

/-- Scalarizing a derivative corresponds to applying its adjoint. -/
theorem gradient_inner_comp_eq_adjoint {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (w : F) :
    gradient (fun y ↦ ⟪w,f y⟫_ℝ) x = (fderiv ℝ f x).adjoint w := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt _ (innerSL ℝ ((fderiv ℝ f x).adjoint w)) x
  have he : innerSL ℝ ((fderiv ℝ f x).adjoint w) =
      (innerSL ℝ w).comp (fderiv ℝ f x) := by
    ext z
    simp only [innerSL_apply_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]
  rw [he]
  exact (innerSL ℝ w).hasFDerivAt.comp x hf.hasFDerivAt

theorem StrictlyContinuousAt.inner_const {f : E → F} {x : E}
    (hf : StrictlyContinuousAt f x) (w : F) :
    StrictlyContinuousAt (fun y ↦ ⟪w,f y⟫_ℝ) x := by
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp hf
  exact strictlyContinuousAt_iff.mpr ⟨‖innerSL ℝ w‖₊ * k,U,hU,
    (innerSL ℝ w).lipschitz.comp_lipschitzOnWith hL⟩

/-- The reachable gradients of a scalarization are precisely the adjoint
images of the reachable Jacobians, with the same prescribed approach set. -/
theorem reachableGradients_inner_comp {f : E → F} {D : Set E} {x : E}
    (hf : StrictlyContinuousAt f x) (hD : ∀ y ∈ D, DifferentiableAt ℝ f y) (w : F) :
    reachableGradients (fun y ↦ ⟪w,f y⟫_ℝ) D x =
      (fun A : E →L[ℝ] F ↦ A.adjoint w) '' reachableJacobians f D x := by
  obtain ⟨k,hk⟩ := hf.eventually_norm_fderiv_le
  unfold reachableGradients reachableJacobians
  rw [clusterValuesWithin_congr (show ∀ᶠ y in 𝓝[D] x,
      gradient (fun z ↦ ⟪w,f z⟫_ℝ) y = (fderiv ℝ f y).adjoint w from
    (show ∀ᶠ y in 𝓝[D] x, y ∈ D from self_mem_nhdsWithin).mono
      fun y hy ↦ gradient_inner_comp_eq_adjoint (hD y hy) w)]
  apply clusterValuesWithin_comp (g := fderiv ℝ f)
    (H := fun A : E →L[ℝ] F ↦ A.adjoint w)
    (ContinuousLinearMap.adjoint.continuous.clm_apply continuous_const)
    (isCompact_closedBall 0 k)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hk] with y hy
  simpa only [mem_closedBall,dist_zero_right] using hy

/-- Evaluation commutes with the convex hull of a family of Jacobians. -/
theorem convexHull_image_apply (K : Set (E →L[ℝ] F)) (w : E) :
    convexHull ℝ ((fun A : E →L[ℝ] F ↦ A w) '' K) =
      (fun A : E →L[ℝ] F ↦ A w) '' convexHull ℝ K := by
  have hlin : IsLinearMap ℝ (fun A : E →L[ℝ] F ↦ A w) :=
    ⟨fun _ _ ↦ rfl,fun _ _ ↦ rfl⟩
  exact (hlin.image_convexHull K).symm

/-- Adjoint evaluation commutes with the convex hull of a real family of
Jacobians. -/
theorem convexHull_image_adjoint_apply (K : Set (E →L[ℝ] F)) (y : F) :
    convexHull ℝ ((fun A : E →L[ℝ] F ↦ A.adjoint y) '' K) =
      (fun A : E →L[ℝ] F ↦ A.adjoint y) '' convexHull ℝ K := by
  have hlin : IsLinearMap ℝ (fun A : E →L[ℝ] F ↦ A.adjoint y) :=
    ⟨fun _ _ ↦ by simp,fun _ _ ↦ by simp⟩
  exact (hlin.image_convexHull K).symm

theorem convexHull_reachableGradients_inner_comp {f : E → F} {D : Set E} {x : E}
    (hf : StrictlyContinuousAt f x) (hD : ∀ y ∈ D, DifferentiableAt ℝ f y) (y : F) :
    convexHull ℝ (reachableGradients (fun a ↦ ⟪y,f a⟫_ℝ) D x) =
      (fun A : E →L[ℝ] F ↦ A.adjoint y) '' convexHull ℝ (reachableJacobians f D x) := by
  rw [reachableGradients_inner_comp hf hD y,convexHull_image_adjoint_apply]

end Derivatives

section NullSets

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- An approach set omitting only a null subset of the differentiability
points contains almost every point of the open domain. -/
theorem ae_mem_differentiability_set_of_null_complement (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → F} {O D : Set E} (hf : ∀ x ∈ O, StrictlyContinuousAt f x)
    (hnull : μ ({x ∈ O | DifferentiableAt ℝ f x} \ D) = 0) :
    ∀ᵐ y ∂μ, y ∈ O → y ∈ D := by
  filter_upwards [ae_differentiableAt_of_strictlyContinuousAt f μ,compl_mem_ae_iff.mpr hnull]
    with y hd hn hy
  by_contra hnot
  exact hn ⟨⟨hy,hd (hf y hy)⟩,hnot⟩

theorem measure_compl_differentiability_approach_set_eq_zero (μ : Measure E)
    [Measure.IsAddHaarMeasure μ] {f : E → F} {O D : Set E}
    (hf : ∀ x ∈ O, StrictlyContinuousAt f x)
    (hnull : μ ({x ∈ O | DifferentiableAt ℝ f x} \ D) = 0) : μ (O \ D) = 0 := by
  apply compl_mem_ae_iff.mp
  filter_upwards [ae_mem_differentiability_set_of_null_complement μ hf hnull] with y hy
  exact fun ⟨hyO,hyD⟩ ↦ hyD (hy hyO)

/-- Removing any null subset of the differentiability points preserves
density. This is the approach-set refinement in **Theorems 9.61 and 9.62**. -/
theorem subset_closure_differentiability_set_of_null_complement (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → F} {O D : Set E} (hO : IsOpen O) (hf : ∀ x ∈ O, StrictlyContinuousAt f x)
    (hnull : μ ({x ∈ O | DifferentiableAt ℝ f x} \ D) = 0) : O ⊆ closure D := by
  have hDense := Measure.dense_of_ae (ae_mem_differentiability_set_of_null_complement μ hf hnull)
  intro x hx
  rw [_root_.mem_closure_iff]
  intro U hU hxU
  obtain ⟨y,hy,hyU,hyO⟩ := hDense.exists_mem_open (hU.inter hO) ⟨x,hxU,hx⟩
  exact ⟨y,hyU,hy hyO⟩

end NullSets

end RW
