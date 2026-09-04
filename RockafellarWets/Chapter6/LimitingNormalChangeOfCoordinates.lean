/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Limiting-normal change of coordinates

This file proves the limiting-normal clause of Exercise 6.7,

  `N_{G⁻¹(D)}(x) = DG(x)* N_D(G(x))`,

for a map `G` that is `C¹` near `x` and whose derivative at `x` is surjective.

Smoothness is genuinely needed: limiting normals are limits of regular normals
at *moving* base points, so both `DG` and its adjoint have to vary continuously.
A single strict derivative at `x` would not suffice.

Only the multiplier space `F` is assumed finite dimensional.  That hypothesis is
used exactly once, to extract a strongly convergent subsequence of multipliers.
-/

import RockafellarWets.Chapter6.RegularNormalChangeOfCoordinates
import RockafellarWets.Chapter6.ContinuousRightInverses
import RockafellarWets.Chapter6.LocalSubmersion

open Filter Metric Set Topology

namespace RW

noncomputable section

section EvaluationContinuity

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Evaluation of continuous linear maps is jointly continuous, so a converging
family of operators applied to a converging family of vectors converges. -/
private theorem tendsto_apply_of_tendsto {ι : Type*} {l : Filter ι}
    {As : ι → E →L[ℝ] F} {A : E →L[ℝ] F} {ys : ι → E} {y : E}
    (hA : Tendsto As l (𝓝 A)) (hy : Tendsto ys l (𝓝 y)) :
    Tendsto (fun i ↦ As i (ys i)) l (𝓝 (A y)) :=
  ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.tendsto
    (A, y)).comp (hA.prodMk_nhds hy)

end EvaluationContinuity

section AdjointContinuity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Taking adjoints is a linear isometry, hence continuous. -/
private theorem tendsto_adjoint {ι : Type*} {l : Filter ι}
    {As : ι → E →L[ℝ] F} {A : E →L[ℝ] F} (hA : Tendsto As l (𝓝 A)) :
    Tendsto (fun i ↦ ContinuousLinearMap.adjoint (As i)) l
      (𝓝 (ContinuousLinearMap.adjoint A)) :=
  (ContinuousLinearMap.adjoint.continuous.tendsto A).comp hA

/-- The combination used at both ends of Exercise 6.7: adjoints of converging
operators, applied to converging vectors, converge to the adjoint of the limit
applied to the limit. -/
private theorem tendsto_adjoint_apply {ι : Type*} {l : Filter ι}
    {As : ι → E →L[ℝ] F} {A : E →L[ℝ] F} {vs : ι → F} {v : F}
    (hA : Tendsto As l (𝓝 A)) (hv : Tendsto vs l (𝓝 v)) :
    Tendsto (fun i ↦ ContinuousLinearMap.adjoint (As i) (vs i)) l
      (𝓝 (ContinuousLinearMap.adjoint A v)) :=
  tendsto_apply_of_tendsto (tendsto_adjoint hA) hv

end AdjointContinuity

section LimitingNormalChangeOfCoordinates

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The easy inclusion of Exercise 6.7 for limiting normals.  A normal to `D` at
`G x` is approximated by regular normals at points `yν → G x`; the local section
of the submersion lifts those to points `xν → x` with `G xν = yν`, where the
pointwise chain rule for regular normals applies. -/
theorem adjoint_image_normalCone_subset_preimage
    {G : E → F} {x : E}
    (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x))
    (D : Set F) :
    ContinuousLinearMap.adjoint (fderiv ℝ G x) '' normalCone D (G x) ⊆
      normalCone (G ⁻¹' D) x := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨hGx, ys, vs, -, hys, hvs, hvto⟩ := hv
  obtain ⟨R, s, -, -, -, hlift, himage⟩ :=
    RW.HasStrictFDerivAt.exists_local_lift_of_surjective
      (hG.hasStrictFDerivAt one_ne_zero) hsurj hys
  have hsmooth : ∀ᶠ n in atTop, ContDiffAt ℝ 1 G (s (ys n)) :=
    hlift.eventually (hG.eventually (by simp))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsmooth.and himage)
  have hxs : Tendsto (fun n ↦ s (ys (n + N))) atTop (𝓝 x) :=
    hlift.comp (tendsto_add_atTop_nat N)
  have hfd : Tendsto (fun n ↦ fderiv ℝ G (s (ys (n + N)))) atTop
      (𝓝 (fderiv ℝ G x)) :=
    Filter.Tendsto.comp (hG.continuousAt_fderiv one_ne_zero) hxs
  have hmem : ∀ n : ℕ,
      ContinuousLinearMap.adjoint (fderiv ℝ G (s (ys (n + N)))) (vs (n + N)) ∈
        regularNormalCone (G ⁻¹' D) (s (ys (n + N))) := by
    intro n
    obtain ⟨hsm, himg⟩ := hN (n + N) (Nat.le_add_left N n)
    have hfderiv : HasFDerivAt G (fderiv ℝ G (s (ys (n + N)))) (s (ys (n + N))) :=
      (hsm.hasStrictFDerivAt one_ne_zero).hasFDerivAt
    refine adjoint_image_regularNormalCone_subset_preimage hfderiv D
      ⟨vs (n + N), ?_, rfl⟩
    rw [himg]
    exact hvs (n + N)
  exact mem_normalCone_of_forall hGx hxs hmem
    (tendsto_adjoint_apply hfd (hvto.comp (tendsto_add_atTop_nat N)))

/-- The hard inclusion of Exercise 6.7 for limiting normals.  Regular normals to
`G ⁻¹' D` at points `xν → x` are pulled back from multipliers `vν` at `G xν`;
a continuously varying family of right inverses keeps the `vν` bounded, and
finite dimensionality of `F` extracts a convergent subsequence. -/
theorem normalCone_preimage_subset_adjoint_image
    {G : E → F} {x : E}
    (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x))
    (D : Set F) :
    normalCone (G ⁻¹' D) x ⊆
      ContinuousLinearMap.adjoint (fderiv ℝ G x) '' normalCone D (G x) := by
  intro w hw
  obtain ⟨hxD, xs, ws, -, hxs, hws, hwto⟩ := hw
  obtain ⟨chooseR, hcontR, -, hRev⟩ :=
    exists_continuousAt_rightInverse_of_surjective (fderiv ℝ G x) hsurj
  have hfd : Tendsto (fun n ↦ fderiv ℝ G (xs n)) atTop (𝓝 (fderiv ℝ G x)) :=
    Filter.Tendsto.comp (hG.continuousAt_fderiv one_ne_zero) hxs
  have hrightinv : ∀ᶠ n in atTop,
      (fderiv ℝ G (xs n)).comp (chooseR (fderiv ℝ G (xs n))) =
        ContinuousLinearMap.id ℝ F := hfd.eventually hRev
  have hsmooth : ∀ᶠ n in atTop, ContDiffAt ℝ 1 G (xs n) :=
    hxs.eventually (hG.eventually (by simp))
  have hRnorm : ∀ᶠ n in atTop,
      ‖chooseR (fderiv ℝ G (xs n))‖ ≤ ‖chooseR (fderiv ℝ G x)‖ + 1 :=
    (Filter.Tendsto.comp hcontR hfd).norm.eventually_le_const (lt_add_one _)
  have hwnorm : ∀ᶠ n in atTop, ‖ws n‖ ≤ ‖w‖ + 1 :=
    hwto.norm.eventually_le_const (lt_add_one _)
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (hrightinv.and (hsmooth.and (hRnorm.and hwnorm)))
  have hchoice : ∀ n : ℕ, ∃ u : F,
      u ∈ regularNormalCone D (G (xs (n + N))) ∧
        ContinuousLinearMap.adjoint (fderiv ℝ G (xs (n + N))) u = ws (n + N) ∧
        ‖u‖ ≤ (‖chooseR (fderiv ℝ G x)‖ + 1) * (‖w‖ + 1) := by
    intro n
    obtain ⟨hinv, hsm, hRn, hwn⟩ := hN (n + N) (Nat.le_add_left N n)
    have hsurjn : Function.Surjective (fderiv ℝ G (xs (n + N))) := by
      intro y
      refine ⟨chooseR (fderiv ℝ G (xs (n + N))) y, ?_⟩
      simpa using congrArg (fun T : F →L[ℝ] F ↦ T y) hinv
    have hmem : ws (n + N) ∈ regularNormalCone (G ⁻¹' D) (xs (n + N)) := hws (n + N)
    rw [regularNormalCone_preimage_of_surjective
      (hsm.hasStrictFDerivAt one_ne_zero) hsurjn D] at hmem
    obtain ⟨u, hu, huw⟩ := hmem
    refine ⟨u, hu, huw, ?_⟩
    have hbound := norm_le_rightInverse_norm_mul_adjoint
      (fderiv ℝ G (xs (n + N))) (chooseR (fderiv ℝ G (xs (n + N)))) hinv u
    rw [huw] at hbound
    exact hbound.trans (mul_le_mul hRn hwn (norm_nonneg _) (by positivity))
  choose us hus hadj hbdd using hchoice
  obtain ⟨v, -, φ, hφ, hvto⟩ :=
    (isCompact_closedBall (0 : F)
        ((‖chooseR (fderiv ℝ G x)‖ + 1) * (‖w‖ + 1))).tendsto_subseq
      (x := us) fun n ↦ by simpa [mem_closedBall_zero_iff] using hbdd n
  have hsub : Tendsto (fun n ↦ xs (φ n + N)) atTop (𝓝 x) :=
    (hxs.comp (tendsto_add_atTop_nat N)).comp hφ.tendsto_atTop
  have hGsub : Tendsto (fun n ↦ G (xs (φ n + N))) atTop (𝓝 (G x)) :=
    Filter.Tendsto.comp hG.continuousAt hsub
  refine ⟨v, mem_normalCone_of_forall hxD hGsub (fun n ↦ hus (φ n)) hvto, ?_⟩
  have hfdsub : Tendsto (fun n ↦ fderiv ℝ G (xs (φ n + N))) atTop
      (𝓝 (fderiv ℝ G x)) :=
    Filter.Tendsto.comp (hG.continuousAt_fderiv one_ne_zero) hsub
  exact tendsto_nhds_unique
    ((tendsto_adjoint_apply hfdsub hvto).congr fun n ↦ hadj (φ n))
    ((hwto.comp (tendsto_add_atTop_nat N)).comp hφ.tendsto_atTop)

/-- **Exercise 6.7**, the limiting-normal clause:

  `N_{G⁻¹(D)}(x̄) = DG(x̄)* N_D(G(x̄))`.

`G` is `C¹` near `x` and `DG(x)` is surjective, the infinite-dimensional form of
the book's full-rank hypothesis.  No hypothesis is placed on `D`; when
`G x ∉ D` both sides are empty. -/
theorem normalCone_preimage_of_surjective
    {G : E → F} {x : E}
    (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x))
    (D : Set F) :
    normalCone (G ⁻¹' D) x =
      ContinuousLinearMap.adjoint (fderiv ℝ G x) '' normalCone D (G x) :=
  Subset.antisymm (normalCone_preimage_subset_adjoint_image hG hsurj D)
    (adjoint_image_normalCone_subset_preimage hG hsurj D)

end LimitingNormalChangeOfCoordinates

end

end RW
