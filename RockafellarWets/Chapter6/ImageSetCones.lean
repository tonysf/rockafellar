/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents and normals to image sets

Theorem 6.43, including the unions and intersections over the entire fiber,
the closed-cone assertion under a locally bounded inverse, and the convex
linear specialization. Convex images need not be locally closed, so the
coincidence of their two tangent cones is proved without that hypothesis.
-/

import RockafellarWets.Chapter6.TangentNormalPolarity
import Mathlib.Topology.MetricSpace.Sequences

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

section ConvexTangents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regular and ordinary tangent cones of a convex set coincide, even
when the set is not locally closed. -/
theorem regularTangentCone_eq_tangentCone_of_convex {C : Set E} {x : E}
    (hC : Convex ℝ C) (hx : x ∈ C) :
    regularTangentCone C x = tangentCone C x := by
  refine Subset.antisymm (regularTangentCone_subset_tangentCone hx) ?_
  rw [tangentCone_eq_closure_radialCone hC hx]
  apply closure_minimal _ (isClosed_regularTangentCone C x)
  rintro w ⟨r, hr, hxr⟩
  rw [mem_regularTangentCone_iff_forall_sequences hx]
  intro ts bs htpos ht0 hbC hbto
  let ys : ℕ → E := fun n ↦
    if ts n ≤ r then (1 - ts n / r) • bs n + (ts n / r) • (x + r • w)
    else bs n
  have hyC : ∀ n, ys n ∈ C := by
    intro n
    dsimp [ys]
    split_ifs with hn
    · apply hC (hbC n) hxr
      · exact sub_nonneg.2 ((div_le_one hr).2 hn)
      · exact div_nonneg (htpos n).le hr.le
      · ring
    · exact hbC n
  have hevent : ∀ᶠ n in atTop, ts n ≤ r := ht0.eventually_le_const hr
  have hq : Tendsto (fun n ↦ (ts n)⁻¹ • (ys n - bs n)) atTop (𝓝 w) := by
    have hlim : Tendsto (fun n ↦ r⁻¹ • (x + r • w - bs n)) atTop (𝓝 w) := by
      convert (tendsto_const_nhds.sub hbto).const_smul r⁻¹ using 1
      simp [smul_smul, hr.ne']
    apply hlim.congr'
    filter_upwards [hevent] with n hn
    dsimp [ys]
    rw [if_pos hn]
    have halg : (1 - ts n / r) • bs n + (ts n / r) • (x + r • w) - bs n =
        (ts n / r) • (x + r • w - bs n) := by module
    rw [halg, smul_smul]
    congr 1
    field_simp [(htpos n).ne']
  refine ⟨ys, hyC, ?_, hq⟩
  have h := (ht0.smul hq).add hbto
  simpa only [smul_smul, mul_inv_cancel₀ (htpos _).ne', one_smul,
    sub_add_cancel, zero_smul, zero_add] using h

end ConvexTangents

section Images

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- **Theorem 6.43**, first tangent inclusion, expressed over the full fiber. -/
theorem iUnion_image_tangentCone_subset {C : Set E} {F : E → G}
    (hF : Differentiable ℝ F) (u : G) :
    (⋃ x ∈ C ∩ F ⁻¹' {u}, fderiv ℝ F x '' tangentCone C x) ⊆
      tangentCone (F '' C) u := by
  intro z hz
  obtain ⟨x, hx, hz⟩ := mem_iUnion₂.1 hz
  have h := image_tangentCone_subset (hF x).hasFDerivAt C hz
  simpa only [mem_inter_iff, mem_preimage, mem_singleton_iff] using hx.2 ▸ h

/-- The adjoint derivative takes a regular normal to an image back to a
regular normal at every point of its fiber. -/
theorem adjoint_mem_regularNormalCone_of_mem_image {C : Set E} {F : E → G}
    {x : E} {A : E →L[ℝ] G} (hF : HasFDerivAt F A x) (hx : x ∈ C)
    {v : G} (hv : v ∈ regularNormalCone (F '' C) (F x)) :
    A.adjoint v ∈ regularNormalCone C x := by
  rw [regularNormalCone_eq_polarCone_tangentCone hx]
  intro w hw
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact inner_nonpos_of_mem_regularNormalCone hv
    (image_tangentCone_subset hF C ⟨w, hw, rfl⟩)

/-- **Theorem 6.43**, first normal inclusion, expressed over the full fiber. -/
theorem regularNormalCone_image_subset_iInter {C : Set E} {F : E → G}
    (hF : Differentiable ℝ F) (u : G) :
    regularNormalCone (F '' C) u ⊆
      ⋂ x ∈ C ∩ F ⁻¹' {u}, (fderiv ℝ F x).adjoint ⁻¹' regularNormalCone C x := by
  intro v hv
  apply mem_iInter₂.2
  intro x hx
  exact adjoint_mem_regularNormalCone_of_mem_image (hF x).hasFDerivAt hx.1
    (by have hxu : F x = u := hx.2; simpa only [hxu] using hv)

omit [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] in
/-- Local boundedness of the inverse relative to a closed set gives a
convergent subsequence of any lifts of a convergent image sequence. -/
theorem exists_tendsto_subseq_of_image_tendsto {C : Set E} {F : E → G} {u : G}
    (hC : IsClosed C) (hF : Continuous F)
    (hb : ∃ U ∈ 𝓝 u, Bornology.IsBounded (C ∩ F ⁻¹' U))
    {xs : ℕ → E} (hxs : ∀ n, xs n ∈ C)
    (hto : Tendsto (F ∘ xs) atTop (𝓝 u)) :
    ∃ x ∈ C ∩ F ⁻¹' {u}, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (xs ∘ φ) atTop (𝓝 x) := by
  obtain ⟨U, hU, hbU⟩ := hb
  have hevent : ∀ᶠ n in atTop, xs n ∈ C ∩ F ⁻¹' U := by
    filter_upwards [hto hU] with n hn
    exact ⟨hxs n, hn⟩
  obtain ⟨x, -, φ, hφ, hx⟩ := tendsto_subseq_of_frequently_bounded hbU hevent.frequently
  refine ⟨x, ⟨hC.mem_of_tendsto hx (Eventually.of_forall fun n ↦ hxs (φ n)), ?_⟩,
    φ, hφ, hx⟩
  exact tendsto_nhds_unique ((hF.tendsto x).comp hx) (hto.comp hφ.tendsto_atTop)

omit [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] in
/-- The image is locally closed whenever its inverse relative to the closed
source is locally bounded. -/
theorem isLocallyClosedAt_image_of_bounded_inverse {C : Set E} {F : E → G} {u : G}
    (hC : IsClosed C) (hF : Continuous F)
    (hb : ∃ U ∈ 𝓝 u, Bornology.IsBounded (C ∩ F ⁻¹' U)) :
    IsLocallyClosedAt (F '' C) u := by
  obtain ⟨U, hU, hbU⟩ := hb
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  let V := closedBall u (r / 2)
  have hVU : V ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hcompact : IsCompact (C ∩ F ⁻¹' V) :=
    Metric.isCompact_of_isClosed_isBounded
      (hC.inter (isClosed_closedBall.preimage hF))
      (hbU.subset (inter_subset_inter_right C (preimage_mono hVU)))
  refine ⟨V, closedBall_mem_nhds _ (by linarith), isClosed_closedBall, ?_⟩
  have heq : F '' C ∩ V = F '' (C ∩ F ⁻¹' V) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hy⟩
  rw [heq]
  exact (hcompact.image hF).isClosed

set_option maxHeartbeats 800000 in
-- Joint evaluation of the varying derivatives and adjoints needs a larger elaboration budget.
private theorem tendsto_image_adjoint {F : E → G} (hF : ContDiff ℝ 1 F)
    {xs : ℕ → E} {x : E} (hx : Tendsto xs atTop (𝓝 x))
    {vs : ℕ → G} {v : G} (hv : Tendsto vs atTop (𝓝 v)) :
    Tendsto (fun n ↦ (fderiv ℝ F (xs n)).adjoint (vs n)) atTop
      (𝓝 ((fderiv ℝ F x).adjoint v)) := by
  have hfd : Tendsto (fun n ↦ fderiv ℝ F (xs n)) atTop (𝓝 (fderiv ℝ F x)) :=
    Filter.Tendsto.comp (hF.contDiffAt.continuousAt_fderiv one_ne_zero) hx
  have hA : Tendsto (fun n ↦ (fderiv ℝ F (xs n)).adjoint) atTop
      (𝓝 ((fderiv ℝ F x).adjoint)) :=
    (ContinuousLinearMap.adjoint.continuous.tendsto (fderiv ℝ F x)).comp hfd
  exact ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := G) (F := E)).continuous.tendsto
    ((fderiv ℝ F x).adjoint, v)).comp (hA.prodMk_nhds hv)

/-- **Theorem 6.43**, limiting normals lie in the union of the adjoint
preimages over the fiber, under the locally bounded inverse hypothesis. -/
theorem normalCone_image_subset_iUnion {C : Set E} {F : E → G} {u : G}
    (hC : IsClosed C) (hF : ContDiff ℝ 1 F)
    (hb : ∃ U ∈ 𝓝 u, Bornology.IsBounded (C ∩ F ⁻¹' U)) :
    normalCone (F '' C) u ⊆
      ⋃ x ∈ C ∩ F ⁻¹' {u}, (fderiv ℝ F x).adjoint ⁻¹' normalCone C x := by
  rintro v ⟨_, us, vs, hus, huto, hvs, hvto⟩
  choose xs hxs hxF using hus
  have hFxto : Tendsto (F ∘ xs) atTop (𝓝 u) := by
    simpa only [Function.comp_def, hxF] using huto
  obtain ⟨x, hx, φ, hφ, hxto⟩ :=
    exists_tendsto_subseq_of_image_tendsto hC hF.continuous hb hxs hFxto
  apply mem_iUnion₂.2
  refine ⟨x, hx, mem_normalCone_of_forall hx.1 hxto (fun n ↦ ?_)
    (tendsto_image_adjoint hF hxto (hvto.comp hφ.tendsto_atTop))⟩
  exact adjoint_mem_regularNormalCone_of_mem_image
    ((hF.differentiable (by simp)) (xs (φ n))).hasFDerivAt (hxs (φ n))
    (by simpa only [hxF] using hvs (φ n))

/-- **Theorem 6.43**: the fiber union bounding the limiting normals is closed. -/
theorem isClosed_iUnion_adjoint_preimage_normalCone {C : Set E} {F : E → G} {u : G}
    (hC : IsClosed C) (hF : ContDiff ℝ 1 F)
    (hb : ∃ U ∈ 𝓝 u, Bornology.IsBounded (C ∩ F ⁻¹' U)) :
    IsClosed (⋃ x ∈ C ∩ F ⁻¹' {u},
      (fderiv ℝ F x).adjoint ⁻¹' normalCone C x) := by
  apply isSeqClosed_iff_isClosed.1
  intro vs v hvs hvto
  have hchoice := fun n ↦ mem_iUnion₂.1 (hvs n)
  choose xs hxs hvxs using hchoice
  obtain ⟨x, hx, φ, hφ, hxto⟩ := exists_tendsto_subseq_of_image_tendsto
    hC hF.continuous hb (fun n ↦ (hxs n).1)
    (by
      have heq : F ∘ xs = fun _ ↦ u := funext fun n ↦ (hxs n).2
      rw [heq]
      exact tendsto_const_nhds)
  exact mem_iUnion₂.2 ⟨x, hx, mem_normalCone_of_tendsto hx.1
    (fun n ↦ (hxs (φ n)).1) hxto (fun n ↦ hvxs (φ n))
    (tendsto_image_adjoint hF hxto (hvto.comp hφ.tendsto_atTop))⟩

/-- **Theorem 6.43**: the same fiber union is a cone. -/
theorem isCone_iUnion_adjoint_preimage_normalCone {C : Set E} {F : E → G} {u : G}
    (hu : u ∈ F '' C) :
    IsCone (⋃ x ∈ C ∩ F ⁻¹' {u},
      (fderiv ℝ F x).adjoint ⁻¹' normalCone C x) := by
  constructor
  · obtain ⟨x, hx, hxu⟩ := hu
    exact mem_iUnion₂.2 ⟨x, ⟨hx, hxu⟩, by simpa using (isCone_normalCone hx).1⟩
  · intro v hv c hc
    obtain ⟨x, hx, hv⟩ := mem_iUnion₂.1 hv
    exact mem_iUnion₂.2 ⟨x, hx, by
      simpa using (isCone_normalCone hx.1).2 hv hc⟩

/-- **Theorem 6.43**, regular tangents include the intersection of the
images of regular tangent cones over the fiber. -/
theorem iInter_image_regularTangentCone_subset {C : Set E} {F : E → G} {u : G}
    (hC : IsClosed C) (hF : ContDiff ℝ 1 F) (hu : u ∈ F '' C)
    (hb : ∃ U ∈ 𝓝 u, Bornology.IsBounded (C ∩ F ⁻¹' U)) :
    (⋂ x ∈ C ∩ F ⁻¹' {u}, fderiv ℝ F x '' regularTangentCone C x) ⊆
      regularTangentCone (F '' C) u := by
  rw [regularTangentCone_eq_polarCone_normalCone hu
    (isLocallyClosedAt_image_of_bounded_inverse hC hF.continuous hb)]
  intro z hz v hv
  obtain ⟨x, hx, hvx⟩ := mem_iUnion₂.1 (normalCone_image_subset_iUnion hC hF hb hv)
  obtain ⟨w, hw, rfl⟩ := mem_iInter₂.1 hz x hx
  rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_left]
  exact inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone
    hx.1 (RW.IsClosed.isLocallyClosedAt hC x) hvx hw

end Images

section LinearImages

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- Radial cones commute with linear images. -/
theorem radialCone_linear_image (A : E →L[ℝ] G) (C : Set E) (x : E) :
    radialCone (A '' C) (A x) = A '' radialCone C x := by
  ext z
  constructor
  · rintro ⟨r, hr, y, hy, hAy⟩
    refine ⟨r⁻¹ • (y - x), ⟨r, hr, ?_⟩, ?_⟩
    · simpa [smul_smul, hr.ne'] using hy
    · rw [map_smul, map_sub, hAy, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ hr.ne', one_smul]
  · rintro ⟨w, ⟨r, hr, hw⟩, rfl⟩
    exact ⟨r, hr, x + r • w, hw, by simp⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- **Theorem 6.43**, the tangent formula for a convex set under a linear map.
Neither the source nor its image is required to be closed. -/
theorem tangentCone_linear_image_of_convex (A : E →L[ℝ] G)
    {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    tangentCone (A '' C) (A x) = closure (A '' tangentCone C x) := by
  have hc : Convex ℝ (A '' C) := hC.linear_image A.toLinearMap
  rw [tangentCone_eq_closure_radialCone hc ⟨x, hx, rfl⟩,
    radialCone_linear_image, tangentCone_eq_closure_radialCone hC hx,
    closure_image_closure A.continuous]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- **Theorem 6.43**, the regular tangent formula for a convex linear image. -/
theorem regularTangentCone_linear_image_of_convex (A : E →L[ℝ] G)
    {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    regularTangentCone (A '' C) (A x) = closure (A '' tangentCone C x) := by
  have hc : Convex ℝ (A '' C) := hC.linear_image A.toLinearMap
  rw [regularTangentCone_eq_tangentCone_of_convex hc ⟨x, hx, rfl⟩,
    tangentCone_linear_image_of_convex A hC hx]

/-- **Theorem 6.43**, the normal formula for a convex linear image. -/
theorem normalCone_linear_image_of_convex (A : E →L[ℝ] G)
    {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    normalCone (A '' C) (A x) = A.adjoint ⁻¹' normalCone C x := by
  have hc : Convex ℝ (A '' C) := hC.linear_image A.toLinearMap
  rw [normalCone_eq_of_convex hc ⟨x, hx, rfl⟩,
    normalCone_eq_of_convex hC hx]
  ext v
  constructor
  · intro hv y hy
    rw [ContinuousLinearMap.adjoint_inner_left, map_sub]
    exact hv (A y) ⟨y, hy, rfl⟩
  · rintro hv _ ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearMap.adjoint_inner_left, map_sub] using hv y hy

/-- **Theorem 6.43**, the regular normal formula for a convex linear image. -/
theorem regularNormalCone_linear_image_of_convex (A : E →L[ℝ] G)
    {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    regularNormalCone (A '' C) (A x) = A.adjoint ⁻¹' normalCone C x := by
  have hc : Convex ℝ (A '' C) := hC.linear_image A.toLinearMap
  rw [← normalCone_eq_regularNormalCone_of_convex hc ⟨x, hx, rfl⟩,
    normalCone_linear_image_of_convex A hC hx]

end LinearImages

end

end RW
