/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Limits of Continuous Images

The elementary inclusions and the sequential no-escape form of Theorem 4.26.
The latter is the operational content of the book's cosmic-direction
condition: convergent image selections cannot have unbounded preimages.
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences
import RockafellarWets.Chapter3.NonlinearImages
import RockafellarWets.Chapter4.EventuallyBounded
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Bornology Filter Function Set Topology

namespace RW

section GeneralImageInclusions

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Theorem 4.26 (inner-limit inclusion).** -/
theorem image_innerSetLimit_subset_innerSetLimit_image
    {C : ℕ → Set E} {G : E → F} (hG : Continuous G) :
    G '' innerSetLimit C ⊆ innerSetLimit (fun n ↦ G '' C n) := by
  rintro _ ⟨x, hx, rfl⟩ V hV
  have hpre : G ⁻¹' V ∈ nhds x := hG.continuousAt hV
  exact (hx _ hpre).mono fun n ⟨y, hyC, hyV⟩ ↦
    ⟨G y, ⟨y, hyC, rfl⟩, hyV⟩

/-- **Theorem 4.26 (outer-limit inclusion).** -/
theorem image_outerSetLimit_subset_outerSetLimit_image
    {C : ℕ → Set E} {G : E → F} (hG : Continuous G) :
    G '' outerSetLimit C ⊆ outerSetLimit (fun n ↦ G '' C n) := by
  rintro _ ⟨x, hx, rfl⟩ V hV
  have hpre : G ⁻¹' V ∈ nhds x := hG.continuousAt hV
  exact (hx _ hpre).mono fun n ⟨y, hyC, hyV⟩ ↦
    ⟨G y, ⟨y, hyC, rfl⟩, hyV⟩

end GeneralImageInclusions

section FiniteDimensionalImages

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sequential no-escape condition behind the equality assertion of
Theorem 4.26.  It only asks for boundedness along selections whose images
converge. -/
def NoConvergentImageEscapeAlong (G : E → F) (C : ℕ → Set E) : Prop :=
  ∀ (φ : ℕ → ℕ) (x : ℕ → E) (y : F),
    StrictMono φ →
    (∀ n, x n ∈ C (φ n)) →
    Tendsto (G ∘ x) atTop (nhds y) →
    IsBounded (Set.range x)

/-- The cone `K` in Theorem 4.26: positive rays whose directions are cosmic
limits of sequences on which `G` stays bounded. -/
def boundedImageDirectionCone (G : E → F) : Set E :=
  {0} ∪ {w | ∃ (u : CosmicBoundary E) (x : ℕ → E) (r : ℝ),
    IsBounded (Set.range (G ∘ x)) ∧
      Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
        (nhds (cosmicDirection u)) ∧
      0 < r ∧ w = r • (u : E)}

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
@[simp]
theorem zero_mem_boundedImageDirectionCone (G : E → F) :
    (0 : E) ∈ boundedImageDirectionCone G :=
  Set.mem_union_left _ (Set.mem_singleton 0)

omit [NormedSpace ℝ F] in
/-- The book's cosmic no-escape condition implies the sequential condition
used by the image-limit backend. -/
theorem noConvergentImageEscapeAlong_of_boundedImageDirectionCone_inter
    {G : E → F} {C : ℕ → Set E}
    (hK : boundedImageDirectionCone G ∩ horizonOuterSetLimit C = {0}) :
    NoConvergentImageEscapeAlong G C := by
  intro φ x y hφ hxC hGxy
  by_contra hxBounded
  rcases exists_cosmicDirection_subsequence_of_not_isBounded hxBounded with
    ⟨u, ψ, hψ, hxDirection⟩
  have hGbounded : IsBounded (Set.range (G ∘ x ∘ ψ)) := by
    apply (Metric.isBounded_range_of_tendsto (G ∘ x) hGxy).subset
    rintro _ ⟨n, rfl⟩
    exact ⟨ψ n, rfl⟩
  have huK : (u : E) ∈ boundedImageDirectionCone G := by
    right
    exact ⟨u, x ∘ ψ, 1, hGbounded, hxDirection, zero_lt_one, by simp⟩
  have huOuterCosmic : cosmicDirection u ∈
      outerSetLimit (ordinaryCosmicSequence C) :=
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ ∘ ψ, fun n ↦ cosmicEmbed (x (ψ n)), hφ.comp hψ,
        fun n ↦ (cosmicEmbed_mem_cosmicSet_iff).2 (hxC (ψ n)),
        hxDirection⟩
  have huHorizon : (u : E) ∈ horizonOuterSetLimit C :=
    cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 huOuterCosmic
  have huZeroMem : (u : E) ∈ ({0} : Set E) := by
    rw [← hK]
    exact ⟨huK, huHorizon⟩
  have huZero : (u : E) = 0 := by simpa using huZeroMem
  have huNorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simp [huZero] at huNorm

omit [NormedSpace ℝ F] in
/-- Under the no-escape condition, the outer-limit image inclusion in 4.26
is an equality. -/
theorem outerSetLimit_image_eq_image_outerSetLimit
    {C : ℕ → Set E} {G : E → F} (hG : Continuous G)
    (hescape : NoConvergentImageEscapeAlong G C) :
    outerSetLimit (fun n ↦ G '' C n) = G '' outerSetLimit C := by
  apply Set.Subset.antisymm
  · intro y hy
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hy with
      ⟨φ, z, hφ, hzImage, hzy⟩
    choose x hxC hxG using hzImage
    have hGxy : Tendsto (G ∘ x) atTop (nhds y) := by
      have heq : G ∘ x = z := by
        funext n
        exact hxG n
      rw [heq]
      exact hzy
    have hxBounded : IsBounded (Set.range x) :=
      hescape φ x y hφ hxC hGxy
    rcases tendsto_subseq_of_bounded hxBounded
        (fun n ↦ Set.mem_range_self n) with
      ⟨xbar, -, ψ, hψ, hxbar⟩
    have hxOuter : xbar ∈ outerSetLimit C :=
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun n ↦ hxC (ψ n), hxbar⟩
    refine ⟨xbar, hxOuter, ?_⟩
    have htoGx : Tendsto (G ∘ x ∘ ψ) atTop (nhds (G xbar)) := by
      simpa only [Function.comp_def] using
        (hG.tendsto xbar).comp hxbar
    have htoy : Tendsto (G ∘ x ∘ ψ) atTop (nhds y) := by
      simpa only [Function.comp_def] using hGxy.comp hψ.tendsto_atTop
    exact tendsto_nhds_unique htoGx htoy
  · exact image_outerSetLimit_subset_outerSetLimit_image hG

omit [NormedSpace ℝ F] in
/-- The convergence consequence in Theorem 4.26. -/
theorem PKConverges.image_of_noConvergentImageEscapeAlong
    {C : ℕ → Set E} {D : Set E} {G : E → F}
    (hC : PKConverges C D) (hG : Continuous G)
    (hescape : NoConvergentImageEscapeAlong G C) :
    PKConverges (fun n ↦ G '' C n) (G '' D) := by
  have hinner : G '' D ⊆ innerSetLimit (fun n ↦ G '' C n) := by
    rw [← hC.inner_eq]
    exact image_innerSetLimit_subset_innerSetLimit_image hG
  have houter : outerSetLimit (fun n ↦ G '' C n) = G '' D := by
    rw [outerSetLimit_image_eq_image_outerSetLimit hG hescape,
      hC.outer_eq]
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans houter.subset) hinner
  · exact houter

omit [NormedSpace ℝ F] in
/-- **Theorem 4.26 (exact cosmic form).** Under the book's condition
`K ∩ limsup∞ Cₙ = {0}`, continuous images preserve the outer limit exactly. -/
theorem outerSetLimit_image_eq_image_outerSetLimit_of_cosmic
    {C : ℕ → Set E} {G : E → F} (hG : Continuous G)
    (hK : boundedImageDirectionCone G ∩ horizonOuterSetLimit C = {0}) :
    outerSetLimit (fun n ↦ G '' C n) = G '' outerSetLimit C :=
  outerSetLimit_image_eq_image_outerSetLimit hG
    (noConvergentImageEscapeAlong_of_boundedImageDirectionCone_inter hK)

omit [NormedSpace ℝ F] in
/-- **Theorem 4.26 (exact convergence form).** -/
theorem PKConverges.image_of_boundedImageDirectionCone_inter
    {C : ℕ → Set E} {D : Set E} {G : E → F}
    (hC : PKConverges C D) (hG : Continuous G)
    (hK : boundedImageDirectionCone G ∩ horizonOuterSetLimit C = {0}) :
    PKConverges (fun n ↦ G '' C n) (G '' D) :=
  hC.image_of_noConvergentImageEscapeAlong hG
    (noConvergentImageEscapeAlong_of_boundedImageDirectionCone_inter hK)

omit [NormedSpace ℝ F] in
/-- The eventually-bounded sufficient case in Theorem 4.26. -/
theorem PKConverges.image_of_eventuallyBounded
    {C : ℕ → Set E} {D : Set E} {G : E → F}
    (hC : PKConverges C D) (hG : Continuous G)
    (hbdd : EventuallyBounded C) :
    PKConverges (fun n ↦ G '' C n) (G '' D) := by
  apply hC.image_of_boundedImageDirectionCone_inter hG
  rw [(horizonOuterSetLimit_eq_singleton_zero_iff_eventuallyBounded C).2 hbdd]
  simp

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- A map which is sequentially coercive on the whole space satisfies the
no-escape condition for every set sequence. -/
theorem IsSequentiallyCoerciveOn.noConvergentImageEscapeAlong
    {G : E → F} (hG : IsSequentiallyCoerciveOn G Set.univ)
    (C : ℕ → Set E) : NoConvergentImageEscapeAlong G C := by
  intro φ x y hφ hxC hGxy
  exact hG x (fun _ ↦ Set.mem_univ _) <|
    Metric.isBounded_range_of_tendsto (G ∘ x) hGxy

omit [NormedSpace ℝ F] in
/-- The coercive-map sufficient case of Theorem 4.26. -/
theorem PKConverges.image_of_isSequentiallyCoerciveOn_univ
    {C : ℕ → Set E} {D : Set E} {G : E → F}
    (hC : PKConverges C D) (hcont : Continuous G)
    (hcoercive : IsSequentiallyCoerciveOn G Set.univ) :
    PKConverges (fun n ↦ G '' C n) (G '' D) :=
  hC.image_of_noConvergentImageEscapeAlong hcont
    (hcoercive.noConvergentImageEscapeAlong C)

end FiniteDimensionalImages

end RW
