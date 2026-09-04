/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents and normals to smooth manifolds

Example 6.8 evaluates the elementary cones at a point `x̄` of a `d`-dimensional
smooth manifold `C ⊆ IRⁿ`: relative to an open neighborhood of `x̄` the set `C`
is the solution set of `G(x) = 0` for a `C¹` map `G : IRⁿ → IRᵐ` whose Jacobian
at `x̄` has full rank `m`, and then

  `T_C(x̄) = {w | ∇G(x̄)w = 0}`,   `N_C(x̄) = {∇G(x̄)*y | y ∈ IRᵐ}`,

two linear subspaces orthogonally complementary to each other, with `C` both
geometrically derivable and Clarke regular at `x̄`.

The local hypothesis is recorded as the germ equality `C =ᶠ[𝓝 x̄] G⁻¹(0)`, the
direct formalization of the book's "represented relative to an open
neighborhood `O ∈ N(x̄)`"; a neighborhood-form wrapper is supplied as well.
Full rank of the Jacobian is surjectivity of `∇G(x̄)`.

The three cone formulas are Exercise 6.7 with `D = {0}`, whose cones at `0` are
`{0}` on the tangent side and the whole space on the normal side.  Geometric
derivability is *not* one of them: it asks for genuine paths inside `C`, and
they are produced here by the implicit function theorem, which straightens the
zero set of `G` near `x̄` onto the kernel of `∇G(x̄)`.  A straight line in that
kernel coordinate then maps to a path in `C` with the prescribed initial
velocity.  Local closedness, the other half of Clarke regularity, is likewise
proved rather than assumed: it comes from the local zero-set representation
together with the continuity of `G` at the points near `x̄`.
-/

import RockafellarWets.Chapter6.LimitingNormalChangeOfCoordinates
import RockafellarWets.Chapter6.ElementaryCones
import Mathlib.Analysis.Calculus.Implicit

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

section AdjointRange

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Between finite-dimensional inner product spaces the range of an adjoint is
the orthogonal complement of the kernel.  In general the identity holds only up
to closure of the range, and finite dimensionality makes that closure
vacuous. -/
theorem range_adjoint_eq_orthogonal_ker (A : E →L[ℝ] F) :
    LinearMap.range (ContinuousLinearMap.adjoint A : F →ₗ[ℝ] E) =
      (LinearMap.ker (A : E →ₗ[ℝ] F))ᗮ := by
  rw [ContinuousLinearMap.orthogonal_ker A]
  exact (Submodule.closed_of_finiteDimensional
    (LinearMap.range (ContinuousLinearMap.adjoint A : F →ₗ[ℝ] E))
      ).submodule_topologicalClosure_eq.symm

/-- Set form of `range_adjoint_eq_orthogonal_ker`. -/
theorem range_adjoint_eq_orthogonal_ker_set (A : E →L[ℝ] F) :
    Set.range (ContinuousLinearMap.adjoint A) =
      ((LinearMap.ker (A : E →ₗ[ℝ] F))ᗮ : Set E) := by
  rw [← range_adjoint_eq_orthogonal_ker A, LinearMap.coe_range]
  rfl

end AdjointRange

section Germs

variable {E F : Type*} [TopologicalSpace E] [Zero F]

/-- The base point of a local zero-set representation is a zero of the map. -/
private theorem apply_eq_zero_of_eventuallyEq {G : E → F} {C : Set E} {x : E}
    (hx : x ∈ C) (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) : G x = 0 := by
  have h : x ∈ G ⁻¹' ({0} : Set F) := Eq.mp hlocal.eq_of_nhds hx
  simpa using h

/-- Sets that agree inside an open neighborhood of a point have the same germ
there. -/
private theorem eventuallyEq_of_inter_eq {C D O : Set E} {x : E} (hO : IsOpen O)
    (hxO : x ∈ O) (hCD : C ∩ O = D ∩ O) : C =ᶠ[nhds x] D := by
  filter_upwards [hO.mem_nhds hxO] with y hy
  refine propext ⟨fun hyC ↦ ?_, fun hyD ↦ ?_⟩
  · exact ((Set.ext_iff.1 hCD y).1 ⟨hyC, hy⟩).1
  · exact ((Set.ext_iff.1 hCD y).2 ⟨hyD, hy⟩).1

end Germs

section KernelChart

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The straightening step behind the geometric derivability of Example 6.8.
Where the derivative of `G` is surjective, the implicit function theorem
supplies a `C¹` parametrization of the level set of `G` through `x` by the
kernel of that derivative: `g` maps a neighborhood of the origin of
`ker ∇G(x)` into `G⁻¹(G x)`, sends `0` to `x`, and has the kernel inclusion as
its derivative there. -/
private theorem exists_local_kernel_chart {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hstrict : HasStrictFDerivAt G G' x)
    (hrange : LinearMap.range (G' : E →ₗ[ℝ] F) = ⊤) :
    ∃ g : LinearMap.ker (G' : E →ₗ[ℝ] F) → E, g 0 = x ∧
      HasFDerivAt g (LinearMap.ker (G' : E →ₗ[ℝ] F)).subtypeL 0 ∧
        ∀ᶠ y in nhds (0 : LinearMap.ker (G' : E →ₗ[ℝ] F)), G (g y) = G x := by
  refine ⟨hstrict.implicitFunction G G' hrange (G x),
    hstrict.implicitFunction_apply_image hrange,
    (hstrict.to_implicitFunction hrange).hasFDerivAt, ?_⟩
  have hpair : Tendsto (fun y : LinearMap.ker (G' : E →ₗ[ℝ] F) ↦ (G x, y)) (nhds 0)
      (nhds ((G x, 0) : F × LinearMap.ker (G' : E →ₗ[ℝ] F))) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  exact hpair.eventually (hstrict.map_implicitFunction_eq hrange)

/-- Every direction annihilated by a surjective strict derivative is a
*derivable* tangent direction to the level set through the base point.  The
path is the image under the chart of `exists_local_kernel_chart` of the
straight line `t ↦ tw` in the kernel coordinate; its right derivative at `0` is
the value of the kernel inclusion at `w`, namely `w` itself. -/
private theorem mem_derivableCone_preimage_of_mem_ker {G : E → F} {G' : E →L[ℝ] F}
    {x : E} (hstrict : HasStrictFDerivAt G G' x)
    (hrange : LinearMap.range (G' : E →ₗ[ℝ] F) = ⊤) {w : E} (hw : G' w = 0) :
    w ∈ derivableCone (G ⁻¹' ({G x} : Set F)) x := by
  obtain ⟨g, hg0, hgd, hgz⟩ := exists_local_kernel_chart hstrict hrange
  have hwk : w ∈ LinearMap.ker (G' : E →ₗ[ℝ] F) := LinearMap.mem_ker.2 hw
  have hline : HasDerivAt
      (fun t : ℝ ↦ t • (⟨w, hwk⟩ : LinearMap.ker (G' : E →ₗ[ℝ] F)))
      (⟨w, hwk⟩ : LinearMap.ker (G' : E →ₗ[ℝ] F)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const
      (⟨w, hwk⟩ : LinearMap.ker (G' : E →ₗ[ℝ] F))
  have hgd0 : HasFDerivAt g (LinearMap.ker (G' : E →ₗ[ℝ] F)).subtypeL
      ((0 : ℝ) • (⟨w, hwk⟩ : LinearMap.ker (G' : E →ₗ[ℝ] F))) := by
    rw [zero_smul]
    exact hgd
  have hpath : HasDerivAt
      (fun t : ℝ ↦ g (t • (⟨w, hwk⟩ : LinearMap.ker (G' : E →ₗ[ℝ] F)))) w 0 := by
    simpa [Function.comp_def] using hgd0.comp_hasDerivAt (0 : ℝ) hline
  have hsmul : Tendsto
      (fun t : ℝ ↦ t • (⟨w, hwk⟩ : LinearMap.ker (G' : E →ₗ[ℝ] F))) (nhds 0)
      (nhds 0) := by
    have hc : Continuous
        fun t : ℝ ↦ t • (⟨w, hwk⟩ : LinearMap.ker (G' : E →ₗ[ℝ] F)) :=
      continuous_id.smul continuous_const
    simpa using hc.tendsto (0 : ℝ)
  obtain ⟨δ, hδ, hδmem⟩ := Metric.eventually_nhds_iff.1 (hsmul.eventually hgz)
  refine ⟨δ / 2, by positivity,
    fun t ↦ g (t • (⟨w, hwk⟩ : LinearMap.ker (G' : E →ₗ[ℝ] F))),
    by simpa using hg0, ?_, ?_⟩
  · intro t ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2]
    simpa using hδmem hdist
  · have hle : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin (0 : ℝ) ({(0 : ℝ)}ᶜ) :=
      nhdsWithin_mono _ fun t (ht : (0 : ℝ) < t) ↦ ht.ne'
    refine ((hasDerivAt_iff_tendsto_slope.1 hpath).mono_left hle).congr fun t ↦ ?_
    simp [slope, hg0]

end KernelChart

section SmoothManifolds

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {G : E → F} {C : Set E} {x : E}

/-- **Example 6.8**, the tangent cone: `T_C(x̄) = {w | ∇G(x̄)w = 0}`.  This is
Exercise 6.7 for `D = {0}`, whose tangent cone at `0` is `{0}`. -/
theorem tangentCone_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    tangentCone C x = {w | fderiv ℝ G x w = 0} := by
  have hGx : G x = 0 := apply_eq_zero_of_eventuallyEq hx hlocal
  rw [tangentCone_congr_nhds hlocal,
    tangentCone_preimage_of_surjective (hG.hasStrictFDerivAt one_ne_zero) hsurj,
    hGx, tangentCone_singleton]
  ext w
  simp

/-- **Example 6.8**, the regular normal cone: `N̂_C(x̄) = range ∇G(x̄)*`.  This is
Exercise 6.7 for `D = {0}`, whose regular normal cone at `0` is everything. -/
theorem regularNormalCone_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    regularNormalCone C x =
      Set.range (ContinuousLinearMap.adjoint (fderiv ℝ G x)) := by
  have hGx : G x = 0 := apply_eq_zero_of_eventuallyEq hx hlocal
  rw [regularNormalCone_congr_nhds hlocal,
    regularNormalCone_preimage_of_surjective (hG.hasStrictFDerivAt one_ne_zero) hsurj,
    hGx, regularNormalCone_singleton, Set.image_univ]

/-- **Example 6.8**, the limiting normal cone: `N_C(x̄) = range ∇G(x̄)*`, the
same subspace as the regular one.  This is Exercise 6.7 for `D = {0}`. -/
theorem normalCone_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    normalCone C x = Set.range (ContinuousLinearMap.adjoint (fderiv ℝ G x)) := by
  have hGx : G x = 0 := apply_eq_zero_of_eventuallyEq hx hlocal
  rw [normalCone_congr_nhds hlocal, normalCone_preimage_of_surjective hG hsurj,
    hGx, normalCone_singleton, Set.image_univ]

/-- **Example 6.8**: a smooth manifold is geometrically derivable.  This does
not follow from the tangent cone formula; the tangent directions are exhibited
as velocities of paths inside `C` built from the local kernel chart. -/
theorem isGeometricallyDerivable_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    IsGeometricallyDerivable C x := by
  have hGx : G x = 0 := apply_eq_zero_of_eventuallyEq hx hlocal
  show tangentCone C x ⊆ derivableCone C x
  intro w hw
  rw [tangentCone_smoothManifold hx hlocal hG hsurj] at hw
  rw [derivableCone_congr_nhds hlocal, ← hGx]
  exact mem_derivableCone_preimage_of_mem_ker (hG.hasStrictFDerivAt one_ne_zero)
    (LinearMap.range_eq_top.2 hsurj) hw

/-- **Example 6.8**, the derivable cone: geometric derivability turns the
tangent cone formula into a formula for the derivable cone. -/
theorem derivableCone_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    derivableCone C x = {w | fderiv ℝ G x w = 0} := by
  rw [← tangentCone_eq_derivableCone hx
    (isGeometricallyDerivable_smoothManifold hx hlocal hG hsurj)]
  exact tangentCone_smoothManifold hx hlocal hG hsurj

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A set with a local zero-set representation by a map that is `C¹` near the
base point is locally closed there.  Only the continuity of `G` at the points
near `x̄` is used, so no closedness of `C` need be assumed. -/
theorem isLocallyClosedAt_smoothManifold
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x) :
    IsLocallyClosedAt C x := by
  obtain ⟨U, hU, hCU⟩ := hlocal.exists_mem
  have hcont : ∀ᶠ y in nhds x, ContinuousAt G y := by
    filter_upwards [hG.eventually (by simp)] with y hy using hy.continuousAt
  obtain ⟨W, hW, hWcont⟩ := hcont.exists_mem
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hW)
  have hsub : Metric.closedBall x (r / 2) ⊆ U ∩ W := by
    intro y hy
    refine hrsub ?_
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (by linarith)
  have heq : C ∩ Metric.closedBall x (r / 2)
      = Metric.closedBall x (r / 2) ∩ G ⁻¹' ({0} : Set F) := by
    ext y
    constructor
    · rintro ⟨hyC, hyB⟩
      exact ⟨hyB, Eq.mp (hCU (hsub hyB).1) hyC⟩
    · rintro ⟨hyB, hyG⟩
      exact ⟨Eq.mpr (hCU (hsub hyB).1) hyG, hyB⟩
  refine ⟨Metric.closedBall x (r / 2), Metric.closedBall_mem_nhds x (by positivity),
    Metric.isClosed_closedBall, ?_⟩
  rw [heq]
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_closedBall
    isClosed_singleton
  intro y hy
  exact (hWcont y (hsub hy).2).continuousWithinAt

/-- **Example 6.8**: a smooth manifold is Clarke regular.  Local closedness is
`isLocallyClosedAt_smoothManifold`, and the two normal cones agree because both
compute the range of the adjoint derivative. -/
theorem isClarkeRegularAt_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    IsClarkeRegularAt C x :=
  ⟨isLocallyClosedAt_smoothManifold hlocal hG, by
    rw [normalCone_smoothManifold hx hlocal hG hsurj,
      regularNormalCone_smoothManifold hx hlocal hG hsurj]⟩

/-- **Example 6.8**: the tangent cone is the linear subspace `ker ∇G(x̄)`. -/
theorem tangentCone_eq_ker_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    tangentCone C x = ((LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F) : Submodule ℝ E) :
      Set E) := by
  rw [tangentCone_smoothManifold hx hlocal hG hsurj]
  ext w
  simp

/-- **Example 6.8**: the normal cone is the orthogonal complement of the
tangent cone, `range ∇G(x̄)* = (ker ∇G(x̄))ᗮ`. -/
theorem normalCone_eq_orthogonal_ker_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    normalCone C x =
      (((LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F))ᗮ : Submodule ℝ E) : Set E) := by
  rw [normalCone_smoothManifold hx hlocal hG hsurj,
    range_adjoint_eq_orthogonal_ker_set]

/-- **Example 6.8**, the printed reading: the tangent and normal cones to `C`
at `x̄` are linear subspaces orthogonally complementary to each other. -/
theorem tangentCone_normalCone_orthogonally_complementary_smoothManifold (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    ∃ T N : Submodule ℝ E,
      tangentCone C x = (T : Set E) ∧ normalCone C x = (N : Set E) ∧
        N = Tᗮ ∧ T = Nᗮ ∧ IsCompl T N :=
  ⟨LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F),
    (LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F))ᗮ,
    tangentCone_eq_ker_smoothManifold hx hlocal hG hsurj,
    normalCone_eq_orthogonal_ker_smoothManifold hx hlocal hG hsurj, rfl,
    (Submodule.orthogonal_orthogonal _).symm,
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection⟩

omit [FiniteDimensional ℝ F] in
/-- The dimension count of Example 6.8: the tangent subspace has dimension
`d = n - m`, the full-rank hypothesis being what makes the count exact. -/
theorem finrank_tangentCone_smoothManifold
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    Module.finrank ℝ (LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F)) +
        Module.finrank ℝ F = Module.finrank ℝ E := by
  have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ G x : E →ₗ[ℝ] F)
  rw [LinearMap.range_eq_top.2 hsurj] at h
  simpa [add_comm] using h

/-- **Example 6.8** in full: at a point of a smooth manifold the set is Clarke
regular and geometrically derivable, and the elementary cones are given by the
kernel of the derivative and the range of its adjoint, two orthogonally
complementary linear subspaces. -/
theorem smoothManifold_tangents_and_normals (hx : x ∈ C)
    (hlocal : C =ᶠ[nhds x] G ⁻¹' ({0} : Set F)) (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    IsClarkeRegularAt C x ∧ IsGeometricallyDerivable C x ∧
      tangentCone C x = {w | fderiv ℝ G x w = 0} ∧
      derivableCone C x = {w | fderiv ℝ G x w = 0} ∧
      regularNormalCone C x = Set.range (ContinuousLinearMap.adjoint (fderiv ℝ G x)) ∧
      normalCone C x = Set.range (ContinuousLinearMap.adjoint (fderiv ℝ G x)) ∧
      tangentCone C x =
        ((LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F) : Submodule ℝ E) : Set E) ∧
      normalCone C x =
        (((LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F))ᗮ : Submodule ℝ E) : Set E) :=
  ⟨isClarkeRegularAt_smoothManifold hx hlocal hG hsurj,
    isGeometricallyDerivable_smoothManifold hx hlocal hG hsurj,
    tangentCone_smoothManifold hx hlocal hG hsurj,
    derivableCone_smoothManifold hx hlocal hG hsurj,
    regularNormalCone_smoothManifold hx hlocal hG hsurj,
    normalCone_smoothManifold hx hlocal hG hsurj,
    tangentCone_eq_ker_smoothManifold hx hlocal hG hsurj,
    normalCone_eq_orthogonal_ker_smoothManifold hx hlocal hG hsurj⟩

/-- **Example 6.8** in the book's neighborhood form: `C` is represented
relative to an open neighborhood `O` of `x̄` as the solution set of `G(x) = 0`
for a `C¹` map on `O` whose derivative at `x̄` has full rank. -/
theorem smoothManifold_tangents_and_normals_of_isOpen {O : Set E} (hx : x ∈ C)
    (hO : IsOpen O) (hxO : x ∈ O) (hG : ContDiffOn ℝ 1 G O)
    (hCO : C ∩ O = G ⁻¹' ({0} : Set F) ∩ O)
    (hsurj : Function.Surjective (fderiv ℝ G x)) :
    IsClarkeRegularAt C x ∧ IsGeometricallyDerivable C x ∧
      tangentCone C x = {w | fderiv ℝ G x w = 0} ∧
      derivableCone C x = {w | fderiv ℝ G x w = 0} ∧
      regularNormalCone C x = Set.range (ContinuousLinearMap.adjoint (fderiv ℝ G x)) ∧
      normalCone C x = Set.range (ContinuousLinearMap.adjoint (fderiv ℝ G x)) ∧
      tangentCone C x =
        ((LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F) : Submodule ℝ E) : Set E) ∧
      normalCone C x =
        (((LinearMap.ker (fderiv ℝ G x : E →ₗ[ℝ] F))ᗮ : Submodule ℝ E) : Set E) :=
  smoothManifold_tangents_and_normals hx (eventuallyEq_of_inter_eq hO hxO hCO)
    (hG.contDiffAt (hO.mem_nhds hxO)) hsurj

end SmoothManifolds

end

end RW
