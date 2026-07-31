/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Linear and Affine Preimages of Polyhedral Functions

This file packages surjective, injective, and equivalence-based linear and affine changes of variables.
-/

import RockafellarWets.Chapter3.PolyhedralOperations.Lattice

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section LinearSurjections

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private noncomputable def epigraphPrecomposeLinearSurjMap
    (L : F →ₗ[ℝ] E) (r : E →L[ℝ] F) :
    ((E × ℝ) × LinearMap.ker L) →ᵃ[ℝ] (F × ℝ) where
  toFun p := (r p.1.1 + p.2, p.1.2)
  linear :=
    let fstPair : ((E × ℝ) × LinearMap.ker L) →ₗ[ℝ] (E × ℝ) :=
      LinearMap.fst ℝ (E × ℝ) (LinearMap.ker L)
    let xPart : ((E × ℝ) × LinearMap.ker L) →ₗ[ℝ] E :=
      (LinearMap.fst ℝ E ℝ).comp fstPair
    let tPart : ((E × ℝ) × LinearMap.ker L) →ₗ[ℝ] ℝ :=
      (LinearMap.snd ℝ E ℝ).comp fstPair
    let kPart : ((E × ℝ) × LinearMap.ker L) →ₗ[ℝ] F :=
      (LinearMap.ker L).subtype.comp (LinearMap.snd ℝ (E × ℝ) (LinearMap.ker L))
    (r.toLinearMap.comp xPart + kPart).prod tPart
  map_vadd' p v := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]

@[simp] private theorem epigraphPrecomposeLinearSurjMap_apply
    (L : F →ₗ[ℝ] E) (r : E →L[ℝ] F) (p : (E × ℝ) × LinearMap.ker L) :
    epigraphPrecomposeLinearSurjMap (E := E) L r p = (r p.1.1 + p.2, p.1.2) :=
  rfl

private theorem image_epigraphPrecomposeLinearSurjMap_eq_epigraph_precompose
    {f : E → EReal} (L : F →ₗ[ℝ] E) (r : E →L[ℝ] F)
    (hr : (L.toContinuousLinearMap).comp r = ContinuousLinearMap.id ℝ E) :
    epigraphPrecomposeLinearSurjMap (E := E) L r ''
        (epigraph f ×ˢ (Set.univ : Set (LinearMap.ker L))) =
      epigraph (fun y : F => f (L y)) := by
  ext z
  rcases z with ⟨y, t⟩
  constructor
  · rintro ⟨⟨⟨x, s⟩, k⟩, hs, hp⟩
    rcases hs with ⟨hxepi, hk⟩
    have hy : r x + (k : F) = y := by
      simpa [epigraphPrecomposeLinearSurjMap_apply] using congrArg Prod.fst hp
    have ht : s = t := by
      simpa [epigraphPrecomposeLinearSurjMap_apply] using congrArg Prod.snd hp
    have hrx : L (r x) = x := by
      simpa using congrArg (fun g : E →L[ℝ] E => g x) hr
    have hkzero : L (k : F) = 0 := k.2
    have hLy : L y = x := by
      calc
        L y = L (r x + (k : F)) := by rw [← hy]
        _ = L (r x) + L (k : F) := by simp
        _ = x := by simp [hrx, hkzero]
    rw [mem_epigraph_iff] at hxepi ⊢
    simpa [ht, hLy] using hxepi
  · intro hz
    rw [mem_epigraph_iff] at hz
    let k : LinearMap.ker L :=
      ⟨y - r (L y), by
        have hry : L (r (L y)) = L y := by
          simpa using congrArg (fun g : E →L[ℝ] E => g (L y)) hr
        change L (y - r (L y)) = 0
        simp [hry]⟩
    refine ⟨((L y, t), k), ?_, ?_⟩
    · exact ⟨by simpa [mem_epigraph_iff] using hz, by simp⟩
    · ext
      · change r (L y) + (y - r (L y)) = y
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      · simp [epigraphPrecomposeLinearSurjMap_apply]

/-- Precomposition by a linear surjection preserves polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (L : F →ₗ[ℝ] E)
    (hL : LinearMap.range L = ⊤) :
    HasPolyhedralEpigraph (fun y : F => f (L y)) := by
  let Lc : F →L[ℝ] E := L.toContinuousLinearMap
  obtain ⟨r, hr⟩ := ContinuousLinearMap.exists_right_inverse_of_surjective Lc (by
    simpa using hL)
  change IsPolyhedral (epigraph (fun y : F => f (L y)))
  rw [← image_epigraphPrecomposeLinearSurjMap_eq_epigraph_precompose (E := E) (f := f) L r hr]
  exact (hf.prod (IsPolyhedral.univ (E := LinearMap.ker L))).affine_image
    (epigraphPrecomposeLinearSurjMap (E := E) L r)

/-- Precomposition by a linear surjection preserves closed polyhedral
epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearMap_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (L : F →ₗ[ℝ] E)
    (hL : LinearMap.range L = ⊤) :
    HasClosedPolyhedralEpigraph (fun y : F => f (L y)) := by
  let M : (F × ℝ) →ₗ[ℝ] (E × ℝ) :=
    (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
  have hpre : M ⁻¹' epigraph f = epigraph (fun y : F => f (L y)) := by
    ext z
    rcases z with ⟨y, t⟩
    simp [M, mem_epigraph_iff]
  have hM : LinearMap.range M = ⊤ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      rcases LinearMap.range_eq_top.mp hL z.1 with ⟨y, hy⟩
      refine ⟨(y, z.2), ?_⟩
      ext <;> simp [M, hy]
  change IsClosedPolyhedral (epigraph (fun y : F => f (L y)))
  rw [← hpre]
  exact hf.preimage_linearMap_of_surjective M hM

/-- Precomposition by a linear map preserves lower semicontinuity in finite
dimension. -/
theorem lowerSemicontinuous_precompose_linearMap
    [FiniteDimensional ℝ F]
    {f : E → EReal} (hlsc : LowerSemicontinuous f) (L : F →ₗ[ℝ] E) :
    LowerSemicontinuous (fun y : F => f (L y)) := by
  simpa [Function.comp] using hlsc.comp L.continuous_of_finiteDimensional

/-- Precomposition by a linear surjection preserves properness. -/
theorem isProper_precompose_linearMap_of_surjective
    {f : E → EReal} (hproper : IsProper f) (L : F →ₗ[ℝ] E)
    (hL : LinearMap.range L = ⊤) :
    IsProper (fun y : F => f (L y)) := by
  have hsurj : Function.Surjective L := LinearMap.range_eq_top.mp hL
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    rcases hsurj x with ⟨y, rfl⟩
    exact ⟨y, hx⟩
  · intro y
    exact hproper.2 (L y)

/-- Precomposition by a linear surjection preserves convex piecewise-linearity
in the project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) := by
  refine ⟨isProper_precompose_linearMap_of_surjective hproper L hL, ?_⟩
  have hpoly : HasPolyhedralEpigraph (fun y : F => f (L y)) :=
    hf.hasPolyhedralEpigraph_precompose_linearMap_of_surjective L hL
  exact hpoly.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    (lowerSemicontinuous_precompose_linearMap hlsc L)

/-- Precomposition by a linear surjection preserves convex
piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) := by
  have hpoly := IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph hf
  have hclosed :
      HasClosedPolyhedralEpigraph (fun y : F => f (L y)) :=
    hpoly.hasClosedPolyhedralEpigraph_precompose_linearMap_of_surjective L hL
  exact ⟨isProper_precompose_linearMap_of_surjective hf.isProper L hL, hclosed⟩

end LinearSurjections

section LinearInjections

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem range_epigraphPrecomposeLinearMap (L : F →ₗ[ℝ] E) :
    let M : (F × ℝ) →ₗ[ℝ] (E × ℝ) :=
      (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
    (LinearMap.range M : Set (E × ℝ)) =
      ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)) := by
  let M : (F × ℝ) →ₗ[ℝ] (E × ℝ) :=
    (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨⟨y, s⟩, hM⟩
    have hfst : L y = x := by
      simpa [M] using congrArg Prod.fst hM
    exact ⟨⟨y, hfst⟩, by simp⟩
  · rintro ⟨hx, -⟩
    rcases hx with ⟨y, rfl⟩
    exact ⟨(y, t), by simp [M]⟩

/-- Properness of a linear precomposition follows from properness of `f` and
the existence of one finite point of `f` in the range of the map. -/
theorem isProper_precompose_linearMap_of_nonempty_effectiveDomain_inter_range
    {f : E → EReal} (hproper : IsProper f) (L : F →ₗ[ℝ] E)
    (hdom : (effectiveDomain f ∩ (LinearMap.range L : Set E)).Nonempty) :
    IsProper (fun y : F => f (L y)) := by
  refine ⟨?_, ?_⟩
  · rcases hdom with ⟨x, hxdom, hxrange⟩
    rcases hxrange with ⟨y, rfl⟩
    exact ⟨y, hxdom⟩
  · intro y
    exact hproper.2 (L y)

/-- Precomposition by an injective linear map preserves polyhedral epigraphs,
provided the epigraph intersects the range cylinder in a polyhedral set. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap_of_injective_of_inter_range
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (L : F →ₗ[ℝ] E)
    (hL : Function.Injective L)
    (hinter :
      IsPolyhedral
        (epigraph f ∩ ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)))) :
    HasPolyhedralEpigraph (fun y : F => f (L y)) := by
  let M : (F × ℝ) →ₗ[ℝ] (E × ℝ) :=
    (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
  have hpre : M ⁻¹' epigraph f = epigraph (fun y : F => f (L y)) := by
    ext z
    rcases z with ⟨y, t⟩
    simp [M, mem_epigraph_iff]
  have hMinj : Function.Injective M := by
    intro p q hpq
    rcases p with ⟨y, s⟩
    rcases q with ⟨z, t⟩
    have hfst : L y = L z := by
      simpa [M] using congrArg Prod.fst hpq
    have hsnd : s = t := by
      simpa [M] using congrArg Prod.snd hpq
    exact by
      ext
      · exact hL hfst
      · exact hsnd
  have hRange : (LinearMap.range M : Set (E × ℝ)) =
      ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)) :=
    range_epigraphPrecomposeLinearMap (E := E) L
  have hinter' : IsPolyhedral (epigraph f ∩ (LinearMap.range M : Set (E × ℝ))) := by
    simpa [hRange] using hinter
  change IsPolyhedral (epigraph (fun y : F => f (L y)))
  rw [← hpre]
  exact
    IsPolyhedral.preimage_linearMap_of_injective_of_inter_range
      M hinter' (LinearMap.ker_eq_bot.mpr hMinj)

/-- Precomposition by an injective linear map preserves closed polyhedral
epigraphs, provided the epigraph intersects the range cylinder in a closed
polyhedral set. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearMap_of_injective_of_inter_range
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (L : F →ₗ[ℝ] E)
    (hL : Function.Injective L)
    (hinter :
      IsClosedPolyhedral
        (epigraph f ∩ ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)))) :
    HasClosedPolyhedralEpigraph (fun y : F => f (L y)) := by
  let M : (F × ℝ) →ₗ[ℝ] (E × ℝ) :=
    (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
  have hpre : M ⁻¹' epigraph f = epigraph (fun y : F => f (L y)) := by
    ext z
    rcases z with ⟨y, t⟩
    simp [M, mem_epigraph_iff]
  have hMinj : Function.Injective M := by
    intro p q hpq
    rcases p with ⟨y, s⟩
    rcases q with ⟨z, t⟩
    have hfst : L y = L z := by
      simpa [M] using congrArg Prod.fst hpq
    have hsnd : s = t := by
      simpa [M] using congrArg Prod.snd hpq
    exact by
      ext
      · exact hL hfst
      · exact hsnd
  have hRange : (LinearMap.range M : Set (E × ℝ)) =
      ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)) :=
    range_epigraphPrecomposeLinearMap (E := E) L
  have hinter' :
      IsClosedPolyhedral (epigraph f ∩ (LinearMap.range M : Set (E × ℝ))) := by
    simpa [hRange] using hinter
  change IsClosedPolyhedral (epigraph (fun y : F => f (L y)))
  rw [← hpre]
  exact
    IsClosedPolyhedral.preimage_linearMap_of_injective_of_inter_range
      M hinter' (LinearMap.ker_eq_bot.mpr hMinj)

/-- Precomposition by an injective linear map preserves convex
piecewise-linearity when the epigraph meets the range cylinder in a closed
polyhedral set and the effective domain meets the range. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_injective_of_inter_range
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : Function.Injective L)
    (hdom : (effectiveDomain f ∩ (LinearMap.range L : Set E)).Nonempty)
    (hinter :
      IsClosedPolyhedral
        (epigraph f ∩ ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)))) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) := by
  refine ⟨isProper_precompose_linearMap_of_nonempty_effectiveDomain_inter_range hproper L hdom, ?_⟩
  exact hf.hasClosedPolyhedralEpigraph_precompose_linearMap_of_injective_of_inter_range
    L hL hinter

/-- Top-level CPL version of injective linear precomposition under the same
range-intersection hypotheses. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearMap_of_injective_of_inter_range
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (L : F →ₗ[ℝ] E) (hL : Function.Injective L)
    (hdom : (effectiveDomain f ∩ (LinearMap.range L : Set E)).Nonempty)
    (hinter :
      IsClosedPolyhedral
        (epigraph f ∩ ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)))) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) := by
  exact
    HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_injective_of_inter_range
      hf.hasClosedPolyhedralEpigraph hf.isProper L hL hdom hinter

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_injective_of_inter_range_of_isProper
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : Function.Injective L)
    (hdom : (effectiveDomain f ∩ (LinearMap.range L : Set E)).Nonempty)
    (hinter :
      IsClosedPolyhedral
        (epigraph f ∩ ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)))) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) :=
  HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_injective_of_inter_range
    hf.hasClosedPolyhedralEpigraph hproper L hL hdom hinter

private def diagonalRangeCylinder : Set ((E × E) × ℝ) :=
  let Δ : E →ₗ[ℝ] E × E :=
    (LinearMap.id : E →ₗ[ℝ] E).prod (LinearMap.id : E →ₗ[ℝ] E)
  ((LinearMap.range Δ : Set (E × E)) ×ˢ (Set.univ : Set ℝ))

private theorem diagonalRangeCylinder_isClosedPolyhedral
    [FiniteDimensional ℝ E] :
    IsClosedPolyhedral (diagonalRangeCylinder (E := E)) := by
  let Δ : E →ₗ[ℝ] E × E :=
    (LinearMap.id : E →ₗ[ℝ] E).prod (LinearMap.id : E →ₗ[ℝ] E)
  have hrange : IsClosedPolyhedral (LinearMap.range Δ : Set (E × E)) :=
    IsClosedPolyhedral.range_linearMap (E := E × E) Δ
  simpa [diagonalRangeCylinder, Δ] using hrange.prod (IsClosedPolyhedral.univ (E := ℝ))

/-- Properness of two functions with a common finite-domain point implies
properness of their pointwise sum. -/
theorem isProper_add_of_nonempty_effectiveDomain_inter
    {f g : E → EReal}
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x : E => f x + g x) := by
  refine ⟨?_, ?_⟩
  · rcases hdom with ⟨x, hxF, hxG⟩
    refine ⟨x, ?_⟩
    exact EReal.add_lt_top (ne_of_lt <| (mem_effectiveDomain_iff f x).1 hxF)
      (ne_of_lt <| (mem_effectiveDomain_iff g x).1 hxG)
  · intro x
    exact (EReal.bot_lt_add_iff).2 ⟨hproperf.2 x, hproperg.2 x⟩

/-- For proper functions, the finite domain of the pointwise sum is exactly
the intersection of the finite domains. Properness rules out the
`⊤ + ⊥` ambiguity. -/
theorem effectiveDomain_add_eq_inter_of_isProper
    {f g : E → EReal}
    (hproperf : IsProper f) (hproperg : IsProper g) :
    effectiveDomain (fun x : E => f x + g x) =
      effectiveDomain f ∩ effectiveDomain g := by
  ext x
  simp only [effectiveDomain, mem_setOf_eq, mem_inter_iff]
  constructor
  · intro hx
    have hsum_ne_top : f x + g x ≠ ⊤ := lt_top_iff_ne_top.mp hx
    have hf_ne_bot : f x ≠ ⊥ := ne_of_gt (hproperf.2 x)
    have hg_ne_bot : g x ≠ ⊥ := ne_of_gt (hproperg.2 x)
    have hfinite :
        f x ≠ ⊤ ∧ g x ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top₂ hf_ne_bot hg_ne_bot).1 hsum_ne_top
    exact ⟨lt_top_iff_ne_top.mpr hfinite.1, lt_top_iff_ne_top.mpr hfinite.2⟩
  · intro hx
    exact EReal.add_lt_top (lt_top_iff_ne_top.mp hx.1) (lt_top_iff_ne_top.mp hx.2)

/-- If the epigraph of the separated sum meets the diagonal range cylinder in a
closed polyhedral set, then the pointwise sum has a closed polyhedral epigraph.
-/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    HasClosedPolyhedralEpigraph (fun x : E => f x + g x) := by
  let Δ : E →ₗ[ℝ] E × E :=
    (LinearMap.id : E →ₗ[ℝ] E).prod (LinearMap.id : E →ₗ[ℝ] E)
  have hΔinj : Function.Injective Δ := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  have hsep : HasClosedPolyhedralEpigraph (fun p : E × E => f p.1 + g p.2) :=
    hf.hasClosedPolyhedralEpigraph_separatedAdd hg hproperf hproperg
  simpa [diagonalRangeCylinder, Δ] using
    hsep.hasClosedPolyhedralEpigraph_precompose_linearMap_of_injective_of_inter_range
      Δ hΔinj hdiag

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
  hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdiag

/-- A diagonal-range closed-polyhedral theorem for the separated sum is enough
to conclude that the pointwise sum is convex piecewise-linear at the
closed-epigraph layer. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_add_of_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    IsConvexPiecewiseLinear (fun x : E => f x + g x) := by
  refine ⟨isProper_add_of_nonempty_effectiveDomain_inter hproperf hproperg hdom, ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
      hg hproperf hproperg hdiag

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_add_of_inter_range_diagonal_of_isProper
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    IsConvexPiecewiseLinear (fun x : E => f x + g x) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_add_of_inter_range_diagonal
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hdiag

/-- The direct diagonal-range criterion for pointwise addition also makes the
common finite domain closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
      hg hproperf hproperg hdiag
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.effectiveDomain_isClosedPolyhedral

theorem HasPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  let hfc : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  exact
    hfc.effectiveDomain_inter_isClosedPolyhedral_of_add_inter_range_diagonal
      hg.hasClosedPolyhedralEpigraph hproperf hproperg hdiag

/-- Under the direct diagonal-range criterion for pointwise addition, the
common finite domain admits finite ordinary and direction generators. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
      hg hproperf hproperg hdiag
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.exists_effectiveDomain_generators

theorem HasPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdiag

/-- Under the direct diagonal-range criterion for pointwise addition, a
nonempty common finite domain admits finite generators with a nonempty
ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
      hg hproperf hproperg hdiag
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using hdom)

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hdiag

/-- Under the direct diagonal-range criterion for pointwise addition, the
common finite domain inherits a finite coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
      hg hproperf hproperg hdiag
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.exists_effectiveDomain_generator_formula

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdiag

/-- Under the direct diagonal-range criterion for pointwise addition, the
common finite-domain coefficient formula can be chosen with a nonempty
ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
      hg hproperf hproperg hdiag
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using hdom)

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hdiag

/-- Ray-space finite-generation version of the diagonal-intersection criterion
for pointwise addition. This is the addition analogue of the ray-space
finite-generation criterion used for pointwise suprema. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    HasClosedPolyhedralEpigraph (fun x : E => f x + g x) := by
  have hsep : HasClosedPolyhedralEpigraph (fun p : E × E => f p.1 + g p.2) :=
    hf.hasClosedPolyhedralEpigraph_separatedAdd hg hproperf hproperg
  have hdiagClosed : IsClosedPolyhedral (diagonalRangeCylinder (E := E)) :=
    diagonalRangeCylinder_isClosedPolyhedral (E := E)
  have hsumProper : IsProper (fun x : E => f x + g x) :=
    isProper_add_of_nonempty_effectiveDomain_inter hproperf hproperg hdom
  have hdiagNonempty :
      (epigraph (fun p : E × E => f p.1 + g p.2) ∩
        diagonalRangeCylinder (E := E)).Nonempty := by
    rcases epigraph_nonempty_of_isProper hsumProper with ⟨p, hp⟩
    rcases p with ⟨x, t⟩
    refine ⟨((x, x), t), ?_, ?_⟩
    · simpa [mem_epigraph_iff] using hp
    · simp [diagonalRangeCylinder]
  have hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩
          diagonalRangeCylinder (E := E)) :=
    IsClosedPolyhedral.inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hsep hdiagClosed hdiagNonempty hRay
  exact
    hf.hasClosedPolyhedralEpigraph_add_of_inter_range_diagonal
      hg hproperf hproperg hdiag

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
  hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hRay

/-- Closed-epigraph-layer CPL consequence of the ray-space finite-generation
criterion for pointwise addition. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    IsConvexPiecewiseLinear (fun x : E => f x + g x) := by
  refine ⟨isProper_add_of_nonempty_effectiveDomain_inter hproperf hproperg hdom, ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
      hg hproperf hproperg hdom hRay

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter_of_isProper
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    IsConvexPiecewiseLinear (fun x : E => f x + g x) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hRay

/-- Under the diagonal ray-space criterion for pointwise addition, the common
finite domain is closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.effectiveDomain_isClosedPolyhedral

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  hf.hasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_add_diagonal_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hRay

/-- Under the diagonal ray-space criterion for pointwise addition, the common
finite domain admits finite ordinary and direction generators. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.exists_effectiveDomain_generators

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hRay

/-- Under the diagonal ray-space criterion for pointwise addition, the common
finite domain admits finite generators with a nonempty ordinary generator set.
-/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using hdom)

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hRay

/-- Under the diagonal ray-space criterion for pointwise addition, the common
finite domain inherits a finite coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.exists_effectiveDomain_generator_formula

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hRay

/-- Under the diagonal ray-space criterion for pointwise addition, the common
finite domain inherits a finite coefficient formula with a nonempty ordinary
generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsum :
      HasClosedPolyhedralEpigraph (fun x : E => f x + g x) :=
    hf.hasClosedPolyhedralEpigraph_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using
    hsum.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_add_eq_inter_of_isProper hproperf hproperg] using hdom)

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hproperf hproperg hdom hRay

/-- A diagonal-range closed-polyhedral theorem for the separated sum is enough
to conclude that the pointwise sum is convex piecewise-linear. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_add_of_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    IsConvexPiecewiseLinear (fun x : E => f x + g x) := by
  exact
    hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_add_of_inter_range_diagonal
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: the direct diagonal-range criterion for pointwise
addition makes the common finite domain closed polyhedral. -/
theorem IsConvexPiecewiseLinear.effectiveDomain_inter_isClosedPolyhedral_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_add_inter_range_diagonal
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdiag

/-- Top-level CPL version: the direct diagonal-range criterion for pointwise
addition gives finite generators for the common finite domain. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdiag

/-- Top-level CPL version: under the direct diagonal-range criterion for
pointwise addition, a nonempty common finite domain admits finite generators
with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_add_inter_range_diagonal
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: under the direct diagonal-range criterion for
pointwise addition, the common finite domain inherits a finite coefficient
formula. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdiag

/-- Top-level CPL version: under the direct diagonal-range criterion for
pointwise addition, the common finite-domain coefficient formula can be chosen
with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (epigraph (fun p : E × E => f p.1 + g p.2) ∩ diagonalRangeCylinder (E := E))) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_inter_range_diagonal
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version of the ray-space finite-generation criterion for
pointwise addition. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    IsConvexPiecewiseLinear (fun x : E => f x + g x) := by
  exact
    hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_add_of_nonempty_effectiveDomain_inter_of_diagonal_raySpaceCone_inter
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the diagonal ray-space criterion for pointwise
addition, the common finite domain is closed polyhedral. -/
theorem IsConvexPiecewiseLinear.effectiveDomain_inter_isClosedPolyhedral_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_add_diagonal_raySpaceCone_inter
      hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
      hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the diagonal ray-space criterion for pointwise
addition, the common finite domain admits finite generators. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the diagonal ray-space criterion for pointwise
addition, the common finite domain admits finite generators with a nonempty
ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_add_diagonal_raySpaceCone_inter
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the diagonal ray-space criterion for pointwise
addition, the common finite domain inherits a finite coefficient formula. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the diagonal ray-space criterion for pointwise
addition, the common finite domain inherits a nonempty finite coefficient
formula. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph (fun p : E × E => f p.1 + g p.2))
            (horizonCone (epigraph (fun p : E × E => f p.1 + g p.2))) ∩
          raySpaceCone (diagonalRangeCylinder (E := E))
            (horizonCone (diagonalRangeCylinder (E := E))))) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_add_diagonal_raySpaceCone_inter
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph
    hf.isProper hg.isProper hdom hRay

end LinearInjections

section AffineLinearInjections

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem image_add_right_inter_epigraph_shiftedRange
    {f : E → EReal} (L : F →ₗ[ℝ] E) (u : E) :
    (fun p : E × ℝ => p + ((-u), (0 : ℝ))) ''
        (epigraph f ∩
          (((fun x : E => x + u) '' (LinearMap.range L : Set E)) ×ˢ (Set.univ : Set ℝ))) =
      epigraph (fun x : E => f (x + u)) ∩
        ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ)) := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨⟨x', s⟩, ⟨hxepi, hxrange, hs⟩, hz⟩
    have hx : x' + -u = x := by
      simpa [add_assoc, add_left_comm, add_comm] using congrArg Prod.fst hz
    have hs' : s = t := by
      simpa using congrArg Prod.snd hz
    have hx' : x' = x + u := by
      have hx'' := congrArg (fun y : E => y + u) hx
      simpa [add_assoc, add_left_comm, add_comm] using hx''
    rcases hxrange with ⟨y, hy, hyx'⟩
    have hyx : y = x := by
      rw [hx'] at hyx'
      exact add_right_cancel hyx'
    subst x'
    subst s
    subst y
    refine ⟨?_, ?_⟩
    · simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hxepi
    · exact ⟨hy, by simp⟩
  · rintro ⟨hxepi, hxrange⟩
    refine ⟨(x + u, t), ?_, ?_⟩
    · refine ⟨?_, ?_, by simp⟩
      · simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hxepi
      · refine ⟨x, hxrange.1, ?_⟩
        simp [add_assoc, add_left_comm, add_comm]
    · ext <;> simp [add_assoc, add_left_comm, add_comm]

/-- Precomposition by an affine injective linear change `y ↦ L y + u`
preserves polyhedral epigraphs, provided the epigraph intersects the shifted
range cylinder in a polyhedral set. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap_add_of_injective_of_inter_shiftedRange
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (hL : Function.Injective L) (u : E)
    (hinter :
      IsPolyhedral
        (epigraph f ∩
          (((fun x : E => x + u) '' (LinearMap.range L : Set E)) ×ˢ (Set.univ : Set ℝ)))) :
    HasPolyhedralEpigraph (fun y : F => f (L y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  have hinter' :
      IsPolyhedral
        (epigraph (fun x : E => f (x + u)) ∩
          ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ))) := by
    let τ : (E × ℝ) →ᵃ[ℝ] (E × ℝ) :=
      { toFun := fun p => p + ((-u), (0 : ℝ))
        linear := LinearMap.id
        map_vadd' := by
          intro p v
          ext <;> simp [add_assoc, add_left_comm, add_comm] }
    rw [← image_add_right_inter_epigraph_shiftedRange (f := f) (L := L) (u := u)]
    exact hinter.affine_image τ
  simpa [Function.comp] using
    hg.hasPolyhedralEpigraph_precompose_linearMap_of_injective_of_inter_range
      L hL hinter'

/-- Precomposition by an affine injective linear change `y ↦ L y + u`
preserves closed polyhedral epigraphs, provided the epigraph intersects the
shifted range cylinder in a closed polyhedral set. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearMap_add_of_injective_of_inter_shiftedRange
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (hL : Function.Injective L) (u : E)
    (hinter :
      IsClosedPolyhedral
        (epigraph f ∩
          (((fun x : E => x + u) '' (LinearMap.range L : Set E)) ×ˢ (Set.univ : Set ℝ)))) :
    HasClosedPolyhedralEpigraph (fun y : F => f (L y + u)) := by
  have hg : HasClosedPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasClosedPolyhedralEpigraph_precompose_add u
  have hinter' :
      IsClosedPolyhedral
        (epigraph (fun x : E => f (x + u)) ∩
          ((LinearMap.range L : Set E) ×ˢ (Set.univ : Set ℝ))) := by
    rw [← image_add_right_inter_epigraph_shiftedRange (f := f) (L := L) (u := u)]
    exact hinter.image_add_right ((-u), (0 : ℝ))
  simpa [Function.comp] using
    hg.hasClosedPolyhedralEpigraph_precompose_linearMap_of_injective_of_inter_range
      L hL hinter'

/-- Precomposition by an affine injective linear change `y ↦ L y + u`
preserves convex piecewise-linearity when the epigraph meets the shifted range
cylinder in a closed polyhedral set and the effective domain meets that shifted
range. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_injective_of_inter_shiftedRange
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : Function.Injective L) (u : E)
    (hdom :
      (effectiveDomain f ∩
        ((fun x : E => x + u) '' (LinearMap.range L : Set E))).Nonempty)
    (hinter :
      IsClosedPolyhedral
        (epigraph f ∩
          (((fun x : E => x + u) '' (LinearMap.range L : Set E)) ×ˢ (Set.univ : Set ℝ)))) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) := by
  have hg_proper : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  have hdom' :
      (effectiveDomain (fun x : E => f (x + u)) ∩ (LinearMap.range L : Set E)).Nonempty := by
    rcases hdom with ⟨x, hxdom, hxrange⟩
    rcases hxrange with ⟨y, hy, rfl⟩
    refine ⟨y, ?_, hy⟩
    simpa using hxdom
  refine ⟨isProper_precompose_linearMap_of_nonempty_effectiveDomain_inter_range
    hg_proper L hdom', ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_precompose_linearMap_add_of_injective_of_inter_shiftedRange
      L hL u hinter

/-- Top-level CPL version of affine injective precomposition under the same
shifted-range intersection hypotheses. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearMap_add_of_injective_of_inter_shiftedRange
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (L : F →ₗ[ℝ] E) (hL : Function.Injective L) (u : E)
    (hdom :
      (effectiveDomain f ∩
        ((fun x : E => x + u) '' (LinearMap.range L : Set E))).Nonempty)
    (hinter :
      IsClosedPolyhedral
        (epigraph f ∩
          (((fun x : E => x + u) '' (LinearMap.range L : Set E)) ×ˢ (Set.univ : Set ℝ)))) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) := by
  exact HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_injective_of_inter_shiftedRange
    hf.hasClosedPolyhedralEpigraph hf.isProper L hL u hdom hinter

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_injective_of_inter_shiftedRange_of_isProper
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : Function.Injective L) (u : E)
    (hdom :
      (effectiveDomain f ∩
        ((fun x : E => x + u) '' (LinearMap.range L : Set E))).Nonempty)
    (hinter :
      IsClosedPolyhedral
        (epigraph f ∩
          (((fun x : E => x + u) '' (LinearMap.range L : Set E)) ×ˢ (Set.univ : Set ℝ)))) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) :=
  HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_injective_of_inter_shiftedRange
    hf.hasClosedPolyhedralEpigraph hproper L hL u hdom hinter

end AffineLinearInjections

section AffineDomainChanges

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precomposition by an affine change of variables `y ↦ e y + u` preserves
polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearEquiv_add
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (e : F ≃L[ℝ] E) (u : E) :
    HasPolyhedralEpigraph (fun y : F => f (e y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  simpa [Function.comp] using
    hg.hasPolyhedralEpigraph_precompose_linearEquiv e

/-- Precomposition by an affine change of variables `y ↦ e y + u` preserves
properness. -/
theorem isProper_precompose_linearEquiv_add {f : E → EReal}
    (hproper : IsProper f) (e : F ≃L[ℝ] E) (u : E) :
    IsProper (fun y : F => f (e y + u)) := by
  have hg : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  simpa [Function.comp] using isProper_precompose_linearEquiv hg e

/-- Precomposition by an affine change of variables `y ↦ e y + u` preserves
lower semicontinuity. -/
theorem lowerSemicontinuous_precompose_linearEquiv_add {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (e : F ≃L[ℝ] E) (u : E) :
    LowerSemicontinuous (fun y : F => f (e y + u)) := by
  have hg : LowerSemicontinuous (fun x : E => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  simpa [Function.comp] using lowerSemicontinuous_precompose_linearEquiv hg e

/-- Precomposition by an affine change of variables `y ↦ e y + u` preserves
convex piecewise-linearity in the project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv_add
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (e : F ≃L[ℝ] E) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  have hg_lsc : LowerSemicontinuous (fun x : E => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  have hg_proper : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  simpa [Function.comp] using
    hg.isConvexPiecewiseLinear_precompose_linearEquiv hg_lsc hg_proper e

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearEquiv_add
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (e : F ≃L[ℝ] E) (u : E) :
    HasClosedPolyhedralEpigraph (fun y : F => f (e y + u)) := by
  have hg : HasClosedPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasClosedPolyhedralEpigraph_precompose_add u
  simpa [Function.comp] using hg.hasClosedPolyhedralEpigraph_precompose_linearEquiv e

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv_add
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) (e : F ≃L[ℝ] E) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y + u)) := by
  exact ⟨isProper_precompose_linearEquiv_add hproper e u,
    hf.hasClosedPolyhedralEpigraph_precompose_linearEquiv_add e u⟩

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv_add_of_isProper
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f) (e : F ≃L[ℝ] E) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y + u)) :=
  HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv_add
    hf.hasClosedPolyhedralEpigraph hproper e u

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearEquiv_add
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) (e : F ≃L[ℝ] E) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y + u)) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv_add
    hf.isProper e u

end AffineDomainChanges

section AffineLinearSurjections

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precomposition by an affine surjective linear change `y ↦ L y + u`
preserves polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    HasPolyhedralEpigraph (fun y : F => f (L y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  simpa [Function.comp] using
    hg.hasPolyhedralEpigraph_precompose_linearMap_of_surjective L hL

/-- Precomposition by an affine surjective linear change `y ↦ L y + u`
preserves properness. -/
theorem isProper_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ F]
    {f : E → EReal} (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    IsProper (fun y : F => f (L y + u)) := by
  have hg : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  simpa [Function.comp] using
    isProper_precompose_linearMap_of_surjective hg L hL

/-- Properness of an affine linear precomposition `y ↦ L y + u` follows from
properness of `f` and the existence of one finite point of `f` on the shifted
range of `L`. -/
theorem isProper_precompose_linearMap_add_of_nonempty_effectiveDomain_inter_shiftedRange
    {f : E → EReal} (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (u : E)
    (hdom :
      (effectiveDomain f ∩
        ((fun x : E => x + u) '' (LinearMap.range L : Set E))).Nonempty) :
    IsProper (fun y : F => f (L y + u)) := by
  have hg : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  have hdom' :
      (effectiveDomain (fun x : E => f (x + u)) ∩ (LinearMap.range L : Set E)).Nonempty := by
    rcases hdom with ⟨x, hxdom, hxrange⟩
    rcases hxrange with ⟨y, hy, rfl⟩
    refine ⟨y, ?_, hy⟩
    simpa using hxdom
  simpa [Function.comp] using
    isProper_precompose_linearMap_of_nonempty_effectiveDomain_inter_range hg L hdom'

/-- Precomposition by an affine surjective linear change `y ↦ L y + u`
preserves lower semicontinuity. -/
theorem lowerSemicontinuous_precompose_linearMap_add
    [FiniteDimensional ℝ F]
    {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (L : F →ₗ[ℝ] E) (u : E) :
    LowerSemicontinuous (fun y : F => f (L y + u)) := by
  have hg : LowerSemicontinuous (fun x : E => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  simpa [Function.comp] using lowerSemicontinuous_precompose_linearMap hg L

/-- Precomposition by an affine surjective linear change `y ↦ L y + u`
preserves convex piecewise-linearity. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  have hg_lsc : LowerSemicontinuous (fun x : E => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  have hg_proper : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  simpa [Function.comp] using
    hg.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
      hg_lsc hg_proper L hL

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    HasClosedPolyhedralEpigraph (fun y : F => f (L y + u)) := by
  have hg : HasPolyhedralEpigraph (fun y : F => f (L y + u)) :=
    hf.hasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap_add_of_surjective L hL u
  exact hg.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    (lowerSemicontinuous_precompose_linearMap_add hf.lowerSemicontinuous L u)

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) := by
  exact ⟨isProper_precompose_linearMap_add_of_surjective hproper L hL u,
    hf.hasClosedPolyhedralEpigraph_precompose_linearMap_add_of_surjective L hL u⟩

set_option linter.style.longLine false in
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_surjective_of_isProper
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) :=
  HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_surjective
    hf.hasClosedPolyhedralEpigraph hproper L hL u

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_surjective
    hf.isProper L hL u

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_affineChange_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E)
    {a : ℝ} (ha : 0 < a) (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    HasClosedPolyhedralEpigraph (fun y : F => (a : EReal) * f (L y + u) + (l y + c : ℝ)) := by
  have hg : HasClosedPolyhedralEpigraph (fun y : F => f (L y + u)) :=
    hf.hasClosedPolyhedralEpigraph_precompose_linearMap_add_of_surjective L hL u
  have hh : HasClosedPolyhedralEpigraph (fun y : F => (a : EReal) * f (L y + u)) :=
    hg.hasClosedPolyhedralEpigraph_const_mul ha
  exact hh.hasClosedPolyhedralEpigraph_addAffine l c

/-- Affine surjective changes on the domain, positive vertical scaling, and
finite affine perturbations on the codomain preserve convex
piecewise-linearity. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E)
    {a : ℝ} (ha : 0 < a) (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (L y + u) + (l y + c : ℝ)) := by
  have hg : HasPolyhedralEpigraph (fun y : F => f (L y + u)) :=
    hf.hasPolyhedralEpigraph_precompose_linearMap_add_of_surjective L hL u
  have hg_lsc : LowerSemicontinuous (fun y : F => f (L y + u)) :=
    lowerSemicontinuous_precompose_linearMap_add hlsc L u
  have hg_proper : IsProper (fun y : F => f (L y + u)) :=
    isProper_precompose_linearMap_add_of_surjective hproper L hL u
  have hh : HasPolyhedralEpigraph (fun y : F => (a : EReal) * f (L y + u)) :=
    hg.hasPolyhedralEpigraph_const_mul ha
  have hh_lsc : LowerSemicontinuous (fun y : F => (a : EReal) * f (L y + u)) :=
    lowerSemicontinuous_const_mul hg_lsc ha
  have hh_proper : IsProper (fun y : F => (a : EReal) * f (L y + u)) :=
    isProper_const_mul hg_proper ha
  exact hh.isConvexPiecewiseLinear_addAffine hh_lsc hh_proper l c

end AffineLinearSurjections

section FullAffineChanges

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Affine changes on the domain, positive vertical scaling, and finite affine
perturbations on the codomain preserve convex piecewise-linearity. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (e : F ≃L[ℝ] E) (u : E) {a : ℝ} (ha : 0 < a)
    (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (e y + u) + (l y + c : ℝ)) := by
  have hg : HasPolyhedralEpigraph (fun y : F => f (e y + u)) :=
    hf.hasPolyhedralEpigraph_precompose_linearEquiv_add e u
  have hg_lsc : LowerSemicontinuous (fun y : F => f (e y + u)) :=
    lowerSemicontinuous_precompose_linearEquiv_add hlsc e u
  have hg_proper : IsProper (fun y : F => f (e y + u)) :=
    isProper_precompose_linearEquiv_add hproper e u
  have hh : HasPolyhedralEpigraph (fun y : F => (a : EReal) * f (e y + u)) :=
    hg.hasPolyhedralEpigraph_const_mul ha
  have hh_lsc : LowerSemicontinuous (fun y : F => (a : EReal) * f (e y + u)) :=
    lowerSemicontinuous_const_mul hg_lsc ha
  have hh_proper : IsProper (fun y : F => (a : EReal) * f (e y + u)) :=
    isProper_const_mul hg_proper ha
  exact hh.isConvexPiecewiseLinear_addAffine hh_lsc hh_proper l c

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_affineChange
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (e : F ≃L[ℝ] E) (u : E) {a : ℝ} (ha : 0 < a)
    (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    HasClosedPolyhedralEpigraph (fun y : F => (a : EReal) * f (e y + u) + (l y + c : ℝ)) := by
  have hg : HasClosedPolyhedralEpigraph (fun y : F => f (e y + u)) :=
    hf.hasClosedPolyhedralEpigraph_precompose_linearEquiv_add e u
  have hh : HasClosedPolyhedralEpigraph (fun y : F => (a : EReal) * f (e y + u)) :=
    hg.hasClosedPolyhedralEpigraph_const_mul ha
  exact hh.hasClosedPolyhedralEpigraph_addAffine l c

end FullAffineChanges

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_addAffine
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x : E => f x + (l x + c : ℝ)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_addAffine
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper l c

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_addAffine_of_isProper
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x : E => f x + (l x + c : ℝ)) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_addAffine hproper l c

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) (u : E) :
    IsConvexPiecewiseLinear (fun x : E => f (x + u)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper u

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add_of_isProper
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f) (u : E) :
    IsConvexPiecewiseLinear (fun x : E => f (x + u)) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add hproper u

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) {a : ℝ} (ha : 0 < a) :
    IsConvexPiecewiseLinear (fun x : E => (a : EReal) * f x) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper ha

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul_of_isProper
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f) {a : ℝ} (ha : 0 < a) :
    IsConvexPiecewiseLinear (fun x : E => (a : EReal) * f x) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul hproper ha

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) (e : F ≃L[ℝ] E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper e

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv_of_isProper
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f) (e : F ≃L[ℝ] E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y)) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv hproper e

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper L hL

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_surjective_of_isProper
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    hproper L hL

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E)
    {a : ℝ} (ha : 0 < a) (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (L y + u) + (l y + c : ℝ)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper L hL u ha l c

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective_of_isProper
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E)
    {a : ℝ} (ha : 0 < a) (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (L y + u) + (l y + c : ℝ)) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    hproper L hL u ha l c

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_affineChange_of_surjective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E)
    {a : ℝ} (ha : 0 < a) (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (L y + u) + (l y + c : ℝ)) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    hf.isProper L hL u ha l c

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f)
    (e : F ≃L[ℝ] E) (u : E) {a : ℝ} (ha : 0 < a)
    (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (e y + u) + (l y + c : ℝ)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper e u ha l c

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_isProper
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hproper : IsProper f)
    (e : F ≃L[ℝ] E) (u : E) {a : ℝ} (ha : 0 < a)
    (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (e y + u) + (l y + c : ℝ)) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    hproper e u ha l c

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_affineChange
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (e : F ≃L[ℝ] E) (u : E) {a : ℝ} (ha : 0 < a)
    (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (e y + u) + (l y + c : ℝ)) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    hf.isProper e u ha l c

end RW
