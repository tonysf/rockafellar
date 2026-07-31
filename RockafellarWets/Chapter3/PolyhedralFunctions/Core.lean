/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Polyhedral Epigraphs

This file packages the function-side language for the polyhedral tail of
Chapter 3:
- functions with polyhedral epigraphs;
- functions with closed polyhedral epigraphs;
- the resulting lower-semicontinuity and convexity consequences;
- the project wrapper for proper convex piecewise-linear functions.
-/

import RockafellarWets.Chapter1.Semicontinuity
import RockafellarWets.Chapter3.GeneratedSets
import RockafellarWets.Chapter3.Pointwise
import RockafellarWets.Chapter3.PositiveHomogeneity

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function has a polyhedral epigraph if its real epigraph is polyhedral in
the Chapter 3 generated-set sense. -/
abbrev HasPolyhedralEpigraph (f : E → EReal) : Prop :=
  IsPolyhedral (epigraph f)

/-- A function has a closed polyhedral epigraph if its real epigraph is closed
polyhedral in the Chapter 3 generated-set sense. -/
abbrev HasClosedPolyhedralEpigraph (f : E → EReal) : Prop :=
  IsClosedPolyhedral (epigraph f)

/-- Project wrapper for proper convex piecewise-linear functions: properness
plus a closed polyhedral epigraph. -/
abbrev IsConvexPiecewiseLinear (f : E → EReal) : Prop :=
  IsProper f ∧ HasClosedPolyhedralEpigraph f

theorem HasPolyhedralEpigraph.convex {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    Convex ℝ (epigraph f) :=
  IsPolyhedral.convex hf

theorem HasPolyhedralEpigraph.exists_generators {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    ∃ s t : Finset (E × ℝ),
      epigraph f = extendedConvexHull (↑s : Set (E × ℝ)) (↑t : Set (E × ℝ)) :=
  hf

theorem HasPolyhedralEpigraph.exists_nonempty_generators_of_isProper {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      epigraph f = extendedConvexHull (↑s : Set (E × ℝ)) (↑t : Set (E × ℝ)) :=
  IsPolyhedral.exists_nonempty_generators_of_nonempty hf
    (epigraph_nonempty_of_isProper hproper)

/-- A polyhedral epigraph admits the finite coefficient description from
Exercise `3.54`: each epigraph point is a convex combination of finitely many
ordinary generators plus a conic combination of finitely many direction
generators, and conversely. -/
theorem HasPolyhedralEpigraph.exists_epigraph_generator_formula {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    ∃ s t : Finset (E × ℝ),
      ∀ {x : E} {a : ℝ},
        (x, a) ∈ epigraph f ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, a) := by
  rcases hf.exists_generators with ⟨s, t, hst⟩
  refine ⟨s, t, ?_⟩
  intro x a
  rw [hst]
  exact mem_extendedConvexHull_finset_iff

/-- A proper function with polyhedral epigraph can be described by finite
epigraph generators with a nonempty ordinary generator set. -/
theorem HasPolyhedralEpigraph.exists_nonempty_epigraph_generator_formula_of_isProper
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E} {a : ℝ},
        (x, a) ∈ epigraph f ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, a) := by
  rcases hf.exists_nonempty_generators_of_isProper hproper with ⟨s, t, hs, hst⟩
  refine ⟨s, t, hs, ?_⟩
  intro x a
  rw [hst]
  exact mem_extendedConvexHull_finset_iff

/-- A finite lower level set of a polyhedral-epigraph function admits the same
epigraph-generator coefficient formula evaluated at height `α`. -/
theorem HasPolyhedralEpigraph.exists_levelSet_generator_formula {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (α : ℝ) :
    ∃ s t : Finset (E × ℝ),
      ∀ {x : E},
        x ∈ levelSet f α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) := by
  rcases hf.exists_epigraph_generator_formula with ⟨s, t, hst⟩
  refine ⟨s, t, ?_⟩
  intro x
  simpa [levelSet, mem_epigraph_iff] using (hst (x := x) (a := α))

/-- A proper function with polyhedral epigraph admits the same finite lower
level-set coefficient formula with a nonempty ordinary generator set. -/
theorem HasPolyhedralEpigraph.exists_nonempty_levelSet_generator_formula_of_isProper
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) (α : ℝ) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet f α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) := by
  rcases hf.exists_nonempty_epigraph_generator_formula_of_isProper hproper with
    ⟨s, t, hs, hst⟩
  refine ⟨s, t, hs, ?_⟩
  intro x
  simpa [levelSet, mem_epigraph_iff] using (hst (x := x) (a := α))

/-- A nonempty finite lower level set of a polyhedral-epigraph function admits
the same coefficient formula with a nonempty ordinary generator set. -/
theorem HasPolyhedralEpigraph.exists_nonempty_levelSet_generator_formula_of_nonempty
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) {α : ℝ}
    (hlevel : (levelSet f α).Nonempty) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet f α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) := by
  rcases hf.exists_levelSet_generator_formula α with ⟨s, t, hst⟩
  rcases hlevel with ⟨x₀, hx₀⟩
  rcases (hst (x := x₀)).1 hx₀ with ⟨w, hw0, hw1, c, hcsub, hc0, hsum⟩
  have hs : s.Nonempty := by
    by_contra hs
    have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hs'] at hw1
  exact ⟨s, t, hs, fun {x} => hst (x := x)⟩

/-- Projecting the horizontal slice `epi f ∩ {a ≤ α}` onto the ambient space
recovers the level set `lev≤α f`. -/
theorem epigraphSlice_proj_eq_levelSet (f : E → EReal) (α : ℝ) :
    (LinearMap.fst ℝ E ℝ) '' (epigraph f ∩ (Set.univ ×ˢ Set.Iic α)) = levelSet f α := by
  ext x
  constructor
  · rintro ⟨⟨y, a⟩, ⟨hya, -, haα⟩, rfl⟩
    exact le_trans ((mem_epigraph_iff f y a).1 hya) (by simpa using haα)
  · intro hx
    refine ⟨(x, α), ?_, by simp [LinearMap.fst]⟩
    refine ⟨(mem_epigraph_iff f x α).2 hx, ?_⟩
    simp

/-- Embedding a level set at a fixed height identifies it with the exact
horizontal section of the epigraph at that height. -/
theorem levelSet_image_eq_epigraphSection (f : E → EReal) (α : ℝ) :
    (fun x : E => (x, α)) '' levelSet f α =
      epigraph f ∩ (Set.univ ×ˢ ({α} : Set ℝ)) := by
  ext p
  rcases p with ⟨x, a⟩
  constructor
  · rintro ⟨y, hy, hya⟩
    have hxy : y = x := by simpa using congrArg Prod.fst hya
    have haa : α = a := by simpa using congrArg Prod.snd hya
    subst x
    subst a
    refine ⟨(mem_epigraph_iff f y α).2 hy, ?_⟩
    simp
  · rintro ⟨hxa, ha⟩
    have ha' : a = α := by simpa using ha
    subst a
    refine ⟨x, ?_, rfl⟩
    simpa [levelSet] using (mem_epigraph_iff f x α).1 hxa

/-- If a level set is polyhedral, then its exact horizontal section inside the
epigraph is polyhedral as well. -/
theorem epigraphSection_isPolyhedral_of_levelSet
    {f : E → EReal} {α : ℝ} (hlevel : IsPolyhedral (levelSet f α)) :
    IsPolyhedral (epigraph f ∩ (Set.univ ×ˢ ({α} : Set ℝ))) := by
  rw [← levelSet_image_eq_epigraphSection f α]
  have hlin : IsPolyhedral ((LinearMap.inl ℝ E ℝ) '' levelSet f α) :=
    hlevel.linear_image (LinearMap.inl ℝ E ℝ)
  let τ : E × ℝ →ᵃ[ℝ] E × ℝ :=
    (AffineEquiv.constVAdd ℝ (E × ℝ) ((0 : E), α) : E × ℝ →ᵃ[ℝ] E × ℝ)
  have hshift :
      IsPolyhedral (τ '' ((LinearMap.inl ℝ E ℝ) '' levelSet f α)) := by
    exact hlin.affine_image τ
  simpa [τ, Set.image_image, LinearMap.inl, add_assoc, add_left_comm, add_comm] using hshift

/-- In finite dimension, a closed polyhedral level set gives a closed
polyhedral exact horizontal epigraph section. -/
theorem epigraphSection_isClosedPolyhedral_of_levelSet
    [FiniteDimensional ℝ E] {f : E → EReal} {α : ℝ}
    (hlevel : IsClosedPolyhedral (levelSet f α)) :
    IsClosedPolyhedral (epigraph f ∩ (Set.univ ×ˢ ({α} : Set ℝ))) := by
  rw [← levelSet_image_eq_epigraphSection f α]
  have hlin : IsClosedPolyhedral ((LinearMap.inl ℝ E ℝ) '' levelSet f α) :=
    hlevel.linear_image (LinearMap.inl ℝ E ℝ)
  have hshift :
      IsClosedPolyhedral
        ((fun p : E × ℝ => p + ((0 : E), α)) ''
          ((LinearMap.inl ℝ E ℝ) '' levelSet f α)) := by
    exact hlin.image_add_right ((0 : E), α)
  simpa [Set.image_image, LinearMap.inl, add_assoc, add_left_comm, add_comm] using hshift

/-- A polyhedral horizontal slice of an epigraph projects to a polyhedral level
set. This packages the linear-image step separately from proving the slice
itself is polyhedral. -/
theorem levelSet_isPolyhedral_of_epigraphSlice
    {f : E → EReal} {α : ℝ}
    (hslice : IsPolyhedral (epigraph f ∩ (Set.univ ×ˢ Set.Iic α))) :
    IsPolyhedral (levelSet f α) := by
  rw [← epigraphSlice_proj_eq_levelSet f α]
  exact hslice.linear_image (LinearMap.fst ℝ E ℝ)

/-- In finite dimension, a closed-polyhedral horizontal slice of an epigraph
projects to a closed polyhedral level set. -/
theorem levelSet_isClosedPolyhedral_of_epigraphSlice
    [FiniteDimensional ℝ E] {f : E → EReal} {α : ℝ}
    (hslice : IsClosedPolyhedral (epigraph f ∩ (Set.univ ×ˢ Set.Iic α))) :
    IsClosedPolyhedral (levelSet f α) := by
  rw [← epigraphSlice_proj_eq_levelSet f α]
  exact hslice.linear_image (LinearMap.fst ℝ E ℝ)

theorem HasPolyhedralEpigraph.closure_isClosedPolyhedral {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    IsClosedPolyhedral (closure (epigraph f)) :=
  IsPolyhedral.closure_isClosedPolyhedral hf

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    HasClosedPolyhedralEpigraph f :=
  IsPolyhedral.isClosedPolyhedral hf

theorem HasPolyhedralEpigraph.isClosed_epigraph
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    IsClosed (epigraph f) :=
  hf.hasClosedPolyhedralEpigraph.isClosed

theorem HasPolyhedralEpigraph.lowerSemicontinuous
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    LowerSemicontinuous f :=
  lowerSemicontinuous_of_isClosed_epigraph_ereal f hf.isClosed_epigraph

theorem hasPolyhedralEpigraph_iff_hasClosedPolyhedralEpigraph
    [FiniteDimensional ℝ E] {f : E → EReal} :
    HasPolyhedralEpigraph f ↔ HasClosedPolyhedralEpigraph f :=
  ⟨fun hf => hf.hasClosedPolyhedralEpigraph, fun hf => IsClosedPolyhedral.isPolyhedral hf⟩

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    IsConvexPiecewiseLinear f :=
  ⟨hproper, hf.hasClosedPolyhedralEpigraph⟩

/-- Finite-dimensional form of Exercise `3.54`: the project wrapper for convex
piecewise-linear functions is equivalently properness together with a
polyhedral epigraph. -/
theorem isConvexPiecewiseLinear_iff_isProper_and_hasPolyhedralEpigraph
    [FiniteDimensional ℝ E] {f : E → EReal} :
    IsConvexPiecewiseLinear f ↔ IsProper f ∧ HasPolyhedralEpigraph f := by
  constructor
  · intro hf
    exact ⟨hf.1, IsClosedPolyhedral.isPolyhedral hf.2⟩
  · rintro ⟨hproper, hpoly⟩
    exact hpoly.isConvexPiecewiseLinear_of_isProper hproper

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_iff_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    IsConvexPiecewiseLinear f ↔ IsProper f :=
  ⟨fun h => h.1, fun hproper => hf.isConvexPiecewiseLinear_of_isProper hproper⟩

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_of_isClosed {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hclosed : IsClosed (epigraph f)) :
    HasClosedPolyhedralEpigraph f :=
  IsPolyhedral.isClosedPolyhedral_of_isClosed hf hclosed

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (hlsc : LowerSemicontinuous f) :
    HasClosedPolyhedralEpigraph f :=
  hf.hasClosedPolyhedralEpigraph_of_isClosed (isClosed_epigraph_of_lsc_ereal f hlsc)

theorem IsPolyhedral.hasPolyhedralEpigraph_indicatorVA {C : Set E}
    (hC : IsPolyhedral C) :
    HasPolyhedralEpigraph (indicatorVA C) := by
  change IsPolyhedral (epigraph (indicatorVA C))
  rw [epigraph_indicatorVA]
  exact hC.prod IsPolyhedral.Ici_zero

theorem IsClosedPolyhedral.hasClosedPolyhedralEpigraph_indicatorVA {C : Set E}
    [FiniteDimensional ℝ E]
    (hC : IsClosedPolyhedral C) :
    HasClosedPolyhedralEpigraph (indicatorVA C) := by
  change IsClosedPolyhedral (epigraph (indicatorVA C))
  rw [epigraph_indicatorVA]
  exact hC.prod IsClosedPolyhedral.Ici_zero

/-- A nonempty polyhedral epigraph has a finitely generated horizon cone. -/
theorem HasPolyhedralEpigraph.horizonCone_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsFinitelyGeneratedCone (horizonCone (epigraph f)) :=
  IsPolyhedral.horizonCone_isFinitelyGeneratedCone hf hne

/-- A nonempty polyhedral epigraph has a polyhedral horizon cone. -/
theorem HasPolyhedralEpigraph.horizonCone_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsPolyhedral (horizonCone (epigraph f)) :=
  IsPolyhedral.horizonCone_isPolyhedral hf hne

/-- A nonempty polyhedral epigraph has a closed polyhedral horizon cone. -/
theorem HasPolyhedralEpigraph.horizonCone_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsClosedPolyhedral (horizonCone (epigraph f)) :=
  IsPolyhedral.horizonCone_isClosedPolyhedral hf hne

/-- A nonempty polyhedral epigraph has a finitely generated ray-space cone. -/
theorem HasPolyhedralEpigraph.raySpaceCone_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsFinitelyGeneratedCone (raySpaceCone (epigraph f) (horizonCone (epigraph f))) :=
  IsPolyhedral.isFinitelyGeneratedCone_raySpaceCone hf hne

/-- A nonempty polyhedral epigraph has a polyhedral ray-space cone. -/
theorem HasPolyhedralEpigraph.raySpaceCone_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsPolyhedral (raySpaceCone (epigraph f) (horizonCone (epigraph f))) :=
  IsPolyhedral.raySpaceCone_isPolyhedral hf hne

/-- A nonempty polyhedral epigraph has a closed polyhedral ray-space cone. -/
theorem HasPolyhedralEpigraph.raySpaceCone_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsClosedPolyhedral (raySpaceCone (epigraph f) (horizonCone (epigraph f))) :=
  IsPolyhedral.raySpaceCone_isClosedPolyhedral hf hne

/-- A nonempty polyhedral epigraph has finitely many horizon-cone generators. -/
theorem HasPolyhedralEpigraph.exists_horizonCone_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ t : Finset (E × ℝ),
      horizonCone (epigraph f) = conicHull (↑t : Set (E × ℝ)) :=
  IsPolyhedral.exists_horizon_conicHull_generators_of_nonempty hf hne

/-- Properness supplies epigraph nonemptiness for horizon-cone generators. -/
theorem HasPolyhedralEpigraph.exists_horizonCone_epigraph_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset (E × ℝ),
      horizonCone (epigraph f) = conicHull (↑t : Set (E × ℝ)) :=
  hf.exists_horizonCone_epigraph_generators
    (epigraph_nonempty_of_isProper hproper)

/-- A nonempty polyhedral epigraph has an explicit finite conic-coefficient
formula for its horizon cone. -/
theorem HasPolyhedralEpigraph.exists_horizonCone_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ horizonCone (epigraph f) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  IsPolyhedral.exists_horizonCone_generator_formula_of_nonempty hf hne

/-- Properness supplies epigraph nonemptiness for the horizon-cone coefficient
formula. -/
theorem HasPolyhedralEpigraph.exists_horizonCone_epigraph_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ horizonCone (epigraph f) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.exists_horizonCone_epigraph_generator_formula
    (epigraph_nonempty_of_isProper hproper)

/-- A nonempty polyhedral epigraph has finitely many ray-space cone
generators. -/
theorem HasPolyhedralEpigraph.exists_raySpaceCone_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph f) (horizonCone (epigraph f)) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  IsPolyhedral.exists_raySpaceCone_generators hf hne

/-- Properness supplies epigraph nonemptiness for ray-space cone generators. -/
theorem HasPolyhedralEpigraph.exists_raySpaceCone_epigraph_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph f) (horizonCone (epigraph f)) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  hf.exists_raySpaceCone_epigraph_generators
    (epigraph_nonempty_of_isProper hproper)

/-- A nonempty polyhedral epigraph has an explicit finite conic-coefficient
formula for its ray-space cone. -/
theorem HasPolyhedralEpigraph.exists_raySpaceCone_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph f) (horizonCone (epigraph f)) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  IsPolyhedral.exists_raySpaceCone_generator_formula_of_nonempty hf hne

/-- Properness supplies epigraph nonemptiness for the ray-space cone
coefficient formula. -/
theorem HasPolyhedralEpigraph.exists_raySpaceCone_epigraph_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph f) (horizonCone (epigraph f)) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.exists_raySpaceCone_epigraph_generator_formula
    (epigraph_nonempty_of_isProper hproper)

theorem HasClosedPolyhedralEpigraph.isClosed {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    IsClosed (epigraph f) :=
  IsClosedPolyhedral.isClosed hf

theorem HasClosedPolyhedralEpigraph.convex {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    Convex ℝ (epigraph f) :=
  IsClosedPolyhedral.convex hf

theorem HasClosedPolyhedralEpigraph.exists_generators {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    ∃ s t : Finset (E × ℝ),
      epigraph f =
        convexHull ℝ (↑s : Set (E × ℝ)) +
          closure (conicHull (↑t : Set (E × ℝ))) :=
  hf

theorem HasClosedPolyhedralEpigraph.exists_nonempty_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      epigraph f = extendedConvexHull (↑s : Set (E × ℝ)) (↑t : Set (E × ℝ)) := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact
    hpoly.exists_nonempty_generators_of_isProper
      hproper

/-- In finite dimension, closed polyhedral epigraphs inherit the same finite
coefficient description as polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.exists_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    ∃ s t : Finset (E × ℝ),
      ∀ {x : E} {a : ℝ},
        (x, a) ∈ epigraph f ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, a) := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact
    HasPolyhedralEpigraph.exists_epigraph_generator_formula
      (f := f)
      hpoly

/-- In finite dimension, a proper function with closed polyhedral epigraph
admits finite epigraph generators with a nonempty ordinary part. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_epigraph_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E} {a : ℝ},
        (x, a) ∈ epigraph f ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, a) := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact
    hpoly.exists_nonempty_epigraph_generator_formula_of_isProper
      hproper

/-- A closed polyhedral epigraph has a closed polyhedral horizon cone. -/
theorem HasClosedPolyhedralEpigraph.horizonCone_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsClosedPolyhedral (horizonCone (epigraph f)) :=
  IsClosedPolyhedral.horizonCone_isClosedPolyhedral hf hne

/-- A closed polyhedral epigraph has a finitely generated horizon cone. -/
theorem HasClosedPolyhedralEpigraph.horizonCone_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsFinitelyGeneratedCone (horizonCone (epigraph f)) :=
  IsClosedPolyhedral.horizonCone_isFinitelyGeneratedCone hf hne

/-- A nonempty closed polyhedral epigraph has a closed polyhedral ray-space
cone. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsClosedPolyhedral (raySpaceCone (epigraph f) (horizonCone (epigraph f))) :=
  IsClosedPolyhedral.raySpaceCone_isClosedPolyhedral hf hne

/-- A nonempty closed polyhedral epigraph has a finitely generated ray-space
cone. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsFinitelyGeneratedCone (raySpaceCone (epigraph f) (horizonCone (epigraph f))) :=
  IsClosedPolyhedral.isFinitelyGeneratedCone_raySpaceCone hf hne

/-- A closed polyhedral epigraph has a finitely generated horizon cone. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonCone_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ t : Finset (E × ℝ),
      horizonCone (epigraph f) = conicHull (↑t : Set (E × ℝ)) :=
  hf.horizonCone_epigraph_isFinitelyGeneratedCone hne

/-- Properness supplies the epigraph nonemptiness needed for finite horizon
cone generators. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonCone_epigraph_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset (E × ℝ),
      horizonCone (epigraph f) = conicHull (↑t : Set (E × ℝ)) :=
  hf.exists_horizonCone_epigraph_generators
    (epigraph_nonempty_of_isProper hproper)

/-- A closed polyhedral epigraph has an explicit finite conic-coefficient
formula for its horizon cone. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonCone_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ horizonCone (epigraph f) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  IsClosedPolyhedral.exists_horizonCone_generator_formula_of_nonempty hf hne

/-- Properness supplies the epigraph nonemptiness needed for the finite
coefficient formula of the epigraph horizon cone. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonCone_epigraph_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ horizonCone (epigraph f) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.exists_horizonCone_epigraph_generator_formula
    (epigraph_nonempty_of_isProper hproper)

/-- A nonempty closed polyhedral epigraph has a finitely generated ray-space
cone. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph f) (horizonCone (epigraph f)) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  IsClosedPolyhedral.exists_raySpaceCone_generators hf hne

/-- Properness supplies the epigraph nonemptiness needed for finite ray-space
cone generators. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_epigraph_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph f) (horizonCone (epigraph f)) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  hf.exists_raySpaceCone_epigraph_generators
    (epigraph_nonempty_of_isProper hproper)

/-- A nonempty closed polyhedral epigraph has an explicit finite
conic-coefficient formula for its ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph f) (horizonCone (epigraph f)) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  IsClosedPolyhedral.exists_raySpaceCone_generator_formula_of_nonempty hf hne

/-- Properness supplies the epigraph nonemptiness needed for the finite
coefficient formula of the epigraph ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_epigraph_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph f) (horizonCone (epigraph f)) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.exists_raySpaceCone_epigraph_generator_formula
    (epigraph_nonempty_of_isProper hproper)

/-- In finite dimension, closed polyhedral epigraphs inherit the same finite
lower-level-set coefficient formula as polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.exists_levelSet_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (α : ℝ) :
    ∃ s t : Finset (E × ℝ),
      ∀ {x : E},
        x ∈ levelSet f α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact hpoly.exists_levelSet_generator_formula α

/-- In finite dimension, a proper function with closed polyhedral epigraph
admits a finite lower-level-set coefficient formula with a nonempty ordinary
generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_levelSet_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) (α : ℝ) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet f α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact
    hpoly.exists_nonempty_levelSet_generator_formula_of_isProper
      hproper α

theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    LowerSemicontinuous f :=
  lowerSemicontinuous_of_isClosed_epigraph_ereal f hf.isClosed

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_iff_isProper
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) :
    IsConvexPiecewiseLinear f ↔ IsProper f :=
  ⟨fun h => h.1, fun hproper => ⟨hproper, hf⟩⟩

/-- In finite dimension, a nonempty finite lower level set of a
closed-polyhedral-epigraph function admits a coefficient formula with a
nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_levelSet_generator_formula_of_nonempty
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) {α : ℝ} (hlevel : (levelSet f α).Nonempty) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet f α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) := by
  rcases hf.exists_levelSet_generator_formula α with ⟨s, t, hst⟩
  rcases hlevel with ⟨x₀, hx₀⟩
  rcases (hst (x := x₀)).1 hx₀ with ⟨w, hw0, hw1, c, hcsub, hc0, hsum⟩
  have hs : s.Nonempty := by
    by_contra hs
    have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hs'] at hw1
  exact ⟨s, t, hs, fun {x} => hst (x := x)⟩

theorem HasPolyhedralEpigraph.effectiveDomain_isPolyhedral {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    IsPolyhedral (effectiveDomain f) := by
  rw [← epigraph_proj_eq_effectiveDomain f]
  exact hf.linear_image (LinearMap.fst ℝ E ℝ)

theorem HasClosedPolyhedralEpigraph.effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    IsClosedPolyhedral (effectiveDomain f) := by
  rw [← epigraph_proj_eq_effectiveDomain f]
  exact hf.linear_image (LinearMap.fst ℝ E ℝ)

/-- Projecting a polyhedral epigraph onto the ambient space yields an extended-
convex-hull description of the effective domain using the first coordinates of
the epigraph generators. -/
theorem HasPolyhedralEpigraph.exists_effectiveDomain_generators {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    ∃ s t : Finset E,
      effectiveDomain f = extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.effectiveDomain_isPolyhedral

/-- A proper function with polyhedral epigraph has an effective domain
described by nonempty ordinary generators together with finitely many
directions. -/
theorem HasPolyhedralEpigraph.exists_nonempty_effectiveDomain_generators_of_isProper
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f = extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  IsPolyhedral.exists_nonempty_generators_of_nonempty
    hf.effectiveDomain_isPolyhedral
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a polyhedral-epigraph function has
nonempty ordinary generators together with finitely many directions. -/
theorem HasPolyhedralEpigraph.exists_nonempty_effectiveDomain_generators_of_nonempty
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hdom : (effectiveDomain f).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f = extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  IsPolyhedral.exists_nonempty_generators_of_nonempty
    hf.effectiveDomain_isPolyhedral hdom

/-- The effective domain of a polyhedral-epigraph function admits the same
finite coefficient description as any extended convex hull. -/
theorem HasPolyhedralEpigraph.exists_effectiveDomain_generator_formula
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  IsPolyhedral.exists_generator_formula hf.effectiveDomain_isPolyhedral

/-- A proper polyhedral-epigraph function admits the effective-domain
coefficient formula with a nonempty ordinary generator set. -/
theorem HasPolyhedralEpigraph.exists_nonempty_effectiveDomain_generator_formula_of_isProper
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  IsPolyhedral.exists_nonempty_generator_formula_of_nonempty
    hf.effectiveDomain_isPolyhedral
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a polyhedral-epigraph function admits the
same coefficient formula with a nonempty ordinary generator set. -/
theorem HasPolyhedralEpigraph.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hdom : (effectiveDomain f).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  IsPolyhedral.exists_nonempty_generator_formula_of_nonempty
    hf.effectiveDomain_isPolyhedral hdom

/-- A nonempty effective domain of a polyhedral-epigraph function has a
finitely generated horizon cone. -/
theorem HasPolyhedralEpigraph.horizonCone_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsFinitelyGeneratedCone (horizonCone (effectiveDomain f)) :=
  IsPolyhedral.horizonCone_isFinitelyGeneratedCone
    hf.effectiveDomain_isPolyhedral hdom

/-- A nonempty effective domain of a polyhedral-epigraph function has a
polyhedral horizon cone. -/
theorem HasPolyhedralEpigraph.horizonCone_effectiveDomain_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsPolyhedral (horizonCone (effectiveDomain f)) :=
  IsPolyhedral.horizonCone_isPolyhedral hf.effectiveDomain_isPolyhedral hdom

/-- A nonempty effective domain of a polyhedral-epigraph function has a closed
polyhedral horizon cone. -/
theorem HasPolyhedralEpigraph.horizonCone_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsClosedPolyhedral (horizonCone (effectiveDomain f)) :=
  IsPolyhedral.horizonCone_isClosedPolyhedral hf.effectiveDomain_isPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for finite horizon-cone
generators. -/
theorem HasPolyhedralEpigraph.horizonCone_effectiveDomain_isFinitelyGeneratedCone_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    IsFinitelyGeneratedCone (horizonCone (effectiveDomain f)) :=
  hf.horizonCone_effectiveDomain_isFinitelyGeneratedCone
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a polyhedral-epigraph function has finite
horizon-cone generators. -/
theorem HasPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ t : Finset E,
      horizonCone (effectiveDomain f) = conicHull (↑t : Set E) :=
  IsPolyhedral.exists_horizon_conicHull_generators_of_nonempty
    hf.effectiveDomain_isPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for finite horizon-cone
generators. -/
theorem HasPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset E,
      horizonCone (effectiveDomain f) = conicHull (↑t : Set E) :=
  hf.exists_horizonCone_effectiveDomain_generators
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a polyhedral-epigraph function has an
explicit finite conic-coefficient formula for its horizon cone. -/
theorem HasPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ horizonCone (effectiveDomain f) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  IsPolyhedral.exists_horizonCone_generator_formula_of_nonempty
    hf.effectiveDomain_isPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for the finite
horizon-cone coefficient formula. -/
theorem HasPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ horizonCone (effectiveDomain f) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  hf.exists_horizonCone_effectiveDomain_generator_formula
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a polyhedral-epigraph function has a
finitely generated ray-space cone. -/
theorem HasPolyhedralEpigraph.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  IsPolyhedral.isFinitelyGeneratedCone_raySpaceCone
    hf.effectiveDomain_isPolyhedral hdom

/-- A nonempty effective domain of a polyhedral-epigraph function has a
polyhedral ray-space cone. -/
theorem HasPolyhedralEpigraph.raySpaceCone_effectiveDomain_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsPolyhedral
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  IsPolyhedral.raySpaceCone_isPolyhedral hf.effectiveDomain_isPolyhedral hdom

/-- A nonempty effective domain of a polyhedral-epigraph function has a closed
polyhedral ray-space cone. -/
theorem HasPolyhedralEpigraph.raySpaceCone_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  IsPolyhedral.raySpaceCone_isClosedPolyhedral hf.effectiveDomain_isPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for finite ray-space cone
generators. -/
theorem HasPolyhedralEpigraph.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  hf.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a polyhedral-epigraph function has finite
ray-space cone generators. -/
theorem HasPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) =
        conicHull (↑u : Set (E × ℝ)) :=
  IsPolyhedral.exists_raySpaceCone_generators hf.effectiveDomain_isPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for finite ray-space cone
generators. -/
theorem HasPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) =
        conicHull (↑u : Set (E × ℝ)) :=
  hf.exists_raySpaceCone_effectiveDomain_generators
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a polyhedral-epigraph function has an
explicit finite conic-coefficient formula for its ray-space cone. -/
theorem HasPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  IsPolyhedral.exists_raySpaceCone_generator_formula_of_nonempty
    hf.effectiveDomain_isPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for the finite ray-space
cone coefficient formula. -/
theorem HasPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.exists_raySpaceCone_effectiveDomain_generator_formula
    (by simpa [effectiveDomain] using hproper.1)

/-- In finite dimension, closed polyhedral epigraphs induce the same explicit
effective-domain generators as polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    ∃ s t : Finset E,
      effectiveDomain f = extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact hpoly.exists_effectiveDomain_generators

theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f = extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact hpoly.exists_nonempty_effectiveDomain_generators_of_isProper hproper

theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_generators_of_nonempty
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f = extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact hpoly.exists_nonempty_effectiveDomain_generators_of_nonempty hdom

/-- In finite dimension, closed polyhedral epigraphs inherit the same
effective-domain coefficient formula as polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact hpoly.exists_effectiveDomain_generator_formula

theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact
    hpoly.exists_nonempty_effectiveDomain_generator_formula_of_isProper
      hproper

theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hpoly : HasPolyhedralEpigraph f := IsClosedPolyhedral.isPolyhedral hf
  exact
    hpoly.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      hdom

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has a
finitely generated horizon cone. -/
theorem HasClosedPolyhedralEpigraph.horizonCone_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsFinitelyGeneratedCone (horizonCone (effectiveDomain f)) :=
  IsClosedPolyhedral.horizonCone_isFinitelyGeneratedCone
    hf.effectiveDomain_isClosedPolyhedral hdom

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has a
polyhedral horizon cone. -/
theorem HasClosedPolyhedralEpigraph.horizonCone_effectiveDomain_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsPolyhedral (horizonCone (effectiveDomain f)) :=
  (hf.horizonCone_effectiveDomain_isFinitelyGeneratedCone hdom).isPolyhedral

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has a
closed polyhedral horizon cone. -/
theorem HasClosedPolyhedralEpigraph.horizonCone_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsClosedPolyhedral (horizonCone (effectiveDomain f)) :=
  IsClosedPolyhedral.horizonCone_isClosedPolyhedral
    hf.effectiveDomain_isClosedPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for finite horizon-cone
generators. -/
theorem HasClosedPolyhedralEpigraph.horizonCone_effectiveDomain_isFinitelyGeneratedCone_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsFinitelyGeneratedCone (horizonCone (effectiveDomain f)) :=
  hf.horizonCone_effectiveDomain_isFinitelyGeneratedCone
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has
finite horizon-cone generators. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ t : Finset E,
      horizonCone (effectiveDomain f) = conicHull (↑t : Set E) :=
  IsClosedPolyhedral.exists_horizon_conicHull_generators
    hf.effectiveDomain_isClosedPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for finite horizon-cone
generators. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset E,
      horizonCone (effectiveDomain f) = conicHull (↑t : Set E) :=
  hf.exists_horizonCone_effectiveDomain_generators
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has an
explicit finite conic-coefficient formula for its horizon cone. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ horizonCone (effectiveDomain f) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  IsClosedPolyhedral.exists_horizonCone_generator_formula_of_nonempty
    hf.effectiveDomain_isClosedPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for the finite
horizon-cone coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ horizonCone (effectiveDomain f) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  hf.exists_horizonCone_effectiveDomain_generator_formula
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has a
finitely generated ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  IsClosedPolyhedral.isFinitelyGeneratedCone_raySpaceCone
    hf.effectiveDomain_isClosedPolyhedral hdom

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has a
polyhedral ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_effectiveDomain_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsPolyhedral
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  (hf.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone hdom).isPolyhedral

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has a
closed polyhedral ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  IsClosedPolyhedral.raySpaceCone_isClosedPolyhedral
    hf.effectiveDomain_isClosedPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for finite ray-space cone
generators. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  hf.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has
finite ray-space cone generators. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) =
        conicHull (↑u : Set (E × ℝ)) :=
  IsClosedPolyhedral.exists_raySpaceCone_generators
    hf.effectiveDomain_isClosedPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for finite ray-space cone
generators. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) =
        conicHull (↑u : Set (E × ℝ)) :=
  hf.exists_raySpaceCone_effectiveDomain_generators
    (by simpa [effectiveDomain] using hproper.1)

/-- A nonempty effective domain of a closed-polyhedral-epigraph function has an
explicit finite conic-coefficient formula for its ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hdom : (effectiveDomain f).Nonempty) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  IsClosedPolyhedral.exists_raySpaceCone_generator_formula_of_nonempty
    hf.effectiveDomain_isClosedPolyhedral hdom

/-- Properness supplies effective-domain nonemptiness for the finite ray-space
cone coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.exists_raySpaceCone_effectiveDomain_generator_formula
    (by simpa [effectiveDomain] using hproper.1)

theorem HasClosedPolyhedralEpigraph.hasPolyhedralEpigraph [FiniteDimensional ℝ E]
    {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    HasPolyhedralEpigraph f :=
  IsClosedPolyhedral.isPolyhedral hf

theorem hasPolyhedralEpigraph_zero [FiniteDimensional ℝ E] :
    HasPolyhedralEpigraph (fun _ : E => (0 : EReal)) := by
  have hzero : indicatorVA (Set.univ : Set E) = (fun _ : E => (0 : EReal)) := by
    funext x
    simp [indicatorVA]
  simpa [hzero] using
    (IsPolyhedral.univ (E := E)).hasPolyhedralEpigraph_indicatorVA

theorem hasClosedPolyhedralEpigraph_zero [FiniteDimensional ℝ E] :
    HasClosedPolyhedralEpigraph (fun _ : E => (0 : EReal)) := by
  have hzero : indicatorVA (Set.univ : Set E) = (fun _ : E => (0 : EReal)) := by
    funext x
    simp [indicatorVA]
  simpa [hzero] using
    (IsClosedPolyhedral.univ (E := E)).hasClosedPolyhedralEpigraph_indicatorVA

theorem isProper_zero : IsProper (fun _ : E => (0 : EReal)) := by
  constructor
  · exact ⟨0, by simp⟩
  · intro x
    simp

theorem lowerSemicontinuous_zero : LowerSemicontinuous (fun _ : E => (0 : EReal)) := by
  simpa using
    (continuous_const : Continuous (fun _ : E => ((0 : ℝ) : EReal))).lowerSemicontinuous

theorem isConvexPiecewiseLinear_zero [FiniteDimensional ℝ E] :
    IsConvexPiecewiseLinear (fun _ : E => (0 : EReal)) :=
  ⟨isProper_zero, hasClosedPolyhedralEpigraph_zero⟩

theorem IsClosedPolyhedral.isConvexPiecewiseLinear_indicatorVA
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsConvexPiecewiseLinear (indicatorVA C) := by
  refine ⟨(indicatorVA_isProper_iff C).2 hCne, ?_⟩
  exact hC.hasClosedPolyhedralEpigraph_indicatorVA

end RW
