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

/-- The horizon function of the indicator of a nonempty polyhedral set has a closed
polyhedral epigraph. -/
theorem IsPolyhedral.hasClosedPolyhedralEpigraph_horizonFunction_indicatorVA
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    HasClosedPolyhedralEpigraph (horizonFunction (indicatorVA C)) := by
  rw [horizonFunction_indicatorVA]
  exact (hC.horizonCone_isClosedPolyhedral hCne).hasClosedPolyhedralEpigraph_indicatorVA

/-- Closed-polyhedral sets give closed-polyhedral epigraphs for the horizon function of their
indicator. -/
theorem IsClosedPolyhedral.hasClosedPolyhedralEpigraph_horizonFunction_indicatorVA
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    HasClosedPolyhedralEpigraph (horizonFunction (indicatorVA C)) :=
  hC.isPolyhedral.hasClosedPolyhedralEpigraph_horizonFunction_indicatorVA hCne

/-- The horizon function of the indicator of a nonempty polyhedral set is convex
piecewise linear. -/
theorem IsPolyhedral.isConvexPiecewiseLinear_horizonFunction_indicatorVA
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsConvexPiecewiseLinear (horizonFunction (indicatorVA C)) := by
  rw [horizonFunction_indicatorVA]
  exact (hC.horizonCone_isClosedPolyhedral hCne).isConvexPiecewiseLinear_indicatorVA
    ⟨0, zero_mem_horizonCone C⟩

/-- Closed-polyhedral sets give convex piecewise-linear horizon functions for indicators. -/
theorem IsClosedPolyhedral.isConvexPiecewiseLinear_horizonFunction_indicatorVA
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsConvexPiecewiseLinear (horizonFunction (indicatorVA C)) :=
  hC.isPolyhedral.isConvexPiecewiseLinear_horizonFunction_indicatorVA hCne

/-- The horizon cone of the effective domain of an indicator horizon is unchanged. -/
theorem horizonCone_effectiveDomain_horizonFunction_indicatorVA_eq [FiniteDimensional ℝ E]
    (C : Set E) :
    horizonCone (effectiveDomain (horizonFunction (indicatorVA C))) = horizonCone C := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact horizonCone_eq_self_of_isClosed_isCone (isClosed_horizonCone C) (isCone_horizonCone C)

/-- Membership in the horizon cone of the effective domain of an indicator horizon. -/
theorem mem_horizonCone_effectiveDomain_horizonFunction_indicatorVA_iff
    [FiniteDimensional ℝ E] {C : Set E} {w : E} :
    w ∈ horizonCone (effectiveDomain (horizonFunction (indicatorVA C))) ↔
      w ∈ horizonCone C := by
  rw [horizonCone_effectiveDomain_horizonFunction_indicatorVA_eq C]

/-- The effective domain of the horizon function of an indicator of a nonempty polyhedral set is
the closed polyhedral horizon cone. -/
theorem IsPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (effectiveDomain (horizonFunction (indicatorVA C))) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact hC.horizonCone_isClosedPolyhedral hCne

/-- The effective domain of the horizon function of an indicator of a nonempty polyhedral set is
finitely generated as a cone. -/
theorem IsPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone (effectiveDomain (horizonFunction (indicatorVA C))) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact hC.horizonCone_isFinitelyGeneratedCone hCne

/-- The effective domain of the horizon function of an indicator of a nonempty closed polyhedral
set is closed polyhedral. -/
theorem IsClosedPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (effectiveDomain (horizonFunction (indicatorVA C))) :=
  hC.isPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isClosedPolyhedral hCne

/-- The effective domain of the horizon function of an indicator of a nonempty closed polyhedral
set is finitely generated as a cone. -/
theorem IsClosedPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone (effectiveDomain (horizonFunction (indicatorVA C))) :=
  hC.isPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone hCne

/-- The effective domain of the horizon function of an indicator of a nonempty polyhedral set is
polyhedral. -/
theorem IsPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (effectiveDomain (horizonFunction (indicatorVA C))) :=
  (hC.effectiveDomain_horizonFunction_indicatorVA_isClosedPolyhedral hCne).isPolyhedral

/-- The effective domain of the horizon function of an indicator of a nonempty closed polyhedral
set is polyhedral. -/
theorem IsClosedPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (effectiveDomain (horizonFunction (indicatorVA C))) :=
  hC.isPolyhedral.effectiveDomain_horizonFunction_indicatorVA_isPolyhedral hCne

/-- The effective domain of the horizon function of an indicator of a nonempty polyhedral set has
finite conic generators. -/
theorem IsPolyhedral.exists_effectiveDomain_horizonFunction_indicatorVA_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ t : Finset E,
      effectiveDomain (horizonFunction (indicatorVA C)) = conicHull (↑t : Set E) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact hC.exists_horizon_conicHull_generators_of_nonempty hCne

/-- The effective domain of the horizon function of an indicator of a nonempty closed polyhedral
set has finite conic generators. -/
theorem IsClosedPolyhedral.exists_effectiveDomain_horizonFunction_indicatorVA_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ t : Finset E,
      effectiveDomain (horizonFunction (indicatorVA C)) = conicHull (↑t : Set E) :=
  hC.isPolyhedral.exists_effectiveDomain_horizonFunction_indicatorVA_generators hCne

/-- The effective domain of the horizon function of an indicator of a nonempty polyhedral set
admits a finite conic-coefficient formula. -/
theorem IsPolyhedral.exists_effectiveDomain_horizonFunction_indicatorVA_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ effectiveDomain (horizonFunction (indicatorVA C)) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact hC.exists_horizonCone_generator_formula_of_nonempty hCne

/-- The effective domain of the horizon function of an indicator of a nonempty closed polyhedral
set admits a finite conic-coefficient formula. -/
theorem IsClosedPolyhedral.exists_effectiveDomain_horizonFunction_indicatorVA_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ effectiveDomain (horizonFunction (indicatorVA C)) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  hC.isPolyhedral.exists_effectiveDomain_horizonFunction_indicatorVA_generator_formula hCne

/-- The ordinary-ray cone of the effective domain of an indicator horizon is the horizon cone
times the negative real ray. -/
theorem ordinaryRayCone_effectiveDomain_horizonFunction_indicatorVA_eq
    [FiniteDimensional ℝ E] (C : Set E) :
    ordinaryRayCone (effectiveDomain (horizonFunction (indicatorVA C))) =
      horizonCone C ×ˢ Set.Iio (0 : ℝ) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact ordinaryRayCone_eq_prod_Iio_zero_of_isCone (isCone_horizonCone C)

/-- Membership in the ordinary-ray cone of the effective domain of an indicator horizon. -/
theorem mem_ordinaryRayCone_effectiveDomain_horizonFunction_indicatorVA_iff
    [FiniteDimensional ℝ E] {C : Set E} {p : E × ℝ} :
    p ∈ ordinaryRayCone (effectiveDomain (horizonFunction (indicatorVA C))) ↔
      p.1 ∈ horizonCone C ∧ p.2 < 0 := by
  rw [ordinaryRayCone_effectiveDomain_horizonFunction_indicatorVA_eq C]
  rfl

/-- The ray-space cone of the effective domain of an indicator horizon is the horizon cone
times the nonpositive real ray. -/
theorem raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_eq
    [FiniteDimensional ℝ E] (C : Set E) :
    raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
        (effectiveDomain (horizonFunction (indicatorVA C))) =
      horizonCone C ×ˢ Set.Iic (0 : ℝ) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact raySpaceCone_eq_prod_Iic_zero_of_isCone (isCone_horizonCone C)

/-- Membership in the ray-space cone of the effective domain of an indicator horizon. -/
theorem mem_raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_iff
    [FiniteDimensional ℝ E] {C : Set E} {p : E × ℝ} :
    p ∈ raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
          (effectiveDomain (horizonFunction (indicatorVA C))) ↔
      p.1 ∈ horizonCone C ∧ p.2 ≤ 0 := by
  rw [raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_eq C]
  rfl

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty
polyhedral set is finitely generated. -/
theorem
IsPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
        (effectiveDomain (horizonFunction (indicatorVA C)))) :=
  (hC.effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).raySpaceCone_of_isCone
    (isCone_effectiveDomain_horizonFunction_indicatorVA C)

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty
polyhedral set is polyhedral. -/
theorem IsPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral
      (raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
        (effectiveDomain (horizonFunction (indicatorVA C)))) :=
  (hC.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).isPolyhedral

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty
polyhedral set is closed polyhedral. -/
theorem
IsPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
        (effectiveDomain (horizonFunction (indicatorVA C)))) :=
  (hC.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).isClosedPolyhedral

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty closed
polyhedral set is finitely generated. -/
theorem
IsClosedPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
        (effectiveDomain (horizonFunction (indicatorVA C)))) :=
  hC.isPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty closed
polyhedral set is polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral
      (raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
        (effectiveDomain (horizonFunction (indicatorVA C)))) :=
  hC.isPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isPolyhedral
    hCne

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty closed
polyhedral set is closed polyhedral. -/
theorem
IsClosedPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
        (effectiveDomain (horizonFunction (indicatorVA C)))) :=
  hC.isPolyhedral.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isClosedPolyhedral
    hCne

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty
polyhedral set has finite conic generators. -/
theorem
IsPolyhedral.exists_raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
          (effectiveDomain (horizonFunction (indicatorVA C))) =
        conicHull (↑u : Set (E × ℝ)) :=
  (hC.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).exists_generators

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty closed
polyhedral set has finite conic generators. -/
theorem
IsClosedPolyhedral.exists_raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
          (effectiveDomain (horizonFunction (indicatorVA C))) =
        conicHull (↑u : Set (E × ℝ)) :=
  hC.isPolyhedral.exists_raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_generators
    hCne

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty
polyhedral set admits a finite conic-coefficient formula. -/
theorem
IsPolyhedral.exists_raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
            (effectiveDomain (horizonFunction (indicatorVA C))) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  (hC.raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).exists_generator_formula

/-- The ray-space cone of the effective domain of an indicator horizon over a nonempty closed
polyhedral set admits a finite conic-coefficient formula. -/
theorem
IsClosedPolyhedral.exists_raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain (horizonFunction (indicatorVA C)))
            (effectiveDomain (horizonFunction (indicatorVA C))) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hC.isPolyhedral.exists_raySpaceCone_effectiveDomain_horizonFunction_indicatorVA_generator_formula
    hCne

/-- The zero level set of the horizon function of an indicator is a cone. -/
theorem isCone_levelSet_zero_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    IsCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact isCone_horizonCone C

/-- The horizon cone of the zero level set of an indicator horizon is unchanged. -/
theorem horizonCone_levelSet_zero_horizonFunction_indicatorVA_eq
    [FiniteDimensional ℝ E] (C : Set E) :
    horizonCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) =
      horizonCone C := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact horizonCone_eq_self_of_isClosed_isCone (isClosed_horizonCone C) (isCone_horizonCone C)

/-- Membership in the horizon cone of the zero level set of an indicator horizon. -/
theorem mem_horizonCone_levelSet_zero_horizonFunction_indicatorVA_iff
    [FiniteDimensional ℝ E] {C : Set E} {w : E} :
    w ∈ horizonCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) ↔
      w ∈ horizonCone C := by
  rw [horizonCone_levelSet_zero_horizonFunction_indicatorVA_eq C]

/-- The ordinary-ray cone of the zero level set of an indicator horizon is the horizon cone
times the negative real ray. -/
theorem ordinaryRayCone_levelSet_zero_horizonFunction_indicatorVA_eq
    [FiniteDimensional ℝ E] (C : Set E) :
    ordinaryRayCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) =
      horizonCone C ×ˢ Set.Iio (0 : ℝ) := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact ordinaryRayCone_eq_prod_Iio_zero_of_isCone (isCone_horizonCone C)

/-- Membership in the ordinary-ray cone of the zero level set of an indicator horizon. -/
theorem mem_ordinaryRayCone_levelSet_zero_horizonFunction_indicatorVA_iff
    [FiniteDimensional ℝ E] {C : Set E} {p : E × ℝ} :
    p ∈ ordinaryRayCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) ↔
      p.1 ∈ horizonCone C ∧ p.2 < 0 := by
  rw [ordinaryRayCone_levelSet_zero_horizonFunction_indicatorVA_eq C]
  rfl

/-- The ray-space cone of the zero level set of an indicator horizon is the horizon cone times
the nonpositive real ray. -/
theorem raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_eq
    [FiniteDimensional ℝ E] (C : Set E) :
    raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) =
      horizonCone C ×ˢ Set.Iic (0 : ℝ) := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact raySpaceCone_eq_prod_Iic_zero_of_isCone (isCone_horizonCone C)

/-- Membership in the ray-space cone of the zero level set of an indicator horizon. -/
theorem mem_raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_iff
    [FiniteDimensional ℝ E] {C : Set E} {p : E × ℝ} :
    p ∈ raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
          (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) ↔
      p.1 ∈ horizonCone C ∧ p.2 ≤ 0 := by
  rw [raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_eq C]
  rfl

/-- The zero level set of the horizon function of the indicator of a nonempty polyhedral set is
finitely generated as a cone. -/
theorem IsPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact hC.horizonCone_isFinitelyGeneratedCone hCne

/-- The zero level set of the horizon function of the indicator of a nonempty polyhedral set is
polyhedral. -/
theorem IsPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) :=
  (hC.levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone hCne).isPolyhedral

/-- The zero level set of the horizon function of the indicator of a nonempty polyhedral set is
closed polyhedral. -/
theorem IsPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) :=
  (hC.levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone hCne).isClosedPolyhedral

/-- The zero level set of the horizon function of the indicator of a nonempty closed polyhedral
set is finitely generated as a cone. -/
theorem IsClosedPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) :=
  hC.isPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone hCne

/-- The zero level set of the horizon function of the indicator of a nonempty closed polyhedral
set is polyhedral. -/
theorem IsClosedPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) :=
  hC.isPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isPolyhedral hCne

/-- The zero level set of the horizon function of the indicator of a nonempty closed polyhedral
set is closed polyhedral. -/
theorem IsClosedPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) :=
  hC.isPolyhedral.levelSet_zero_horizonFunction_indicatorVA_isClosedPolyhedral hCne

/-- The zero level set of the horizon function of the indicator of a nonempty polyhedral set has
finite conic generators. -/
theorem IsPolyhedral.exists_levelSet_zero_horizonFunction_indicatorVA_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ t : Finset E,
      levelSet (horizonFunction (indicatorVA C)) (0 : EReal) = conicHull (↑t : Set E) := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact hC.exists_horizon_conicHull_generators_of_nonempty hCne

/-- The zero level set of the horizon function of the indicator of a nonempty closed polyhedral
set has finite conic generators. -/
theorem IsClosedPolyhedral.exists_levelSet_zero_horizonFunction_indicatorVA_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ t : Finset E,
      levelSet (horizonFunction (indicatorVA C)) (0 : EReal) = conicHull (↑t : Set E) :=
  hC.isPolyhedral.exists_levelSet_zero_horizonFunction_indicatorVA_generators hCne

/-- The zero level set of the horizon function of the indicator of a nonempty polyhedral set
admits a finite conic-coefficient formula. -/
theorem IsPolyhedral.exists_levelSet_zero_horizonFunction_indicatorVA_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ levelSet (horizonFunction (indicatorVA C)) (0 : EReal) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact hC.exists_horizonCone_generator_formula_of_nonempty hCne

/-- The zero level set of the horizon function of the indicator of a nonempty closed polyhedral
set admits a finite conic-coefficient formula. -/
theorem IsClosedPolyhedral.exists_levelSet_zero_horizonFunction_indicatorVA_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ levelSet (horizonFunction (indicatorVA C)) (0 : EReal) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  hC.isPolyhedral.exists_levelSet_zero_horizonFunction_indicatorVA_generator_formula hCne

/-- Every finite lower level of an indicator horizon over a nonempty polyhedral set is
polyhedral: it is either the horizon cone or empty. -/
theorem IsPolyhedral.levelSet_horizonFunction_indicatorVA_coe_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) := by
  by_cases hα : 0 ≤ α
  · rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
    exact hC.horizonCone_isPolyhedral hCne
  · have hαlt : α < 0 := not_le.mp hα
    rw [levelSet_horizonFunction_indicatorVA_coe_of_neg C hαlt]
    exact IsPolyhedral.empty

/-- Every finite lower level of an indicator horizon over a nonempty polyhedral set is closed
polyhedral. -/
theorem IsPolyhedral.levelSet_horizonFunction_indicatorVA_coe_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) := by
  by_cases hα : 0 ≤ α
  · rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
    exact hC.horizonCone_isClosedPolyhedral hCne
  · have hαlt : α < 0 := not_le.mp hα
    rw [levelSet_horizonFunction_indicatorVA_coe_of_neg C hαlt]
    exact IsClosedPolyhedral.empty

/-- Every finite lower level of an indicator horizon over a nonempty closed polyhedral set is
polyhedral. -/
theorem IsClosedPolyhedral.levelSet_horizonFunction_indicatorVA_coe_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) :=
  hC.isPolyhedral.levelSet_horizonFunction_indicatorVA_coe_isPolyhedral hCne

/-- Every finite lower level of an indicator horizon over a nonempty closed polyhedral set is
closed polyhedral. -/
theorem IsClosedPolyhedral.levelSet_horizonFunction_indicatorVA_coe_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) :=
  hC.isPolyhedral.levelSet_horizonFunction_indicatorVA_coe_isClosedPolyhedral hCne

/-- Nonnegative finite lower levels of an indicator horizon over a nonempty polyhedral set are
finitely generated cones. -/
theorem IsPolyhedral.levelSet_horizonFunction_indicatorVA_coe_of_nonneg_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    IsFinitelyGeneratedCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
  exact hC.horizonCone_isFinitelyGeneratedCone hCne

/-- Nonnegative finite lower levels of an indicator horizon over a nonempty closed polyhedral set
are finitely generated cones. -/
theorem
    IsClosedPolyhedral.levelSet_horizonFunction_indicatorVA_coe_of_nonneg_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    IsFinitelyGeneratedCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) :=
  hC.isPolyhedral.levelSet_horizonFunction_indicatorVA_coe_of_nonneg_isFinitelyGeneratedCone
    hCne hα

/-- Nonnegative finite lower levels of an indicator horizon over a nonempty polyhedral set have
finite conic generators. -/
theorem IsPolyhedral.exists_levelSet_horizonFunction_indicatorVA_coe_generators_of_nonneg
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    ∃ t : Finset E,
      levelSet (horizonFunction (indicatorVA C)) (α : EReal) = conicHull (↑t : Set E) := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
  exact hC.exists_horizon_conicHull_generators_of_nonempty hCne

/-- Nonnegative finite lower levels of an indicator horizon over a nonempty closed polyhedral set
have finite conic generators. -/
theorem IsClosedPolyhedral.exists_levelSet_horizonFunction_indicatorVA_coe_generators_of_nonneg
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    ∃ t : Finset E,
      levelSet (horizonFunction (indicatorVA C)) (α : EReal) = conicHull (↑t : Set E) :=
  hC.isPolyhedral.exists_levelSet_horizonFunction_indicatorVA_coe_generators_of_nonneg
    hCne hα

/-- Nonnegative finite lower levels of an indicator horizon over a nonempty polyhedral set come
with a finite conic-coefficient formula. -/
theorem IsPolyhedral.exists_levelSet_horizonFunction_indicatorVA_coe_generator_formula_of_nonneg
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ levelSet (horizonFunction (indicatorVA C)) (α : EReal) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
  exact hC.exists_horizonCone_generator_formula_of_nonempty hCne

/-- Nonnegative finite lower levels of an indicator horizon over a nonempty closed polyhedral set
come with a finite conic-coefficient formula. -/
theorem
    IsClosedPolyhedral.exists_levelSet_horizonFunction_indicatorVA_coe_generator_formula_of_nonneg
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ levelSet (horizonFunction (indicatorVA C)) (α : EReal) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  hC.isPolyhedral.exists_levelSet_horizonFunction_indicatorVA_coe_generator_formula_of_nonneg
    hCne hα

/-- Every finite strict lower level of an indicator horizon over a nonempty polyhedral set is
polyhedral: it is either the horizon cone or empty. -/
theorem IsPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) := by
  by_cases hα : 0 < α
  · rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
    exact hC.horizonCone_isPolyhedral hCne
  · have hαle : α ≤ 0 := le_of_not_gt hα
    rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_nonpos C hαle]
    exact IsPolyhedral.empty

/-- Every finite strict lower level of an indicator horizon over a nonempty polyhedral set is
closed polyhedral. -/
theorem IsPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) := by
  by_cases hα : 0 < α
  · rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
    exact hC.horizonCone_isClosedPolyhedral hCne
  · have hαle : α ≤ 0 := le_of_not_gt hα
    rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_nonpos C hαle]
    exact IsClosedPolyhedral.empty

/-- Every finite strict lower level of an indicator horizon over a nonempty closed polyhedral set
is polyhedral. -/
theorem IsClosedPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) :=
  hC.isPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_isPolyhedral hCne

/-- Every finite strict lower level of an indicator horizon over a nonempty closed polyhedral set
is closed polyhedral. -/
theorem IsClosedPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) :=
  hC.isPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_isClosedPolyhedral hCne

/-- Positive finite strict lower levels of an indicator horizon over a nonempty polyhedral set are
finitely generated cones. -/
theorem IsPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_of_pos_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    IsFinitelyGeneratedCone
      (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
  exact hC.horizonCone_isFinitelyGeneratedCone hCne

/-- Positive finite strict lower levels of an indicator horizon over a nonempty closed polyhedral
set are finitely generated cones. -/
theorem
    IsClosedPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_of_pos_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    IsFinitelyGeneratedCone
      (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) :=
  hC.isPolyhedral.strictLevelSet_horizonFunction_indicatorVA_coe_of_pos_isFinitelyGeneratedCone
    hCne hα

/-- Positive finite strict lower levels of an indicator horizon over a nonempty polyhedral set
have finite conic generators. -/
theorem IsPolyhedral.exists_strictLevelSet_horizonFunction_indicatorVA_coe_generators_of_pos
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    ∃ t : Finset E,
      strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal) =
        conicHull (↑t : Set E) := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
  exact hC.exists_horizon_conicHull_generators_of_nonempty hCne

/-- Positive finite strict lower levels of an indicator horizon over a nonempty closed polyhedral
set have finite conic generators. -/
theorem
    IsClosedPolyhedral.exists_strictLevelSet_horizonFunction_indicatorVA_coe_generators_of_pos
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    ∃ t : Finset E,
      strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal) =
        conicHull (↑t : Set E) :=
  hC.isPolyhedral.exists_strictLevelSet_horizonFunction_indicatorVA_coe_generators_of_pos
    hCne hα

/-- Positive finite strict lower levels of an indicator horizon over a nonempty polyhedral set
come with a finite conic-coefficient formula. -/
theorem IsPolyhedral.exists_strictLevelSet_horizonFunction_indicatorVA_coe_generator_formula_of_pos
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
  exact hC.exists_horizonCone_generator_formula_of_nonempty hCne

/-- Positive finite strict lower levels of an indicator horizon over a nonempty closed polyhedral
set come with a finite conic-coefficient formula. -/
theorem IsClosedPolyhedral.exists_strictLevelSet_horizonFunction_indicatorVA_coe_formula_of_pos
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  hC.isPolyhedral.exists_strictLevelSet_horizonFunction_indicatorVA_coe_generator_formula_of_pos
    hCne hα

/-- Nonnegative finite lower levels of an indicator horizon are cones. -/
theorem isCone_indicatorHorizon_levelSet_coe_of_nonneg [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : 0 ≤ α) :
    IsCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
  exact isCone_horizonCone C

/-- Positive finite strict lower levels of an indicator horizon are cones. -/
theorem isCone_indicatorHorizon_strictLevelSet_coe_of_pos [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : 0 < α) :
    IsCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
  exact isCone_horizonCone C

/-- The horizon cone of a nonnegative finite lower level of an indicator horizon is unchanged. -/
theorem horizonCone_indicatorHorizon_levelSet_nonneg_eq [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : 0 ≤ α) :
    horizonCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      horizonCone C := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
  exact horizonCone_eq_self_of_isClosed_isCone (isClosed_horizonCone C) (isCone_horizonCone C)

/-- Membership in the horizon cone of a nonnegative finite lower level of an indicator horizon. -/
theorem mem_horizonCone_indicatorHorizon_levelSet_nonneg_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : 0 ≤ α) {w : E} :
    w ∈ horizonCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      w ∈ horizonCone C := by
  rw [horizonCone_indicatorHorizon_levelSet_nonneg_eq C hα]

/-- The horizon cone of a negative finite lower level of an indicator horizon is `{0}`. -/
theorem horizonCone_indicatorHorizon_levelSet_neg_eq [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : α < 0) :
    horizonCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      ({0} : Set E) := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_neg C hα]
  simp

/-- Membership in the horizon cone of a negative finite lower level of an indicator horizon. -/
theorem mem_horizonCone_indicatorHorizon_levelSet_neg_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : α < 0) {w : E} :
    w ∈ horizonCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      w = 0 := by
  rw [horizonCone_indicatorHorizon_levelSet_neg_eq C hα]
  simp

/-- The horizon cone of a positive finite strict lower level of an indicator horizon is
unchanged. -/
theorem horizonCone_indicatorHorizon_strictLevelSet_pos_eq [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : 0 < α) :
    horizonCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      horizonCone C := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
  exact horizonCone_eq_self_of_isClosed_isCone (isClosed_horizonCone C) (isCone_horizonCone C)

/-- Membership in the horizon cone of a positive finite strict lower level of an indicator
horizon. -/
theorem mem_horizonCone_indicatorHorizon_strictLevelSet_pos_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : 0 < α) {w : E} :
    w ∈ horizonCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      w ∈ horizonCone C := by
  rw [horizonCone_indicatorHorizon_strictLevelSet_pos_eq C hα]

/-- The horizon cone of a nonpositive finite strict lower level of an indicator horizon is
`{0}`. -/
theorem horizonCone_indicatorHorizon_strictLevelSet_nonpos_eq [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : α ≤ 0) :
    horizonCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      ({0} : Set E) := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_nonpos C hα]
  simp

/-- Membership in the horizon cone of a nonpositive finite strict lower level of an indicator
horizon. -/
theorem mem_horizonCone_indicatorHorizon_strictLevelSet_nonpos_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : α ≤ 0) {w : E} :
    w ∈ horizonCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      w = 0 := by
  rw [horizonCone_indicatorHorizon_strictLevelSet_nonpos_eq C hα]
  simp

/-- The ordinary-ray cone of a nonnegative finite lower level of an indicator horizon is the
horizon cone times the negative real ray. -/
theorem ordinaryRayCone_indicatorHorizon_levelSet_nonneg_eq
    [FiniteDimensional ℝ E] (C : Set E) {α : ℝ} (hα : 0 ≤ α) :
    ordinaryRayCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      horizonCone C ×ˢ Set.Iio (0 : ℝ) := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
  exact ordinaryRayCone_eq_prod_Iio_zero_of_isCone (isCone_horizonCone C)

/-- Membership in the ordinary-ray cone of a nonnegative finite lower level of an indicator
horizon. -/
theorem mem_ordinaryRayCone_indicatorHorizon_levelSet_nonneg_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : 0 ≤ α) {p : E × ℝ} :
    p ∈ ordinaryRayCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      p.1 ∈ horizonCone C ∧ p.2 < 0 := by
  rw [ordinaryRayCone_indicatorHorizon_levelSet_nonneg_eq C hα]
  rfl

/-- The ordinary-ray cone of a negative finite lower level of an indicator horizon is empty. -/
theorem ordinaryRayCone_indicatorHorizon_levelSet_neg_eq
    [FiniteDimensional ℝ E] (C : Set E) {α : ℝ} (hα : α < 0) :
    ordinaryRayCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      ∅ := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_neg C hα]
  exact ordinaryRayCone_empty

/-- No point lies in the ordinary-ray cone of a negative finite lower level of an indicator
horizon. -/
theorem mem_ordinaryRayCone_indicatorHorizon_levelSet_neg_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : α < 0) {p : E × ℝ} :
    p ∈ ordinaryRayCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      False := by
  rw [ordinaryRayCone_indicatorHorizon_levelSet_neg_eq C hα]
  simp

/-- The ordinary-ray cone of a positive finite strict lower level of an indicator horizon is
the horizon cone times the negative real ray. -/
theorem ordinaryRayCone_indicatorHorizon_strictLevelSet_pos_eq
    [FiniteDimensional ℝ E] (C : Set E) {α : ℝ} (hα : 0 < α) :
    ordinaryRayCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      horizonCone C ×ˢ Set.Iio (0 : ℝ) := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
  exact ordinaryRayCone_eq_prod_Iio_zero_of_isCone (isCone_horizonCone C)

/-- Membership in the ordinary-ray cone of a positive finite strict lower level of an indicator
horizon. -/
theorem mem_ordinaryRayCone_indicatorHorizon_strictLevelSet_pos_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : 0 < α) {p : E × ℝ} :
    p ∈ ordinaryRayCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      p.1 ∈ horizonCone C ∧ p.2 < 0 := by
  rw [ordinaryRayCone_indicatorHorizon_strictLevelSet_pos_eq C hα]
  rfl

/-- The ordinary-ray cone of a nonpositive finite strict lower level of an indicator horizon is
empty. -/
theorem ordinaryRayCone_indicatorHorizon_strictLevelSet_nonpos_eq
    [FiniteDimensional ℝ E] (C : Set E) {α : ℝ} (hα : α ≤ 0) :
    ordinaryRayCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      ∅ := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_nonpos C hα]
  exact ordinaryRayCone_empty

/-- No point lies in the ordinary-ray cone of a nonpositive finite strict lower level of an
indicator horizon. -/
theorem mem_ordinaryRayCone_indicatorHorizon_strictLevelSet_nonpos_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : α ≤ 0) {p : E × ℝ} :
    p ∈ ordinaryRayCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      False := by
  rw [ordinaryRayCone_indicatorHorizon_strictLevelSet_nonpos_eq C hα]
  simp

/-- The ray-space cone of a nonnegative finite lower level of an indicator horizon is the
horizon cone times the nonpositive real ray. -/
theorem raySpaceCone_indicatorHorizon_levelSet_nonneg_eq [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : 0 ≤ α) :
    raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      horizonCone C ×ˢ Set.Iic (0 : ℝ) := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_nonneg C hα]
  exact raySpaceCone_eq_prod_Iic_zero_of_isCone (isCone_horizonCone C)

/-- Membership in the ray-space cone of a nonnegative finite lower level of an indicator
horizon. -/
theorem mem_raySpaceCone_indicatorHorizon_levelSet_nonneg_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : 0 ≤ α) {p : E × ℝ} :
    p ∈ raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
          (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      p.1 ∈ horizonCone C ∧ p.2 ≤ 0 := by
  rw [raySpaceCone_indicatorHorizon_levelSet_nonneg_eq C hα]
  rfl

/-- The ray-space cone of a negative finite lower level of an indicator horizon is empty. -/
theorem raySpaceCone_indicatorHorizon_levelSet_neg_eq [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : α < 0) :
    raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      ∅ := by
  rw [levelSet_horizonFunction_indicatorVA_coe_of_neg C hα]
  exact raySpaceCone_empty_empty

/-- No point lies in the ray-space cone of a negative finite lower level of an indicator
horizon. -/
theorem mem_raySpaceCone_indicatorHorizon_levelSet_neg_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : α < 0) {p : E × ℝ} :
    p ∈ raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
          (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      False := by
  rw [raySpaceCone_indicatorHorizon_levelSet_neg_eq C hα]
  simp

/-- The ray-space cone of a positive finite strict lower level of an indicator horizon is the
horizon cone times the nonpositive real ray. -/
theorem raySpaceCone_indicatorHorizon_strictLevelSet_pos_eq [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : 0 < α) :
    raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      horizonCone C ×ˢ Set.Iic (0 : ℝ) := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_pos C hα]
  exact raySpaceCone_eq_prod_Iic_zero_of_isCone (isCone_horizonCone C)

/-- Membership in the ray-space cone of a positive finite strict lower level of an indicator
horizon. -/
theorem mem_raySpaceCone_indicatorHorizon_strictLevelSet_pos_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : 0 < α) {p : E × ℝ} :
    p ∈ raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
          (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      p.1 ∈ horizonCone C ∧ p.2 ≤ 0 := by
  rw [raySpaceCone_indicatorHorizon_strictLevelSet_pos_eq C hα]
  rfl

/-- The ray-space cone of a nonpositive finite strict lower level of an indicator horizon is
empty. -/
theorem raySpaceCone_indicatorHorizon_strictLevelSet_nonpos_eq [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : α ≤ 0) :
    raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
      ∅ := by
  rw [strictLevelSet_horizonFunction_indicatorVA_coe_of_nonpos C hα]
  exact raySpaceCone_empty_empty

/-- No point lies in the ray-space cone of a nonpositive finite strict lower level of an
indicator horizon. -/
theorem mem_raySpaceCone_indicatorHorizon_strictLevelSet_nonpos_iff
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ} (hα : α ≤ 0) {p : E × ℝ} :
    p ∈ raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
          (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
      False := by
  rw [raySpaceCone_indicatorHorizon_strictLevelSet_nonpos_eq C hα]
  simp

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
polyhedral set is finitely generated. -/
theorem IsPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    IsFinitelyGeneratedCone
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  (hC.levelSet_horizonFunction_indicatorVA_coe_of_nonneg_isFinitelyGeneratedCone
    hCne hα).raySpaceCone_of_isCone
    (isCone_indicatorHorizon_levelSet_coe_of_nonneg C hα)

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
polyhedral set is polyhedral. -/
theorem IsPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    IsPolyhedral
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  (hC.raySpaceCone_indicatorHorizon_levelSet_nonneg_isFinitelyGeneratedCone
    hCne hα).isPolyhedral

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
polyhedral set is closed polyhedral. -/
theorem IsPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    IsClosedPolyhedral
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  (hC.raySpaceCone_indicatorHorizon_levelSet_nonneg_isFinitelyGeneratedCone
    hCne hα).isClosedPolyhedral

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
closed polyhedral set is finitely generated. -/
theorem
    IsClosedPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    IsFinitelyGeneratedCone
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  hC.isPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isFinitelyGeneratedCone
    hCne hα

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
closed polyhedral set is polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    IsPolyhedral
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  hC.isPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isPolyhedral
    hCne hα

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
closed polyhedral set is closed polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    IsClosedPolyhedral
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  hC.isPolyhedral.raySpaceCone_indicatorHorizon_levelSet_nonneg_isClosedPolyhedral
    hCne hα

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
polyhedral set has finite conic generators. -/
theorem IsPolyhedral.exists_raySpaceCone_indicatorHorizon_levelSet_nonneg_generators
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
          (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
        conicHull (↑u : Set (E × ℝ)) :=
  (hC.raySpaceCone_indicatorHorizon_levelSet_nonneg_isFinitelyGeneratedCone
    hCne hα).exists_generators

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
closed polyhedral set has finite conic generators. -/
theorem IsClosedPolyhedral.exists_raySpaceCone_indicatorHorizon_levelSet_nonneg_generators
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
          (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
        conicHull (↑u : Set (E × ℝ)) :=
  hC.isPolyhedral.exists_raySpaceCone_indicatorHorizon_levelSet_nonneg_generators
    hCne hα

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
polyhedral set comes with a finite conic-coefficient formula. -/
theorem IsPolyhedral.exists_raySpaceCone_indicatorHorizon_levelSet_nonneg_formula
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
            (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  (hC.raySpaceCone_indicatorHorizon_levelSet_nonneg_isFinitelyGeneratedCone
    hCne hα).exists_generator_formula

/-- The ray-space cone of a nonnegative finite indicator-horizon lower level over a nonempty
closed polyhedral set comes with a finite conic-coefficient formula. -/
theorem IsClosedPolyhedral.exists_raySpaceCone_indicatorHorizon_levelSet_nonneg_formula
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 ≤ α) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (α : EReal))
            (levelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hC.isPolyhedral.exists_raySpaceCone_indicatorHorizon_levelSet_nonneg_formula
    hCne hα

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
polyhedral set is finitely generated. -/
theorem IsPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    IsFinitelyGeneratedCone
      (raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  (hC.strictLevelSet_horizonFunction_indicatorVA_coe_of_pos_isFinitelyGeneratedCone
    hCne hα).raySpaceCone_of_isCone
    (isCone_indicatorHorizon_strictLevelSet_coe_of_pos C hα)

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
polyhedral set is polyhedral. -/
theorem IsPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    IsPolyhedral
      (raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  (hC.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isFinitelyGeneratedCone
    hCne hα).isPolyhedral

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
polyhedral set is closed polyhedral. -/
theorem IsPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    IsClosedPolyhedral
      (raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  (hC.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isFinitelyGeneratedCone
    hCne hα).isClosedPolyhedral

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
closed polyhedral set is finitely generated. -/
theorem
    IsClosedPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    IsFinitelyGeneratedCone
      (raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  hC.isPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isFinitelyGeneratedCone
    hCne hα

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
closed polyhedral set is polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    IsPolyhedral
      (raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  hC.isPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isPolyhedral
    hCne hα

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
closed polyhedral set is closed polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    IsClosedPolyhedral
      (raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
        (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))) :=
  hC.isPolyhedral.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isClosedPolyhedral
    hCne hα

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
polyhedral set has finite conic generators. -/
theorem IsPolyhedral.exists_raySpaceCone_indicatorHorizon_strictLevelSet_pos_generators
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
          (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
        conicHull (↑u : Set (E × ℝ)) :=
  (hC.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isFinitelyGeneratedCone
    hCne hα).exists_generators

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
closed polyhedral set has finite conic generators. -/
theorem IsClosedPolyhedral.exists_raySpaceCone_indicatorHorizon_strictLevelSet_pos_generators
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
          (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) =
        conicHull (↑u : Set (E × ℝ)) :=
  hC.isPolyhedral.exists_raySpaceCone_indicatorHorizon_strictLevelSet_pos_generators
    hCne hα

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
polyhedral set comes with a finite conic-coefficient formula. -/
theorem IsPolyhedral.exists_raySpaceCone_indicatorHorizon_strictLevelSet_pos_formula
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
            (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  (hC.raySpaceCone_indicatorHorizon_strictLevelSet_pos_isFinitelyGeneratedCone
    hCne hα).exists_generator_formula

/-- The ray-space cone of a positive finite indicator-horizon strict lower level over a nonempty
closed polyhedral set comes with a finite conic-coefficient formula. -/
theorem IsClosedPolyhedral.exists_raySpaceCone_indicatorHorizon_strictLevelSet_pos_formula
    [FiniteDimensional ℝ E] {C : Set E} {α : ℝ}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) (hα : 0 < α) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal))
            (strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hC.isPolyhedral.exists_raySpaceCone_indicatorHorizon_strictLevelSet_pos_formula
    hCne hα

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty
polyhedral set is finitely generated. -/
theorem IsPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))) :=
  (hC.levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).raySpaceCone_of_isCone
    (isCone_levelSet_zero_horizonFunction_indicatorVA C)

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty
polyhedral set is polyhedral. -/
theorem IsPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))) :=
  (hC.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).isPolyhedral

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty
polyhedral set is closed polyhedral. -/
theorem IsPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))) :=
  (hC.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).isClosedPolyhedral

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty closed
polyhedral set is finitely generated. -/
theorem
IsClosedPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))) :=
  hC.isPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty closed
polyhedral set is polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))) :=
  hC.isPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isPolyhedral hCne

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty closed
polyhedral set is closed polyhedral. -/
theorem
    IsClosedPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
        (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))) :=
  hC.isPolyhedral.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isClosedPolyhedral
    hCne

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty polyhedral
set has finite conic generators. -/
theorem IsPolyhedral.exists_raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
          (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) =
        conicHull (↑u : Set (E × ℝ)) :=
  (hC.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).exists_generators

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty closed
polyhedral set has finite conic generators. -/
theorem
    IsClosedPolyhedral.exists_raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
          (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) =
        conicHull (↑u : Set (E × ℝ)) :=
  hC.isPolyhedral.exists_raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_generators
    hCne

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty polyhedral
set admits a finite conic-coefficient formula. -/
theorem
    IsPolyhedral.exists_raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
            (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  (hC.raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_isFinitelyGeneratedCone
    hCne).exists_generator_formula

/-- The ray-space cone of the zero level set of an indicator horizon over a nonempty closed
polyhedral set admits a finite conic-coefficient formula. -/
theorem
IsClosedPolyhedral.exists_raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (levelSet (horizonFunction (indicatorVA C)) (0 : EReal))
            (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hC.isPolyhedral.exists_raySpaceCone_levelSet_zero_horizonFunction_indicatorVA_generator_formula
    hCne

/-- The epigraph of the horizon function of the indicator of a nonempty polyhedral set is a
finitely generated cone. -/
theorem IsPolyhedral.horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone (epigraph (horizonFunction (indicatorVA C))) := by
  rw [epigraph_horizonFunction_indicatorVA]
  exact (hC.horizonCone_isFinitelyGeneratedCone hCne).prod
    IsFinitelyGeneratedCone.Ici_zero

/-- The epigraph of the horizon function of the indicator of a nonempty polyhedral set is
polyhedral. -/
theorem IsPolyhedral.horizonFunction_indicatorVA_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (epigraph (horizonFunction (indicatorVA C))) :=
  (hC.horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone hCne).isPolyhedral

/-- The epigraph of the horizon function of the indicator of a nonempty polyhedral set is closed
polyhedral. -/
theorem IsPolyhedral.horizonFunction_indicatorVA_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (epigraph (horizonFunction (indicatorVA C))) :=
  (hC.horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone hCne).isClosedPolyhedral

/-- The epigraph of the horizon function of the indicator of a nonempty closed polyhedral set is
a finitely generated cone. -/
theorem IsClosedPolyhedral.horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone (epigraph (horizonFunction (indicatorVA C))) :=
  hC.isPolyhedral.horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone hCne

/-- The epigraph of the horizon function of the indicator of a nonempty closed polyhedral set is
polyhedral. -/
theorem IsClosedPolyhedral.horizonFunction_indicatorVA_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral (epigraph (horizonFunction (indicatorVA C))) :=
  hC.isPolyhedral.horizonFunction_indicatorVA_epigraph_isPolyhedral hCne

/-- The epigraph of the horizon function of the indicator of a nonempty closed polyhedral set is
closed polyhedral. -/
theorem IsClosedPolyhedral.horizonFunction_indicatorVA_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral (epigraph (horizonFunction (indicatorVA C))) :=
  hC.isPolyhedral.horizonFunction_indicatorVA_epigraph_isClosedPolyhedral hCne

/-- The epigraph of the horizon function of the indicator of a nonempty polyhedral set has finite
conic generators. -/
theorem IsPolyhedral.exists_horizonFunction_indicatorVA_epigraph_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      epigraph (horizonFunction (indicatorVA C)) = conicHull (↑u : Set (E × ℝ)) :=
  (hC.horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone hCne).exists_generators

/-- The epigraph of the horizon function of the indicator of a nonempty closed polyhedral set has
finite conic generators. -/
theorem IsClosedPolyhedral.exists_horizonFunction_indicatorVA_epigraph_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      epigraph (horizonFunction (indicatorVA C)) = conicHull (↑u : Set (E × ℝ)) :=
  hC.isPolyhedral.exists_horizonFunction_indicatorVA_epigraph_generators hCne

/-- The epigraph of the horizon function of the indicator of a nonempty polyhedral set admits a
finite conic-coefficient formula. -/
theorem IsPolyhedral.exists_horizonFunction_indicatorVA_epigraph_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ epigraph (horizonFunction (indicatorVA C)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  (hC.horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone hCne).exists_generator_formula

/-- The epigraph of the horizon function of the indicator of a nonempty closed polyhedral set
admits a finite conic-coefficient formula. -/
theorem IsClosedPolyhedral.exists_horizonFunction_indicatorVA_epigraph_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ epigraph (horizonFunction (indicatorVA C)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hC.isPolyhedral.exists_horizonFunction_indicatorVA_epigraph_generator_formula hCne

/-- The epigraph of an indicator horizon is a cone. -/
theorem isCone_epigraph_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    IsCone (epigraph (horizonFunction (indicatorVA C))) :=
  isCone_epigraph_of_positivelyHomogeneous
    (positivelyHomogeneous_horizonFunction (indicatorVA C))

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty polyhedral set is
finitely generated. -/
theorem IsPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
        (epigraph (horizonFunction (indicatorVA C)))) :=
  (hC.horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone hCne).raySpaceCone_of_isCone
    (isCone_epigraph_horizonFunction_indicatorVA C)

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty polyhedral set is
polyhedral. -/
theorem IsPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral
      (raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
        (epigraph (horizonFunction (indicatorVA C)))) :=
  (hC.raySpaceCone_horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    hCne).isPolyhedral

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty polyhedral set is closed
polyhedral. -/
theorem IsPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
        (epigraph (horizonFunction (indicatorVA C)))) :=
  (hC.raySpaceCone_horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    hCne).isClosedPolyhedral

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty closed polyhedral set is
finitely generated. -/
theorem IsClosedPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
        (epigraph (horizonFunction (indicatorVA C)))) :=
  hC.isPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    hCne

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty closed polyhedral set is
polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsPolyhedral
      (raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
        (epigraph (horizonFunction (indicatorVA C)))) :=
  hC.isPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isPolyhedral hCne

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty closed polyhedral set is
closed polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
        (epigraph (horizonFunction (indicatorVA C)))) :=
  hC.isPolyhedral.raySpaceCone_horizonFunction_indicatorVA_epigraph_isClosedPolyhedral
    hCne

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty polyhedral set has finite
conic generators. -/
theorem IsPolyhedral.exists_raySpaceCone_horizonFunction_indicatorVA_epigraph_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
          (epigraph (horizonFunction (indicatorVA C))) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  (hC.raySpaceCone_horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    hCne).exists_generators

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty closed polyhedral set has
finite conic generators. -/
theorem IsClosedPolyhedral.exists_raySpaceCone_horizonFunction_indicatorVA_epigraph_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
          (epigraph (horizonFunction (indicatorVA C))) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  hC.isPolyhedral.exists_raySpaceCone_horizonFunction_indicatorVA_epigraph_generators hCne

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty polyhedral set admits a
finite conic-coefficient formula. -/
theorem IsPolyhedral.exists_raySpaceCone_horizonFunction_indicatorVA_epigraph_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
            (epigraph (horizonFunction (indicatorVA C))) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  (hC.raySpaceCone_horizonFunction_indicatorVA_epigraph_isFinitelyGeneratedCone
    hCne).exists_generator_formula

/-- The ray-space cone of the indicator-horizon epigraph of a nonempty closed polyhedral set
admits a finite conic-coefficient formula. -/
theorem
    IsClosedPolyhedral.exists_raySpaceCone_horizonFunction_indicatorVA_epigraph_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph (horizonFunction (indicatorVA C)))
            (epigraph (horizonFunction (indicatorVA C))) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hC.isPolyhedral.exists_raySpaceCone_horizonFunction_indicatorVA_epigraph_generator_formula
    hCne

theorem IsConvexPiecewiseLinear.isProper {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsProper f :=
  hf.1

theorem IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    HasClosedPolyhedralEpigraph f :=
  hf.2

theorem IsConvexPiecewiseLinear.hasPolyhedralEpigraph
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    HasPolyhedralEpigraph f :=
  IsClosedPolyhedral.isPolyhedral hf.2

theorem IsConvexPiecewiseLinear.epigraph_nonempty {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    (epigraph f).Nonempty :=
  epigraph_nonempty_of_isProper hf.1

theorem IsConvexPiecewiseLinear.isClosed_epigraph {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosed (epigraph f) :=
  hf.2.isClosed

theorem IsConvexPiecewiseLinear.lowerSemicontinuous {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    LowerSemicontinuous f :=
  hf.2.lowerSemicontinuous

theorem IsConvexPiecewiseLinear.effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral (effectiveDomain f) :=
  hf.2.effectiveDomain_isClosedPolyhedral

theorem IsConvexPiecewiseLinear.exists_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset E,
      effectiveDomain f = extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  exact hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_generators

theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f = extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  exact
    HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_generators_of_isProper
      hf.hasClosedPolyhedralEpigraph
      hf.isProper

/-- In finite dimension, a convex piecewise-linear function admits an explicit
finite generator formula for its effective domain. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
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
  exact hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_generator_formula

theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
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
  exact
    HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_generator_formula_of_isProper
      hf.hasClosedPolyhedralEpigraph
      hf.isProper

/-- A convex piecewise-linear function has a finitely generated
effective-domain horizon cone. -/
theorem IsConvexPiecewiseLinear.horizonCone_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsFinitelyGeneratedCone (horizonCone (effectiveDomain f)) :=
  hf.hasClosedPolyhedralEpigraph.horizonCone_effectiveDomain_isFinitelyGeneratedCone
    (by simpa [effectiveDomain] using hf.isProper.1)

/-- A convex piecewise-linear function has a closed polyhedral
effective-domain horizon cone. -/
theorem IsConvexPiecewiseLinear.horizonCone_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral (horizonCone (effectiveDomain f)) :=
  hf.hasClosedPolyhedralEpigraph.horizonCone_effectiveDomain_isClosedPolyhedral
    (by simpa [effectiveDomain] using hf.isProper.1)

/-- A convex piecewise-linear function has finite effective-domain horizon-cone
generators. -/
theorem IsConvexPiecewiseLinear.exists_horizonCone_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ t : Finset E,
      horizonCone (effectiveDomain f) = conicHull (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generators
    (by simpa [effectiveDomain] using hf.isProper.1)

/-- A convex piecewise-linear function has an explicit finite conic-coefficient
formula for its effective-domain horizon cone. -/
theorem IsConvexPiecewiseLinear.exists_horizonCone_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ horizonCone (effectiveDomain f) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  hf.hasClosedPolyhedralEpigraph.exists_horizonCone_effectiveDomain_generator_formula
    (by simpa [effectiveDomain] using hf.isProper.1)

/-- A convex piecewise-linear function has a finitely generated
effective-domain ray-space cone. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_effectiveDomain_isFinitelyGeneratedCone
    (by simpa [effectiveDomain] using hf.isProper.1)

/-- A convex piecewise-linear function has a closed polyhedral
effective-domain ray-space cone. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral
      (raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_effectiveDomain_isClosedPolyhedral
    (by simpa [effectiveDomain] using hf.isProper.1)

/-- A convex piecewise-linear function has finite effective-domain ray-space
cone generators. -/
theorem IsConvexPiecewiseLinear.exists_raySpaceCone_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) =
        conicHull (↑u : Set (E × ℝ)) :=
  hf.hasClosedPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generators
    (by simpa [effectiveDomain] using hf.isProper.1)

/-- A convex piecewise-linear function has an explicit finite conic-coefficient
formula for its effective-domain ray-space cone. -/
theorem IsConvexPiecewiseLinear.exists_raySpaceCone_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain f) (horizonCone (effectiveDomain f)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.hasClosedPolyhedralEpigraph.exists_raySpaceCone_effectiveDomain_generator_formula
    (by simpa [effectiveDomain] using hf.isProper.1)

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_indicatorVA_effectiveDomain
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsConvexPiecewiseLinear (indicatorVA (effectiveDomain f)) := by
  refine IsClosedPolyhedral.isConvexPiecewiseLinear_indicatorVA
    (hC := hf.effectiveDomain_isClosedPolyhedral) ?_
  exact hf.isProper.1

theorem HasClosedPolyhedralEpigraph.isProper_sup_of_nonempty_effectiveDomain_inter
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) :=
  isProper_sup_of_isProper_of_nonempty_effectiveDomain_inter hproperf hproperg hdom

theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_sup
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g) :
    LowerSemicontinuous (fun x => f x ⊔ g x) :=
  RW.lowerSemicontinuous_sup hf.lowerSemicontinuous hg.lowerSemicontinuous

theorem HasClosedPolyhedralEpigraph.convex_epigraph_sup
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g) :
    Convex ℝ (epigraph (fun x => f x ⊔ g x)) :=
  RW.convex_epigraph_sup hf.convex hg.convex

theorem HasClosedPolyhedralEpigraph.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    horizonFunction (fun x => f x ⊔ g x) =
      fun w => horizonFunction f w ⊔ horizonFunction g w := by
  have hproperSup :
      IsProper (fun x => f x ⊔ g x) :=
    hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  exact RW.horizonFunction_sup_eq_sup
    hf.convex
    hg.convex
    hf.lowerSemicontinuous
    hg.lowerSemicontinuous
    hproperf
    hproperg
    (epigraph_nonempty_of_isProper hproperSup)

theorem HasClosedPolyhedralEpigraph.sup_regular_of_nonempty_effectiveDomain_inter
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) ∧
      LowerSemicontinuous (fun x => f x ⊔ g x) ∧
      Convex ℝ (epigraph (fun x => f x ⊔ g x)) ∧
      horizonFunction (fun x => f x ⊔ g x) =
        fun w => horizonFunction f w ⊔ horizonFunction g w := by
  refine
    ⟨hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom,
      ?_, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_sup hg
  · exact hf.convex_epigraph_sup hg
  · exact hf.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom

/-- Finite pointwise suprema of proper closed-polyhedral-epigraph functions are
proper when the effective domains have a common point. -/
theorem HasClosedPolyhedralEpigraph.isProper_iSup_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (_hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) :=
  isProper_iSup_of_finite_of_isProper_of_nonempty_iInter_effectiveDomain hproper hdom

/-- Lower semicontinuity is preserved by finite pointwise suprema of
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_iSup
    {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i)) :
    LowerSemicontinuous (fun x => ⨆ i, f i x) :=
  RW.lowerSemicontinuous_iSup fun i => (hf i).lowerSemicontinuous

/-- Convex epigraphs are preserved by finite pointwise suprema of
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.convex_epigraph_iSup
    {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i)) :
    Convex ℝ (epigraph (fun x => ⨆ i, f i x)) :=
  RW.convex_epigraph_iSup fun i => (hf i).convex

/-- Finite-family form of Proposition 3.30 for closed-polyhedral-epigraph
functions: under a common effective-domain point, the horizon function commutes
with the pointwise supremum. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w := by
  have hproperSup :
      IsProper (fun x => ⨆ i, f i x) :=
    HasClosedPolyhedralEpigraph.isProper_iSup_of_nonempty_iInter_effectiveDomain
      hf hproper hdom
  exact RW.horizonFunction_iSup_eq_iSup
    (fun i => (hf i).convex)
    (fun i => (hf i).lowerSemicontinuous)
    hproper
    (epigraph_nonempty_of_isProper hproperSup)

/-- Regularity package for finite pointwise suprema of closed-polyhedral-epigraph
functions with a common finite-domain point. -/
theorem HasClosedPolyhedralEpigraph.iSup_regular_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) ∧
      LowerSemicontinuous (fun x => ⨆ i, f i x) ∧
      Convex ℝ (epigraph (fun x => ⨆ i, f i x)) ∧
      horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      HasClosedPolyhedralEpigraph.isProper_iSup_of_nonempty_iInter_effectiveDomain
        hf hproper hdom
  · exact HasClosedPolyhedralEpigraph.lowerSemicontinuous_iSup hf
  · exact HasClosedPolyhedralEpigraph.convex_epigraph_iSup hf
  · exact
      HasClosedPolyhedralEpigraph.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
        hf hproper hdom

theorem IsConvexPiecewiseLinear.isProper_sup_of_nonempty_effectiveDomain_inter
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) :=
  isProper_sup_of_isProper_of_nonempty_effectiveDomain_inter hf.isProper hg.isProper hdom

theorem IsConvexPiecewiseLinear.lowerSemicontinuous_sup
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    LowerSemicontinuous (fun x => f x ⊔ g x) :=
  RW.lowerSemicontinuous_sup hf.lowerSemicontinuous hg.lowerSemicontinuous

theorem IsConvexPiecewiseLinear.convex_epigraph_sup
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    Convex ℝ (epigraph (fun x => f x ⊔ g x)) :=
  RW.convex_epigraph_sup hf.2.convex hg.2.convex

theorem IsConvexPiecewiseLinear.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    horizonFunction (fun x => f x ⊔ g x) =
      fun w => horizonFunction f w ⊔ horizonFunction g w := by
  have hproperSup :
      IsProper (fun x => f x ⊔ g x) :=
    hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hdom
  exact RW.horizonFunction_sup_eq_sup
    hf.2.convex
    hg.2.convex
    hf.lowerSemicontinuous
    hg.lowerSemicontinuous
    hf.isProper
    hg.isProper
    (epigraph_nonempty_of_isProper hproperSup)

theorem IsConvexPiecewiseLinear.sup_regular_of_nonempty_effectiveDomain_inter
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) ∧
      LowerSemicontinuous (fun x => f x ⊔ g x) ∧
      Convex ℝ (epigraph (fun x => f x ⊔ g x)) ∧
      horizonFunction (fun x => f x ⊔ g x) =
        fun w => horizonFunction f w ⊔ horizonFunction g w := by
  refine ⟨hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hdom, ?_, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_sup hg
  · exact hf.convex_epigraph_sup hg
  · exact hf.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter hg hdom

/-- Finite pointwise suprema of convex piecewise-linear functions are proper
when the effective domains have a common point. -/
theorem IsConvexPiecewiseLinear.isProper_iSup_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) :=
  isProper_iSup_of_finite_of_isProper_of_nonempty_iInter_effectiveDomain
    (fun i => (hf i).isProper) hdom

/-- Lower semicontinuity is preserved by finite pointwise suprema of convex
piecewise-linear functions. -/
theorem IsConvexPiecewiseLinear.lowerSemicontinuous_iSup
    {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    LowerSemicontinuous (fun x => ⨆ i, f i x) :=
  RW.lowerSemicontinuous_iSup fun i => (hf i).lowerSemicontinuous

/-- Convex epigraphs are preserved by finite pointwise suprema of convex
piecewise-linear functions. -/
theorem IsConvexPiecewiseLinear.convex_epigraph_iSup
    {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    Convex ℝ (epigraph (fun x => ⨆ i, f i x)) :=
  RW.convex_epigraph_iSup fun i => (hf i).hasClosedPolyhedralEpigraph.convex

/-- Finite-family form of Proposition 3.30 for convex piecewise-linear
functions with a common effective-domain point. -/
theorem IsConvexPiecewiseLinear.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w :=
  HasClosedPolyhedralEpigraph.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
    (fun i => (hf i).hasClosedPolyhedralEpigraph)
    (fun i => (hf i).isProper)
    hdom

/-- Regularity package for finite pointwise suprema of convex piecewise-linear
functions with a common finite-domain point. -/
theorem IsConvexPiecewiseLinear.iSup_regular_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) ∧
      LowerSemicontinuous (fun x => ⨆ i, f i x) ∧
      Convex ℝ (epigraph (fun x => ⨆ i, f i x)) ∧
      horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsConvexPiecewiseLinear.isProper_iSup_of_nonempty_iInter_effectiveDomain hf hdom
  · exact IsConvexPiecewiseLinear.lowerSemicontinuous_iSup hf
  · exact IsConvexPiecewiseLinear.convex_epigraph_iSup hf
  · exact
      IsConvexPiecewiseLinear.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
        hf hdom

theorem HasClosedPolyhedralEpigraph.isProper_inf_of_closedPolyhedralEpigraph
    {f g : E → EReal}
    (_hf : HasClosedPolyhedralEpigraph f) (_hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g) :
    IsProper (fun x => f x ⊓ g x) :=
  isProper_inf_of_isProper hproperf hproperg

theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_inf_of_closedPolyhedralEpigraph
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g) :
    LowerSemicontinuous (fun x => f x ⊓ g x) :=
  RW.lowerSemicontinuous_inf hf.lowerSemicontinuous hg.lowerSemicontinuous

theorem HasClosedPolyhedralEpigraph.horizonFunction_inf_eq_inf_of_closedPolyhedralEpigraph
    {f g : E → EReal}
    (_hf : HasClosedPolyhedralEpigraph f) (_hg : HasClosedPolyhedralEpigraph g) :
    horizonFunction (fun x => f x ⊓ g x) =
      fun w => horizonFunction f w ⊓ horizonFunction g w :=
  RW.horizonFunction_inf_eq_inf

/-- Regularity package for binary pointwise infima of proper
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.inf_regular
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g) :
    IsProper (fun x => f x ⊓ g x) ∧
      LowerSemicontinuous (fun x => f x ⊓ g x) ∧
      horizonFunction (fun x => f x ⊓ g x) =
        fun w => horizonFunction f w ⊓ horizonFunction g w := by
  refine ⟨hf.isProper_inf_of_closedPolyhedralEpigraph hg hproperf hproperg, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_inf_of_closedPolyhedralEpigraph hg
  · exact hf.horizonFunction_inf_eq_inf_of_closedPolyhedralEpigraph hg

/-- Finite pointwise infima of proper closed-polyhedral-epigraph functions are
proper. -/
theorem HasClosedPolyhedralEpigraph.isProper_iInf_of_finite_of_closedPolyhedralEpigraph
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (_hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i)) :
    IsProper (fun x => ⨅ i, f i x) :=
  RW.isProper_iInf_of_finite hproper

/-- Lower semicontinuity is preserved by finite pointwise infima of
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_iInf_of_finite_of_closedPolyhedralEpigraph
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i)) :
    LowerSemicontinuous (fun x => ⨅ i, f i x) :=
  RW.lowerSemicontinuous_iInf_of_finite fun i => (hf i).lowerSemicontinuous

/-- Finite-family form of Proposition 3.30 for closed-polyhedral-epigraph
functions: the horizon function commutes with the pointwise infimum. -/
theorem
    HasClosedPolyhedralEpigraph.horizonFunction_iInf_eq_iInf_of_finite_of_closedPolyhedralEpigraph
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (_hf : ∀ i, HasClosedPolyhedralEpigraph (f i)) :
    horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w :=
  RW.horizonFunction_iInf_eq_iInf_of_finite f

/-- Regularity package for finite pointwise infima of proper
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.iInf_regular_of_finite
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i)) :
    IsProper (fun x => ⨅ i, f i x) ∧
      LowerSemicontinuous (fun x => ⨅ i, f i x) ∧
      horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      HasClosedPolyhedralEpigraph.isProper_iInf_of_finite_of_closedPolyhedralEpigraph
        hf hproper
  · exact
      HasClosedPolyhedralEpigraph.lowerSemicontinuous_iInf_of_finite_of_closedPolyhedralEpigraph
        hf
  · exact
      HasClosedPolyhedralEpigraph.horizonFunction_iInf_eq_iInf_of_finite_of_closedPolyhedralEpigraph
        hf

theorem IsConvexPiecewiseLinear.isProper_inf_of_cpl
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    IsProper (fun x => f x ⊓ g x) :=
  isProper_inf_of_isProper hf.isProper hg.isProper

theorem IsConvexPiecewiseLinear.lowerSemicontinuous_inf_of_cpl
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    LowerSemicontinuous (fun x => f x ⊓ g x) :=
  RW.lowerSemicontinuous_inf hf.lowerSemicontinuous hg.lowerSemicontinuous

theorem IsConvexPiecewiseLinear.horizonFunction_inf_eq_inf_of_cpl
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    horizonFunction (fun x => f x ⊓ g x) =
      fun w => horizonFunction f w ⊓ horizonFunction g w :=
  HasClosedPolyhedralEpigraph.horizonFunction_inf_eq_inf_of_closedPolyhedralEpigraph
    hf.hasClosedPolyhedralEpigraph
    hg.hasClosedPolyhedralEpigraph

/-- Regularity package for binary pointwise infima of convex piecewise-linear
functions. -/
theorem IsConvexPiecewiseLinear.inf_regular
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    IsProper (fun x => f x ⊓ g x) ∧
      LowerSemicontinuous (fun x => f x ⊓ g x) ∧
      horizonFunction (fun x => f x ⊓ g x) =
        fun w => horizonFunction f w ⊓ horizonFunction g w := by
  refine ⟨hf.isProper_inf_of_cpl hg, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_inf_of_cpl hg
  · exact hf.horizonFunction_inf_eq_inf_of_cpl hg

/-- Finite pointwise infima of convex piecewise-linear functions are proper. -/
theorem IsConvexPiecewiseLinear.isProper_iInf_of_finite_of_cpl
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    IsProper (fun x => ⨅ i, f i x) :=
  RW.isProper_iInf_of_finite fun i => (hf i).isProper

/-- Lower semicontinuity is preserved by finite pointwise infima of convex
piecewise-linear functions. -/
theorem IsConvexPiecewiseLinear.lowerSemicontinuous_iInf_of_finite_of_cpl
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    LowerSemicontinuous (fun x => ⨅ i, f i x) :=
  RW.lowerSemicontinuous_iInf_of_finite fun i => (hf i).lowerSemicontinuous

/-- Finite-family form of Proposition 3.30 for convex piecewise-linear
functions: the horizon function commutes with the pointwise infimum. -/
theorem IsConvexPiecewiseLinear.horizonFunction_iInf_eq_iInf_of_finite_of_cpl
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w :=
  HasClosedPolyhedralEpigraph.horizonFunction_iInf_eq_iInf_of_finite_of_closedPolyhedralEpigraph
    (fun i => (hf i).hasClosedPolyhedralEpigraph)

/-- Regularity package for finite pointwise infima of convex piecewise-linear
functions. -/
theorem IsConvexPiecewiseLinear.iInf_regular_of_finite
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    IsProper (fun x => ⨅ i, f i x) ∧
      LowerSemicontinuous (fun x => ⨅ i, f i x) ∧
      horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w := by
  refine ⟨?_, ?_, ?_⟩
  · exact IsConvexPiecewiseLinear.isProper_iInf_of_finite_of_cpl hf
  · exact IsConvexPiecewiseLinear.lowerSemicontinuous_iInf_of_finite_of_cpl hf
  · exact
      IsConvexPiecewiseLinear.horizonFunction_iInf_eq_iInf_of_finite_of_cpl hf

theorem IsConvexPiecewiseLinear.convex_epigraph {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    Convex ℝ (epigraph f) :=
  hf.2.convex

theorem IsConvexPiecewiseLinear.exists_epigraph_generators {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset (E × ℝ),
      epigraph f =
        convexHull ℝ (↑s : Set (E × ℝ)) +
          closure (conicHull (↑t : Set (E × ℝ))) :=
  hf.2

theorem IsConvexPiecewiseLinear.exists_nonempty_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      epigraph f = extendedConvexHull (↑s : Set (E × ℝ)) (↑t : Set (E × ℝ)) := by
  exact
    hf.hasClosedPolyhedralEpigraph.exists_nonempty_generators_of_isProper
      hf.isProper

/-- In finite dimension, a convex piecewise-linear function admits the same
finite epigraph coefficient formula as any function with closed polyhedral
epigraph. -/
theorem IsConvexPiecewiseLinear.exists_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
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
  exact
    HasClosedPolyhedralEpigraph.exists_epigraph_generator_formula
      (f := f)
      (IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph (f := f) hf)

/-- In finite dimension, a convex piecewise-linear function admits a finite
epigraph generator formula with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
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
  exact
    hf.hasClosedPolyhedralEpigraph.exists_nonempty_epigraph_generator_formula_of_isProper
      hf.isProper

/-- In finite dimension, a convex piecewise-linear function has a finitely
generated epigraph horizon cone. -/
theorem IsConvexPiecewiseLinear.horizonCone_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral (horizonCone (epigraph f)) :=
  hf.hasClosedPolyhedralEpigraph.horizonCone_epigraph_isClosedPolyhedral
    (epigraph_nonempty_of_isProper hf.isProper)

/-- In finite dimension, a convex piecewise-linear function has a finitely
generated epigraph horizon cone. -/
theorem IsConvexPiecewiseLinear.horizonCone_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsFinitelyGeneratedCone (horizonCone (epigraph f)) :=
  hf.hasClosedPolyhedralEpigraph.horizonCone_epigraph_isFinitelyGeneratedCone
    (epigraph_nonempty_of_isProper hf.isProper)

/-- In finite dimension, a convex piecewise-linear function has a closed
polyhedral epigraph ray-space cone. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral (raySpaceCone (epigraph f) (horizonCone (epigraph f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_epigraph_isClosedPolyhedral
    (epigraph_nonempty_of_isProper hf.isProper)

/-- In finite dimension, a convex piecewise-linear function has a finitely
generated epigraph ray-space cone. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsFinitelyGeneratedCone (raySpaceCone (epigraph f) (horizonCone (epigraph f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_epigraph_isFinitelyGeneratedCone
    (epigraph_nonempty_of_isProper hf.isProper)

/-- In finite dimension, a convex piecewise-linear function has a finitely
generated epigraph horizon cone. -/
theorem IsConvexPiecewiseLinear.exists_horizonCone_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ t : Finset (E × ℝ),
      horizonCone (epigraph f) = conicHull (↑t : Set (E × ℝ)) :=
  hf.horizonCone_epigraph_isFinitelyGeneratedCone

/-- In finite dimension, a convex piecewise-linear function has an explicit
finite conic-coefficient formula for the horizon cone of its epigraph. -/
theorem IsConvexPiecewiseLinear.exists_horizonCone_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ horizonCone (epigraph f) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.hasClosedPolyhedralEpigraph.exists_horizonCone_epigraph_generator_formula
    (epigraph_nonempty_of_isProper hf.isProper)

/-- In finite dimension, a convex piecewise-linear function has a finitely
generated ray-space cone for its epigraph. -/
theorem IsConvexPiecewiseLinear.exists_raySpaceCone_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph f) (horizonCone (epigraph f)) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  hf.hasClosedPolyhedralEpigraph.exists_raySpaceCone_epigraph_generators
    (epigraph_nonempty_of_isProper hf.isProper)

/-- In finite dimension, a convex piecewise-linear function has an explicit
finite conic-coefficient formula for the ray-space cone of its epigraph. -/
theorem IsConvexPiecewiseLinear.exists_raySpaceCone_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph f) (horizonCone (epigraph f)) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.hasClosedPolyhedralEpigraph.exists_raySpaceCone_epigraph_generator_formula
    (epigraph_nonempty_of_isProper hf.isProper)

/-- In finite dimension, a convex piecewise-linear function admits the same
finite lower-level-set coefficient formula as any function with closed
polyhedral epigraph. -/
theorem IsConvexPiecewiseLinear.exists_levelSet_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (α : ℝ) :
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
  exact hf.hasClosedPolyhedralEpigraph.exists_levelSet_generator_formula α

/-- In finite dimension, a convex piecewise-linear function admits a lower
level-set generator formula with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_levelSet_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (α : ℝ) :
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
  exact
    hf.hasClosedPolyhedralEpigraph.exists_nonempty_levelSet_generator_formula_of_isProper
      hf.isProper α

theorem IsConvexPiecewiseLinear.exists_nonempty_levelSet_generator_formula_of_nonempty
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) {α : ℝ} (hlevel : (levelSet f α).Nonempty) :
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
  exact
    hf.hasClosedPolyhedralEpigraph.exists_nonempty_levelSet_generator_formula_of_nonempty
      hlevel

theorem IsConvexPiecewiseLinear.convex_inequality {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y :=
  convex_inequality_of_convex_epigraph_of_ne_bot hf.convex_epigraph
    (fun x => ne_of_gt (hf.1.2 x))

end RW
