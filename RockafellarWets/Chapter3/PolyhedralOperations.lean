/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Polyhedral Function Operations

This file packages the first operation theorem from the polyhedral/function tail
of Chapter 3:
- the horizon function of a proper convex piecewise-linear function is again
  proper with closed polyhedral epigraph.
-/

import RockafellarWets.Chapter3.PolyhedralFunctions
import RockafellarWets.Chapter3.EpiAddition

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The epigraph of a horizon function is a cone. -/
theorem isCone_epigraph_horizonFunction (f : E → EReal) :
    IsCone (epigraph (horizonFunction f)) :=
  isCone_epigraph_of_positivelyHomogeneous (positivelyHomogeneous_horizonFunction f)

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    HasClosedPolyhedralEpigraph (horizonFunction f) := by
  have hhorizon : IsClosedPolyhedral (horizonCone (epigraph f)) :=
    IsClosedPolyhedral.horizonCone_isClosedPolyhedral (C := epigraph f) hf hne
  exact (show IsClosedPolyhedral (epigraph (horizonFunction f)) from by
    rw [epigraph_horizonFunction_eq_horizonCone_epigraph hne]
    exact hhorizon)

/-- The epigraph of the horizon function of a closed-polyhedral-epigraph
function is a finitely generated cone. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsFinitelyGeneratedCone (epigraph (horizonFunction f)) := by
  simpa [epigraph_horizonFunction_eq_horizonCone_epigraph hne] using
    hf.horizonCone_epigraph_isFinitelyGeneratedCone hne

/-- The ray-space cone of the horizon-function epigraph is finitely generated. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  (hf.horizonFunction_epigraph_isFinitelyGeneratedCone hne).raySpaceCone_of_isCone
    (isCone_epigraph_horizonFunction f)

/-- The epigraph of the horizon function of a closed-polyhedral-epigraph
function is a finitely generated cone. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ t : Finset (E × ℝ),
      epigraph (horizonFunction f) = conicHull (↑t : Set (E × ℝ)) := by
  exact (hf.horizonFunction_epigraph_isFinitelyGeneratedCone hne).exists_generators

/-- The epigraph of the horizon function of a closed-polyhedral-epigraph
function has an explicit finite conic-coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ epigraph (horizonFunction f) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p := by
  exact (hf.horizonFunction_epigraph_isFinitelyGeneratedCone hne).exists_generator_formula

/-- The ray-space cone of the horizon-function epigraph has finite generators. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f)) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  (hf.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone hne).exists_generators

/-- The ray-space cone of the horizon-function epigraph has an explicit finite
conic-coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f)) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  IsFinitelyGeneratedCone.exists_generator_formula
    (hf.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone hne)

/-- Properness supplies the epigraph nonemptiness needed for finite generators
of the horizon-function epigraph. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_epigraph_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset (E × ℝ),
      epigraph (horizonFunction f) = conicHull (↑t : Set (E × ℝ)) :=
  hf.exists_horizonFunction_epigraph_generators
    (epigraph_nonempty_of_isProper hproper)

/-- Properness supplies the epigraph nonemptiness needed for the finite
coefficient formula of the horizon-function epigraph. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_epigraph_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ epigraph (horizonFunction f) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.exists_horizonFunction_epigraph_generator_formula
    (epigraph_nonempty_of_isProper hproper)

/-- Properness supplies the epigraph nonemptiness needed for finite generators
of the horizon-function epigraph ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_epigraph_generators_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f)) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  hf.exists_raySpaceCone_horizonFunction_epigraph_generators
    (epigraph_nonempty_of_isProper hproper)

/-- Properness supplies the epigraph nonemptiness needed for the finite
coefficient formula of the horizon-function epigraph ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_epigraph_generator_formula_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f)) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.exists_raySpaceCone_horizonFunction_epigraph_generator_formula
    (epigraph_nonempty_of_isProper hproper)

theorem IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    HasClosedPolyhedralEpigraph (horizonFunction f) :=
  hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_horizonFunction
    (epigraph_nonempty_of_isProper hf.isProper)

/-- The horizon-function epigraph of a convex piecewise-linear function is a
finitely generated cone. -/
theorem IsConvexPiecewiseLinear.exists_horizonFunction_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ t : Finset (E × ℝ),
      epigraph (horizonFunction f) = conicHull (↑t : Set (E × ℝ)) :=
  hf.hasClosedPolyhedralEpigraph.exists_horizonFunction_epigraph_generators_of_isProper
    hf.isProper

/-- The horizon-function epigraph of a convex piecewise-linear function has an
explicit finite conic-coefficient formula. -/
theorem IsConvexPiecewiseLinear.exists_horizonFunction_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ epigraph (horizonFunction f) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.hasClosedPolyhedralEpigraph.exists_horizonFunction_epigraph_generator_formula_of_isProper
    hf.isProper

/-- The horizon-function epigraph ray-space cone of a convex piecewise-linear
function has finite generators. -/
theorem IsConvexPiecewiseLinear.exists_raySpaceCone_horizonFunction_epigraph_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f)) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  hf.hasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_epigraph_generators_of_isProper
    hf.isProper

/-- The horizon-function epigraph ray-space cone of a convex piecewise-linear
function has an explicit finite conic-coefficient formula. -/
theorem IsConvexPiecewiseLinear.exists_raySpaceCone_horizonFunction_epigraph_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f)) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.hasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_epigraph_generator_formula_of_isProper
    hf.isProper

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsConvexPiecewiseLinear (horizonFunction f) := by
  refine
    ⟨?_,
      hf.hasClosedPolyhedralEpigraph_horizonFunction
        (epigraph_nonempty_of_isProper hproper)⟩
  constructor
  · refine ⟨0, ?_⟩
    rw [horizonFunction_zero_eq_zero_of_convex
      hf.convex hf.lowerSemicontinuous hproper]
    simp
  · intro w
    exact bot_lt_horizonFunction_of_convex
      hf.convex hf.lowerSemicontinuous hproper w

/-- The first operation clause in Proposition `3.55(b)`: the horizon function
of a proper convex piecewise-linear function is again proper with closed
polyhedral epigraph. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsConvexPiecewiseLinear (horizonFunction f) := by
  refine ⟨?_, hf.hasClosedPolyhedralEpigraph_horizonFunction⟩
  constructor
  · refine ⟨0, ?_⟩
    rw [horizonFunction_zero_eq_zero_of_convex
      hf.convex_epigraph hf.lowerSemicontinuous hf.isProper]
    simp
  · intro w
    exact bot_lt_horizonFunction_of_convex
      hf.convex_epigraph hf.lowerSemicontinuous hf.isProper w

theorem IsConvexPiecewiseLinear.sublinear_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    Sublinear (horizonFunction f) := by
  refine sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot
    (positivelyHomogeneous_horizonFunction f)
    (convex_epigraph_horizonFunction hf.convex_epigraph)
    ?_
  intro w
  exact ne_of_gt <|
    bot_lt_horizonFunction_of_convex
      hf.convex_epigraph hf.lowerSemicontinuous hf.isProper w

theorem HasClosedPolyhedralEpigraph.sublinear_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    Sublinear (horizonFunction f) := by
  refine sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot
    (positivelyHomogeneous_horizonFunction f)
    (convex_epigraph_horizonFunction hf.convex)
    ?_
  intro w
  exact ne_of_gt <|
    bot_lt_horizonFunction_of_convex
      hf.convex hf.lowerSemicontinuous hproper w

/-- The effective domain of the horizon function of a proper closed convex
function is a cone. -/
theorem isCone_effectiveDomain_horizonFunction_of_convex
    {f : E → EReal} (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsCone (effectiveDomain (horizonFunction f)) := by
  refine ⟨?_, ?_⟩
  · rw [mem_effectiveDomain_iff, horizonFunction_zero_eq_zero_of_convex hconv hlsc hproper]
    exact EReal.coe_lt_top 0
  · intro w hw c hc
    rw [mem_effectiveDomain_iff] at hw ⊢
    rw [(positivelyHomogeneous_horizonFunction f).2 hc]
    exact lt_top_iff_ne_top.mpr <| by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot c), Or.inl ?_, Or.inl (EReal.coe_ne_top c),
        Or.inr (ne_of_lt hw)⟩
      exact_mod_cast hc.le

/-- The effective domain of the horizon function of a closed-polyhedral-epigraph
proper function is closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsClosedPolyhedral (effectiveDomain (horizonFunction f)) :=
  (hf.isConvexPiecewiseLinear_horizonFunction hproper).effectiveDomain_isClosedPolyhedral

/-- The effective domain of the horizon function of a closed-polyhedral-epigraph
proper function is a cone. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_effectiveDomain_isCone
    {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsCone (effectiveDomain (horizonFunction f)) :=
  isCone_effectiveDomain_horizonFunction_of_convex
    hf.convex hf.lowerSemicontinuous hproper

/-- The effective domain of the horizon function of a closed-polyhedral-epigraph
proper function is a finitely generated cone. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsFinitelyGeneratedCone (effectiveDomain (horizonFunction f)) :=
  (hf.horizonFunction_effectiveDomain_isClosedPolyhedral hproper).isFinitelyGeneratedCone_of_isCone
    (hf.horizonFunction_effectiveDomain_isCone hproper)

/-- The effective domain of the horizon function has actual finite conic
generators. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_effectiveDomain_conicGenerators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset E,
      effectiveDomain (horizonFunction f) = conicHull (↑t : Set E) :=
  (hf.horizonFunction_effectiveDomain_isFinitelyGeneratedCone hproper).exists_generators

/-- The effective domain of the horizon function admits a finite conic
coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_effectiveDomain_conicGenerator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ effectiveDomain (horizonFunction f) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  (hf.horizonFunction_effectiveDomain_isFinitelyGeneratedCone hproper).exists_generator_formula

/-- The effective domain of the horizon function is its own horizon cone. -/
theorem HasClosedPolyhedralEpigraph.horizonCone_horizonFunction_effectiveDomain_eq_self
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    horizonCone (effectiveDomain (horizonFunction f)) =
      effectiveDomain (horizonFunction f) :=
  (hf.horizonFunction_effectiveDomain_isFinitelyGeneratedCone hproper).horizonCone_eq_self

/-- The ray-space cone of the horizon-function effective domain is finitely
generated. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain (horizonFunction f))
        (effectiveDomain (horizonFunction f))) :=
  (hf.horizonFunction_effectiveDomain_isFinitelyGeneratedCone hproper).raySpaceCone_of_isCone
    (hf.horizonFunction_effectiveDomain_isCone hproper)

/-- The ray-space cone of the horizon-function effective domain has finite
generators. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain (horizonFunction f))
          (effectiveDomain (horizonFunction f)) =
        conicHull (↑u : Set (E × ℝ)) :=
  (hf.raySpaceCone_horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    hproper).exists_generators

/-- The ray-space cone of the horizon-function effective domain admits a finite
conic-coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain (horizonFunction f))
            (effectiveDomain (horizonFunction f)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  (hf.raySpaceCone_horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    hproper).exists_generator_formula

/-- The effective domain of the horizon function of a closed-polyhedral-epigraph
proper function admits finite ordinary and direction generators. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset E,
      effectiveDomain (horizonFunction f) =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  (hf.isConvexPiecewiseLinear_horizonFunction hproper).exists_effectiveDomain_generators

/-- The effective domain of the horizon function admits finite generators with
a nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_horizonFunction_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain (horizonFunction f) =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  (hf.isConvexPiecewiseLinear_horizonFunction hproper).exists_nonempty_effectiveDomain_generators

/-- The effective domain of the horizon function inherits the finite
convex-plus-conic coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain (horizonFunction f) ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  IsConvexPiecewiseLinear.exists_effectiveDomain_generator_formula
    (hf.isConvexPiecewiseLinear_horizonFunction hproper)

/-- The finite coefficient formula for the effective domain of the horizon
function can be chosen with a nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_horizonFunction_effectiveDomain_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain (horizonFunction f) ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_generator_formula
    (hf.isConvexPiecewiseLinear_horizonFunction hproper)

/-- The effective domain of the horizon function of a convex piecewise-linear
function is closed polyhedral. -/
theorem IsConvexPiecewiseLinear.horizonFunction_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral (effectiveDomain (horizonFunction f)) :=
  hf.isConvexPiecewiseLinear_horizonFunction.effectiveDomain_isClosedPolyhedral

/-- The effective domain of the horizon function of a convex piecewise-linear
function is a cone. -/
theorem IsConvexPiecewiseLinear.horizonFunction_effectiveDomain_isCone
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) :
    IsCone (effectiveDomain (horizonFunction f)) :=
  hf.hasClosedPolyhedralEpigraph.horizonFunction_effectiveDomain_isCone hf.isProper

/-- The effective domain of the horizon function of a convex piecewise-linear
function is a finitely generated cone. -/
theorem IsConvexPiecewiseLinear.horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsFinitelyGeneratedCone (effectiveDomain (horizonFunction f)) :=
  hf.hasClosedPolyhedralEpigraph.horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    hf.isProper

/-- The effective domain of the horizon function of a convex piecewise-linear
function has actual finite conic generators. -/
theorem IsConvexPiecewiseLinear.exists_horizonFunction_effectiveDomain_conicGenerators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ t : Finset E,
      effectiveDomain (horizonFunction f) = conicHull (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_horizonFunction_effectiveDomain_conicGenerators
    hf.isProper

/-- The effective domain of the horizon function of a convex piecewise-linear
function admits a finite conic coefficient formula. -/
theorem IsConvexPiecewiseLinear.exists_horizonFunction_effectiveDomain_conicGenerator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ t : Finset E,
      ∀ {w : E},
        w ∈ effectiveDomain (horizonFunction f) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = w :=
  hf.hasClosedPolyhedralEpigraph.exists_horizonFunction_effectiveDomain_conicGenerator_formula
    hf.isProper

/-- The effective domain of the horizon function is its own horizon cone for a
convex piecewise-linear function. -/
theorem IsConvexPiecewiseLinear.horizonCone_horizonFunction_effectiveDomain_eq_self
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    horizonCone (effectiveDomain (horizonFunction f)) =
      effectiveDomain (horizonFunction f) :=
  hf.hasClosedPolyhedralEpigraph.horizonCone_horizonFunction_effectiveDomain_eq_self
    hf.isProper

/-- The ray-space cone of the horizon-function effective domain is finitely
generated for a convex piecewise-linear function. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain (horizonFunction f))
        (effectiveDomain (horizonFunction f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    hf.isProper

/-- The ray-space cone of the horizon-function effective domain has finite
generators for a convex piecewise-linear function. -/
theorem IsConvexPiecewiseLinear.exists_raySpaceCone_horizonFunction_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain (horizonFunction f))
          (effectiveDomain (horizonFunction f)) =
        conicHull (↑u : Set (E × ℝ)) :=
  hf.hasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_effectiveDomain_generators
    hf.isProper

/-- The ray-space cone of the horizon-function effective domain admits a finite
conic-coefficient formula for a convex piecewise-linear function. -/
theorem IsConvexPiecewiseLinear.exists_raySpaceCone_horizonFunction_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain (horizonFunction f))
            (effectiveDomain (horizonFunction f)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  hf.hasClosedPolyhedralEpigraph.exists_raySpaceCone_horizonFunction_effectiveDomain_generator_formula
    hf.isProper

/-- The effective domain of the horizon function of a convex piecewise-linear
function admits finite ordinary and direction generators. -/
theorem IsConvexPiecewiseLinear.exists_horizonFunction_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset E,
      effectiveDomain (horizonFunction f) =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.isConvexPiecewiseLinear_horizonFunction.exists_effectiveDomain_generators

/-- The effective domain of the horizon function admits finite generators with
a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_horizonFunction_effectiveDomain_generators
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain (horizonFunction f) =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.isConvexPiecewiseLinear_horizonFunction.exists_nonempty_effectiveDomain_generators

/-- The effective domain of the horizon function inherits the finite
convex-plus-conic coefficient formula. -/
theorem IsConvexPiecewiseLinear.exists_horizonFunction_effectiveDomain_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain (horizonFunction f) ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  IsConvexPiecewiseLinear.exists_effectiveDomain_generator_formula
    hf.isConvexPiecewiseLinear_horizonFunction

/-- The finite coefficient formula for the effective domain of the horizon
function can be chosen with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_horizonFunction_effectiveDomain_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain (horizonFunction f) ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_generator_formula
    hf.isConvexPiecewiseLinear_horizonFunction

/-- The indicator of the horizon-function effective domain is convex
piecewise-linear for a proper closed-polyhedral-epigraph function. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_indicatorVA_horizonFunction_effectiveDomain
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsConvexPiecewiseLinear (indicatorVA (effectiveDomain (horizonFunction f))) :=
  (hf.isConvexPiecewiseLinear_horizonFunction hproper).isConvexPiecewiseLinear_indicatorVA_effectiveDomain

/-- The indicator of the horizon-function effective domain is convex
piecewise-linear for a convex piecewise-linear function. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_indicatorVA_horizonFunction_effectiveDomain
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsConvexPiecewiseLinear (indicatorVA (effectiveDomain (horizonFunction f))) :=
  hf.isConvexPiecewiseLinear_horizonFunction.isConvexPiecewiseLinear_indicatorVA_effectiveDomain

/-- Lower level sets of the horizon function inherit the finite epigraph-slice
coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_horizonFunction_levelSet_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) (α : ℝ) :
    ∃ s t : Finset (E × ℝ),
      ∀ {x : E},
        x ∈ levelSet (horizonFunction f) α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) :=
  (hf.isConvexPiecewiseLinear_horizonFunction hproper).exists_levelSet_generator_formula α

/-- Lower level sets of the horizon function inherit a finite coefficient
formula with a nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_horizonFunction_levelSet_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) (α : ℝ) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet (horizonFunction f) α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) :=
  (hf.isConvexPiecewiseLinear_horizonFunction hproper).exists_nonempty_levelSet_generator_formula α

/-- A nonempty lower level set of the horizon function admits a finite
coefficient formula with a nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_horizonFunction_levelSet_generator_formula_of_nonempty
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) {α : ℝ}
    (hlevel : (levelSet (horizonFunction f) α).Nonempty) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet (horizonFunction f) α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) :=
  IsConvexPiecewiseLinear.exists_nonempty_levelSet_generator_formula_of_nonempty
    (hf.isConvexPiecewiseLinear_horizonFunction hproper) hlevel

/-- Lower level sets of the horizon function of a convex piecewise-linear
function inherit the finite epigraph-slice coefficient formula. -/
theorem IsConvexPiecewiseLinear.exists_horizonFunction_levelSet_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (α : ℝ) :
    ∃ s t : Finset (E × ℝ),
      ∀ {x : E},
        x ∈ levelSet (horizonFunction f) α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) :=
  hf.isConvexPiecewiseLinear_horizonFunction.exists_levelSet_generator_formula α

/-- Lower level sets of the horizon function of a convex piecewise-linear
function inherit a finite coefficient formula with a nonempty ordinary
generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_horizonFunction_levelSet_generator_formula
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (α : ℝ) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet (horizonFunction f) α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) :=
  hf.isConvexPiecewiseLinear_horizonFunction.exists_nonempty_levelSet_generator_formula α

/-- A nonempty lower level set of the horizon function of a convex
piecewise-linear function admits a finite coefficient formula with a nonempty
ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_horizonFunction_levelSet_generator_formula_of_nonempty
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) {α : ℝ}
    (hlevel : (levelSet (horizonFunction f) α).Nonempty) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet (horizonFunction f) α ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, α) :=
  IsConvexPiecewiseLinear.exists_nonempty_levelSet_generator_formula_of_nonempty
    hf.isConvexPiecewiseLinear_horizonFunction hlevel

theorem HasPolyhedralEpigraph.epiSumIntegrand
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hbot₁ : ∀ x, f₁ x > ⊥) (hbot₂ : ∀ x, f₂ x > ⊥) :
    HasPolyhedralEpigraph (RW.epiSumIntegrand f₁ f₂) := by
  change IsPolyhedral (epigraph (fun p : E × E => f₁ (p.2 - p.1) + f₂ p.1))
  rw [← image_epiSumLinearMap_eq_epigraph hbot₁ hbot₂]
  exact (IsPolyhedral.prod hf₁ hf₂).linear_image epiSumLinearMap

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSumIntegrand
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    HasClosedPolyhedralEpigraph (RW.epiSumIntegrand f₁ f₂) := by
  have hpoly : HasPolyhedralEpigraph (RW.epiSumIntegrand f₁ f₂) :=
    HasPolyhedralEpigraph.epiSumIntegrand
      (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hproper₁.2 hproper₂.2
  exact HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    hpoly (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSumIntegrand
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    HasClosedPolyhedralEpigraph (RW.epiSumIntegrand f₁ f₂) := by
  exact HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSumIntegrand
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epiSumIntegrand
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    IsConvexPiecewiseLinear (RW.epiSumIntegrand f₁ f₂) := by
  refine ⟨isProper_epiSumIntegrand hproper₁ hproper₂, ?_⟩
  exact hf₁.hasClosedPolyhedralEpigraph_epiSumIntegrand hf₂ hproper₁ hproper₂

section Parametric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E]
    {f : E × F → EReal} (hf : HasPolyhedralEpigraph f) (hlsc : LowerSemicontinuous f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    HasPolyhedralEpigraph (valueFunction f) := by
  change IsPolyhedral (epigraph (valueFunction f))
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (f := f) hlsc hLB]
  exact hf.linear_image valueProjection

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasPolyhedralEpigraph f) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    HasClosedPolyhedralEpigraph (valueFunction f) := by
  have hpoly : HasPolyhedralEpigraph (valueFunction f) :=
    hf.hasPolyhedralEpigraph_valueFunction_of_lsc_localUniform hlsc
      (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)
  exact hpoly.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    (lowerSemicontinuous_valueFunction_of_horizonFunction_pos hlsc hproper hpos)

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    HasClosedPolyhedralEpigraph (valueFunction f) := by
  let hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  change IsClosedPolyhedral (epigraph (valueFunction f))
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (f := f) hlsc (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)]
  exact hf.linear_image valueProjection

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    HasClosedPolyhedralEpigraph (valueFunction f) := by
  let hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  change IsClosedPolyhedral (epigraph (valueFunction f))
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (f := f) hlsc hLB]
  exact hf.linear_image valueProjection

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasPolyhedralEpigraph f) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    IsConvexPiecewiseLinear (valueFunction f) := by
  refine ⟨?_, ?_⟩
  · exact isProper_valueFunction_of_lsc_localUniform hlsc hproper
      (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)
  · exact hf.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos
      hlsc hproper hpos

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    IsConvexPiecewiseLinear (valueFunction f) := by
  let hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  refine ⟨?_, hf.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos hproper hpos⟩
  exact isProper_valueFunction_of_lsc_localUniform hlsc hproper
    (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    IsConvexPiecewiseLinear (valueFunction f) := by
  let hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  refine ⟨isProper_valueFunction_of_lsc_localUniform hlsc hproper hLB, ?_⟩
  exact hf.hasClosedPolyhedralEpigraph_valueFunction_of_lsc_localUniform hLB

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : IsConvexPiecewiseLinear f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    IsConvexPiecewiseLinear (valueFunction f) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_lsc_localUniform
    hf.isProper hLB

end Parametric

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    HasClosedPolyhedralEpigraph (epiSum f₁ f₂) := by
  exact
    HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos
      (f := RW.epiSumIntegrand f₁ f₂)
      (HasPolyhedralEpigraph.epiSumIntegrand
        (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hproper₁.2 hproper₂.2)
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      (isProper_epiSumIntegrand hproper₁ hproper₂) hpos

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    HasClosedPolyhedralEpigraph (epiSum f₁ f₂) := by
  apply HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_horizon_pos
    (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hlsc₁ hlsc₂ hproper₁ hproper₂
  exact horizonFunction_epiSumIntegrand_pos_of_pos
    hf₁.convex hf₂.convex hlsc₁ hlsc₂ hproper₁ hproper₂ hpos

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    HasClosedPolyhedralEpigraph (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_horizon_pos
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hpos

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    HasClosedPolyhedralEpigraph (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_pos
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hpos

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  simpa [epiSum] using
    HasPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_horizonFunction_pos
      (E := E) (F := E)
      (f := RW.epiSumIntegrand f₁ f₂)
      (HasPolyhedralEpigraph.epiSumIntegrand
        (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hproper₁.2 hproper₂.2)
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      (isProper_epiSumIntegrand hproper₁ hproper₂) hpos

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  apply HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hlsc₁ hlsc₂ hproper₁ hproper₂
  exact horizonFunction_epiSumIntegrand_pos_of_pos
    hf₁.convex hf₂.convex hlsc₁ hlsc₂ hproper₁ hproper₂ hpos

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  apply HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hlsc₁ hlsc₂ hproper₁ hproper₂
  exact horizonFunction_epiSum_pos_of_isCoercive
    hf₁.convex hf₂.convex hlsc₁ hlsc₂ hproper₁ hproper₂ hcoercive₂

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hpos

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hpos

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_isCoercive
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hcoercive₂

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : IsConvexPiecewiseLinear f₁) (hf₂ : IsConvexPiecewiseLinear f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    (hf₁.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    (hf₂.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous hf₁.isProper hf₂.isProper hpos

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : IsConvexPiecewiseLinear f₁) (hf₂ : IsConvexPiecewiseLinear f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    (hf₁.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    (hf₂.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous hf₁.isProper hf₂.isProper hpos

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epiSum_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : IsConvexPiecewiseLinear f₁) (hf₂ : IsConvexPiecewiseLinear f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_isCoercive
    (hf₁.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    (hf₂.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous hf₁.isProper hf₂.isProper hcoercive₂

private noncomputable def separatedAddLinearEquiv :
    (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.mk
    { toFun := fun p => (p.2, p.1 + p.2)
      invFun := fun p => (p.2 - p.1, p.1)
      left_inv := by
        intro p
        ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      right_inv := by
        intro p
        ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_add' := by
        intro p q
        ext <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        ext <;> simp [smul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }
    (continuous_snd.prodMk (continuous_fst.add continuous_snd))
    ((continuous_snd.sub continuous_fst).prodMk continuous_fst)

section AffinePerturbations

private noncomputable def epigraphAddLinearEquiv [FiniteDimensional ℝ E] (l : E →ₗ[ℝ] ℝ) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  ContinuousLinearEquiv.mk
    { toFun := fun p => (p.1, p.2 + l p.1)
      invFun := fun p => (p.1, p.2 - l p.1)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro p
        ext <;> simp
      map_add' := by
        intro p q
        ext <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        ext
        · simp
        · simp [smul_add, map_smul, mul_add, add_comm, add_left_comm, add_assoc] }
    (by
      have hl :
          Continuous fun p : E × ℝ => l p.1 :=
        l.continuous_of_finiteDimensional.comp continuous_fst
      exact continuous_fst.prodMk (continuous_snd.add hl))
    (by
      have hl :
          Continuous fun p : E × ℝ => l p.1 :=
        l.continuous_of_finiteDimensional.comp continuous_fst
      exact continuous_fst.prodMk (continuous_snd.sub hl))

@[simp] private theorem epigraphAddLinearEquiv_apply [FiniteDimensional ℝ E]
    (l : E →ₗ[ℝ] ℝ) (p : E × ℝ) :
    epigraphAddLinearEquiv (E := E) l p = (p.1, p.2 + l p.1) :=
  rfl

private noncomputable def epigraphAddAffineMap (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    (E × ℝ) →ᵃ[ℝ] (E × ℝ) where
  toFun p := (p.1, p.2 + l p.1 + c)
  linear :=
    (LinearMap.fst ℝ E ℝ).prod
      (l.comp (LinearMap.fst ℝ E ℝ) + LinearMap.snd ℝ E ℝ)
  map_vadd' p v := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]

@[simp] private theorem epigraphAddAffineMap_apply
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) (p : E × ℝ) :
    epigraphAddAffineMap (E := E) l c p = (p.1, p.2 + l p.1 + c) :=
  rfl

private theorem image_epigraphAddAffineMap_eq_epigraph_addAffine
    {f : E → EReal} (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    epigraphAddAffineMap (E := E) l c '' epigraph f =
      epigraph (fun x => f x + (l x + c : ℝ)) := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨⟨x', s⟩, hs, hp⟩
    have hx : x' = x := by
      simpa [epigraphAddAffineMap_apply] using congrArg Prod.fst hp
    have ht : s + l x' + c = t := by
      simpa [epigraphAddAffineMap_apply] using congrArg Prod.snd hp
    subst x'
    rw [mem_epigraph_iff] at hs ⊢
    have hle' : ((l x + c : ℝ) : EReal) + f x ≤ ((l x + c : ℝ) : EReal) + s := by
      exact add_le_add_right hs (((l x + c : ℝ) : EReal))
    have hle : f x + ((l x + c : ℝ) : EReal) ≤ (s : EReal) + (l x + c : ℝ) := by
      simpa [add_assoc, add_left_comm, add_comm] using hle'
    have hleNorm : f x + ((c : EReal) + (l x : ℝ)) ≤ (c : EReal) + ((s : EReal) + (l x : ℝ)) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hle
    have ht' : (c : EReal) + ((s : EReal) + (l x : ℝ)) = (t : EReal) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using
        congrArg (fun u : ℝ => (u : EReal)) ht
    have hfinal : f x + ((c : EReal) + (l x : ℝ)) ≤ (t : EReal) := by
      exact hleNorm.trans (le_of_eq ht')
    simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hfinal
  · intro hz
    refine ⟨(x, t - (l x + c)), ?_, ?_⟩
    · rw [mem_epigraph_iff] at hz ⊢
      exact
        (EReal.le_sub_iff_add_le
          (a := f x) (b := ((l x + c : ℝ) : EReal)) (c := (t : EReal))
          (Or.inl (by simpa [EReal.coe_add] using (EReal.coe_ne_bot (l x + c))))
          (Or.inl (by simpa [EReal.coe_add] using (EReal.coe_ne_top (l x + c))))).2 <|
          by simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hz
    · ext
      · simp [epigraphAddAffineMap_apply]
      · simp [epigraphAddAffineMap_apply]
        ring

/-- Affine perturbations preserve polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_addAffine
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    HasPolyhedralEpigraph (fun x => f x + (l x + c : ℝ)) := by
  change IsPolyhedral (epigraph (fun x => f x + (l x + c : ℝ)))
  rw [← image_epigraphAddAffineMap_eq_epigraph_addAffine (f := f) (l := l) (c := c)]
  exact hf.affine_image (epigraphAddAffineMap (E := E) l c)

/-- Adding a finite affine function preserves closed polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_addAffine
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    HasClosedPolyhedralEpigraph (fun x => f x + (l x + c : ℝ)) := by
  have hlin : IsClosedPolyhedral (epigraphAddLinearEquiv (E := E) l '' epigraph f) :=
    hf.image_linearEquiv (epigraphAddLinearEquiv (E := E) l)
  have htrans :
      IsClosedPolyhedral
        ((fun p : E × ℝ => p + ((0 : E), c)) '' (epigraphAddLinearEquiv (E := E) l '' epigraph f)) :=
    hlin.image_add_right ((0 : E), c)
  have himage :
      epigraphAddAffineMap (E := E) l c '' epigraph f =
        (fun p : E × ℝ => p + ((0 : E), c)) '' (epigraphAddLinearEquiv (E := E) l '' epigraph f) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨epigraphAddLinearEquiv (E := E) l p, ⟨p, hp, rfl⟩, ?_⟩
      simp [epigraphAddAffineMap_apply, epigraphAddLinearEquiv_apply, add_assoc, add_left_comm,
        add_comm]
    · rintro ⟨q, ⟨p, hp, rfl⟩, hq⟩
      refine ⟨p, hp, ?_⟩
      simpa [epigraphAddAffineMap_apply, epigraphAddLinearEquiv_apply, add_assoc,
        add_left_comm, add_comm] using hq
  change IsClosedPolyhedral (epigraph (fun x => f x + (l x + c : ℝ)))
  rw [← image_epigraphAddAffineMap_eq_epigraph_addAffine (f := f) (l := l) (c := c)]
  rw [himage]
  exact htrans

/-- Adding a finite affine function preserves properness. -/
theorem isProper_addAffine {f : E → EReal}
    (hproper : IsProper f) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsProper (fun x => f x + (l x + c : ℝ)) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact EReal.add_lt_top (ne_of_lt hx) <|
      by simpa [EReal.coe_add] using (EReal.coe_ne_top (l x + c))
  · intro x
    simpa using EReal.add_lt_add_right_coe (hproper.2 x) (l x + c)

/-- Adding a finite affine function preserves lower semicontinuity. -/
theorem lowerSemicontinuous_addAffine {f : E → EReal}
    [FiniteDimensional ℝ E]
    (hlsc : LowerSemicontinuous f) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    LowerSemicontinuous (fun x => f x + (l x + c : ℝ)) := by
  have hcont_aff : Continuous (fun x : E => (((l x + c : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.comp
      (l.continuous_of_finiteDimensional.add continuous_const)
  refine LowerSemicontinuous.add' hlsc hcont_aff.lowerSemicontinuous ?_
  intro x
  exact EReal.continuousAt_add
    (Or.inr (by simpa [EReal.coe_add] using (EReal.coe_ne_bot (l x + c))))
    (Or.inr (by simpa [EReal.coe_add] using (EReal.coe_ne_top (l x + c))))

/-- Affine perturbations preserve convex piecewise-linearity in the project's
epigraph-based sense once properness and lower semicontinuity are available. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_addAffine
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x => f x + (l x + c : ℝ)) := by
  refine ⟨isProper_addAffine hproper l c, ?_⟩
  exact
    (hf.hasPolyhedralEpigraph_addAffine l c).hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
      (lowerSemicontinuous_addAffine hlsc l c)

/-- Adding a finite affine function preserves convex piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_addAffine
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x => f x + (l x + c : ℝ)) := by
  exact ⟨isProper_addAffine hf.isProper l c,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_addAffine l c⟩

/-- Finite affine functions are convex piecewise-linear. -/
theorem isConvexPiecewiseLinear_affine
    [FiniteDimensional ℝ E] (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x : E => (l x + c : ℝ)) := by
  simpa using
    (hasPolyhedralEpigraph_zero (E := E)).isConvexPiecewiseLinear_addAffine
      lowerSemicontinuous_zero isProper_zero l c

end AffinePerturbations

section DomainTranslations

private noncomputable def epigraphTranslateInputMap (u : E) :
    (E × ℝ) →ᵃ[ℝ] (E × ℝ) where
  toFun p := (p.1 - u, p.2)
  linear := LinearMap.id
  map_vadd' p v := by
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

@[simp] private theorem epigraphTranslateInputMap_apply
    (u : E) (p : E × ℝ) :
    epigraphTranslateInputMap (E := E) u p = (p.1 - u, p.2) :=
  rfl

private theorem image_epigraphTranslateInputMap_eq_epigraph_precompose_add
    {f : E → EReal} (u : E) :
    epigraphTranslateInputMap (E := E) u '' epigraph f =
      epigraph (fun x => f (x + u)) := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨⟨x', s⟩, hs, hp⟩
    have hx : x' - u = x := by
      simpa [epigraphTranslateInputMap_apply] using congrArg Prod.fst hp
    have ht : s = t := by
      simpa [epigraphTranslateInputMap_apply] using congrArg Prod.snd hp
    have hx' : x' = x + u := by
      have hx'' := congrArg (fun y : E => y + u) hx
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx''
    subst x'
    subst s
    simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hs
  · intro hz
    refine ⟨(x + u, t), ?_, ?_⟩
    · simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hz
    · ext <;> simp [epigraphTranslateInputMap_apply, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm]

/-- Translating the argument preserves polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_add
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (u : E) :
    HasPolyhedralEpigraph (fun x => f (x + u)) := by
  change IsPolyhedral (epigraph (fun x => f (x + u)))
  rw [← image_epigraphTranslateInputMap_eq_epigraph_precompose_add (f := f) (u := u)]
  exact hf.affine_image (epigraphTranslateInputMap (E := E) u)

/-- Translating the argument preserves closed polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_add
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (u : E) :
    HasClosedPolyhedralEpigraph (fun x => f (x + u)) := by
  have htrans :
      IsClosedPolyhedral
        ((fun p : E × ℝ => p + ((-u), (0 : ℝ))) '' epigraph f) :=
    hf.image_add_right ((-u), (0 : ℝ))
  have himage :
      ((fun p : E × ℝ => p + ((-u), (0 : ℝ))) '' epigraph f) =
        epigraph (fun x => f (x + u)) := by
    ext z
    rcases z with ⟨x, t⟩
    constructor
    · rintro ⟨⟨x', s⟩, hs, hz⟩
      have hx : x' + -u = x := by
        simpa [add_comm, add_left_comm, add_assoc] using congrArg Prod.fst hz
      have ht : s = t := by
        simpa using congrArg Prod.snd hz
      have hx' : x' = x + u := by
        have hx'' := congrArg (fun y : E => y + u) hx
        simpa [add_assoc, add_left_comm, add_comm] using hx''
      subst x'
      subst s
      simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hs
    · intro hz
      refine ⟨(x + u, t), ?_, ?_⟩
      · simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hz
      · ext <;> simp [add_assoc, add_left_comm, add_comm]
  change IsClosedPolyhedral (epigraph (fun x => f (x + u)))
  rw [← himage]
  exact htrans

/-- Translating the argument preserves properness. -/
theorem isProper_precompose_add {f : E → EReal}
    (hproper : IsProper f) (u : E) :
    IsProper (fun x => f (x + u)) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨x - u, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx
  · intro x
    simpa [add_assoc, add_left_comm, add_comm] using hproper.2 (x + u)

/-- Translating the argument preserves lower semicontinuity. -/
theorem lowerSemicontinuous_precompose_add {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (u : E) :
    LowerSemicontinuous (fun x => f (x + u)) := by
  simpa [Function.comp] using hlsc.comp (continuous_id.add continuous_const)

/-- Translating the argument preserves convex piecewise-linearity in the
project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) (u : E) :
    IsConvexPiecewiseLinear (fun x => f (x + u)) := by
  refine ⟨isProper_precompose_add hproper u, ?_⟩
  exact
    (hf.hasPolyhedralEpigraph_precompose_add u).hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
      (lowerSemicontinuous_precompose_add hlsc u)

/-- Translating the argument preserves convex piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_add
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) (u : E) :
    IsConvexPiecewiseLinear (fun x => f (x + u)) := by
  exact ⟨isProper_precompose_add hf.isProper u,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_add u⟩

end DomainTranslations

section PositiveScalings

private noncomputable def epigraphScaleSecondLinearEquiv (a : ℝ) (ha : 0 < a) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  ContinuousLinearEquiv.mk
    { toFun := fun p => (p.1, a * p.2)
      invFun := fun p => (p.1, p.2 / a)
      left_inv := by
        intro p
        ext <;> simp [ha.ne']
      right_inv := by
        intro p
        ext
        · simp
        · exact mul_div_cancel₀ p.2 ha.ne'
      map_add' := by
        intro p q
        ext <;> simp [mul_add]
      map_smul' := by
        intro r p
        ext <;> simp [mul_assoc, mul_left_comm, mul_comm] }
    (by continuity)
    (by continuity)

@[simp] private theorem epigraphScaleSecondLinearEquiv_apply
    (a : ℝ) (ha : 0 < a) (p : E × ℝ) :
    epigraphScaleSecondLinearEquiv (E := E) a ha p = (p.1, a * p.2) :=
  rfl

private noncomputable def epigraphScaleSecondMap (a : ℝ) :
    (E × ℝ) →ᵃ[ℝ] (E × ℝ) where
  toFun p := (p.1, a * p.2)
  linear := (LinearMap.fst ℝ E ℝ).prod (a • LinearMap.snd ℝ E ℝ)
  map_vadd' p v := by
    ext <;> simp [smul_eq_mul, mul_add]

@[simp] private theorem epigraphScaleSecondMap_apply
    (a : ℝ) (p : E × ℝ) :
    epigraphScaleSecondMap (E := E) a p = (p.1, a * p.2) :=
  rfl

private noncomputable def epigraphScaleSecondHomeomorph (a : ℝ) (ha0 : a ≠ 0) :
    (E × ℝ) ≃ₜ (E × ℝ) :=
  (Homeomorph.refl E).prodCongr (Homeomorph.smulOfNeZero a ha0)

@[simp] private theorem epigraphScaleSecondHomeomorph_apply
    (a : ℝ) (ha0 : a ≠ 0) (p : E × ℝ) :
    epigraphScaleSecondHomeomorph (E := E) a ha0 p = (p.1, a * p.2) := by
  cases p
  rfl

private theorem image_epigraphScaleSecondMap_eq_epigraph_const_mul
    {f : E → EReal} {a : ℝ} (ha : 0 < a) :
    epigraphScaleSecondMap (E := E) a '' epigraph f =
      epigraph (fun x => (a : EReal) * f x) := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨⟨x', s⟩, hs, hp⟩
    have hx : x' = x := by
      simpa [epigraphScaleSecondMap_apply] using congrArg Prod.fst hp
    have ht : a * s = t := by
      simpa [epigraphScaleSecondMap_apply] using congrArg Prod.snd hp
    subst x'
    rw [mem_epigraph_iff] at hs ⊢
    have hmul : (a : EReal) * f x ≤ (a : EReal) * s := by
      gcongr
    have ht' : ((a * s : ℝ) : EReal) = (t : EReal) := by
      simpa [EReal.coe_mul] using congrArg (fun u : ℝ => (u : EReal)) ht
    have hmul' : (a : EReal) * f x ≤ ((a * s : ℝ) : EReal) := by
      simpa [EReal.coe_mul] using hmul
    simpa [ht'] using hmul'
  · intro hz
    refine ⟨(x, t / a), ?_, ?_⟩
    · rw [mem_epigraph_iff] at hz ⊢
      exact
        (EReal.le_div_iff_mul_le
          (a := f x) (b := (a : EReal)) (c := (t : EReal))
          (by exact_mod_cast ha) (by simp)).2 <|
          by simpa [mul_comm] using hz
    · ext
      · simp [epigraphScaleSecondMap_apply]
      · simpa [epigraphScaleSecondMap_apply, mul_comm] using div_mul_cancel₀ t ha.ne'

/-- Positive scalar multiples preserve polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_const_mul
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) {a : ℝ} (ha : 0 < a) :
    HasPolyhedralEpigraph (fun x => (a : EReal) * f x) := by
  change IsPolyhedral (epigraph (fun x => (a : EReal) * f x))
  rw [← image_epigraphScaleSecondMap_eq_epigraph_const_mul (f := f) ha]
  exact hf.affine_image (epigraphScaleSecondMap (E := E) a)

/-- Positive scalar multiples preserve closed polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_const_mul
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) {a : ℝ} (ha : 0 < a) :
    HasClosedPolyhedralEpigraph (fun x => (a : EReal) * f x) := by
  have hlin : IsClosedPolyhedral
      (epigraphScaleSecondLinearEquiv (E := E) a ha '' epigraph f) :=
    hf.image_linearEquiv (epigraphScaleSecondLinearEquiv (E := E) a ha)
  change IsClosedPolyhedral (epigraph (fun x => (a : EReal) * f x))
  rw [← image_epigraphScaleSecondMap_eq_epigraph_const_mul (f := f) ha]
  simpa [epigraphScaleSecondMap_apply, epigraphScaleSecondLinearEquiv_apply, mul_comm] using hlin

/-- Positive scalar multiples preserve properness. -/
theorem isProper_const_mul {f : E → EReal}
    (hproper : IsProper f) {a : ℝ} (ha : 0 < a) :
    IsProper (fun x => (a : EReal) * f x) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply lt_top_iff_ne_top.mpr
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (by simp), Or.inl (by exact_mod_cast ha.le), Or.inl (by simp),
      Or.inr (ne_of_lt hx)⟩
  · intro x
    apply bot_lt_iff_ne_bot.mpr
    rw [EReal.mul_ne_bot]
    refine ⟨Or.inl (by simp), Or.inr (ne_of_gt (hproper.2 x)), Or.inl (by simp),
      Or.inl (by exact_mod_cast ha.le)⟩

/-- Positive scalar multiples preserve lower semicontinuity. -/
theorem lowerSemicontinuous_const_mul {f : E → EReal}
    (hlsc : LowerSemicontinuous f) {a : ℝ} (ha : 0 < a) :
    LowerSemicontinuous (fun x => (a : EReal) * f x) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [← image_epigraphScaleSecondMap_eq_epigraph_const_mul (f := f) ha]
  have hclosedMap : IsClosedMap (epigraphScaleSecondMap (E := E) a) := by
    simpa [epigraphScaleSecondMap_apply, epigraphScaleSecondHomeomorph_apply, smul_eq_mul] using
      (epigraphScaleSecondHomeomorph (E := E) a ha.ne').isClosedMap
  exact hclosedMap _ (isClosed_epigraph_of_lsc_ereal f hlsc)

/-- Positive scalar multiples preserve convex piecewise-linearity in the
project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) {a : ℝ} (ha : 0 < a) :
    IsConvexPiecewiseLinear (fun x => (a : EReal) * f x) := by
  refine ⟨isProper_const_mul hproper ha, ?_⟩
  exact
    (hf.hasPolyhedralEpigraph_const_mul ha).hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
      (lowerSemicontinuous_const_mul hlsc ha)

/-- Positive scalar multiples preserve convex piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_const_mul
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) {a : ℝ} (ha : 0 < a) :
    IsConvexPiecewiseLinear (fun x => (a : EReal) * f x) := by
  exact ⟨isProper_const_mul hf.isProper ha,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_const_mul ha⟩

end PositiveScalings

section CombinedOperations

/-- Positive vertical scaling, input translation, and finite affine
perturbation preserve convex piecewise-linearity in the project's epigraph-based
sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineRescaleTranslate
    [FiniteDimensional ℝ E] {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    {a : ℝ} (ha : 0 < a) (u : E) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x => (a : EReal) * f (x + u) + (l x + c : ℝ)) := by
  have hf₁ : HasPolyhedralEpigraph (fun x => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  have hlsc₁ : LowerSemicontinuous (fun x => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  have hproper₁ : IsProper (fun x => f (x + u)) :=
    isProper_precompose_add hproper u
  have hf₂ : HasPolyhedralEpigraph (fun x => (a : EReal) * f (x + u)) :=
    hf₁.hasPolyhedralEpigraph_const_mul ha
  have hlsc₂ : LowerSemicontinuous (fun x => (a : EReal) * f (x + u)) :=
    lowerSemicontinuous_const_mul hlsc₁ ha
  have hproper₂ : IsProper (fun x => (a : EReal) * f (x + u)) :=
    isProper_const_mul hproper₁ ha
  exact hf₂.isConvexPiecewiseLinear_addAffine hlsc₂ hproper₂ l c

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_affineRescaleTranslate
    [FiniteDimensional ℝ E] {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    {a : ℝ} (ha : 0 < a) (u : E) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    HasClosedPolyhedralEpigraph
      (fun x => (a : EReal) * f (x + u) + (l x + c : ℝ)) := by
  have hf₁ : HasClosedPolyhedralEpigraph (fun x => f (x + u)) :=
    hf.hasClosedPolyhedralEpigraph_precompose_add u
  have hf₂ : HasClosedPolyhedralEpigraph (fun x => (a : EReal) * f (x + u)) :=
    hf₁.hasClosedPolyhedralEpigraph_const_mul ha
  exact hf₂.hasClosedPolyhedralEpigraph_addAffine l c

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineRescaleTranslate
    [FiniteDimensional ℝ E] {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f)
    {a : ℝ} (ha : 0 < a) (u : E) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear
      (fun x => (a : EReal) * f (x + u) + (l x + c : ℝ)) := by
  have hf₁_proper : IsProper (fun x => f (x + u)) :=
    isProper_precompose_add hproper u
  have hf₂_proper : IsProper (fun x => (a : EReal) * f (x + u)) :=
    isProper_const_mul hf₁_proper ha
  exact ⟨isProper_addAffine hf₂_proper l c,
    hf.hasClosedPolyhedralEpigraph_affineRescaleTranslate ha u l c⟩

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_affineRescaleTranslate
    [FiniteDimensional ℝ E] {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    {a : ℝ} (ha : 0 < a) (u : E) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear
      (fun x => (a : EReal) * f (x + u) + (l x + c : ℝ)) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineRescaleTranslate
    hf.isProper ha u l c

end CombinedOperations

section LinearEquivalences

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def epigraphPrecomposeLinearEquivMap (e : F ≃L[ℝ] E) :
    (E × ℝ) →ᵃ[ℝ] (F × ℝ) where
  toFun p := (e.symm p.1, p.2)
  linear :=
    (e.symm.toLinearMap.comp (LinearMap.fst ℝ E ℝ)).prod (LinearMap.snd ℝ E ℝ)
  map_vadd' p v := by
    ext <;> simp

@[simp] private theorem epigraphPrecomposeLinearEquivMap_apply
    (e : F ≃L[ℝ] E) (p : E × ℝ) :
    epigraphPrecomposeLinearEquivMap (E := E) e p = (e.symm p.1, p.2) :=
  rfl

private theorem image_epigraphPrecomposeLinearEquivMap_eq_epigraph_precompose
    {f : E → EReal} (e : F ≃L[ℝ] E) :
    epigraphPrecomposeLinearEquivMap (E := E) e '' epigraph f =
      epigraph (fun y : F => f (e y)) := by
  ext z
  rcases z with ⟨y, t⟩
  constructor
  · rintro ⟨⟨x, s⟩, hs, hp⟩
    have hy : e.symm x = y := by
      simpa [epigraphPrecomposeLinearEquivMap_apply] using congrArg Prod.fst hp
    have ht : s = t := by
      simpa [epigraphPrecomposeLinearEquivMap_apply] using congrArg Prod.snd hp
    have hx : x = e y := by
      simpa using congrArg e hy
    subst x
    subst s
    simpa [mem_epigraph_iff] using hs
  · intro hz
    refine ⟨(e y, t), ?_, ?_⟩
    · simpa [mem_epigraph_iff] using hz
    · ext <;> simp [epigraphPrecomposeLinearEquivMap_apply]

/-- Precomposition by a continuous linear equivalence preserves polyhedral
epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearEquiv
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (e : F ≃L[ℝ] E) :
    HasPolyhedralEpigraph (fun y : F => f (e y)) := by
  change IsPolyhedral (epigraph (fun y : F => f (e y)))
  rw [← image_epigraphPrecomposeLinearEquivMap_eq_epigraph_precompose (E := E) (f := f) e]
  exact hf.affine_image (epigraphPrecomposeLinearEquivMap (E := E) e)

/-- Precomposition by a continuous linear equivalence preserves closed
polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearEquiv
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (e : F ≃L[ℝ] E) :
    HasClosedPolyhedralEpigraph (fun y : F => f (e y)) := by
  let e' : (F × ℝ) ≃L[ℝ] (E × ℝ) :=
    e.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have himage : e'.symm '' epigraph f = epigraph (fun y : F => f (e y)) := by
    ext z
    rcases z with ⟨y, t⟩
    constructor
    · rintro ⟨⟨x, s⟩, hs, hz⟩
      have hy : e.symm x = y := by
        simpa [e', ContinuousLinearEquiv.prodCongr_symm] using congrArg Prod.fst hz
      have ht : s = t := by
        simpa [e', ContinuousLinearEquiv.prodCongr_symm] using congrArg Prod.snd hz
      have hx : x = e y := by
        simpa using congrArg e hy
      subst x
      subst s
      simpa [mem_epigraph_iff] using hs
    · intro hz
      refine ⟨(e y, t), ?_, ?_⟩
      · simpa [mem_epigraph_iff] using hz
      · ext <;> simp [e', ContinuousLinearEquiv.prodCongr_symm]
  change IsClosedPolyhedral (epigraph (fun y : F => f (e y)))
  rw [← himage]
  exact hf.image_linearEquiv e'.symm

/-- Precomposition by a continuous linear equivalence preserves properness. -/
theorem isProper_precompose_linearEquiv {f : E → EReal}
    (hproper : IsProper f) (e : F ≃L[ℝ] E) :
    IsProper (fun y : F => f (e y)) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    simpa using hx
  · intro y
    simpa using hproper.2 (e y)

/-- Precomposition by a continuous linear equivalence preserves lower
semicontinuity. -/
theorem lowerSemicontinuous_precompose_linearEquiv {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (e : F ≃L[ℝ] E) :
    LowerSemicontinuous (fun y : F => f (e y)) := by
  simpa [Function.comp] using hlsc.comp e.continuous

/-- Precomposition by a continuous linear equivalence preserves convex
piecewise-linearity in the project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) (e : F ≃L[ℝ] E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y)) := by
  refine ⟨isProper_precompose_linearEquiv hproper e, ?_⟩
  have hpoly : HasPolyhedralEpigraph (fun y : F => f (e y)) :=
    hf.hasPolyhedralEpigraph_precompose_linearEquiv e
  exact hpoly.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    (lowerSemicontinuous_precompose_linearEquiv hlsc e)

/-- Precomposition by a continuous linear equivalence preserves convex
piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearEquiv
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) (e : F ≃L[ℝ] E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y)) := by
  exact ⟨isProper_precompose_linearEquiv hf.isProper e,
    (hf.hasClosedPolyhedralEpigraph).hasClosedPolyhedralEpigraph_precompose_linearEquiv e⟩

/-- The scalar-height epigraph integrand attached to a proper function with
closed polyhedral epigraph is again convex piecewise-linear. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epigraphHeightIntegrand
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsConvexPiecewiseLinear (epigraphHeightIntegrand f) := by
  have hInd : IsConvexPiecewiseLinear (indicatorVA (epigraph f)) :=
    IsClosedPolyhedral.isConvexPiecewiseLinear_indicatorVA
      (hC := (hf : IsClosedPolyhedral (epigraph f)))
      (hCne := epigraph_nonempty_of_isProper hproper)
  have hSwap :
      IsConvexPiecewiseLinear (fun p : ℝ × E => indicatorVA (epigraph f) (p.2, p.1)) := by
    simpa using IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearEquiv hInd
      (ContinuousLinearEquiv.prodComm ℝ ℝ E)
  simpa [epigraphHeightIntegrand] using
    IsConvexPiecewiseLinear.isConvexPiecewiseLinear_addAffine hSwap (LinearMap.fst ℝ ℝ E) 0

/-- The scalar-height epigraph integrand attached to a convex piecewise-linear
function is again convex piecewise-linear. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epigraphHeightIntegrand
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) :
    IsConvexPiecewiseLinear (epigraphHeightIntegrand f) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epigraphHeightIntegrand hf.isProper

/-- If the intersection `epi f ∩ epi g` is polyhedral, then the scalar-height
model for `f ⊔ g` has a polyhedral epigraph. This isolates the remaining
set-side intersection input behind the `max` part of Proposition `3.55(b)`. -/
theorem hasPolyhedralEpigraph_supHeightIntegrand_of_isPolyhedral_inter_epigraph
    [FiniteDimensional ℝ E]
    {f g : E → EReal} (hinter : IsPolyhedral (epigraph f ∩ epigraph g)) :
    HasPolyhedralEpigraph (supHeightIntegrand f g) := by
  have hind : HasPolyhedralEpigraph (indicatorVA (epigraph f ∩ epigraph g)) :=
    hinter.hasPolyhedralEpigraph_indicatorVA
  have hswap :
      HasPolyhedralEpigraph
        (fun p : ℝ × E => indicatorVA (epigraph f ∩ epigraph g) (p.2, p.1)) := by
    simpa using
      hind.hasPolyhedralEpigraph_precompose_linearEquiv
        (ContinuousLinearEquiv.prodComm ℝ ℝ E)
  simpa [supHeightIntegrand, indicatorVA_inter, epigraph_sup, ← add_assoc] using
    hswap.hasPolyhedralEpigraph_addAffine (LinearMap.fst ℝ ℝ E) 0

/-- If the intersection `epi f ∩ epi g` is closed polyhedral, then the
scalar-height model for `f ⊔ g` has a closed polyhedral epigraph. -/
theorem hasClosedPolyhedralEpigraph_supHeightIntegrand_of_isClosedPolyhedral_inter_epigraph
    [FiniteDimensional ℝ E]
    {f g : E → EReal} (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    HasClosedPolyhedralEpigraph (supHeightIntegrand f g) := by
  have hind : HasClosedPolyhedralEpigraph (indicatorVA (epigraph f ∩ epigraph g)) :=
    hinter.hasClosedPolyhedralEpigraph_indicatorVA
  have hswap :
      HasClosedPolyhedralEpigraph
        (fun p : ℝ × E => indicatorVA (epigraph f ∩ epigraph g) (p.2, p.1)) := by
    simpa using
      hind.hasClosedPolyhedralEpigraph_precompose_linearEquiv
        (ContinuousLinearEquiv.prodComm ℝ ℝ E)
  simpa [supHeightIntegrand, indicatorVA_inter, epigraph_sup, ← add_assoc] using
    hswap.hasClosedPolyhedralEpigraph_addAffine (LinearMap.fst ℝ ℝ E) 0

/-- The pointwise supremum of two convex piecewise-linear functions with a
common finite-domain point admits the scalar-height value-function model from
`valueFunction_sup_eq`, and that model already satisfies the proper/lsc/local
uniform hypotheses of Theorem 3.31. -/
theorem IsConvexPiecewiseLinear.supHeightIntegrand_regular_of_nonempty_effectiveDomain_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (supHeightIntegrand f g) ∧
      LowerSemicontinuous (supHeightIntegrand f g) ∧
      IsLevelBoundedInXLocallyUniformly (supHeightIntegrand f g) ∧
      valueFunction (E := ℝ) (F := E) (supHeightIntegrand f g) =
        fun x => f x ⊔ g x := by
  have hreg := hf.sup_regular_of_nonempty_effectiveDomain_inter hg hdom
  refine ⟨isProper_supHeightIntegrand (f := f) (g := g) hreg.1, ?_, ?_, valueFunction_sup_eq f g⟩
  · exact lowerSemicontinuous_supHeightIntegrand (f := f) (g := g) hreg.2.1
  · exact isLevelBoundedInXLocallyUniformly_supHeightIntegrand (f := f) (g := g) hreg.2.1 hreg.1

theorem HasClosedPolyhedralEpigraph.supHeightIntegrand_regular_of_nonempty_effectiveDomain_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (supHeightIntegrand f g) ∧
      LowerSemicontinuous (supHeightIntegrand f g) ∧
      IsLevelBoundedInXLocallyUniformly (supHeightIntegrand f g) ∧
      valueFunction (E := ℝ) (F := E) (supHeightIntegrand f g) =
        fun x => f x ⊔ g x := by
  have hreg :=
    hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  refine ⟨isProper_supHeightIntegrand (f := f) (g := g) hreg.1, ?_, ?_, valueFunction_sup_eq f g⟩
  · exact lowerSemicontinuous_supHeightIntegrand (f := f) (g := g) hreg.2.1
  · exact isLevelBoundedInXLocallyUniformly_supHeightIntegrand (f := f) (g := g) hreg.2.1 hreg.1

/-- Direct epigraph form of the pointwise supremum operation: if the
intersection of the epigraphs is closed polyhedral, then the pointwise
supremum has a closed polyhedral epigraph. -/
theorem hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral
    {ι : Type*} {f : ι → E → EReal}
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) := by
  change IsClosedPolyhedral (epigraph (fun x : E => ⨆ i, f i x))
  rwa [epigraph_iSup]

/-- Binary direct epigraph form of the pointwise supremum operation. -/
theorem hasClosedPolyhedralEpigraph_sup_of_inter_closedPolyhedral
    {f g : E → EReal}
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x : E => f x ⊔ g x) := by
  change IsClosedPolyhedral (epigraph (fun x : E => f x ⊔ g x))
  rwa [epigraph_sup]

/-- If an arbitrary pointwise supremum is proper and its epigraph intersection
is closed polyhedral, then it is convex piecewise-linear. -/
theorem isConvexPiecewiseLinear_iSup_of_iInter_closedPolyhedral
    {ι : Type*} {f : ι → E → EReal}
    (hproper : IsProper (fun x : E => ⨆ i, f i x))
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨆ i, f i x) :=
  ⟨hproper, hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral hinter⟩

/-- Binary direct epigraph form of the pointwise maximum operation at the CPL
layer. -/
theorem isConvexPiecewiseLinear_sup_of_inter_closedPolyhedral
    {f g : E → EReal}
    (hproper : IsProper (fun x : E => f x ⊔ g x))
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊔ g x) :=
  ⟨hproper, hasClosedPolyhedralEpigraph_sup_of_inter_closedPolyhedral hinter⟩

/-- If the scalar-height model for `f ⊔ g` has a polyhedral epigraph, then the
pointwise supremum itself has a closed polyhedral epigraph. This isolates the
remaining structural step in the `max` part of Proposition `3.55(b)`. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hpoly : HasPolyhedralEpigraph (supHeightIntegrand f g)) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  have hreg :=
    hf.supHeightIntegrand_regular_of_nonempty_effectiveDomain_inter
      hg hproperf hproperg hdom
  have hclosedInt : HasClosedPolyhedralEpigraph (supHeightIntegrand f g) :=
    hpoly.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous hreg.2.1
  have hval :
      HasClosedPolyhedralEpigraph
        (valueFunction (E := ℝ) (F := E) (supHeightIntegrand f g)) :=
    hclosedInt.hasClosedPolyhedralEpigraph_valueFunction_of_lsc_localUniform
      hreg.2.2.1
  simpa [hreg.2.2.2] using hval

/-- A polyhedral scalar-height model is enough to conclude that `f ⊔ g` is
convex piecewise-linear. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hpoly : HasPolyhedralEpigraph (supHeightIntegrand f g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hreg :=
    hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  refine ⟨hreg.1, ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
      hg hproperf hproperg hdom hpoly

/-- Top-level reduction of the CPL `max` theorem to polyhedrality of the
scalar-height model. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hpoly : HasPolyhedralEpigraph (supHeightIntegrand f g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hclosedf : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  exact
    hclosedf.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hpoly

/-- A polyhedral intersection theorem for `epi f ∩ epi g` is enough to conclude
that `f ⊔ g` has a closed polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsPolyhedral (epigraph f ∩ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
      hg hproperf hproperg hdom
      (hasPolyhedralEpigraph_supHeightIntegrand_of_isPolyhedral_inter_epigraph hinter)

/-- A polyhedral intersection theorem for `epi f ∩ epi g` is enough to conclude
that `f ⊔ g` is convex piecewise-linear. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_inter_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsPolyhedral (epigraph f ∩ epigraph g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  exact
    hf.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
      hg hdom
      (hasPolyhedralEpigraph_supHeightIntegrand_of_isPolyhedral_inter_epigraph hinter)

/-- A closed-polyhedral intersection theorem for `epi f ∩ epi g` is enough to
conclude that `f ⊔ g` has a closed polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  have hreg :=
    hf.supHeightIntegrand_regular_of_nonempty_effectiveDomain_inter
      hg hproperf hproperg hdom
  have hclosedInt : HasClosedPolyhedralEpigraph (supHeightIntegrand f g) :=
    hasClosedPolyhedralEpigraph_supHeightIntegrand_of_isClosedPolyhedral_inter_epigraph hinter
  have hval :
      HasClosedPolyhedralEpigraph
        (valueFunction (E := ℝ) (F := E) (supHeightIntegrand f g)) :=
    hclosedInt.hasClosedPolyhedralEpigraph_valueFunction_of_lsc_localUniform
      hreg.2.2.1
  simpa [hreg.2.2.2] using hval

/-- A closed-polyhedral intersection theorem for `epi f ∩ epi g` is enough to
conclude that `f ⊔ g` is convex piecewise-linear. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hreg := hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  refine ⟨hreg.1, ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- The same closed-polyhedral intersection hypothesis that yields a
closed-polyhedral epigraph for `f ⊔ g` also makes the effective-domain
intersection `dom f ∩ dom g` closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using hsup.effectiveDomain_isClosedPolyhedral

/-- Under the same closed-polyhedral epigraph-intersection hypothesis, the
effective-domain intersection admits finite ordinary and direction
generators. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using hsup.exists_effectiveDomain_generators

/-- If the effective-domain intersection is nonempty, the same hypothesis gives
an ordinary generator description with a nonempty finite point set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using
    hsup.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_sup] using hdom)

/-- The effective-domain intersection also inherits the finite coefficient
formula from the closed-polyhedral `sup` epigraph. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
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
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using hsup.exists_effectiveDomain_generator_formula

/-- If `dom f ∩ dom g` is nonempty, the same coefficient formula can be chosen
with a nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
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
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using
    hsup.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_sup] using hdom)

/-- A closed-polyhedral theorem for the product epigraphs intersected with the
diagonal already implies the closed-polyhedral epigraph theorem for `f ⊔ g`. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Product-epigraph intersection with the diagonal is enough to conclude that
`f ⊔ g` is convex piecewise-linear at the closed-polyhedral middle layer. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hreg := hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  refine ⟨hreg.1, ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
      hg hproperf hproperg hdom hdiag

/-- The product-diagonal closed-polyhedral criterion also makes the common
effective domain closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.effectiveDomain_inter_isClosedPolyhedral_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Under the product-diagonal closed-polyhedral criterion, the common
effective domain admits finite ordinary and direction generators. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.exists_effectiveDomain_inter_generators_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Under the product-diagonal closed-polyhedral criterion, a nonempty common
effective domain admits finite generators with a nonempty ordinary generator
set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.exists_nonempty_effectiveDomain_inter_generators_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Under the product-diagonal closed-polyhedral criterion, the common
effective domain inherits a finite coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
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
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.exists_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Under the product-diagonal closed-polyhedral criterion, the finite
coefficient formula for the common effective domain can be chosen with a
nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
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
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.exists_nonempty_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- A finitely generated ray-space cone intersection for `epi f` and `epi g`
is enough to conclude that `f ⊔ g` has a closed polyhedral epigraph. This
packages the new set-side ray-space reduction directly at the function layer. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  have hreg := hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  have hne_inter : (epigraph f ∩ epigraph g).Nonempty := by
    simpa [epigraph_sup] using epigraph_nonempty_of_isProper hreg.1
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    hf.inter_of_isFinitelyGeneratedCone_raySpaceCone_inter hg hne_inter hRay
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- The ray-space finite-generation criterion for `epi f ∩ epi g` also makes
`dom f ∩ dom g` closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using hsup.effectiveDomain_isClosedPolyhedral

/-- Under the ray-space finite-generation criterion for `epi f ∩ epi g`, the
effective-domain intersection admits finite ordinary and direction generators.
-/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using hsup.exists_effectiveDomain_generators

/-- Under the ray-space finite-generation criterion for `epi f ∩ epi g`, a
nonempty effective-domain intersection admits finite generators with a nonempty
ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using
    hsup.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_sup] using hdom)

/-- Under the ray-space finite-generation criterion for `epi f ∩ epi g`, the
effective-domain intersection inherits the finite coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
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
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using hsup.exists_effectiveDomain_generator_formula

/-- Under the ray-space finite-generation criterion for `epi f ∩ epi g`, the
finite coefficient formula for a nonempty effective-domain intersection can be
chosen with a nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
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
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using
    hsup.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_sup] using hdom)

/-- Top-level CPL consequence of a closed-polyhedral theorem for
`epi f ∩ epi g`. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hclosedf : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  exact
    hclosedf.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: a closed-polyhedral theorem for `epi f ∩ epi g`
makes the common effective domain closed polyhedral. -/
theorem IsConvexPiecewiseLinear.effectiveDomain_inter_isClosedPolyhedral_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  hf.hasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: a closed-polyhedral theorem for `epi f ∩ epi g`
gives finite generators for the common effective domain. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: a nonempty common effective domain admits finite
generators with a nonempty ordinary generator set under the closed-polyhedral
epigraph-intersection hypothesis. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: the common effective domain inherits the finite
coefficient formula from a closed-polyhedral theorem for `epi f ∩ epi g`. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
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
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: the finite coefficient formula for the common
effective domain can be chosen with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
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
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Product-epigraph intersection with the diagonal is enough to conclude that
`f ⊔ g` is convex piecewise-linear. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hclosedf : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  exact
    HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
      hclosedf hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: the product-diagonal closed-polyhedral criterion
makes the common effective domain closed polyhedral. -/
theorem IsConvexPiecewiseLinear.effectiveDomain_inter_isClosedPolyhedral_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  hf.hasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: the product-diagonal closed-polyhedral criterion
gives finite generators for the common effective domain. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generators_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: under the product-diagonal closed-polyhedral
criterion, a nonempty common effective domain admits finite generators with a
nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generators_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: under the product-diagonal closed-polyhedral
criterion, the common effective domain inherits a finite coefficient formula.
-/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
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
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: under the product-diagonal closed-polyhedral
criterion, the common effective-domain coefficient formula can be chosen with
a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
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
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL consequence of the ray-space finite-generation criterion for
`epi f ∩ epi g`. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hclosedf : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  refine ⟨hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hdom, ?_⟩
  exact
    hclosedf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: the ray-space finite-generation criterion for
`epi f ∩ epi g` makes `dom f ∩ dom g` closed polyhedral. -/
theorem IsConvexPiecewiseLinear.effectiveDomain_inter_isClosedPolyhedral_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  hf.hasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the ray-space finite-generation criterion for
`epi f ∩ epi g`, the effective-domain intersection admits finite generators. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the ray-space finite-generation criterion for
`epi f ∩ epi g`, a nonempty effective-domain intersection admits finite
generators with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the ray-space finite-generation criterion for
`epi f ∩ epi g`, the effective-domain intersection inherits the finite
coefficient formula. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
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
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the ray-space finite-generation criterion for
`epi f ∩ epi g`, the finite coefficient formula can be chosen with a nonempty
ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
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
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Closed polyhedral epigraphs are stable under separated addition on a
product space. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_separatedAdd
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g) :
    HasClosedPolyhedralEpigraph (fun p : E × E => f p.1 + g p.2) := by
  have hsep : HasClosedPolyhedralEpigraph (RW.epiSumIntegrand f g) :=
    HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSumIntegrand
      (hf.hasPolyhedralEpigraph) (hg.hasPolyhedralEpigraph)
      hf.lowerSemicontinuous hg.lowerSemicontinuous hproperf hproperg
  simpa [separatedAddLinearEquiv, RW.epiSumIntegrand, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    hsep.hasClosedPolyhedralEpigraph_precompose_linearEquiv
      (separatedAddLinearEquiv (E := E))

/-- Convex piecewise-linearity is stable under separated addition on a product
space. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_separatedAdd
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    IsConvexPiecewiseLinear (fun p : E × E => f p.1 + g p.2) := by
  refine ⟨?_, hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_separatedAdd
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper⟩
  simpa [separatedAddLinearEquiv, RW.epiSumIntegrand, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    isProper_precompose_linearEquiv
      (isProper_epiSumIntegrand hf.isProper hg.isProper)
      (separatedAddLinearEquiv (E := E))

end LinearEquivalences

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

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) (u : E) :
    IsConvexPiecewiseLinear (fun x : E => f (x + u)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper u

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) {a : ℝ} (ha : 0 < a) :
    IsConvexPiecewiseLinear (fun x : E => (a : EReal) * f x) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper ha

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) (e : F ≃L[ℝ] E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper e

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper L hL

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
