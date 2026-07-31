/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Generated Representations of Polyhedral Functions

This file packages generated-set descriptions and regularity projections for convex piecewise-linear functions.
-/

import RockafellarWets.Chapter3.PolyhedralFunctions.Horizon

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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
