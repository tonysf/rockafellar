/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Horizon Constructions for Polyhedral Functions

This file develops the indicator and horizon-function part of the polyhedral-function API.
-/

import RockafellarWets.Chapter3.PolyhedralFunctions.Core

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

end RW
