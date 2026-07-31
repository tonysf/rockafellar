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

/-- The linear involution that turns the negative-height ray-space model into
the positive-height epigraph model for gauges. -/
def gaugeEpigraphReflectMap : E × ℝ →ₗ[ℝ] E × ℝ where
  toFun p := (p.1, -p.2)
  map_add' p q := by
    ext <;> simp [add_comm]
  map_smul' c p := by
    ext <;> simp

@[simp] theorem gaugeEpigraphReflectMap_apply (p : E × ℝ) :
    gaugeEpigraphReflectMap (E := E) p = (p.1, -p.2) :=
  rfl

/-- The epigraph of the gauge of a closed convex set containing `0` is the
ray-space cone of the set and its horizon cone, reflected in the scalar
coordinate. This is the ray-space form of Example `3.50`. -/
theorem gaugeFunction_epigraph_eq_reflected_raySpaceCone
    {C : Set E} (hC : Convex ℝ C) (hCclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    (gaugeEpigraphReflectMap (E := E)) ''
        raySpaceCone C (horizonCone C) =
      epigraph (gaugeFunction C) := by
  ext p
  rcases p with ⟨x, a⟩
  constructor
  · rintro ⟨q, hq, hqeq⟩
    rcases q with ⟨y, b⟩
    have hy : y = x := by
      simpa using congrArg Prod.fst hqeq
    have hb : -b = a := by
      simpa using congrArg Prod.snd hqeq
    subst y
    have hb' : b = -a := by linarith
    subst b
    change gaugeFunction C x ≤ a
    rcases hq with hOrd | hHor
    · rcases hOrd with ⟨z, hz, c, hc, hEq⟩
      have hx : x = c • z := by
        simpa using congrArg Prod.fst hEq
      have ha : a = c := by
        have hneg : -a = -c := by
          simpa using congrArg Prod.snd hEq
        linarith
      subst a
      have hxmem : x ∈ c • C := by
        refine ⟨z, hz, ?_⟩
        exact hx.symm
      exact gaugeFunction_le_of_mem_smul hc.le hxmem
    · rcases hHor with ⟨hxhor, ha0⟩
      have hneg : -a = 0 := by
        simpa using ha0
      have ha : a = 0 := by linarith
      rw [ha]
      exact (gaugeFunction_le_zero_iff_mem_horizonCone hC hCclosed h0).2 hxhor
  · intro hp
    change gaugeFunction C x ≤ a at hp
    have ha_nonneg : 0 ≤ a := by
      have haE : (0 : EReal) ≤ (a : EReal) :=
        le_trans (nonneg_gaugeFunction C x) hp
      exact_mod_cast haE
    rcases ha_nonneg.eq_or_lt with rfl | ha_pos
    · have hxhor : x ∈ horizonCone C :=
        (gaugeFunction_le_zero_iff_mem_horizonCone hC hCclosed h0).1 hp
      refine ⟨(x, 0), Or.inr ⟨hxhor, rfl⟩, ?_⟩
      simp
    · have hxlevel : x ∈ levelSet (gaugeFunction C) a := hp
      rw [levelSet_gaugeFunction_eq_smul hC hCclosed h0 ha_pos] at hxlevel
      rcases hxlevel with ⟨z, hz, hzx⟩
      refine ⟨(x, -a), Or.inl ?_, ?_⟩
      · refine ⟨z, hz, a, ha_pos, ?_⟩
        ext <;> simp [hzx]
      · simp

/-- The sublevel sets of the gauge of a closed polyhedral convex set containing
`0` are closed polyhedral. At negative heights the level set is empty, at
height zero it is the horizon cone, and at positive heights it is a scalar
multiple of the base set. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) (a : ℝ) :
    IsClosedPolyhedral (levelSet (gaugeFunction C) a) := by
  rcases lt_trichotomy a 0 with hneg | hzero | hpos
  · rw [levelSet_gaugeFunction_eq_empty_of_neg (C := C) hneg]
    exact IsClosedPolyhedral.empty
  · subst a
    rw [levelSet_gaugeFunction_zero hC.convex hC.isClosed h0]
    exact hC.horizonCone_isClosedPolyhedral ⟨0, h0⟩
  · rw [levelSet_gaugeFunction_eq_smul hC.convex hC.isClosed h0 hpos]
    exact hC.smul a

theorem IsClosedPolyhedral.levelSet_gaugeFunction_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) (a : ℝ) :
    IsPolyhedral (levelSet (gaugeFunction C) a) :=
  (hC.levelSet_gaugeFunction_isClosedPolyhedral h0 a).isPolyhedral

/-- Negative gauge sublevels of a closed polyhedral set are empty. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_eq_empty_of_neg
    {C : Set E} (_hC : IsClosedPolyhedral C) {a : ℝ} (ha : a < 0) :
    levelSet (gaugeFunction C) a = ∅ :=
  RW.levelSet_gaugeFunction_eq_empty_of_neg (C := C) ha

/-- Gauge sublevels of a closed polyhedral set are nonempty exactly at
nonnegative heights. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_nonempty_iff_nonneg
    {C : Set E} (_hC : IsClosedPolyhedral C) {a : ℝ} :
    (levelSet (gaugeFunction C) a).Nonempty ↔ 0 ≤ a :=
  RW.levelSet_gaugeFunction_nonempty_iff_nonneg (C := C) (a := a)

/-- Gauge sublevels of a closed polyhedral set are empty exactly at negative
heights. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_eq_empty_iff_neg
    {C : Set E} (_hC : IsClosedPolyhedral C) {a : ℝ} :
    levelSet (gaugeFunction C) a = ∅ ↔ a < 0 :=
  RW.levelSet_gaugeFunction_eq_empty_iff_neg (C := C) (a := a)

/-- Nonpositive strict gauge sublevels of a closed polyhedral set are empty. -/
theorem IsClosedPolyhedral.strictLevelSet_gaugeFunction_eq_empty_of_nonpos
    {C : Set E} (_hC : IsClosedPolyhedral C) {a : ℝ} (ha : a ≤ 0) :
    strictLevelSet (gaugeFunction C) a = ∅ :=
  RW.strictLevelSet_gaugeFunction_eq_empty_of_nonpos (C := C) ha

/-- Strict gauge sublevels of a closed polyhedral set are nonempty exactly at
positive heights. -/
theorem IsClosedPolyhedral.strictLevelSet_gaugeFunction_nonempty_iff_pos
    {C : Set E} (_hC : IsClosedPolyhedral C) {a : ℝ} :
    (strictLevelSet (gaugeFunction C) a).Nonempty ↔ 0 < a :=
  RW.strictLevelSet_gaugeFunction_nonempty_iff_pos (C := C) (a := a)

/-- Strict gauge sublevels of a closed polyhedral set are empty exactly at
nonpositive heights. -/
theorem IsClosedPolyhedral.strictLevelSet_gaugeFunction_eq_empty_iff_nonpos
    {C : Set E} (_hC : IsClosedPolyhedral C) {a : ℝ} :
    strictLevelSet (gaugeFunction C) a = ∅ ↔ a ≤ 0 :=
  RW.strictLevelSet_gaugeFunction_eq_empty_iff_nonpos (C := C) (a := a)

/-- Positive gauge sublevels of a closed polyhedral convex set containing `0`
are exactly the corresponding scalar multiples of the set. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_eq_smul
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    {a : ℝ} (ha : 0 < a) :
    levelSet (gaugeFunction C) a = a • C :=
  RW.levelSet_gaugeFunction_eq_smul hC.convex hC.isClosed h0 ha

/-- Positive gauge sublevel membership for a closed polyhedral convex set
containing `0`. -/
theorem IsClosedPolyhedral.gaugeFunction_le_iff_mem_smul
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    {a : ℝ} (ha : 0 < a) {x : E} :
    gaugeFunction C x ≤ (a : EReal) ↔ x ∈ a • C :=
  RW.gaugeFunction_le_iff_mem_smul hC.convex hC.isClosed h0 ha

/-- Strict gauge bounds for a closed polyhedral convex set containing `0` are
witnessed by membership in smaller nonnegative scalar copies. -/
theorem IsClosedPolyhedral.gaugeFunction_lt_iff_exists_mem_smul
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    {a : ℝ} {x : E} :
    gaugeFunction C x < (a : EReal) ↔
      ∃ r : ℝ, 0 ≤ r ∧ r < a ∧ x ∈ r • C :=
  RW.gaugeFunction_lt_iff_exists_mem_smul hC.convex h0

/-- Strict gauge sublevels of a closed polyhedral convex set containing `0`
are unions of nonnegative scalar copies below the level. -/
theorem IsClosedPolyhedral.strictLevelSet_gaugeFunction_eq_iUnion_smul
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) {a : ℝ} :
    strictLevelSet (gaugeFunction C) a =
      ⋃ r : {r : ℝ // 0 ≤ r ∧ r < a}, r.1 • C :=
  RW.strictLevelSet_gaugeFunction_eq_iUnion_smul hC.convex h0

/-- Gauge sublevels of a closed polyhedral convex set containing `0` can be
written as intersections of all larger positive scalar copies. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_eq_iInter_smul
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    {a : ℝ} (ha : 0 ≤ a) :
    levelSet (gaugeFunction C) a = ⋂ (r : ℝ) (_ : a < r), r • C :=
  RW.levelSet_gaugeFunction_eq_iInter_smul hC.convex h0 ha

/-- The unit sublevel set of the gauge of a closed polyhedral convex set is the
set itself. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_one
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    levelSet (gaugeFunction C) 1 = C :=
  RW.levelSet_gaugeFunction_one hC.convex hC.isClosed h0

/-- Unit gauge sublevel membership for a closed polyhedral convex set
containing `0`. -/
theorem IsClosedPolyhedral.gaugeFunction_le_one_iff_mem
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) {x : E} :
    gaugeFunction C x ≤ (1 : EReal) ↔ x ∈ C :=
  RW.gaugeFunction_le_one_iff_mem hC.convex hC.isClosed h0

/-- Strict positive gauge sublevels of a closed polyhedral convex set
containing `0` are contained in the corresponding scalar multiple. -/
theorem IsClosedPolyhedral.strictLevelSet_gaugeFunction_subset_smul
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    {a : ℝ} (ha : 0 < a) :
    strictLevelSet (gaugeFunction C) a ⊆ a • C :=
  RW.strictLevelSet_gaugeFunction_subset_smul hC.convex hC.isClosed h0 ha

/-- The strict unit gauge sublevel of a closed polyhedral convex set is
contained in the set. -/
theorem IsClosedPolyhedral.strictLevelSet_gaugeFunction_one_subset
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    strictLevelSet (gaugeFunction C) 1 ⊆ C :=
  RW.strictLevelSet_gaugeFunction_one_subset hC.convex hC.isClosed h0

/-- The zero sublevel set of the gauge of a closed polyhedral convex set is its
horizon cone. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_zero
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    levelSet (gaugeFunction C) (0 : ℝ) = horizonCone C :=
  RW.levelSet_gaugeFunction_zero hC.convex hC.isClosed h0

/-- Gauge values at most zero are exactly horizon directions for a closed
polyhedral convex set. -/
theorem IsClosedPolyhedral.gaugeFunction_le_zero_iff_mem_horizonCone
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) {x : E} :
    gaugeFunction C x ≤ 0 ↔ x ∈ horizonCone C :=
  RW.gaugeFunction_le_zero_iff_mem_horizonCone hC.convex hC.isClosed h0

/-- The gauge vanishes exactly on the horizon cone. -/
theorem IsClosedPolyhedral.gaugeFunction_eq_zero_iff_mem_horizonCone
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) {x : E} :
    gaugeFunction C x = 0 ↔ x ∈ horizonCone C :=
  RW.gaugeFunction_eq_zero_iff_mem_horizonCone hC.convex hC.isClosed h0

/-- Away from the horizon cone, the gauge is strictly positive. -/
theorem IsClosedPolyhedral.gaugeFunction_pos_iff_not_mem_horizonCone
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) {x : E} :
    0 < gaugeFunction C x ↔ x ∉ horizonCone C :=
  RW.gaugeFunction_pos_iff_not_mem_horizonCone hC.convex hC.isClosed h0

/-- For bounded closed polyhedral sets, the zero sublevel set of the gauge
collapses to `{0}`. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_zero_eq_singleton_zero_of_isBounded
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (hCbdd : Bornology.IsBounded C) :
    levelSet (gaugeFunction C) (0 : ℝ) = ({0} : Set E) :=
  RW.levelSet_gaugeFunction_zero_eq_singleton_zero_of_isBounded
    hC.convex hC.isClosed h0 hCbdd

/-- For bounded closed polyhedral sets, the gauge vanishes only at the origin. -/
theorem IsClosedPolyhedral.gaugeFunction_eq_zero_iff_of_isBounded
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (hCbdd : Bornology.IsBounded C) {x : E} :
    gaugeFunction C x = 0 ↔ x = 0 :=
  RW.gaugeFunction_eq_zero_iff_of_isBounded hC.convex hC.isClosed h0 hCbdd

/-- For bounded closed polyhedral sets, the gauge is strictly positive away
from the origin. -/
theorem IsClosedPolyhedral.gaugeFunction_pos_iff_ne_zero_of_isBounded
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (hCbdd : Bornology.IsBounded C) {x : E} :
    0 < gaugeFunction C x ↔ x ≠ 0 :=
  RW.gaugeFunction_pos_iff_ne_zero_of_isBounded hC.convex hC.isClosed h0 hCbdd

/-- A gauge sublevel set of a closed polyhedral convex set containing `0`
admits finite ordinary and direction generators. -/
theorem IsClosedPolyhedral.exists_gaugeFunction_levelSet_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) (a : ℝ) :
    ∃ s t : Finset E,
      levelSet (gaugeFunction C) a =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  (hC.levelSet_gaugeFunction_isClosedPolyhedral h0 a).exists_generators

/-- At nonnegative heights, the finite description of a gauge sublevel set can
be chosen with a nonempty ordinary generator set. -/
theorem IsClosedPolyhedral.exists_nonempty_gaugeFunction_levelSet_generators_of_nonneg
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) {a : ℝ} (ha : 0 ≤ a) :
    ∃ s t : Finset E, s.Nonempty ∧
      levelSet (gaugeFunction C) a =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  by
    simpa [extendedConvexHull, closure_conicHull_finset] using
      (hC.levelSet_gaugeFunction_isClosedPolyhedral h0 a).exists_nonempty_generators_of_nonempty
        ((RW.levelSet_gaugeFunction_nonempty_iff_nonneg (C := C) (a := a)).2 ha)

/-- A gauge sublevel set of a closed polyhedral convex set containing `0` has
the standard finite convex-plus-conic coefficient formula. -/
theorem IsClosedPolyhedral.exists_gaugeFunction_levelSet_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) (a : ℝ) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ levelSet (gaugeFunction C) a ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  (hC.levelSet_gaugeFunction_isClosedPolyhedral h0 a).exists_generator_formula

/-- At nonnegative heights, the finite description of a gauge sublevel set can
be chosen with a nonempty ordinary generator set. -/
theorem IsClosedPolyhedral.exists_nonempty_gaugeFunction_levelSet_generator_formula_of_nonneg
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) {a : ℝ} (ha : 0 ≤ a) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ levelSet (gaugeFunction C) a ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  (hC.levelSet_gaugeFunction_isClosedPolyhedral h0 a).exists_nonempty_generator_formula_of_nonempty
    ((RW.levelSet_gaugeFunction_nonempty_iff_nonneg (C := C) (a := a)).2 ha)

theorem IsClosedPolyhedral.hasClosedPolyhedralEpigraph_gaugeFunction
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    HasClosedPolyhedralEpigraph (gaugeFunction C) := by
  change IsClosedPolyhedral (epigraph (gaugeFunction C))
  rw [← gaugeFunction_epigraph_eq_reflected_raySpaceCone hC.convex hC.isClosed h0]
  exact (hC.raySpaceCone_isClosedPolyhedral ⟨0, h0⟩).linear_image
    (gaugeEpigraphReflectMap (E := E))

theorem IsClosedPolyhedral.hasPolyhedralEpigraph_gaugeFunction
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    HasPolyhedralEpigraph (gaugeFunction C) :=
  (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).isPolyhedral

theorem IsClosedPolyhedral.isConvexPiecewiseLinear_gaugeFunction
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsConvexPiecewiseLinear (gaugeFunction C) :=
  ⟨isProper_gaugeFunction C, hC.hasClosedPolyhedralEpigraph_gaugeFunction h0⟩

theorem IsClosedPolyhedral.lowerSemicontinuous_gaugeFunction
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    LowerSemicontinuous (gaugeFunction C) :=
  RW.lowerSemicontinuous_gaugeFunction hC.convex hC.isClosed h0

theorem IsClosedPolyhedral.isClosed_epigraph_gaugeFunction
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsClosed (epigraph (gaugeFunction C)) :=
  RW.isClosed_epigraph_gaugeFunction hC.convex hC.isClosed h0

theorem IsClosedPolyhedral.sublinear_gaugeFunction
    {C : Set E} (hC : IsClosedPolyhedral C) :
    Sublinear (gaugeFunction C) :=
  RW.sublinear_gaugeFunction hC.convex

theorem IsClosedPolyhedral.horizonFunction_gaugeFunction_eq_self
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    horizonFunction (gaugeFunction C) = gaugeFunction C :=
  RW.horizonFunction_gaugeFunction_eq_self hC.convex hC.isClosed h0

/-- The gauge of a closed polyhedral cone is exactly its variational-analysis
indicator. -/
theorem IsClosedPolyhedral.gaugeFunction_eq_indicatorVA_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C) :
    gaugeFunction C = indicatorVA C :=
  RW.gaugeFunction_eq_indicatorVA_of_isClosed_convex_cone hC.convex hC.isClosed hCone

/-- On a closed polyhedral cone, the gauge vanishes exactly on the cone. -/
theorem IsClosedPolyhedral.gaugeFunction_eq_zero_iff_mem_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C) {x : E} :
    gaugeFunction C x = 0 ↔ x ∈ C :=
  RW.gaugeFunction_eq_zero_iff_mem_of_isClosed_convex_cone
    hC.convex hC.isClosed hCone

/-- Outside a closed polyhedral cone, the gauge is `⊤`. -/
theorem IsClosedPolyhedral.gaugeFunction_eq_top_iff_not_mem_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C) {x : E} :
    gaugeFunction C x = ⊤ ↔ x ∉ C :=
  RW.gaugeFunction_eq_top_iff_not_mem_of_isClosed_convex_cone
    hC.convex hC.isClosed hCone

/-- On a closed polyhedral cone, finiteness of the gauge is membership in the
cone. -/
theorem IsClosedPolyhedral.gaugeFunction_lt_top_iff_mem_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C) {x : E} :
    gaugeFunction C x < ⊤ ↔ x ∈ C :=
  RW.gaugeFunction_lt_top_iff_mem_of_isClosed_convex_cone
    hC.convex hC.isClosed hCone

/-- On a closed polyhedral cone, avoiding `⊤` is membership in the cone. -/
theorem IsClosedPolyhedral.gaugeFunction_ne_top_iff_mem_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C) {x : E} :
    gaugeFunction C x ≠ ⊤ ↔ x ∈ C :=
  RW.gaugeFunction_ne_top_iff_mem_of_isClosed_convex_cone
    hC.convex hC.isClosed hCone

/-- On a closed polyhedral cone, strict positivity of the gauge is nonmembership
in the cone. -/
theorem IsClosedPolyhedral.gaugeFunction_pos_iff_not_mem_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C) {x : E} :
    0 < gaugeFunction C x ↔ x ∉ C :=
  RW.gaugeFunction_pos_iff_not_mem_of_isClosed_convex_cone
    hC.convex hC.isClosed hCone

/-- The gauge epigraph of a closed polyhedral cone is the vertical
half-cylinder over the cone. -/
theorem IsClosedPolyhedral.epigraph_gaugeFunction_eq_prod_Ici_zero_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C) :
    epigraph (gaugeFunction C) = C ×ˢ Set.Ici (0 : ℝ) :=
  RW.epigraph_gaugeFunction_eq_prod_Ici_zero_of_isClosed_convex_cone
    hC.convex hC.isClosed hCone

/-- Nonnegative finite lower level sets of a closed-polyhedral cone gauge are
the cone itself. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_eq_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C)
    {a : ℝ} (ha : 0 ≤ a) :
    levelSet (gaugeFunction C) a = C :=
  RW.levelSet_gaugeFunction_eq_of_isClosed_convex_cone
    hC.convex hC.isClosed hCone ha

/-- Positive finite strict lower level sets of a closed-polyhedral cone gauge
are the cone itself. -/
theorem IsClosedPolyhedral.strictLevelSet_gaugeFunction_eq_of_isCone
    {C : Set E} (hC : IsClosedPolyhedral C) (hCone : IsCone C)
    {a : ℝ} (ha : 0 < a) :
    strictLevelSet (gaugeFunction C) a = C :=
  RW.strictLevelSet_gaugeFunction_eq_of_isClosed_convex_cone
    hC.convex hC.isClosed hCone ha

/-- The positive hull of a closed polyhedral set contains the origin. -/
theorem IsClosedPolyhedral.zero_mem_positiveHull
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    (0 : E) ∈ positiveHull C :=
  RW.zero_mem_positiveHull C

/-- A closed polyhedral set is contained in its positive hull. -/
theorem IsClosedPolyhedral.subset_positiveHull
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    C ⊆ positiveHull C :=
  RW.subset_positiveHull

/-- The positive hull of a closed polyhedral set is nonempty. -/
theorem IsClosedPolyhedral.positiveHull_nonempty
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    (positiveHull C).Nonempty :=
  RW.positiveHull_nonempty C

/-- The positive hull of a closed polyhedral set is a cone. -/
theorem IsClosedPolyhedral.positiveHull_isCone
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    IsCone (positiveHull C) :=
  RW.isCone_positiveHull

/-- The positive hull of a closed polyhedral set is convex. -/
theorem IsClosedPolyhedral.positiveHull_convex
    {C : Set E} (hC : IsClosedPolyhedral C) :
    Convex ℝ (positiveHull C) :=
  RW.convex_positiveHull hC.convex

/-- A closed-polyhedral cone is equal to its positive hull. -/
theorem IsClosedPolyhedral.positiveHull_eq_self_of_isCone
    {C : Set E} (_hC : IsClosedPolyhedral C) (hCone : IsCone C) :
    positiveHull C = C :=
  RW.positiveHull_eq_self hCone

/-- The positive hull operation is idempotent on closed polyhedral sets. -/
theorem IsClosedPolyhedral.positiveHull_idempotent
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    positiveHull (positiveHull C) = positiveHull C :=
  RW.positiveHull_idempotent C

/-- A closed polyhedral set is equal to its positive hull exactly when it is a
cone. -/
theorem IsClosedPolyhedral.positiveHull_eq_iff_isCone
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    positiveHull C = C ↔ IsCone C :=
  RW.positiveHull_eq_iff_isCone

/-- Positive hulls are monotone under inclusion of closed polyhedral sets. -/
theorem IsClosedPolyhedral.positiveHull_mono_of_subset
    {C D : Set E} (_hC : IsClosedPolyhedral C) (hCD : C ⊆ D) :
    positiveHull C ⊆ positiveHull D :=
  RW.positiveHull_mono hCD

/-- The positive hull is the smallest cone containing a closed polyhedral set. -/
theorem IsClosedPolyhedral.positiveHull_minimal_of_isCone
    {C K : Set E} (_hC : IsClosedPolyhedral C)
    (hK : IsCone K) (hCK : C ⊆ K) :
    positiveHull C ⊆ K :=
  RW.positiveHull_minimal hK hCK

/-- Positive hull containment in a cone is equivalent to containment of the
original closed polyhedral set. -/
theorem IsClosedPolyhedral.positiveHull_subset_iff_of_isCone
    {C K : Set E} (_hC : IsClosedPolyhedral C) (hK : IsCone K) :
    positiveHull C ⊆ K ↔ C ⊆ K :=
  RW.positiveHull_subset_iff hK

/-- The positive hull of a closed polyhedral set is `{0}` exactly when the set
itself is contained in `{0}`. -/
theorem IsClosedPolyhedral.positiveHull_eq_singleton_zero_iff
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    positiveHull C = ({0} : Set E) ↔ C ⊆ ({0} : Set E) :=
  RW.positiveHull_eq_singleton_zero_iff

/-- Adding the origin to a closed polyhedral set does not change its positive
hull. -/
theorem IsClosedPolyhedral.positiveHull_insert_zero
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    positiveHull (insert (0 : E) C) = positiveHull C :=
  RW.positiveHull_insert_zero C

/-- Positive hull turns unions into unions. -/
theorem IsClosedPolyhedral.positiveHull_union_eq_union
    {C D : Set E} (_hC : IsClosedPolyhedral C) (_hD : IsClosedPolyhedral D) :
    positiveHull (C ∪ D) = positiveHull C ∪ positiveHull D :=
  RW.positiveHull_union C D

/-- The positive hull of an intersection is contained in the intersection of
the positive hulls. -/
theorem IsClosedPolyhedral.positiveHull_inter_subset_inter
    {C D : Set E} (_hC : IsClosedPolyhedral C) (_hD : IsClosedPolyhedral D) :
    positiveHull (C ∩ D) ⊆ positiveHull C ∩ positiveHull D :=
  RW.positiveHull_inter_subset C D

/-- The ray-space cone with zero direction part projects to the positive hull
of a closed polyhedral set. -/
theorem IsClosedPolyhedral.fst_image_raySpaceCone_zero_eq_positiveHull
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    (LinearMap.fst ℝ E ℝ) '' raySpaceCone C ({0} : Set E) = positiveHull C :=
  RW.fst_image_raySpaceCone_zero_eq_positiveHull C

/-- The ray-space cone with horizon directions projects to the union of the
positive hull and the horizon cone. -/
theorem IsClosedPolyhedral.fst_image_raySpaceCone_horizon_eq
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    (LinearMap.fst ℝ E ℝ) '' raySpaceCone C (horizonCone C) =
      positiveHull C ∪ horizonCone C :=
  RW.fst_image_raySpaceCone_horizon_eq C

/-- Exercise `3.48(a)`: if a closed polyhedral set avoids the origin, the
closure of its positive hull is obtained by adjoining its horizon cone. -/
theorem IsClosedPolyhedral.closure_positiveHull_eq_union_horizonCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0C : (0 : E) ∉ C) :
    closure (positiveHull C) = positiveHull C ∪ horizonCone C :=
  RW.closure_positiveHull_eq_union_horizonCone hC.isClosed h0C

/-- Exercise `3.48(a)`, bounded case: the positive hull of a bounded closed
polyhedral set avoiding the origin is closed. -/
theorem IsClosedPolyhedral.isClosed_positiveHull_of_isBounded
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0C : (0 : E) ∉ C)
    (hCbdd : Bornology.IsBounded C) :
    IsClosed (positiveHull C) :=
  RW.isClosed_positiveHull_of_isClosed_of_isBounded hC.isClosed h0C hCbdd

/-- For bounded closed polyhedral sets avoiding `0`, the horizon directions
already lie in the positive hull. -/
theorem IsClosedPolyhedral.positiveHull_union_horizonCone_eq_self_of_isBounded
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0C : (0 : E) ∉ C)
    (hCbdd : Bornology.IsBounded C) :
    positiveHull C ∪ horizonCone C = positiveHull C := by
  rw [← hC.closure_positiveHull_eq_union_horizonCone h0C,
    closure_eq_iff_isClosed.mpr (hC.isClosed_positiveHull_of_isBounded h0C hCbdd)]

/-- Exercise `3.48(b)`: for a closed-polyhedral epigraph with positive finite
value at the origin, the closure of `epi (pos f)` is obtained by adjoining the
horizon epigraph. -/
theorem HasClosedPolyhedralEpigraph.closure_epigraph_positiveHullFunction_eq_union_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f)
    (h0pos : (0 : EReal) < f 0) (h0fin : f 0 < ⊤) :
    closure (epigraph (positiveHullFunction f)) =
      epigraph (positiveHullFunction f) ∪ epigraph (horizonFunction f) :=
  RW.closure_epigraph_positiveHullFunction_eq_union_horizonFunction
    hf.lowerSemicontinuous h0pos h0fin

set_option linter.style.longLine false in
/-- Function form of Exercise `3.48(b)` for closed-polyhedral epigraphs: the
closed epigraph attached to `pos f` is the epigraph of
`min (pos f) (f∞)`. -/
theorem HasClosedPolyhedralEpigraph.closure_epigraph_positiveHullFunction_eq_epigraph_min_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f)
    (h0pos : (0 : EReal) < f 0) (h0fin : f 0 < ⊤) :
    closure (epigraph (positiveHullFunction f)) =
      epigraph (fun x => min (positiveHullFunction f x) (horizonFunction f x)) :=
  RW.closure_epigraph_positiveHullFunction_eq_epigraph_min_horizonFunction
    hf.lowerSemicontinuous h0pos h0fin

/-- Exercise `3.48(b)`, closed-polyhedral lower-semicontinuity criterion for
the positive hull function. -/
theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_positiveHullFunction_of_le_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f)
    (h0pos : (0 : EReal) < f 0) (h0fin : f 0 < ⊤)
    (hph : positiveHullFunction f ≤ horizonFunction f) :
    LowerSemicontinuous (positiveHullFunction f) :=
  RW.lowerSemicontinuous_positiveHullFunction_of_le_horizonFunction
    hf.lowerSemicontinuous h0pos h0fin hph

/-- The perspective of a proper closed-polyhedral-epigraph function is
positively homogeneous. -/
theorem HasClosedPolyhedralEpigraph.positivelyHomogeneous_perspectiveFunction_of_isProper
    {f : E → EReal} (_hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) :
    PositivelyHomogeneous (perspectiveFunction f) :=
  RW.positivelyHomogeneous_perspectiveFunction hproper

/-- The perspective epigraph of a proper closed-polyhedral-epigraph function is
convex. -/
theorem HasClosedPolyhedralEpigraph.convex_epigraph_perspectiveFunction_of_isProper
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) :
    Convex ℝ (epigraph (perspectiveFunction f)) :=
  RW.convex_epigraph_perspectiveFunction hproper hf.convex

set_option linter.style.longLine false in
/-- For a proper closed-polyhedral-epigraph function, the closure of the
perspective epigraph is the closed-perspective epigraph. -/
theorem HasClosedPolyhedralEpigraph.closure_epigraph_perspectiveFunction_eq_epigraph_closedPerspectiveFunction_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    closure (epigraph (perspectiveFunction f)) =
      epigraph (closedPerspectiveFunction f) :=
  RW.closure_epigraph_perspectiveFunction_eq_epigraph_closedPerspectiveFunction
    hf.lowerSemicontinuous hproper

/-- The closed perspective of a proper closed-polyhedral-epigraph function is
lower semicontinuous. -/
theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_closedPerspectiveFunction_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    LowerSemicontinuous (closedPerspectiveFunction f) :=
  RW.lowerSemicontinuous_closedPerspectiveFunction hf.lowerSemicontinuous hproper

/-- Convex piecewise-linear specialization: perspectives are positively
homogeneous. -/
theorem IsConvexPiecewiseLinear.positivelyHomogeneous_perspectiveFunction
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) :
    PositivelyHomogeneous (perspectiveFunction f) :=
  hf.2.positivelyHomogeneous_perspectiveFunction_of_isProper hf.1

/-- Convex piecewise-linear specialization: perspective epigraphs are convex. -/
theorem IsConvexPiecewiseLinear.convex_epigraph_perspectiveFunction
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) :
    Convex ℝ (epigraph (perspectiveFunction f)) :=
  hf.2.convex_epigraph_perspectiveFunction_of_isProper hf.1

set_option linter.style.longLine false in
/-- Convex piecewise-linear specialization: the closed-perspective closure
formula. -/
theorem IsConvexPiecewiseLinear.closure_epigraph_perspectiveFunction_eq_epigraph_closedPerspectiveFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    closure (epigraph (perspectiveFunction f)) =
      epigraph (closedPerspectiveFunction f) :=
  hf.2.closure_epigraph_perspectiveFunction_eq_epigraph_closedPerspectiveFunction_of_isProper
    hf.1

/-- Convex piecewise-linear specialization: closed perspectives are lower
semicontinuous. -/
theorem IsConvexPiecewiseLinear.lowerSemicontinuous_closedPerspectiveFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    LowerSemicontinuous (closedPerspectiveFunction f) :=
  hf.2.lowerSemicontinuous_closedPerspectiveFunction_of_isProper hf.1

/-- Positive rescaling does not change the positive hull. -/
theorem IsClosedPolyhedral.positiveHull_smul_eq_of_pos
    {C : Set E} (_hC : IsClosedPolyhedral C) {a : ℝ} (ha : 0 < a) :
    positiveHull (a • C) = positiveHull C :=
  RW.positiveHull_smul_eq_of_pos ha

/-- Linear maps commute with positive hulls of closed polyhedral sets. -/
theorem IsClosedPolyhedral.linear_image_positiveHull
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {C : Set E} (_hC : IsClosedPolyhedral C) (L : E →ₗ[ℝ] F) :
    L '' positiveHull C = positiveHull (L '' C) :=
  RW.LinearMap.image_positiveHull L C

/-- Positive hulls of linear preimages map into positive hulls of the target
set. -/
theorem IsClosedPolyhedral.positiveHull_preimage_subset_linear_preimage
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {C : Set F} (L : E →ₗ[ℝ] F) (_hC : IsClosedPolyhedral C) :
    positiveHull (L ⁻¹' C) ⊆ L ⁻¹' positiveHull C :=
  RW.LinearMap.positiveHull_preimage_subset L C

/-- The effective domain of a closed-polyhedral gauge is its positive hull. -/
theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_eq_positiveHull
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    effectiveDomain (gaugeFunction C) = positiveHull C :=
  RW.effectiveDomain_gaugeFunction C

/-- The effective domain of a closed-polyhedral gauge is a cone. -/
theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_isCone
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    IsCone (effectiveDomain (gaugeFunction C)) := by
  rw [RW.effectiveDomain_gaugeFunction C]
  exact isCone_positiveHull

/-- The effective domain of a closed-polyhedral gauge is convex. -/
theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_convex
    {C : Set E} (hC : IsClosedPolyhedral C) :
    Convex ℝ (effectiveDomain (gaugeFunction C)) := by
  rw [RW.effectiveDomain_gaugeFunction C]
  exact convex_positiveHull hC.convex

/-- The effective domain of a closed-polyhedral gauge contains the origin. -/
theorem IsClosedPolyhedral.zero_mem_effectiveDomain_gaugeFunction
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    (0 : E) ∈ effectiveDomain (gaugeFunction C) := by
  rw [RW.effectiveDomain_gaugeFunction C]
  exact RW.zero_mem_positiveHull C

/-- The effective domain of a closed-polyhedral gauge is nonempty. -/
theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_nonempty
    {C : Set E} (hC : IsClosedPolyhedral C) :
    (effectiveDomain (gaugeFunction C)).Nonempty :=
  ⟨0, hC.zero_mem_effectiveDomain_gaugeFunction⟩

/-- Gauge functions of closed polyhedral sets are positively homogeneous. -/
theorem IsClosedPolyhedral.positivelyHomogeneous_gaugeFunction
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    PositivelyHomogeneous (gaugeFunction C) :=
  RW.positivelyHomogeneous_gaugeFunction C

/-- Gauge functions of closed polyhedral sets are nonnegative. -/
theorem IsClosedPolyhedral.nonneg_gaugeFunction
    {C : Set E} (_hC : IsClosedPolyhedral C) (x : E) :
    0 ≤ gaugeFunction C x :=
  RW.nonneg_gaugeFunction C x

/-- Gauge functions of closed polyhedral sets never take the value `⊥`. -/
theorem IsClosedPolyhedral.gaugeFunction_ne_bot
    {C : Set E} (_hC : IsClosedPolyhedral C) (x : E) :
    gaugeFunction C x ≠ ⊥ :=
  RW.gaugeFunction_ne_bot C x

/-- The gauge of a closed polyhedral set vanishes at the origin. -/
@[simp] theorem IsClosedPolyhedral.gaugeFunction_zero_eq_zero
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    gaugeFunction C 0 = 0 :=
  RW.gaugeFunction_zero C

/-- Gauges are antitone with respect to inclusion of closed polyhedral base
sets. -/
theorem IsClosedPolyhedral.gaugeFunction_antitone_of_subset
    {C D : Set E} (_hC : IsClosedPolyhedral C) (hCD : C ⊆ D) :
    gaugeFunction D ≤ gaugeFunction C :=
  RW.gaugeFunction_antitone hCD

/-- Gauge sublevel sets grow when the closed polyhedral base set grows. -/
theorem IsClosedPolyhedral.levelSet_gaugeFunction_mono_of_subset
    {C D : Set E} (_hC : IsClosedPolyhedral C) (hCD : C ⊆ D) (a : ℝ) :
    levelSet (gaugeFunction C) a ⊆ levelSet (gaugeFunction D) a :=
  RW.levelSet_gaugeFunction_mono_of_subset hCD a

/-- Strict gauge sublevel sets grow when the closed polyhedral base set grows. -/
theorem IsClosedPolyhedral.strictLevelSet_gaugeFunction_mono_of_subset
    {C D : Set E} (_hC : IsClosedPolyhedral C) (hCD : C ⊆ D) (a : ℝ) :
    strictLevelSet (gaugeFunction C) a ⊆ strictLevelSet (gaugeFunction D) a :=
  RW.strictLevelSet_gaugeFunction_mono_of_subset hCD a

/-- Effective domains of closed-polyhedral gauges are monotone under inclusion
of the base sets. -/
theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_mono_of_subset
    {C D : Set E} (_hC : IsClosedPolyhedral C) (hCD : C ⊆ D) :
    effectiveDomain (gaugeFunction C) ⊆ effectiveDomain (gaugeFunction D) :=
  RW.effectiveDomain_gaugeFunction_mono hCD

/-- For a closed-polyhedral gauge, finite values are exactly the points in the
positive hull. -/
theorem IsClosedPolyhedral.gaugeFunction_lt_top_iff_mem_positiveHull
    {C : Set E} (_hC : IsClosedPolyhedral C) {x : E} :
    gaugeFunction C x < ⊤ ↔ x ∈ positiveHull C :=
  RW.gaugeFunction_lt_top_iff_mem_positiveHull

/-- For a closed-polyhedral gauge, avoiding `⊤` is exactly membership in the
positive hull. -/
theorem IsClosedPolyhedral.gaugeFunction_ne_top_iff_mem_positiveHull
    {C : Set E} (_hC : IsClosedPolyhedral C) {x : E} :
    gaugeFunction C x ≠ ⊤ ↔ x ∈ positiveHull C :=
  RW.gaugeFunction_ne_top_iff_mem_positiveHull

/-- For a closed-polyhedral gauge, value `⊤` is exactly nonmembership in the
positive hull. -/
theorem IsClosedPolyhedral.gaugeFunction_eq_top_iff_not_mem_positiveHull
    {C : Set E} (_hC : IsClosedPolyhedral C) {x : E} :
    gaugeFunction C x = ⊤ ↔ x ∉ positiveHull C :=
  RW.gaugeFunction_eq_top_iff_not_mem_positiveHull

/-- The effective domain of the gauge of a closed-polyhedral cone is the cone
itself. -/
theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_eq_of_isCone
    {C : Set E} (_hC : IsClosedPolyhedral C) (hCone : IsCone C) :
    effectiveDomain (gaugeFunction C) = C :=
  RW.effectiveDomain_gaugeFunction_eq_of_isCone hCone

/-- The conic hull of the positive hull of a closed polyhedral set is the
positive hull itself. -/
theorem IsClosedPolyhedral.conicHull_positiveHull_eq_self
    {C : Set E} (hC : IsClosedPolyhedral C) :
    conicHull (positiveHull C) = positiveHull C :=
  calc
    conicHull (positiveHull C) = positiveHull (positiveHull C) :=
      RW.conicHull_eq_positiveHull_of_convex (convex_positiveHull hC.convex)
    _ = positiveHull C := positiveHull_eq_self isCone_positiveHull

/-- The conic hull of the effective domain of a closed-polyhedral gauge is
the effective domain itself. -/
theorem IsClosedPolyhedral.conicHull_effectiveDomain_gaugeFunction_eq_self
    {C : Set E} (hC : IsClosedPolyhedral C) :
    conicHull (effectiveDomain (gaugeFunction C)) =
      effectiveDomain (gaugeFunction C) :=
  RW.conicHull_effectiveDomain_gaugeFunction_eq_self_of_convex hC.convex

/-- The horizon cone of the positive hull of a closed polyhedral set is the
closure of that positive hull. -/
theorem IsClosedPolyhedral.horizonCone_positiveHull_eq_closure
    {C : Set E} (hC : IsClosedPolyhedral C) :
    horizonCone (positiveHull C) = closure (positiveHull C) :=
  RW.horizonCone_positiveHull_eq_closure_of_convex hC.convex

/-- The horizon cone of the gauge effective domain is the closure of that
effective domain. -/
theorem IsClosedPolyhedral.horizonCone_effectiveDomain_gaugeFunction_eq_closure
    {C : Set E} (hC : IsClosedPolyhedral C) :
    horizonCone (effectiveDomain (gaugeFunction C)) =
      closure (effectiveDomain (gaugeFunction C)) :=
  RW.horizonCone_effectiveDomain_gaugeFunction_eq_closure_of_convex hC.convex

/-- Finiteness everywhere for the closed-polyhedral gauge is equivalent to
full positive hull. -/
theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_eq_univ_iff
    {C : Set E} (_hC : IsClosedPolyhedral C) :
    effectiveDomain (gaugeFunction C) = Set.univ ↔ positiveHull C = Set.univ :=
  RW.effectiveDomain_gaugeFunction_eq_univ_iff C

/-- If `0` lies in the interior of a closed polyhedral set, its positive hull
is the whole space. -/
theorem IsClosedPolyhedral.positiveHull_eq_univ_of_mem_interior_zero
    {C : Set E} (_hC : IsClosedPolyhedral C) (h0int : (0 : E) ∈ interior C) :
    positiveHull C = Set.univ :=
  RW.positiveHull_eq_univ_of_mem_interior_zero h0int

/-- Interior containment of the origin makes the closed-polyhedral gauge finite
everywhere. -/
theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_eq_univ_of_mem_interior_zero
    {C : Set E} (_hC : IsClosedPolyhedral C) (h0int : (0 : E) ∈ interior C) :
    effectiveDomain (gaugeFunction C) = Set.univ :=
  RW.effectiveDomain_gaugeFunction_eq_univ_of_mem_interior_zero h0int

/-- Full positive hull and symmetry make a closed polyhedral convex set
absorbent. -/
theorem IsClosedPolyhedral.absorbent_of_positiveHull_eq_univ_of_symmetric
    {C : Set E} (hC : IsClosedPolyhedral C)
    (hpos : positiveHull C = Set.univ) (h0 : (0 : E) ∈ C)
    (hsym : ∀ ⦃x : E⦄, x ∈ C → -x ∈ C) :
    Absorbent ℝ C :=
  RW.absorbent_of_positiveHull_eq_univ_of_convex_of_zero_mem_of_symmetric
    hpos hC.convex h0 hsym

/-- The real-valued Minkowski gauge of a closed polyhedral absorbent set is
lower semicontinuous. -/
theorem IsClosedPolyhedral.lowerSemicontinuous_gauge_of_absorbent
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (hAbs : Absorbent ℝ C) :
    LowerSemicontinuous (gauge C) :=
  RW.lowerSemicontinuous_gauge_of_isClosed hC.convex hC.isClosed h0 hAbs

/-- Symmetric closed polyhedral sets have even gauges. -/
theorem IsClosedPolyhedral.gaugeFunction_neg_eq_of_symmetric
    {C : Set E} (_hC : IsClosedPolyhedral C)
    (hsym : ∀ ⦃x : E⦄, x ∈ C → -x ∈ C) (x : E) :
    gaugeFunction C (-x) = gaugeFunction C x :=
  RW.gaugeFunction_neg_eq_of_symmetric hsym x

/-- Evenness of the closed-polyhedral gauge recovers symmetry of the set from
its unit sublevel description. -/
theorem IsClosedPolyhedral.symmetric_of_gaugeFunction_neg_eq
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (heven : ∀ x : E, gaugeFunction C (-x) = gaugeFunction C x) :
    ∀ ⦃x : E⦄, x ∈ C → -x ∈ C :=
  RW.symmetric_of_gaugeFunction_neg_eq hC.convex hC.isClosed h0 heven

/-- Evenness of a closed-polyhedral gauge is equivalent to symmetry of the
underlying set. -/
theorem IsClosedPolyhedral.gaugeFunction_neg_eq_iff_symmetric
    {C : Set E} (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    (∀ x : E, gaugeFunction C (-x) = gaugeFunction C x) ↔
      (∀ ⦃x : E⦄, x ∈ C → -x ∈ C) :=
  RW.gaugeFunction_neg_eq_iff_symmetric hC.convex hC.isClosed h0

/-- Positive-definiteness of the gauge forces boundedness of the underlying
closed polyhedral set. -/
theorem IsClosedPolyhedral.isBounded_of_gaugeFunction_eq_zero_iff
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (hzero : ∀ x : E, gaugeFunction C x = 0 ↔ x = 0) :
    Bornology.IsBounded C :=
  RW.isBounded_of_gaugeFunction_eq_zero_iff hC.convex hC.isClosed h0 hzero

/-- For closed polyhedral sets containing `0`, boundedness is equivalent to
positive-definiteness of the gauge in equality form. -/
theorem IsClosedPolyhedral.isBounded_iff_gaugeFunction_eq_zero_iff
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    Bornology.IsBounded C ↔ ∀ x : E, gaugeFunction C x = 0 ↔ x = 0 :=
  RW.isBounded_iff_gaugeFunction_eq_zero_iff hC.convex hC.isClosed h0

/-- For closed polyhedral sets containing `0`, boundedness is equivalent to
strict positivity of the gauge away from the origin. -/
theorem IsClosedPolyhedral.isBounded_iff_gaugeFunction_pos_iff_ne_zero
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    Bornology.IsBounded C ↔ ∀ x : E, 0 < gaugeFunction C x ↔ x ≠ 0 :=
  RW.isBounded_iff_gaugeFunction_pos_iff_ne_zero hC.convex hC.isClosed h0

set_option linter.style.longLine false in
/-- Under boundedness, interior containment of `0`, and symmetry, a closed
polyhedral gauge has the expected norm-like package of properties. -/
theorem IsClosedPolyhedral.gaugeFunction_has_norm_properties_of_isBounded_of_mem_interior_zero_of_symmetric
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0int : (0 : E) ∈ interior C)
    (hsym : ∀ ⦃x : E⦄, x ∈ C → -x ∈ C) (hCbdd : Bornology.IsBounded C) :
    effectiveDomain (gaugeFunction C) = Set.univ ∧
      LowerSemicontinuous (gaugeFunction C) ∧
      Sublinear (gaugeFunction C) ∧
      (∀ x : E, gaugeFunction C (-x) = gaugeFunction C x) ∧
      (∀ x : E, gaugeFunction C x = 0 ↔ x = 0) ∧
      levelSet (gaugeFunction C) 1 = C :=
  RW.gaugeFunction_has_norm_properties_of_isBounded_of_mem_interior_zero_of_symmetric
    hC.convex hC.isClosed h0int hsym hCbdd

/-- Evenness and positive-definiteness of the closed-polyhedral gauge recover
symmetry and boundedness of the underlying set. -/
theorem IsClosedPolyhedral.symmetric_and_isBounded_of_gaugeFunction_norm_properties
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (heven : ∀ x : E, gaugeFunction C (-x) = gaugeFunction C x)
    (hzero : ∀ x : E, gaugeFunction C x = 0 ↔ x = 0) :
    (∀ ⦃x : E⦄, x ∈ C → -x ∈ C) ∧ Bornology.IsBounded C :=
  RW.symmetric_and_isBounded_of_gaugeFunction_norm_properties
    hC.convex hC.isClosed h0 heven hzero

/-- If a closed-polyhedral gauge is finite everywhere and the underlying set is
symmetric, then `0` lies in the interior. -/
theorem IsClosedPolyhedral.mem_interior_zero_of_effectiveDomain_gaugeFunction_eq_univ_of_symmetric
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (hdom : effectiveDomain (gaugeFunction C) = Set.univ)
    (hsym : ∀ ⦃x : E⦄, x ∈ C → -x ∈ C) :
    (0 : E) ∈ interior C :=
  RW.mem_interior_zero_of_effectiveDomain_gaugeFunction_eq_univ_of_symmetric
    hC.convex hC.isClosed h0 hdom hsym

/-- If the closed-polyhedral gauge is finite everywhere and even, then `0` is
an interior point of the set. -/
theorem IsClosedPolyhedral.mem_interior_zero_of_gaugeFunction_norm_properties
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C)
    (hdom : effectiveDomain (gaugeFunction C) = Set.univ)
    (heven : ∀ x : E, gaugeFunction C (-x) = gaugeFunction C x) :
    (0 : E) ∈ interior C :=
  RW.mem_interior_zero_of_gaugeFunction_norm_properties
    hC.convex hC.isClosed h0 hdom heven

/-- Closed-polyhedral version of Example 3.50's gauge norm-property
equivalence. -/
theorem IsClosedPolyhedral.gaugeFunction_has_norm_properties_iff
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    (effectiveDomain (gaugeFunction C) = Set.univ ∧
      LowerSemicontinuous (gaugeFunction C) ∧
      Sublinear (gaugeFunction C) ∧
      (∀ x : E, gaugeFunction C (-x) = gaugeFunction C x) ∧
      (∀ x : E, gaugeFunction C x = 0 ↔ x = 0) ∧
      levelSet (gaugeFunction C) 1 = C) ↔
    ((0 : E) ∈ interior C ∧
      (∀ ⦃x : E⦄, x ∈ C → -x ∈ C) ∧
      Bornology.IsBounded C) :=
  RW.gaugeFunction_has_norm_properties_iff hC.convex hC.isClosed h0

theorem IsClosedPolyhedral.exists_gaugeFunction_epigraph_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ s t : Finset (E × ℝ),
      epigraph (gaugeFunction C) =
        convexHull ℝ (↑s : Set (E × ℝ)) +
          closure (conicHull (↑t : Set (E × ℝ))) :=
  (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).exists_generators

theorem IsClosedPolyhedral.exists_nonempty_gaugeFunction_epigraph_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      epigraph (gaugeFunction C) =
        extendedConvexHull (↑s : Set (E × ℝ)) (↑t : Set (E × ℝ)) :=
  (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).exists_nonempty_generators_of_isProper
    (isProper_gaugeFunction C)

theorem IsClosedPolyhedral.exists_gaugeFunction_epigraph_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ s t : Finset (E × ℝ),
      ∀ {x : E} {a : ℝ},
        (x, a) ∈ epigraph (gaugeFunction C) ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, a) :=
  (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).exists_epigraph_generator_formula

theorem IsClosedPolyhedral.exists_nonempty_gaugeFunction_epigraph_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ s t : Finset (E × ℝ), s.Nonempty ∧
      ∀ {x : E} {a : ℝ},
        (x, a) ∈ epigraph (gaugeFunction C) ↔
          ∃ w : (E × ℝ) → ℝ,
            (∀ p ∈ s, 0 ≤ w p) ∧
            ∑ p ∈ s, w p = 1 ∧
            ∃ c : (E × ℝ) →₀ ℝ,
              ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
              (∀ p, 0 ≤ c p) ∧
              (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, a) :=
  let hg : HasClosedPolyhedralEpigraph (gaugeFunction C) :=
    hC.hasClosedPolyhedralEpigraph_gaugeFunction h0
  hg.exists_nonempty_epigraph_generator_formula_of_isProper (isProper_gaugeFunction C)

/-- The horizon cone of the gauge epigraph of a closed polyhedral set is closed
polyhedral. -/
theorem IsClosedPolyhedral.horizonCone_gaugeFunction_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsClosedPolyhedral (horizonCone (epigraph (gaugeFunction C))) :=
  (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).horizonCone_epigraph_isClosedPolyhedral
    (epigraph_nonempty_of_isProper (isProper_gaugeFunction C))

/-- The horizon cone of the gauge epigraph of a closed polyhedral set is
finitely generated. -/
theorem IsClosedPolyhedral.horizonCone_gaugeFunction_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsFinitelyGeneratedCone (horizonCone (epigraph (gaugeFunction C))) :=
  (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).horizonCone_epigraph_isFinitelyGeneratedCone
    (epigraph_nonempty_of_isProper (isProper_gaugeFunction C))

/-- The horizon cone of the gauge epigraph has finite conic generators. -/
theorem IsClosedPolyhedral.exists_horizonCone_gaugeFunction_epigraph_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ t : Finset (E × ℝ),
      horizonCone (epigraph (gaugeFunction C)) =
        conicHull (↑t : Set (E × ℝ)) :=
  HasClosedPolyhedralEpigraph.exists_horizonCone_epigraph_generators_of_isProper
    (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0) (isProper_gaugeFunction C)

/-- The horizon cone of the gauge epigraph has the finite conic-coefficient
formula. -/
theorem IsClosedPolyhedral.exists_horizonCone_gaugeFunction_epigraph_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ t : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ horizonCone (epigraph (gaugeFunction C)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  let hg : HasClosedPolyhedralEpigraph (gaugeFunction C) :=
    hC.hasClosedPolyhedralEpigraph_gaugeFunction h0
  hg.exists_horizonCone_epigraph_generator_formula_of_isProper (isProper_gaugeFunction C)

/-- The ray-space cone of the gauge epigraph is finitely generated. -/
theorem IsClosedPolyhedral.raySpaceCone_gaugeFunction_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsFinitelyGeneratedCone
      (raySpaceCone (epigraph (gaugeFunction C))
        (horizonCone (epigraph (gaugeFunction C)))) :=
  (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).raySpaceCone_epigraph_isFinitelyGeneratedCone
    (epigraph_nonempty_of_isProper (isProper_gaugeFunction C))

/-- The ray-space cone of the gauge epigraph is closed polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_gaugeFunction_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsClosedPolyhedral
      (raySpaceCone (epigraph (gaugeFunction C))
        (horizonCone (epigraph (gaugeFunction C)))) :=
  (hC.raySpaceCone_gaugeFunction_epigraph_isFinitelyGeneratedCone h0).isClosedPolyhedral

/-- The ray-space cone of the gauge epigraph is polyhedral. -/
theorem IsClosedPolyhedral.raySpaceCone_gaugeFunction_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsPolyhedral
      (raySpaceCone (epigraph (gaugeFunction C))
        (horizonCone (epigraph (gaugeFunction C)))) :=
  (hC.raySpaceCone_gaugeFunction_epigraph_isFinitelyGeneratedCone h0).isPolyhedral

/-- The ray-space cone of the gauge epigraph has finite conic generators. -/
theorem IsClosedPolyhedral.exists_raySpaceCone_gaugeFunction_epigraph_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      raySpaceCone (epigraph (gaugeFunction C))
          (horizonCone (epigraph (gaugeFunction C))) =
        conicHull (↑u : Set ((E × ℝ) × ℝ)) :=
  HasClosedPolyhedralEpigraph.exists_raySpaceCone_epigraph_generators_of_isProper
    (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0) (isProper_gaugeFunction C)

/-- The ray-space cone of the gauge epigraph has the finite conic-coefficient
formula. -/
theorem IsClosedPolyhedral.exists_raySpaceCone_gaugeFunction_epigraph_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ u : Finset ((E × ℝ) × ℝ),
      ∀ {p : (E × ℝ) × ℝ},
        p ∈ raySpaceCone (epigraph (gaugeFunction C))
            (horizonCone (epigraph (gaugeFunction C))) ↔
          ∃ c : ((E × ℝ) × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set ((E × ℝ) × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  let hg : HasClosedPolyhedralEpigraph (gaugeFunction C) :=
    hC.hasClosedPolyhedralEpigraph_gaugeFunction h0
  hg.exists_raySpaceCone_epigraph_generator_formula_of_isProper (isProper_gaugeFunction C)

theorem IsClosedPolyhedral.positiveHull_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsClosedPolyhedral (positiveHull C) := by
  rw [← effectiveDomain_gaugeFunction C]
  exact (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).effectiveDomain_isClosedPolyhedral

theorem IsClosedPolyhedral.positiveHull_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsPolyhedral (positiveHull C) :=
  (hC.positiveHull_isClosedPolyhedral h0).isPolyhedral

theorem IsClosedPolyhedral.positiveHull_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsFinitelyGeneratedCone (positiveHull C) :=
  (hC.positiveHull_isClosedPolyhedral h0).isFinitelyGeneratedCone_of_isCone
    (isCone_positiveHull (C := C))

theorem IsClosedPolyhedral.exists_positiveHull_conicHull_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ t : Finset E, positiveHull C = conicHull (↑t : Set E) :=
  (hC.positiveHull_isFinitelyGeneratedCone h0).exists_generators

theorem IsClosedPolyhedral.exists_positiveHull_conicGenerator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ t : Finset E,
      ∀ {x : E},
        x ∈ positiveHull C ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = x :=
  (hC.positiveHull_isFinitelyGeneratedCone h0).exists_generator_formula

theorem IsClosedPolyhedral.horizonCone_positiveHull_eq_self
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    horizonCone (positiveHull C) = positiveHull C :=
  (hC.positiveHull_isFinitelyGeneratedCone h0).horizonCone_eq_self

theorem IsClosedPolyhedral.raySpaceCone_positiveHull_horizon_eq_self
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    raySpaceCone (positiveHull C) (horizonCone (positiveHull C)) =
      raySpaceCone (positiveHull C) (positiveHull C) := by
  rw [hC.horizonCone_positiveHull_eq_self h0]

theorem IsClosedPolyhedral.raySpaceCone_positiveHull_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsFinitelyGeneratedCone
      (raySpaceCone (positiveHull C) (horizonCone (positiveHull C))) :=
  (hC.positiveHull_isClosedPolyhedral h0).isFinitelyGeneratedCone_raySpaceCone
    ⟨0, RW.zero_mem_positiveHull C⟩

theorem IsClosedPolyhedral.raySpaceCone_positiveHull_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsClosedPolyhedral
      (raySpaceCone (positiveHull C) (horizonCone (positiveHull C))) :=
  (hC.raySpaceCone_positiveHull_isFinitelyGeneratedCone h0).isClosedPolyhedral

theorem IsClosedPolyhedral.raySpaceCone_positiveHull_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsPolyhedral
      (raySpaceCone (positiveHull C) (horizonCone (positiveHull C))) :=
  (hC.raySpaceCone_positiveHull_isFinitelyGeneratedCone h0).isPolyhedral

theorem IsClosedPolyhedral.exists_raySpaceCone_positiveHull_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (positiveHull C) (horizonCone (positiveHull C)) =
        conicHull (↑u : Set (E × ℝ)) :=
  (hC.raySpaceCone_positiveHull_isFinitelyGeneratedCone h0).exists_generators

theorem IsClosedPolyhedral.exists_raySpaceCone_positiveHull_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (positiveHull C) (horizonCone (positiveHull C)) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  (hC.raySpaceCone_positiveHull_isFinitelyGeneratedCone h0).exists_generator_formula

theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsClosedPolyhedral (effectiveDomain (gaugeFunction C)) := by
  rw [effectiveDomain_gaugeFunction C]
  exact hC.positiveHull_isClosedPolyhedral h0

theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsPolyhedral (effectiveDomain (gaugeFunction C)) :=
  (hC.effectiveDomain_gaugeFunction_isClosedPolyhedral h0).isPolyhedral

theorem IsClosedPolyhedral.effectiveDomain_gaugeFunction_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsFinitelyGeneratedCone (effectiveDomain (gaugeFunction C)) := by
  rw [effectiveDomain_gaugeFunction C]
  exact hC.positiveHull_isFinitelyGeneratedCone h0

theorem IsClosedPolyhedral.exists_effectiveDomain_gaugeFunction_conicHull_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ t : Finset E,
      effectiveDomain (gaugeFunction C) = conicHull (↑t : Set E) :=
  (hC.effectiveDomain_gaugeFunction_isFinitelyGeneratedCone h0).exists_generators

theorem IsClosedPolyhedral.exists_effectiveDomain_gaugeFunction_conicGenerator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain (gaugeFunction C) ↔
          ∃ c : E →₀ ℝ,
            ↑c.support ⊆ (↑t : Set E) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = x :=
  (hC.effectiveDomain_gaugeFunction_isFinitelyGeneratedCone h0).exists_generator_formula

theorem IsClosedPolyhedral.horizonCone_effectiveDomain_gaugeFunction_eq_self
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    horizonCone (effectiveDomain (gaugeFunction C)) =
      effectiveDomain (gaugeFunction C) :=
  (hC.effectiveDomain_gaugeFunction_isFinitelyGeneratedCone h0).horizonCone_eq_self

theorem IsClosedPolyhedral.raySpaceCone_effectiveDomain_gaugeFunction_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsFinitelyGeneratedCone
      (raySpaceCone (effectiveDomain (gaugeFunction C))
        (horizonCone (effectiveDomain (gaugeFunction C)))) :=
  (hC.effectiveDomain_gaugeFunction_isClosedPolyhedral h0).isFinitelyGeneratedCone_raySpaceCone
    ⟨0, by rw [RW.effectiveDomain_gaugeFunction C]; exact RW.zero_mem_positiveHull C⟩

theorem IsClosedPolyhedral.raySpaceCone_effectiveDomain_gaugeFunction_isClosedPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsClosedPolyhedral
      (raySpaceCone (effectiveDomain (gaugeFunction C))
        (horizonCone (effectiveDomain (gaugeFunction C)))) :=
  (hC.raySpaceCone_effectiveDomain_gaugeFunction_isFinitelyGeneratedCone h0).isClosedPolyhedral

theorem IsClosedPolyhedral.raySpaceCone_effectiveDomain_gaugeFunction_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    IsPolyhedral
      (raySpaceCone (effectiveDomain (gaugeFunction C))
        (horizonCone (effectiveDomain (gaugeFunction C)))) :=
  (hC.raySpaceCone_effectiveDomain_gaugeFunction_isFinitelyGeneratedCone h0).isPolyhedral

theorem IsClosedPolyhedral.exists_raySpaceCone_effectiveDomain_gaugeFunction_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ u : Finset (E × ℝ),
      raySpaceCone (effectiveDomain (gaugeFunction C))
          (horizonCone (effectiveDomain (gaugeFunction C))) =
        conicHull (↑u : Set (E × ℝ)) :=
  (hC.raySpaceCone_effectiveDomain_gaugeFunction_isFinitelyGeneratedCone h0).exists_generators

theorem IsClosedPolyhedral.exists_raySpaceCone_effectiveDomain_gaugeFunction_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ u : Finset (E × ℝ),
      ∀ {p : E × ℝ},
        p ∈ raySpaceCone (effectiveDomain (gaugeFunction C))
            (horizonCone (effectiveDomain (gaugeFunction C))) ↔
          ∃ c : (E × ℝ) →₀ ℝ,
            ↑c.support ⊆ (↑u : Set (E × ℝ)) ∧
            (∀ y, 0 ≤ c y) ∧
            c.sum (fun y r => r • y) = p :=
  IsFinitelyGeneratedCone.exists_generator_formula
    (hC.raySpaceCone_effectiveDomain_gaugeFunction_isFinitelyGeneratedCone h0)

theorem IsClosedPolyhedral.exists_positiveHull_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ s t : Finset E,
      positiveHull C = extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  rcases (hC.hasClosedPolyhedralEpigraph_gaugeFunction h0).exists_effectiveDomain_generators with
    ⟨s, t, hst⟩
  rw [effectiveDomain_gaugeFunction C] at hst
  exact ⟨s, t, hst⟩

theorem IsClosedPolyhedral.exists_nonempty_positiveHull_generators
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ s t : Finset E, s.Nonempty ∧
      positiveHull C = extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hg : HasClosedPolyhedralEpigraph (gaugeFunction C) :=
    hC.hasClosedPolyhedralEpigraph_gaugeFunction h0
  rcases hg.exists_nonempty_effectiveDomain_generators_of_isProper (isProper_gaugeFunction C) with
    ⟨s, t, hs, hst⟩
  rw [effectiveDomain_gaugeFunction C] at hst
  exact ⟨s, t, hs, hst⟩

theorem IsClosedPolyhedral.exists_positiveHull_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ positiveHull C ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hg : HasClosedPolyhedralEpigraph (gaugeFunction C) :=
    hC.hasClosedPolyhedralEpigraph_gaugeFunction h0
  rcases hg.exists_effectiveDomain_generator_formula with
    ⟨s, t, hst⟩
  rw [effectiveDomain_gaugeFunction C] at hst
  exact ⟨s, t, hst⟩

theorem IsClosedPolyhedral.exists_nonempty_positiveHull_generator_formula
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (h0 : (0 : E) ∈ C) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ positiveHull C ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hg : HasClosedPolyhedralEpigraph (gaugeFunction C) :=
    hC.hasClosedPolyhedralEpigraph_gaugeFunction h0
  rcases
      hg.exists_nonempty_effectiveDomain_generator_formula_of_isProper
        (isProper_gaugeFunction C) with
    ⟨s, t, hs, hst⟩
  rw [effectiveDomain_gaugeFunction C] at hst
  exact ⟨s, t, hs, hst⟩

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    HasClosedPolyhedralEpigraph (horizonFunction f) := by
  have hhorizon : IsClosedPolyhedral (horizonCone (epigraph f)) :=
    IsClosedPolyhedral.horizonCone_isClosedPolyhedral (C := epigraph f) hf hne
  exact (show IsClosedPolyhedral (epigraph (horizonFunction f)) from by
    rw [epigraph_horizonFunction_eq_horizonCone_epigraph hne]
    exact hhorizon)

/-- Properness supplies epigraph nonemptiness for the horizon-function
closed-polyhedral epigraph theorem. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_horizonFunction_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    HasClosedPolyhedralEpigraph (horizonFunction f) :=
  hf.hasClosedPolyhedralEpigraph_horizonFunction
    (epigraph_nonempty_of_isProper hproper)

/-- The horizon function of a closed-polyhedral-epigraph function has a
polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.hasPolyhedralEpigraph_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    HasPolyhedralEpigraph (horizonFunction f) :=
  (hf.hasClosedPolyhedralEpigraph_horizonFunction hne).isPolyhedral

/-- Properness supplies epigraph nonemptiness for the horizon-function
polyhedral epigraph theorem. -/
theorem HasClosedPolyhedralEpigraph.hasPolyhedralEpigraph_horizonFunction_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    HasPolyhedralEpigraph (horizonFunction f) :=
  hf.hasPolyhedralEpigraph_horizonFunction
    (epigraph_nonempty_of_isProper hproper)

/-- The horizon function of a closed-polyhedral-epigraph function has a closed
polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsClosedPolyhedral (epigraph (horizonFunction f)) :=
  hf.hasClosedPolyhedralEpigraph_horizonFunction hne

/-- The horizon function of a closed-polyhedral-epigraph function has a
polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsPolyhedral (epigraph (horizonFunction f)) :=
  (hf.horizonFunction_epigraph_isClosedPolyhedral hne).isPolyhedral

/-- The epigraph of the horizon function of a closed-polyhedral-epigraph
function is a finitely generated cone. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsFinitelyGeneratedCone (epigraph (horizonFunction f)) := by
  simpa [epigraph_horizonFunction_eq_horizonCone_epigraph hne] using
    hf.horizonCone_epigraph_isFinitelyGeneratedCone hne

/-- Properness supplies epigraph nonemptiness for the closed-polyhedral
horizon-function epigraph theorem. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_epigraph_isClosedPolyhedral_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsClosedPolyhedral (epigraph (horizonFunction f)) :=
  hf.horizonFunction_epigraph_isClosedPolyhedral
    (epigraph_nonempty_of_isProper hproper)

/-- Properness supplies epigraph nonemptiness for the polyhedral
horizon-function epigraph theorem. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_epigraph_isPolyhedral_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsPolyhedral (epigraph (horizonFunction f)) :=
  hf.horizonFunction_epigraph_isPolyhedral
    (epigraph_nonempty_of_isProper hproper)

/-- Properness supplies epigraph nonemptiness for finite generation of the
horizon-function epigraph. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_epigraph_fgCone_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsFinitelyGeneratedCone (epigraph (horizonFunction f)) :=
  hf.horizonFunction_epigraph_isFinitelyGeneratedCone
    (epigraph_nonempty_of_isProper hproper)

/-- The ray-space cone of the horizon-function epigraph is finitely generated. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsFinitelyGeneratedCone
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  (hf.horizonFunction_epigraph_isFinitelyGeneratedCone hne).raySpaceCone_of_isCone
    (isCone_epigraph_horizonFunction f)

/-- Properness supplies epigraph nonemptiness for finite generation of the
horizon-function epigraph ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_fgCone_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsFinitelyGeneratedCone
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  hf.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone
    (epigraph_nonempty_of_isProper hproper)

/-- The horizon-function epigraph ray-space cone is polyhedral. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsPolyhedral
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  (hf.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone hne).isPolyhedral

/-- The horizon-function epigraph ray-space cone is closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    IsClosedPolyhedral
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  (hf.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone hne).isClosedPolyhedral

/-- Properness supplies epigraph nonemptiness for polyhedrality of the
horizon-function epigraph ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isPolyhedral_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsPolyhedral
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  hf.raySpaceCone_horizonFunction_epigraph_isPolyhedral
    (epigraph_nonempty_of_isProper hproper)

set_option linter.style.longLine false in
/-- Properness supplies epigraph nonemptiness for closed polyhedrality of the
horizon-function epigraph ray-space cone. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isClosedPolyhedral_of_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsClosedPolyhedral
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  hf.raySpaceCone_horizonFunction_epigraph_isClosedPolyhedral
    (epigraph_nonempty_of_isProper hproper)

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

/-- The horizon function of a convex piecewise-linear function has a
polyhedral epigraph. -/
theorem IsConvexPiecewiseLinear.hasPolyhedralEpigraph_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    HasPolyhedralEpigraph (horizonFunction f) :=
  hf.hasClosedPolyhedralEpigraph_horizonFunction.isPolyhedral

/-- The horizon function of a convex piecewise-linear function has a closed
polyhedral epigraph. -/
theorem IsConvexPiecewiseLinear.horizonFunction_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral (epigraph (horizonFunction f)) :=
  hf.hasClosedPolyhedralEpigraph_horizonFunction

/-- The horizon function of a convex piecewise-linear function has a
polyhedral epigraph. -/
theorem IsConvexPiecewiseLinear.horizonFunction_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsPolyhedral (epigraph (horizonFunction f)) :=
  hf.horizonFunction_epigraph_isClosedPolyhedral.isPolyhedral

/-- The horizon-function epigraph of a convex piecewise-linear function is a
finitely generated cone. -/
theorem IsConvexPiecewiseLinear.horizonFunction_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsFinitelyGeneratedCone (epigraph (horizonFunction f)) :=
  hf.hasClosedPolyhedralEpigraph.horizonFunction_epigraph_isFinitelyGeneratedCone
    (epigraph_nonempty_of_isProper hf.isProper)

/-- The horizon-function epigraph ray-space cone of a convex piecewise-linear
function is finitely generated. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsFinitelyGeneratedCone
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isFinitelyGeneratedCone
    (epigraph_nonempty_of_isProper hf.isProper)

/-- The horizon-function epigraph ray-space cone of a convex piecewise-linear
function is polyhedral. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_horizonFunction_epigraph_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsPolyhedral
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isPolyhedral
    (epigraph_nonempty_of_isProper hf.isProper)

/-- The horizon-function epigraph ray-space cone of a convex piecewise-linear
function is closed polyhedral. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_horizonFunction_epigraph_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral
      (raySpaceCone (epigraph (horizonFunction f)) (epigraph (horizonFunction f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_epigraph_isClosedPolyhedral
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
proper function is polyhedral. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_effectiveDomain_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsPolyhedral (effectiveDomain (horizonFunction f)) :=
  (hf.horizonFunction_effectiveDomain_isClosedPolyhedral hproper).isPolyhedral

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

/-- The ray-space cone of the horizon-function effective domain is
polyhedral. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_effectiveDomain_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsPolyhedral
      (raySpaceCone (effectiveDomain (horizonFunction f))
        (effectiveDomain (horizonFunction f))) :=
  (hf.raySpaceCone_horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    hproper).isPolyhedral

/-- The ray-space cone of the horizon-function effective domain is closed
polyhedral. -/
theorem HasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsClosedPolyhedral
      (raySpaceCone (effectiveDomain (horizonFunction f))
        (effectiveDomain (horizonFunction f))) :=
  (hf.raySpaceCone_horizonFunction_effectiveDomain_isFinitelyGeneratedCone
    hproper).isClosedPolyhedral

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
function is polyhedral. -/
theorem IsConvexPiecewiseLinear.horizonFunction_effectiveDomain_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsPolyhedral (effectiveDomain (horizonFunction f)) :=
  hf.horizonFunction_effectiveDomain_isClosedPolyhedral.isPolyhedral

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

/-- The ray-space cone of the horizon-function effective domain is polyhedral
for a convex piecewise-linear function. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_horizonFunction_effectiveDomain_isPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsPolyhedral
      (raySpaceCone (effectiveDomain (horizonFunction f))
        (effectiveDomain (horizonFunction f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_effectiveDomain_isPolyhedral
    hf.isProper

/-- The ray-space cone of the horizon-function effective domain is closed
polyhedral for a convex piecewise-linear function. -/
theorem IsConvexPiecewiseLinear.raySpaceCone_horizonFunction_effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral
      (raySpaceCone (effectiveDomain (horizonFunction f))
        (effectiveDomain (horizonFunction f))) :=
  hf.hasClosedPolyhedralEpigraph.raySpaceCone_horizonFunction_effectiveDomain_isClosedPolyhedral
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

end RW
