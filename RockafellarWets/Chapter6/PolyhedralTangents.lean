/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents to Polyhedral Sets

Exercise 6.47 and the tangent cone half of Theorem 6.46.

For `C = {x | ⟨aᵢ, x⟩ ≤ αᵢ, i = 1, …, m}` and `x̄ ∈ C`, write `I(x̄)` for the
active index set.  Two sets are attached to `x̄`: the cone
`{w | ⟨aᵢ, w⟩ ≤ 0 for i ∈ I(x̄)}` and the polyhedron
`{y | ⟨aᵢ, y⟩ ≤ αᵢ for i ∈ I(x̄)}` obtained by discarding the inactive
constraints.  The second is exactly `x̄` plus the first, and it agrees with `C`
throughout the open set where the inactive constraints stay inactive.

That single observation carries both results, and it reverses the book's
order: 6.47 is proved first, directly, and the tangent cone formula of 6.46
is then read off it by the locality of the tangent cone, rather than the
other way round.  Nothing here needs an inner product, a nearest-point
argument, or finite dimension; only the `H`-description of Chapter 3G* is
used, and finite dimension enters solely to convert a finitely generated
polyhedron into that description by Minkowski--Weyl.
-/

import RockafellarWets.Chapter3.MinkowskiWeyl
import RockafellarWets.Chapter6.ChangeOfCoordinates

open Filter Set Topology

namespace RW

section PolyhedralTangents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cone cut out by the constraints active at `x̄`: Theorem 6.46's formula
for `T_C(x̄)`. -/
def activeTangentCone {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ) (x : E) :
    Set E := {w : E | ∀ i, A i x = b i → A i w ≤ 0}

@[simp]
theorem mem_activeTangentCone {m : ℕ} {A : Fin m → (E →L[ℝ] ℝ)} {b : Fin m → ℝ}
    {x w : E} : w ∈ activeTangentCone A b x ↔ ∀ i, A i x = b i → A i w ≤ 0 :=
  Iff.rfl

/-- The polyhedron obtained by discarding the constraints inactive at `x̄`. -/
def activeConstraintSet {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ) (x : E) :
    Set E := {y : E | ∀ i, A i x = b i → A i y ≤ b i}

@[simp]
theorem mem_activeConstraintSet {m : ℕ} {A : Fin m → (E →L[ℝ] ℝ)} {b : Fin m → ℝ}
    {x y : E} : y ∈ activeConstraintSet A b x ↔ ∀ i, A i x = b i → A i y ≤ b i :=
  Iff.rfl

theorem mem_activeConstraintSet_self {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ))
    (b : Fin m → ℝ) (x : E) : x ∈ activeConstraintSet A b x := fun _ hi ↦ hi.le

/-- The active polyhedron is `x̄` translated by the active cone. -/
theorem activeConstraintSet_eq_image_add {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ))
    (b : Fin m → ℝ) (x : E) :
    activeConstraintSet A b x = (fun w ↦ x + w) '' activeTangentCone A b x := by
  ext y
  constructor
  · intro hy
    refine ⟨y - x, fun i hi ↦ ?_, by module⟩
    have h := hy i hi
    rw [map_sub, hi]
    linarith
  · rintro ⟨w, hw, rfl⟩
    intro i hi
    have h := hw i hi
    rw [map_add, hi]
    linarith

/-- The active cone is an `H`-polyhedral cone: the inactive functionals are
replaced by `0`, whose homogeneous inequality is vacuous. -/
theorem isHPolyhedralCone_activeTangentCone {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ))
    (b : Fin m → ℝ) (x : E) : IsHPolyhedralCone (activeTangentCone A b x) := by
  classical
  refine ⟨m, fun i ↦ if A i x = b i then A i else 0, ?_⟩
  ext w
  simp only [mem_homogeneousLinearInequalitySet, mem_activeTangentCone]
  constructor
  · intro h i
    by_cases hi : A i x = b i
    · rw [if_pos hi]
      exact h i hi
    · rw [if_neg hi]
      simp
  · intro h i hi
    have hw := h i
    rwa [if_pos hi] at hw

/-- The open set on which the constraints inactive at `x̄` stay inactive. -/
def inactiveRegion {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ) (x : E) :
    Set E := {y : E | ∀ i, A i x ≠ b i → A i y < b i}

theorem isOpen_inactiveRegion {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ)
    (x : E) : IsOpen (inactiveRegion A b x) := by
  have hset : inactiveRegion A b x
      = ⋂ i : Fin m, {y : E | A i x ≠ b i → A i y < b i} := by
    ext y
    simp [inactiveRegion]
  rw [hset]
  refine isOpen_iInter_of_finite fun i ↦ ?_
  by_cases hi : A i x = b i
  · have huniv : {y : E | A i x ≠ b i → A i y < b i} = univ := by
      ext y
      simp [hi]
    rw [huniv]
    exact isOpen_univ
  · have hlt : {y : E | A i x ≠ b i → A i y < b i} = {y : E | A i y < b i} := by
      ext y
      simp [hi]
    rw [hlt]
    exact isOpen_lt (A i).continuous continuous_const

theorem inactiveRegion_mem_nhds {m : ℕ} {A : Fin m → (E →L[ℝ] ℝ)} {b : Fin m → ℝ}
    {x : E} (hx : x ∈ linearInequalitySet A b) : inactiveRegion A b x ∈ nhds x := by
  refine (isOpen_inactiveRegion A b x).mem_nhds fun i hi ↦ ?_
  exact lt_of_le_of_ne (hx i) hi

/-- The constraint set and its active part agree wherever the inactive
constraints stay inactive. -/
theorem linearInequalitySet_inter_inactiveRegion {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ))
    (b : Fin m → ℝ) (x : E) :
    linearInequalitySet A b ∩ inactiveRegion A b x
      = activeConstraintSet A b x ∩ inactiveRegion A b x := by
  ext y
  constructor
  · rintro ⟨hy, hyV⟩
    exact ⟨fun i _ ↦ hy i, hyV⟩
  · rintro ⟨hy, hyV⟩
    refine ⟨fun i ↦ ?_, hyV⟩
    by_cases hi : A i x = b i
    · exact hy i hi
    · exact (hyV i hi).le

/-- The tangent cone to the active polyhedron is the active cone.  The hard
half is elementary here: the whole ray `x̄ + λw`, `λ > 0`, lies in the active
polyhedron once `w` lies in the active cone. -/
theorem tangentCone_activeConstraintSet {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ))
    (b : Fin m → ℝ) (x : E) :
    tangentCone (activeConstraintSet A b x) x = activeTangentCone A b x := by
  refine Subset.antisymm ?_ ?_
  · rintro w ⟨xs, τs, hxC, -, hτpos, -, hq⟩ i hi
    have hle : ∀ n, A i ((τs n)⁻¹ • (xs n - x)) ≤ 0 := by
      intro n
      have h1 : A i (xs n) ≤ b i := hxC n i hi
      have h2 : A i (xs n) - A i x ≤ 0 := by rw [hi]; linarith
      have h3 : (τs n)⁻¹ * (A i (xs n) - A i x) ≤ (τs n)⁻¹ * 0 :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (hτpos n).le)
      rw [map_smul, map_sub, smul_eq_mul]
      linarith
    have htend : Tendsto (fun n ↦ A i ((τs n)⁻¹ • (xs n - x))) atTop (nhds (A i w)) :=
      ((A i).continuous.tendsto w).comp hq
    exact le_of_tendsto htend (Eventually.of_forall hle)
  · intro w hw
    refine mem_tangentCone_of_forall (xs := fun n ↦ x + (1 / ((n : ℝ) + 1)) • w)
      (τs := fun n ↦ 1 / ((n : ℝ) + 1)) (fun n ↦ ?_) (fun n ↦ by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat ?_
    · intro i hi
      have hc : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      have h := hw i hi
      have hmul : 1 / ((n : ℝ) + 1) * A i w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc h
      rw [map_add, hi, map_smul, smul_eq_mul]
      linarith
    · have heq : ∀ n : ℕ,
          (1 / ((n : ℝ) + 1))⁻¹ • (x + (1 / ((n : ℝ) + 1)) • w - x) = w := by
        intro n
        have hne : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hne, one_smul]
      exact tendsto_const_nhds.congr fun n ↦ (heq n).symm

/-- **Theorem 6.46**, the tangent cone formula: relative to any description of
`C` by finitely many linear inequalities, `T_C(x̄)` is cut out by the
constraints active at `x̄`. -/
theorem tangentCone_linearInequalitySet {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ))
    (b : Fin m → ℝ) {x : E} (hx : x ∈ linearInequalitySet A b) :
    tangentCone (linearInequalitySet A b) x = activeTangentCone A b x := by
  have hV := inactiveRegion_mem_nhds hx
  calc
    tangentCone (linearInequalitySet A b) x
        = tangentCone (linearInequalitySet A b ∩ inactiveRegion A b x) x :=
      (tangentCone_inter_nhds hV).symm
    _ = tangentCone (activeConstraintSet A b x ∩ inactiveRegion A b x) x := by
      rw [linearInequalitySet_inter_inactiveRegion]
    _ = tangentCone (activeConstraintSet A b x) x := tangentCone_inter_nhds hV
    _ = activeTangentCone A b x := tangentCone_activeConstraintSet A b x

/-- **Theorem 6.46**: the tangent cone to a polyhedral set is polyhedral. -/
theorem isHPolyhedralCone_tangentCone {m : ℕ} (A : Fin m → (E →L[ℝ] ℝ))
    (b : Fin m → ℝ) {x : E} (hx : x ∈ linearInequalitySet A b) :
    IsHPolyhedralCone (tangentCone (linearInequalitySet A b) x) := by
  rw [tangentCone_linearInequalitySet A b hx]
  exact isHPolyhedralCone_activeTangentCone A b x

/-- **Exercise 6.47**, for a description by finitely many linear inequalities:
the tangent approximation is exact near `x̄`. -/
theorem exists_nhds_inter_eq_add_tangentCone_linearInequalitySet {m : ℕ}
    (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ) {x : E}
    (hx : x ∈ linearInequalitySet A b) :
    ∃ V ∈ nhds x, linearInequalitySet A b ∩ V
      = ((fun w ↦ x + w) '' tangentCone (linearInequalitySet A b) x) ∩ V := by
  refine ⟨inactiveRegion A b x, inactiveRegion_mem_nhds hx, ?_⟩
  rw [linearInequalitySet_inter_inactiveRegion, tangentCone_linearInequalitySet A b hx,
    ← activeConstraintSet_eq_image_add]

/-- **Exercise 6.47**: a polyhedral set coincides with its tangent
approximation near any of its points. -/
theorem IsHPolyhedral.exists_nhds_inter_eq_add_tangentCone {C : Set E}
    (hC : IsHPolyhedral C) {x : E} (hx : x ∈ C) :
    ∃ V ∈ nhds x, C ∩ V = ((fun w ↦ x + w) '' tangentCone C x) ∩ V := by
  obtain ⟨m, A, b, rfl⟩ := hC
  exact exists_nhds_inter_eq_add_tangentCone_linearInequalitySet A b hx

/-- **Exercise 6.47** for a finitely generated polyhedron, through
Minkowski--Weyl. -/
theorem IsPolyhedral.exists_nhds_inter_eq_add_tangentCone [FiniteDimensional ℝ E]
    {C : Set E} (hC : IsPolyhedral C) {x : E} (hx : x ∈ C) :
    ∃ V ∈ nhds x, C ∩ V = ((fun w ↦ x + w) '' tangentCone C x) ∩ V :=
  (isHPolyhedral_iff_isPolyhedral.2 hC).exists_nhds_inter_eq_add_tangentCone hx

/-- **Theorem 6.46** for a finitely generated polyhedron: the tangent cone is
polyhedral. -/
theorem IsPolyhedral.isHPolyhedralCone_tangentCone [FiniteDimensional ℝ E]
    {C : Set E} (hC : IsPolyhedral C) {x : E} (hx : x ∈ C) :
    IsHPolyhedralCone (tangentCone C x) := by
  obtain ⟨m, A, b, rfl⟩ := isHPolyhedral_iff_isPolyhedral.2 hC
  exact RW.isHPolyhedralCone_tangentCone A b hx

end PolyhedralTangents

end RW
