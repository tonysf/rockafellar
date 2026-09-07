/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Polars of Polyhedral Cones, and Normals to Polyhedral Sets

Lemma 6.45 (Farkas) and the normal cone half of Theorem 6.46.

6.45 says the polar of `K = {x | ⟨aᵢ, x⟩ ≤ 0}` is the cone of nonnegative
combinations `y₁a₁ + ⋯ + yₘaₘ`.  The proof is the book's: that cone is
finitely generated, hence closed by Chapter 3's Minkowski--Weyl development;
its own polar is `K`, which is elementary; and the bipolar theorem of 6.21
closes the loop.

6.46's normal cone formula then follows from the tangent cone formula of
[`PolyhedralTangents.lean`](RockafellarWets/Chapter6/PolyhedralTangents.lean),
since a polyhedral set is convex, so its normal cone is the polar of its
tangent cone.
-/

import RockafellarWets.Chapter6.PolyhedralTangents
import RockafellarWets.Chapter6.ClarkeRegularityCharacterizations

open Set
open scoped InnerProductSpace

namespace RW

section NonnegCombinations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cone of nonnegative combinations `y₁a₁ + ⋯ + yₘaₘ` of Lemma 6.45. -/
def nonnegCombinationCone {m : ℕ} (a : Fin m → E) : Set E :=
  {v : E | ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i • a i = v}

@[simp]
theorem mem_nonnegCombinationCone {m : ℕ} {a : Fin m → E} {v : E} :
    v ∈ nonnegCombinationCone a ↔
      ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i • a i = v := Iff.rfl

theorem self_mem_nonnegCombinationCone {m : ℕ} (a : Fin m → E) (i : Fin m) :
    a i ∈ nonnegCombinationCone a := by
  classical
  refine ⟨fun j ↦ if j = i then 1 else 0, fun j ↦ by positivity, ?_⟩
  simp

theorem isCone_nonnegCombinationCone {m : ℕ} (a : Fin m → E) :
    IsCone (nonnegCombinationCone a) := by
  constructor
  · exact ⟨fun _ ↦ 0, fun _ ↦ le_rfl, by simp⟩
  · rintro v ⟨y, hy, rfl⟩ c hc
    refine ⟨fun i ↦ c * y i, fun i ↦ mul_nonneg hc.le (hy i), ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ mul_smul c (y i) (a i)

theorem convex_nonnegCombinationCone {m : ℕ} (a : Fin m → E) :
    Convex ℝ (nonnegCombinationCone a) := by
  rintro v ⟨y, hy, rfl⟩ w ⟨z, hz, rfl⟩ s t hs ht _
  refine ⟨fun i ↦ s * y i + t * z i,
    fun i ↦ add_nonneg (mul_nonneg hs (hy i)) (mul_nonneg ht (hz i)), ?_⟩
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [add_smul, mul_smul, mul_smul]

/-- The elementary half of Lemma 6.45: the polar of the cone of nonnegative
combinations is cut out by the generating inequalities. -/
theorem polarCone_nonnegCombinationCone {m : ℕ} (a : Fin m → E) :
    polarCone (nonnegCombinationCone a) = {v : E | ∀ i, ⟪v, a i⟫_ℝ ≤ 0} := by
  ext v
  constructor
  · intro hv i
    exact hv _ (self_mem_nonnegCombinationCone a i)
  · rintro hv _ ⟨y, hy, rfl⟩
    rw [inner_sum]
    refine Finset.sum_nonpos fun i _ ↦ ?_
    rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (hy i) (hv i)

/-- The cone of nonnegative combinations is the conic hull of the generators,
hence finitely generated. -/
theorem nonnegCombinationCone_eq_conicHull {m : ℕ} (a : Fin m → E) :
    nonnegCombinationCone a = conicHull (Set.range a) := by
  classical
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hconv := convex_conicHull (Set.range a)
    have hcone := isCone_conicHull (Set.range a)
    have hstep : ∀ s : Finset (Fin m),
        ∑ i ∈ s, y i • a i ∈ conicHull (Set.range a) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hcone.1
      | insert j s hj ih =>
          rw [Finset.sum_insert hj]
          exact add_mem_of_convex_isCone hconv hcone
            (hcone.smul_mem (subset_conicHull ⟨j, rfl⟩) (hy j)) ih
    exact hstep Finset.univ
  · refine conicHull_minimal (convex_nonnegCombinationCone a)
      (isCone_nonnegCombinationCone a) ?_
    rintro _ ⟨i, rfl⟩
    exact self_mem_nonnegCombinationCone a i

theorem isFinitelyGeneratedCone_nonnegCombinationCone {m : ℕ} (a : Fin m → E) :
    IsFinitelyGeneratedCone (nonnegCombinationCone a) := by
  classical
  refine ⟨Finset.image a Finset.univ, ?_⟩
  rw [nonnegCombinationCone_eq_conicHull]
  congr 1
  simp

/-- The generators active at `x̄`, with the inactive ones replaced by `0`. -/
noncomputable def activeVectors {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (x : E) :
    Fin m → E :=
  open scoped Classical in fun i ↦ if ⟪a i, x⟫_ℝ = b i then a i else 0

/-- The tangent cone description of 6.46, in the vector form the book prints:
the active cone is cut out by the inequalities of the active generators. -/
theorem activeTangentCone_innerSL_eq {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (x : E) :
    activeTangentCone (fun i ↦ innerSL ℝ (a i)) b x
      = {w : E | ∀ i, ⟪w, activeVectors a b x i⟫_ℝ ≤ 0} := by
  classical
  ext w
  simp only [mem_activeTangentCone, mem_setOf_eq, activeVectors, innerSL_apply_apply]
  constructor
  · intro h i
    by_cases hi : ⟪a i, x⟫_ℝ = b i
    · rw [if_pos hi, real_inner_comm]
      exact h i hi
    · rw [if_neg hi]
      simp
  · intro h i hi
    have hw := h i
    rw [if_pos hi, real_inner_comm] at hw
    exact hw

end NonnegCombinations

section PolyhedralNormals

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isClosed_nonnegCombinationCone {m : ℕ} (a : Fin m → E) :
    IsClosed (nonnegCombinationCone a) :=
  (isFinitelyGeneratedCone_nonnegCombinationCone a).isClosedPolyhedral.isClosed

/-- **Lemma 6.45** (Farkas): the polar of a cone cut out by finitely many
homogeneous inequalities is the cone of nonnegative combinations of the
defining vectors. -/
theorem polarCone_setOf_inner_nonpos {m : ℕ} (a : Fin m → E) :
    polarCone {v : E | ∀ i, ⟪v, a i⟫_ℝ ≤ 0} = nonnegCombinationCone a := by
  rw [← polarCone_nonnegCombinationCone a]
  exact polarCone_bipolar_eq_self (isClosed_nonnegCombinationCone a)
    (convex_nonnegCombinationCone a) (isCone_nonnegCombinationCone a)

/-- **Theorem 6.46**, the normal cone formula: relative to a description of a
polyhedral set by finitely many linear inequalities, the normal cone at `x̄`
is generated by the vectors active at `x̄`. -/
theorem normalCone_linearInequalitySet_innerSL {m : ℕ} (a : Fin m → E)
    (b : Fin m → ℝ) {x : E}
    (hx : x ∈ linearInequalitySet (fun i ↦ innerSL ℝ (a i)) b) :
    normalCone (linearInequalitySet (fun i ↦ innerSL ℝ (a i)) b) x
      = nonnegCombinationCone (activeVectors a b x) := by
  have hconv : Convex ℝ (linearInequalitySet (fun i ↦ innerSL ℝ (a i)) b) :=
    IsHPolyhedral.convex ⟨m, _, b, rfl⟩
  rw [normalCone_eq_regularNormalCone_of_convex hconv hx,
    regularNormalCone_eq_polarCone_tangentCone hx,
    tangentCone_linearInequalitySet _ b hx, activeTangentCone_innerSL_eq,
    polarCone_setOf_inner_nonpos]

/-- **Theorem 6.46**: the normal cone to a polyhedral set is polyhedral. -/
theorem isHPolyhedralCone_normalCone_linearInequalitySet {m : ℕ} (a : Fin m → E)
    (b : Fin m → ℝ) {x : E}
    (hx : x ∈ linearInequalitySet (fun i ↦ innerSL ℝ (a i)) b) :
    IsHPolyhedralCone
      (normalCone (linearInequalitySet (fun i ↦ innerSL ℝ (a i)) b) x) := by
  rw [normalCone_linearInequalitySet_innerSL a b hx]
  exact (isFinitelyGeneratedCone_nonnegCombinationCone _).isHPolyhedralCone

end PolyhedralNormals

end RW
