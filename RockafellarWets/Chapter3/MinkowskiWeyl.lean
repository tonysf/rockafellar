/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: The H-side of Minkowski--Weyl

This file introduces the finite-halfspace (`H`) description of polyhedral
sets and cones.  The finite-generation (`V`) description is
`RW.IsPolyhedral` and `RW.IsFinitelyGeneratedCone`, respectively, from
`GeneratedSets`.

The definitions here deliberately use continuous linear functionals.  This
makes closedness available without a finite-dimensional assumption and makes
preimages under arbitrary continuous linear maps immediate.  In finite
dimensions, the corresponding statement for arbitrary linear maps follows
because every linear map is continuous.
-/

import RockafellarWets.Chapter3.GeneratedSets
import Mathlib.Tactic.Module

open Set

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The solution set of a finite family of continuous-linear inequalities
`A i x ≤ b i`. -/
def linearInequalitySet {m : ℕ}
    (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ) : Set E :=
  {x | ∀ i, A i x ≤ b i}

@[simp] theorem mem_linearInequalitySet {m : ℕ}
    {A : Fin m → (E →L[ℝ] ℝ)} {b : Fin m → ℝ} {x : E} :
    x ∈ linearInequalitySet A b ↔ ∀ i, A i x ≤ b i :=
  Iff.rfl

theorem linearInequalitySet_eq_iInter {m : ℕ}
    (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ) :
    linearInequalitySet A b = ⋂ i, (A i) ⁻¹' Set.Iic (b i) := by
  ext x
  simp [linearInequalitySet]

/-- The solution set of a finite family of homogeneous continuous-linear
inequalities `A i x ≤ 0`. -/
def homogeneousLinearInequalitySet {m : ℕ}
    (A : Fin m → (E →L[ℝ] ℝ)) : Set E :=
  linearInequalitySet A 0

@[simp] theorem mem_homogeneousLinearInequalitySet {m : ℕ}
    {A : Fin m → (E →L[ℝ] ℝ)} {x : E} :
    x ∈ homogeneousLinearInequalitySet A ↔ ∀ i, A i x ≤ 0 := by
  simp [homogeneousLinearInequalitySet]

/-- A set is `H`-polyhedral if it is the solution set of finitely many
continuous-linear inequalities. -/
def IsHPolyhedral (C : Set E) : Prop :=
  ∃ (m : ℕ) (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ),
    C = linearInequalitySet A b

/-- A cone is `H`-polyhedral if it is the solution set of finitely many
homogeneous continuous-linear inequalities. -/
def IsHPolyhedralCone (K : Set E) : Prop :=
  ∃ (m : ℕ) (A : Fin m → (E →L[ℝ] ℝ)),
    K = homogeneousLinearInequalitySet A

theorem isHPolyhedral_iff_exists_inequalities {C : Set E} :
    IsHPolyhedral C ↔
      ∃ (m : ℕ) (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ),
        C = linearInequalitySet A b :=
  Iff.rfl

theorem isHPolyhedralCone_iff_exists_homogeneous_inequalities {K : Set E} :
    IsHPolyhedralCone K ↔
      ∃ (m : ℕ) (A : Fin m → (E →L[ℝ] ℝ)),
        K = homogeneousLinearInequalitySet A :=
  Iff.rfl

theorem IsHPolyhedral.linearInequalitySet {m : ℕ}
    (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ) :
    IsHPolyhedral (linearInequalitySet A b) :=
  ⟨m, A, b, rfl⟩

theorem IsHPolyhedralCone.homogeneousLinearInequalitySet {m : ℕ}
    (A : Fin m → (E →L[ℝ] ℝ)) :
    IsHPolyhedralCone (homogeneousLinearInequalitySet A) :=
  ⟨m, A, rfl⟩

/-- Membership wrapper exposing a finite inequality description. -/
theorem IsHPolyhedral.exists_mem_iff {C : Set E} (hC : IsHPolyhedral C) :
    ∃ (m : ℕ) (A : Fin m → (E →L[ℝ] ℝ)) (b : Fin m → ℝ),
      ∀ x, x ∈ C ↔ ∀ i, A i x ≤ b i := by
  rcases hC with ⟨m, A, b, rfl⟩
  exact ⟨m, A, b, fun _ => Iff.rfl⟩

/-- Membership wrapper exposing a finite homogeneous inequality
description. -/
theorem IsHPolyhedralCone.exists_mem_iff {K : Set E}
    (hK : IsHPolyhedralCone K) :
    ∃ (m : ℕ) (A : Fin m → (E →L[ℝ] ℝ)),
      ∀ x, x ∈ K ↔ ∀ i, A i x ≤ 0 := by
  rcases hK with ⟨m, A, rfl⟩
  exact ⟨m, A, fun _ => mem_homogeneousLinearInequalitySet⟩

theorem IsHPolyhedral.halfspace (a : E →L[ℝ] ℝ) (b : ℝ) :
    IsHPolyhedral {x | a x ≤ b} := by
  refine ⟨1, fun _ => a, fun _ => b, ?_⟩
  ext x
  constructor
  · intro hx i
    simpa using hx
  · intro hx
    simpa using hx (0 : Fin 1)

theorem IsHPolyhedralCone.homogeneousHalfspace (a : E →L[ℝ] ℝ) :
    IsHPolyhedralCone {x | a x ≤ 0} := by
  refine ⟨1, fun _ => a, ?_⟩
  ext x
  constructor
  · intro hx i
    simpa using hx
  · intro hx
    simpa using hx (0 : Fin 1)

theorem IsHPolyhedral.empty : IsHPolyhedral (∅ : Set E) := by
  refine ⟨1, fun _ => 0, fun _ => -1, ?_⟩
  ext x
  simp

theorem IsHPolyhedral.univ : IsHPolyhedral (Set.univ : Set E) := by
  refine ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  ext x
  simp

theorem IsHPolyhedralCone.univ : IsHPolyhedralCone (Set.univ : Set E) := by
  refine ⟨0, fun i => Fin.elim0 i, ?_⟩
  ext x
  simp

theorem IsHPolyhedral.inter {C D : Set E}
    (hC : IsHPolyhedral C) (hD : IsHPolyhedral D) :
    IsHPolyhedral (C ∩ D) := by
  rcases hC with ⟨m, A, b, rfl⟩
  rcases hD with ⟨n, B, d, rfl⟩
  refine
    ⟨m + n, Fin.addCases A B, Fin.addCases b d, ?_⟩
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using hxA j
    · intro j
      simpa only [Fin.addCases_right] using hxB j
  · intro hx
    constructor
    · intro i
      simpa only [Fin.addCases_left] using hx (Fin.castAdd n i)
    · intro i
      simpa only [Fin.addCases_right] using hx (Fin.natAdd m i)

theorem IsHPolyhedralCone.inter {K L : Set E}
    (hK : IsHPolyhedralCone K) (hL : IsHPolyhedralCone L) :
    IsHPolyhedralCone (K ∩ L) := by
  rcases hK with ⟨m, A, rfl⟩
  rcases hL with ⟨n, B, rfl⟩
  refine ⟨m + n, Fin.addCases A B, ?_⟩
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left, Pi.zero_apply] using hxA j
    · intro j
      simpa only [Fin.addCases_right, Pi.zero_apply] using hxB j
  · intro hx
    constructor
    · intro i
      simpa only [Fin.addCases_left, Pi.zero_apply] using hx (Fin.castAdd n i)
    · intro i
      simpa only [Fin.addCases_right, Pi.zero_apply] using hx (Fin.natAdd m i)

/-! Finite intersections are the native closure operation on the `H` side. -/

theorem IsHPolyhedral.iInter_finset {ι : Type*} (s : Finset ι)
    (C : ι → Set E) (hC : ∀ i ∈ s, IsHPolyhedral (C i)) :
    IsHPolyhedral (⋂ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (IsHPolyhedral.univ : IsHPolyhedral (Set.univ : Set E))
  | @insert a s ha ih =>
      have haC : IsHPolyhedral (C a) := hC a (Finset.mem_insert_self a s)
      have hsC : IsHPolyhedral (⋂ i ∈ s, C i) :=
        ih fun i hi => hC i (Finset.mem_insert_of_mem hi)
      simpa [ha] using haC.inter hsC

theorem IsHPolyhedralCone.iInter_finset {ι : Type*} (s : Finset ι)
    (K : ι → Set E) (hK : ∀ i ∈ s, IsHPolyhedralCone (K i)) :
    IsHPolyhedralCone (⋂ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (IsHPolyhedralCone.univ : IsHPolyhedralCone (Set.univ : Set E))
  | @insert a s ha ih =>
      have haK : IsHPolyhedralCone (K a) :=
        hK a (Finset.mem_insert_self a s)
      have hsK : IsHPolyhedralCone (⋂ i ∈ s, K i) :=
        ih fun i hi => hK i (Finset.mem_insert_of_mem hi)
      simpa [ha] using haK.inter hsK

section Preimages

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `H`-polyhedrality is preserved by preimages under arbitrary continuous
linear maps; no injectivity or surjectivity is required. -/
theorem IsHPolyhedral.continuousLinear_preimage {C : Set E}
    (hC : IsHPolyhedral C) (L : F →L[ℝ] E) :
    IsHPolyhedral (L ⁻¹' C) := by
  rcases hC with ⟨m, A, b, rfl⟩
  refine ⟨m, fun i => (A i).comp L, b, ?_⟩
  rfl

/-- Homogeneous `H`-polyhedrality is preserved by preimages under arbitrary
continuous linear maps. -/
theorem IsHPolyhedralCone.continuousLinear_preimage {K : Set E}
    (hK : IsHPolyhedralCone K) (L : F →L[ℝ] E) :
    IsHPolyhedralCone (L ⁻¹' K) := by
  rcases hK with ⟨m, A, rfl⟩
  refine ⟨m, fun i => (A i).comp L, ?_⟩
  rfl

/-- In a finite-dimensional domain, `H`-polyhedrality is preserved by the
preimage of an arbitrary linear map. -/
theorem IsHPolyhedral.linear_preimage [FiniteDimensional ℝ F]
    {C : Set E} (hC : IsHPolyhedral C) (L : F →ₗ[ℝ] E) :
    IsHPolyhedral (L ⁻¹' C) := by
  simpa using hC.continuousLinear_preimage (LinearMap.toContinuousLinearMap L)

/-- In a finite-dimensional domain, homogeneous `H`-polyhedrality is
preserved by the preimage of an arbitrary linear map. -/
theorem IsHPolyhedralCone.linear_preimage [FiniteDimensional ℝ F]
    {K : Set E} (hK : IsHPolyhedralCone K) (L : F →ₗ[ℝ] E) :
    IsHPolyhedralCone (L ⁻¹' K) := by
  simpa using hK.continuousLinear_preimage (LinearMap.toContinuousLinearMap L)

end Preimages

theorem IsHPolyhedral.isClosed {C : Set E} (hC : IsHPolyhedral C) :
    IsClosed C := by
  rcases hC with ⟨m, A, b, rfl⟩
  rw [linearInequalitySet_eq_iInter]
  exact isClosed_iInter fun i => isClosed_Iic.preimage (A i).continuous

theorem IsHPolyhedral.convex {C : Set E} (hC : IsHPolyhedral C) :
    Convex ℝ C := by
  rcases hC with ⟨m, A, b, rfl⟩
  rw [linearInequalitySet_eq_iInter]
  exact convex_iInter fun i =>
    (convex_Iic (b i)).linear_preimage (A i : E →ₗ[ℝ] ℝ)

/-- A homogeneous finite inequality description is, in particular, a finite
inequality description with all right-hand sides equal to zero. -/
theorem IsHPolyhedralCone.isHPolyhedral {K : Set E}
    (hK : IsHPolyhedralCone K) :
    IsHPolyhedral K := by
  rcases hK with ⟨m, A, hA⟩
  exact ⟨m, A, 0, hA⟩

theorem IsHPolyhedralCone.isClosed {K : Set E}
    (hK : IsHPolyhedralCone K) :
    IsClosed K :=
  hK.isHPolyhedral.isClosed

theorem IsHPolyhedralCone.convex {K : Set E}
    (hK : IsHPolyhedralCone K) :
    Convex ℝ K :=
  hK.isHPolyhedral.convex

theorem IsHPolyhedralCone.isCone {K : Set E}
    (hK : IsHPolyhedralCone K) :
    IsCone K := by
  rcases hK with ⟨m, A, rfl⟩
  constructor
  · simp
  · intro x hx c hc i
    rw [map_smul]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (hx i)

theorem IsHPolyhedralCone.zero_mem {K : Set E}
    (hK : IsHPolyhedralCone K) :
    (0 : E) ∈ K :=
  hK.isCone.1

theorem IsHPolyhedralCone.nonempty {K : Set E}
    (hK : IsHPolyhedralCone K) :
    K.Nonempty :=
  ⟨0, hK.zero_mem⟩

theorem not_isHPolyhedralCone_empty :
    ¬ IsHPolyhedralCone (∅ : Set E) := by
  intro h
  simpa using h.zero_mem

/-- Conversely, if an `H`-polyhedral set is a cone, its same left-hand sides
give a homogeneous description.  Indeed, positive rescaling forces every
active left-hand side to be nonpositive. -/
theorem IsHPolyhedral.isHPolyhedralCone_of_isCone {K : Set E}
    (hK : IsHPolyhedral K) (hcone : IsCone K) :
    IsHPolyhedralCone K := by
  rcases hK with ⟨m, A, b, hrepr⟩
  refine ⟨m, A, ?_⟩
  ext x
  constructor
  · intro hx i
    by_contra hAxi
    have hAxi' : 0 < A i x := lt_of_not_ge hAxi
    let c : ℝ := (max (b i) 0 + 1) / A i x
    have hnum : 0 < max (b i) 0 + 1 := by
      linarith [le_max_right (b i) 0]
    have hc : 0 < c := div_pos hnum hAxi'
    have hcx : c • x ∈ K := hcone.2 hx hc
    rw [hrepr] at hcx
    have hle : A i (c • x) ≤ b i := hcx i
    rw [map_smul] at hle
    change c * A i x ≤ b i at hle
    have hcA : c * A i x = max (b i) 0 + 1 := by
      dsimp [c]
      exact div_mul_cancel₀ _ hAxi'.ne'
    rw [hcA] at hle
    linarith [le_max_left (b i) 0]
  · intro hx
    rw [hrepr]
    intro i
    have hzero : (0 : E) ∈ K := hcone.1
    rw [hrepr] at hzero
    have hb : 0 ≤ b i := by
      simpa using hzero i
    exact (hx i).trans hb

/-- Homogeneous `H`-polyhedral cones are exactly the `H`-polyhedral sets that
are cones. -/
theorem isHPolyhedralCone_iff_isHPolyhedral_and_isCone {K : Set E} :
    IsHPolyhedralCone K ↔ IsHPolyhedral K ∧ IsCone K := by
  constructor
  · intro hK
    exact ⟨hK.isHPolyhedral, hK.isCone⟩
  · rintro ⟨hK, hcone⟩
    exact hK.isHPolyhedralCone_of_isCone hcone

/-!
The following is a genuine overlap between the `H` and `V` descriptions that
does not require the full Minkowski--Weyl theorem: a single closed halfspace
has a finite-generation description.  For a nonzero functional this follows
from the already-proved preservation of `RW.IsPolyhedral` by a surjective
linear preimage; the zero functional gives either `univ` or `∅`.
-/

theorem isPolyhedral_linearHalfspace [FiniteDimensional ℝ E]
    (a : E →L[ℝ] ℝ) (b : ℝ) :
    IsPolyhedral {x | a x ≤ b} := by
  by_cases ha : a = 0
  · by_cases hb : 0 ≤ b
    · have hset : {x : E | a x ≤ b} = Set.univ := by
        ext x
        simp [ha, hb]
      rw [hset]
      exact IsPolyhedral.univ
    · have hset : {x : E | a x ≤ b} = ∅ := by
        ext x
        simp [ha, hb]
      rw [hset]
      exact IsPolyhedral.empty
  · have ha' : (a : E →ₗ[ℝ] ℝ) ≠ 0 := by
      intro h
      apply ha
      ext x
      exact LinearMap.congr_fun h x
    have hrange : LinearMap.range (a : E →ₗ[ℝ] ℝ) = ⊤ :=
      LinearMap.range_eq_top.mpr (LinearMap.surjective ha')
    change IsPolyhedral ((a : E →ₗ[ℝ] ℝ) ⁻¹' Set.Iic b)
    exact
      (IsPolyhedral.Iic b).preimage_linearMap_of_surjective
        (a : E →ₗ[ℝ] ℝ) hrange

theorem isClosedPolyhedral_linearHalfspace [FiniteDimensional ℝ E]
    (a : E →L[ℝ] ℝ) (b : ℝ) :
    IsClosedPolyhedral {x | a x ≤ b} :=
  (isPolyhedral_linearHalfspace a b).isClosedPolyhedral

/-- A homogeneous closed halfspace is a finitely generated cone.  This is the
one-inequality cone case of Minkowski--Weyl. -/
theorem isFinitelyGeneratedCone_homogeneousHalfspace
    [FiniteDimensional ℝ E] (a : E →L[ℝ] ℝ) :
    IsFinitelyGeneratedCone {x | a x ≤ 0} := by
  exact
    (isPolyhedral_linearHalfspace a 0).isFinitelyGeneratedCone
      (IsHPolyhedralCone.homogeneousHalfspace a).isCone

open Classical in
private noncomputable def halfspaceConeGenerators
    (s : Finset E) (a : E →L[ℝ] ℝ) : Finset E :=
  (s.filter fun x => a x ≤ 0) ∪
    (((s.filter fun x => a x < 0).product (s.filter fun x => 0 < a x)).image
      fun p => a p.2 • p.1 - a p.1 • p.2)

private theorem nonneg_smul_mem_conicHull {C : Set E} {x : E}
    (hx : x ∈ conicHull C) {c : ℝ} (hc : 0 ≤ c) :
    c • x ∈ conicHull C :=
  (isCone_conicHull C).smul_mem hx hc

private theorem sum_mem_conicHull {ι : Type*} {C : Set E}
    (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, f i ∈ conicHull C) :
    ∑ i ∈ s, f i ∈ conicHull C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_mem_conicHull]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact add_mem_of_convex_isCone
        (convex_conicHull C) (isCone_conicHull C)
        (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem sum_eq_sum_filter_neg_add_zero_add_pos
    {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (r : ι → ℝ) (f : ι → M) :
    ∑ i ∈ s, f i =
      (∑ i ∈ s.filter fun i => r i < 0, f i) +
      (∑ i ∈ s.filter fun i => r i = 0, f i) +
      ∑ i ∈ s.filter fun i => 0 < r i, f i := by
  classical
  let sn := s.filter fun i => r i < 0
  let sz := s.filter fun i => r i = 0
  let sp := s.filter fun i => 0 < r i
  have hcover : (sn ∪ sz) ∪ sp = s := by
    ext i
    simp only [sn, sz, sp, Finset.mem_union, Finset.mem_filter]
    constructor
    · aesop
    · intro hi
      rcases lt_trichotomy (r i) 0 with hneg | hzero | hpos
      · exact Or.inl (Or.inl ⟨hi, hneg⟩)
      · exact Or.inl (Or.inr ⟨hi, hzero⟩)
      · exact Or.inr ⟨hi, hpos⟩
  have hnz : Disjoint sn sz := by
    rw [Finset.disjoint_left]
    intro i hin hiz
    simp only [sn, Finset.mem_filter] at hin
    simp only [sz, Finset.mem_filter] at hiz
    linarith
  have hnzp : Disjoint (sn ∪ sz) sp := by
    rw [Finset.disjoint_left]
    intro i hin hiz
    simp only [Finset.mem_union] at hin
    simp only [sp, Finset.mem_filter] at hiz
    rcases hin with hin | hizero
    · simp only [sn, Finset.mem_filter] at hin
      linarith
    · simp only [sz, Finset.mem_filter] at hizero
      linarith
  change (∑ i ∈ s, f i) =
    (∑ i ∈ sn, f i) + (∑ i ∈ sz, f i) + ∑ i ∈ sp, f i
  rw [← hcover, Finset.sum_union hnzp, Finset.sum_union hnz]

private theorem weighted_pair_sum_eq
    (sn sp : Finset E) (a : E →L[ℝ] ℝ) (c : E → ℝ)
    (Q P : ℝ)
    (hQ : Q = ∑ n ∈ sn, c n * (-a n))
    (hP : P = ∑ p ∈ sp, c p * a p)
    (hQ0 : Q ≠ 0) :
    (∑ n ∈ sn, ∑ p ∈ sp,
        (c n * c p / Q) • (a p • n - a n • p)) =
      (P / Q) • (∑ n ∈ sn, c n • n) +
        ∑ p ∈ sp, c p • p := by
  classical
  have hinner (n : E) :
      (∑ p ∈ sp, (c n * c p / Q) • (a p • n - a n • p)) =
        (c n * P / Q) • n +
          (c n * (-a n) / Q) • (∑ p ∈ sp, c p • p) := by
    calc
      (∑ p ∈ sp, (c n * c p / Q) • (a p • n - a n • p)) =
          ∑ p ∈ sp,
            ((c n * c p * a p / Q) • n +
              ((c n * (-a n) / Q) * c p) • p) := by
            apply Finset.sum_congr rfl
            intro p hp
            module
      _ = (∑ p ∈ sp, c n * c p * a p / Q) • n +
          ∑ p ∈ sp, ((c n * (-a n) / Q) * c p) • p := by
            rw [Finset.sum_add_distrib, Finset.sum_smul]
      _ = (c n * P / Q) • n +
          (c n * (-a n) / Q) • (∑ p ∈ sp, c p • p) := by
            congr 1
            · congr 1
              calc
                (∑ p ∈ sp, c n * c p * a p / Q) =
                    (c n / Q) * ∑ p ∈ sp, c p * a p := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro p hp
                      ring
                _ = c n * P / Q := by rw [← hP]; ring
            · rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro p hp
              module
  calc
    (∑ n ∈ sn, ∑ p ∈ sp,
        (c n * c p / Q) • (a p • n - a n • p)) =
        ∑ n ∈ sn,
          ((c n * P / Q) • n +
            (c n * (-a n) / Q) • (∑ p ∈ sp, c p • p)) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact hinner n
    _ = (∑ n ∈ sn, (c n * P / Q) • n) +
        ∑ n ∈ sn, (c n * (-a n) / Q) • (∑ p ∈ sp, c p • p) := by
          rw [Finset.sum_add_distrib]
    _ = (P / Q) • (∑ n ∈ sn, c n • n) +
        (∑ n ∈ sn, c n * (-a n) / Q) • (∑ p ∈ sp, c p • p) := by
          congr 1
          · rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            module
          · rw [Finset.sum_smul]
    _ = (P / Q) • (∑ n ∈ sn, c n • n) +
        ∑ p ∈ sp, c p • p := by
          have hscalar : (∑ n ∈ sn, c n * (-a n) / Q) = 1 := by
            calc
              (∑ n ∈ sn, c n * (-a n) / Q) =
                  (∑ n ∈ sn, c n * (-a n)) / Q := by
                    rw [Finset.sum_div]
              _ = Q / Q := by rw [← hQ]
              _ = 1 := div_self hQ0
          rw [hscalar, one_smul]

/-- Intersecting a finitely generated cone with one homogeneous halfspace has
an explicit finite generating set. -/
theorem conicHull_inter_homogeneousHalfspace
    (s : Finset E) (a : E →L[ℝ] ℝ) :
    conicHull (↑s : Set E) ∩ {x | a x ≤ 0} =
      conicHull (↑(halfspaceConeGenerators s a) : Set E) := by
  classical
  let t := halfspaceConeGenerators s a
  apply le_antisymm
  · rintro x ⟨hxK, hxa⟩
    rcases (mem_conicHull_iff_exists_finsupp.mp hxK) with
      ⟨c, hcs, hc0, hcx⟩
    let sn := s.filter fun y => a y < 0
    let sz := s.filter fun y => a y = 0
    let sp := s.filter fun y => 0 < a y
    let Q : ℝ := ∑ n ∈ sn, c n * (-a n)
    let P : ℝ := ∑ p ∈ sp, c p * a p
    have hcx' : (∑ y ∈ s, c y • y) = x := by
      rw [← hcx]
      exact
        (Finsupp.sum_of_support_subset c hcs (fun y r => r • y) (by simp)).symm
    have hpart :
        (∑ y ∈ s, c y • y) =
          (∑ n ∈ sn, c n • n) +
          (∑ z ∈ sz, c z • z) +
          ∑ p ∈ sp, c p • p := by
      simpa [sn, sz, sp] using
        (sum_eq_sum_filter_neg_add_zero_add_pos
          s (fun y => a y) (fun y => c y • y))
    have hQnonneg : 0 ≤ Q := by
      dsimp [Q]
      apply Finset.sum_nonneg
      intro n hn
      have hneg : a n < 0 := (Finset.mem_filter.mp hn).2
      exact mul_nonneg (hc0 n) (neg_nonneg.mpr hneg.le)
    have hPnonneg : 0 ≤ P := by
      dsimp [P]
      apply Finset.sum_nonneg
      intro p hp
      have hpos : 0 < a p := (Finset.mem_filter.mp hp).2
      exact mul_nonneg (hc0 p) hpos.le
    have hnegEval :
        (∑ n ∈ sn, c n * a n) = -Q := by
      dsimp [Q]
      calc
        (∑ n ∈ sn, c n * a n) =
            ∑ n ∈ sn, -(c n * (-a n)) := by
              apply Finset.sum_congr rfl
              intro n hn
              ring
        _ = -(∑ n ∈ sn, c n * (-a n)) := by
              rw [Finset.sum_neg_distrib]
    have hzeroEval :
        (∑ z ∈ sz, c z * a z) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have haz : a z = 0 := (Finset.mem_filter.mp hz).2
      simp [haz]
    have hposEval :
        (∑ p ∈ sp, c p * a p) = P := by
      rfl
    have heval :
        a (∑ y ∈ s, c y • y) =
          (∑ n ∈ sn, c n * a n) +
          (∑ z ∈ sz, c z * a z) +
          ∑ p ∈ sp, c p * a p := by
      rw [hpart]
      simp only [map_add, map_sum, map_smul, smul_eq_mul]
    have hPQ : P ≤ Q := by
      have hle : a (∑ y ∈ s, c y • y) ≤ 0 := by
        rw [hcx']
        exact hxa
      rw [heval, hnegEval, hzeroEval, hposEval] at hle
      linarith
    have hnonposGenerator {y : E} (hys : y ∈ s) (hay : a y ≤ 0) :
        y ∈ conicHull (↑t : Set E) := by
      apply subset_conicHull
      change y ∈ t
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_filter.mpr ⟨hys, hay⟩)
    have hpairGenerator {n p : E}
        (hn : n ∈ sn) (hp : p ∈ sp) :
        a p • n - a n • p ∈ conicHull (↑t : Set E) := by
      apply subset_conicHull
      change a p • n - a n • p ∈ t
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨(n, p), Finset.mem_product.mpr ⟨hn, hp⟩, rfl⟩
    by_cases hQzero : Q = 0
    · have hPzero : P = 0 := by
        apply le_antisymm
        · simpa [hQzero] using hPQ
        · exact hPnonneg
      have hpterm :
          ∀ p ∈ sp, c p * a p = 0 := by
        apply
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun p hp => mul_nonneg (hc0 p)
              (le_of_lt (Finset.mem_filter.mp hp).2))).mp
        simpa [P] using hPzero
      have hcpzero : ∀ p ∈ sp, c p = 0 := by
        intro p hp
        exact (mul_eq_zero.mp (hpterm p hp)).resolve_right
          (ne_of_gt (Finset.mem_filter.mp hp).2)
      have hpvec :
          (∑ p ∈ sp, c p • p) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        simp [hcpzero p hp]
      have hnmem :
          (∑ n ∈ sn, c n • n) ∈ conicHull (↑t : Set E) := by
        apply sum_mem_conicHull
        intro n hn
        apply nonneg_smul_mem_conicHull
        · exact hnonposGenerator (Finset.mem_filter.mp hn).1
            (le_of_lt (Finset.mem_filter.mp hn).2)
        · exact hc0 n
      have hzmem :
          (∑ z ∈ sz, c z • z) ∈ conicHull (↑t : Set E) := by
        apply sum_mem_conicHull
        intro z hz
        apply nonneg_smul_mem_conicHull
        · exact hnonposGenerator (Finset.mem_filter.mp hz).1
            (le_of_eq (Finset.mem_filter.mp hz).2)
        · exact hc0 z
      have hxsum :
          x = (∑ n ∈ sn, c n • n) + ∑ z ∈ sz, c z • z := by
        calc
          x = ∑ y ∈ s, c y • y := hcx'.symm
          _ = (∑ n ∈ sn, c n • n) +
              (∑ z ∈ sz, c z • z) +
              ∑ p ∈ sp, c p • p := hpart
          _ = (∑ n ∈ sn, c n • n) + ∑ z ∈ sz, c z • z := by
                rw [hpvec, add_zero]
      rw [hxsum]
      exact add_mem_of_convex_isCone
        (convex_conicHull (↑t : Set E)) (isCone_conicHull (↑t : Set E))
        hnmem hzmem
    · have hQpos : 0 < Q := lt_of_le_of_ne hQnonneg (Ne.symm hQzero)
      let R : ℝ := P / Q
      have hRnonneg : 0 ≤ R := div_nonneg hPnonneg hQnonneg
      have hRle : R ≤ 1 := (div_le_one hQpos).mpr hPQ
      have hleftmem :
          (∑ n ∈ sn, ((1 - R) * c n) • n) ∈
            conicHull (↑t : Set E) := by
        apply sum_mem_conicHull
        intro n hn
        apply nonneg_smul_mem_conicHull
        · exact hnonposGenerator (Finset.mem_filter.mp hn).1
            (le_of_lt (Finset.mem_filter.mp hn).2)
        · exact mul_nonneg (sub_nonneg.mpr hRle) (hc0 n)
      have hzmem :
          (∑ z ∈ sz, c z • z) ∈ conicHull (↑t : Set E) := by
        apply sum_mem_conicHull
        intro z hz
        apply nonneg_smul_mem_conicHull
        · exact hnonposGenerator (Finset.mem_filter.mp hz).1
            (le_of_eq (Finset.mem_filter.mp hz).2)
        · exact hc0 z
      have hpairsMem :
          (∑ n ∈ sn, ∑ p ∈ sp,
            (c n * c p / Q) • (a p • n - a n • p)) ∈
              conicHull (↑t : Set E) := by
        apply sum_mem_conicHull
        intro n hn
        apply sum_mem_conicHull
        intro p hp
        apply nonneg_smul_mem_conicHull
        · exact hpairGenerator hn hp
        · exact div_nonneg (mul_nonneg (hc0 n) (hc0 p)) hQnonneg
      have hleft :
          (∑ n ∈ sn, ((1 - R) * c n) • n) =
            (1 - R) • (∑ n ∈ sn, c n • n) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        module
      have hpairs :
          (∑ n ∈ sn, ∑ p ∈ sp,
              (c n * c p / Q) • (a p • n - a n • p)) =
            R • (∑ n ∈ sn, c n • n) +
              ∑ p ∈ sp, c p • p := by
        simpa [R, Q, P] using
          (weighted_pair_sum_eq sn sp a c Q P rfl rfl hQzero)
      have hxsum :
          x =
            ((∑ n ∈ sn, ((1 - R) * c n) • n) +
              ∑ z ∈ sz, c z • z) +
            ∑ n ∈ sn, ∑ p ∈ sp,
              (c n * c p / Q) • (a p • n - a n • p) := by
        calc
          x = ∑ y ∈ s, c y • y := hcx'.symm
          _ = (∑ n ∈ sn, c n • n) +
              (∑ z ∈ sz, c z • z) +
              ∑ p ∈ sp, c p • p := hpart
          _ = ((∑ n ∈ sn, ((1 - R) * c n) • n) +
                ∑ z ∈ sz, c z • z) +
              ∑ n ∈ sn, ∑ p ∈ sp,
                (c n * c p / Q) • (a p • n - a n • p) := by
                  rw [hleft, hpairs]
                  module
      rw [hxsum]
      exact add_mem_of_convex_isCone
        (convex_conicHull (↑t : Set E)) (isCone_conicHull (↑t : Set E))
        (add_mem_of_convex_isCone
          (convex_conicHull (↑t : Set E)) (isCone_conicHull (↑t : Set E))
          hleftmem hzmem)
        hpairsMem
  · refine conicHull_minimal
      ((convex_conicHull (↑s : Set E)).inter
        ((convex_Iic (0 : ℝ)).linear_preimage (a : E →ₗ[ℝ] ℝ)))
      ?_ ?_
    · constructor
      · exact ⟨zero_mem_conicHull (↑s : Set E), by simp⟩
      · intro x hx c hc
        refine ⟨(isCone_conicHull (↑s : Set E)).smul_mem hx.1 hc.le, ?_⟩
        change a (c • x) ≤ 0
        rw [map_smul]
        exact mul_nonpos_of_nonneg_of_nonpos hc.le hx.2
    · intro y hy
      change y ∈ halfspaceConeGenerators s a at hy
      rcases Finset.mem_union.mp hy with hy | hy
      · rcases Finset.mem_filter.mp hy with ⟨hys, hay⟩
        exact ⟨subset_conicHull hys, hay⟩
      · rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
        rcases Finset.mem_product.mp hp with ⟨hn, hp⟩
        have hn' := Finset.mem_filter.mp hn
        have hp' := Finset.mem_filter.mp hp
        constructor
        · have hleft :
              a p.2 • p.1 ∈ conicHull (↑s : Set E) :=
            nonneg_smul_mem_conicHull (subset_conicHull hn'.1) hp'.2.le
          have hright :
              (-a p.1) • p.2 ∈ conicHull (↑s : Set E) :=
            nonneg_smul_mem_conicHull (subset_conicHull hp'.1)
              (neg_nonneg.mpr hn'.2.le)
          have hadd := add_mem_of_convex_isCone
            (convex_conicHull (↑s : Set E)) (isCone_conicHull (↑s : Set E))
            hleft hright
          convert hadd using 1
          module
        · change a (a p.2 • p.1 - a p.1 • p.2) ≤ 0
          simp only [map_sub, map_smul, smul_eq_mul]
          ring_nf
          exact le_rfl

/-- A finitely generated cone remains finitely generated after intersection
with one homogeneous closed halfspace. -/
theorem IsFinitelyGeneratedCone.inter_homogeneousHalfspace
    {K : Set E} (hK : IsFinitelyGeneratedCone K) (a : E →L[ℝ] ℝ) :
    IsFinitelyGeneratedCone (K ∩ {x | a x ≤ 0}) := by
  rcases hK with ⟨s, rfl⟩
  exact ⟨halfspaceConeGenerators s a, conicHull_inter_homogeneousHalfspace s a⟩

/-- The solution cone of any finite homogeneous continuous-linear system is
finitely generated in finite dimensions.  This is the `H → V` cone direction
of Minkowski--Weyl. -/
theorem isFinitelyGeneratedCone_homogeneousLinearInequalitySet
    [FiniteDimensional ℝ E] {m : ℕ}
    (A : Fin m → (E →L[ℝ] ℝ)) :
    IsFinitelyGeneratedCone (homogeneousLinearInequalitySet A) := by
  induction m with
  | zero =>
      have htop : IsFinitelyGeneratedCone (Set.univ : Set E) :=
        IsFinitelyGeneratedCone.submodule (⊤ : Submodule ℝ E)
      simpa [homogeneousLinearInequalitySet, linearInequalitySet] using htop
  | succ m ih =>
      let A' : Fin m → (E →L[ℝ] ℝ) := fun i => A i.castSucc
      have hset :
          homogeneousLinearInequalitySet A =
            homogeneousLinearInequalitySet A' ∩
              {x | A (Fin.last m) x ≤ 0} := by
        ext x
        constructor
        · intro hx
          exact ⟨fun i => hx i.castSucc, hx (Fin.last m)⟩
        · rintro ⟨hinit, hlast⟩ i
          exact Fin.lastCases hlast hinit i
      rw [hset]
      exact (ih A').inter_homogeneousHalfspace (A (Fin.last m))

/-- Every finite homogeneous `H`-description is a finite `V`-description in
finite dimensions. -/
theorem IsHPolyhedralCone.isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {K : Set E}
    (hK : IsHPolyhedralCone K) :
    IsFinitelyGeneratedCone K := by
  rcases hK with ⟨m, A, rfl⟩
  exact isFinitelyGeneratedCone_homogeneousLinearInequalitySet A

private theorem continuousLinearMap_nonneg_on_conicHull
    (f : E →L[ℝ] ℝ) {s : Set E}
    (hf : ∀ x ∈ s, 0 ≤ f x) {x : E} (hx : x ∈ conicHull s) :
    0 ≤ f x := by
  apply
    conicHull_minimal
      ((convex_Ici (0 : ℝ)).linear_preimage (f : E →ₗ[ℝ] ℝ))
      ?_ hf hx
  constructor
  · simp
  · intro y hy c hc
    change 0 ≤ f (c • y)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg hc.le hy

/-- Every finitely generated cone in a finite-dimensional normed space has a
finite homogeneous inequality description.

The proof finitely generates the dual cone and uses conic separation for the
reverse inclusion. -/
theorem IsFinitelyGeneratedCone.isHPolyhedralCone
    [FiniteDimensional ℝ E] {K : Set E}
    (hK : IsFinitelyGeneratedCone K) :
    IsHPolyhedralCone K := by
  classical
  rcases hK with ⟨s, rfl⟩
  let D : Set (StrongDual ℝ E) :=
    {f | ∀ y ∈ (↑s : Set E), 0 ≤ f y}
  have hDH : IsHPolyhedralCone D := by
    refine
      ⟨s.card,
        fun i =>
          -((ContinuousLinearMap.apply ℝ ℝ) (((s.equivFin).symm i).1)),
        ?_⟩
    ext f
    simp only [D, Set.mem_setOf_eq, mem_homogeneousLinearInequalitySet,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.apply_apply,
      neg_nonpos]
    constructor
    · intro hf i
      exact hf _ (((s.equivFin).symm i).2)
    · intro hf y hy
      let i : Fin s.card := s.equivFin ⟨y, hy⟩
      have hi := hf i
      have heq : (((s.equivFin).symm i).1) = y := by
        exact congrArg Subtype.val ((s.equivFin).symm_apply_apply ⟨y, hy⟩)
      simpa [heq] using hi
  rcases hDH.isFinitelyGeneratedCone with ⟨t, ht⟩
  refine
    ⟨t.card,
      fun i => -(((t.equivFin).symm i).1),
      ?_⟩
  ext x
  simp only [mem_homogeneousLinearInequalitySet,
    ContinuousLinearMap.neg_apply, neg_nonpos]
  constructor
  · intro hx i
    let f : StrongDual ℝ E := ((t.equivFin).symm i).1
    have hfD : f ∈ D := by
      rw [ht]
      exact subset_conicHull (((t.equivFin).symm i).2)
    have hfs : ∀ y ∈ (↑s : Set E), 0 ≤ f y := by
      simpa [D] using hfD
    exact continuousLinearMap_nonneg_on_conicHull f hfs hx
  · intro hx
    have hxt : ∀ f ∈ (↑t : Set (StrongDual ℝ E)), 0 ≤ f x := by
      intro f hf
      let i : Fin t.card := t.equivFin ⟨f, hf⟩
      have hi := hx i
      have heq : (((t.equivFin).symm i).1) = f := by
        exact congrArg Subtype.val ((t.equivFin).symm_apply_apply ⟨f, hf⟩)
      simpa [heq] using hi
    have hxD : ∀ f ∈ D, 0 ≤ f x := by
      intro f hf
      have hf' : f ∈ conicHull (↑t : Set (StrongDual ℝ E)) := by
        rw [← ht]
        exact hf
      exact
        continuousLinearMap_nonneg_on_conicHull
          ((ContinuousLinearMap.apply ℝ ℝ) x) hxt hf'
    by_contra hxK
    let C : ProperCone ℝ E :=
      { toSubmodule := PointedCone.span ℝ (↑s : Set E)
        isClosed' := by
          simpa [conicHull] using
            (isClosed_conicHull_finset (E := E) s) }
    have hxC : x ∉ (C : Set E) := by
      simpa [C, conicHull] using hxK
    obtain ⟨f, hfC, hfx⟩ := C.hyperplane_separation_point hxC
    have hfD : f ∈ D := by
      intro y hy
      apply hfC y
      change y ∈ conicHull (↑s : Set E)
      exact subset_conicHull hy
    exact (not_lt_of_ge (hxD f hfD)) hfx

/-- Every finite affine `H`-description is a finite
convex-plus-conic `V`-description in finite dimensions.  The proof
homogenizes the affine system in ray space and applies the cone theorem. -/
theorem IsHPolyhedral.isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsHPolyhedral C) :
    IsPolyhedral C := by
  rcases hC with ⟨m, A, b, rfl⟩
  let fstL : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  let sndL : E × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  let B : Fin (1 + m) → (E × ℝ →L[ℝ] ℝ) :=
    Fin.addCases (fun _ : Fin 1 => sndL)
      (fun i => (A i).comp fstL + (b i) • sndL)
  let K : Set E := homogeneousLinearInequalitySet A
  have hray :
      raySpaceCone (RW.linearInequalitySet A b) K =
        homogeneousLinearInequalitySet B := by
    ext p
    rcases p with ⟨z, t⟩
    constructor
    · rintro (hord | hzero)
      · rcases hord with ⟨x, hx, r, hr, hp⟩
        have hp1 : z = r • x := congrArg Prod.fst hp
        have hp2 : t = -r := congrArg Prod.snd hp
        intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          simpa [B, sndL, hp2] using (neg_nonpos.mpr hr.le)
        · intro i
          have hxi : A i x ≤ b i := hx i
          have : A i z + b i * t ≤ 0 := by
            rw [hp1, hp2, map_smul]
            simp only [smul_eq_mul]
            calc
              r * A i x + b i * -r = r * (A i x - b i) := by ring
              _ ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos hr.le (sub_nonpos.mpr hxi)
          simpa [B, fstL, sndL, smul_eq_mul] using this
      · have ht : t = 0 := by simpa using hzero.2
        have hz : z ∈ K := hzero.1
        intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          simp [B, sndL, ht]
        · intro i
          have hzi : A i z ≤ 0 := hz i
          simpa [B, fstL, sndL, ht] using hzi
    · intro hp
      have ht : t ≤ 0 := by
        have h := hp (Fin.castAdd m (0 : Fin 1))
        simpa [B, sndL] using h
      rcases lt_or_eq_of_le ht with htneg | htzero
      · let r : ℝ := -t
        have hr : 0 < r := by dsimp [r]; linarith
        let x : E := r⁻¹ • z
        have hx : x ∈ RW.linearInequalitySet A b := by
          intro i
          have hi := hp (Fin.natAdd 1 i)
          have hi' : A i z + b i * t ≤ 0 := by
            simpa [B, fstL, sndL, smul_eq_mul] using hi
          have ht' : t = -r := by simp [r]
          have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
          have hmul : r * (A i x - b i) ≤ 0 := by
            calc
              r * (A i x - b i)
                  = r * (r⁻¹ * A i z - b i) := by
                      simp only [x, map_smul, smul_eq_mul]
              _ = (r * r⁻¹) * A i z - r * b i := by ring
              _ = A i z - r * b i := by rw [hri, one_mul]
              _ = A i z + b i * t := by rw [ht']; ring
              _ ≤ 0 := hi'
          exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hmul hr)
        left
        refine ⟨x, hx, r, hr, ?_⟩
        ext
        · simp [x, smul_smul, mul_inv_cancel₀ hr.ne']
        · simp [r]
      · right
        refine ⟨?_, by simp [htzero]⟩
        intro i
        have hi := hp (Fin.natAdd 1 i)
        simpa [B, fstL, sndL, htzero, smul_eq_mul] using hi
  have hRayH :
      IsHPolyhedralCone
        (raySpaceCone (RW.linearInequalitySet A b) K) := by
    rw [hray]
    exact IsHPolyhedralCone.homogeneousLinearInequalitySet B
  exact hRayH.isFinitelyGeneratedCone.isPolyhedral_of_eq_raySpaceCone

/-- Every finite ordinary-points-plus-directions description in finite
dimensions has a finite affine inequality description.  For a nonempty set,
apply the cone theorem to its ray-space homogenization and restrict the
homogeneous inequalities to the height `-1` slice. -/
theorem IsPolyhedral.isHPolyhedral
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsPolyhedral C) :
    IsHPolyhedral C := by
  classical
  obtain rfl | hCne := C.eq_empty_or_nonempty
  · exact IsHPolyhedral.empty
  have hRayH :
      IsHPolyhedralCone (raySpaceCone C (horizonCone C)) :=
    (hC.isFinitelyGeneratedCone_raySpaceCone hCne).isHPolyhedralCone
  rcases hRayH with ⟨m, A, hA⟩
  let inlL : E →L[ℝ] E × ℝ := ContinuousLinearMap.inl ℝ E ℝ
  refine
    ⟨m, fun i => (A i).comp inlL,
      fun i => -(A i) (0, (-1 : ℝ)), ?_⟩
  ext x
  change x ∈ C ↔
    ∀ i, (A i) (x, 0) ≤ -(A i) (0, (-1 : ℝ))
  rw [← mem_raySpaceCone_neg_one_iff (K := horizonCone C), hA]
  change (∀ i, (A i) (x, (-1 : ℝ)) ≤ 0) ↔
    ∀ i, (A i) (x, 0) ≤ -(A i) (0, (-1 : ℝ))
  constructor
  · intro hx i
    have hi := hx i
    have hdecomp :
        (x, (-1 : ℝ)) = (x, 0) + (0, (-1 : ℝ)) := by
      ext <;> simp
    rw [hdecomp, map_add] at hi
    linarith
  · intro hx i
    have hi := hx i
    have hdecomp :
        (x, (-1 : ℝ)) = (x, 0) + (0, (-1 : ℝ)) := by
      ext <;> simp
    rw [hdecomp, map_add]
    linarith

/-- Minkowski--Weyl for cones: finite homogeneous inequalities and finite
conic generation are equivalent in finite dimensions. -/
theorem isHPolyhedralCone_iff_isFinitelyGeneratedCone
    [FiniteDimensional ℝ E] {K : Set E} :
    IsHPolyhedralCone K ↔ IsFinitelyGeneratedCone K :=
  ⟨IsHPolyhedralCone.isFinitelyGeneratedCone,
    IsFinitelyGeneratedCone.isHPolyhedralCone⟩

/-- **Minkowski--Weyl theorem.** In finite dimensions, finite affine
inequality descriptions and finite ordinary-points-plus-directions
descriptions are equivalent. -/
theorem isHPolyhedral_iff_isPolyhedral
    [FiniteDimensional ℝ E] {C : Set E} :
    IsHPolyhedral C ↔ IsPolyhedral C :=
  ⟨IsHPolyhedral.isPolyhedral, IsPolyhedral.isHPolyhedral⟩

/-! ## Closure consequences transferred from the H-representation -/

/-- Finite-dimensional polyhedral sets are closed under binary
intersection, with no ray-space generation certificate required. -/
theorem IsPolyhedral.inter
    [FiniteDimensional ℝ E] {C D : Set E}
    (hC : IsPolyhedral C) (hD : IsPolyhedral D) :
    IsPolyhedral (C ∩ D) :=
  (hC.isHPolyhedral.inter hD.isHPolyhedral).isPolyhedral

/-- Finite intersections of finite-dimensional polyhedral sets are
polyhedral. -/
theorem IsPolyhedral.iInter_finset
    [FiniteDimensional ℝ E] {ι : Type*} (s : Finset ι)
    (C : ι → Set E) (hC : ∀ i ∈ s, IsPolyhedral (C i)) :
    IsPolyhedral (⋂ i ∈ s, C i) :=
  (IsHPolyhedral.iInter_finset s C fun i hi ↦
    (hC i hi).isHPolyhedral).isPolyhedral

/-- Closed polyhedral sets are closed under binary intersection, without
the former diagonal/ray-space side condition. -/
theorem IsClosedPolyhedral.inter
    [FiniteDimensional ℝ E] {C D : Set E}
    (hC : IsClosedPolyhedral C) (hD : IsClosedPolyhedral D) :
    IsClosedPolyhedral (C ∩ D) :=
  (hC.isPolyhedral.inter hD.isPolyhedral).isClosedPolyhedral

/-- Finitely generated cones are closed under binary intersection in finite
dimensions. -/
theorem IsFinitelyGeneratedCone.inter
    [FiniteDimensional ℝ E] {K L : Set E}
    (hK : IsFinitelyGeneratedCone K)
    (hL : IsFinitelyGeneratedCone L) :
    IsFinitelyGeneratedCone (K ∩ L) :=
  (hK.isHPolyhedralCone.inter hL.isHPolyhedralCone).isFinitelyGeneratedCone

section UnconditionalPreimages

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Polyhedrality is preserved by preimages under arbitrary continuous
linear maps between finite-dimensional spaces; neither injectivity nor
surjectivity is required. -/
theorem IsPolyhedral.continuousLinear_preimage
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : Set E} (hC : IsPolyhedral C) (L : F →L[ℝ] E) :
    IsPolyhedral (L ⁻¹' C) :=
  (hC.isHPolyhedral.continuousLinear_preimage L).isPolyhedral

/-- Polyhedrality is preserved by preimages under arbitrary linear maps
between finite-dimensional spaces. -/
theorem IsPolyhedral.linear_preimage
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : Set E} (hC : IsPolyhedral C) (L : F →ₗ[ℝ] E) :
    IsPolyhedral (L ⁻¹' C) :=
  (hC.isHPolyhedral.linear_preimage L).isPolyhedral

/-- Closed polyhedrality is preserved by arbitrary linear preimages in
finite dimensions. -/
theorem IsClosedPolyhedral.linear_preimage
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : Set E} (hC : IsClosedPolyhedral C) (L : F →ₗ[ℝ] E) :
    IsClosedPolyhedral (L ⁻¹' C) :=
  (hC.isPolyhedral.linear_preimage L).isClosedPolyhedral

/-- Finite generation of cones is preserved by arbitrary linear preimages
in finite dimensions. -/
theorem IsFinitelyGeneratedCone.linear_preimage
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {K : Set E} (hK : IsFinitelyGeneratedCone K) (L : F →ₗ[ℝ] E) :
    IsFinitelyGeneratedCone (L ⁻¹' K) :=
  (hK.isHPolyhedralCone.linear_preimage L).isFinitelyGeneratedCone

end UnconditionalPreimages

end RW
