/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3B: Finite Cone, Product, and Sum Operations

This file packages the finite-family forms of Exercises 3.7, 3.11, and 3.12.
It also records the strongest currently available fixed-cardinality form of
Theorem 3.15 in a form convenient for later use.
-/

import RockafellarWets.Chapter3.SetOperations
import RockafellarWets.Chapter3.PointedCones

open scoped BigOperators Pointwise
open Set Bornology Filter Topology

namespace RW

section ConvexCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closure under arbitrary finite nonnegative combinations. -/
def IsClosedUnderFiniteNonnegativeCombinations (K : Set E) : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (z : Fin n → E),
    (∀ i, 0 ≤ a i) → (∀ i, z i ∈ K) →
      ∑ i, a i • z i ∈ K

/-- **Exercise 3.7**: for a cone, convexity, closure under addition, and
closure under arbitrary finite nonnegative combinations are equivalent. -/
theorem IsCone.convex_iff_add_mem_and_finite_nonnegative_combinations
    {K : Set E} (hcone : IsCone K) :
    (Convex ℝ K ↔ ∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K) ∧
      ((∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K) ↔
        IsClosedUnderFiniteNonnegativeCombinations K) := by
  refine ⟨hcone.convex_iff_add_mem, ?_⟩
  constructor
  · intro hadd n a z ha hz
    exact sum_mem_of_convex_isCone
      ((hcone.convex_iff_add_mem).2 hadd) hcone Finset.univ
      (fun i => a i • z i)
      (fun i _ => hcone.smul_mem (hz i) (ha i))
  · intro hfinite x y hx hy
    simpa [Fin.sum_univ_two] using hfinite 2 (fun _ => 1)
      (fun i => if i = 0 then x else y) (by simp)
      (by intro i; fin_cases i <;> simp [hx, hy])

/-- A direct two-condition packaging of Exercise 3.7. -/
theorem IsCone.convex_iff_finite_nonnegative_combinations
    {K : Set E} (hcone : IsCone K) :
    Convex ℝ K ↔ IsClosedUnderFiniteNonnegativeCombinations K :=
  hcone.convex_iff_add_mem_and_finite_nonnegative_combinations.1.trans
    hcone.convex_iff_add_mem_and_finite_nonnegative_combinations.2

end ConvexCones

section FiniteProducts

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 3.11** (finite-family inclusion): a horizon direction of a
finite Cartesian product is a horizon direction in every coordinate. -/
theorem horizonCone_pi_subset_pi_horizonCone (C : ι → Set E) :
    horizonCone (Set.pi Set.univ C) ⊆
      Set.pi Set.univ (fun i => horizonCone (C i)) := by
  intro w hw
  have hw' : w = 0 ∨ w ∈ asymptoticCone ℝ (Set.pi Set.univ C) := by
    simpa [horizonCone] using hw
  rcases hw' with rfl | hw
  · simp [Set.mem_pi, zero_mem_horizonCone]
  · rcases exists_seq_pos_smul_of_mem_asymptoticCone
      (C := Set.pi Set.univ C) hw with ⟨c, u, hc, hu, hcpos, hmem⟩
    rw [Set.mem_pi]
    intro i hi
    apply Set.mem_insert_of_mem 0
    refine mem_asymptoticCone_of_seq_smul
      (u := fun n => u n i) hc ?_ ?_
    · exact tendsto_pi_nhds.1 hu i
    · intro n
      have h := hmem n
      rw [Set.mem_pi] at h
      simpa using h i (Set.mem_univ i)

/-- **Exercise 3.11** (finite-family equality, convex case): for a finite
family of nonempty convex sets, the horizon cone of their Cartesian product is
the Cartesian product of their horizon cones. -/
theorem horizonCone_pi_eq_pi_horizonCone_of_convex_nonempty
    (C : ι → Set E) (hconv : ∀ i, Convex ℝ (C i))
    (hne : ∀ i, (C i).Nonempty) :
    horizonCone (Set.pi Set.univ C) =
      Set.pi Set.univ (fun i => horizonCone (C i)) := by
  apply le_antisymm (horizonCone_pi_subset_pi_horizonCone C)
  intro w hw
  rw [Set.mem_pi] at hw
  choose x hx using hne
  have hxpi : x ∈ Set.pi Set.univ C := by
    simp [Set.mem_pi, hx]
  have hray :
      ∀ ⦃τ : ℝ⦄, 0 ≤ τ →
        τ • w + x ∈ closure (Set.pi Set.univ C) := by
    intro τ hτ
    rw [closure_pi_set, Set.mem_pi]
    intro i hi
    exact smul_add_mem_closure_of_mem_horizonCone
      (hconv i) (subset_closure (hx i)) (hw i (Set.mem_univ i)) hτ
  have hclosure :
      w ∈ horizonCone (closure (Set.pi Set.univ C)) :=
    mem_horizonCone_of_forall_smul_add_mem
      (C := closure (Set.pi Set.univ C)) (x := x) (w := w) hray
  simpa [horizonCone_closure] using hclosure

/-- **Exercise 3.11** (finite-family equality, bounded case): equality also
holds when every set is nonempty and all factors except a designated one are
bounded.  The designated factor may be bounded as well. -/
theorem horizonCone_pi_eq_pi_horizonCone_of_bounded_off
    (C : ι → Set E) (j : ι) (hne : ∀ i, (C i).Nonempty)
    (hbdd : ∀ i, i ≠ j → IsBounded (C i)) :
    horizonCone (Set.pi Set.univ C) =
      Set.pi Set.univ (fun i => horizonCone (C i)) := by
  classical
  apply le_antisymm (horizonCone_pi_subset_pi_horizonCone C)
  intro w hw
  rw [Set.mem_pi] at hw
  have hwoff : ∀ i, i ≠ j → w i = 0 := by
    intro i hij
    have hzero : horizonCone (C i) = ({0} : Set E) :=
      (isBounded_iff_horizonCone_eq_singleton_zero (C := C i)).mp
        (hbdd i hij)
    simpa [hzero] using hw i (Set.mem_univ i)
  by_cases hwj : w j = 0
  · have hw0 : w = 0 := by
      funext i
      by_cases hij : i = j
      · simpa [hij] using hwj
      · exact hwoff i hij
    subst w
    exact zero_mem_horizonCone _
  have hwjasym : w j ∈ asymptoticCone ℝ (C j) := by
    rcases (show w j = 0 ∨ w j ∈ asymptoticCone ℝ (C j) by
      simpa [horizonCone] using hw j (Set.mem_univ j)) with h | h
    · exact (hwj h).elim
    · exact h
  rcases exists_seq_pos_smul_of_mem_asymptoticCone hwjasym with
    ⟨c, u, hc, hu, hcpos, hmem⟩
  choose x hx using hne
  let v : ℕ → ι → E :=
    fun n i => if i = j then u n else (c n)⁻¹ • x i
  have hv : Tendsto v atTop (𝓝 w) := by
    apply tendsto_pi_nhds.2
    intro i
    by_cases hij : i = j
    · subst i
      simpa [v] using hu
    · have hi0 :
          Tendsto (fun n => (c n)⁻¹ • x i) atTop (𝓝 (0 : E)) := by
        simpa using hc.inv_tendsto_atTop.smul_const (x i)
      simpa [v, hij, hwoff i hij] using hi0
  have hcvmem : ∀ n, c n • v n ∈ Set.pi Set.univ C := by
    intro n
    rw [Set.mem_pi]
    intro i hi
    by_cases hij : i = j
    · subst i
      simpa [v] using hmem n
    · simpa [v, hij, smul_smul, mul_inv_cancel₀ (hcpos n).ne',
        one_smul] using hx i
  exact Set.mem_insert_of_mem 0 <|
    mem_asymptoticCone_of_seq_smul hc hv hcvmem

/-- The finite product is bounded exactly coordinatewise (in the nonempty
case), so its horizon cone is trivial exactly when all factors are bounded. -/
theorem horizonCone_pi_eq_singleton_zero_of_nonempty_bounded
    (C : ι → Set E) (hbdd : ∀ i, IsBounded (C i)) :
    horizonCone (Set.pi Set.univ C) = ({0} : Set (ι → E)) := by
  apply (isBounded_iff_horizonCone_eq_singleton_zero
    (C := Set.pi Set.univ C)).mp
  exact IsBounded.pi hbdd

end FiniteProducts

section FiniteSums

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The set of sums obtained by choosing one point from every member of a
finite indexed family. -/
def finiteSetSum (C : ι → Set E) : Set E :=
  {x | ∃ z : ι → E, (∀ i, z i ∈ C i) ∧ ∑ i, z i = x}

private def finiteSumLinearMap : (ι → E) →ₗ[ℝ] E where
  toFun z := ∑ i, z i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.smul_sum]

omit [FiniteDimensional ℝ E] in
private theorem finiteSetSum_eq_image (C : ι → Set E) :
    finiteSetSum C =
      finiteSumLinearMap '' Set.pi Set.univ C := by
  ext x
  simp [finiteSetSum, finiteSumLinearMap, Set.mem_pi]

private theorem finiteSumLinearMap_hker
    {C : ι → Set E}
    (hker : ∀ u : ι → E, (∀ i, u i ∈ horizonCone (C i)) →
      (∑ i, u i) = 0 → u = 0) :
    ∀ ⦃u : ι → E⦄, u ∈ horizonCone (Set.pi Set.univ C) →
      finiteSumLinearMap u = 0 → u = 0 := by
  intro u hu hsum
  apply hker u
  · have hu' := horizonCone_pi_subset_pi_horizonCone C hu
    simpa [Set.mem_pi] using hu'
  · simpa [finiteSumLinearMap] using hsum

/-- **Exercise 3.12** (finite-family closedness): if the only selection of
horizon directions whose sum vanishes is the zero selection, then the finite
sum of closed sets is closed. -/
theorem isClosed_finiteSetSum_of_horizonCone_no_cancel
    {C : ι → Set E} (hclosed : ∀ i, IsClosed (C i))
    (hker : ∀ u : ι → E, (∀ i, u i ∈ horizonCone (C i)) →
      (∑ i, u i) = 0 → u = 0) :
    IsClosed (finiteSetSum C) := by
  rw [finiteSetSum_eq_image]
  exact isClosed_linearImage_of_horizonCone_ker_trivial
    (isClosed_set_pi fun _ _ => hclosed _)
    (finiteSumLinearMap_hker hker)

/-- **Exercise 3.12** (finite-family horizon inclusion): under the same
noncancellation hypothesis, the horizon cone of the finite sum is contained
in the finite sum of the individual horizon cones. -/
theorem horizonCone_finiteSetSum_subset_of_horizonCone_no_cancel
    {C : ι → Set E}
    (hker : ∀ u : ι → E, (∀ i, u i ∈ horizonCone (C i)) →
      (∑ i, u i) = 0 → u = 0) :
    horizonCone (finiteSetSum C) ⊆
      finiteSetSum (fun i => horizonCone (C i)) := by
  rw [finiteSetSum_eq_image, ← linearImage_horizonCone_eq
    (L := finiteSumLinearMap) (C := Set.pi Set.univ C)
    (finiteSumLinearMap_hker hker)]
  rintro x ⟨u, hu, rfl⟩
  have hu' := horizonCone_pi_subset_pi_horizonCone C hu
  refine ⟨u, ?_, rfl⟩
  simpa [Set.mem_pi] using hu'

/-- **Exercise 3.12** (finite-family equality, convex case): under
noncancellation, finite sums of nonempty convex sets have horizon cone equal
to the finite sum of the factor horizon cones. -/
theorem horizonCone_finiteSetSum_eq_of_convex_nonempty_of_horizonCone_no_cancel
    {C : ι → Set E} (hconv : ∀ i, Convex ℝ (C i))
    (hne : ∀ i, (C i).Nonempty)
    (hker : ∀ u : ι → E, (∀ i, u i ∈ horizonCone (C i)) →
      (∑ i, u i) = 0 → u = 0) :
    horizonCone (finiteSetSum C) =
      finiteSetSum (fun i => horizonCone (C i)) := by
  rw [finiteSetSum_eq_image, ← linearImage_horizonCone_eq
    (L := finiteSumLinearMap) (C := Set.pi Set.univ C)
    (finiteSumLinearMap_hker hker),
    horizonCone_pi_eq_pi_horizonCone_of_convex_nonempty C hconv hne]
  exact (finiteSetSum_eq_image (fun i => horizonCone (C i))).symm

private theorem finite_horizon_no_cancel_of_bounded_off
    {C : ι → Set E} (j : ι)
    (hbdd : ∀ i, i ≠ j → IsBounded (C i)) :
    ∀ u : ι → E, (∀ i, u i ∈ horizonCone (C i)) →
      (∑ i, u i) = 0 → u = 0 := by
  classical
  intro u hu hsum
  have huoff : ∀ i, i ≠ j → u i = 0 := by
    intro i hij
    have hzero : horizonCone (C i) = ({0} : Set E) :=
      (isBounded_iff_horizonCone_eq_singleton_zero (C := C i)).mp
        (hbdd i hij)
    simpa [hzero] using hu i
  have huj : u j = 0 := by
    have hsumj : ∑ i, u i = u j := by
      exact Finset.sum_eq_single j
        (fun i _ hij => huoff i hij)
        (fun hj => (hj (Finset.mem_univ j)).elim)
    rw [hsumj] at hsum
    exact hsum
  funext i
  by_cases hij : i = j
  · simpa [hij] using huj
  · exact huoff i hij

/-- **Exercise 3.12** (finite-family equality, bounded case): if all but one
of a finite family of nonempty sets are bounded, the finite sum has horizon
cone equal to the finite sum of the factor horizon cones. -/
theorem horizonCone_finiteSetSum_eq_of_bounded_off
    {C : ι → Set E} (j : ι) (hne : ∀ i, (C i).Nonempty)
    (hbdd : ∀ i, i ≠ j → IsBounded (C i)) :
    horizonCone (finiteSetSum C) =
      finiteSetSum (fun i => horizonCone (C i)) := by
  have hker := finite_horizon_no_cancel_of_bounded_off (C := C) j hbdd
  rw [finiteSetSum_eq_image, ← linearImage_horizonCone_eq
    (L := finiteSumLinearMap) (C := Set.pi Set.univ C)
    (finiteSumLinearMap_hker hker),
    horizonCone_pi_eq_pi_horizonCone_of_bounded_off C j hne hbdd]
  exact (finiteSetSum_eq_image (fun i => horizonCone (C i))).symm

/-- **Exercise 3.12** (finite-family closedness, bounded case): a finite sum
of closed sets is closed when all but at most one factor are bounded. -/
theorem isClosed_finiteSetSum_of_bounded_off
    {C : ι → Set E} (j : ι) (hclosed : ∀ i, IsClosed (C i))
    (hbdd : ∀ i, i ≠ j → IsBounded (C i)) :
    IsClosed (finiteSetSum C) :=
  isClosed_finiteSetSum_of_horizonCone_no_cancel hclosed
    (finite_horizon_no_cancel_of_bounded_off (C := C) j hbdd)

end FiniteSums

section ConvexHullOfCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **Theorem 3.15** (independent representation): a point in the convex hull
of a cone has a representation as a sum of linearly independent vectors of
the cone.  At `x = 0` the family may be empty. -/
theorem exists_linearlyIndependent_sum_of_mem_convexHull
    {K : Set E} (hcone : IsCone K) {x : E}
    (hx : x ∈ convexHull ℝ K) :
    ∃ (p : ℕ) (z : Fin p → E), LinearIndependent ℝ z ∧
      (∀ i, z i ∈ K) ∧ ∑ i, z i = x := by
  classical
  let P : ℕ → Prop :=
    fun p => ∃ z : Fin p → E, (∀ i, z i ∈ K) ∧ ∑ i, z i = x
  have hP : ∃ p, P p := by
    rcases (mem_convexHull_iff_exists_fintype_sum_mem hcone).1 hx with
      ⟨α, _, z, hz, hsum⟩
    let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
    refine ⟨Fintype.card α, z ∘ e.symm, ?_, ?_⟩
    · intro i
      exact hz (e.symm i)
    · exact (Fintype.sum_equiv e z (z ∘ e.symm)
        (fun i => by simp)).symm.trans hsum
  let p : ℕ := Nat.find hP
  obtain ⟨z, hz, hsum⟩ := Nat.find_spec hP
  refine ⟨p, z, ?_, hz, hsum⟩
  by_contra hdep
  rcases Fintype.not_linearIndependent_iff.mp hdep with
    ⟨μ, hμsum, i, hμi⟩
  have hpne : Nonempty (Fin p) := ⟨i⟩
  obtain ⟨k, -, hkmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin p))
      (fun j => |μ j|) Finset.univ_nonempty
  have hkpos : 0 < |μ k| := by
    have hiabs : 0 < |μ i| := abs_pos.mpr hμi
    exact hiabs.trans_le (hkmax i (Finset.mem_univ i))
  let ν : Fin p → ℝ := if 0 < μ k then μ else fun j => -μ j
  have hνk : 0 < ν k := by
    by_cases hk : 0 < μ k
    · simp [ν, hk]
    · have hmuk : μ k < 0 := lt_of_le_of_ne (le_of_not_gt hk)
          (abs_pos.mp hkpos)
      simp [ν, hk, hmuk]
  have hνsum : ∑ j, ν j • z j = 0 := by
    by_cases hk : 0 < μ k
    · simpa [ν, hk] using hμsum
    · calc
        ∑ j, ν j • z j = -∑ j, μ j • z j := by
          simp [ν, hk, Finset.sum_neg_distrib]
        _ = 0 := by simp [hμsum]
  have hνle : ∀ j, ν j ≤ ν k := by
    intro j
    have habs : |μ j| ≤ |μ k| := hkmax j (Finset.mem_univ j)
    by_cases hk : 0 < μ k
    · have hmuk : |μ k| = μ k := abs_of_pos hk
      calc
        ν j ≤ |μ j| := by
          simp only [ν, if_pos hk]
          exact le_abs_self _
        _ ≤ |μ k| := habs
        _ = ν k := by simp [ν, hk, hmuk]
    · have hmuk : μ k < 0 := lt_of_le_of_ne (le_of_not_gt hk)
          (abs_pos.mp hkpos)
      calc
        ν j = -μ j := by simp [ν, hk]
        _ ≤ |μ j| := neg_le_abs _
        _ ≤ |μ k| := habs
        _ = -μ k := abs_of_neg hmuk
        _ = ν k := by simp [ν, hk]
  let z' : Fin p → E := fun j => (1 - ν j / ν k) • z j
  have hz' : ∀ j, z' j ∈ K := by
    intro j
    apply hcone.smul_mem (hz j)
    exact sub_nonneg.mpr ((div_le_one hνk).2 (hνle j))
  have hz'k : z' k = 0 := by
    simp [z', (ne_of_gt hνk)]
  have hsum' : ∑ j, z' j = x := by
    calc
      ∑ j, z' j =
          ∑ j, z j - (ν k)⁻¹ • ∑ j, ν j • z j := by
            simp only [z', sub_smul, one_smul, div_eq_mul_inv,
              mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [smul_smul, smul_smul, mul_comm]
      _ = x := by simp [hνsum, hsum]
  let s : Finset (Fin p) := Finset.univ.erase k
  let q : ℕ := s.card
  let e : (↥s) ≃ Fin q := by
    simpa [q] using Fintype.equivFin (↥s)
  let u : Fin q → E := fun r => z' (e.symm r)
  have huK : ∀ r, u r ∈ K := fun r => hz' _
  have husum : ∑ r, u r = x := by
    calc
      ∑ r, u r = ∑ a : ↥s, z' a := by
        exact (Fintype.sum_equiv e (fun a : ↥s => z' a) u
          (fun a => by simp [u])).symm
      _ = ∑ j ∈ s, z' j := by
        simpa using Finset.sum_attach s z'
      _ = ∑ j, z' j := by
        exact Finset.sum_erase Finset.univ hz'k
      _ = x := hsum'
  have hqP : P q := ⟨u, huK, husum⟩
  have hq : q < p := by
    have hkmem : k ∈ (Finset.univ : Finset (Fin p)) := Finset.mem_univ k
    have hp0 : 0 < p := Nat.zero_lt_of_lt i.isLt
    simp [q, s, Finset.card_erase_of_mem hkmem, hp0]
  exact (Nat.find_min hP hq) hqP

/-- The independent representation in Theorem 3.15 uses at most the dimension
of the ambient space. -/
theorem exists_sum_finrank_bound_of_mem_convexHull
    {K : Set E} (hcone : IsCone K) {x : E}
    (hx : x ∈ convexHull ℝ K) :
    ∃ (p : ℕ) (z : Fin p → E), p ≤ Module.finrank ℝ E ∧
      (∀ i, z i ∈ K) ∧ ∑ i, z i = x := by
  rcases exists_linearlyIndependent_sum_of_mem_convexHull
    hcone hx with ⟨p, z, hli, hz, hsum⟩
  exact ⟨p, z, by simpa using hli.fintype_card_le_finrank, hz, hsum⟩

/-- **Theorem 3.15** (`n`-term form): in an `n`-dimensional space, the convex
hull of a cone consists exactly of sums of `n` elements of the cone. -/
theorem mem_convexHull_iff_exists_finrank_sum_mem
    {K : Set E} (hcone : IsCone K) {x : E} :
    x ∈ convexHull ℝ K ↔
      ∃ z : Fin (Module.finrank ℝ E) → E,
        (∀ i, z i ∈ K) ∧ ∑ i, z i = x := by
  constructor
  · intro hx
    let n := Module.finrank ℝ E
    rcases exists_sum_finrank_bound_of_mem_convexHull
      hcone hx with ⟨p, z, hp, hz, hsum⟩
    let β := Fin p ⊕ Fin (n - p)
    have hβ : Fintype.card β = n := by
      simp [β, n, Nat.add_sub_of_le hp]
    let e : β ≃ Fin n := Fintype.equivFinOfCardEq hβ
    let uβ : β → E := Sum.elim z (fun _ => 0)
    let u : Fin n → E := uβ ∘ e.symm
    refine ⟨u, ?_, ?_⟩
    · intro j
      dsimp [u, uβ]
      cases e.symm j with
      | inl i => exact hz i
      | inr k => exact hcone.1
    · calc
        ∑ j, u j = ∑ b : β, uβ b := by
          exact Fintype.sum_equiv e.symm _ _
            (fun j => by simp [u])
        _ = (∑ i : Fin p, z i) +
            ∑ k : Fin (n - p), (0 : E) := by
              rw [Fintype.sum_sum_type]
              simp [uβ]
        _ = x := by simp [hsum]
  · rintro ⟨z, hz, hsum⟩
    exact (mem_convexHull_iff_exists_fintype_sum_mem hcone).2
      ⟨Fin (Module.finrank ℝ E), inferInstance, z, hz, hsum⟩

/-- **Theorem 3.15** (fixed-cardinality adapted form): every point in the
convex hull of a cone is a sum of at most `finrank + 1` cone elements, encoded
by padding the family with zeroes. -/
theorem mem_convexHull_iff_exists_finrank_succ_nonnegative_combination
    {K : Set E} (hcone : IsCone K) {x : E} :
    x ∈ convexHull ℝ K ↔
      ∃ (a : Fin (Module.finrank ℝ E + 1) → ℝ)
        (z : Fin (Module.finrank ℝ E + 1) → E),
        (∀ i, 0 ≤ a i) ∧ (∀ i, z i ∈ K) ∧ ∑ i, a i • z i = x := by
  constructor
  · intro hx
    rcases (mem_convexHull_iff_exists_finrank_succ_sum_mem hcone).1 hx with
      ⟨z, hz, hsum⟩
    exact ⟨fun _ => 1, z, by simp, hz, by simpa using hsum⟩
  · rintro ⟨a, z, ha, hz, hsum⟩
    apply (mem_convexHull_iff_exists_finrank_succ_sum_mem hcone).2
    exact ⟨fun i => a i • z i,
      fun i => hcone.smul_mem (hz i) (ha i), hsum⟩

end ConvexHullOfCone

end RW
