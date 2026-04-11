/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3B: Pointed Cones and Convex Hulls

This file formalizes the next cone-theoretic results from Chapter 3 of
Rockafellar & Wets, "Variational Analysis":
- Definition 3.13: pointed cones
- Proposition 3.14: pointedness of convex cones
- Theorem 3.15: the basic finite-sum characterization of `convexHull` for cones
-/

import RockafellarWets.Chapter3.Cones
import RockafellarWets.Chapter3.LinearImages
import RockafellarWets.Chapter2.ConvexHulls

open scoped BigOperators Pointwise
open Set

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 3.13**: a cone is pointed if no finite sum of its elements can
equal `0` unless every summand already vanishes. -/
def IsPointed (K : Set E) : Prop :=
  ∀ n : ℕ, ∀ z : Fin n → E, (∀ i, z i ∈ K) → (∑ i, z i) = 0 → ∀ i, z i = 0

/-- Pointedness is inherited by subsets. -/
theorem IsPointed.mono {K L : Set E} (hL : IsPointed L) (hKL : K ⊆ L) :
    IsPointed K := by
  intro n z hz hsum i
  exact hL n z (fun j => hKL (hz j)) hsum i

/-- A pointed cone annihilates any vanishing finite sum indexed by an arbitrary
finite type. -/
theorem IsPointed.fintype {K : Set E} (hK : IsPointed K)
    {ι : Type*} [Fintype ι] (z : ι → E) (hz : ∀ i, z i ∈ K)
    (hsum : ∑ i, z i = 0) :
    ∀ i, z i = 0 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hsum' : ∑ j : Fin (Fintype.card ι), z (e.symm j) = 0 := by
    calc
      ∑ j : Fin (Fintype.card ι), z (e.symm j)
          = ∑ i : ι, z i := by
              symm
              exact Fintype.sum_equiv e (fun i => z i) (fun j => z (e.symm j))
                (by intro i; simp)
      _ = 0 := hsum
  have hz' : ∀ j : Fin (Fintype.card ι), z (e.symm j) ∈ K := by
    intro j
    exact hz (e.symm j)
  have hzero := hK (Fintype.card ι) (fun j => z (e.symm j)) hz' hsum'
  intro i
  simpa using hzero (e i)

/-- A closed cone coincides with its asymptotic cone. -/
theorem asymptoticCone_eq_self_of_isClosed_isCone {K : Set E}
    (hclosed : IsClosed K) (hcone : IsCone K) :
    asymptoticCone ℝ K = K := by
  calc
    asymptoticCone ℝ K = closure K := by
      exact asymptoticCone_eq_closure_of_forall_smul_mem fun c hc x hx =>
        hcone.2 hx hc
    _ = K := hclosed.closure_eq

/-- A closed cone coincides with its horizon cone. -/
theorem horizonCone_eq_self_of_isClosed_isCone {K : Set E}
    (hclosed : IsClosed K) (hcone : IsCone K) :
    horizonCone K = K := by
  have hne : K.Nonempty := ⟨0, hcone.1⟩
  rw [horizonCone_eq_asymptoticCone hne]
  exact asymptoticCone_eq_self_of_isClosed_isCone hclosed hcone

/-- Finite sums of elements of a convex cone remain in the cone. -/
theorem sum_mem_of_convex_isCone {K : Set E} (hconv : Convex ℝ K) (hcone : IsCone K)
    {ι : Type*} (s : Finset ι) (z : ι → E) (hz : ∀ i ∈ s, z i ∈ K) :
    Finset.sum s z ∈ K := by
  classical
  have hadd : ∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K :=
    (hcone.convex_iff_add_mem).1 hconv
  induction s using Finset.induction_on with
  | empty =>
      simpa using hcone.1
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd (hz a (Finset.mem_insert_self a s))
        (ih fun i hi => hz i (Finset.mem_insert_of_mem hi))

/-- **Proposition 3.14**: for a convex cone, pointedness is equivalent to the
usual condition `K ∩ (-K) = {0}`. -/
theorem isPointed_iff_inter_neg_eq_singleton_zero
    {K : Set E} (hconv : Convex ℝ K) (hcone : IsCone K) :
    IsPointed K ↔ K ∩ -K = ({0} : Set E) := by
  constructor
  · intro hpointed
    apply le_antisymm
    · intro x hx
      have hxK : x ∈ K := hx.1
      have hnegxK : -x ∈ K := by
        simpa using hx.2
      have hzero := hpointed 2 (fun i => if i = 0 then x else -x)
        (by
          intro i
          fin_cases i <;> simp [hxK, hnegxK])
        (by
          rw [Fin.sum_univ_two]
          simp)
      have hx0 : x = 0 := by
        simpa using hzero 0
      simp [hx0]
    · intro x hx
      have hx0 : x = 0 := by
        simpa using hx
      subst x
      constructor
      · exact hcone.1
      · simpa using hcone.1
  · intro hzero n
    induction n with
    | zero =>
        intro z hz hsum i
        exact Fin.elim0 i
    | succ n ih =>
        intro z hz hsum i
        have hsum0 : z 0 + ∑ j : Fin n, z j.succ = 0 := by
          simpa [Fin.sum_univ_succ] using hsum
        have htail : (∑ j : Fin n, z j.succ) ∈ K := by
          simpa using
            sum_mem_of_convex_isCone hconv hcone (Finset.univ : Finset (Fin n))
              (fun j : Fin n => z j.succ) (by intro j _; exact hz j.succ)
        have hz0 : z 0 = 0 := by
          have hnegz0 : -z 0 ∈ K := by
            have hEq : ∑ j : Fin n, z j.succ = -z 0 := by
              rw [eq_neg_iff_add_eq_zero]
              simpa [add_comm] using hsum0
            simpa [hEq] using htail
          have hzint : z 0 ∈ K ∩ -K := by
            refine ⟨hz 0, ?_⟩
            simpa using hnegz0
          have : z 0 ∈ ({0} : Set E) := by
            simpa [hzero] using hzint
          simpa using this
        obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
        · exact hz0
        · have hsum' : (∑ j : Fin n, z j.succ) = 0 := by
            simpa [Fin.sum_univ_succ, hz0] using hsum
          exact ih (fun j : Fin n => z j.succ) (fun j => hz j.succ) hsum' j

/-- **Theorem 3.15** (first characterization): a vector lies in the convex hull
of a cone iff it is a finite sum of elements of that cone. -/
theorem mem_convexHull_iff_exists_fintype_sum_mem
    {K : Set E} (hcone : IsCone K) {x : E} :
    x ∈ convexHull ℝ K ↔
      ∃ (ι : Type) (_ : Fintype ι) (z : ι → E), (∀ i, z i ∈ K) ∧ ∑ i, z i = x := by
  constructor
  · intro hx
    obtain ⟨ι, _, w, z, hw0, _hw1, hzK, hsum⟩ :=
      (mem_convexHull_iff_exists_fintype (R := ℝ) (s := K) (x := x)).mp hx
    refine ⟨ι, inferInstance, fun i => w i • z i, ?_, ?_⟩
    · intro i
      exact hcone.smul_mem (hzK i) (hw0 i)
    · simpa using hsum
  · rintro ⟨ι, _, z, hz, hsum⟩
    by_cases hι : Nonempty ι
    · let n : ℝ := Fintype.card ι
      have hcard : n ≠ 0 := by
        dsimp [n]
        exact_mod_cast Fintype.card_ne_zero
      refine mem_convexHull_of_exists_fintype
        (w := fun _ : ι => n⁻¹) (z := fun i => n • z i) ?_ ?_ ?_ ?_
      · intro i
        exact inv_nonneg.mpr (by
          dsimp [n]
          positivity)
      · dsimp [n]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard]
      · intro i
        exact hcone.smul_mem (hz i) (by
          dsimp [n]
          positivity)
      · calc
          ∑ i, n⁻¹ • (n • z i) = ∑ i, z i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]
          _ = x := hsum
    · letI : IsEmpty ι := not_nonempty_iff.mp hι
      have hx0 : x = 0 := by
        simpa using hsum.symm
      simpa [hx0] using (subset_convexHull ℝ K hcone.1)

/-- In finite dimension, every point of the convex hull of a cone can be written
as a sum of exactly `finrank + 1` elements of the cone by padding with `0`. -/
theorem mem_convexHull_iff_exists_finrank_succ_sum_mem
    [FiniteDimensional ℝ E] {K : Set E} (hcone : IsCone K) {x : E} :
    x ∈ convexHull ℝ K ↔
      ∃ z : Fin (Module.finrank ℝ E + 1) → E, (∀ i, z i ∈ K) ∧ ∑ i, z i = x := by
  constructor
  · intro hx
    let n : ℕ := Module.finrank ℝ E + 1
    obtain ⟨ι, _, z, w, hzK, hAI, hwpos, hw1, hcomb⟩ :=
      eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hx
    have hzmem : ∀ i, z i ∈ K := by
      intro i
      exact hzK ⟨i, rfl⟩
    have hcard : Fintype.card ι ≤ n := by
      dsimp [n]
      exact hAI.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    let β := ι ⊕ Fin (n - Fintype.card ι)
    have hβ : Fintype.card β = n := by
      simp [β, n, Nat.add_sub_of_le hcard]
    let e : β ≃ Fin n := Fintype.equivFinOfCardEq hβ
    let uβ : β → E := Sum.elim (fun i => w i • z i) (fun _ => 0)
    let u : Fin n → E := uβ ∘ e.symm
    refine ⟨u, ?_, ?_⟩
    · intro j
      dsimp [u, uβ]
      cases h : e.symm j with
      | inl i =>
          exact hcone.smul_mem (hzmem i) (hwpos i).le
      | inr k =>
          simpa using hcone.1
    · calc
        ∑ j, u j = ∑ b : β, uβ b := by
          exact Fintype.sum_equiv e.symm _ _ (by intro j; rfl)
        _ = (∑ i : ι, w i • z i) + ∑ k : Fin (n - Fintype.card ι), (0 : E) := by
              rw [Fintype.sum_sum_type]
              simp [uβ]
        _ = x := by simpa [hcomb]
  · rintro ⟨z, hz, hsum⟩
    exact (mem_convexHull_iff_exists_fintype_sum_mem hcone).2
      ⟨Fin (Module.finrank ℝ E + 1), inferInstance, z, hz, hsum⟩

private def sumLinearMap {ι : Type*} [Fintype ι] : (ι → E) →ₗ[ℝ] E where
  toFun z := ∑ i, z i
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.smul_sum]

/-- The product of finitely many copies of a cone is a cone. -/
theorem isCone_pi_univ {ι : Type*} [Fintype ι] {K : Set E} (hcone : IsCone K) :
    IsCone (Set.pi Set.univ (fun _ : ι => K)) := by
  refine ⟨?_, ?_⟩
  · simpa [Set.mem_pi] using (fun _ : ι => hcone.1)
  · intro z hz c hc
    have hzK : ∀ i : ι, z i ∈ K := by
      simpa [Set.mem_pi] using hz
    have hcz : ∀ i : ι, (c • z) i ∈ K := by
      intro i
      simpa using hcone.smul_mem (hzK i) hc.le
    simpa [Set.mem_pi] using hcz

/-- In finite dimension, the convex hull of a cone is the image of a fixed
finite product of that cone under the summation map. -/
theorem convexHull_eq_image_sumLinearMap_pi_finrank_succ
    [FiniteDimensional ℝ E] {K : Set E} (hcone : IsCone K) :
    (convexHull ℝ K : Set E) =
      sumLinearMap (ι := Fin (Module.finrank ℝ E + 1)) ''
        Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E + 1) => K) := by
  ext x
  constructor
  · intro hx
    rcases (mem_convexHull_iff_exists_finrank_succ_sum_mem hcone).1 hx with ⟨z, hz, hsum⟩
    refine ⟨z, ?_, ?_⟩
    · simpa [Set.mem_pi] using hz
    · simpa [sumLinearMap, hsum]
  · rintro ⟨z, hz, rfl⟩
    have hzK : ∀ i, z i ∈ K := by
      simpa [Set.mem_pi] using hz
    exact (mem_convexHull_iff_exists_finrank_succ_sum_mem hcone).2 ⟨z, hzK, rfl⟩

/-- The convex hull of a cone is again a cone. -/
theorem isCone_convexHull {K : Set E} (hcone : IsCone K) :
    IsCone (convexHull ℝ K : Set E) := by
  refine ⟨subset_convexHull ℝ K hcone.1, ?_⟩
  intro x hx c hc
  rcases (mem_convexHull_iff_exists_fintype_sum_mem hcone).1 hx with
    ⟨ι, _, z, hz, hsum⟩
  refine (mem_convexHull_iff_exists_fintype_sum_mem hcone).2
    ⟨ι, inferInstance, fun i => c • z i, ?_, ?_⟩
  · intro i
    exact hcone.2 (hz i) hc
  · calc
      ∑ i, c • z i = c • ∑ i, z i := by simp [Finset.smul_sum]
      _ = c • x := by rw [hsum]

/-- The convex hull of a pointed cone remains pointed. -/
theorem isPointed_convexHull {K : Set E} (hcone : IsCone K) (hpointed : IsPointed K) :
    IsPointed (convexHull ℝ K : Set E) := by
  intro n z hz hsum i
  classical
  choose ι hι u hu hsumu using fun j =>
    (mem_convexHull_iff_exists_fintype_sum_mem hcone).1 (hz j)
  letI : ∀ j, Fintype (ι j) := hι
  let α := Σ j, ι j
  let v : α → E := fun a => u a.1 a.2
  have hv : ∀ a : α, v a ∈ K := by
    intro a
    exact hu a.1 a.2
  have hsumv : ∑ a : α, v a = 0 := by
    calc
      ∑ a : α, v a = ∑ j, ∑ k, u j k := by
        simp [v, α, Fintype.sum_sigma]
      _ = ∑ j, z j := by
        simp [hsumu]
      _ = 0 := hsum
  have hvzero : ∀ a : α, v a = 0 := hpointed.fintype v hv hsumv
  calc
    z i = ∑ k, u i k := (hsumu i).symm
    _ = ∑ k, (0 : E) := by
          apply Fintype.sum_congr
          intro k
          simpa [v] using hvzero ⟨i, k⟩
    _ = 0 := by simp

/-- For a pointed cone, the convex hull has trivial intersection with its
negative. -/
theorem inter_neg_convexHull_eq_singleton_zero {K : Set E}
    (hcone : IsCone K) (hpointed : IsPointed K) :
    (convexHull ℝ K : Set E) ∩ -convexHull ℝ K = ({0} : Set E) := by
  exact (isPointed_iff_inter_neg_eq_singleton_zero
    (convex_convexHull ℝ K) (isCone_convexHull hcone)).mp
      (isPointed_convexHull hcone hpointed)

/-- **Theorem 3.15** (closedness consequence): in finite dimension, the convex
hull of a closed pointed cone is closed. -/
theorem isClosed_convexHull_of_isClosed_isPointed
    [FiniteDimensional ℝ E] {K : Set E}
    (hclosed : IsClosed K) (hcone : IsCone K) (hpointed : IsPointed K) :
    IsClosed (convexHull ℝ K : Set E) := by
  let n : ℕ := Module.finrank ℝ E + 1
  let S : Set (Fin n → E) := Set.pi Set.univ (fun _ : Fin n => K)
  have hSclosed : IsClosed S := by
    exact isClosed_set_pi fun _ _ => hclosed
  have hScone : IsCone S := isCone_pi_univ (ι := Fin n) hcone
  have hker :
      ∀ ⦃v : Fin n → E⦄, v ∈ horizonCone S → sumLinearMap v = 0 → v = 0 := by
    intro v hv hsum
    have hvS : v ∈ S := by
      simpa [horizonCone_eq_self_of_isClosed_isCone hSclosed hScone] using hv
    have hvK : ∀ i, v i ∈ K := by
      simpa [S, Set.mem_pi] using hvS
    have hv0 : ∀ i, v i = 0 := hpointed.fintype v hvK (by simpa [sumLinearMap] using hsum)
    funext i
    exact hv0 i
  have himage :
      IsClosed (sumLinearMap (ι := Fin n) '' S) :=
    isClosed_linearImage_of_horizonCone_ker_trivial
      (L := sumLinearMap (ι := Fin n)) (C := S) hSclosed hker
  have hEq :
      sumLinearMap (ι := Fin n) '' S = convexHull ℝ K := by
    simpa [S, n] using
      (convexHull_eq_image_sumLinearMap_pi_finrank_succ (E := E) hcone).symm
  simpa [hEq] using himage

/-- **Theorem 3.15** (final consequence): in finite dimension, the convex hull
of a closed pointed cone is again closed and pointed. -/
theorem isClosed_isPointed_convexHull_of_isClosed_isPointed
    [FiniteDimensional ℝ E] {K : Set E}
    (hclosed : IsClosed K) (hcone : IsCone K) (hpointed : IsPointed K) :
    IsClosed (convexHull ℝ K : Set E) ∧ IsPointed (convexHull ℝ K : Set E) := by
  exact ⟨isClosed_convexHull_of_isClosed_isPointed hclosed hcone hpointed,
    isPointed_convexHull hcone hpointed⟩

end RW
