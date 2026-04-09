/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2E: Convex Hulls

This file formalizes Section E of Chapter 2 of Rockafellar & Wets,
"Variational Analysis":
- Theorem 2.27: Convex hull = set of all convex combinations
- Theorem 2.29: Caratheodory's theorem
- Corollary 2.30: Compactness of convex hulls of compact sets
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Convex

set_option linter.style.openClassical false

open Set Filter Topology Classical Finset

noncomputable section

namespace RW

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-! ## Theorem 2.27: Convex hull as set of convex combinations

The convex hull of a set `S` is the set of all finite convex combinations
of elements of `S`. In Mathlib, this is `convexHull_eq`. -/

/-- **Theorem 2.27**: The convex hull of `S` equals the set of all finite
convex combinations of points in `S`. This is a restatement of Mathlib's
`convexHull_eq`. -/
theorem convexHull_eq_convex_combinations (S : Set E) :
    (convexHull ℝ S : Set E) =
      {x | ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → E),
        (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = x} := by
  ext x
  exact mem_convexHull_iff_exists_fintype

/-- The convex hull of a set is the smallest convex set containing it.
This is `convexHull_min` in Mathlib. -/
theorem convexHull_minimal {S T : Set E} (hST : S ⊆ T) (hT : Convex ℝ T) :
    (convexHull ℝ S : Set E) ⊆ T :=
  convexHull_min hST hT

/-- A set is convex iff it equals its own convex hull.
This is `Convex.convexHull_eq` in Mathlib. -/
theorem convex_iff_eq_convexHull (S : Set E) :
    Convex ℝ S ↔ (convexHull ℝ S : Set E) = S := by
  constructor
  · exact fun h => h.convexHull_eq
  · intro h
    rw [← h]
    exact convex_convexHull ℝ S

/-! ## Theorem 2.29: Caratheodory's theorem

Every point in the convex hull of a set `S ⊆ ℝⁿ` can be expressed as a
convex combination of at most `n + 1` points of `S`. -/

/-- **Theorem 2.29 (Caratheodory)**: In a finite-dimensional space of
dimension `d`, every point of `convexHull ℝ S` is a convex combination
of at most `d + 1` points of `S`. -/
theorem caratheodory [FiniteDimensional ℝ E] (S : Set E) (x : E)
    (hx : x ∈ convexHull ℝ S) :
    ∃ (T : Finset E), ↑T ⊆ S ∧ T.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑T : Set E) := by
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨T, hTS, hAI, hxT⟩ := hx
  refine ⟨T, hTS, ?_, hxT⟩
  have h := hAI.card_le_finrank_succ
  rw [Fintype.card_coe] at h
  exact h.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)

end RW

/-! ## Corollary 2.30: Compactness of convex hulls -/

namespace RW

/-- **Corollary 2.30**: In a finite-dimensional normed space, the convex hull
of a compact set is compact. -/
theorem isCompact_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S : Set E) := by
  by_cases hSne : S.Nonempty
  · letI : CompactSpace S := (isCompact_iff_compactSpace.mp hS)
    let n : ℕ := Module.finrank ℝ E + 1
    let s0 : S := ⟨hSne.choose, hSne.choose_spec⟩
    let Φ : ((Fin n → S) × stdSimplex ℝ (Fin n)) → E :=
      fun p => ∑ i, ((p.2 : Fin n → ℝ) i) • (((p.1 i : S) : E))
    have hΦ : Continuous Φ := by
      refine continuous_finset_sum _ ?_
      intro i _
      have hw : Continuous fun p : (Fin n → S) × stdSimplex ℝ (Fin n) =>
          ((p.2 : Fin n → ℝ) i) :=
        (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
      have hz : Continuous fun p : (Fin n → S) × stdSimplex ℝ (Fin n) =>
          (((p.1 i : S) : E)) :=
        continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
      exact hw.smul hz
    have hsubset : Set.range Φ ⊆ convexHull ℝ S := by
      rintro x ⟨p, rfl⟩
      apply mem_convexHull_of_exists_fintype (w := fun i => ((p.2 : Fin n → ℝ) i))
        (z := fun i => (((p.1 i : S) : E)))
      · intro i
        exact stdSimplex.zero_le p.2 i
      · exact stdSimplex.sum_eq_one p.2
      · intro i
        exact (p.1 i).2
      · rfl
    have hsupset : convexHull ℝ S ⊆ Set.range Φ := by
      intro x hx
      obtain ⟨ι, _, z, w, hzS, hAI, hwpos, hw1, hcomb⟩ :=
        eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hx
      have hcard : Fintype.card ι ≤ n := by
        exact (hAI.card_le_finrank_succ).trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      let β := ι ⊕ Fin (n - Fintype.card ι)
      have hβ : Fintype.card β = n := by
        simp [β, n, Nat.add_sub_of_le hcard]
      let e : β ≃ Fin n := Fintype.equivFinOfCardEq hβ
      let zβ : β → S :=
        Sum.elim (fun i => ⟨z i, hzS (by exact mem_range_self i)⟩) (fun _ => s0)
      let wβ : β → ℝ := Sum.elim w (fun _ => 0)
      let p1 : Fin n → S := zβ ∘ e.symm
      let p2 : Fin n → ℝ := wβ ∘ e.symm
      have hp2 : p2 ∈ stdSimplex ℝ (Fin n) := by
        refine ⟨?_, ?_⟩
        · intro j
          dsimp [p2, wβ]
          cases e.symm j with
          | inl i => exact le_of_lt (hwpos i)
          | inr k => simp
        · calc
            ∑ j, p2 j = ∑ b : β, wβ b := by
              exact Fintype.sum_equiv e.symm _ _ (by intro j; rfl)
            _ = (∑ i : ι, w i) + ∑ k : Fin (n - Fintype.card ι), (0 : ℝ) := by
              rw [Fintype.sum_sum_type]
              simp [wβ]
            _ = 1 := by simp [hw1]
      have hp : Φ (p1, ⟨p2, hp2⟩) = x := by
        calc
          Φ (p1, ⟨p2, hp2⟩)
              = ∑ j, p2 j • (((p1 j : S) : E)) := by rfl
          _ = ∑ b : β, wβ b • (((zβ b : S) : E)) := by
                exact Fintype.sum_equiv e.symm _ _ (by intro j; rfl)
          _ = (∑ i : ι, w i • z i) +
                ∑ k : Fin (n - Fintype.card ι), (0 : ℝ) • (((s0 : S) : E)) := by
                rw [Fintype.sum_sum_type]
                simp [wβ, zβ]
          _ = x := by simp [hcomb]
      exact ⟨(p1, ⟨p2, hp2⟩), hp⟩
    have hrange : Set.range Φ = convexHull ℝ S := subset_antisymm hsubset hsupset
    simpa [hrange] using isCompact_range hΦ
  · rw [not_nonempty_iff_eq_empty.mp hSne, convexHull_empty]
    exact isCompact_empty

end RW
