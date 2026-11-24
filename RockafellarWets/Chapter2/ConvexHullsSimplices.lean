/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2E: Convex hulls, Carathéodory, and convexification of functions

This file formalizes Section E of Chapter 2 of Rockafellar–Wets in finite
dimensions (`n = finrank ℝ E`).

* Theorem 2.27: `con C` is the set of convex combinations `∑_{i=0}^p λᵢxᵢ`.
* Theorem 2.29 (Carathéodory): every point of `con C` lies in a simplex with
  vertices in `C` and is a convex combination of `n + 1` points of `C`; points of
  `con C` on the boundary of `con C` need only `n` points (the Chapter 3
  boundary lemma `eq_pos_convex_span_of_mem_boundary_convexHull`).
* Corollary 2.30: compactness of convex hulls.
* Proposition 2.31: the convex hull `con f` of a function (Chapter 3
  `convexHullFunction`) is the greatest convex minorant of `f` and is given by
  the infimum of `∑_{i=0}^n λᵢ f(xᵢ)` over `n + 1` points.
-/

import RockafellarWets.Chapter2.ConvexOperations
import RockafellarWets.Chapter2.ConvexHulls
import RockafellarWets.Chapter3.ConvexHullFunctionSharp
import RockafellarWets.Chapter11.ConvexHullEpigraphClosure

open Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RW

/-! ## Padding finite combinations to a fixed number of points -/

/-- A convex combination over a finite set of at most `m` points can be
written with exactly `m` (not necessarily distinct) points, the extra ones
carrying weight `0`. -/
theorem exists_fin_padding {M : Type*} [AddCommGroup M] [Module ℝ M] {m : ℕ} (T : Finset M)
    (hT : T.card ≤ m) (w : M → ℝ) (z₀ : M) :
    ∃ (lam : Fin m → ℝ) (z : Fin m → M),
      (∀ i, (z i ∈ T ∧ lam i = w (z i)) ∨ (lam i = 0 ∧ z i = z₀)) ∧
        ∑ i, lam i = ∑ p ∈ T, w p ∧ ∑ i, lam i • z i = ∑ p ∈ T, w p • p := by
  classical
  let β := T ⊕ Fin (m - T.card)
  have hβ : Fintype.card β = m := by
    simp [β, Fintype.card_sum, Nat.add_sub_of_le hT]
  let e : β ≃ Fin m := Fintype.equivFinOfCardEq hβ
  let lamβ : β → ℝ := Sum.elim (fun t ↦ w t) (fun _ ↦ 0)
  let zβ : β → M := Sum.elim (fun t ↦ (t : M)) (fun _ ↦ z₀)
  refine ⟨lamβ ∘ e.symm, zβ ∘ e.symm, fun i ↦ ?_, ?_, ?_⟩
  · rcases h : e.symm i with t | k
    · left
      simp [lamβ, zβ, h]
    · right
      simp [lamβ, zβ, h]
  · calc ∑ i, (lamβ ∘ e.symm) i = ∑ b, lamβ b := Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)
      _ = ∑ p ∈ T, w p := by
          rw [Fintype.sum_sum_type]
          simp only [lamβ, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
          exact Finset.sum_coe_sort T w
  · calc ∑ i, (lamβ ∘ e.symm) i • (zβ ∘ e.symm) i = ∑ b, lamβ b • zβ b :=
          Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)
      _ = ∑ p ∈ T, w p • p := by
          rw [Fintype.sum_sum_type]
          simp only [lamβ, zβ, Sum.elim_inl, Sum.elim_inr, zero_smul, Finset.sum_const_zero,
            add_zero]
          exact Finset.sum_coe_sort T (fun p ↦ w p • p)

/-! ## Theorem 2.27 -/

section Hulls

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Theorem 2.27**: `con C` consists of all convex combinations
`∑_{i=0}^p λᵢ xᵢ` of elements of `C`. -/
theorem convexHull_eq_finCombinations (C : Set E) :
    convexHull ℝ C = {x | ∃ (p : ℕ) (lam : Fin (p + 1) → ℝ) (y : Fin (p + 1) → E),
      (∀ i, y i ∈ C) ∧ (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • y i = x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hx
    have hne : Fintype.card ι ≠ 0 := by
      intro h
      rw [Fintype.card_eq_zero_iff] at h
      simp at hw1
    obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hne
    let e : ι ≃ Fin (p + 1) := (Fintype.equivFin ι).trans (finCongr hp)
    refine ⟨p, w ∘ e.symm, z ∘ e.symm, fun i ↦ hz _, fun i ↦ hw0 _, ?_, ?_⟩
    · rw [← hw1]
      exact Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)
    · rw [← hsum]
      exact Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)
  · rintro ⟨p, lam, y, hy, hlam0, hlam1, rfl⟩
    exact (convex_convexHull ℝ C).sum_mem (fun i _ ↦ hlam0 i) hlam1
      (fun i _ ↦ subset_convexHull ℝ C (hy i))

end Hulls

/-! ## Theorem 2.29 and Corollary 2.30 -/

section Caratheodory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 2.29 (Carathéodory)**: every point of `con C` belongs to a simplex
with vertices in `C`, and is a convex combination of `n + 1` (not necessarily
distinct) points of `C`. -/
theorem caratheodory_simplex {C : Set E} {x : E} (hx : x ∈ convexHull ℝ C) :
    (∃ t : Finset E, ↑t ⊆ C ∧ AffineIndependent ℝ ((↑) : t → E) ∧ x ∈ convexHull ℝ ↑t) ∧
      ∃ (lam : Fin (Module.finrank ℝ E + 1) → ℝ) (y : Fin (Module.finrank ℝ E + 1) → E),
        (∀ i, y i ∈ C) ∧ (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • y i = x := by
  have hx' := hx
  rw [convexHull_eq_union] at hx'
  simp only [mem_iUnion, exists_prop] at hx'
  obtain ⟨t, htC, hai, hxt⟩ := hx'
  refine ⟨⟨t, htC, hai, hxt⟩, ?_⟩
  have hcard : t.card ≤ Module.finrank ℝ E + 1 := by
    have h := hai.card_le_finrank_succ
    rw [Fintype.card_coe] at h
    exact h.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxt
  obtain ⟨c, hc⟩ : C.Nonempty := (convexHull_nonempty_iff.mp ⟨x, hx⟩)
  obtain ⟨lam, y, hcases, hsum, hcomb⟩ := exists_fin_padding t hcard w c
  refine ⟨lam, y, fun i ↦ ?_, fun i ↦ ?_, hsum.trans hw1, hcomb.trans hwx⟩
  · rcases hcases i with ⟨hy, -⟩ | ⟨-, hy⟩
    · exact htC hy
    · rw [hy]; exact hc
  · rcases hcases i with ⟨hy, hl⟩ | ⟨hl, -⟩
    · rw [hl]; exact hw0 _ hy
    · rw [hl]

/-- **Theorem 2.29**, boundary refinement: a point of `con C` on the boundary of
`con C` is a convex combination of `n` points of `C`. -/
theorem caratheodory_boundary {C : Set E} {x : E} (hx : x ∈ convexHull ℝ C)
    (hxb : x ∉ interior (convexHull ℝ C)) :
    ∃ (lam : Fin (Module.finrank ℝ E) → ℝ) (y : Fin (Module.finrank ℝ E) → E),
      (∀ i, y i ∈ C) ∧ (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • y i = x := by
  obtain ⟨T, w, hcard, hTC, hw0, hw1, hwx⟩ :=
    exists_finite_convexCombination_of_mem_boundary_convexHull hx hxb
  obtain ⟨c, hc⟩ : C.Nonempty := (convexHull_nonempty_iff.mp ⟨x, hx⟩)
  obtain ⟨lam, y, hcases, hsum, hcomb⟩ := exists_fin_padding T hcard w c
  refine ⟨lam, y, fun i ↦ ?_, fun i ↦ ?_, hsum.trans hw1, hcomb.trans hwx⟩
  · rcases hcases i with ⟨hy, -⟩ | ⟨-, hy⟩
    · exact hTC hy
    · rw [hy]; exact hc
  · rcases hcases i with ⟨hy, hl⟩ | ⟨hl, -⟩
    · rw [hl]; exact hw0 _ hy
    · rw [hl]

/-- **Corollary 2.30**: the convex hull of a compact set is compact; in
particular convex hulls of finite sets, and simplices, are compact. -/
theorem isCompact_convexHull_and_finite {C : Set E} :
    (IsCompact C → IsCompact (convexHull ℝ C)) ∧ (C.Finite → IsCompact (convexHull ℝ C)) :=
  ⟨isCompact_convexHull, fun h ↦ h.isCompact_convexHull⟩

end Caratheodory

/-! ## Proposition 2.31 -/

section Convexification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The convex hull function is convex in the sense of Definition 2.1. -/
theorem isConvexRelative_convexHullFunction (f : E → EReal) :
    IsConvexRelative univ (convexHullFunction f) :=
  (isConvexRelative_univ_iff _).mpr (convex_epigraph_convexHullFunction f)

/-- `con f` is the greatest convex function majorized by `f`. -/
theorem convexHullFunction_isGreatest (f : E → EReal) :
    IsConvexRelative univ (convexHullFunction f) ∧ convexHullFunction f ≤ f ∧
      ∀ g : E → EReal, IsConvexRelative univ g → g ≤ f → g ≤ convexHullFunction f := by
  refine ⟨isConvexRelative_convexHullFunction f, convexHullFunction_le_all f, ?_⟩
  intro g hg hgf x
  have hsub : convexHull ℝ (epigraph f) ⊆ epigraph g :=
    convexHull_min (epigraph_subset_epigraph_iff.mpr hgf) ((isConvexRelative_univ_iff g).mp hg)
  refine le_iInf fun a ↦ ?_
  exact (mem_epigraph_iff g x a).mp (hsub a.2)

/-- `f = con f` exactly when `f` is convex. -/
theorem convexHullFunction_eq_self_iff (f : E → EReal) :
    convexHullFunction f = f ↔ IsConvexRelative univ f := by
  constructor
  · intro h
    rw [← h]
    exact isConvexRelative_convexHullFunction f
  · intro hf
    exact le_antisymm (convexHullFunction_le_all f)
      ((convexHullFunction_isGreatest f).2.2 f hf le_rfl)

/-- Any convex combination of finitely many values of `f` dominates `con f`. -/
theorem convexHullFunction_le_finiteInfAddition {f : E → EReal} {m : ℕ} {lam : Fin m → ℝ}
    {y : Fin m → E} (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    convexHullFunction f (∑ i, lam i • y i) ≤
      finiteInfAddition (fun i ↦ (lam i : EReal) * f (y i)) := by
  have hg := (convexHullFunction_isGreatest f).1
  have hJ := (isConvexRelative_iff_jensen convex_univ _).mp hg
  calc convexHullFunction f (∑ i, lam i • y i)
      ≤ finiteInfAddition (fun i ↦ (lam i : EReal) * convexHullFunction f (y i)) := by
        cases m with
        | zero => simp at h1
        | succ p => exact hJ p lam y h0 h1 (fun _ ↦ mem_univ _)
    _ ≤ finiteInfAddition (fun i ↦ (lam i : EReal) * f (y i)) := by
        refine le_iInf fun r ↦ ?_
        refine finiteInfAddition_le_sum fun i ↦ ?_
        exact (mul_le_mul_of_nonneg_left (convexHullFunction_le_all f (y i))
          (EReal.coe_nonneg.mpr (h0 i))).trans (r.2 i)

variable [FiniteDimensional ℝ E]

/-- Every point `(x, α)` of `con(epi f)` is dominated by a convex combination of
`n + 1` values of `f`, using the boundary form of Carathéodory's theorem in
`E × ℝ`. -/
theorem exists_fin_combination_le_of_mem_convexHull_epigraph {f : E → EReal} {x : E} {a : ℝ}
    (h : (x, a) ∈ convexHull ℝ (epigraph f)) :
    ∃ (lam : Fin (Module.finrank ℝ E + 1) → ℝ) (y : Fin (Module.finrank ℝ E + 1) → E),
      (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • y i = x ∧
        finiteInfAddition (fun i ↦ (lam i : EReal) * f (y i)) ≤ (a : EReal) := by
  classical
  rw [convexHull_eq_union_convexHull_finite_subsets] at h
  simp only [mem_iUnion, exists_prop] at h
  obtain ⟨T, hTepi, hxT⟩ := h
  set K := convexHull ℝ (↑T : Set (E × ℝ)) with hK
  have hKc : IsCompact K := T.finite_toSet.isCompact_convexHull
  set L := {t : ℝ | (x, t) ∈ K} with hL
  have hLc : IsClosed L := hKc.isClosed.preimage (by fun_prop)
  have hLne : L.Nonempty := ⟨a, hxT⟩
  have hLb : BddBelow L := by
    obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall 0
    refine ⟨-R, fun t ht ↦ ?_⟩
    have hmem := hR ht
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    have : |t| ≤ R := by
      have := (norm_snd_le (x, t)).trans hmem
      simpa [Real.norm_eq_abs] using this
    linarith [neg_abs_le t]
  set v := sInf L with hv
  have hvL : v ∈ L := hLc.csInf_mem hLne hLb
  have hva : v ≤ a := csInf_le hLb hxT
  have hnotint : (x, v) ∉ interior K := by
    intro hint
    have hev : ∀ᶠ t in 𝓝 v, (x, t) ∈ K :=
      ((continuous_const.prodMk continuous_id).tendsto v).eventually
        (mem_interior_iff_mem_nhds.mp hint)
    obtain ⟨t, ht, htv⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Iio v ∈ 𝓝[<] v)).exists
    exact absurd (csInf_le hLb ht) (not_le.mpr htv)
  obtain ⟨T', w, hcard, hT'T, hw0, hw1, hwx⟩ :=
    exists_finite_convexCombination_of_mem_boundary_convexHull hvL hnotint
  have hcard' : T'.card ≤ Module.finrank ℝ E + 1 := by
    rw [Module.finrank_prod, Module.finrank_self] at hcard
    exact hcard
  obtain ⟨lam, z, hcases, hsum, hcomb⟩ := exists_fin_padding T' hcard' w (x, 0)
  have hmemT' : ∀ i, (z i ∈ T' ∧ lam i = w (z i)) ∨ (lam i = 0 ∧ z i = (x, 0)) := hcases
  have hlam0 : ∀ i, 0 ≤ lam i := by
    intro i
    rcases hmemT' i with ⟨hz, hl⟩ | ⟨hl, -⟩
    · rw [hl]; exact hw0 _ hz
    · rw [hl]
  have hfst : ∑ i, lam i • (z i).1 = x := by
    have := congrArg Prod.fst (hcomb.trans hwx)
    simpa [Prod.fst_sum] using this
  have hsnd : ∑ i, lam i * (z i).2 = v := by
    have := congrArg Prod.snd (hcomb.trans hwx)
    simpa [Prod.snd_sum] using this
  refine ⟨lam, fun i ↦ (z i).1, hlam0, hsum.trans hw1, hfst, ?_⟩
  have hterm : ∀ i, (lam i : EReal) * f (z i).1 ≤ ((lam i * (z i).2 : ℝ) : EReal) := by
    intro i
    rcases hmemT' i with ⟨hz, -⟩ | ⟨hl, -⟩
    · have hepi : f (z i).1 ≤ ((z i).2 : EReal) := hTepi (hT'T hz)
      rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left hepi (EReal.coe_nonneg.mpr (hlam0 i))
    · simp [hl]
  calc finiteInfAddition (fun i ↦ (lam i : EReal) * f (z i).1)
      ≤ ((∑ i, lam i * (z i).2 : ℝ) : EReal) := finiteInfAddition_le_sum hterm
    _ = (v : EReal) := by rw [hsnd]
    _ ≤ (a : EReal) := EReal.coe_le_coe_iff.mpr hva

/-- **Proposition 2.31 (convexification of a function)**: in `ℝⁿ`,
`con f(x) = inf { ∑_{i=0}^n λᵢ f(xᵢ) | ∑ λᵢ xᵢ = x, λᵢ ≥ 0, ∑ λᵢ = 1 }`, the sums
formed with inf-addition and `0 · ∞ = 0`. -/
theorem convexHullFunction_eq_iInf (f : E → EReal) (x : E) :
    convexHullFunction f x =
      ⨅ (q : {q : (Fin (Module.finrank ℝ E + 1) → ℝ) × (Fin (Module.finrank ℝ E + 1) → E) //
          (∀ i, 0 ≤ q.1 i) ∧ ∑ i, q.1 i = 1 ∧ ∑ i, q.1 i • q.2 i = x}),
        finiteInfAddition (fun i ↦ (q.1.1 i : EReal) * f (q.1.2 i)) := by
  apply le_antisymm
  · refine le_iInf fun q ↦ ?_
    obtain ⟨⟨lam, y⟩, h0, h1, hx⟩ := q
    change convexHullFunction f x ≤ finiteInfAddition (fun i ↦ (lam i : EReal) * f (y i))
    change ∑ i, lam i • y i = x at hx
    calc convexHullFunction f x = convexHullFunction f (∑ i, lam i • y i) := by rw [hx]
      _ ≤ _ := convexHullFunction_le_finiteInfAddition h0 h1
  · refine le_iInf fun a ↦ ?_
    obtain ⟨lam, y, h0, h1, hx, hle⟩ := exists_fin_combination_le_of_mem_convexHull_epigraph a.2
    exact (iInf_le_of_le ⟨(lam, y), h0, h1, hx⟩ le_rfl).trans hle

end Convexification

end RW
