/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2E*: Carathéodory's theorem for connected sets (Theorem 2.29)

This file completes Theorem 2.29 of Rockafellar and Wets, *Variational
Analysis*, in a finite-dimensional real normed space `E` with
`n = finrank ℝ E ≥ 1`.

* `caratheodory_connected`, `caratheodory_connected_fin`: when `C` is
  connected, every point of `con C` is a convex combination of no more than
  `n` points of `C`.
* `caratheodory_boundary_counterexample`: the boundary clause of 2.29 must be
  read with the boundary of `con C` (as in the book's proof, see
  `caratheodory_boundary`): for the boundary of `C` itself it fails in `ℝ²`.

The proof of the connected case follows the book.  If `x = ∑ wᵢ zᵢ` with
`n + 1` affinely independent `zᵢ ∈ C` and all `wᵢ > 0`, consider the ratios
`rᵢ(y) = βᵢ(y) / wᵢ` of the barycentric coordinates `β(y)` of `y` relative to
the `zᵢ` (`SimplexTechnology`).  The open sets where `r₀` is the strict
maximum and where `r₀` is not maximal separate `z₀` from `z₁`, so `C` contains
a point `y` at which the maximum `m` of the `rᵢ(y)` is attained at `0` and at
some `k ≠ 0`; then `x = m⁻¹ y + ∑ (wᵢ - βᵢ(y)/m) zᵢ` uses neither `z₀` nor
`z_k`.
-/

import RockafellarWets.Chapter2.ConvexHullsSimplices
import RockafellarWets.Chapter2.SimplexTechnology

open Set Filter Topology Matrix Module

namespace RW

section Connected

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The core of the connected case of Theorem 2.29: a positive combination of
`n + 1` affinely independent points of a preconnected set `C` is a convex
combination of `n` points of `C`. -/
theorem exists_card_le_finrank_of_isPreconnected (hn : 0 < finrank ℝ E) {C : Set E}
    (hC : IsPreconnected C) {z : Fin (finrank ℝ E + 1) → E} (hz : AffineIndependent ℝ z)
    (hzC : ∀ i, z i ∈ C) {w : Fin (finrank ℝ E + 1) → ℝ} (hw0 : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1) {x : E} (hx : ∑ i, w i • z i = x) :
    ∃ T : Finset E, ↑T ⊆ C ∧ T.card ≤ finrank ℝ E ∧ x ∈ convexHull ℝ ↑T := by
  classical
  have hdet := (affineIndependent_iff_det_baryMatrix_ne_zero z).mp hz
  have hunit : IsUnit (baryMatrix z).det := isUnit_iff_ne_zero.mpr hdet
  -- barycentric coordinates relative to `z`
  let β : E → Fin (finrank ℝ E + 1) → ℝ := fun y ↦ (baryMatrix z)⁻¹ *ᵥ baryVec y
  have hβ : ∀ y, ∑ i, β y i = 1 ∧ ∑ i, β y i • z i = y := fun y ↦
    baryMatrix_mulVec_eq_baryVec_iff.mp (by
      simp only [β, mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec])
  have hβcont : Continuous β := continuous_const.matrix_mulVec continuous_baryVec
  have hβz : ∀ j, β (z j) = Pi.single j 1 := fun j ↦
    (eq_inv_mulVec_of_barycentric hdet (w := Pi.single j 1) (by simp) (by simp)).symm
  -- the ratios `rᵢ = βᵢ / wᵢ`
  let r : E → Fin (finrank ℝ E + 1) → ℝ := fun y i ↦ β y i / w i
  have hrcont : ∀ i, Continuous fun y ↦ r y i := fun i ↦
    ((continuous_apply i).comp hβcont).div_const _
  have hrz : ∀ j i, r (z j) i = if i = j then (w j)⁻¹ else 0 := fun j i ↦ by
    by_cases h : i = j
    · subst h
      simp [r, hβz]
    · simp [r, hβz, h]
  let U : Set E := {y | ∀ i, i ≠ 0 → r y i < r y 0}
  let V : Set E := {y | ∃ i, r y 0 < r y i}
  have hU : IsOpen U := by
    have : U = ⋂ i ∈ Finset.univ.erase (0 : Fin (finrank ℝ E + 1)), {y | r y i < r y 0} := by
      ext y
      simp [U]
    rw [this]
    exact isOpen_biInter_finset fun i _ ↦ isOpen_lt (hrcont i) (hrcont 0)
  have hV : IsOpen V := by
    have : V = ⋃ i, {y | r y 0 < r y i} := by
      ext y
      simp [V]
    rw [this]
    exact isOpen_iUnion fun i ↦ isOpen_lt (hrcont 0) (hrcont i)
  have h1 : (1 : Fin (finrank ℝ E + 1)) ≠ 0 := fun h ↦ by
    have := Fin.one_eq_zero_iff.mp h
    omega
  have h0U : z 0 ∈ U := fun i hi ↦ by
    rw [hrz, hrz, if_neg hi, if_pos rfl]
    exact inv_pos.mpr (hw0 0)
  have h1V : z 1 ∈ V := ⟨1, by
    rw [hrz, hrz, if_neg h1.symm, if_pos rfl]
    exact inv_pos.mpr (hw0 1)⟩
  -- connectedness gives a point of `C` outside `U ∪ V`
  obtain ⟨y, hyC, hyU, hyV⟩ : ∃ y ∈ C, y ∉ U ∧ y ∉ V := by
    by_contra hcon
    push_neg at hcon
    have hcover : C ⊆ U ∪ V := fun y hy ↦ by
      by_cases h : y ∈ U
      · exact Or.inl h
      · exact Or.inr (hcon y hy h)
    obtain ⟨p, -, hpU, hpV⟩ := hC U V hU hV hcover ⟨z 0, hzC 0, h0U⟩ ⟨z 1, hzC 1, h1V⟩
    obtain ⟨i, hi⟩ := hpV
    by_cases hi0 : i = 0
    · subst hi0
      exact lt_irrefl _ hi
    · exact lt_asymm hi (hpU i hi0)
  have hle : ∀ i, r y i ≤ r y 0 := fun i ↦ not_lt.mp fun h ↦ hyV ⟨i, h⟩
  obtain ⟨k, hk0, hk⟩ : ∃ k, k ≠ 0 ∧ r y k = r y 0 := by
    simp only [U, mem_setOf_eq, not_forall, not_lt] at hyU
    obtain ⟨k, hk0, hk⟩ := hyU
    exact ⟨k, hk0, le_antisymm (hle k) hk⟩
  set m := r y 0 with hmdef
  have hβw : ∀ i, β y i = r y i * w i := fun i ↦ (div_mul_cancel₀ _ (hw0 i).ne').symm
  have hm : 0 < m := by
    by_contra hm
    push_neg at hm
    have hsum : ∑ i, β y i ≤ 0 := Finset.sum_nonpos fun i _ ↦ by
      rw [hβw]
      exact mul_nonpos_of_nonpos_of_nonneg ((hle i).trans hm) (hw0 i).le
    linarith [(hβ y).1]
  -- the new weights
  let c : Fin (finrank ℝ E + 1) → ℝ := fun i ↦ w i - β y i / m
  have hc_nonneg : ∀ i, 0 ≤ c i := fun i ↦ by
    have : β y i / m ≤ w i := by
      rw [div_le_iff₀ hm, hβw]
      nlinarith [hle i, hw0 i]
    simp only [c]
    linarith
  have hc0 : c 0 = 0 := by
    simp only [c, hβw 0, ← hmdef]
    field_simp
    ring
  have hck : c k = 0 := by
    simp only [c, hβw k, hk]
    field_simp
    ring
  have hcsum : ∑ i, c i = 1 - m⁻¹ := by
    simp only [c, Finset.sum_sub_distrib, hw1, ← Finset.sum_div, (hβ y).1, one_div]
  have hcx : ∑ i, c i • z i = x - m⁻¹ • y := by
    simp only [c, sub_smul, Finset.sum_sub_distrib, hx, div_eq_inv_mul, ← smul_smul,
      ← Finset.smul_sum, (hβ y).2]
  -- the points `y, z₁, …, zₙ` with weights `m⁻¹, c₁, …, cₙ`
  let q : Fin (finrank ℝ E + 1) → E := Fin.cons y fun j ↦ z j.succ
  let c' : Fin (finrank ℝ E + 1) → ℝ := Fin.cons m⁻¹ fun j ↦ c j.succ
  have hc'k : c' k = 0 := by
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hk0
    simpa [c'] using hck
  have hc'sum : ∑ i, c' i = 1 := by
    have := hcsum
    rw [Fin.sum_univ_succ, hc0, zero_add] at this
    rw [Fin.sum_univ_succ]
    simp only [c', Fin.cons_zero, Fin.cons_succ, this]
    ring
  have hc'x : ∑ i, c' i • q i = x := by
    have := hcx
    rw [Fin.sum_univ_succ, hc0, zero_smul, zero_add] at this
    rw [Fin.sum_univ_succ]
    simp only [c', q, Fin.cons_zero, Fin.cons_succ, this]
    abel
  have hqC : ∀ i, q i ∈ C := fun i ↦ by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [q] using hyC
    · simpa [q] using hzC j.succ
  refine ⟨(Finset.univ.erase k).image q, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hp
    obtain ⟨i, -, rfl⟩ := hp
    exact hqC i
  · refine Finset.card_image_le.trans ?_
    simp [Finset.card_erase_of_mem]
  · have hsum : ∑ i ∈ Finset.univ.erase k, c' i = 1 := by
      rw [Finset.sum_erase _ hc'k, hc'sum]
    have hx' : ∑ i ∈ Finset.univ.erase k, c' i • q i = x := by
      rw [Finset.sum_erase _ (by rw [hc'k, zero_smul]), hc'x]
    rw [← hx']
    refine (convex_convexHull ℝ _).sum_mem (fun i _ ↦ ?_) hsum fun i hi ↦
      subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem q hi))
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [c'] using hm.le
    · simpa [c'] using hc_nonneg j.succ

/-- **Theorem 2.29** (connected case): when `C` is connected and `n ≥ 1`,
every point of `con C` is a convex combination of no more than `n` points of
`C`. -/
theorem caratheodory_connected (hn : 0 < finrank ℝ E) {C : Set E} (hC : IsPreconnected C)
    {x : E} (hx : x ∈ convexHull ℝ C) :
    ∃ T : Finset E, ↑T ⊆ C ∧ T.card ≤ finrank ℝ E ∧ x ∈ convexHull ℝ ↑T := by
  classical
  obtain ⟨ι, _, z, w, hzC, hz, hw0, hw1, hzx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ finrank ℝ E + 1 :=
    hz.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  rcases hcard.lt_or_eq with hlt | heq
  · refine ⟨Finset.univ.image z, ?_, ?_, ?_⟩
    · intro p hp
      simp only [Finset.coe_image, Finset.coe_univ, image_univ] at hp
      exact hzC hp
    · exact Finset.card_image_le.trans (by simpa [Nat.lt_succ_iff] using hlt)
    · rw [← hzx]
      exact (convex_convexHull ℝ _).sum_mem (fun i _ ↦ (hw0 i).le) hw1 fun i _ ↦
        subset_convexHull ℝ _ (by simp)
  · let e : ι ≃ Fin (finrank ℝ E + 1) := Fintype.equivFinOfCardEq heq
    refine exists_card_le_finrank_of_isPreconnected hn hC (z := z ∘ e.symm)
      (hz.comp_embedding e.symm.toEmbedding) (fun i ↦ hzC ⟨_, rfl⟩) (w := w ∘ e.symm)
      (fun i ↦ hw0 _) ?_ ?_
    · rw [← hw1]
      exact Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl
    · rw [← hzx]
      exact Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl

/-- **Theorem 2.29** (connected case, with exactly `n` not necessarily
distinct points). -/
theorem caratheodory_connected_fin (hn : 0 < finrank ℝ E) {C : Set E} (hC : IsPreconnected C)
    {x : E} (hx : x ∈ convexHull ℝ C) :
    ∃ (lam : Fin (finrank ℝ E) → ℝ) (y : Fin (finrank ℝ E) → E),
      (∀ i, y i ∈ C) ∧ (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • y i = x := by
  obtain ⟨T, hTC, hcard, hxT⟩ := caratheodory_connected hn hC hx
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxT
  obtain ⟨c, hc⟩ : C.Nonempty := convexHull_nonempty_iff.mp ⟨x, hx⟩
  obtain ⟨lam, y, hcases, hsum, hcomb⟩ := exists_fin_padding T hcard w c
  refine ⟨lam, y, fun i ↦ ?_, fun i ↦ ?_, hsum.trans hw1, hcomb.trans hwx⟩
  · rcases hcases i with ⟨hy, -⟩ | ⟨-, hy⟩
    · exact hTC hy
    · rw [hy]
      exact hc
  · rcases hcases i with ⟨hy, hl⟩ | ⟨hl, -⟩
    · rw [hl]
      exact hw0 _ hy
    · rw [hl]

end Connected

/-! ### The boundary clause -/

section BoundaryCounterexample

/-- The set showing that the boundary clause of Theorem 2.29 concerns the
boundary of `con C`: the vertices `(0,0), (3,0), (0,3)` of a triangle together
with the half-open segment `{(t, 1) | 1 < t ≤ 2}` ending at the centroid
`(1, 1)`. -/
def boundaryCounterexampleSet : Set (ℝ × ℝ) :=
  {(0, 0), (3, 0), (0, 3)} ∪ {p | 1 < p.1 ∧ p.1 ≤ 2 ∧ p.2 = 1}

theorem not_mem_segment_boundaryCounterexampleSet {a b : ℝ × ℝ}
    (ha : a ∈ boundaryCounterexampleSet) (hb : b ∈ boundaryCounterexampleSet) {l₀ l₁ : ℝ}
    (h₀ : 0 ≤ l₀) (h₁ : 0 ≤ l₁) (hs : l₀ + l₁ = 1) (h : l₀ • a + l₁ • b = (1, 1)) : False := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, smul_eq_mul] at h
  obtain ⟨e₁, e₂⟩ := h
  simp only [boundaryCounterexampleSet, mem_union, mem_insert_iff, mem_singleton_iff,
    Prod.mk.injEq, mem_setOf_eq, or_assoc] at ha hb
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha₁, -, rfl⟩ <;>
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hb₁, -, rfl⟩
  all_goals first
    | linarith
    | nlinarith
    | (rcases eq_or_lt_of_le h₀ with hl | hl
       · subst hl
         nlinarith
       · nlinarith [mul_pos hl (sub_pos.mpr ha₁), mul_nonneg h₁ (sub_nonneg.mpr hb₁.le)])

/-- **Theorem 2.29**, boundary clause: with the boundary of `C` in place of the
boundary of `con C` the clause fails.  In `ℝ²` (`n = 2`), the point `(1, 1)`
lies in `bdry C ∩ con C` for `C = boundaryCounterexampleSet`, but it is not a
convex combination of two points of `C`. -/
theorem caratheodory_boundary_counterexample :
    finrank ℝ (ℝ × ℝ) = 2 ∧
    ((1, 1) : ℝ × ℝ) ∈ frontier boundaryCounterexampleSet ∧
    ((1, 1) : ℝ × ℝ) ∈ convexHull ℝ boundaryCounterexampleSet ∧
    ¬∃ (lam : Fin 2 → ℝ) (y : Fin 2 → ℝ × ℝ), (∀ i, y i ∈ boundaryCounterexampleSet) ∧
      (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • y i = (1, 1) := by
  have hnot : ((1, 1) : ℝ × ℝ) ∉ boundaryCounterexampleSet := by
    simp [boundaryCounterexampleSet]
  refine ⟨by simp, ⟨?_, fun h ↦ hnot (interior_subset h)⟩, ?_, ?_⟩
  · have hlim : Tendsto (fun t : ℝ ↦ ((1 + t, 1) : ℝ × ℝ)) (𝓝[>] 0) (𝓝 (1, 1)) := by
      have hc : Continuous fun t : ℝ ↦ ((1 + t, 1) : ℝ × ℝ) := by fun_prop
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto 0)
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    refine Or.inr (show 1 < 1 + t ∧ 1 + t ≤ 2 ∧ (1 : ℝ) = 1 from ?_)
    exact ⟨by linarith [ht.1], by linarith [ht.2], rfl⟩
  · have hv : ∀ p ∈ ({(0, 0), (3, 0), (0, 3)} : Set (ℝ × ℝ)),
        p ∈ convexHull ℝ boundaryCounterexampleSet := fun p hp ↦
      subset_convexHull ℝ _ (Or.inl hp)
    have hm := convex_convexHull ℝ boundaryCounterexampleSet (hv (3, 0) (by simp))
      (hv (0, 3) (by simp)) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have hx := convex_convexHull ℝ boundaryCounterexampleSet (hv (0, 0) (by simp)) hm
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num)
    convert hx using 1
    ext <;> simp <;> norm_num
  · rintro ⟨lam, y, hy, hl0, hl1, hly⟩
    rw [Fin.sum_univ_two] at hl1 hly
    exact not_mem_segment_boundaryCounterexampleSet (hy 0) (hy 1) (hl0 0) (hl0 1) hl1 hly

end BoundaryCounterexample

end RW
