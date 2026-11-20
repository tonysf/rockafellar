/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: piecewise linear-quadratic functions in conjugacy

**Theorem 11.14(b)**: a proper, lower semicontinuous, convex function is piecewise
linear-quadratic iff its conjugate is (`isPiecewiseLinearQuadratic_fenchelConjugate_iff`).

The proof follows the book.  The inequalities describing the polyhedral pieces of `f` split its
domain into finitely many cells (sign patterns).  Over the closure of the cell of `x` the
subgradient relation of `f` contains the polyhedral set `plqGraphPiece` of pairs `(y, v)`, and
these sets cover the graph of `∂f`.  Along a segment in such a set, `f*` is a quadratic polynomial
(Fenchel's equality), so Lemma 11.15 makes `f*` linear-quadratic on its projections.  These
projections exhaust `dom f*` by the density of subgradients (8.10) and the inversion rule (11.3).
-/

import RockafellarWets.Chapter11.LinearQuadraticSegments
import RockafellarWets.Chapter11.PiecewiseLinearConjugacy
import RockafellarWets.Chapter11.ConjugateSubgradientGraph
import RockafellarWets.Chapter10.PLQSubgradients
import RockafellarWets.Chapter8.SubgradientExistence

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Preliminaries -/

omit [FiniteDimensional ℝ E] in
/-- The derivative of a linear-quadratic formula. -/
theorem QuadraticPiece.fderiv_eval_apply (q : QuadraticPiece E) (x w : E) :
    fderiv ℝ q.eval x w = ⟪q.matrix x + q.linear, w⟫_ℝ := by
  have h1 := (hasFDerivAt_id x).inner ℝ q.matrix.hasFDerivAt
  have h2 := (hasFDerivAt_const q.linear x).inner ℝ (hasFDerivAt_id x)
  have h := ((h1.const_mul (1 / 2 : ℝ)).add h2).add_const q.constant
  rw [show fderiv ℝ q.eval x = _ from h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    smul_eq_mul, inner_add_left, ContinuousLinearMap.zero_apply, inner_zero_left, add_zero]
  simp only [ContinuousLinearMap.coe_id', id_eq]
  rw [← q.symmetric x w, real_inner_comm (q.matrix x) w]
  ring

/-- **Proposition 10.21**, subgradients of a convex piecewise linear-quadratic function: at a
point of the domain, `v` is a subgradient iff `v - ∇qᵢ(x)` is normal to every piece `Cᵢ`
containing `x`. -/
theorem plq_mem_subdifferential_iff {m : ℕ} {f : E → EReal} {C : Fin m → Set E}
    {q : Fin m → QuadraticPiece E} (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hC : ∀ i, IsPolyhedral (C i)) (hdom : effectiveDomain f = ⋃ i, C i)
    (hf : ∀ i x, x ∈ C i → f x = (q i).eval x) {x : E} (hx : x ∈ effectiveDomain f) {v : E} :
    v ∈ subdifferential f x ↔
      ∀ i, x ∈ C i → v - ((q i).matrix x + (q i).linear) ∈ normalCone (C i) x := by
  have h : IsPiecewiseLinearQuadratic f := ⟨m, C, q, hC, hdom, hf⟩
  have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (h.ne_bot x)).symm
  rw [subdifferential_eq_regularSubdifferential_of_convex hc hp hfin]
  have hdf := h.subderivative_piecewiseLinear hx
  have hvalue (i : Fin m) (hi : x ∈ C i) {w : E} (hw : w ∈ tangentCone (C i) x) :
      subderivative f x w = (⟪(q i).matrix x + (q i).linear, w⟫_ℝ : EReal) := by
    rw [plqRepresentation_subderivative_on_piece hC hdom hf hi hw,
      QuadraticPiece.fderiv_eval_apply]
  rw [mem_regularSubdifferential_iff_inner_le_subderivative hfin]
  constructor
  · intro hv i hi
    rw [normalCone_eq_regularNormalCone_of_convex (hC i).convex hi,
      mem_regularNormalCone_iff_inner_nonpos hi]
    intro w hw
    have hb := hv w
    rw [hvalue i hi hw, EReal.coe_le_coe_iff] at hb
    simpa [inner_sub_left] using sub_nonpos.mpr hb
  · intro hv w
    by_cases ht : subderivative f x w = ⊤
    · rw [ht]; exact le_top
    · have hwdom : w ∈ tangentCone (effectiveDomain f) x := hdf.2 ▸
        (show w ∈ effectiveDomain (subderivative f x) from lt_top_iff_ne_top.mpr ht)
      rw [hdom, tangentCone_finite_iUnion] at hwdom
      obtain ⟨i, hwi⟩ := mem_iUnion.mp hwdom
      have hxi : x ∈ C i := by
        obtain ⟨a, t, ha, hat, _⟩ := hwi
        exact (hC i).isClosed.mem_of_tendsto hat (.of_forall ha)
      have hvi := hv i hxi
      rw [normalCone_eq_regularNormalCone_of_convex (hC i).convex hxi,
        mem_regularNormalCone_iff_inner_nonpos hxi] at hvi
      rw [hvalue i hxi hwi, EReal.coe_le_coe_iff]
      exact sub_nonpos.mp (by simpa [inner_sub_left] using hvi w hwi)

omit [FiniteDimensional ℝ E] in
/-- A piecewise linear-quadratic representation may be indexed by any finite type. -/
theorem isPiecewiseLinearQuadratic_of_fintype {ι : Type*} [Fintype ι] {f : E → EReal}
    (C : ι → Set E) (q : ι → QuadraticPiece E) (hC : ∀ i, IsPolyhedral (C i))
    (hdom : effectiveDomain f = ⋃ i, C i) (hf : ∀ i x, x ∈ C i → f x = (q i).eval x) :
    IsPiecewiseLinearQuadratic f := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k ↦ C (e.symm k), fun k ↦ q (e.symm k), fun k ↦ hC _, ?_,
    fun k x hx ↦ hf _ x hx⟩
  rw [hdom]
  ext x
  simp only [mem_iUnion]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨e i, by simpa using hi⟩, fun ⟨k, hk⟩ ↦ ⟨_, hk⟩⟩

/-! ### Cells of a hyperplane arrangement -/

section Cells

variable {ι : Type*} (a : ι → E) (b : ι → ℝ)

/-- The closure of the cell of `x` in the arrangement of the hyperplanes `⟪a j, ·⟫ = b j`: each
inequality that is strict, an equality, or reversed at `x` holds weakly, as an equality, or
reversed weakly. -/
def cellClosure (x : E) : Set E :=
  {y | ∀ j, (⟪a j, x⟫_ℝ < b j → ⟪a j, y⟫_ℝ ≤ b j) ∧ (⟪a j, x⟫_ℝ = b j → ⟪a j, y⟫_ℝ = b j) ∧
    (b j < ⟪a j, x⟫_ℝ → b j ≤ ⟪a j, y⟫_ℝ)}

/-- The sign pattern of `x` relative to the hyperplanes `⟪a j, ·⟫ = b j`. -/
def signPattern (x : E) : ι → SignType := fun j ↦ SignType.sign (⟪a j, x⟫_ℝ - b j)

variable {a b}

omit [FiniteDimensional ℝ E] in
theorem self_mem_cellClosure (x : E) : x ∈ cellClosure a b x :=
  fun _ ↦ ⟨le_of_lt, id, le_of_lt⟩

omit [FiniteDimensional ℝ E] in
theorem cmp_iff_of_signPattern_eq {x x' : E} (h : signPattern a b x = signPattern a b x')
    (j : ι) :
    (⟪a j, x⟫_ℝ < b j ↔ ⟪a j, x'⟫_ℝ < b j) ∧ (⟪a j, x⟫_ℝ = b j ↔ ⟪a j, x'⟫_ℝ = b j) ∧
      (b j < ⟪a j, x⟫_ℝ ↔ b j < ⟪a j, x'⟫_ℝ) := by
  have hj := congrFun h j
  simp only [signPattern] at hj
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_neg, ← sign_eq_neg_one_iff, hj, sign_eq_neg_one_iff, sub_neg]
  · rw [← sub_eq_zero, ← sign_eq_zero_iff, hj, sign_eq_zero_iff, sub_eq_zero]
  · rw [← sub_pos, ← sign_eq_one_iff, hj, sign_eq_one_iff, sub_pos]

omit [FiniteDimensional ℝ E] in
theorem cellClosure_eq_of_signPattern_eq {x x' : E}
    (h : signPattern a b x = signPattern a b x') : cellClosure a b x = cellClosure a b x' := by
  ext y
  simp only [cellClosure, mem_setOf_eq]
  refine forall_congr' fun j ↦ ?_
  obtain ⟨h1, h2, h3⟩ := cmp_iff_of_signPattern_eq h j
  rw [h1, h2, h3]

omit [FiniteDimensional ℝ E] in
/-- Moving from a point of the closed cell of `x` towards `x` enters the cell of `x`. -/
theorem signPattern_combo {x y : E} (hy : y ∈ cellClosure a b x) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) : signPattern a b ((1 - t) • y + t • x) = signPattern a b x := by
  funext j
  simp only [signPattern]
  have he : ⟪a j, (1 - t) • y + t • x⟫_ℝ - b j
      = (1 - t) * (⟪a j, y⟫_ℝ - b j) + t * (⟪a j, x⟫_ℝ - b j) := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    ring
  rw [he]
  obtain ⟨h1, h2, h3⟩ := hy j
  rcases lt_trichotomy (⟪a j, x⟫_ℝ) (b j) with hx | hx | hx
  · have hy' := h1 hx
    rw [sign_neg (by nlinarith), sign_neg (by linarith)]
  · have hy' := h2 hx
    rw [hy', hx]
    simp
  · have hy' := h3 hx
    rw [sign_pos (by nlinarith), sign_pos (by linarith)]

theorem isPolyhedral_cellClosure [Fintype ι] (x : E) : IsPolyhedral (cellClosure a b x) := by
  have hj : ∀ j, IsPolyhedral {y : E | (⟪a j, x⟫_ℝ < b j → ⟪a j, y⟫_ℝ ≤ b j) ∧
      (⟪a j, x⟫_ℝ = b j → ⟪a j, y⟫_ℝ = b j) ∧ (b j < ⟪a j, x⟫_ℝ → b j ≤ ⟪a j, y⟫_ℝ)} := by
    intro j
    have hge : {y : E | b j ≤ ⟪a j, y⟫_ℝ} = {y : E | ⟪-a j, y⟫_ℝ ≤ -b j} := by
      ext y
      simp [inner_neg_left]
    rcases lt_trichotomy (⟪a j, x⟫_ℝ) (b j) with hx | hx | hx
    · convert isPolyhedral_inner_le (a j) (b j) using 1
      ext y
      simp [hx, hx.ne, not_lt.2 hx.le]
    · convert (isPolyhedral_inner_le (a j) (b j)).inter (isPolyhedral_inner_le (-a j) (-b j))
        using 1
      ext y
      simp only [hx, lt_self_iff_false, false_implies, true_implies, true_and, and_true,
        mem_setOf_eq, mem_inter_iff, inner_neg_left, neg_le_neg_iff]
      exact ⟨fun h ↦ ⟨h.le, h.ge⟩, fun h ↦ le_antisymm h.1 h.2⟩
    · rw [show {y : E | (⟪a j, x⟫_ℝ < b j → ⟪a j, y⟫_ℝ ≤ b j) ∧
          (⟪a j, x⟫_ℝ = b j → ⟪a j, y⟫_ℝ = b j) ∧ (b j < ⟪a j, x⟫_ℝ → b j ≤ ⟪a j, y⟫_ℝ)}
          = {y : E | b j ≤ ⟪a j, y⟫_ℝ} by
        ext y
        simp [hx, hx.ne', not_lt.2 hx.le], hge]
      exact isPolyhedral_inner_le (-a j) (-b j)
  have he : cellClosure a b x = ⋂ j ∈ (Finset.univ : Finset ι), {y : E |
      (⟪a j, x⟫_ℝ < b j → ⟪a j, y⟫_ℝ ≤ b j) ∧ (⟪a j, x⟫_ℝ = b j → ⟪a j, y⟫_ℝ = b j) ∧
      (b j < ⟪a j, x⟫_ℝ → b j ≤ ⟪a j, y⟫_ℝ)} := by
    ext y
    simp [cellClosure]
  rw [he]
  exact IsPolyhedral.iInter_finset _ _ fun j _ ↦ hj j

end Cells


/-! ### Cells of the pieces and the polyhedral pieces of the subgradient graph -/

section PieceCells

variable {m : ℕ} {C : Fin m → Set E} {q : Fin m → QuadraticPiece E} {n : Fin m → ℕ}
  {a : (Σ k : Fin m, Fin (n k)) → E} {b : (Σ k : Fin m, Fin (n k)) → ℝ}

omit [FiniteDimensional ℝ E] in
theorem mem_piece_iff_of_signPattern_eq
    (hrep : ∀ k, C k = {y | ∀ i, ⟪a ⟨k, i⟩, y⟫_ℝ ≤ b ⟨k, i⟩}) {x x' : E}
    (h : signPattern a b x = signPattern a b x') (k : Fin m) : x ∈ C k ↔ x' ∈ C k := by
  rw [hrep k]
  simp only [mem_setOf_eq]
  refine forall_congr' fun i ↦ ?_
  obtain ⟨h1, h2, -⟩ := cmp_iff_of_signPattern_eq h ⟨k, i⟩
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, h1, h2]

omit [FiniteDimensional ℝ E] in
theorem mem_piece_of_mem_cellClosure
    (hrep : ∀ k, C k = {y | ∀ i, ⟪a ⟨k, i⟩, y⟫_ℝ ≤ b ⟨k, i⟩}) {x y : E}
    (hy : y ∈ cellClosure a b x) {k : Fin m} (hx : x ∈ C k) : y ∈ C k := by
  rw [hrep k] at hx ⊢
  intro i
  rcases (hx i).lt_or_eq with h | h
  · exact (hy ⟨k, i⟩).1 h
  · exact ((hy ⟨k, i⟩).2.1 h).le

theorem normalCone_piece_eq_of_signPattern_eq
    (hrep : ∀ k, C k = {y | ∀ i, ⟪a ⟨k, i⟩, y⟫_ℝ ≤ b ⟨k, i⟩}) {x x' : E}
    (h : signPattern a b x = signPattern a b x') {k : Fin m} (hx : x ∈ C k) :
    normalCone (C k) x = normalCone (C k) x' := by
  have hx' := (mem_piece_iff_of_signPattern_eq hrep h k).1 hx
  have hx1 : ∀ i, ⟪a ⟨k, i⟩, x⟫_ℝ ≤ b ⟨k, i⟩ := by rw [hrep k] at hx; exact hx
  have hx1' : ∀ i, ⟪a ⟨k, i⟩, x'⟫_ℝ ≤ b ⟨k, i⟩ := by rw [hrep k] at hx'; exact hx'
  rw [hrep k, normalCone_setOf_inner_le hx1, normalCone_setOf_inner_le hx1']
  have hiff : ∀ i, (⟪a ⟨k, i⟩, x⟫_ℝ = b ⟨k, i⟩ ↔ ⟪a ⟨k, i⟩, x'⟫_ℝ = b ⟨k, i⟩) :=
    fun i ↦ (cmp_iff_of_signPattern_eq h ⟨k, i⟩).2.1
  simp only [ne_eq, hiff]

/-- Pairs `(y, v)` with `y` in a set `D` and `v - ∇qₖ(y)` normal at `x` to every piece `Cₖ`
containing `x`.  For `D` the closed cell of `x`, these are subgradient pairs of `f`. -/
def plqGraphPiece (C : Fin m → Set E) (q : Fin m → QuadraticPiece E) (D : Set E) (x : E) :
    Set (E × E) :=
  {p | p.1 ∈ D ∧ ∀ k, x ∈ C k → p.2 - ((q k).matrix p.1 + (q k).linear) ∈ normalCone (C k) x}

theorem isPolyhedral_plqGraphPiece (hC : ∀ k, IsPolyhedral (C k)) {D : Set E}
    (hD : IsPolyhedral D) (x : E) : IsPolyhedral (plqGraphPiece C q D x) := by
  classical
  let S : Fin m → Set (E × E) := fun k ↦ if x ∈ C k then
    (ContinuousLinearMap.snd ℝ E E - (q k).matrix ∘L ContinuousLinearMap.fst ℝ E E) ⁻¹'
      ((fun z ↦ (ContinuousLinearMap.id ℝ E) z + -(q k).linear) ⁻¹' normalCone (C k) x)
    else univ
  have hS : ∀ k, IsPolyhedral (S k) := by
    intro k
    by_cases hk : x ∈ C k
    · simp only [S, if_pos hk]
      exact (((hC k).isPolyhedral_normalCone hk).affine_preimage (ContinuousLinearMap.id ℝ E)
        (-(q k).linear)).continuousLinear_preimage _
    · simp only [S, if_neg hk]
      exact IsPolyhedral.univ
  have he : plqGraphPiece C q D x =
      (D ×ˢ (univ : Set E)) ∩ ⋂ k ∈ (Finset.univ : Finset (Fin m)), S k := by
    ext ⟨y, v⟩
    simp only [plqGraphPiece, mem_setOf_eq, mem_inter_iff, mem_prod, mem_univ, and_true,
      Finset.mem_univ, iInter_true, mem_iInter]
    refine and_congr Iff.rfl (forall_congr' fun k ↦ ?_)
    by_cases hk : x ∈ C k
    · simp only [S, if_pos hk, hk, true_implies, mem_preimage, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_id', id_eq]
      rw [show v - ((q k).matrix y + (q k).linear) = v - (q k).matrix y + -(q k).linear by abel]
    · simp [S, hk]
  rw [he]
  exact (hD.prod IsPolyhedral.univ).inter (IsPolyhedral.iInter_finset _ _ fun k _ ↦ hS k)

theorem plqGraphPiece_eq_of_signPattern_eq
    (hrep : ∀ k, C k = {y | ∀ i, ⟪a ⟨k, i⟩, y⟫_ℝ ≤ b ⟨k, i⟩}) {x x' : E}
    (h : signPattern a b x = signPattern a b x') :
    plqGraphPiece C q (cellClosure a b x) x = plqGraphPiece C q (cellClosure a b x') x' := by
  ext p
  simp only [plqGraphPiece, mem_setOf_eq, cellClosure_eq_of_signPattern_eq h]
  refine and_congr Iff.rfl (forall_congr' fun k ↦ ?_)
  by_cases hk : x ∈ C k
  · have hk' := (mem_piece_iff_of_signPattern_eq hrep h k).1 hk
    simp only [hk, hk', true_implies, normalCone_piece_eq_of_signPattern_eq hrep h hk]
  · have hk' : x' ∉ C k := fun hk' ↦ hk ((mem_piece_iff_of_signPattern_eq hrep h k).2 hk')
    simp only [hk, hk', false_implies]

section Graph

variable {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
  (hc : Convex ℝ (epigraph f)) (hC : ∀ k, IsPolyhedral (C k))
  (hdom : effectiveDomain f = ⋃ k, C k) (hfq : ∀ k x, x ∈ C k → f x = (q k).eval x)
  (hrep : ∀ k, C k = {y | ∀ i, ⟪a ⟨k, i⟩, y⟫_ℝ ≤ b ⟨k, i⟩})
include hp hc hC hdom hfq

theorem mem_plqGraphPiece_of_mem_subdifferential {x v : E} (hx : x ∈ effectiveDomain f)
    (hv : v ∈ subdifferential f x) : (x, v) ∈ plqGraphPiece C q (cellClosure a b x) x :=
  ⟨self_mem_cellClosure x, (plq_mem_subdifferential_iff hp hc hC hdom hfq hx).1 hv⟩

include hl hrep in
/-- Over the closed cell of a point `x` of the domain, the graph piece consists of subgradient
pairs: approach along segments ending in the cell of `x`, and close the graph (11.3). -/
theorem plqGraphPiece_subset_graph {x : E} (hx : x ∈ effectiveDomain f) :
    plqGraphPiece C q (cellClosure a b x) x ⊆ svGraph (subdifferential f) := by
  rintro ⟨y, v⟩ ⟨hy, hv⟩
  have hplq : IsPiecewiseLinearQuadratic f := ⟨m, C, q, hC, hdom, hfq⟩
  obtain ⟨v0, hv0⟩ := (hplq.convex_subgradient_properties hc hx).1
  have hv0' := (plq_mem_subdifferential_iff hp hc hC hdom hfq hx).1 hv0
  obtain ⟨k₀, hk₀⟩ := mem_iUnion.1 (hdom ▸ hx)
  have hmem : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ((1 - t) • y + t • x, (1 - t) • v + t • v0) ∈ svGraph (subdifferential f) := by
    intro t ht0 ht1
    have hpat : signPattern a b ((1 - t) • y + t • x) = signPattern a b x :=
      signPattern_combo hy ht0 ht1
    have hxt : (1 - t) • y + t • x ∈ effectiveDomain f :=
      hdom ▸ mem_iUnion.2 ⟨k₀, (mem_piece_iff_of_signPattern_eq hrep hpat k₀).2 hk₀⟩
    show (1 - t) • v + t • v0 ∈ subdifferential f ((1 - t) • y + t • x)
    rw [plq_mem_subdifferential_iff hp hc hC hdom hfq hxt]
    intro k hk
    have hxk := (mem_piece_iff_of_signPattern_eq hrep hpat k).1 hk
    rw [normalCone_piece_eq_of_signPattern_eq hrep hpat hk]
    have hcomb : (1 - t) • v + t • v0 - ((q k).matrix ((1 - t) • y + t • x) + (q k).linear)
        = (1 - t) • (v - ((q k).matrix y + (q k).linear))
          + t • (v0 - ((q k).matrix x + (q k).linear)) := by
      simp only [map_add, map_smul]
      module
    rw [hcomb]
    exact ((hC k).isPolyhedral_normalCone hxk).convex (hv k hxk) (hv0' k hxk) (by linarith)
      ht0.le (by ring)
  have hclosed := isClosed_graph_subdifferential_of_convex hp hl hc
  have hlim : Tendsto (fun t : ℝ ↦ ((1 - t) • y + t • x, (1 - t) • v + t • v0)) (𝓝[>] 0)
      (𝓝 (y, v)) := by
    have hcont : Continuous (fun t : ℝ ↦ ((1 - t) • y + t • x, (1 - t) • v + t • v0)) := by
      fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact hclosed.mem_of_tendsto hlim
    (by filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht using hmem t ht.1 ht.2)


include hl hrep in
/-- Along a segment of a graph piece, the conjugate is a quadratic polynomial (Fenchel's
equality), so by Lemma 11.15 it is linear-quadratic on the projection of the piece. -/
theorem isLinearQuadraticOnEReal_conjugate_plqGraphPiece {x : E} (hx : x ∈ effectiveDomain f) :
    IsLinearQuadraticOnEReal (fenchelConjugate f)
      (Prod.snd '' plqGraphPiece C q (cellClosure a b x) x) := by
  have hpoly := isPolyhedral_plqGraphPiece (q := q) hC
    (isPolyhedral_cellClosure (a := a) (b := b) x) x
  have hconvG := hpoly.convex
  have hconv : Convex ℝ (Prod.snd '' plqGraphPiece C q (cellClosure a b x) x) := by
    simpa using hconvG.linear_image (LinearMap.snd ℝ E E)
  obtain ⟨k₀, hk₀⟩ := mem_iUnion.1 (hdom ▸ hx)
  rw [isLinearQuadraticOnEReal_iff_segments hconv]
  rintro _ ⟨p0, hp0, rfl⟩ _ ⟨p1, hp1, rfl⟩
  set Q := q k₀ with hQ
  have hseg' : ∀ θ ∈ Icc (0 : ℝ) 1, fenchelConjugate f (p0.2 + θ • (p1.2 - p0.2)) =
      (((⟪p0.2, p0.1⟫_ℝ - Q.eval p0.1)
        + (⟪p0.2, p1.1 - p0.1⟫_ℝ + ⟪p1.2 - p0.2, p0.1⟫_ℝ
            - (⟪p1.1 - p0.1, Q.matrix p0.1⟫_ℝ + ⟪Q.linear, p1.1 - p0.1⟫_ℝ)) * θ
        + (⟪p1.2 - p0.2, p1.1 - p0.1⟫_ℝ - (1 / 2) * ⟪p1.1 - p0.1, Q.matrix (p1.1 - p0.1)⟫_ℝ)
          * θ ^ 2 : ℝ) : EReal) := by
    intro θ hθ
    have hpθ : p0 + θ • (p1 - p0) ∈ plqGraphPiece C q (cellClosure a b x) x :=
      hconvG.add_smul_sub_mem hp0 hp1 hθ
    have hsub := plqGraphPiece_subset_graph hp hl hc hC hdom hfq hrep hx hpθ
    have hyk : (p0 + θ • (p1 - p0)).1 ∈ C k₀ := mem_piece_of_mem_cellClosure hrep hpθ.1 hk₀
    have he := (mem_subdifferential_iff_fenchelConjugate_eq hp hc (hfq k₀ _ hyk)).1 hsub
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub] at he
    rw [he, ← hQ, QuadraticPiece.eval_line]
    congr 1
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    ring
  obtain ⟨c₀, c₁, c₂, hseg⟩ : ∃ c₀ c₁ c₂ : ℝ, ∀ θ ∈ Icc (0 : ℝ) 1,
      fenchelConjugate f (p0.2 + θ • (p1.2 - p0.2)) = ((c₀ + c₁ * θ + c₂ * θ ^ 2 : ℝ) : EReal) :=
    ⟨_, _, _, hseg'⟩
  obtain ⟨q', hq'⟩ := isLinearQuadraticOn_segment_of_poly
    (φ := fun v ↦ (fenchelConjugate f v).toReal) (x := p0.2) (y := p1.2) (c₀ := c₀) (c₁ := c₁)
    (c₂ := c₂) (fun θ hθ ↦ by simp only [hseg θ hθ, EReal.toReal_coe])
  refine ⟨q', fun v hv ↦ ?_⟩
  have h1 : (fenchelConjugate f v).toReal = q'.eval v := hq' v hv
  have hv' := hv
  rw [segment_eq_image'] at hv'
  obtain ⟨θ, hθ, hvθ⟩ := hv'
  have hfv : fenchelConjugate f v = ((c₀ + c₁ * θ + c₂ * θ ^ 2 : ℝ) : EReal) := by
    rw [← hvθ]
    exact hseg θ hθ
  rw [hfv] at h1 ⊢
  rw [EReal.toReal_coe] at h1
  rw [h1]

end Graph

/-- The projections of the graph pieces over the points of `dom f` with a given sign pattern. -/
def plqPatternPiece (f : E → EReal) (C : Fin m → Set E) (q : Fin m → QuadraticPiece E)
    (a : (Σ k : Fin m, Fin (n k)) → E) (b : (Σ k : Fin m, Fin (n k)) → ℝ)
    (s : (Σ k : Fin m, Fin (n k)) → SignType) : Set E :=
  ⋃ x ∈ {x | x ∈ effectiveDomain f ∧ signPattern a b x = s},
    Prod.snd '' plqGraphPiece C q (cellClosure a b x) x

theorem plqPatternPiece_eq {f : E → EReal}
    (hrep : ∀ k, C k = {y | ∀ i, ⟪a ⟨k, i⟩, y⟫_ℝ ≤ b ⟨k, i⟩})
    {s : (Σ k : Fin m, Fin (n k)) → SignType} {x₀ : E} (hx₀ : x₀ ∈ effectiveDomain f)
    (hs : signPattern a b x₀ = s) :
    plqPatternPiece f C q a b s = Prod.snd '' plqGraphPiece C q (cellClosure a b x₀) x₀ := by
  apply Subset.antisymm
  · intro v hv
    simp only [plqPatternPiece, mem_iUnion, mem_setOf_eq] at hv
    obtain ⟨x, ⟨-, hxs⟩, hv⟩ := hv
    rwa [plqGraphPiece_eq_of_signPattern_eq hrep (hxs.trans hs.symm)] at hv
  · intro v hv
    simp only [plqPatternPiece, mem_iUnion, mem_setOf_eq]
    exact ⟨x₀, ⟨hx₀, hs⟩, hv⟩

theorem isPolyhedral_plqPatternPiece {f : E → EReal} (hC : ∀ k, IsPolyhedral (C k))
    (hrep : ∀ k, C k = {y | ∀ i, ⟪a ⟨k, i⟩, y⟫_ℝ ≤ b ⟨k, i⟩})
    (s : (Σ k : Fin m, Fin (n k)) → SignType) : IsPolyhedral (plqPatternPiece f C q a b s) := by
  by_cases h : ∃ x₀, x₀ ∈ effectiveDomain f ∧ signPattern a b x₀ = s
  · obtain ⟨x₀, hx₀, hs⟩ := h
    rw [plqPatternPiece_eq hrep hx₀ hs]
    exact (isPolyhedral_plqGraphPiece hC (isPolyhedral_cellClosure x₀) x₀).linear_image
      (LinearMap.snd ℝ E E)
  · have he : plqPatternPiece f C q a b s = ∅ := by
      ext v
      simp only [plqPatternPiece, mem_iUnion, mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨x, ⟨hx, hs⟩, -⟩
      exact h ⟨x, hx, hs⟩
    rw [he]
    exact IsPolyhedral.empty

section Domain

variable {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
  (hc : Convex ℝ (epigraph f)) (hC : ∀ k, IsPolyhedral (C k))
  (hdom : effectiveDomain f = ⋃ k, C k) (hfq : ∀ k x, x ∈ C k → f x = (q k).eval x)
  (hrep : ∀ k, C k = {y | ∀ i, ⟪a ⟨k, i⟩, y⟫_ℝ ≤ b ⟨k, i⟩})
include hp hl hc hC hdom hfq hrep

/-- The domain of the conjugate is the finite union of the pattern pieces: they lie in the range
of `∂f`, which is closed and dense in `dom f*` (8.10, 11.3). -/
theorem effectiveDomain_fenchelConjugate_eq_iUnion_plqPatternPiece :
    effectiveDomain (fenchelConjugate f) = ⋃ s, plqPatternPiece f C q a b s := by
  have hU : (⋃ s, plqPatternPiece f C q a b s) =
      ⋃ x ∈ effectiveDomain f, Prod.snd '' plqGraphPiece C q (cellClosure a b x) x := by
    ext v
    simp only [plqPatternPiece, mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨s, x, ⟨hx, -⟩, hv⟩
      exact ⟨x, hx, hv⟩
    · rintro ⟨x, hx, hv⟩
      exact ⟨signPattern a b x, x, ⟨hx, rfl⟩, hv⟩
  have hclosed : IsClosed (⋃ s, plqPatternPiece f C q a b s) :=
    isClosed_iUnion_of_finite fun s ↦ (isPolyhedral_plqPatternPiece hC hrep s).isClosed
  apply Subset.antisymm
  · intro v hv
    have hpc := isProper_fenchelConjugate hp hl hc
    have hfin : fenchelConjugate f v = ((fenchelConjugate f v).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hv) (hpc.2 v).ne').symm
    have hll : IsLocallyLscAt (fenchelConjugate f) v :=
      isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin (RW.IsClosed.isLocallyClosedAt
        (isClosed_epigraph_of_lsc_ereal _ (lowerSemicontinuous_fenchelConjugate f)) _)
    obtain ⟨w, hw, hwsub⟩ := exists_attentive_seq_regularSubdifferential_nonempty hll hfin
    refine hclosed.mem_of_tendsto (tendsto_attentiveNhds_iff.mp hw).1
      (Eventually.of_forall fun k ↦ ?_)
    obtain ⟨y, hy⟩ := (hwsub k).2
    have hv' : w k ∈ subdifferential f y :=
      (mem_subdifferential_fenchelConjugate_iff hp hl hc y (w k)).1 hy
    have hyd : y ∈ effectiveDomain f := by
      obtain ⟨c, hc'⟩ := hv'.1
      change f y < ⊤
      rw [hc']
      exact EReal.coe_lt_top _
    rw [hU]
    exact mem_iUnion₂.2 ⟨y, hyd, ⟨(y, w k),
      mem_plqGraphPiece_of_mem_subdifferential hp hc hC hdom hfq hyd hv', rfl⟩⟩
  · rw [hU]
    intro v hv
    obtain ⟨x, hx, ⟨y, v'⟩, hpG, rfl⟩ := mem_iUnion₂.1 hv
    have hsub := plqGraphPiece_subset_graph hp hl hc hC hdom hfq hrep hx hpG
    obtain ⟨c, hc'⟩ := hsub.1
    change fenchelConjugate f v' < ⊤
    rw [(mem_subdifferential_iff_fenchelConjugate_eq hp hc hc').1 hsub]
    exact EReal.coe_lt_top _

/-- **Theorem 11.14(b)**, main implication, for a representation with explicit inequalities. -/
theorem isPiecewiseLinearQuadratic_fenchelConjugate_of_rep :
    IsPiecewiseLinearQuadratic (fenchelConjugate f) := by
  classical
  have hq : ∀ s, ∃ q' : QuadraticPiece E, ∀ v ∈ plqPatternPiece f C q a b s,
      fenchelConjugate f v = q'.eval v := by
    intro s
    by_cases h : ∃ x₀, x₀ ∈ effectiveDomain f ∧ signPattern a b x₀ = s
    · obtain ⟨x₀, hx₀, hs⟩ := h
      obtain ⟨q', hq'⟩ :=
        isLinearQuadraticOnEReal_conjugate_plqGraphPiece hp hl hc hC hdom hfq hrep hx₀
      refine ⟨q', fun v hv ↦ hq' v ?_⟩
      rwa [plqPatternPiece_eq hrep hx₀ hs] at hv
    · refine ⟨⟨0, fun _ _ ↦ by simp, 0, 0⟩, fun v hv ↦ ?_⟩
      exfalso
      simp only [plqPatternPiece, mem_iUnion, mem_setOf_eq] at hv
      obtain ⟨x, ⟨hx, hs⟩, -⟩ := hv
      exact h ⟨x, hx, hs⟩
  choose q' hq' using hq
  exact isPiecewiseLinearQuadratic_of_fintype (plqPatternPiece f C q a b) q'
    (isPolyhedral_plqPatternPiece hC hrep)
    (effectiveDomain_fenchelConjugate_eq_iUnion_plqPatternPiece hp hl hc hC hdom hfq hrep) hq'

end Domain

end PieceCells

/-! ### Theorem 11.14(b) -/

/-- **Theorem 11.14(b)**, main implication: the conjugate of a proper, lower semicontinuous,
convex, piecewise linear-quadratic function is piecewise linear-quadratic. -/
theorem IsPiecewiseLinearQuadratic.isPiecewiseLinearQuadratic_fenchelConjugate {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) : IsPiecewiseLinearQuadratic (fenchelConjugate f) := by
  obtain ⟨m, C, q, hC, hdom, hfq⟩ := hf
  choose n a b hrep using fun k ↦ (hC k).isHPolyhedral.exists_inner_representation
  exact isPiecewiseLinearQuadratic_fenchelConjugate_of_rep (a := fun j ↦ a j.1 j.2)
    (b := fun j ↦ b j.1 j.2) hp hl hc hC hdom hfq hrep

/-- **Theorem 11.14(b)**: a proper, lower semicontinuous, convex function is piecewise
linear-quadratic iff its conjugate is. -/
theorem isPiecewiseLinearQuadratic_fenchelConjugate_iff {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    IsPiecewiseLinearQuadratic (fenchelConjugate f) ↔ IsPiecewiseLinearQuadratic f := by
  constructor
  · intro h
    have h2 := h.isPiecewiseLinearQuadratic_fenchelConjugate
      (isProper_fenchelConjugate hp hl hc) (lowerSemicontinuous_fenchelConjugate f)
      (convex_epigraph_fenchelConjugate f)
    rwa [fenchelConjugate_fenchelConjugate_eq hp hl hc] at h2
  · exact fun h ↦ h.isPiecewiseLinearQuadratic_fenchelConjugate hp hl hc

end

end RW
