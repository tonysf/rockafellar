/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Monotone and maximal monotone mappings

This file formalizes Definition 12.1 (monotonicity and strict monotonicity)
and Definition 12.5 (maximal monotonicity, globally and locally around a
point of the graph).

A set-valued mapping `T : ℝⁿ ⇉ ℝⁿ` is represented, as in Chapter 5, by a
function `T : E → Set E`, where `E` is any real inner product space; the book's
setting is `E = ℝⁿ`.  Graphs, inverses, domains and ranges are the Chapter 5
notions `svGraph`, `svInv`, `svDom` and `svRange`.

Definition 12.5 describes maximality in two ways: no monotone mapping has a
strictly larger graph, or, every pair outside the graph violates the
monotonicity inequality against some pair of the graph.  The definition
`SvMaximalMonotone` uses the second form, and
`svMaximalMonotone_iff_no_enlargement` proves that the two agree.  The local
notion `SvMaximalMonotoneLocallyAt` is the same condition with both pairs
restricted to a neighborhood of the base point; for a maximal monotone mapping
the whole space is such a neighborhood.
-/

import RockafellarWets.Chapter5.Semicontinuity
import Mathlib.Analysis.InnerProductSpace.Basic

open Set Topology Filter
open scoped InnerProductSpace

namespace RW

section Monotonicity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Definition 12.1 (monotonicity).** A mapping `T : E ⇉ E` is monotone if
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ 0` whenever `v₀ ∈ T x₀` and `v₁ ∈ T x₁`. -/
def SvMonotone (T : E → Set E) : Prop :=
  ∀ ⦃x₀ v₀ : E⦄, v₀ ∈ T x₀ → ∀ ⦃x₁ v₁ : E⦄, v₁ ∈ T x₁ → 0 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- **Definition 12.1 (strict monotonicity).** The monotonicity inequality is
strict whenever `x₀ ≠ x₁`. -/
def SvStrictlyMonotone (T : E → Set E) : Prop :=
  ∀ ⦃x₀ v₀ : E⦄, v₀ ∈ T x₀ → ∀ ⦃x₁ v₁ : E⦄, v₁ ∈ T x₁ → x₀ ≠ x₁ →
    0 < ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- Strict monotonicity includes monotonicity: for `x₀ = x₁` the inner product
vanishes. -/
theorem SvStrictlyMonotone.svMonotone {T : E → Set E} (hT : SvStrictlyMonotone T) :
    SvMonotone T := by
  intro x₀ v₀ h₀ x₁ v₁ h₁
  by_cases hx : x₀ = x₁
  · subst hx
    simp
  · exact (hT h₀ h₁ hx).le

/-- Monotonicity read on the graph. -/
theorem svMonotone_iff_graph {T : E → Set E} :
    SvMonotone T ↔ ∀ p ∈ svGraph T, ∀ q ∈ svGraph T, 0 ≤ ⟪q.2 - p.2, q.1 - p.1⟫_ℝ := by
  constructor
  · intro hT p hp q hq
    exact hT hp hq
  · intro hT x₀ v₀ h₀ x₁ v₁ h₁
    exact hT (x₀, v₀) h₀ (x₁, v₁) h₁

/-- The monotonicity inequality is symmetric in the two pairs. -/
theorem inner_sub_sub_comm (x₀ v₀ x₁ v₁ : E) :
    ⟪v₀ - v₁, x₀ - x₁⟫_ℝ = ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  rw [← neg_sub v₁ v₀, ← neg_sub x₁ x₀, inner_neg_left, inner_neg_right, neg_neg]

/-- **Definition 12.1, single-valued form.** A single-valued mapping is
monotone exactly when `⟪F x₁ - F x₀, x₁ - x₀⟫ ≥ 0` for all `x₀` and `x₁`. -/
theorem svMonotone_singleton_iff {F : E → E} :
    SvMonotone (fun x ↦ ({F x} : Set E)) ↔ ∀ x₀ x₁, 0 ≤ ⟪F x₁ - F x₀, x₁ - x₀⟫_ℝ := by
  constructor
  · intro hF x₀ x₁
    exact hF (mem_singleton (F x₀)) (mem_singleton (F x₁))
  · intro hF x₀ v₀ h₀ x₁ v₁ h₁
    rw [mem_singleton_iff] at h₀ h₁
    subst h₀ h₁
    exact hF x₀ x₁

/-- **Definition 12.1, single-valued form of strict monotonicity.** -/
theorem svStrictlyMonotone_singleton_iff {F : E → E} :
    SvStrictlyMonotone (fun x ↦ ({F x} : Set E)) ↔
      ∀ x₀ x₁, x₀ ≠ x₁ → 0 < ⟪F x₁ - F x₀, x₁ - x₀⟫_ℝ := by
  constructor
  · intro hF x₀ x₁ hx
    exact hF (mem_singleton (F x₀)) (mem_singleton (F x₁)) hx
  · intro hF x₀ v₀ h₀ x₁ v₁ h₁ hx
    rw [mem_singleton_iff] at h₀ h₁
    subst h₀ h₁
    exact hF x₀ x₁ hx

/-- A mapping whose graph lies in the graph of a monotone mapping is
monotone. -/
theorem SvMonotone.mono {S T : E → Set E} (hT : SvMonotone T) (hST : ∀ x, S x ⊆ T x) :
    SvMonotone S :=
  fun _ _ h₀ _ _ h₁ ↦ hT (hST _ h₀) (hST _ h₁)

/-- A mapping whose graph lies in the graph of a strictly monotone mapping is
strictly monotone. -/
theorem SvStrictlyMonotone.mono {S T : E → Set E} (hT : SvStrictlyMonotone T)
    (hST : ∀ x, S x ⊆ T x) : SvStrictlyMonotone S :=
  fun _ _ h₀ _ _ h₁ hx ↦ hT (hST _ h₀) (hST _ h₁) hx

/-- The mapping with empty graph is monotone. -/
theorem svMonotone_empty : SvMonotone (fun _ : E ↦ (∅ : Set E)) :=
  fun _ _ h ↦ (notMem_empty _ h).elim

/-- **Definition 12.5 (maximal monotonicity).** A monotone mapping is maximal
monotone if every pair outside its graph violates the monotonicity inequality
against some pair in the graph. -/
def SvMaximalMonotone (T : E → Set E) : Prop :=
  SvMonotone T ∧ ∀ x v, v ∉ T x → ∃ x' v', v' ∈ T x' ∧ ⟪v - v', x - x'⟫_ℝ < 0

/-- **Definition 12.5 (local maximal monotonicity).** The monotone mapping `T`
is maximal monotone locally around the graph point `(x̄, v̄)` if, for some
neighborhood `V` of `(x̄, v̄)`, every pair of `V` outside the graph violates
the monotonicity inequality against some pair of `V` in the graph. -/
def SvMaximalMonotoneLocallyAt (T : E → Set E) (xbar vbar : E) : Prop :=
  SvMonotone T ∧ vbar ∈ T xbar ∧ ∃ V ∈ 𝓝 (xbar, vbar), ∀ p ∈ V, p.2 ∉ T p.1 →
    ∃ q ∈ V, q.2 ∈ T q.1 ∧ ⟪p.2 - q.2, p.1 - q.1⟫_ℝ < 0

theorem SvMaximalMonotone.svMonotone {T : E → Set E} (hT : SvMaximalMonotone T) :
    SvMonotone T :=
  hT.1

/-- Maximality in the contrapositive form used throughout Chapter 12: a pair
satisfying the monotonicity inequality against the whole graph belongs to the
graph. -/
theorem SvMaximalMonotone.mem_of_forall_inner_nonneg {T : E → Set E}
    (hT : SvMaximalMonotone T) {x v : E}
    (h : ∀ x' v', v' ∈ T x' → 0 ≤ ⟪v - v', x - x'⟫_ℝ) : v ∈ T x := by
  by_contra hv
  obtain ⟨x', v', hv', hlt⟩ := hT.2 x v hv
  exact (h x' v' hv').not_gt hlt

/-- For a maximal monotone mapping, membership in the graph is characterized
by the monotonicity inequality against the whole graph. -/
theorem SvMaximalMonotone.mem_iff {T : E → Set E} (hT : SvMaximalMonotone T) {x v : E} :
    v ∈ T x ↔ ∀ x' v', v' ∈ T x' → 0 ≤ ⟪v - v', x - x'⟫_ℝ :=
  ⟨fun hv _ _ hv' ↦ hT.1 hv' hv, hT.mem_of_forall_inner_nonneg⟩

/-- Maximal monotonicity in the contrapositive form. -/
theorem svMaximalMonotone_iff_forall_inner_nonneg {T : E → Set E} :
    SvMaximalMonotone T ↔ SvMonotone T ∧
      ∀ x v, (∀ x' v', v' ∈ T x' → 0 ≤ ⟪v - v', x - x'⟫_ℝ) → v ∈ T x := by
  constructor
  · intro hT
    exact ⟨hT.1, fun _ _ ↦ hT.mem_of_forall_inner_nonneg⟩
  · rintro ⟨hT, hmax⟩
    refine ⟨hT, fun x v hv ↦ ?_⟩
    by_contra hneg
    push_neg at hneg
    exact hv (hmax x v hneg)

/-- **Definition 12.5**, equivalence of its two formulations: a monotone
mapping is maximal monotone exactly when no monotone mapping has a larger
graph. -/
theorem svMaximalMonotone_iff_no_enlargement {T : E → Set E} :
    SvMaximalMonotone T ↔ SvMonotone T ∧
      ∀ T' : E → Set E, SvMonotone T' → svGraph T ⊆ svGraph T' → svGraph T' = svGraph T := by
  classical
  constructor
  · intro hT
    refine ⟨hT.1, fun T' hT' hsub ↦ ?_⟩
    refine Subset.antisymm (fun p hp ↦ ?_) hsub
    refine hT.mem_of_forall_inner_nonneg fun x' v' hv' ↦ ?_
    exact hT' (hsub (show (x', v') ∈ svGraph T from hv')) hp
  · rintro ⟨hT, hmax⟩
    refine svMaximalMonotone_iff_forall_inner_nonneg.2 ⟨hT, fun x v h ↦ ?_⟩
    let T' : E → Set E := fun y ↦ T y ∪ {w | y = x ∧ w = v}
    have hT' : SvMonotone T' := by
      rintro x₀ v₀ (h₀ | ⟨rfl, rfl⟩) x₁ v₁ (h₁ | ⟨rfl, rfl⟩)
      · exact hT h₀ h₁
      · exact h x₀ v₀ h₀
      · rw [inner_sub_sub_comm]
        exact h x₁ v₁ h₁
      · simp
    have hsub : svGraph T ⊆ svGraph T' := fun p hp ↦ Or.inl hp
    have hp : (x, v) ∈ svGraph T' := Or.inr ⟨rfl, rfl⟩
    rw [hmax T' hT' hsub] at hp
    exact hp

/-- A maximal monotone mapping is maximal monotone locally around every point
of its graph, with the whole space as neighborhood. -/
theorem SvMaximalMonotone.locallyAt {T : E → Set E} (hT : SvMaximalMonotone T) {x v : E}
    (hv : v ∈ T x) : SvMaximalMonotoneLocallyAt T x v := by
  refine ⟨hT.1, hv, univ, univ_mem, fun p _ hp ↦ ?_⟩
  obtain ⟨x', v', hv', hlt⟩ := hT.2 p.1 p.2 hp
  exact ⟨(x', v'), mem_univ _, hv', hlt⟩

/-- Local maximal monotonicity with the whole space as neighborhood is maximal
monotonicity. -/
theorem svMaximalMonotone_of_univ {T : E → Set E} (hT : SvMonotone T)
    (h : ∀ p : E × E, p.2 ∉ T p.1 → ∃ q : E × E, q.2 ∈ T q.1 ∧ ⟪p.2 - q.2, p.1 - q.1⟫_ℝ < 0) :
    SvMaximalMonotone T := by
  refine ⟨hT, fun x v hv ↦ ?_⟩
  obtain ⟨q, hq, hlt⟩ := h (x, v) hv
  exact ⟨q.1, q.2, hq, hlt⟩

/-- Two maximal monotone mappings with nested graphs coincide. -/
theorem SvMaximalMonotone.eq_of_subset {S T : E → Set E} (hS : SvMaximalMonotone S)
    (hT : SvMonotone T) (hST : ∀ x, S x ⊆ T x) : T = S := by
  have h := (svMaximalMonotone_iff_no_enlargement.1 hS).2 T hT (fun p hp ↦ hST _ hp)
  funext x
  ext v
  have := congrArg (fun G : Set (E × E) ↦ (x, v) ∈ G) h
  simpa [svGraph] using this

end Monotonicity

end RW
