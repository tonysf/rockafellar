/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Separation of Convex Cones

Exercise 6.48.

The separation vocabulary is the book's, from the paragraph opening Chapter
2G*: a hyperplane `{x | ⟨a, x⟩ = α}` with `a ≠ 0` *separates* two sets when
they lie in the two corresponding closed half-spaces, the separation is
*proper* when the hyperplane does not contain both, and 6.48(c)'s *almost
strict* separation asks the nonzero parts to lie in complementary open
half-spaces.  Those notions are not in the repository, since Chapter 2 is not
ledgered, so they are introduced here, exactly as `IsLocallyClosedAt` -- a
Chapter 1 notion -- was introduced for Definition 6.4.

For *cones* the separating hyperplane may always be taken through the origin,
and that is what makes the first clause elementary: the separation inequality
`⟨a, x⟩ ≤ α` along the whole ray `tx`, `t > 0`, forces `⟨a, x⟩ ≤ 0`.  So
separability is literally the statement that `K₁* ∩ [-K₂*]` contains a nonzero
vector, with no appeal to Hahn--Banach at all; Hahn--Banach enters only for
the *proper* separation of clause (b).
-/

import RockafellarWets.Chapter3.HomogeneousCompletion
import RockafellarWets.Chapter6.Polarity
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

open Set
open scoped Pointwise InnerProductSpace

namespace RW

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two sets can be separated when some hyperplane `{x | ⟨a, x⟩ = α}` with
`a ≠ 0` has one of them in each closed half-space. -/
def CanBeSeparated (C₁ C₂ : Set E) : Prop :=
  ∃ (a : E) (α : ℝ), a ≠ 0 ∧ (∀ x ∈ C₁, ⟪a, x⟫_ℝ ≤ α) ∧ ∀ y ∈ C₂, α ≤ ⟪a, y⟫_ℝ

/-- The separation is *proper* when the separating hyperplane does not contain
both sets. -/
def CanBeSeparatedProperly (C₁ C₂ : Set E) : Prop :=
  ∃ (a : E) (α : ℝ), a ≠ 0 ∧ (∀ x ∈ C₁, ⟪a, x⟫_ℝ ≤ α) ∧ (∀ y ∈ C₂, α ≤ ⟪a, y⟫_ℝ) ∧
    ¬ ((∀ x ∈ C₁, ⟪a, x⟫_ℝ = α) ∧ ∀ y ∈ C₂, ⟪a, y⟫_ℝ = α)

theorem CanBeSeparatedProperly.canBeSeparated {C₁ C₂ : Set E}
    (h : CanBeSeparatedProperly C₁ C₂) : CanBeSeparated C₁ C₂ := by
  obtain ⟨a, α, ha, h₁, h₂, -⟩ := h
  exact ⟨a, α, ha, h₁, h₂⟩

/-- **Exercise 6.48(c)**: two cones are separated *almost strictly* when their
nonzero parts lie in complementary open half-spaces through the origin. -/
def CanBeSeparatedAlmostStrictly (K₁ K₂ : Set E) : Prop :=
  ∃ a : E, a ≠ 0 ∧ (∀ x ∈ K₁, x ≠ 0 → ⟪a, x⟫_ℝ < 0) ∧
    ∀ y ∈ K₂, y ≠ 0 → 0 < ⟪a, y⟫_ℝ

end Definitions

section PolarOfDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The polar of a difference of cones is the intersection of the polar of the
first with the negative of the polar of the second. -/
theorem polarCone_sub {K₁ K₂ : Set E} (h₁ : IsCone K₁) (h₂ : IsCone K₂) :
    polarCone (K₁ - K₂) = polarCone K₁ ∩ (-polarCone K₂) := by
  ext v
  constructor
  · intro hv
    constructor
    · intro x hx
      have h := hv (x - 0) ⟨x, hx, 0, h₂.1, rfl⟩
      simpa using h
    · rw [Set.mem_neg]
      intro y hy
      have h := hv (0 - y) ⟨0, h₁.1, y, hy, rfl⟩
      rw [zero_sub, inner_neg_right] at h
      rw [inner_neg_left]
      exact h
  · rintro ⟨hv₁, hv₂⟩ _ ⟨x, hx, y, hy, rfl⟩
    have hxle : ⟪v, x⟫_ℝ ≤ 0 := hv₁ x hx
    have hyle : ⟪-v, y⟫_ℝ ≤ 0 := (Set.mem_neg.1 hv₂) y hy
    rw [inner_neg_left] at hyle
    rw [inner_sub_right]
    linarith

end PolarOfDifference

section SeparationOfCones

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Along a ray inside a cone, a bound `⟨a, x⟩ ≤ α` forces `⟨a, x⟩ ≤ 0`. -/
theorem inner_nonpos_of_le_on_isCone {K : Set E} (hK : IsCone K) {a : E} {α : ℝ}
    (hb : ∀ x ∈ K, ⟪a, x⟫_ℝ ≤ α) {x : E} (hx : x ∈ K) : ⟪a, x⟫_ℝ ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have ht : 0 < (|α| + 1) / ⟪a, x⟫_ℝ := by positivity
  have hmem : ((|α| + 1) / ⟪a, x⟫_ℝ) • x ∈ K := hK.2 hx ht
  have hle := hb _ hmem
  rw [real_inner_smul_right, div_mul_cancel₀ _ (ne_of_gt hpos)] at hle
  linarith [le_abs_self α]

/-- **Exercise 6.48(a)**: two cones can be separated exactly when their polars
meet in a nonzero vector.  For cones the separating hyperplane may be taken
through the origin, so no separation theorem is needed in either direction. -/
theorem canBeSeparated_iff_exists_ne_zero {K₁ K₂ : Set E} (h₁ : IsCone K₁)
    (h₂ : IsCone K₂) :
    CanBeSeparated K₁ K₂ ↔ ∃ v ∈ polarCone K₁ ∩ (-polarCone K₂), v ≠ 0 := by
  constructor
  · rintro ⟨a, α, ha, hb₁, hb₂⟩
    refine ⟨a, ⟨fun x hx ↦ inner_nonpos_of_le_on_isCone h₁ hb₁ hx, ?_⟩, ha⟩
    rw [Set.mem_neg]
    intro y hy
    rw [inner_neg_left]
    have hge : ∀ y ∈ K₂, ⟪-a, y⟫_ℝ ≤ -α := by
      intro y hy
      rw [inner_neg_left]
      linarith [hb₂ y hy]
    have h := inner_nonpos_of_le_on_isCone h₂ hge hy
    rw [inner_neg_left] at h
    exact h
  · rintro ⟨v, ⟨hv₁, hv₂⟩, hv0⟩
    refine ⟨v, 0, hv0, fun x hx ↦ hv₁ x hx, fun y hy ↦ ?_⟩
    have h := (Set.mem_neg.1 hv₂) y hy
    rw [inner_neg_left] at h
    linarith

end SeparationOfCones

section DenseConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A convex set whose closure is everything is everything.  In finite
dimensions a convex set with empty interior lies in a proper affine subspace,
which is closed. -/
theorem eq_univ_of_convex_of_closure_eq_univ {C : Set E} (hC : Convex ℝ C)
    (hcl : closure C = univ) : C = univ := by
  have hint : (interior C).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have haff : affineSpan ℝ C ≠ ⊤ := by
      intro h
      have hne := (hC.interior_nonempty_iff_affineSpan_eq_top).2 h
      rw [hempty] at hne
      exact hne.ne_empty rfl
    have hclosed : IsClosed ((affineSpan ℝ C : AffineSubspace ℝ E) : Set E) :=
      AffineSubspace.closed_of_finiteDimensional _
    have hsub : closure C ⊆ ((affineSpan ℝ C : AffineSubspace ℝ E) : Set E) :=
      hclosed.closure_subset_iff.2 (subset_affineSpan ℝ C)
    rw [hcl] at hsub
    exact haff (eq_top_iff.2 fun z _ ↦ hsub (mem_univ z))
  have h2 := hC.interior_closure_eq_interior_of_nonempty_interior hint
  rw [hcl, interior_univ] at h2
  exact eq_univ_of_univ_subset (h2 ▸ interior_subset)

end DenseConvex

section SeparationAndDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem isCone_sub {K₁ K₂ : Set E} (h₁ : IsCone K₁) (h₂ : IsCone K₂) :
    IsCone (K₁ - K₂) := by
  constructor
  · exact ⟨0, h₁.1, 0, h₂.1, by simp⟩
  · rintro _ ⟨x, hx, y, hy, rfl⟩ c hc
    refine ⟨c • x, h₁.2 hx hc, c • y, h₂.2 hy hc, ?_⟩
    rw [smul_sub]

/-- **Exercise 6.48(a)**, the printed form: two convex cones can be separated
exactly when their difference is not the whole space. -/
theorem canBeSeparated_iff_sub_ne_univ {K₁ K₂ : Set E} (h₁conv : Convex ℝ K₁)
    (h₁ : IsCone K₁) (h₂conv : Convex ℝ K₂) (h₂ : IsCone K₂) :
    CanBeSeparated K₁ K₂ ↔ K₁ - K₂ ≠ univ := by
  rw [canBeSeparated_iff_exists_ne_zero h₁ h₂, ← polarCone_sub h₁ h₂]
  constructor
  · rintro ⟨v, hv, hv0⟩ hEq
    have hmem : v ∈ K₁ - K₂ := by rw [hEq]; exact mem_univ v
    have h := hv v hmem
    rw [real_inner_self_eq_norm_sq] at h
    have : 0 < ‖v‖ ^ 2 := by positivity
    linarith
  · intro hne
    by_contra hno
    push_neg at hno
    have hpolar : polarCone (K₁ - K₂) = {0} := by
      refine Subset.antisymm (fun v hv ↦ ?_) ?_
      · rw [mem_singleton_iff]
        exact hno v hv
      · rintro v hv
        rw [mem_singleton_iff] at hv
        rw [hv]
        exact zero_mem_polarCone _
    have hconv : Convex ℝ (K₁ - K₂) := h₁conv.sub h₂conv
    have hcone : IsCone (K₁ - K₂) := isCone_sub h₁ h₂
    have hbip := polarCone_bipolar (K₁ - K₂)
    rw [hpolar, polarCone_singleton_zero,
      conicHull_eq_self_of_convex_isCone hconv hcone] at hbip
    exact hne (eq_univ_of_convex_of_closure_eq_univ hconv hbip.symm)

end SeparationAndDifference

section ProperSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A hyperplane through the origin has empty interior. -/
theorem interior_setOf_inner_eq_zero_eq_empty {v : E} (hv : v ≠ 0) :
    interior {z : E | ⟪v, z⟫_ℝ = 0} = ∅ := by
  refine eq_empty_of_forall_notMem fun w hw ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hw)
  have hwS : w ∈ {z : E | ⟪v, z⟫_ℝ = 0} := interior_subset hw
  have hw0 : ⟪v, w⟫_ℝ = 0 := hwS
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have ht : 0 < ε / (2 * ‖v‖) := by positivity
  have hmem : w + (ε / (2 * ‖v‖)) • v ∈ Metric.ball w ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    have hval : ε / (2 * ‖v‖) * ‖v‖ = ε / 2 := by field_simp
    rw [hval]
    linarith
  have h0 : ⟪v, w + (ε / (2 * ‖v‖)) • v⟫_ℝ = 0 := hball hmem
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hw0,
    zero_add] at h0
  have : 0 < ε / (2 * ‖v‖) * ‖v‖ ^ 2 := by positivity
  linarith

/-- **Exercise 6.48(b)**: the sufficient condition for *proper* separation.  No
separation theorem is needed: the separating vector is supplied by clause (a),
and properness follows because a hyperplane through the origin has empty
interior while `K₁ - K₂` does not. -/
theorem canBeSeparatedProperly_of_interior_nonempty {K₁ K₂ : Set E}
    (h₁conv : Convex ℝ K₁) (h₁ : IsCone K₁) (h₂conv : Convex ℝ K₂) (h₂ : IsCone K₂)
    (hne : K₁ - K₂ ≠ univ) (hint : (interior (K₁ - K₂)).Nonempty) :
    CanBeSeparatedProperly K₁ K₂ := by
  obtain ⟨v, ⟨hv₁, hv₂⟩, hv0⟩ := (canBeSeparated_iff_exists_ne_zero h₁ h₂).1
    ((canBeSeparated_iff_sub_ne_univ h₁conv h₁ h₂conv h₂).2 hne)
  refine ⟨v, 0, hv0, fun x hx ↦ hv₁ x hx, fun y hy ↦ ?_, ?_⟩
  · have h := (Set.mem_neg.1 hv₂) y hy
    rw [inner_neg_left] at h
    linarith
  · rintro ⟨hz₁, hz₂⟩
    obtain ⟨w, hw⟩ := hint
    have hsub : K₁ - K₂ ⊆ {z : E | ⟪v, z⟫_ℝ = 0} := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [mem_setOf_eq, inner_sub_right, hz₁ x hx, hz₂ y hy, sub_zero]
    have hwint : w ∈ interior {z : E | ⟪v, z⟫_ℝ = 0} := interior_mono hsub hw
    rw [interior_setOf_inner_eq_zero_eq_empty hv0] at hwint
    exact hwint

/-- **Exercise 6.48(a)**, polar form of the separability condition. -/
theorem sub_ne_univ_iff_polarCone_ne_zero {K₁ K₂ : Set E} (h₁conv : Convex ℝ K₁)
    (h₁ : IsCone K₁) (h₂conv : Convex ℝ K₂) (h₂ : IsCone K₂) :
    K₁ - K₂ ≠ univ ↔ polarCone K₁ ∩ (-polarCone K₂) ≠ ({0} : Set E) := by
  rw [← canBeSeparated_iff_sub_ne_univ h₁conv h₁ h₂conv h₂,
    canBeSeparated_iff_exists_ne_zero h₁ h₂]
  constructor
  · rintro ⟨v, hv, hv0⟩ hEq
    rw [hEq, mem_singleton_iff] at hv
    exact hv0 hv
  · intro hne
    by_contra hno
    push_neg at hno
    refine hne (Subset.antisymm (fun v hv ↦ ?_) ?_)
    · rw [mem_singleton_iff]
      exact hno v hv
    · rintro v hv
      rw [mem_singleton_iff] at hv
      rw [hv, ← polarCone_sub h₁ h₂]
      exact zero_mem_polarCone _

/-- **Exercise 6.48(b)**, polar form of the interior condition: it is
pointedness of `K₁* ∩ [-K₂*]`, by 6.22. -/
theorem interior_sub_nonempty_iff_isPointed {K₁ K₂ : Set E} (h₁conv : Convex ℝ K₁)
    (h₁ : IsCone K₁) (h₂conv : Convex ℝ K₂) (h₂ : IsCone K₂) :
    (interior (K₁ - K₂)).Nonempty ↔ IsPointed (polarCone K₁ ∩ (-polarCone K₂)) := by
  rw [← polarCone_sub h₁ h₂]
  exact interior_nonempty_iff_isPointed_polarCone (h₁conv.sub h₂conv) (isCone_sub h₁ h₂)

end ProperSeparation

section AlmostStrictSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem interior_neg (S : Set E) : interior (-S) = -interior S := by
  have h1 : (-S : Set E) = (Homeomorph.neg E) ⁻¹' S := by
    ext z
    simp [Set.mem_neg]
  have h2 : (-interior S : Set E) = (Homeomorph.neg E) ⁻¹' interior S := by
    ext z
    simp [Set.mem_neg]
  rw [h1, h2]
  exact ((Homeomorph.neg E).preimage_interior S).symm

/-- **Exercise 6.48(c)**: almost strict separation is exactly a common point of
`int K₁*` and `-int K₂*`.  This is 6.22's strict pairing criterion read on
each cone separately. -/
theorem canBeSeparatedAlmostStrictly_iff_interior_polarCone [Nontrivial E]
    {K₁ K₂ : Set E} (h₁closed : IsClosed K₁) (h₁ : IsCone K₁)
    (h₂closed : IsClosed K₂) (h₂ : IsCone K₂) :
    CanBeSeparatedAlmostStrictly K₁ K₂ ↔
      (interior (polarCone K₁) ∩ (-interior (polarCone K₂))).Nonempty := by
  constructor
  · rintro ⟨a, -, hb₁, hb₂⟩
    refine ⟨a, ?_, ?_⟩
    · rw [mem_interior_polarCone_iff_inner_lt_zero h₁closed h₁]
      intro x hx hx0
      rw [real_inner_comm]
      exact hb₁ x hx hx0
    · rw [Set.mem_neg, mem_interior_polarCone_iff_inner_lt_zero h₂closed h₂]
      intro y hy hy0
      have heq : ⟪y, -a⟫_ℝ = -⟪a, y⟫_ℝ := by
        rw [inner_neg_right, real_inner_comm]
      rw [heq]
      linarith [hb₂ y hy hy0]
  · intro hS
    have hopen : IsOpen (interior (polarCone K₁) ∩ (-interior (polarCone K₂))) := by
      refine isOpen_interior.inter ?_
      rw [← interior_neg]
      exact isOpen_interior
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ interior (polarCone K₁) ∩ (-interior (polarCone K₂)),
        a ≠ 0 := by
      obtain ⟨a, ha⟩ := hS
      by_cases ha0 : a = 0
      · subst ha0
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds ha)
        obtain ⟨u, hu⟩ := exists_ne (0 : E)
        have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
        refine ⟨(ε / (2 * ‖u‖)) • u, hball ?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (by positivity : (0:ℝ) < ε / (2 * ‖u‖))]
          have hval : ε / (2 * ‖u‖) * ‖u‖ = ε / 2 := by field_simp
          rw [hval]
          linarith
        · exact smul_ne_zero (by positivity) hu
      · exact ⟨a, ha, ha0⟩
    refine ⟨a, ha0, ?_, ?_⟩
    · intro x hx hx0
      have h := (mem_interior_polarCone_iff_inner_lt_zero h₁closed h₁).1 ha.1 x hx hx0
      rwa [real_inner_comm] at h
    · intro y hy hy0
      have h := (mem_interior_polarCone_iff_inner_lt_zero h₂closed h₂).1
        (Set.mem_neg.1 ha.2) y hy hy0
      have heq : ⟪y, -a⟫_ℝ = -⟪a, y⟫_ℝ := by
        rw [inner_neg_right, real_inner_comm]
      rw [heq] at h
      linarith

/-- **Exercise 6.48(c)**: that common point exists exactly when the closure of
`K₁ - K₂` is pointed. -/
theorem interior_polarCone_inter_nonempty_iff_isPointed_closure {K₁ K₂ : Set E}
    (h₁ : IsCone K₁) (h₂ : IsCone K₂) :
    (interior (polarCone K₁) ∩ (-interior (polarCone K₂))).Nonempty ↔
      IsPointed (closure (K₁ - K₂)) := by
  have hstep : interior (polarCone K₁) ∩ (-interior (polarCone K₂))
      = interior (polarCone (closure (K₁ - K₂))) := by
    rw [polarCone_closure, polarCone_sub h₁ h₂, interior_inter, interior_neg]
  rw [hstep]
  exact interior_polarCone_nonempty_iff_isPointed isClosed_closure
    (RW.IsCone.closure (isCone_sub h₁ h₂))

end AlmostStrictSeparation

section PointedDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem isPointed_of_isPointed_neg {K : Set E} (hK : IsPointed (-K)) : IsPointed K := by
  intro n z hz hsum i
  have hneg : ∀ j, -z j ∈ -K := by
    intro j
    rw [Set.mem_neg, neg_neg]
    exact hz j
  have hsum' : ∑ j, -z j = 0 := by
    rw [Finset.sum_neg_distrib, hsum, neg_zero]
  have h := hK n (fun j ↦ -z j) hneg hsum' i
  simpa using h

omit [FiniteDimensional ℝ E] in
theorem isCone_neg {K : Set E} (hK : IsCone K) : IsCone (-K) := by
  constructor
  · rw [Set.mem_neg, neg_zero]
    exact hK.1
  · intro x hx c hc
    rw [Set.mem_neg] at hx ⊢
    rw [← smul_neg]
    exact hK.2 hx hc

omit [FiniteDimensional ℝ E] in
/-- **Exercise 6.48(c)**, the easy direction of the last equivalence. -/
theorem isPointed_and_inter_of_isPointed_closure_sub {K₁ K₂ : Set E} (h₁ : IsCone K₁)
    (h₂ : IsCone K₂) (h : IsPointed (closure (K₁ - K₂))) :
    IsPointed K₁ ∧ IsPointed K₂ ∧ K₁ ∩ K₂ = ({0} : Set E) := by
  have hsub₁ : K₁ ⊆ closure (K₁ - K₂) := fun x hx ↦
    subset_closure ⟨x, hx, 0, h₂.1, by simp⟩
  have hsubneg₂ : -K₂ ⊆ closure (K₁ - K₂) := by
    intro y hy
    rw [Set.mem_neg] at hy
    exact subset_closure ⟨0, h₁.1, -y, hy, by simp⟩
  refine ⟨h.mono hsub₁, isPointed_of_isPointed_neg (h.mono hsubneg₂), ?_⟩
  refine Subset.antisymm (fun z hz ↦ ?_) ?_
  · rw [mem_singleton_iff]
    have hz₁ : z ∈ closure (K₁ - K₂) := hsub₁ hz.1
    have hz₂ : -z ∈ closure (K₁ - K₂) := subset_closure ⟨0, h₁.1, z, hz.2, by simp⟩
    have hfam : ∀ i : Fin 2, ![z, -z] i ∈ closure (K₁ - K₂) := by
      intro i
      fin_cases i
      · simpa using hz₁
      · simpa using hz₂
    have hzero : ∑ i, ![z, -z] i = 0 := by simp [Fin.sum_univ_two]
    have hres := h 2 ![z, -z] hfam hzero 0
    simpa using hres
  · rintro z hz
    rw [mem_singleton_iff] at hz
    subst hz
    exact ⟨h₁.1, h₂.1⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem finiteSetSum_pair_eq_sub (K₁ K₂ : Set E) :
    finiteSetSum ![K₁, -K₂] = K₁ - K₂ := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h0 : z 0 ∈ K₁ := by simpa using hz 0
    have h1 : -z 1 ∈ K₂ := by
      have := hz 1
      simpa [Set.mem_neg] using this
    refine ⟨z 0, h0, -z 1, h1, ?_⟩
    rw [Fin.sum_univ_two]
    dsimp only
    rw [sub_neg_eq_add]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨![a, -b], ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using ha
      · simpa [Set.mem_neg] using hb
    · rw [Fin.sum_univ_two]
      simp [sub_eq_add_neg]

/-- **Exercise 6.48(c)**, the substantive direction: two closed convex pointed
cones meeting only at the origin have a closed, pointed difference.  Closedness
is Chapter 3's no-cancellation criterion for finite set sums, whose hypothesis
is exactly `K₁ ∩ K₂ = {0}` once the horizon cones of the closed cones are
themselves. -/
theorem isPointed_closure_sub {K₁ K₂ : Set E} (h₁closed : IsClosed K₁)
    (h₁conv : Convex ℝ K₁) (h₁ : IsCone K₁) (h₂closed : IsClosed K₂)
    (h₂conv : Convex ℝ K₂) (h₂ : IsCone K₂) (hp₁ : IsPointed K₁)
    (hp₂ : IsPointed K₂) (hinter : K₁ ∩ K₂ = ({0} : Set E)) :
    IsPointed (closure (K₁ - K₂)) := by
  have hnegcone : IsCone (-K₂) := isCone_neg h₂
  have hnegclosed : IsClosed (-K₂) := h₂closed.neg
  have hclosedsub : IsClosed (K₁ - K₂) := by
    have hfam : ∀ i : Fin 2, IsClosed ((![K₁, -K₂] : Fin 2 → Set E) i) := by
      intro i
      fin_cases i
      · simpa using h₁closed
      · simpa using hnegclosed
    have hker : ∀ u : Fin 2 → E,
        (∀ i, u i ∈ horizonCone ((![K₁, -K₂] : Fin 2 → Set E) i)) →
        (∑ i, u i) = 0 → u = 0 := by
      intro u hu hsum
      have h0 : u 0 ∈ K₁ := by
        have := hu 0
        rwa [show (![K₁, -K₂] : Fin 2 → Set E) 0 = K₁ from rfl,
          horizonCone_eq_self_of_isClosed_isCone h₁closed h₁] at this
      have h1 : u 1 ∈ -K₂ := by
        have := hu 1
        rwa [show (![K₁, -K₂] : Fin 2 → Set E) 1 = -K₂ from rfl,
          horizonCone_eq_self_of_isClosed_isCone hnegclosed hnegcone] at this
      rw [Fin.sum_univ_two] at hsum
      have hu1 : u 1 = -u 0 := by
        have : u 1 = -u 0 := by linear_combination (norm := module) hsum
        exact this
      have hmem : u 0 ∈ K₁ ∩ K₂ := by
        refine ⟨h0, ?_⟩
        rw [Set.mem_neg] at h1
        rw [hu1] at h1
        simpa using h1
      rw [hinter, mem_singleton_iff] at hmem
      funext i
      fin_cases i
      · simpa using hmem
      · simp [hu1, hmem]
    have := isClosed_finiteSetSum_of_horizonCone_no_cancel hfam hker
    rwa [finiteSetSum_pair_eq_sub] at this
  rw [hclosedsub.closure_eq]
  intro n z hz hsum i
  choose xa hxa yb hyb hxy using fun j ↦ Set.mem_sub.1 (hz j)
  have hzeq : (fun j ↦ xa j - yb j) = z := funext hxy
  have hsumsub : ∑ j, (xa j - yb j) = 0 := by rw [hzeq]; exact hsum
  rw [Finset.sum_sub_distrib] at hsumsub
  have hsx : ∑ j, xa j = ∑ j, yb j := sub_eq_zero.1 hsumsub
  have hpK₁ : (∑ j, xa j) ∈ K₁ :=
    sum_mem_of_convex_isCone h₁conv h₁ Finset.univ xa fun j _ ↦ hxa j
  have hpK₂ : (∑ j, xa j) ∈ K₂ := by
    rw [hsx]
    exact sum_mem_of_convex_isCone h₂conv h₂ Finset.univ yb fun j _ ↦ hyb j
  have hp0 : (∑ j, xa j) = 0 := by
    have hmem : (∑ j, xa j) ∈ K₁ ∩ K₂ := ⟨hpK₁, hpK₂⟩
    rw [hinter, mem_singleton_iff] at hmem
    exact hmem
  have hx0 := hp₁ n xa hxa hp0 i
  have hy0 := hp₂ n yb hyb (by rw [← hsx]; exact hp0) i
  rw [← hxy i, hx0, hy0, sub_zero]

/-- **Exercise 6.48(c)**, the last equivalence. -/
theorem isPointed_closure_sub_iff {K₁ K₂ : Set E} (h₁closed : IsClosed K₁)
    (h₁conv : Convex ℝ K₁) (h₁ : IsCone K₁) (h₂closed : IsClosed K₂)
    (h₂conv : Convex ℝ K₂) (h₂ : IsCone K₂) :
    IsPointed (closure (K₁ - K₂)) ↔
      IsPointed K₁ ∧ IsPointed K₂ ∧ K₁ ∩ K₂ = ({0} : Set E) := by
  refine ⟨isPointed_and_inter_of_isPointed_closure_sub h₁ h₂, ?_⟩
  rintro ⟨hp₁, hp₂, hinter⟩
  exact isPointed_closure_sub h₁closed h₁conv h₁ h₂closed h₂conv h₂ hp₁ hp₂ hinter

end PointedDifference

end RW
