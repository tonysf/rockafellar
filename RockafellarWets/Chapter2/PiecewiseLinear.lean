/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2I: Piecewise linear functions

This file formalizes Section I of Chapter 2 of Rockafellar–Wets in finite
dimensions, with polyhedral sets in the Chapter 3 sense `IsPolyhedral`, which
agrees with the book's finite intersections of closed half-spaces by
Minkowski–Weyl (`isHPolyhedral_iff_isPolyhedral`, and
`isPolyhedralSet_iff_isPolyhedral` of `LevelSetsAffine`).

* Definition 2.47: piecewise linear mappings `IsPiecewiseLinearOn` (Chapter 12)
  and functions `IsPiecewiseLinear` (Chapter 10); `isPiecewiseLinear_iff`
  identifies the latter with 2.47(b).
* Exercise 2.48: Chapter 12 `isPiecewiseLinearOn_iff_isPiecewisePolyhedral_graph`.
* Theorem 2.49: proper convex piecewise linear functions are exactly the
  proper functions with polyhedral epigraphs, and polyhedral epigraphs are
  exactly those of functions `max {l₁, …, l_p}` on a polyhedral set, `∞`
  elsewhere; such functions are convex and lsc.
* Lemma 2.50: a convex finite union of polyhedral sets is polyhedral, and when
  its interior is nonempty the pieces with empty interior are superfluous;
  moreover it is then the union of finitely many polyhedral cells `Dⱼ`, each in
  some piece, with `int Dⱼ ≠ ∅`, `Dⱼ = cl(int Dⱼ)` and pairwise disjoint
  interiors (`exists_refined_iUnion_of_interior_nonempty`).
-/

import RockafellarWets.Chapter2.LevelSetsAffine
import RockafellarWets.Chapter10.ConvexPolyhedralUnions
import RockafellarWets.Chapter12.PiecewisePolyhedralMonotonicity

open Set Filter Topology
open scoped InnerProductSpace Pointwise

noncomputable section

namespace RW

/-! ## Lemma 2.50 -/

section Unions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A polyhedron has finite point and direction generators lying in the
polyhedron and in its horizon cone. -/
theorem exists_generators_subset_of_isPolyhedral {C : Set E} (hC : IsPolyhedral C) :
    ∃ s t : Finset E, C = extendedConvexHull (s : Set E) (t : Set E) ∧
      (s : Set E) ⊆ C ∧ (t : Set E) ⊆ horizonCone C := by
  rcases C.eq_empty_or_nonempty with h | h
  · refine ⟨∅, ∅, ?_, by simp, by simp⟩
    simp [h, extendedConvexHull]
  · obtain ⟨s, t, hs, he⟩ := hC.exists_nonempty_generators_of_nonempty h
    refine ⟨s, t, he, ?_, ?_⟩
    · rw [he]
      exact subset_extendedConvexHull_left _ _
    · rw [he, horizonCone_extendedConvexHull_finset_eq_conicHull s t hs
        (isClosed_conicHull_finset t)]
      exact subset_conicHull

/-- **Lemma 2.50**: if a convex set is the union of finitely many polyhedral
sets, it is itself polyhedral (in any finite-dimensional real normed space). -/
theorem isPolyhedral_iUnion_of_convex_normed {ι : Type*} [Finite ι] {C : ι → Set E}
    (hC : ∀ i, IsPolyhedral (C i)) (hc : Convex ℝ (⋃ i, C i)) : IsPolyhedral (⋃ i, C i) := by
  classical
  have := Fintype.ofFinite ι
  choose s t he hs ht using fun i ↦ exists_generators_subset_of_isPolyhedral (hC i)
  let S := Finset.univ.biUnion s
  let T := Finset.univ.biUnion t
  have hS (i : ι) : (s i : Set E) ⊆ (S : Set E) := fun y hy ↦
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hy⟩
  have hT (i : ι) : (t i : Set E) ⊆ (T : Set E) := fun y hy ↦
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hy⟩
  have hSsub : (S : Set E) ⊆ ⋃ i, C i := by
    intro y hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
    exact mem_iUnion.mpr ⟨i, hs i hi⟩
  have hTsub : (T : Set E) ⊆ horizonCone (⋃ i, C i) := by
    intro y hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
    exact horizonCone_mono (subset_iUnion C i) (ht i hi)
  have hclosed : IsClosed (⋃ i, C i) := isClosed_iUnion_of_finite fun i ↦ (hC i).isClosed
  refine ⟨S, T, Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact extendedConvexHull_mono (hS i) (hT i) (he i ▸ hi)
  · rintro y ⟨a, ha, b, hb, rfl⟩
    have haC := convexHull_minimal hSsub hc ha
    have hbC := conicHull_minimal (convex_horizonCone hc) (isCone_horizonCone _) hTsub hb
    simpa [add_comm] using smul_add_mem_of_mem_horizonCone hc hclosed haC hbC (τ := 1)
      zero_le_one

/-- **Lemma 2.50**: when the convex union `C` of finitely many polyhedral sets
has nonempty interior, the pieces with empty interior are superfluous. -/
theorem iUnion_eq_iUnion_of_interior_nonempty {ι : Type*} [Finite ι] {C : ι → Set E}
    (hC : ∀ i, IsPolyhedral (C i)) (hc : Convex ℝ (⋃ i, C i))
    (hint : (interior (⋃ i, C i)).Nonempty) :
    (⋃ i, C i) = ⋃ i ∈ {i | (interior (C i)).Nonempty}, C i := by
  classical
  have := Fintype.ofFinite ι
  set K₀ := {i | (interior (C i)).Nonempty}
  have hcl : ∀ i, IsClosed (C i) := fun i ↦ (hC i).isClosed
  -- the union of the pieces with empty interior has empty interior
  have hthin : ∀ s : Finset ι, (∀ i ∈ s, i ∉ K₀) → interior (⋃ i ∈ s, C i) = ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert j s hj ih =>
      intro hs
      rw [Finset.set_biUnion_insert, union_comm,
        interior_union_isClosed_of_interior_empty
          (isClosed_biUnion_finset fun i _ ↦ hcl i)
          (not_nonempty_iff_eq_empty.mp (hs j (Finset.mem_insert_self j s)))]
      exact ih fun i hi ↦ hs i (Finset.mem_insert_of_mem hi)
  apply Subset.antisymm _ (iUnion₂_subset fun i _ ↦ subset_iUnion C i)
  set U := ⋃ i ∈ K₀, C i
  have hUcl : IsClosed U := by
    have : U = ⋃ i ∈ Finset.univ.filter (· ∈ K₀), C i := by
      ext x
      simp [U]
    rw [this]
    exact isClosed_biUnion_finset fun i _ ↦ hcl i
  have hsubU : interior (⋃ i, C i) ⊆ U := by
    intro x hx
    by_contra hxU
    have hopen : IsOpen (interior (⋃ i, C i) \ U) := isOpen_interior.sdiff hUcl
    have hsub : interior (⋃ i, C i) \ U ⊆ ⋃ i ∈ Finset.univ.filter (· ∉ K₀), C i := by
      rintro y ⟨hy, hyU⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hy)
      have hiK : i ∉ K₀ := fun hiK ↦ hyU (mem_biUnion hiK hi)
      exact mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiK⟩) hi
    have hempty := hthin (Finset.univ.filter (· ∉ K₀)) (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    have : x ∈ interior (⋃ i ∈ Finset.univ.filter (· ∉ K₀), C i) :=
      interior_maximal hsub hopen ⟨hx, hxU⟩
    rw [hempty] at this
    exact this
  calc (⋃ i, C i) ⊆ closure (⋃ i, C i) := subset_closure
    _ = closure (interior (⋃ i, C i)) :=
        (hc.closure_interior_eq_closure_of_nonempty_interior hint).symm
    _ ⊆ U := closure_minimal hsubU hUcl

omit [FiniteDimensional ℝ E] in
/-- The level sets of a nonzero continuous linear functional have empty interior. -/
theorem interior_setOf_apply_eq_eq_empty {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) (β : ℝ) :
    interior {x | φ x = β} = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra! h
    exact hφ (ContinuousLinearMap.ext h)
  refine eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
  have hcont : Continuous fun t : ℝ ↦ x + t • v := by fun_prop
  have hmem : (fun t : ℝ ↦ x + t • v) ⁻¹' interior {x | φ x = β} ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hx)
  have h₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ interior {x | φ x = β} :=
    nhdsWithin_le_nhds hmem
  have h₂ : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, ht0⟩ := (h₁.and h₂).exists
  have hx' : x ∈ {x | φ x = β} := interior_subset hx
  have ht' : x + t • v ∈ {x | φ x = β} := interior_subset ht
  simp only [mem_setOf_eq, map_add, map_smul, smul_eq_mul] at hx' ht'
  rcases mul_eq_zero.mp (by linarith : t * φ v = 0) with h | h
  · exact ht0.ne' h
  · exact hv h

omit [FiniteDimensional ℝ E] in
/-- Sets on opposite sides of a hyperplane `{φ = β}` (with `φ ≠ 0`) have
disjoint interiors. -/
theorem disjoint_interior_of_subset_le_of_subset_ge {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) (β : ℝ)
    {D₁ D₂ : Set E} (h₁ : D₁ ⊆ {x | φ x ≤ β}) (h₂ : D₂ ⊆ {x | β ≤ φ x}) :
    Disjoint (interior D₁) (interior D₂) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← interior_inter, ← subset_empty_iff,
    ← interior_setOf_apply_eq_eq_empty hφ β]
  exact interior_mono fun x hx ↦ le_antisymm (h₁ hx.1) (h₂ hx.2)

/-- **Lemma 2.50 (refined representation)**: if the convex union `C` of
finitely many polyhedral sets `Cₖ` has nonempty interior, then `C` is the union
of finitely many polyhedral sets `Dⱼ` such that (a) each `Dⱼ` lies in some `Cₖ`,
(b) `int Dⱼ ≠ ∅`, so `Dⱼ = cl(int Dⱼ)`, and (c) the interiors of distinct `Dⱼ`
are disjoint.  The `Dⱼ` are the full-dimensional cells of the arrangement of
the nonconstant affine constraints describing the `Cₖ`, as in the book. -/
theorem exists_refined_iUnion_of_interior_nonempty {ι : Type*} [Finite ι] {C : ι → Set E}
    (hC : ∀ i, IsPolyhedral (C i)) (hc : Convex ℝ (⋃ i, C i))
    (hint : (interior (⋃ i, C i)).Nonempty) :
    ∃ (n : ℕ) (D : Fin n → Set E), (⋃ i, C i) = ⋃ j, D j ∧
      (∀ j, IsPolyhedral (D j)) ∧ (∀ j, ∃ i, D j ⊆ C i) ∧
      (∀ j, (interior (D j)).Nonempty ∧ D j = closure (interior (D j))) ∧
      Pairwise fun j₁ j₂ ↦ Disjoint (interior (D j₁)) (interior (D j₂)) := by
  classical
  have := Fintype.ofFinite ι
  choose m A b hAb using fun i ↦ (hC i).isHPolyhedral
  -- the nonconstant constraints `A i k x ≤ b i k` of all pieces
  let Λ := {p : Σ i, Fin (m i) // A p.1 p.2 ≠ 0}
  let φ : Λ → E →L[ℝ] ℝ := fun p ↦ A p.1.1 p.1.2
  let β : Λ → ℝ := fun p ↦ b p.1.1 p.1.2
  -- the cell of a sign pattern `S`: `≤` on `S`, `≥` off `S`
  let half : Set Λ → Λ → Set E := fun S p ↦
    if p ∈ S then {x | φ p x ≤ β p} else {x | (-φ p) x ≤ -β p}
  let cell : Set Λ → Set E := fun S ↦ ⋂ p, half S p
  have mem_cell : ∀ S x, x ∈ cell S ↔ ∀ p, (p ∈ S → φ p x ≤ β p) ∧ (p ∉ S → β p ≤ φ p x) := by
    intro S x
    simp only [cell, half, mem_iInter]
    refine forall_congr' fun p ↦ ?_
    by_cases hp : p ∈ S <;> simp [hp]
  have cell_poly : ∀ S, IsPolyhedral (cell S) := by
    intro S
    have : cell S = ⋂ p ∈ (Finset.univ : Finset Λ), half S p := by simp [cell]
    rw [this]
    refine (IsHPolyhedral.iInter_finset _ _ fun p _ ↦ ?_).isPolyhedral
    by_cases hp : p ∈ S
    · rw [show half S p = {x | φ p x ≤ β p} from if_pos hp]
      exact IsHPolyhedral.halfspace _ _
    · rw [show half S p = {x | (-φ p) x ≤ -β p} from if_neg hp]
      exact IsHPolyhedral.halfspace _ _
  -- (a): a pattern that is `≤` on all constraints of a nonempty `Cᵢ` gives a cell in `Cᵢ`
  have cell_sub : ∀ S i, (C i).Nonempty → (∀ p : Λ, p.1.1 = i → p ∈ S) → cell S ⊆ C i := by
    rintro S i ⟨y, hy⟩ hS x hx
    rw [hAb i, mem_linearInequalitySet] at hy ⊢
    intro k
    by_cases hk : A i k = 0
    · have := hy k
      rw [hk] at this ⊢
      simpa using this
    · exact ((mem_cell S x).mp hx ⟨⟨i, k⟩, hk⟩).1 (hS _ rfl)
  let good : Set (Set Λ) := {S | ∃ i, (C i).Nonempty ∧ ∀ p : Λ, p.1.1 = i → p ∈ S}
  have hcover : (⋃ i, C i) = ⋃ S : good, cell S := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hi' := hi
      rw [hAb i, mem_linearInequalitySet] at hi'
      let S : Set Λ := {p | φ p x ≤ β p}
      have hS : S ∈ good := by
        refine ⟨i, ⟨x, hi⟩, ?_⟩
        rintro ⟨⟨i', k⟩, hk⟩ (rfl : i' = i)
        exact hi' k
      exact mem_iUnion.mpr ⟨⟨S, hS⟩, (mem_cell S x).mpr fun p ↦ ⟨id, fun hp ↦ (not_le.mp hp).le⟩⟩
    · refine iUnion_subset fun S ↦ ?_
      obtain ⟨i, hi, hS⟩ := S.2
      exact (cell_sub S.1 i hi hS).trans (subset_iUnion C i)
  have hred := iUnion_eq_iUnion_of_interior_nonempty (fun S : good ↦ cell_poly S.1)
    (hcover ▸ hc) (hcover ▸ hint)
  let J := {S : good // (interior (cell S.1)).Nonempty}
  have hdisj : Pairwise fun S₁ S₂ : J ↦
      Disjoint (interior (cell S₁.1.1)) (interior (cell S₂.1.1)) := by
    intro S₁ S₂ hne
    have hne' : S₁.1.1 ≠ S₂.1.1 := fun h ↦ hne (Subtype.ext (Subtype.ext h))
    obtain ⟨p, hp⟩ : ∃ p, ¬(p ∈ S₁.1.1 ↔ p ∈ S₂.1.1) := by
      by_contra! h
      exact hne' (Set.ext h)
    have hφ : φ p ≠ 0 := p.2
    have sub_le : ∀ S : Set Λ, p ∈ S → cell S ⊆ {x | φ p x ≤ β p} :=
      fun S hpS x hx ↦ ((mem_cell S x).mp hx p).1 hpS
    have sub_ge : ∀ S : Set Λ, p ∉ S → cell S ⊆ {x | β p ≤ φ p x} :=
      fun S hpS x hx ↦ ((mem_cell S x).mp hx p).2 hpS
    by_cases h₁ : p ∈ S₁.1.1
    · have h₂ : p ∉ S₂.1.1 := fun h₂ ↦ hp (iff_of_true h₁ h₂)
      exact disjoint_interior_of_subset_le_of_subset_ge hφ (β p) (sub_le _ h₁) (sub_ge _ h₂)
    · have h₂ : p ∈ S₂.1.1 := by
        by_contra h₂
        exact hp (iff_of_false h₁ h₂)
      exact (disjoint_interior_of_subset_le_of_subset_ge hφ (β p) (sub_le _ h₂)
        (sub_ge _ h₁)).symm
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  refine ⟨n, fun j ↦ cell (e.symm j).1.1, ?_, fun j ↦ cell_poly _, fun j ↦ ?_, fun j ↦ ?_,
    fun j₁ j₂ hj ↦ hdisj (e.symm.injective.ne hj)⟩
  · rw [hcover, hred]
    ext x
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, hx⟩
      exact ⟨e ⟨S, hS⟩, by simpa using hx⟩
    · rintro ⟨j, hx⟩
      exact ⟨(e.symm j).1, (e.symm j).2, hx⟩
  · obtain ⟨i, hi, hS⟩ := (e.symm j).1.2
    exact ⟨i, cell_sub _ i hi hS⟩
  · refine ⟨(e.symm j).2, ?_⟩
    rw [(cell_poly _).convex.closure_interior_eq_closure_of_nonempty_interior (e.symm j).2,
      (cell_poly _).isClosed.closure_eq]

end Unions

/-! ## Definition 2.47 -/

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Definition 2.47(b)**: the Chapter 10 notion `IsPiecewiseLinear f` says
exactly that `f` is finite on `dom f` and piecewise linear there as a mapping
into `ℝ` in the sense of 2.47(a) (Chapter 12 `IsPiecewiseLinearOn`). -/
theorem isPiecewiseLinear_iff (f : E → EReal) :
    IsPiecewiseLinear f ↔ (∀ x ∈ effectiveDomain f, f x ≠ ⊥) ∧
      IsPiecewiseLinearOn (fun x ↦ (f x).toReal) (effectiveDomain f) := by
  constructor
  · rintro ⟨m, C, a, b, hC, hdom, hf⟩
    refine ⟨fun x hx ↦ ?_, ⟨m, C, fun i ↦ innerSL ℝ (a i), b, hC, hdom, fun i x hx ↦ ?_⟩⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hdom ▸ hx)
      rw [hf i x hi]
      exact EReal.coe_ne_bot _
    · change (f x).toReal = _
      rw [hf i x hx, EReal.toReal_coe]
      simp
  · rintro ⟨hbot, m, C, A, b, hC, hdom, hf⟩
    refine ⟨m, C, fun i ↦ (InnerProductSpace.toDual ℝ E).symm (A i), b, hC, hdom,
      fun i x hx ↦ ?_⟩
    have hxd : x ∈ effectiveDomain f := hdom ▸ mem_iUnion.mpr ⟨i, hx⟩
    rw [InnerProductSpace.toDual_symm_apply, ← hf i x hx]
    exact (EReal.coe_toReal (ne_of_lt hxd) (hbot x hxd)).symm

end Definitions

/-! ## Theorem 2.49 -/

section Epigraphs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The representation of Theorem 2.49: `f = max {l₁, …, l_p}` on a polyhedral
set `D` with affine `lᵢ(x) = ⟪aᵢ, x⟫ - βᵢ`, and `f = ∞` off `D`; for `p = 0` the
maximum is `-∞`. -/
def HasMaxAffineRepresentation (f : E → EReal) : Prop :=
  ∃ (D : Set E) (p : ℕ) (a : Fin p → E) (β : Fin p → ℝ), IsPolyhedral D ∧
    (∀ x ∈ D, f x = ⨆ i, ((⟪a i, x⟫_ℝ - β i : ℝ) : EReal)) ∧ ∀ x ∉ D, f x = ⊤

theorem ereal_eq_of_forall_le_coe_iff {u v : EReal} (h : ∀ α : ℝ, u ≤ α ↔ v ≤ α) : u = v := by
  apply le_antisymm
  · exact EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ (h z).mpr hz.le
  · exact EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ (h z).mp hz.le

theorem eq_top_of_forall_not_le_coe {u : EReal} (h : ∀ α : ℝ, ¬u ≤ α) : u = ⊤ := by
  by_contra hne
  obtain ⟨α, hα, -⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hne)
  exact h α hα.le

omit [FiniteDimensional ℝ E] in
/-- A finite polyhedral description of `E × ℝ` by continuous linear functionals
`(x, α) ↦ c(x) + α η`. -/
theorem prod_apply_decomp (A : (E × ℝ) →L[ℝ] ℝ) (x : E) (α : ℝ) :
    A (x, α) = A.comp (ContinuousLinearMap.inl ℝ E ℝ) x + α * A (0, 1) := by
  have : (x, α) = (x, 0) + α • ((0 : E), (1 : ℝ)) := by simp
  rw [this, map_add, map_smul, smul_eq_mul]
  simp

/-- **Theorem 2.49**: `epi f` is polyhedral if and only if `f` has the
representation `max {l₁, …, l_p}` on a polyhedral set and `∞` elsewhere. -/
theorem isPolyhedral_epigraph_iff (f : E → EReal) :
    IsPolyhedral (epigraph f) ↔ HasMaxAffineRepresentation f := by
  classical
  constructor
  · intro hP
    rcases (epigraph f).eq_empty_or_nonempty with hempty | ⟨⟨x₁, α₁⟩, h₁⟩
    · refine ⟨∅, 0, Fin.elim0, Fin.elim0, IsPolyhedral.empty, by simp, fun x _ ↦ ?_⟩
      refine eq_top_of_forall_not_le_coe fun α hα ↦ ?_
      have : (x, α) ∈ epigraph f := (mem_epigraph_iff f x α).mpr hα
      rw [hempty] at this
      exact this
    obtain ⟨m, A, γ, hAγ⟩ := (isHPolyhedral_iff_isPolyhedral.mpr hP)
    have hmem : ∀ x α, (x, α) ∈ epigraph f ↔ ∀ k, A k (x, α) ≤ γ k := by
      intro x α
      rw [hAγ]
      rfl
    set η : Fin m → ℝ := fun k ↦ A k (0, 1) with hη
    set c : Fin m → E →L[ℝ] ℝ := fun k ↦ (A k).comp (ContinuousLinearMap.inl ℝ E ℝ) with hc
    have hdec : ∀ k x α, A k (x, α) = c k x + α * η k := fun k x α ↦ prod_apply_decomp _ x α
    have hηle : ∀ k, η k ≤ 0 := by
      intro k
      by_contra hpos
      push_neg at hpos
      set t : ℝ := (γ k - A k (x₁, α₁)) / η k + 1
      have ht : (x₁, α₁ + |t|) ∈ epigraph f := by
        rw [mem_epigraph_iff] at h₁ ⊢
        exact h₁.trans (EReal.coe_le_coe_iff.mpr (by linarith [abs_nonneg t]))
      have h1 := (hmem _ _).mp ht k
      have h0 : A k (x₁, α₁) = c k x₁ + α₁ * η k := hdec k x₁ α₁
      rw [hdec] at h1
      have hlt : γ k < c k x₁ + (α₁ + |t|) * η k := by
        have htt : t ≤ |t| := le_abs_self t
        have hkey : (γ k - A k (x₁, α₁)) < |t| * η k := by
          have : (γ k - A k (x₁, α₁)) / η k < |t| := by linarith
          rwa [div_lt_iff₀ hpos] at this
        nlinarith
      linarith
    set Kn := {k : Fin m // η k < 0}
    set p := Fintype.card Kn
    let e : Kn ≃ Fin p := Fintype.equivFin Kn
    let a : Fin p → E := fun i ↦ (-η (e.symm i))⁻¹ • (InnerProductSpace.toDual ℝ E).symm
      (c (e.symm i))
    let β : Fin p → ℝ := fun i ↦ γ (e.symm i) / -η (e.symm i)
    have hl : ∀ i x, ⟪a i, x⟫_ℝ - β i = (c (e.symm i) x - γ (e.symm i)) / -η (e.symm i) := by
      intro i x
      simp only [a, β, real_inner_smul_left, InnerProductSpace.toDual_symm_apply]
      ring
    set D := {x : E | ∀ k, η k = 0 → c k x ≤ γ k}
    have hD : IsPolyhedral D := by
      apply IsHPolyhedral.isPolyhedral
      have : D = ⋂ k ∈ Finset.univ.filter (fun k ↦ η k = 0), {x : E | c k x ≤ γ k} := by
        ext x
        simp [D]
      rw [this]
      exact IsHPolyhedral.iInter_finset _ _ fun k _ ↦ IsHPolyhedral.halfspace (c k) (γ k)
    have hchar : ∀ x α, (x, α) ∈ epigraph f ↔
        x ∈ D ∧ ∀ i, ⟪a i, x⟫_ℝ - β i ≤ α := by
      intro x α
      rw [hmem]
      constructor
      · intro h
        refine ⟨fun k hk ↦ ?_, fun i ↦ ?_⟩
        · have := h k
          rw [hdec, hk, mul_zero, add_zero] at this
          exact this
        · rw [hl, div_le_iff₀ (neg_pos.mpr (e.symm i).2)]
          have := h (e.symm i)
          rw [hdec] at this
          linarith
      · rintro ⟨hxD, hi⟩ k
        rw [hdec]
        rcases (hηle k).eq_or_lt with h0 | hneg
        · rw [h0, mul_zero, add_zero]
          exact hxD k h0
        · have := hi (e ⟨k, hneg⟩)
          rw [hl, div_le_iff₀ (neg_pos.mpr (e.symm (e ⟨k, hneg⟩)).2)] at this
          simp only [Equiv.symm_apply_apply] at this
          linarith
    refine ⟨D, p, a, β, hD, fun x hxD ↦ ?_, fun x hxD ↦ ?_⟩
    · refine ereal_eq_of_forall_le_coe_iff fun α ↦ ?_
      rw [← mem_epigraph_iff, hchar, iSup_le_iff]
      simp only [EReal.coe_le_coe_iff, hxD, true_and]
    · refine eq_top_of_forall_not_le_coe fun α hα ↦ hxD ?_
      exact ((hchar x α).mp ((mem_epigraph_iff f x α).mpr hα)).1
  · rintro ⟨D, p, a, β, hD, hfD, hfout⟩
    have hepi : epigraph f = (Prod.fst ⁻¹' D) ∩
        ⋂ i ∈ (Finset.univ : Finset (Fin p)), {q : E × ℝ | ⟪a i, q.1⟫_ℝ - q.2 ≤ β i} := by
      ext ⟨x, α⟩
      simp only [mem_inter_iff, mem_preimage, mem_iInter, Finset.mem_univ, mem_setOf_eq,
        forall_const]
      constructor
      · intro h
        have hxD : x ∈ D := by
          by_contra hxD
          rw [mem_epigraph_iff, hfout x hxD] at h
          exact absurd h (by simp)
        rw [mem_epigraph_iff, hfD x hxD, iSup_le_iff] at h
        exact ⟨hxD, fun i ↦ by have := EReal.coe_le_coe_iff.mp (h i); linarith⟩
      · rintro ⟨hxD, hi⟩
        rw [mem_epigraph_iff, hfD x hxD, iSup_le_iff]
        exact fun i ↦ EReal.coe_le_coe_iff.mpr (by linarith [hi i])
    rw [hepi]
    have hfst : IsPolyhedral (Prod.fst ⁻¹' D : Set (E × ℝ)) := by
      simpa using hD.continuousLinear_preimage (ContinuousLinearMap.fst ℝ E ℝ)
    refine hfst.inter (IsHPolyhedral.isPolyhedral
      (IsHPolyhedral.iInter_finset _ _ fun i _ ↦ ?_))
    have := IsHPolyhedral.halfspace
      ((innerSL ℝ (a i)).comp (ContinuousLinearMap.fst ℝ E ℝ) - ContinuousLinearMap.snd ℝ E ℝ)
      (β i)
    simpa using this

/-- **Theorem 2.49**: every function of the form `max {l₁, …, l_p}` on a
polyhedral set and `∞` elsewhere is convex and lower semicontinuous. -/
theorem HasMaxAffineRepresentation.convex_lsc {f : E → EReal} (hf : HasMaxAffineRepresentation f) :
    IsConvexRelative univ f ∧ LowerSemicontinuous f := by
  have hP := (isPolyhedral_epigraph_iff f).mpr hf
  exact ⟨(isConvexRelative_univ_iff f).mpr hP.convex,
    lowerSemicontinuous_of_isClosed_epigraph_ereal f hP.isClosed⟩

/-- **Theorem 2.49**: a proper function is convex and piecewise linear if and only
if its epigraph is polyhedral. -/
theorem convex_isPiecewiseLinear_iff_isPolyhedral_epigraph {f : E → EReal} (hp : IsProper f) :
    (IsConvexRelative univ f ∧ IsPiecewiseLinear f) ↔ IsPolyhedral (epigraph f) := by
  classical
  constructor
  · rintro ⟨hc, m, C, a, b, hC, hdom, hf⟩
    have hepi : epigraph f = ⋃ i, ((Prod.fst ⁻¹' C i) ∩
        {q : E × ℝ | ⟪a i, q.1⟫_ℝ - q.2 ≤ -b i}) := by
      ext ⟨x, α⟩
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_setOf_eq]
      constructor
      · intro h
        have hxd : x ∈ effectiveDomain f :=
          lt_of_le_of_lt ((mem_epigraph_iff f x α).mp h) (EReal.coe_lt_top α)
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hdom ▸ hxd)
        refine ⟨i, hi, ?_⟩
        have := (mem_epigraph_iff f x α).mp h
        rw [hf i x hi, EReal.coe_le_coe_iff] at this
        linarith
      · rintro ⟨i, hi, hα⟩
        rw [mem_epigraph_iff, hf i x hi, EReal.coe_le_coe_iff]
        linarith
    rw [hepi]
    refine isPolyhedral_iUnion_of_convex_normed (fun i ↦ ?_) ?_
    swap
    · rw [← hepi]
      exact (isConvexRelative_univ_iff f).mp hc
    have hfst : IsPolyhedral (Prod.fst ⁻¹' C i : Set (E × ℝ)) := by
      simpa using (hC i).continuousLinear_preimage (ContinuousLinearMap.fst ℝ E ℝ)
    refine hfst.inter (IsHPolyhedral.isPolyhedral ?_)
    have := IsHPolyhedral.halfspace
      ((innerSL ℝ (a i)).comp (ContinuousLinearMap.fst ℝ E ℝ) - ContinuousLinearMap.snd ℝ E ℝ)
      (-b i)
    simpa using this
  · intro hP
    refine ⟨(HasMaxAffineRepresentation.convex_lsc ((isPolyhedral_epigraph_iff f).mp hP)).1, ?_⟩
    obtain ⟨D, p, a, β, hD, hfD, hfout⟩ := (isPolyhedral_epigraph_iff f).mp hP
    have hdomD : effectiveDomain f = D := by
      ext x
      constructor
      · intro hx
        by_contra hxD
        rw [effectiveDomain, mem_setOf_eq, hfout x hxD] at hx
        exact lt_irrefl _ hx
      · intro hxD
        by_contra hx
        have htop : f x = ⊤ := by simpa [effectiveDomain] using hx
        rw [hfD x hxD] at htop
        rcases isEmpty_or_nonempty (Fin p) with hp0 | hp0
        · rw [iSup_of_empty] at htop
          exact bot_ne_top htop
        · obtain ⟨i, hi⟩ := Finite.exists_max (fun i ↦ ⟪a i, x⟫_ℝ - β i)
          have : (⨆ i, ((⟪a i, x⟫_ℝ - β i : ℝ) : EReal)) ≤ ((⟪a i, x⟫_ℝ - β i : ℝ) : EReal) :=
            iSup_le fun j ↦ EReal.coe_le_coe_iff.mpr (hi j)
          rw [htop] at this
          exact not_le.mpr (EReal.coe_lt_top _) this
    have hpos : 0 < p := by
      obtain ⟨x, hx⟩ := hp.1
      have hxD : x ∈ D := hdomD ▸ hx
      by_contra h0
      have hp0 : p = 0 := by omega
      subst hp0
      have := hp.2 x
      rw [hfD x hxD, iSup_of_empty] at this
      exact lt_irrefl _ this
    haveI : Nonempty (Fin p) := ⟨⟨0, hpos⟩⟩
    set C : Fin p → Set E := fun k ↦ D ∩ ⋂ i ∈ (Finset.univ : Finset (Fin p)),
      {x | ⟪a i, x⟫_ℝ - β i ≤ ⟪a k, x⟫_ℝ - β k}
    have hCpoly : ∀ k, IsPolyhedral (C k) := by
      intro k
      refine hD.inter (IsHPolyhedral.isPolyhedral (IsHPolyhedral.iInter_finset _ _ fun i _ ↦ ?_))
      have := IsHPolyhedral.halfspace (innerSL ℝ (a i - a k)) (β i - β k)
      convert this using 1
      ext x
      simp only [mem_setOf_eq, innerSL_apply_apply, inner_sub_left]
      constructor <;> intro h <;> linarith
    refine ⟨p, C, a, fun k ↦ -β k, hCpoly, ?_, fun k x hx ↦ ?_⟩
    · rw [hdomD]
      ext x
      constructor
      · intro hxD
        obtain ⟨k, hk⟩ := Finite.exists_max (fun i ↦ ⟪a i, x⟫_ℝ - β i)
        exact mem_iUnion.mpr ⟨k, hxD, by simpa using fun i ↦ hk i⟩
      · intro hx
        obtain ⟨k, hk⟩ := mem_iUnion.mp hx
        exact hk.1
    · have hxD : x ∈ D := hx.1
      have hmax : ∀ i, ⟪a i, x⟫_ℝ - β i ≤ ⟪a k, x⟫_ℝ - β k := by
        have := hx.2
        simp only [mem_iInter, Finset.mem_univ, mem_setOf_eq, forall_const] at this
        exact this
      rw [hfD x hxD]
      apply le_antisymm
      · refine iSup_le fun i ↦ EReal.coe_le_coe_iff.mpr ?_
        linarith [hmax i]
      · refine le_trans (le_of_eq ?_) (le_iSup (fun i ↦ ((⟪a i, x⟫_ℝ - β i : ℝ) : EReal)) k)
        congr 1

end Epigraphs

end RW
