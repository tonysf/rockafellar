/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Preservation of measurability

Proposition 14.11 (unions, intersections, sums and products), Theorem 14.13 (composition of
mappings) and Corollary 14.14 (composition with measurable functions) of Rockafellar–Wets.

Countable intersections (14.11(a)) are proved directly by a compactness argument over rational
balls, for closed-valued mappings into any proper metric space; the book instead reduces the
binary case to sums of compact-valued truncations.
-/

import RockafellarWets.Chapter14.MeasurableSelections
import RockafellarWets.Chapter5.MappingOperations
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace RW

section Bases

variable {T F : Type*} [MeasurableSpace T] [TopologicalSpace F]

omit [MeasurableSpace T] [TopologicalSpace F] in
theorem svPreimage_sUnion (S : T → Set F) (W : Set (Set F)) :
    svPreimage S (⋃₀ W) = ⋃ w ∈ W, svPreimage S w := by
  ext t
  simp only [mem_svPreimage, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨s, hs, w, hw, hsw⟩
    exact ⟨w, hw, s, hs, hsw⟩
  · rintro ⟨w, hw, s, hs, hsw⟩
    exact ⟨s, hs, w, hw, hsw⟩

/-- Measurability can be tested on the members of a countable topological basis. -/
theorem svMeasurable_of_isTopologicalBasis {S : T → Set F} {B : Set (Set F)}
    (hB : IsTopologicalBasis B) (hBc : B.Countable)
    (h : ∀ W ∈ B, MeasurableSet (svPreimage S W)) : SvMeasurable S := by
  intro O hO
  rw [hB.open_eq_sUnion' hO, svPreimage_sUnion]
  exact MeasurableSet.biUnion (hBc.mono fun W hW ↦ hW.1) fun W hW ↦ h W hW.1

end Bases

section Proposition1411

variable {T : Type*} [MeasurableSpace T]

/-- **Proposition 14.11(b)**: countable unions of measurable mappings are measurable. -/
theorem SvMeasurable.iUnion {F J : Type*} [TopologicalSpace F] [Countable J]
    {S : J → T → Set F} (h : ∀ j, SvMeasurable (S j)) :
    SvMeasurable (fun t ↦ ⋃ j, S j t) := by
  intro O hO
  have : svPreimage (fun t ↦ ⋃ j, S j t) O = ⋃ j, svPreimage (S j) O := by
    ext t
    simp only [mem_svPreimage, mem_iUnion, iUnion_inter, nonempty_iUnion]
  rw [this]
  exact MeasurableSet.iUnion fun j ↦ h j O hO

theorem SvMeasurable.union {F : Type*} [TopologicalSpace F] {S₁ S₂ : T → Set F}
    (h₁ : SvMeasurable S₁) (h₂ : SvMeasurable S₂) :
    SvMeasurable (fun t ↦ S₁ t ∪ S₂ t) := by
  have := SvMeasurable.iUnion (J := Bool) (S := fun b t ↦ cond b (S₁ t) (S₂ t))
    (fun b ↦ by cases b <;> assumption)
  have heq : (fun t ↦ ⋃ b, cond b (S₁ t) (S₂ t)) = fun t ↦ S₁ t ∪ S₂ t :=
    funext fun t ↦ union_eq_iUnion.symm
  rwa [heq] at this

/-- **Proposition 14.11(d)**: the product `t ↦ S₁(t) × S₂(t)` of measurable mappings into
second-countable spaces is measurable. -/
theorem SvMeasurable.prod {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]
    [SecondCountableTopology F] [SecondCountableTopology G] {S₁ : T → Set F} {S₂ : T → Set G}
    (h₁ : SvMeasurable S₁) (h₂ : SvMeasurable S₂) :
    SvMeasurable (fun t ↦ S₁ t ×ˢ S₂ t) := by
  refine svMeasurable_of_isTopologicalBasis
    ((isBasis_countableBasis F).prod (isBasis_countableBasis G))
    ((countable_countableBasis F).image2 (countable_countableBasis G) _) ?_
  rintro _ ⟨U, hU, V, hV, rfl⟩
  have : svPreimage (fun t ↦ S₁ t ×ˢ S₂ t) (U ×ˢ V) = svPreimage S₁ U ∩ svPreimage S₂ V := by
    ext t
    simp only [mem_svPreimage, mem_inter_iff, prod_inter_prod, prod_nonempty_iff]
  rw [this]
  exact (h₁ U (isOpen_of_mem_countableBasis hU)).inter (h₂ V (isOpen_of_mem_countableBasis hV))

/-- **Proposition 14.11(d)**: finite products `t ↦ S₁(t) × ⋯ × S_r(t)` of measurable mappings
into second-countable spaces are measurable. -/
theorem SvMeasurable.pi {ι : Type*} [Finite ι] {F : ι → Type*} [∀ i, TopologicalSpace (F i)]
    [∀ i, SecondCountableTopology (F i)] {S : ∀ i, T → Set (F i)}
    (h : ∀ i, SvMeasurable (S i)) :
    SvMeasurable (fun t ↦ Set.pi univ fun i ↦ S i t) := by
  intro O hO
  haveI : ∀ i, Countable ↥(countableBasis (F i)) := fun i ↦
    (countable_countableBasis (F i)).to_subtype
  have key : O = ⋃ (W : ∀ i, ↥(countableBasis (F i)))
      (_ : Set.pi univ (fun i ↦ (W i : Set (F i))) ⊆ O), Set.pi univ fun i ↦ (W i : Set (F i)) := by
    apply Subset.antisymm
    · intro p hp
      obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.1 hO p hp
      have hW : ∀ i, ∃ w ∈ countableBasis (F i), p i ∈ w ∧ w ⊆ u i := fun i ↦
        (isBasis_countableBasis (F i)).exists_subset_of_mem_open (hu i).2 (hu i).1
      choose w hwB hpw hwu using hW
      refine mem_iUnion₂.2 ⟨fun i ↦ ⟨w i, hwB i⟩, ?_, ?_⟩
      · exact (Set.pi_mono fun i _ ↦ hwu i).trans hsub
      · exact fun i _ ↦ hpw i
    · exact iUnion₂_subset fun W hW ↦ hW
  have hbox : ∀ W : ∀ i, ↥(countableBasis (F i)),
      svPreimage (fun t ↦ Set.pi univ fun i ↦ S i t) (Set.pi univ fun i ↦ (W i : Set (F i))) =
        ⋂ i, svPreimage (S i) (W i) := by
    intro W
    ext t
    simp only [mem_svPreimage, mem_iInter, ← pi_inter_distrib, univ_pi_nonempty_iff]
  rw [key]
  have : svPreimage (fun t ↦ Set.pi univ fun i ↦ S i t) (⋃ (W : ∀ i, ↥(countableBasis (F i)))
      (_ : Set.pi univ (fun i ↦ (W i : Set (F i))) ⊆ O), Set.pi univ fun i ↦ (W i : Set (F i))) =
      ⋃ (W : ∀ i, ↥(countableBasis (F i)))
        (_ : Set.pi univ (fun i ↦ (W i : Set (F i))) ⊆ O), ⋂ i, svPreimage (S i) (W i) := by
    ext t
    simp only [mem_svPreimage, mem_iUnion, inter_iUnion, nonempty_iUnion, exists_prop]
    constructor
    · rintro ⟨W, hW, hne⟩
      refine ⟨W, hW, ?_⟩
      have := hbox W
      rw [Set.ext_iff] at this
      exact (this t).1 hne
    · rintro ⟨W, hW, hmem⟩
      refine ⟨W, hW, ?_⟩
      have := hbox W
      rw [Set.ext_iff] at this
      exact (this t).2 hmem
  rw [this]
  exact MeasurableSet.iUnion fun W ↦ MeasurableSet.iUnion fun _ ↦
    MeasurableSet.iInter fun i ↦ h i _ (isOpen_of_mem_countableBasis (W i).2)

/-- Images of measurable mappings under continuous single-valued maps are measurable. -/
theorem SvMeasurable.image {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]
    {S : T → Set F} (hS : SvMeasurable S) {f : F → G} (hf : Continuous f) :
    SvMeasurable (fun t ↦ f '' S t) := by
  intro O hO
  have : svPreimage (fun t ↦ f '' S t) O = svPreimage S (f ⁻¹' O) := by
    ext t
    simp only [mem_svPreimage]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxO⟩
      exact ⟨x, hx, hxO⟩
    · rintro ⟨x, hx, hxO⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, hxO⟩
  rw [this]
  exact hS _ (hO.preimage hf)

/-- **Proposition 14.11(c)**: finite linear combinations `t ↦ ∑ λⱼ Sⱼ(t)` of measurable
mappings are measurable, for arbitrary real coefficients. -/
theorem SvMeasurable.finsetSum {J F : Type*} [Fintype J] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F] {S : J → T → Set F} (h : ∀ j, SvMeasurable (S j)) (lam : J → ℝ) :
    SvMeasurable (fun t ↦ ∑ j, lam j • S j t) := by
  have heq : (fun t ↦ ∑ j, lam j • S j t) =
      fun t ↦ (fun x : J → F ↦ ∑ j, lam j • x j) '' Set.pi univ fun j ↦ S j t := by
    funext t
    ext x
    rw [Set.mem_finset_sum]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : ∀ j, ∃ y ∈ S j t, lam j • y = g j := fun j ↦
        Set.mem_smul_set.1 (hg (Finset.mem_univ j))
      choose y hy hyg using hg'
      exact ⟨y, fun j _ ↦ hy j, by simp only [hyg]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨fun j ↦ lam j • y j, fun {j} _ ↦ Set.smul_mem_smul_set (hy j (mem_univ j)), rfl⟩
  rw [heq]
  exact (SvMeasurable.pi h).image (continuous_finset_sum _ fun j _ ↦
    (continuous_apply j).const_smul (lam j))

/-- **Proposition 14.11(c)**, binary sums. -/
theorem SvMeasurable.add {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {S₁ S₂ : T → Set F} (h₁ : SvMeasurable S₁) (h₂ : SvMeasurable S₂) :
    SvMeasurable (fun t ↦ S₁ t + S₂ t) := by
  have heq : (fun t ↦ S₁ t + S₂ t) = fun t ↦ (fun p : F × F ↦ p.1 + p.2) '' (S₁ t ×ˢ S₂ t) := by
    funext t
    exact (image_prod (· + ·)).symm
  rw [heq]
  exact (h₁.prod h₂).image continuous_add

/-- **Proposition 14.11(c)**, scalar multiples. -/
theorem SvMeasurable.const_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : T → Set F} (hS : SvMeasurable S) (lam : ℝ) :
    SvMeasurable (fun t ↦ lam • S t) := by
  have heq : (fun t ↦ lam • S t) = fun t ↦ (fun x : F ↦ lam • x) '' S t := by
    funext t
    rfl
  rw [heq]
  exact hS.image (continuous_const_smul lam)

variable {F : Type*} [MetricSpace F] [ProperSpace F]

/-- The compact-set inverse images of a countable intersection of closed-valued measurable
mappings are measurable. -/
theorem measurableSet_svPreimage_iInter_nat {S : ℕ → T → Set F}
    (h : ∀ j, SvMeasurable (S j)) (hc : ∀ j t, IsClosed (S j t)) {C : Set F} (hC : IsCompact C) :
    MeasurableSet (svPreimage (fun t ↦ ⋂ j, S j t) C) := by
  rcases isEmpty_or_nonempty F with hF | hF
  · have : svPreimage (fun t ↦ ⋂ j, S j t) C = ∅ := by
      ext t
      simp only [mem_svPreimage, mem_empty_iff_false, iff_false]
      rintro ⟨s, -⟩
      exact hF.elim s
    rw [this]
    exact MeasurableSet.empty
  set d := denseSeq F
  have hd : DenseRange d := denseRange_denseSeq F
  set r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hr
  have hrpos : ∀ n, 0 < r n := fun n ↦ by positivity
  have key : svPreimage (fun t ↦ ⋂ j, S j t) C = ⋂ n : ℕ, ⋃ i : ℕ,
      ⋂ j ∈ Finset.range (n + 1), svPreimage (S j) (closedBall (d i) (r n) ∩ C) := by
    ext t
    simp only [mem_iInter, mem_iUnion, mem_svPreimage]
    constructor
    · rintro ⟨x, hx, hxC⟩ n
      obtain ⟨i, hi⟩ := hd.exists_dist_lt x (hrpos n)
      exact ⟨i, fun j _ ↦ ⟨x, mem_iInter.1 hx j, hi.le, hxC⟩⟩
    · intro H
      choose i hi using H
      have hpt : ∀ n j, ∃ a : F, j ≤ n → a ∈ S j t ∩ (closedBall (d (i n)) (r n) ∩ C) := by
        intro n j
        by_cases hj : j ≤ n
        · obtain ⟨a, ha⟩ := hi n j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
          exact ⟨a, fun _ ↦ ha⟩
        · exact ⟨d 0, fun h ↦ absurd h hj⟩
      choose a ha using hpt
      have hcC : ∀ n, a n 0 ∈ C := fun n ↦ (ha n 0 (Nat.zero_le n)).2.2
      obtain ⟨c, hcC', φ, hφ, hlim⟩ := hC.tendsto_subseq hcC
      refine ⟨c, mem_iInter.2 fun j ↦ ?_, hcC'⟩
      refine (hc j t).mem_of_tendsto (f := fun m ↦ a (φ m) j) (b := atTop) ?_ ?_
      · rw [tendsto_iff_dist_tendsto_zero]
        have hlim' := tendsto_iff_dist_tendsto_zero.1 hlim
        have hr0 : Tendsto (fun m ↦ 2 * r (φ m)) atTop (𝓝 0) := by
          have : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          simpa using (this.comp hφ.tendsto_atTop).const_mul 2
        refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ (by
          simpa using hr0.add hlim')
        filter_upwards [eventually_ge_atTop j] with m hm
        have hjm : j ≤ φ m := hm.trans (hφ.id_le m)
        have h1 : dist (a (φ m) j) (d (i (φ m))) ≤ r (φ m) := (ha (φ m) j hjm).2.1
        have h2 : dist (a (φ m) 0) (d (i (φ m))) ≤ r (φ m) := (ha (φ m) 0 (Nat.zero_le _)).2.1
        calc dist (a (φ m) j) c ≤ dist (a (φ m) j) (a (φ m) 0) + dist (a (φ m) 0) c :=
              dist_triangle _ _ _
          _ ≤ (dist (a (φ m) j) (d (i (φ m))) + dist (a (φ m) 0) (d (i (φ m)))) +
                dist (a (φ m) 0) c := by
              gcongr
              exact dist_triangle_right _ _ _
          _ ≤ 2 * r (φ m) + dist (a (φ m) 0) c := by linarith
          _ = 2 * r (φ m) + dist ((a ∘ φ) m 0) c := rfl
      · filter_upwards [eventually_ge_atTop j] with m hm
        exact (ha (φ m) j (hm.trans (hφ.id_le m))).1
  rw [key]
  refine MeasurableSet.iInter fun n ↦ MeasurableSet.iUnion fun i ↦ ?_
  exact Finset.measurableSet_biInter _ fun j _ ↦
    (h j).measurableSet_svPreimage_of_isCompact (hc j)
      ((isCompact_closedBall _ _).inter_right hC.isClosed)

/-- **Proposition 14.11(a)**: countable intersections of closed-valued measurable mappings are
measurable (into a proper metric space). -/
theorem SvMeasurable.iInter {J : Type*} [Countable J] {S : J → T → Set F}
    (h : ∀ j, SvMeasurable (S j)) (hc : ∀ j t, IsClosed (S j t)) :
    SvMeasurable (fun t ↦ ⋂ j, S j t) := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · simp only [iInter_of_empty]
    exact svMeasurable_const univ
  obtain ⟨e, he⟩ := exists_surjective_nat J
  have heq : (fun t ↦ ⋂ j, S j t) = fun t ↦ ⋂ n, S (e n) t := by
    funext t
    ext x
    simp only [mem_iInter]
    exact ⟨fun hx n ↦ hx (e n), fun hx j ↦ by obtain ⟨n, rfl⟩ := he j; exact hx n⟩
  rw [heq]
  exact svMeasurable_of_measurableSet_svPreimage_isCompact fun K hK ↦
    measurableSet_svPreimage_iInter_nat (fun n ↦ h (e n)) (fun n ↦ hc (e n)) hK

theorem SvMeasurable.inter {S₁ S₂ : T → Set F} (h₁ : SvMeasurable S₁) (h₂ : SvMeasurable S₂)
    (hc₁ : ∀ t, IsClosed (S₁ t)) (hc₂ : ∀ t, IsClosed (S₂ t)) :
    SvMeasurable (fun t ↦ S₁ t ∩ S₂ t) := by
  have := SvMeasurable.iInter (J := Bool) (S := fun b t ↦ cond b (S₁ t) (S₂ t))
    (fun b ↦ by cases b <;> assumption) (fun b ↦ by cases b <;> assumption)
  have heq : (fun t ↦ ⋂ b, cond b (S₁ t) (S₂ t)) = fun t ↦ S₁ t ∩ S₂ t :=
    funext fun t ↦ inter_eq_iInter.symm
  rwa [heq] at this

/-- **Proposition 14.11 (unions, intersections, sums and products)**, assembled:
(a) countable intersections of closed-valued measurable mappings, (b) countable unions,
(c) finite linear combinations with arbitrary real coefficients and (d) finite products are
measurable. -/
theorem unions_intersections_sums_and_products {J : Type*} [Countable J] :
    (∀ {S : J → T → Set F}, (∀ j, SvMeasurable (S j)) → (∀ j t, IsClosed (S j t)) →
        SvMeasurable (fun t ↦ ⋂ j, S j t)) ∧
      (∀ {G : Type*} [TopologicalSpace G] {S : J → T → Set G}, (∀ j, SvMeasurable (S j)) →
        SvMeasurable (fun t ↦ ⋃ j, S j t)) ∧
      (∀ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [SecondCountableTopology G]
        [Fintype J] {S : J → T → Set G}, (∀ j, SvMeasurable (S j)) → ∀ lam : J → ℝ,
          SvMeasurable (fun t ↦ ∑ j, lam j • S j t)) ∧
      (∀ {G : J → Type*} [∀ j, TopologicalSpace (G j)] [∀ j, SecondCountableTopology (G j)]
        [Finite J] {S : ∀ j, T → Set (G j)}, (∀ j, SvMeasurable (S j)) →
          SvMeasurable (fun t ↦ Set.pi univ fun j ↦ S j t)) :=
  ⟨fun h hc ↦ SvMeasurable.iInter h hc, fun h ↦ SvMeasurable.iUnion h,
    fun h lam ↦ SvMeasurable.finsetSum h lam, fun h ↦ SvMeasurable.pi h⟩

end Proposition1411

end RW
