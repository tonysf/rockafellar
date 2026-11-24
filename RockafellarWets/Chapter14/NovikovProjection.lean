/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Novikov's projection theorem

The corrected Theorem 14.8 and Corollary 14.34 of Rockafellar–Wets assume that the σ-field is
complete for an s-finite measure, because the projection of a Borel set need not be Borel.  For
closed sections in `ℝⁿ` and a standard Borel parameter space no measure is needed: by Novikov's
theorem, the projection of a Borel set with compact sections is Borel.  We prove it, and its
variant for closed sections in a σ-compact target, along the classical route through separation
theorems (Kechris, *Classical Descriptive Set Theory*, Section 28):

* `measurablySeparableSeq_of_analyticSet` (**Novikov's separation theorem**): a sequence of
  analytic sets with empty intersection has Borel supersets with empty intersection.  The proof is
  Lusin's (Mathlib's `measurablySeparable_range_of_disjoint`), with all members refined along a
  single cylinder of `ℕ → ℕ`, read through the pairing `ℕ × ℕ ≃ ℕ`.
* `exists_measurableSet_eq_iUnion_prod_of_isOpen_sections` (**Kunugui–Novikov**): a Borel subset
  of `X × Y` with open sections is a countable union of Borel rectangles `Bₙ × Vₙ` over a
  countable basis `(Vₙ)` of `Y`.
* `measurableSet_image_fst_of_isClosed_sections_of_isCompact`: if the sections are closed subsets
  of a compact set `K`, then `x` is not in the projection iff finitely many `Vₙ` with `x ∈ Bₙ`
  (for the complement) cover `K`, a Borel condition on `x`.
* `measurableSet_image_fst_of_isCompact_sections` (**Novikov's theorem**): compact sections in any
  Polish target, through a continuous injection of the target into the cube `[0, 1]^ℕ`
  (`exists_continuous_injective_unitCube`) and the Lusin–Souslin theorem.
* `measurableSet_image_fst_of_isClosed_sections`: closed sections in a σ-compact Polish target
  such as `ℝⁿ`.

The source `X` is any standard Borel space (e.g. a Polish space with its Borel σ-field).
-/

import Mathlib.MeasureTheory.Constructions.Polish.Basic

open Set Function Filter Topology MeasureTheory PiNat TopologicalSpace

noncomputable section

namespace RW

section MeasurablySeparableSeq

variable {α : Type*} [MeasurableSpace α]

/-- A sequence of sets is measurably separable if it has measurable supersets with empty
intersection (for two sets this is Mathlib's `MeasurablySeparable`). -/
def MeasurablySeparableSeq (s : ℕ → Set α) : Prop :=
  ∃ u : ℕ → Set α, (∀ n, s n ⊆ u n) ∧ (∀ n, MeasurableSet (u n)) ∧ ⋂ n, u n = ∅

theorem MeasurablySeparableSeq.mono {s t : ℕ → Set α} (ht : MeasurablySeparableSeq t)
    (hst : ∀ n, s n ⊆ t n) : MeasurablySeparableSeq s := by
  obtain ⟨u, htu, hu, hempty⟩ := ht
  exact ⟨u, fun n ↦ (hst n).trans (htu n), hu, hempty⟩

/-- Two members of the sequence inside disjoint measurable sets separate the sequence. -/
theorem measurablySeparableSeq_of_disjoint {s : ℕ → Set α} {i j : ℕ} {u v : Set α}
    (hu : MeasurableSet u) (hv : MeasurableSet v) (huv : Disjoint u v) (hsu : s i ⊆ u)
    (hsv : s j ⊆ v) : MeasurablySeparableSeq s := by
  classical
  refine ⟨fun n ↦ (if n = i then u else univ) ∩ (if n = j then v else univ), fun n ↦ ?_,
    fun n ↦ ?_, ?_⟩
  · refine subset_inter ?_ ?_
    · split_ifs with h
      · subst h
        exact hsu
      · exact subset_univ _
    · split_ifs with h
      · subst h
        exact hsv
      · exact subset_univ _
  · refine MeasurableSet.inter ?_ ?_
    · split_ifs
      · exact hu
      · exact MeasurableSet.univ
    · split_ifs
      · exact hv
      · exact MeasurableSet.univ
  · refine eq_empty_of_forall_notMem fun x hx ↦ ?_
    have hi := mem_iInter.1 hx i
    have hj := mem_iInter.1 hx j
    rw [if_pos rfl] at hi
    rw [if_pos rfl] at hj
    exact disjoint_left.1 huv hi.1 hj.2

/-- If one member of the sequence is covered by countably many sets `c m`, and the sequence is
measurably separable with that member replaced by any `c m`, then it is measurably separable. -/
theorem measurablySeparableSeq_of_subset_iUnion {s : ℕ → Set α} (k : ℕ) {c : ℕ → Set α}
    (hc : s k ⊆ ⋃ m, c m) (h : ∀ m, MeasurablySeparableSeq (update s k (c m))) :
    MeasurablySeparableSeq s := by
  classical
  choose u hsu hu hempty using h
  refine ⟨fun n ↦ if n = k then ⋃ m, u m k else ⋂ m, u m n, fun n ↦ ?_, fun n ↦ ?_, ?_⟩
  · dsimp only
    split_ifs with hn
    · subst hn
      refine hc.trans (iUnion_mono fun m ↦ ?_)
      have := hsu m n
      rwa [update_self] at this
    · refine subset_iInter fun m ↦ ?_
      have := hsu m n
      rwa [update_of_ne hn] at this
  · dsimp only
    split_ifs
    · exact MeasurableSet.iUnion fun m ↦ hu m k
    · exact MeasurableSet.iInter fun m ↦ hu m n
  · refine eq_empty_of_forall_notMem fun x hx ↦ ?_
    have hk := mem_iInter.1 hx k
    rw [if_pos rfl] at hk
    obtain ⟨m, hm⟩ := mem_iUnion.1 hk
    have hx' : x ∈ ⋂ n, u m n := mem_iInter.2 fun n ↦ by
      by_cases hn : n = k
      · subst hn
        exact hm
      · have := mem_iInter.1 hx n
        rw [if_neg hn] at this
        exact mem_iInter.1 this m
    rw [hempty m] at hx'
    exact hx'

end MeasurablySeparableSeq

namespace NovikovSeparation

/-- The sequences `s` with `s i = z ⟨n, i⟩` whenever `⟨n, i⟩ < d`: the `n`-th coordinate block of
the cylinder of length `d` around `z` in `ℕ → ℕ`, read through the pairing `ℕ × ℕ ≃ ℕ`. -/
def cell (n : ℕ) (z : ℕ → ℕ) (d : ℕ) : Set (ℕ → ℕ) :=
  {s | ∀ i, Nat.pair n i < d → s i = z (Nat.pair n i)}

theorem cell_zero (n : ℕ) (z : ℕ → ℕ) : cell n z 0 = univ := by
  ext s
  simp [cell]

theorem cell_congr {n d : ℕ} {z z' : ℕ → ℕ} (h : ∀ k < d, z k = z' k) :
    cell n z d = cell n z' d := by
  ext s
  simp only [cell, mem_setOf_eq]
  exact forall_congr' fun i ↦ imp_congr_right fun hi ↦ by rw [h _ hi]

theorem cell_anti (n : ℕ) (z : ℕ → ℕ) {d d' : ℕ} (h : d ≤ d') : cell n z d' ⊆ cell n z d :=
  fun _ hs i hi ↦ hs i (lt_of_lt_of_le hi h)

/-- Extending the cylinder by one coordinate only affects the block that owns that coordinate. -/
theorem cell_update_of_ne {n d m : ℕ} {z : ℕ → ℕ} (hn : n ≠ (Nat.unpair d).1) :
    cell n (update z d m) (d + 1) = cell n z d := by
  have hne : ∀ i, Nat.pair n i ≠ d := fun i h ↦ hn (by rw [← h, Nat.unpair_pair])
  ext s
  simp only [cell, mem_setOf_eq]
  constructor
  · intro hs i hi
    have := hs i (hi.trans (Nat.lt_succ_self d))
    rwa [update_of_ne (hne i)] at this
  · intro hs i hi
    rw [update_of_ne (hne i)]
    exact hs i (lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) (hne i))

/-- The block that owns the coordinate `d` is the union of its refinements. -/
theorem cell_subset_iUnion (d : ℕ) (z : ℕ → ℕ) :
    cell (Nat.unpair d).1 z d ⊆ ⋃ m, cell (Nat.unpair d).1 (update z d m) (d + 1) := by
  intro s hs
  refine mem_iUnion.2 ⟨s (Nat.unpair d).2, fun i hi ↦ ?_⟩
  rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hlt | heq
  · rw [update_of_ne hlt.ne]
    exact hs i hlt
  · have hi' : i = (Nat.unpair d).2 := by
      have := congrArg (fun k ↦ (Nat.unpair k).2) heq
      simpa using this
    rw [heq, update_self, hi']

theorem cell_subset_cylinder (n N : ℕ) (z : ℕ → ℕ) :
    cell n z (Nat.pair n N) ⊆ cylinder (fun i ↦ z (Nat.pair n i)) N :=
  fun _ hs ↦ mem_cylinder_iff.2 fun i hi ↦ hs i (Nat.pair_lt_pair_right n hi)

variable {α : Type*} [MeasurableSpace α] {f : ℕ → (ℕ → ℕ) → α}

theorem exists_not_measurablySeparableSeq_succ {z : ℕ → ℕ} {d : ℕ}
    (h : ¬ MeasurablySeparableSeq fun n ↦ f n '' cell n z d) :
    ∃ m, ¬ MeasurablySeparableSeq fun n ↦ f n '' cell n (update z d m) (d + 1) := by
  by_contra hcon
  push_neg at hcon
  apply h
  refine measurablySeparableSeq_of_subset_iUnion (Nat.unpair d).1
    (c := fun m ↦ f (Nat.unpair d).1 '' cell (Nat.unpair d).1 (update z d m) (d + 1)) ?_
    fun m ↦ (hcon m).mono fun n ↦ ?_
  · rw [← image_iUnion]
    exact image_mono (cell_subset_iUnion d z)
  · by_cases hn : n = (Nat.unpair d).1
    · subst hn
      rw [update_self]
    · rw [update_of_ne hn, cell_update_of_ne hn]

theorem exists_cylinder_subset {X : Type*} [TopologicalSpace X] {g : (ℕ → ℕ) → X}
    (hg : Continuous g) {x : ℕ → ℕ} {w : Set X} (hw : IsOpen w) (hx : g x ∈ w) :
    ∃ N, cylinder x N ⊆ g ⁻¹' w := by
  obtain ⟨c, ⟨y, N, rfl⟩, hxc, hcw⟩ :=
    (isTopologicalBasis_cylinders (E := fun _ : ℕ ↦ ℕ)).exists_subset_of_mem_open
      (mem_preimage.2 hx) (hw.preimage hg)
  refine ⟨N, ?_⟩
  rw [mem_cylinder_iff_eq.1 hxc]
  exact hcw

variable [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α]

/-- Novikov's separation theorem for ranges of continuous maps on `ℕ → ℕ`.  If the ranges are not
measurably separable, refining one block of a cylinder at a time keeps the images inseparable;
the limit points `f n (σ n)` of the blocks cannot all coincide, and two different ones have
disjoint open neighborhoods that already separate the images of long enough blocks. -/
theorem measurablySeparableSeq_range (hf : ∀ n, Continuous (f n))
    (h : ⋂ n, range (f n) = ∅) : MeasurablySeparableSeq fun n ↦ range (f n) := by
  by_contra hns
  let A := {p : ℕ × (ℕ → ℕ) // ¬ MeasurablySeparableSeq fun n ↦ f n '' cell n p.2 p.1}
  have hstep : ∀ p : A, ∃ q : A, q.1.1 = p.1.1 + 1 ∧ ∀ k < p.1.1, q.1.2 k = p.1.2 k := by
    rintro ⟨⟨d, z⟩, hp⟩
    obtain ⟨m, hm⟩ := exists_not_measurablySeparableSeq_succ hp
    exact ⟨⟨⟨d + 1, update z d m⟩, hm⟩, rfl, fun k hk ↦ update_of_ne hk.ne _ _⟩
  choose F hFd hFz using hstep
  let p0 : A := ⟨⟨0, fun _ ↦ 0⟩, by simpa [cell_zero, image_univ] using hns⟩
  let p : ℕ → A := fun n ↦ F^[n] p0
  have prec : ∀ n, p (n + 1) = F (p n) := fun n ↦ by
    simp only [p, iterate_succ', Function.comp]
  have pd : ∀ n, (p n).1.1 = n := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n IH => rw [prec, hFd, IH]
  have Iz : ∀ k n, k + 1 ≤ n → (p n).1.2 k = (p (k + 1)).1.2 k := by
    intro k
    apply Nat.le_induction
    · rfl
    intro n hkn IH
    rw [prec, hFz (p n) k (by rw [pd]; exact hkn), IH]
  set z : ℕ → ℕ := fun k ↦ (p (k + 1)).1.2 k
  have M : ∀ d, ¬ MeasurablySeparableSeq fun n ↦ f n '' cell n z d := by
    intro d
    have hcell : ∀ n, cell n z d = cell n (p d).1.2 (p d).1.1 := by
      intro n
      rw [pd]
      exact cell_congr fun k hk ↦ (Iz k d hk).symm
    simpa only [hcell] using (p d).2
  set σ : ℕ → ℕ → ℕ := fun n i ↦ z (Nat.pair n i)
  obtain ⟨a, b, hab⟩ : ∃ a b, f a (σ a) ≠ f b (σ b) := by
    by_contra hcon
    push_neg at hcon
    have : f 0 (σ 0) ∈ ⋂ n, range (f n) := mem_iInter.2 fun n ↦ ⟨σ n, hcon n 0⟩
    rw [h] at this
    exact this
  obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := t2_separation hab
  obtain ⟨Na, hNa⟩ := exists_cylinder_subset (hf a) hu hau
  obtain ⟨Nb, hNb⟩ := exists_cylinder_subset (hf b) hv hbv
  apply M (max (Nat.pair a Na) (Nat.pair b Nb))
  refine measurablySeparableSeq_of_disjoint (i := a) (j := b) hu.measurableSet hv.measurableSet
    huv ?_ ?_
  · rw [image_subset_iff]
    exact (cell_anti a z (le_max_left _ _)).trans ((cell_subset_cylinder a Na z).trans hNa)
  · rw [image_subset_iff]
    exact (cell_anti b z (le_max_right _ _)).trans ((cell_subset_cylinder b Nb z).trans hNb)

end NovikovSeparation

/-- **Novikov's separation theorem**: in a Hausdorff space whose open sets are measurable, a
sequence of analytic sets with empty intersection has measurable supersets with empty intersection
(for two sets this is Lusin's separation theorem `AnalyticSet.measurablySeparable`). -/
theorem measurablySeparableSeq_of_analyticSet {α : Type*} [TopologicalSpace α] [T2Space α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {s : ℕ → Set α} (hs : ∀ n, AnalyticSet (s n))
    (h : ⋂ n, s n = ∅) : MeasurablySeparableSeq s := by
  classical
  by_cases he : ∃ n, s n = ∅
  · obtain ⟨k, hk⟩ := he
    refine ⟨fun n ↦ if n = k then ∅ else univ, fun n ↦ ?_, fun n ↦ ?_, ?_⟩
    · dsimp only
      split_ifs with hn
      · subst hn
        rw [hk]
      · exact subset_univ _
    · dsimp only
      split_ifs
      · exact MeasurableSet.empty
      · exact MeasurableSet.univ
    · refine eq_empty_of_forall_notMem fun x hx ↦ ?_
      have := mem_iInter.1 hx k
      rw [if_pos rfl] at this
      exact this
  · push_neg at he
    have hg : ∀ n, ∃ g : (ℕ → ℕ) → α, Continuous g ∧ range g = s n := fun n ↦ by
      have hsn := hs n
      rw [AnalyticSet] at hsn
      rcases hsn with h0 | hg
      · exact absurd h0 (he n).ne_empty
      · exact hg
    choose g hgc hgs using hg
    have := NovikovSeparation.measurablySeparableSeq_range hgc (by simp_rw [hgs]; exact h)
    simpa only [hgs] using this

/-- A Polish space admits a continuous injection into the compact cube `[0, 1]^ℕ ⊆ ℕ → ℝ`:
`y ↦ (min 1 (dist y (d n)))ₙ` for a compatible metric and a dense sequence `d`. -/
theorem exists_continuous_injective_unitCube (Y : Type*) [TopologicalSpace Y] [PolishSpace Y] :
    ∃ e : Y → ℕ → ℝ, Continuous e ∧ Injective e ∧ ∀ y n, e y n ∈ Icc (0 : ℝ) 1 := by
  letI := upgradeIsCompletelyMetrizable Y
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨fun _ _ ↦ 0, continuous_const, fun y ↦ hY.elim y, fun y ↦ hY.elim y⟩
  set d := denseSeq Y
  refine ⟨fun y n ↦ min 1 (dist y (d n)),
    continuous_pi fun n ↦ continuous_const.min (continuous_id.dist continuous_const), ?_,
    fun y n ↦ ⟨le_min zero_le_one dist_nonneg, min_le_left _ _⟩⟩
  intro y y' h
  by_contra hne
  have hpos : 0 < dist y y' := dist_pos.2 hne
  set δ := min (dist y y' / 3) (1 / 3)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ3 : δ ≤ dist y y' / 3 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 3 := min_le_right _ _
  obtain ⟨n, hn⟩ := (denseRange_denseSeq Y).exists_dist_lt y hδ
  have h1 := congrFun h n
  simp only at h1
  have hy : min 1 (dist y (d n)) = dist y (d n) := min_eq_right (by linarith)
  have hy' : dist y y' ≤ dist y (d n) + dist y' (d n) := dist_triangle_right y y' (d n)
  have hlt : min 1 (dist y (d n)) < min 1 (dist y' (d n)) := by
    rw [hy]
    exact lt_min (by linarith) (by linarith)
  exact hlt.ne h1

section Projection

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [TopologicalSpace Y]
  [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Kunugui–Novikov theorem**: on a standard Borel space `X`, a Borel subset `A` of `X × Y` with
open sections is a countable union of Borel rectangles `B n × V n`, for any countable family `V`
of open sets with the basis property.  With `D n` the (analytic) set of `x` whose section misses
part of `V n`, the sequence `A, D 0 × Y ∪ X × (V 0)ᶜ, …` has empty intersection; Novikov's
separation theorem gives Borel supersets with empty intersection, and Lusin's separation theorem
turns the `n`-th superset into a rectangle `(B n)ᶜ × Y ∪ X × (V n)ᶜ`. -/
theorem exists_measurableSet_eq_iUnion_prod_of_isOpen_sections {V : ℕ → Set Y}
    (hVo : ∀ n, IsOpen (V n)) (hV : ∀ y W, IsOpen W → y ∈ W → ∃ n, y ∈ V n ∧ V n ⊆ W)
    {A : Set (X × Y)} (hA : MeasurableSet A) (hAo : ∀ x, IsOpen (Prod.mk x ⁻¹' A)) :
    ∃ B : ℕ → Set X, (∀ n, MeasurableSet (B n)) ∧ A = ⋃ n, B n ×ˢ V n := by
  letI := upgradeStandardBorel X
  set D : ℕ → Set X := fun n ↦ Prod.fst '' ((univ ×ˢ V n) \ A)
  have hDa : ∀ n, AnalyticSet (D n) := fun n ↦
    ((MeasurableSet.univ.prod (hVo n).measurableSet).diff hA).analyticSet_image measurable_fst
  set P : ℕ → Set (X × Y) := fun n ↦ (Prod.fst ⁻¹' D n) ∪ (univ ×ˢ (V n)ᶜ)
  have hPa : ∀ n, AnalyticSet (P n) := fun n ↦ by
    have : P n = ⋃ b : Bool, cond b (Prod.fst ⁻¹' D n) (univ ×ˢ (V n)ᶜ) := union_eq_iUnion
    rw [this]
    refine AnalyticSet.iUnion fun b ↦ ?_
    cases b
    · exact (isClosed_univ.prod (hVo n).isClosed_compl).analyticSet
    · exact (hDa n).preimage continuous_fst
  set s : ℕ → Set (X × Y) := fun n ↦ Nat.casesOn n A P
  have hsa : ∀ n, AnalyticSet (s n) := fun n ↦ by
    cases n
    · exact hA.analyticSet
    · exact hPa _
  have hsi : ⋂ n, s n = ∅ := by
    refine eq_empty_of_forall_notMem fun p hp ↦ ?_
    have hpA : p ∈ A := mem_iInter.1 hp 0
    have hpP : ∀ n, p ∈ P n := fun n ↦ mem_iInter.1 hp (n + 1)
    obtain ⟨n, hpn, hnA⟩ := hV p.2 _ (hAo p.1) hpA
    rcases hpP n with hD' | hV'
    · obtain ⟨q, ⟨⟨-, hqV⟩, hqA⟩, hq⟩ := hD'
      exact hqA (hnA (show q.2 ∈ V n from hqV) |> fun h ↦ by rwa [← hq] at h)
    · exact hV'.2 hpn
  obtain ⟨u, hsu, hu, hempty⟩ := measurablySeparableSeq_of_analyticSet hsa hsi
  have hsep : ∀ n, MeasurablySeparable (D n) (Prod.fst '' (u (n + 1))ᶜ) := fun n ↦
    (hDa n).measurablySeparable ((hu (n + 1)).compl.analyticSet_image measurable_fst) <| by
      refine disjoint_left.2 fun x hxD hx ↦ ?_
      obtain ⟨⟨x', y⟩, hxy, rfl⟩ := hx
      exact hxy (hsu (n + 1) (Or.inl hxD))
  choose E hDE hEdisj hEm using hsep
  refine ⟨fun n ↦ (E n)ᶜ, fun n ↦ (hEm n).compl, ?_⟩
  ext ⟨x, y⟩
  simp only [mem_iUnion, mem_prod, mem_compl_iff]
  constructor
  · intro hxy
    by_contra hcon
    push_neg at hcon
    have hmem : (x, y) ∈ ⋂ n, u n := by
      refine mem_iInter.2 fun n ↦ ?_
      cases n with
      | zero => exact hsu 0 hxy
      | succ n =>
        by_cases hxE : x ∈ E n
        · by_contra hnot
          exact disjoint_left.1 (hEdisj n) ⟨(x, y), hnot, rfl⟩ hxE
        · exact hsu (n + 1) (Or.inr ⟨mem_univ _, hcon n hxE⟩)
    rw [hempty] at hmem
    exact hmem
  · rintro ⟨n, hxE, hyV⟩
    by_contra hxy
    exact hxE (hDE n ⟨(x, y), ⟨⟨mem_univ _, hyV⟩, hxy⟩, rfl⟩)

/-- **Novikov's theorem**, bounded form: on a standard Borel space `X`, the projection of a Borel
subset of `X × Y` whose sections are closed subsets of a fixed compact set `K` is Borel.  By
Kunugui–Novikov the complement is `⋃ n, B n × V n`, and `x` is outside the projection iff
finitely many `V n` with `x ∈ B n` cover `K`. -/
theorem measurableSet_image_fst_of_isClosed_sections_of_isCompact {K : Set Y} (hK : IsCompact K)
    {A : Set (X × Y)} (hA : MeasurableSet A) (hAK : A ⊆ univ ×ˢ K)
    (hAc : ∀ x, IsClosed (Prod.mk x ⁻¹' A)) : MeasurableSet (Prod.fst '' A) := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · have : A = ∅ := eq_empty_of_forall_notMem fun p _ ↦ hY.elim p.2
    rw [this, image_empty]
    exact MeasurableSet.empty
  obtain ⟨V, hVo, hV⟩ : ∃ V : ℕ → Set Y, (∀ n, IsOpen (V n)) ∧
      ∀ y W, IsOpen W → y ∈ W → ∃ n, y ∈ V n ∧ V n ⊆ W := by
    have hb := isBasis_countableBasis Y
    have hne : (countableBasis Y).Nonempty := by
      obtain ⟨y⟩ := hY
      obtain ⟨W, hW, -, -⟩ := hb.exists_subset_of_mem_open (mem_univ y) isOpen_univ
      exact ⟨W, hW⟩
    obtain ⟨V, hVeq⟩ := (countable_countableBasis Y).exists_eq_range hne
    refine ⟨V, fun n ↦ hb.isOpen (hVeq ▸ mem_range_self n), fun y W hW hy ↦ ?_⟩
    obtain ⟨c, hc, hyc, hcW⟩ := hb.exists_subset_of_mem_open hy hW
    rw [hVeq] at hc
    obtain ⟨n, rfl⟩ := hc
    exact ⟨n, hyc, hcW⟩
  obtain ⟨B, hBm, hB⟩ := exists_measurableSet_eq_iUnion_prod_of_isOpen_sections hVo hV hA.compl
    fun x ↦ by rw [preimage_compl]; exact (hAc x).isOpen_compl
  have key : Prod.fst '' A = (⋃ F : Finset ℕ, ⋃ (_ : K ⊆ ⋃ n ∈ F, V n), ⋂ n ∈ F, B n)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨x', y⟩, hxy, rfl⟩ hx
      simp only [mem_iUnion, mem_iInter] at hx
      obtain ⟨F, hKF, hxF⟩ := hx
      obtain ⟨n, hnF, hyn⟩ := mem_iUnion₂.1 (hKF (hAK hxy).2)
      have : (x', y) ∈ Aᶜ := by
        rw [hB]
        exact mem_iUnion.2 ⟨n, hxF n hnF, hyn⟩
      exact this hxy
    · intro hx
      by_contra hne
      have hcover : K ⊆ ⋃ n ∈ {n | x ∈ B n}, V n := by
        intro y _
        have : (x, y) ∈ Aᶜ := fun h ↦ hne ⟨(x, y), h, rfl⟩
        rw [hB] at this
        obtain ⟨n, hxn, hyn⟩ := mem_iUnion.1 this
        exact mem_iUnion₂.2 ⟨n, hxn, hyn⟩
      obtain ⟨b, hbB, hbfin, hKb⟩ := hK.elim_finite_subcover_image (fun n _ ↦ hVo n) hcover
      refine hx (mem_iUnion.2 ⟨hbfin.toFinset, mem_iUnion.2 ⟨?_, mem_iInter₂.2 fun n hn ↦ ?_⟩⟩)
      · simpa using hKb
      · exact hbB (by simpa using hn)
  rw [key]
  refine (MeasurableSet.iUnion fun F ↦ MeasurableSet.iUnion fun _ ↦ ?_).compl
  exact Finset.measurableSet_biInter F fun n _ ↦ hBm n

/-- Novikov's theorem for closed sections in a σ-compact Polish target such as `ℝⁿ` (the sections
are then `K_σ`): on a standard Borel space `X`, the projection of a Borel subset of `X × Y` with
closed sections is Borel (cut the sections by the compact sets `compactCovering Y n`). -/
theorem measurableSet_image_fst_of_isClosed_sections [SigmaCompactSpace Y] {A : Set (X × Y)}
    (hA : MeasurableSet A) (hAc : ∀ x, IsClosed (Prod.mk x ⁻¹' A)) :
    MeasurableSet (Prod.fst '' A) := by
  have : Prod.fst '' A = ⋃ n, Prod.fst '' (A ∩ univ ×ˢ compactCovering Y n) := by
    rw [← image_iUnion, ← inter_iUnion, ← prod_iUnion, iUnion_compactCovering, univ_prod_univ,
      inter_univ]
  rw [this]
  refine MeasurableSet.iUnion fun n ↦ measurableSet_image_fst_of_isClosed_sections_of_isCompact
    (isCompact_compactCovering Y n)
    (hA.inter (MeasurableSet.univ.prod (isCompact_compactCovering Y n).measurableSet))
    inter_subset_right fun x ↦ ?_
  rw [preimage_inter, mk_preimage_prod_right (mem_univ x)]
  exact (hAc x).inter (isCompact_compactCovering Y n).isClosed

/-- **Novikov's theorem**: on a standard Borel space `X`, the projection of a Borel subset of
`X × Y`, `Y` Polish, with compact sections is Borel.  A continuous injection `e` of `Y` into the
compact cube `[0, 1]^ℕ` carries `A` to a Borel set (Lusin–Souslin) whose sections `e(A_x)` are
compact subsets of the cube, and the bounded form applies. -/
theorem measurableSet_image_fst_of_isCompact_sections {A : Set (X × Y)} (hA : MeasurableSet A)
    (hAc : ∀ x, IsCompact (Prod.mk x ⁻¹' A)) : MeasurableSet (Prod.fst '' A) := by
  letI := upgradeStandardBorel X
  obtain ⟨e, he, hinj, hI⟩ := exists_continuous_injective_unitCube Y
  set Φ : X × Y → X × (ℕ → ℝ) := fun p ↦ (p.1, e p.2) with hΦ
  have hΦc : Continuous Φ := continuous_fst.prodMk (he.comp continuous_snd)
  have hΦi : Injective Φ := fun p q h ↦ by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 (hinj h2)
  have hA' : MeasurableSet (Φ '' A) := hA.image_of_continuousOn_injOn hΦc.continuousOn hΦi.injOn
  have hK : IsCompact (Set.pi univ fun _ : ℕ ↦ Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ ↦ isCompact_Icc
  have himage : Prod.fst '' (Φ '' A) = Prod.fst '' A := by
    rw [image_image]
  rw [← himage]
  refine measurableSet_image_fst_of_isClosed_sections_of_isCompact hK hA' ?_ fun x ↦ ?_
  · rintro _ ⟨p, -, rfl⟩
    exact ⟨mem_univ _, fun n _ ↦ hI p.2 n⟩
  · have hsec : Prod.mk x ⁻¹' (Φ '' A) = e '' (Prod.mk x ⁻¹' A) := by
      ext z
      simp only [mem_preimage, mem_image, hΦ, Prod.mk.injEq, Prod.exists]
      constructor
      · rintro ⟨a, y, hay, rfl, rfl⟩
        exact ⟨y, hay, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨x, y, hy, rfl, rfl⟩
    rw [hsec]
    exact ((hAc x).image he).isClosed

end Projection

end RW
