/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Analytic sets are universally measurable

The fact behind the measurable projection theorem 14(2) of Rockafellar–Wets: an analytic subset
of a (regular Hausdorff) topological space is null-measurable for every finite Borel measure.

Proof (Lusin): write `P = f(ℕ^ℕ)` with `f` continuous.  By continuity of outer measure from
below, choose bounds `N : ℕ → ℕ` such that the images of the boxes
`{x | x i ≤ N i for i < k}` keep outer measure above `ν(P) - ε`; the intersection of their
closures is a closed subset of `f({x | x ≤ N})` (a compactness argument), hence of `P`.
-/

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.MeasurableSpace.Prod

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace RW

section Boxes

/-- The box `{x | x i ≤ N i for i < k}` in Baire space. -/
def natBox (N : ℕ → ℕ) (k : ℕ) : Set (ℕ → ℕ) := {x | ∀ i < k, x i ≤ N i}

/-- The compact box `{x | x ≤ N}`. -/
def natBoxInf (N : ℕ → ℕ) : Set (ℕ → ℕ) := {x | ∀ i, x i ≤ N i}

theorem isCompact_natBoxInf (N : ℕ → ℕ) : IsCompact (natBoxInf N) := by
  have : natBoxInf N = Set.pi univ fun i ↦ Iic (N i) := by
    ext x
    simp only [natBoxInf, mem_setOf_eq, Set.mem_pi, mem_univ, mem_Iic, true_implies]
  rw [this]
  exact isCompact_univ_pi fun i ↦ (Set.finite_Iic _).isCompact

theorem natBoxInf_subset_natBox (N : ℕ → ℕ) (k : ℕ) : natBoxInf N ⊆ natBox N k :=
  fun _ hx i _ ↦ hx i

theorem natBox_antitone (N : ℕ → ℕ) : Antitone (natBox N) :=
  fun _ _ hkl _ hx i hi ↦ hx i (lt_of_lt_of_le hi hkl)

/-- A neighborhood of the compact box contains one of the boxes `natBox N k`. -/
theorem exists_natBox_subset {N : ℕ → ℕ} {W : Set (ℕ → ℕ)} (hW : IsOpen W)
    (h : natBoxInf N ⊆ W) : ∃ k, natBox N k ⊆ W := by
  by_contra hcon
  push_neg at hcon
  have hpick : ∀ k, ∃ x, x ∈ natBox N k ∧ x ∉ W := fun k ↦ not_subset.1 (hcon k)
  choose x hxbox hxW using hpick
  set z : ℕ → ℕ → ℕ := fun k i ↦ if i < k then x k i else 0 with hzdef
  have hzbox : ∀ k, z k ∈ natBoxInf N := by
    intro k i
    simp only [hzdef]
    split_ifs with hi
    · exact hxbox k i hi
    · exact Nat.zero_le _
  obtain ⟨y, hy, φ, hφ, hzφ⟩ := (isCompact_natBoxInf N).tendsto_subseq hzbox
  have hyW : W ∈ 𝓝 y := hW.mem_nhds (h hy)
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hW y (h hy)
  -- coordinates in `I` eventually agree
  have hcoord : ∀ i, ∀ᶠ j in atTop, z (φ j) i = y i := by
    intro i
    have := (continuous_apply i).continuousAt.tendsto.comp hzφ
    simpa [nhds_discrete, tendsto_pure] using this
  set M := I.sup id + 1 with hM
  have hev : ∀ᶠ j in atTop, (∀ i ∈ I, z (φ j) i = y i) ∧ M ≤ φ j := by
    refine (Filter.eventually_all_finset I |>.2 fun i _ ↦ hcoord i).and ?_
    exact (hφ.tendsto_atTop).eventually (eventually_ge_atTop M)
  obtain ⟨j, hjI, hjM⟩ := hev.exists
  apply hxW (φ j)
  refine hsub fun i hi ↦ ?_
  have hiM : i < φ j := lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)) hjM
  have hzx : z (φ j) i = x (φ j) i := by simp [hzdef, hiM]
  have := (hu i hi).2
  rw [← hjI i hi, hzx] at this
  exact this

end Boxes


section Universal

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [RegularSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

theorem natBox_eq_iUnion (N : ℕ → ℕ) (k : ℕ) :
    natBox N k = ⋃ m : ℕ, natBox (Function.update N k m) (k + 1) := by
  ext x
  simp only [natBox, mem_setOf_eq, mem_iUnion]
  constructor
  · intro hx
    refine ⟨x k, fun i hi ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hik | rfl
    · rw [Function.update_of_ne hik.ne]
      exact hx i hik
    · rw [Function.update_self]
  · rintro ⟨m, hm⟩ i hi
    have := hm i (Nat.lt_succ_of_lt hi)
    rwa [Function.update_of_ne hi.ne] at this

theorem natBox_update_mono (N : ℕ → ℕ) (k : ℕ) :
    Monotone fun m ↦ natBox (Function.update N k m) (k + 1) := by
  intro m m' hmm' x hx i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hik | rfl
  · have := hx i hi
    rwa [Function.update_of_ne hik.ne] at this ⊢
  · have := hx i hi
    rw [Function.update_self] at this ⊢
    exact this.trans hmm'

omit [TopologicalSpace Y] [T2Space Y] [RegularSpace Y] [OpensMeasurableSpace Y] in
/-- The greedy choice of bounds keeping the outer measure of the images of the boxes above `c`. -/
theorem exists_bounds_lt {f : (ℕ → ℕ) → Y} (ν : Measure Y) {c : ℝ≥0∞} (hc : c < ν (range f)) :
    ∃ N : ℕ → ℕ, ∀ k, c < ν (f '' natBox N k) := by
  classical
  have hstep : ∀ (M : ℕ → ℕ) (k : ℕ), c < ν (f '' natBox M k) →
      ∃ m, c < ν (f '' natBox (Function.update M k m) (k + 1)) := by
    intro M k h
    rw [natBox_eq_iUnion, image_iUnion] at h
    rw [Monotone.measure_iUnion (fun m m' hmm' ↦ image_mono (natBox_update_mono M k hmm'))] at h
    exact lt_iSup_iff.1 h
  set next : (ℕ → ℕ) → ℕ → ℕ := fun M k ↦
    if h : ∃ m, c < ν (f '' natBox (Function.update M k m) (k + 1)) then Nat.find h else 0
  obtain ⟨pref, h0, hsucc⟩ : ∃ pref : ℕ → ℕ → ℕ, pref 0 = 0 ∧
      ∀ k, pref (k + 1) = Function.update (pref k) k (next (pref k) k) :=
    ⟨fun k ↦ Nat.rec (0 : ℕ → ℕ) (fun k M ↦ Function.update M k (next M k)) k, rfl, fun _ ↦ rfl⟩
  have hinv : ∀ k, c < ν (f '' natBox (pref k) k) := by
    intro k
    induction k with
    | zero =>
      have : natBox (pref 0) 0 = univ := by ext x; simp [natBox]
      rw [this, image_univ]
      exact hc
    | succ k ih =>
      have hex := hstep (pref k) k ih
      rw [hsucc k]
      have : next (pref k) k = Nat.find hex := by simp only [next, dif_pos hex]
      rw [this]
      exact Nat.find_spec hex
  have hstable : ∀ j i, i < j → pref j i = pref (i + 1) i := by
    intro j
    induction j with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hij | rfl
      · rw [hsucc j, Function.update_of_ne hij.ne]
        exact ih i hij
      · rfl
  refine ⟨fun i ↦ pref (i + 1) i, fun k ↦ ?_⟩
  have : natBox (fun i ↦ pref (i + 1) i) k = natBox (pref k) k := by
    ext x
    simp only [natBox, mem_setOf_eq]
    exact forall₂_congr fun i hi ↦ by rw [hstable k i hi]
  rw [this]
  exact hinv k

/-- Inner approximation of analytic sets by closed sets. -/
theorem exists_isClosed_subset_lt_measure {f : (ℕ → ℕ) → Y} (hf : Continuous f) (ν : Measure Y)
    [IsFiniteMeasure ν] {c : ℝ≥0∞} (hc : c < ν (range f)) :
    ∃ K, IsClosed K ∧ K ⊆ range f ∧ c ≤ ν K := by
  obtain ⟨N, hN⟩ := exists_bounds_lt ν hc
  set K := ⋂ k, _root_.closure (f '' natBox N k) with hKdef
  refine ⟨K, isClosed_iInter fun _ ↦ isClosed_closure, ?_, ?_⟩
  · intro y hy
    by_contra hyr
    set L := f '' natBoxInf N with hLdef
    have hLc : IsCompact L := (isCompact_natBoxInf N).image hf
    have hyL : y ∉ L := fun h ↦ hyr (image_subset_range _ _ h)
    obtain ⟨C, hC, hCcl, hCL⟩ := exists_mem_nhds_isClosed_subset (hLc.isClosed.compl_mem_nhds hyL)
    have hW : IsOpen (f ⁻¹' Cᶜ) := hCcl.isOpen_compl.preimage hf
    have hsubW : natBoxInf N ⊆ f ⁻¹' Cᶜ := fun x hx hxC ↦ hCL hxC ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := exists_natBox_subset hW hsubW
    have hcl : _root_.closure (f '' natBox N k) ⊆ (interior C)ᶜ := by
      rw [← closure_compl]
      exact closure_mono (image_subset_iff.2 hk)
    exact hcl (mem_iInter.1 hy k) (mem_interior_iff_mem_nhds.2 hC)
  · have hmeas : ∀ k, NullMeasurableSet (_root_.closure (f '' natBox N k)) ν := fun k ↦
      isClosed_closure.measurableSet.nullMeasurableSet
    have hdir : Directed (· ⊇ ·) fun k ↦ _root_.closure (f '' natBox N k) :=
      (Antitone.directed_ge fun k l hkl ↦ closure_mono (image_mono (natBox_antitone N hkl)))
    rw [hKdef, Directed.measure_iInter hmeas hdir ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun k ↦ (hN k).le.trans (measure_mono subset_closure)

/-- **Analytic sets are universally measurable**: an analytic subset of a regular Hausdorff space
is null-measurable for every finite Borel measure. -/
theorem AnalyticSet.nullMeasurableSet {P : Set Y} (hP : AnalyticSet P) (ν : Measure Y)
    [IsFiniteMeasure ν] : NullMeasurableSet P ν := by
  rw [AnalyticSet] at hP
  rcases hP with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  rcases eq_or_ne (ν (range f)) 0 with h0 | h0
  · exact NullMeasurableSet.of_null h0
  have hfin : ν (range f) ≠ ⊤ := measure_ne_top _ _
  have hc : ∀ n : ℕ, ν (range f) - (1 / ((n : ℝ≥0∞) + 1)) < ν (range f) := fun n ↦
    ENNReal.sub_lt_self hfin h0 (by simp)
  choose K hKc hKsub hKmeas using fun n ↦ exists_isClosed_subset_lt_measure hf ν (hc n)
  set B := ⋃ n, K n with hBdef
  have hBsub : B ⊆ range f := iUnion_subset hKsub
  have hBmeas : MeasurableSet B := MeasurableSet.iUnion fun n ↦ (hKc n).measurableSet
  have hνB : ν B = ν (range f) := by
    refine le_antisymm (measure_mono hBsub) ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.coe_ne_zero.2 hε.ne')
    have h1 : ν (range f) - (1 / ((n : ℝ≥0∞) + 1)) ≤ ν B :=
      (hKmeas n).trans (measure_mono (subset_iUnion K n))
    calc ν (range f) ≤ (ν (range f) - (1 / ((n : ℝ≥0∞) + 1))) + 1 / ((n : ℝ≥0∞) + 1) :=
          le_tsub_add
      _ ≤ ν B + ε := by
          gcongr
          refine le_trans ?_ hn.le
          rw [one_div]
          exact ENNReal.inv_le_inv.2 le_self_add
  have hdiff : ν (range f \ B) = 0 := by
    have h1 : range f \ B ⊆ toMeasurable ν (range f) \ B :=
      diff_subset_diff_left (subset_toMeasurable _ _)
    refine measure_mono_null h1 ?_
    rw [measure_diff (hBsub.trans (subset_toMeasurable _ _)) hBmeas.nullMeasurableSet
      (measure_ne_top _ _), measure_toMeasurable, hνB, tsub_self]
  have : range f = B ∪ (range f \ B) := (union_diff_cancel hBsub).symm
  rw [this]
  exact hBmeas.nullMeasurableSet.union (NullMeasurableSet.of_null hdiff)

end Universal


section Projection

variable {T F : Type*} [MeasurableSpace T] [MeasurableSpace F]

omit [MeasurableSpace T] in
open scoped Classical in
/-- The coding of points of `T` by their membership pattern in a sequence of sets
`C : ℕ → Set T`, a map into the Cantor space `ℕ → Bool`. -/
def cantorCode (C : ℕ → Set T) (t : T) : ℕ → Bool := fun n ↦ decide (t ∈ C n)

omit [MeasurableSpace T] in
theorem cantorCode_apply (C : ℕ → Set T) (t : T) (n : ℕ) :
    cantorCode C t n = true ↔ t ∈ C n := by
  classical
  simp [cantorCode]

theorem measurable_cantorCode {C : ℕ → Set T} (hC : ∀ n, MeasurableSet (C n)) :
    Measurable (cantorCode C) := by
  refine measurable_pi_lambda _ fun n ↦ measurable_to_bool ?_
  convert hC n using 1
  ext t
  simp [cantorCode_apply]

/-- **Countable coding of product-measurable sets**: every `A ⊗ B`-measurable set is the inverse
image, under `(t, x) ↦ (cantorCode C t, x)` for a sequence `C` of measurable sets, of a
measurable subset of `(ℕ → Bool) × F`. -/
theorem exists_cantorCode_preimage {G : Set (T × F)} (hG : MeasurableSet G) :
    ∃ C : ℕ → Set T, (∀ n, MeasurableSet (C n)) ∧ ∃ G' : Set ((ℕ → Bool) × F), MeasurableSet G' ∧
      G = (fun q : T × F ↦ (cantorCode C q.1, q.2)) ⁻¹' G' := by
  have hG' : MeasurableSet[MeasurableSpace.generateFrom (image2 (· ×ˢ ·)
      {s : Set T | MeasurableSet s} {d : Set F | MeasurableSet d})] G := by
    rw [generateFrom_prod]
    exact hG
  clear hG
  induction G, hG' using MeasurableSpace.generateFrom_induction with
  | hC t ht _ =>
    obtain ⟨s, hs, d, hd, rfl⟩ := ht
    refine ⟨fun _ ↦ s, fun _ ↦ hs, ((fun b : ℕ → Bool ↦ b 0) ⁻¹' {true}) ×ˢ d,
      ((measurable_pi_apply 0) (measurableSet_singleton true)).prod hd, ?_⟩
    ext ⟨t, x⟩
    simp [cantorCode_apply]
  | empty =>
    exact ⟨fun _ ↦ ∅, fun _ ↦ MeasurableSet.empty, ∅, MeasurableSet.empty, rfl⟩
  | compl t _ ih =>
    obtain ⟨C, hC, G', hG', rfl⟩ := ih
    exact ⟨C, hC, G'ᶜ, hG'.compl, rfl⟩
  | iUnion s _ ih =>
    choose C hC G' hG' hs using ih
    set C' : ℕ → Set T := fun k ↦ C (Nat.unpair k).1 (Nat.unpair k).2
    have hC' : ∀ k, MeasurableSet (C' k) := fun k ↦ hC _ _
    set ρ : ℕ → (ℕ → Bool) → (ℕ → Bool) := fun n b j ↦ b (Nat.pair n j)
    have hρ : ∀ n, Measurable (ρ n) := fun n ↦
      measurable_pi_lambda _ fun j ↦ measurable_pi_apply _
    have hcode : ∀ n t, ρ n (cantorCode C' t) = cantorCode (C n) t := by
      intro n t
      funext j
      apply Bool.eq_iff_iff.2
      simp only [ρ, cantorCode_apply, C', Nat.unpair_pair]
    refine ⟨C', hC', ⋃ n, (fun q : (ℕ → Bool) × F ↦ (ρ n q.1, q.2)) ⁻¹' G' n,
      MeasurableSet.iUnion fun n ↦ ((hρ n).prodMap measurable_id) (hG' n), ?_⟩
    ext ⟨t, x⟩
    simp only [mem_iUnion, mem_preimage, hcode]
    exact exists_congr fun n ↦ by rw [hs n]; rfl

variable [TopologicalSpace F] [PolishSpace F] [BorelSpace F]

/-- **Measurable projection theorem** (14(2)): if the σ-field of `T` is complete for an s-finite
(e.g. σ-finite) measure `μ`, the projection on `T` of an `A ⊗ B(F)`-measurable subset of `T × F`,
`F` Polish, is measurable. -/
theorem measurableSet_image_fst_of_isComplete (μ : Measure T) [SFinite μ] [μ.IsComplete]
    {G : Set (T × F)} (hG : MeasurableSet G) : MeasurableSet (Prod.fst '' G) := by
  obtain ⟨C, hC, G', hG', rfl⟩ := exists_cantorCode_preimage hG
  have himage : Prod.fst '' ((fun q : T × F ↦ (cantorCode C q.1, q.2)) ⁻¹' G') =
      cantorCode C ⁻¹' (Prod.fst '' G') := by
    ext t
    simp
  rw [himage]
  have hφ := measurable_cantorCode hC
  have hA : AnalyticSet (Prod.fst '' G') := hG'.analyticSet_image measurable_fst
  have h1 : NullMeasurableSet (Prod.fst '' G') (μ.toFinite.map (cantorCode C)) :=
    RW.AnalyticSet.nullMeasurableSet hA _
  have h2 : NullMeasurableSet (cantorCode C ⁻¹' (Prod.fst '' G')) μ.toFinite :=
    h1.preimage ⟨hφ, Measure.AbsolutelyContinuous.rfl⟩
  exact (h2.mono_ac (absolutelyContinuous_toFinite μ)).measurable_of_complete

end Projection

end RW
