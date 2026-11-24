/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaps of the ternary Cantor set

Geometry for the counterexample to the unrestricted graphical part of Theorem 14.56.  Binary words
`σ` index the closed intervals `I σ` of the ternary Cantor construction (`I [] = [0, 1]`, and
`I (c :: σ)` is `I σ` shrunk by `1/3` and moved into the left or right third), and `J σ` is the
open middle third of `I σ`, the gap removed at node `σ`.  A binary sequence `b` determines the point
`point b = ∑ digit (b i) / 3^(i+1)` of the Cantor set, which lies in every `I (b|m)`.

Facts used later: the gaps are pairwise disjoint (`disjoint_J`) and miss the Cantor set
(`point_not_mem_J`); `point` is continuous and injective; a limit of points in intervals of
unbounded depth is a Cantor point whose prefixes are eventually those of the intervals
(`exists_point_of_tendsto`).  Finally `dip` is a lower semicontinuous function which vanishes on
the gaps and is negative exactly on the image of the closed sets `column i` of sequences with no
`true` in column `i`; on the Cantor set it vanishes exactly on the witness space of
`RW.SuslinDiagonal`.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Semicontinuity.Basic
import RockafellarWets.Chapter14.SuslinDiagonal

open Set Filter Topology

namespace RW.CantorGaps

open RW.SuslinDiagonal

/-- The ternary digit `0` or `2` of a binary digit. -/
def digit (c : Bool) : ℝ := if c then 2 else 0

theorem digit_nonneg (c : Bool) : 0 ≤ digit c := by
  cases c <;> norm_num [digit]

theorem digit_le_two (c : Bool) : digit c ≤ 2 := by
  cases c <;> norm_num [digit]

/-- Left endpoint of the interval `I σ`. -/
noncomputable def left : List Bool → ℝ
  | [] => 0
  | c :: σ => (digit c + left σ) / 3

/-- The closed interval of the Cantor construction at node `σ`. -/
def I (σ : List Bool) : Set ℝ := Icc (left σ) (left σ + (1 / 3 : ℝ) ^ σ.length)

/-- The open middle third of `I σ`, the gap removed at node `σ`. -/
def J (σ : List Bool) : Set ℝ :=
  Ioo (left σ + (1 / 3 : ℝ) ^ (σ.length + 1)) (left σ + 2 * (1 / 3 : ℝ) ^ (σ.length + 1))

theorem left_bounds (σ : List Bool) : 0 ≤ left σ ∧ left σ + (1 / 3 : ℝ) ^ σ.length ≤ 1 := by
  induction σ with
  | nil => simp [left]
  | cons c σ ih =>
    obtain ⟨h1, h2⟩ := ih
    have hd0 := digit_nonneg c
    have hd2 := digit_le_two c
    simp only [left, List.length_cons, pow_succ]
    constructor <;> linarith

theorem I_nil : I [] = Icc 0 1 := by
  simp [I, left]

theorem I_subset_unit (σ : List Bool) : I σ ⊆ Icc 0 1 := by
  intro y hy
  obtain ⟨h1, h2⟩ := left_bounds σ
  have h3 : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ σ.length := by positivity
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem mem_I_cons {c : Bool} {σ : List Bool} {y : ℝ} :
    y ∈ I (c :: σ) ↔ 3 * y - digit c ∈ I σ := by
  simp only [I, left, List.length_cons, mem_Icc, pow_succ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem mem_J_cons {c : Bool} {σ : List Bool} {y : ℝ} :
    y ∈ J (c :: σ) ↔ 3 * y - digit c ∈ J σ := by
  simp only [J, left, List.length_cons, mem_Ioo, pow_succ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem J_subset_I (σ : List Bool) : J σ ⊆ I σ := by
  intro y hy
  have h : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ σ.length := by positivity
  simp only [J, I, mem_Ioo, mem_Icc, pow_succ] at hy ⊢
  constructor <;> linarith [hy.1, hy.2]

theorem I_cons_subset (c : Bool) (σ : List Bool) :
    I (c :: σ) ⊆ Icc (digit c / 3) ((digit c + 1) / 3) := by
  intro y hy
  obtain ⟨h1, h2⟩ := I_subset_unit σ (mem_I_cons.1 hy)
  constructor <;> linarith

theorem abs_sub_le_of_mem_I {σ : List Bool} {y y' : ℝ} (hy : y ∈ I σ) (hy' : y' ∈ I σ) :
    |y - y'| ≤ (1 / 3 : ℝ) ^ σ.length := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [hy.1, hy.2, hy'.1, hy'.2]

/-- Distinct nodes of the same depth `m` carry intervals at distance at least `3⁻ᵐ`. -/
theorem le_abs_sub_of_mem_I {σ τ : List Bool} (hlen : σ.length = τ.length) (hne : σ ≠ τ)
    {y y' : ℝ} (hy : y ∈ I σ) (hy' : y' ∈ I τ) : (1 / 3 : ℝ) ^ σ.length ≤ |y - y'| := by
  induction σ generalizing τ y y' with
  | nil =>
    cases τ with
    | nil => exact absurd rfl hne
    | cons d τ => simp at hlen
  | cons c σ ih =>
    cases τ with
    | nil => simp at hlen
    | cons d τ =>
      simp only [List.length_cons, add_left_inj] at hlen
      by_cases hcd : c = d
      · subst hcd
        have hne' : σ ≠ τ := fun h ↦ hne (h ▸ rfl)
        have h := ih hlen hne' (mem_I_cons.1 hy) (mem_I_cons.1 hy')
        have heq : 3 * y - digit c - (3 * y' - digit c) = 3 * (y - y') := by ring
        rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
        rw [List.length_cons, pow_succ]
        linarith
      · have hpow : (1 / 3 : ℝ) ^ (c :: σ).length ≤ 1 / 3 := by
          rw [List.length_cons, pow_succ]
          have : (1 / 3 : ℝ) ^ σ.length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          nlinarith
        refine hpow.trans ?_
        obtain ⟨a1, a2⟩ := I_cons_subset _ _ hy
        obtain ⟨b1, b2⟩ := I_cons_subset _ _ hy'
        cases c <;> cases d <;> simp only [digit] at a1 a2 b1 b2 hcd <;>
          norm_num at a1 a2 b1 b2 hcd
        · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        · rw [abs_of_nonneg (by linarith)]
          linarith

theorem I_subset_I_take (σ : List Bool) (k : ℕ) : I σ ⊆ I (σ.take k) := by
  induction σ generalizing k with
  | nil => simp
  | cons c σ ih =>
    cases k with
    | zero =>
      rw [List.take_zero, I_nil]
      exact I_subset_unit _
    | succ k =>
      intro y hy
      rw [List.take_succ_cons, mem_I_cons]
      exact ih k (mem_I_cons.1 hy)

theorem disjoint_J_I_append (σ : List Bool) (c : Bool) : Disjoint (J σ) (I (σ ++ [c])) := by
  induction σ with
  | nil =>
    rw [Set.disjoint_left]
    intro y hJ hI
    simp only [J, I, left, List.length_nil, List.nil_append, List.length_cons, mem_Ioo, mem_Icc,
      zero_add, pow_one] at hJ hI
    cases c <;> simp only [digit] at hI <;> norm_num at hI hJ <;> linarith [hI.1, hI.2]
  | cons d σ ih =>
    rw [Set.disjoint_left]
    intro y hJ hI
    rw [mem_J_cons] at hJ
    rw [List.cons_append, mem_I_cons] at hI
    exact Set.disjoint_left.1 ih hJ hI

/-- The gaps of the Cantor construction are pairwise disjoint. -/
theorem disjoint_J {σ τ : List Bool} (h : σ ≠ τ) : Disjoint (J σ) (J τ) := by
  wlog hle : σ.length ≤ τ.length generalizing σ τ with H
  · exact (H h.symm (le_of_not_ge hle)).symm
  rw [Set.disjoint_left]
  intro y hσ hτ
  have hyτ := J_subset_I τ hτ
  rcases hle.lt_or_eq with hlt | heq
  · by_cases hpre : τ.take σ.length = σ
    · have hsucc : τ.take (σ.length + 1) = σ ++ [τ[σ.length]] := by
        rw [List.take_add_one, hpre, List.getElem?_eq_getElem hlt, Option.toList_some]
      have := I_subset_I_take τ (σ.length + 1) hyτ
      rw [hsucc] at this
      exact Set.disjoint_left.1 (disjoint_J_I_append σ _) hσ this
    · have hlen : σ.length = (τ.take σ.length).length := by simp [hlt.le]
      have := le_abs_sub_of_mem_I hlen (Ne.symm hpre) (J_subset_I σ hσ)
        (I_subset_I_take τ σ.length hyτ)
      rw [sub_self, abs_zero] at this
      exact absurd this (not_le.2 (by positivity))
  · have := le_abs_sub_of_mem_I heq h (J_subset_I σ hσ) hyτ
    rw [sub_self, abs_zero] at this
    exact absurd this (not_le.2 (by positivity))

/-! ### Points of the Cantor set -/

theorem summable_digit (b : ℕ → Bool) : Summable fun i ↦ digit (b i) / 3 ^ (i + 1) := by
  refine Summable.of_nonneg_of_le (fun i ↦ by have := digit_nonneg (b i); positivity)
    (fun i ↦ ?_) ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num)).mul_left (2 / 3))
  have h := digit_le_two (b i)
  rw [div_eq_mul_inv, ← inv_pow, pow_succ, show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) i]

/-- The point of the Cantor set with binary address `b`. -/
noncomputable def point (b : ℕ → Bool) : ℝ := ∑' i, digit (b i) / 3 ^ (i + 1)

theorem point_eq (b : ℕ → Bool) :
    point b = (digit (b 0) + point (fun i ↦ b (i + 1))) / 3 := by
  rw [point, (summable_digit b).tsum_eq_zero_add, point]
  have : ∀ i : ℕ, digit (b (i + 1)) / 3 ^ (i + 1 + 1) = digit (b (i + 1)) / 3 ^ (i + 1) / 3 :=
    fun i ↦ by rw [pow_succ, div_div]
  simp only [this, tsum_div_const, zero_add, pow_one]
  ring

theorem point_bounds (b : ℕ → Bool) : 0 ≤ point b ∧ point b ≤ 1 := by
  constructor
  · exact tsum_nonneg fun i ↦ by have := digit_nonneg (b i); positivity
  · have hs : Summable fun i : ℕ ↦ (2 / 3 : ℝ) * (1 / 3) ^ i :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    calc point b ≤ ∑' i : ℕ, (2 / 3 : ℝ) * (1 / 3) ^ i := by
          refine (summable_digit b).tsum_le_tsum (fun i ↦ ?_) hs
          have h := digit_le_two (b i)
          rw [div_eq_mul_inv, ← inv_pow, pow_succ, show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) i]
      _ = 1 := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num

theorem pre_succ_cons {α : Type*} (x : ℕ → α) (n : ℕ) :
    pre x (n + 1) = x 0 :: pre (fun i ↦ x (i + 1)) n := by
  simp [pre, List.ofFn_succ]

theorem point_mem_I (b : ℕ → Bool) (m : ℕ) : point b ∈ I (pre b m) := by
  induction m generalizing b with
  | zero =>
    simp only [pre, List.ofFn_zero, I_nil]
    exact point_bounds b
  | succ m ih =>
    rw [pre_succ_cons, mem_I_cons, point_eq b]
    convert ih (fun i ↦ b (i + 1)) using 1
    ring

theorem eq_point_of_forall_mem {y : ℝ} {b : ℕ → Bool} (hy : ∀ m, y ∈ I (pre b m)) :
    y = point b := by
  by_contra hne
  have hpos : 0 < |y - point b| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 3 : ℝ) < 1)
  have := abs_sub_le_of_mem_I (hy m) (point_mem_I b m)
  rw [length_pre] at this
  linarith

theorem point_injective : Function.Injective point := by
  intro b b' h
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hne' : pre b (i + 1) ≠ pre b' (i + 1) := fun h ↦
    hi (pre_eq_pre_iff.1 h i (Nat.lt_succ_self i))
  have := le_abs_sub_of_mem_I (by simp) hne' (point_mem_I b _) (point_mem_I b' _)
  rw [h, sub_self, abs_zero] at this
  exact absurd this (not_le.2 (by positivity))

/-- Cantor points never lie in a gap. -/
theorem point_not_mem_J (b : ℕ → Bool) (σ : List Bool) : point b ∉ J σ := by
  intro hJ
  by_cases hpre : pre b σ.length = σ
  · have := point_mem_I b (σ.length + 1)
    rw [pre_succ, hpre] at this
    exact Set.disjoint_left.1 (disjoint_J_I_append σ _) hJ this
  · have := le_abs_sub_of_mem_I (by simp) hpre (point_mem_I b _) (J_subset_I σ hJ)
    rw [sub_self, abs_zero] at this
    exact absurd this (not_le.2 (by positivity))

theorem continuous_point : Continuous point := by
  refine continuous_tsum (fun i ↦ ?_) ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num)).mul_left (2 / 3)) (fun i b ↦ ?_)
  · have hi : Continuous fun b : ℕ → Bool ↦ b i := continuous_apply i
    exact ((continuous_of_discreteTopology (f := digit)).comp hi).div_const _
  · have h0 := digit_nonneg (b i)
    have h := digit_le_two (b i)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_mul_inv, ← inv_pow, pow_succ,
      show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) i]

/-- A limit of points in Cantor intervals of unbounded depth is a Cantor point, and the
prefixes of the nodes are eventually those of its address. -/
theorem exists_point_of_tendsto {z : ℕ → ℝ} {σ : ℕ → List Bool} {ζ : ℝ}
    (hz : ∀ k, z k ∈ I (σ k)) (hlen : Tendsto (fun k ↦ (σ k).length) atTop atTop)
    (hlim : Tendsto z atTop (𝓝 ζ)) :
    ∃ b, ζ = point b ∧ ∀ m, ∀ᶠ k in atTop, (σ k).take m = pre b m := by
  have step : ∀ m, ∃ τ : List Bool, τ.length = m ∧ ζ ∈ I τ ∧
      ∀ᶠ k in atTop, (σ k).take m = τ := by
    intro m
    have hev : ∀ᶠ k in atTop, m ≤ (σ k).length := hlen.eventually (eventually_ge_atTop m)
    have hmem : ∀ᶠ k in atTop, z k ∈ ⋃ τ ∈ {τ : List Bool | τ.length = m}, I τ :=
      hev.mono fun k hk ↦ mem_biUnion (x := (σ k).take m) (by simp [hk])
        (I_subset_I_take _ _ (hz k))
    have hclosed : IsClosed (⋃ τ ∈ {τ : List Bool | τ.length = m}, I τ) :=
      (List.finite_length_eq Bool m).isClosed_biUnion fun τ _ ↦ isClosed_Icc
    obtain ⟨τ, hτm, hζτ⟩ := mem_iUnion₂.1 (hclosed.mem_of_tendsto hlim hmem)
    refine ⟨τ, hτm, hζτ, ?_⟩
    have hclose : ∀ᶠ k in atTop, |z k - ζ| < (1 / 3 : ℝ) ^ m := by
      have := (Metric.tendsto_nhds.1 hlim) ((1 / 3 : ℝ) ^ m) (by positivity)
      simpa [Real.dist_eq] using this
    filter_upwards [hev, hclose] with k hk hkc
    by_contra hne
    have hlen' : ((σ k).take m).length = τ.length := by
      rw [List.length_take, min_eq_left hk]
      exact hτm.symm
    have := le_abs_sub_of_mem_I hlen' hne (I_subset_I_take _ _ (hz k)) hζτ
    rw [hlen', hτm] at this
    linarith
  choose τ hτlen hτI hτev using step
  have hcons : ∀ m, (τ (m + 1)).take m = τ m := by
    intro m
    obtain ⟨k, hk1, hk2⟩ := ((hτev (m + 1)).and (hτev m)).exists
    rw [← hk1, List.take_take, min_eq_left (Nat.le_succ m), hk2]
  set b : ℕ → Bool := fun n ↦ (τ (n + 1)).getD n false with hbdef
  have hpre : ∀ m, pre b m = τ m := by
    intro m
    induction m with
    | zero =>
      have := hτlen 0
      rw [List.length_eq_zero_iff] at this
      simp [pre, this]
    | succ m ih =>
      have hl : m < (τ (m + 1)).length := by rw [hτlen]; exact Nat.lt_succ_self m
      have hbm : b m = (τ (m + 1))[m] := by
        simp only [hbdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl,
          Option.getD_some]
      rw [pre_succ, ih, hbm, ← hcons m, List.take_append_getElem hl]
      exact List.take_of_length_le (by rw [hτlen])
  refine ⟨b, eq_point_of_forall_mem fun m ↦ by rw [hpre m]; exact hτI m, fun m ↦ ?_⟩
  simpa [hpre m] using hτev m

/-! ### The lower semicontinuous dip function -/

/-- Sequences with no `true` in column `i`. -/
def column (i : ℕ) : Set (ℕ → Bool) := {b | ∀ n, b (Nat.pair i n) = false}

theorem isClosed_column (i : ℕ) : IsClosed (column i) := by
  rw [column, setOf_forall]
  exact isClosed_iInter fun n ↦ isClosed_eq (continuous_apply _) continuous_const

/-- The compact pieces of the bad part of the Cantor set. -/
def bad (i : ℕ) : Set ℝ := point '' column i

theorem isClosed_bad (i : ℕ) : IsClosed (bad i) :=
  ((isClosed_column i).isCompact.image continuous_point).isClosed

open scoped Classical in
/-- The dip function: `-(1/2)^i` on `bad i \ ⋃_{j<i} bad j`, and `0` off the bad sets. -/
noncomputable def dip (z : ℝ) : ℝ := if h : ∃ i, z ∈ bad i then -(1 / 2 : ℝ) ^ Nat.find h else 0

open scoped Classical in
theorem dip_nonpos (z : ℝ) : dip z ≤ 0 := by
  unfold dip
  split_ifs
  · exact neg_nonpos.2 (by positivity)
  · exact le_rfl

open scoped Classical in
theorem dip_eq_zero_iff (z : ℝ) : dip z = 0 ↔ ∀ i, z ∉ bad i := by
  unfold dip
  split_ifs with h
  · simp only [neg_eq_zero, pow_eq_zero_iff', one_div, inv_eq_zero, OfNat.ofNat_ne_zero,
      ne_eq, false_and, false_iff, not_forall, not_not]
    exact h
  · push_neg at h
    simpa using h

open scoped Classical in
theorem lowerSemicontinuous_dip : LowerSemicontinuous dip := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : 0 ≤ c
  · convert isClosed_univ
    ext z
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    exact (dip_nonpos z).trans hc
  push_neg at hc
  have hfin : {i : ℕ | -c ≤ (1 / 2 : ℝ) ^ i}.Finite := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (neg_pos.2 hc) (by norm_num : (1 / 2 : ℝ) < 1)
    refine (Set.finite_lt_nat N).subset fun i hi ↦ ?_
    by_contra hiN
    have : (1 / 2 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.1 hiN)
    exact absurd hi (not_le.2 (this.trans_lt hN))
  have heq : dip ⁻¹' Iic c = ⋃ i ∈ {i : ℕ | -c ≤ (1 / 2 : ℝ) ^ i}, bad i := by
    ext z
    simp only [mem_preimage, mem_Iic, mem_iUnion, mem_setOf_eq, exists_prop]
    unfold dip
    split_ifs with h
    · constructor
      · intro hz
        exact ⟨Nat.find h, by linarith, Nat.find_spec h⟩
      · rintro ⟨i, hci, hi⟩
        have : (1 / 2 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ Nat.find h :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.find_min' h hi)
        linarith
    · constructor
      · intro hz
        linarith
      · rintro ⟨i, -, hi⟩
        exact absurd ⟨i, hi⟩ h
  rw [heq]
  exact hfin.isClosed_biUnion fun i _ ↦ isClosed_bad i

/-- On the Cantor set the dip vanishes exactly on the witness space. -/
theorem dip_point_eq_zero_iff (b : ℕ → Bool) : dip (point b) = 0 ↔ b ∈ witnessSet := by
  rw [dip_eq_zero_iff]
  simp only [bad, column, point_injective.mem_set_image, mem_setOf_eq, not_forall,
    Bool.not_eq_false, witnessSet]

theorem dip_eq_zero_of_mem_J {z : ℝ} {σ : List Bool} (hz : z ∈ J σ) : dip z = 0 := by
  rw [dip_eq_zero_iff]
  rintro i ⟨b, -, rfl⟩
  exact point_not_mem_J b σ hz

end RW.CantorGaps
