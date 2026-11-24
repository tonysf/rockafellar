/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A coded non-Borel set (Suslin's diagonal argument)

The counterexample to the unrestricted graphical part of Theorem 14.56 needs a set of parameters
that is not Borel although it is the projection of a Borel set.  We code such a set on the Baire
space `𝒩 = ℕ → ℕ` with its Borel (product) σ-field.

A parameter `t ∈ 𝒩` codes the tree `onSet t` of binary words `σ` with
`t (code (t|k, σ|k)) = 0` for all `k ≤ |σ|`.  Branches are taken in the witness set
`witnessSet` of binary sequences with a `true` in every column `n ↦ b ⟨i, n⟩`; this set maps
continuously onto `𝒩` by reading off the first `true` in each column (`readout`).  Every analytic
subset of `𝒩` is the set of `x` for which the tree coded by some fixed `y` along `x` has a branch in
`witnessSet` (`exists_code_eq_of_analyticSet`), and the diagonal
`{t ∣ onSet t has a branch in witnessSet}` is therefore not Borel (`not_measurableSet_diagonal`):
otherwise its complement, being analytic, would be coded by some `y`, and `y` would belong to the
diagonal exactly when it does not.
-/

import Mathlib.MeasureTheory.Constructions.Polish.Basic

open Set Filter Topology MeasureTheory

namespace RW.SuslinDiagonal

/-! ### The witness space and its readout onto the Baire space -/

/-- Binary sequences with a `true` in every column `n ↦ b ⟨i, n⟩`. -/
def witnessSet : Set (ℕ → Bool) := {b | ∀ i, ∃ n, b (Nat.pair i n) = true}

open scoped Classical in
/-- The first row with a `true` in column `i` (and `0` if there is none). -/
noncomputable def readout (b : ℕ → Bool) (i : ℕ) : ℕ :=
  if h : ∃ n, b (Nat.pair i n) = true then Nat.find h else 0

theorem readout_eq_iff {b : ℕ → Bool} (hb : b ∈ witnessSet) (i m : ℕ) :
    readout b i = m ↔ b (Nat.pair i m) = true ∧ ∀ n < m, b (Nat.pair i n) = false := by
  rw [readout, dif_pos (hb i), Nat.find_eq_iff]
  simp

/-- The readout is locally constant on the witness space. -/
theorem readout_local {b : ℕ → Bool} (hb : b ∈ witnessSet) (i : ℕ) :
    ∃ N, ∀ b' ∈ witnessSet, (∀ j < N, b' j = b j) → readout b' i = readout b i := by
  set m := readout b i with hm
  obtain ⟨hbm, hlt⟩ := (readout_eq_iff hb i m).1 rfl
  refine ⟨Nat.pair i m + 1, fun b' hb' hagree ↦ (readout_eq_iff hb' i m).2 ⟨?_, ?_⟩⟩
  · rw [hagree _ (Nat.lt_succ_self _)]
    exact hbm
  · intro n hn
    rw [hagree _ (Nat.lt_succ_of_lt (Nat.pair_lt_pair_right i hn))]
    exact hlt n hn

/-- The readout maps the witness space onto the Baire space. -/
theorem exists_readout_eq (z : ℕ → ℕ) : ∃ b ∈ witnessSet, readout b = z := by
  set b : ℕ → Bool := fun k ↦ decide ((Nat.unpair k).2 = z (Nat.unpair k).1)
  have hb : ∀ i n, b (Nat.pair i n) = decide (n = z i) := fun i n ↦ by
    simp [b, Nat.unpair_pair]
  have hW : b ∈ witnessSet := fun i ↦ ⟨z i, by rw [hb]; simp⟩
  refine ⟨b, hW, funext fun i ↦ (readout_eq_iff hW i (z i)).2 ⟨by rw [hb]; simp, ?_⟩⟩
  intro n hn
  rw [hb]
  simp [hn.ne]

/-! ### Prefixes and the coded trees -/

/-- The prefix `x|n = [x 0, …, x (n-1)]`. -/
def pre {α : Type*} (x : ℕ → α) (n : ℕ) : List α := List.ofFn fun i : Fin n ↦ x i

@[simp]
theorem length_pre {α : Type*} (x : ℕ → α) (n : ℕ) : (pre x n).length = n := by
  simp [pre]

theorem pre_eq_pre_iff {α : Type*} {x y : ℕ → α} {n : ℕ} :
    pre x n = pre y n ↔ ∀ i < n, x i = y i := by
  rw [pre, pre, List.ofFn_inj]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.2

theorem take_pre {α : Type*} (x : ℕ → α) {k n : ℕ} (h : k ≤ n) :
    (pre x n).take k = pre x k := by
  apply List.ext_getElem
  · simp [h]
  · intro i h₁ h₂
    simp [pre]

theorem pre_succ {α : Type*} (x : ℕ → α) (n : ℕ) : pre x (n + 1) = pre x n ++ [x n] := by
  rw [pre, pre, List.ofFn_succ', List.concat_eq_append]
  rfl

/-- Codes of pairs of prefixes. -/
def code (p : List ℕ × List Bool) : ℕ := Encodable.encode p

theorem code_injective : Function.Injective code := Encodable.encode_injective

/-- The tree of binary words coded by the parameter `t`. -/
def onSet (t : ℕ → ℕ) : Set (List Bool) :=
  {σ | ∀ k ≤ σ.length, t (code (pre t k, σ.take k)) = 0}

/-- The coded sets are trees: closed under prefixes. -/
theorem take_mem_onSet {t : ℕ → ℕ} {σ : List Bool} (hσ : σ ∈ onSet t) (m : ℕ) :
    σ.take m ∈ onSet t := by
  intro k hk
  rw [List.length_take] at hk
  rw [List.take_take, min_eq_left (le_min_iff.1 hk).1]
  exact hσ k (le_min_iff.1 hk).2

theorem forall_pre_mem_onSet_iff {t : ℕ → ℕ} {b : ℕ → Bool} :
    (∀ m, pre b m ∈ onSet t) ↔ ∀ n, t (code (pre t n, pre b n)) = 0 := by
  constructor
  · intro h n
    have := h n n (by simp)
    rwa [take_pre b le_rfl] at this
  · intro h m k hk
    rw [length_pre] at hk
    rw [take_pre b hk]
    exact h k

/-- The diagonal set: parameters whose coded tree has a branch in the witness space. -/
def diagonal : Set (ℕ → ℕ) :=
  {t | ∃ b ∈ witnessSet, ∀ n, t (code (pre t n, pre b n)) = 0}

theorem diagonal_eq : diagonal = {t | ∃ b ∈ witnessSet, ∀ m, pre b m ∈ onSet t} := by
  ext t
  simp only [diagonal, mem_setOf_eq, forall_pre_mem_onSet_iff]

/-! ### Measurability of the coded trees -/

theorem measurableSet_code_eq_zero (k : ℕ) (u : List Bool) :
    MeasurableSet {t : ℕ → ℕ | t (code (pre t k, u)) = 0} := by
  have : {t : ℕ → ℕ | t (code (pre t k, u)) = 0} =
      ⋃ s : Fin k → ℕ, ({t | ∀ i : Fin k, t i = s i} ∩ {t | t (code (List.ofFn s, u)) = 0}) := by
    ext t
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun i ↦ t i, fun i ↦ rfl, h⟩
    · rintro ⟨s, hs, h⟩
      have hpre : pre t k = List.ofFn s := by
        unfold pre
        congr 1
        funext i
        exact hs i
      rw [hpre]
      exact h
  rw [this]
  refine MeasurableSet.iUnion fun s ↦ MeasurableSet.inter ?_ ?_
  · rw [setOf_forall]
    exact MeasurableSet.iInter fun i ↦ (measurable_pi_apply (i : ℕ)) (measurableSet_singleton _)
  · exact (measurable_pi_apply _) (measurableSet_singleton 0)

/-- Membership of a fixed word in the coded tree is a measurable condition on the parameter. -/
theorem measurableSet_mem_onSet (σ : List Bool) : MeasurableSet {t : ℕ → ℕ | σ ∈ onSet t} := by
  have : {t : ℕ → ℕ | σ ∈ onSet t} =
      ⋂ k ∈ Finset.range (σ.length + 1), {t | t (code (pre t k, σ.take k)) = 0} := by
    ext t
    simp [onSet]
  rw [this]
  exact Finset.measurableSet_biInter _ fun k _ ↦ measurableSet_code_eq_zero k _

/-! ### Universality and the diagonal argument -/

theorem eq_of_forall_pre {g : (ℕ → ℕ) → ℕ → ℕ} (hg : Continuous g) {x : ℕ → ℕ}
    {b : ℕ → Bool} (hb : b ∈ witnessSet)
    (h : ∀ n, ∃ b' ∈ witnessSet, pre (g (readout b')) n = pre x n ∧ pre b' n = pre b n) :
    x = g (readout b) := by
  choose c hcW hcx hcb using h
  have h1 : Tendsto (fun n ↦ readout (c n)) atTop (𝓝 (readout b)) := by
    rw [tendsto_pi_nhds]
    intro i
    obtain ⟨N, hN⟩ := readout_local hb i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (hN (c n) (hcW n) fun j hj ↦
      (pre_eq_pre_iff.1 (hcb n)) j (lt_of_lt_of_le hj hn)).symm
  have h2 : Tendsto (fun n ↦ g (readout (c n))) atTop (𝓝 x) := by
    rw [tendsto_pi_nhds]
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    exact ((pre_eq_pre_iff.1 (hcx n)) i hn).symm
  exact tendsto_nhds_unique h2 ((hg.tendsto _).comp h1)

/-- **Universality**: every analytic subset of the Baire space is the set of `x` along which the
tree coded by a fixed `y` has a branch in the witness space. -/
theorem exists_code_eq_of_analyticSet {A : Set (ℕ → ℕ)} (hA : AnalyticSet A) :
    ∃ y : ℕ → ℕ, A = {x | ∃ b ∈ witnessSet, ∀ n, y (code (pre x n, pre b n)) = 0} := by
  classical
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨g, hg, rfl⟩
  · refine ⟨fun _ ↦ 1, ?_⟩
    ext x
    simp only [mem_empty_iff_false, mem_setOf_eq, false_iff, not_exists, not_and]
    intro b _ h
    exact one_ne_zero (h 0)
  set P : ℕ → Prop := fun m ↦
    ∃ b ∈ witnessSet, ∃ n, code (pre (g (readout b)) n, pre b n) = m
  refine ⟨fun m ↦ if P m then 0 else 1, ?_⟩
  have key : ∀ (x : ℕ → ℕ) (b : ℕ → Bool) (n : ℕ),
      ((if P (code (pre x n, pre b n)) then 0 else 1) = 0) ↔
        ∃ b' ∈ witnessSet, pre (g (readout b')) n = pre x n ∧ pre b' n = pre b n := by
    intro x b n
    simp only [ite_eq_left_iff, one_ne_zero, imp_false, not_not]
    constructor
    · rintro ⟨b', hb', n', hcode⟩
      have hpair := code_injective hcode
      simp only [Prod.mk.injEq] at hpair
      have hn : n' = n := by
        have := congrArg List.length hpair.2
        simpa using this
      subst hn
      exact ⟨b', hb', hpair.1, hpair.2⟩
    · rintro ⟨b', hb', h1, h2⟩
      exact ⟨b', hb', n, by rw [h1, h2]⟩
  ext x
  simp only [mem_range, mem_setOf_eq, key]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨b, hb, rfl⟩ := exists_readout_eq z
    exact ⟨b, hb, fun n ↦ ⟨b, hb, rfl, rfl⟩⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨readout b, (eq_of_forall_pre hg hb h).symm⟩

/-- **Suslin's diagonal argument**: the coded diagonal set is not Borel in the Baire space. -/
theorem not_measurableSet_diagonal : ¬ MeasurableSet diagonal := by
  intro hD
  obtain ⟨y, hy⟩ := exists_code_eq_of_analyticSet hD.compl.analyticSet
  have h : y ∉ diagonal ↔ y ∈ diagonal := by
    rw [← mem_compl_iff, hy]
    rfl
  exact not_iff_self h

end RW.SuslinDiagonal
