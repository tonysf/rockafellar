/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: A Borel-inseparable pair and the converse of Corollary 14.34

Corollary 14.34 says that an `A ⊗ B(ℝⁿ)`-measurable `f`, lsc in `x`, is a normal integrand when
`(T, A)` is "complete for some measure".  That hypothesis is vacuous (`count_isComplete`), so read
literally the converse is claimed on every measurable space.  It holds when `A` is complete for an
s-finite measure (`isNormalIntegrand_of_measurable_uncurry`) and on standard Borel spaces
(`isNormalIntegrand_of_measurable_uncurry_of_standardBorel`, through Novikov's theorem), but it
fails on a subspace of the Baire space `ℕ → ℕ` with the trace of the Borel σ-field
(`joint_measurability_criterion_counterexample`).  The same space refutes the closed-valued
(b) ⇒ (a) of Theorem 14.8 when no measure is available
(`graph_measurability_nonstandard_counterexample`).

The construction follows the classical idea of a Borel-inseparable pair of sets of tree codes and
a Borel set of rank comparisons, but needs no ordinal ranks:

* a parameter `c` codes, along each `x`, a tree `tree c x` on `ℕ`, and every analytic subset of
  `ℕ → ℕ` is `{x ∣ tree c x has a branch}` for some `c` (`exists_code_eq_of_analyticSet`);
* a parameter `y` carries two codes and so two trees `treeA y`, `treeB y` along `y`.  No Borel set
  separates `onlyA` (only `treeA y` has a branch) from `onlyB` (only `treeB y` has one)
  (`not_measurablySeparable_onlyA_onlyB`): for codes `c` of `Bᶜ` and `d` of `B`, the parameter with
  codes `c`, `d` would lie in `onlyB ∩ B` or in `onlyA \ B`;
* the comparison relations `A`, fixed points of "`A(σ, ρ)` iff `σ ∈ treeB y`, `ρ ∈ treeA y` and
  every child of `σ` in `treeB y` is related to some child of `ρ` in `treeA y`" with `A([], [])`,
  form a Borel set of pairs `(y, A)` (`measurableSet_comparisonGraph`).  There is exactly one on
  `onlyA` (`comparisons_eq_singleton`: the greatest fixed point, unique by well-founded induction
  on the branchless tree) and none on `onlyB` (`comparisons_eq_empty`: it would carry a branch of
  `treeB y` into `treeA y`).

On `T = onlyA ∪ onlyB` (`InseparablePair.Domain`) the sets `C(t) ⊆ ℝ`, the image of the comparison
relation under a measurable embedding into `ℝ` (`InseparablePair.points`), are closed and have a
measurable graph, while `dom C = onlyA` is not measurable in `T`
(`InseparablePair.not_measurableSet_svDom_points`).  Hence `f(t, ·) = δ_{C(t)}` is jointly
measurable, lsc and convex in `x`, but not normal.  So `T` is not standard Borel
(`InseparablePair.not_standardBorelSpace`) and is complete for no s-finite measure
(`InseparablePair.not_isComplete`).
-/

import RockafellarWets.Chapter14.StandardBorelMeasurability
import RockafellarWets.Chapter14.SuslinDiagonal
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

open Set Filter Topology MeasureTheory

noncomputable section

namespace RW

namespace InseparablePair

open SuslinDiagonal (pre length_pre take_pre pre_succ pre_eq_pre_iff)

/-! ### Trees on `ℕ` coded along a parameter -/

/-- Codes of pairs of words over `ℕ`. -/
def seqCode (p : List ℕ × List ℕ) : ℕ := Encodable.encode p

/-- Codes of pairs of words are injective. -/
theorem seqCode_injective : Function.Injective seqCode := Encodable.encode_injective

/-- The tree on `ℕ` coded by `c` along `x`: the words `s` with `c (code (x|k, s|k)) = 0` for
`1 ≤ k ≤ |s|`.  It contains the empty word and is closed under prefixes. -/
def tree (c x : ℕ → ℕ) : Set (List ℕ) :=
  {s | ∀ k, 0 < k → k ≤ s.length → c (seqCode (pre x k, s.take k)) = 0}

/-- A set of words has a branch if it contains every prefix of some `z : ℕ → ℕ`. -/
def HasBranch (a : Set (List ℕ)) : Prop := ∃ z : ℕ → ℕ, ∀ n, pre z n ∈ a

/-- The empty word belongs to every coded tree. -/
theorem nil_mem_tree (c x : ℕ → ℕ) : [] ∈ tree c x := by
  intro k hk hk'
  simp only [List.length_nil] at hk'
  omega

/-- Coded trees are closed under prefixes. -/
theorem take_mem_tree {c x : ℕ → ℕ} {s : List ℕ} (hs : s ∈ tree c x) (m : ℕ) :
    s.take m ∈ tree c x := by
  intro k hk hkm
  rw [List.length_take] at hkm
  rw [List.take_take, min_eq_left (le_min_iff.1 hkm).1]
  exact hs k hk (le_min_iff.1 hkm).2

/-- A coded tree has a branch `z` iff `c` vanishes at the codes of the pairs of prefixes. -/
theorem hasBranch_tree_iff {c x : ℕ → ℕ} :
    HasBranch (tree c x) ↔ ∃ z : ℕ → ℕ, ∀ n, 0 < n → c (seqCode (pre x n, pre z n)) = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun n hn ↦ ?_⟩
    have := hz n n hn (by simp)
    rwa [take_pre z le_rfl] at this
  · rintro ⟨z, hz⟩
    refine ⟨z, fun m k hk hkm ↦ ?_⟩
    rw [length_pre] at hkm
    rw [take_pre z hkm]
    exact hz k hk

/-- A condition on one coordinate of `C a`, at an index depending on finitely many coordinates of
`X a`, is measurable. -/
theorem measurableSet_code_eq_zero {α : Type*} [MeasurableSpace α] {C X : α → ℕ → ℕ}
    (hC : Measurable C) (hX : Measurable X) (k : ℕ) (u : List ℕ) :
    MeasurableSet {a | C a (seqCode (pre (X a) k, u)) = 0} := by
  have : {a | C a (seqCode (pre (X a) k, u)) = 0} = ⋃ v : Fin k → ℕ,
      ({a | ∀ i : Fin k, X a i = v i} ∩ {a | C a (seqCode (List.ofFn v, u)) = 0}) := by
    ext a
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun i ↦ X a i, fun i ↦ rfl, h⟩
    · rintro ⟨v, hv, h⟩
      have hpre : pre (X a) k = List.ofFn v := by
        unfold pre
        congr 1
        funext i
        exact hv i
      rw [hpre]
      exact h
  rw [this]
  refine MeasurableSet.iUnion fun v ↦ MeasurableSet.inter ?_ ?_
  · rw [setOf_forall]
    exact MeasurableSet.iInter fun i ↦
      ((measurable_pi_apply (i : ℕ)).comp hX) (measurableSet_singleton _)
  · exact ((measurable_pi_apply _).comp hC) (measurableSet_singleton 0)

/-- Membership of a fixed word in the coded tree is a measurable condition. -/
theorem measurableSet_mem_tree {α : Type*} [MeasurableSpace α] {C X : α → ℕ → ℕ}
    (hC : Measurable C) (hX : Measurable X) (s : List ℕ) :
    MeasurableSet {a | s ∈ tree (C a) (X a)} := by
  have : {a | s ∈ tree (C a) (X a)} =
      ⋂ k ∈ Finset.Icc 1 s.length, {a | C a (seqCode (pre (X a) k, s.take k)) = 0} := by
    ext a
    simp only [tree, mem_setOf_eq, mem_iInter, Finset.mem_Icc]
    constructor
    · rintro h k ⟨hk1, hk2⟩
      exact h k hk1 hk2
    · intro h k hk hk'
      exact h k ⟨hk, hk'⟩
  rw [this]
  exact Finset.measurableSet_biInter _ fun k _ ↦ measurableSet_code_eq_zero hC hX k _

/-! ### Universality -/

/-- If for each `n` some `z'` agrees with `z`, and `g z'` with `x`, on the first `n` coordinates,
then `x = g z` (continuity of `g`). -/
theorem eq_apply_of_forall_pre {g : (ℕ → ℕ) → ℕ → ℕ} (hg : Continuous g) {x z : ℕ → ℕ}
    (h : ∀ n, ∃ z', pre (g z') n = pre x n ∧ pre z' n = pre z n) : x = g z := by
  choose w hwx hwz using h
  have h1 : Tendsto w atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    exact ((pre_eq_pre_iff.1 (hwz n)) i hn).symm
  have h2 : Tendsto (fun n ↦ g (w n)) atTop (𝓝 x) := by
    rw [tendsto_pi_nhds]
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    exact ((pre_eq_pre_iff.1 (hwx n)) i hn).symm
  exact tendsto_nhds_unique h2 ((hg.tendsto _).comp h1)

/-- **Universality**: every analytic subset of the Baire space is the set of `x` along which the
tree coded by a fixed `c` has a branch. -/
theorem exists_code_eq_of_analyticSet {A : Set (ℕ → ℕ)} (hA : AnalyticSet A) :
    ∃ c : ℕ → ℕ, A = {x | HasBranch (tree c x)} := by
  classical
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨g, hg, rfl⟩
  · refine ⟨fun _ ↦ 1, ?_⟩
    ext x
    simp only [mem_empty_iff_false, mem_setOf_eq, false_iff, hasBranch_tree_iff, not_exists]
    intro z h
    exact one_ne_zero (h 1 one_pos)
  set P : ℕ → Prop := fun m ↦ ∃ z' : ℕ → ℕ, ∃ n, seqCode (pre (g z') n, pre z' n) = m
  refine ⟨fun m ↦ if P m then 0 else 1, ?_⟩
  have key : ∀ (x z : ℕ → ℕ) (n : ℕ),
      ((if P (seqCode (pre x n, pre z n)) then 0 else 1) = 0) ↔
        ∃ z', pre (g z') n = pre x n ∧ pre z' n = pre z n := by
    intro x z n
    simp only [ite_eq_left_iff, one_ne_zero, imp_false, not_not]
    constructor
    · rintro ⟨z', n', hcode⟩
      have hpair := seqCode_injective hcode
      simp only [Prod.mk.injEq] at hpair
      have hn : n' = n := by
        have := congrArg List.length hpair.2
        simpa using this
      subst hn
      exact ⟨z', hpair.1, hpair.2⟩
    · rintro ⟨z', h1, h2⟩
      exact ⟨z', n, by rw [h1, h2]⟩
  ext x
  simp only [mem_range, mem_setOf_eq, hasBranch_tree_iff, key]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, fun n _ ↦ ⟨z, rfl, rfl⟩⟩
  · rintro ⟨z, h⟩
    refine ⟨z, (eq_apply_of_forall_pre hg fun n ↦ ?_).symm⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨z, by simp [pre], rfl⟩
    · exact h n hn

/-! ### Two coded trees and a Borel-inseparable pair -/

/-- The first code read off a parameter. -/
def leftCode (y : ℕ → ℕ) : ℕ → ℕ := fun n ↦ y (Nat.pair 0 n)

/-- The second code read off a parameter. -/
def rightCode (y : ℕ → ℕ) : ℕ → ℕ := fun n ↦ y (Nat.pair 1 n)

/-- A parameter with prescribed codes. -/
def joinCodes (c d : ℕ → ℕ) : ℕ → ℕ := fun k ↦
  if (Nat.unpair k).1 = 0 then c (Nat.unpair k).2 else d (Nat.unpair k).2

/-- The first code of `joinCodes c d` is `c`. -/
theorem leftCode_joinCodes (c d : ℕ → ℕ) : leftCode (joinCodes c d) = c := by
  funext n
  simp [leftCode, joinCodes, Nat.unpair_pair]

/-- The second code of `joinCodes c d` is `d`. -/
theorem rightCode_joinCodes (c d : ℕ → ℕ) : rightCode (joinCodes c d) = d := by
  funext n
  simp [rightCode, joinCodes, Nat.unpair_pair]

/-- Reading off the first code is measurable. -/
theorem measurable_leftCode : Measurable leftCode :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- Reading off the second code is measurable. -/
theorem measurable_rightCode : Measurable rightCode :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- The first tree coded by a parameter `y`, along `y` itself. -/
def treeA (y : ℕ → ℕ) : Set (List ℕ) := tree (leftCode y) y

/-- The second tree coded by a parameter `y`, along `y` itself. -/
def treeB (y : ℕ → ℕ) : Set (List ℕ) := tree (rightCode y) y

/-- Parameters whose first tree has a branch while the second has none. -/
def onlyA : Set (ℕ → ℕ) := {y | HasBranch (treeA y) ∧ ¬ HasBranch (treeB y)}

/-- Parameters whose second tree has a branch while the first has none. -/
def onlyB : Set (ℕ → ℕ) := {y | ¬ HasBranch (treeA y) ∧ HasBranch (treeB y)}

/-- `onlyA` and `onlyB` are disjoint. -/
theorem disjoint_onlyA_onlyB : Disjoint onlyA onlyB :=
  Set.disjoint_left.2 fun _ hA hB ↦ hB.1 hA.1

/-- **No Borel set separates `onlyA` from `onlyB`** (a diagonal argument with the universal
coding of analytic sets): if `B` did, code `Bᶜ` by `c` and `B` by `d`; the parameter `y` with
codes `c`, `d` lies in `onlyB` if `y ∈ B`, and in `onlyA` if `y ∉ B`. -/
theorem not_measurablySeparable_onlyA_onlyB : ¬ MeasurablySeparable onlyA onlyB := by
  rintro ⟨B, hAB, hdisj, hB⟩
  obtain ⟨c, hc⟩ := exists_code_eq_of_analyticSet hB.compl.analyticSet
  obtain ⟨d, hd⟩ := exists_code_eq_of_analyticSet hB.analyticSet
  set y := joinCodes c d
  have hA : HasBranch (treeA y) ↔ y ∉ B := by
    rw [← mem_compl_iff, hc, treeA, leftCode_joinCodes]
    rfl
  have hB' : HasBranch (treeB y) ↔ y ∈ B := by
    rw [hd, treeB, rightCode_joinCodes]
    rfl
  by_cases hy : y ∈ B
  · exact Set.disjoint_left.1 hdisj ⟨fun h ↦ hA.1 h hy, hB'.2 hy⟩ hy
  · exact hy (hAB ⟨hA.2 hy, fun h ↦ hy (hB'.1 h)⟩)

/-! ### Comparison relations -/

/-- The operator whose fixed points are the comparison relations between the trees `b` and `a`:
`R(σ, ρ)` holds for `σ ∈ b`, `ρ ∈ a` when every child of `σ` in `b` is related to some child of
`ρ` in `a`.  (These are the rank comparisons of the classical construction; ranks are not used.) -/
def compStep (a b : Set (List ℕ)) (R : List ℕ → List ℕ → Prop) (σ ρ : List ℕ) : Prop :=
  σ ∈ b ∧ ρ ∈ a ∧ ∀ n, σ ++ [n] ∈ b → ∃ m, ρ ++ [m] ∈ a ∧ R (σ ++ [n]) (ρ ++ [m])

/-- `compStep a b` is monotone in the relation. -/
theorem compStep_mono {a b : Set (List ℕ)} {R R' : List ℕ → List ℕ → Prop}
    (h : ∀ σ ρ, R σ ρ → R' σ ρ) {σ ρ : List ℕ} : compStep a b R σ ρ → compStep a b R' σ ρ := by
  rintro ⟨hσ, hρ, hc⟩
  exact ⟨hσ, hρ, fun n hn ↦ (hc n hn).imp fun m hm ↦ ⟨hm.1, h _ _ hm.2⟩⟩

/-- `A`, read as a relation on words, is a fixed point of `compStep a b`. -/
def IsComparison (a b : Set (List ℕ)) (A : List ℕ × List ℕ → Bool) : Prop :=
  ∀ σ ρ, A (σ, ρ) = true ↔ compStep a b (fun σ' ρ' ↦ A (σ', ρ') = true) σ ρ

/-- The comparison relations relating the two roots. -/
def comparisons (a b : Set (List ℕ)) : Set (List ℕ × List ℕ → Bool) :=
  {A | IsComparison a b A ∧ A ([], []) = true}

/-- The greatest fixed point of `compStep a b` (Knaster–Tarski). -/
def gfpRel (a b : Set (List ℕ)) (σ ρ : List ℕ) : Prop :=
  ∃ R : List ℕ → List ℕ → Prop, (∀ σ' ρ', R σ' ρ' → compStep a b R σ' ρ') ∧ R σ ρ

/-- The greatest fixed point is a post-fixed point. -/
theorem gfpRel_le (a b : Set (List ℕ)) {σ ρ : List ℕ} (h : gfpRel a b σ ρ) :
    compStep a b (gfpRel a b) σ ρ := by
  obtain ⟨R, hR, hσρ⟩ := h
  exact compStep_mono (fun σ' ρ' h' ↦ ⟨R, hR, h'⟩) (hR σ ρ hσρ)

/-- The greatest fixed point is a fixed point (Knaster–Tarski). -/
theorem gfpRel_iff (a b : Set (List ℕ)) (σ ρ : List ℕ) :
    gfpRel a b σ ρ ↔ compStep a b (gfpRel a b) σ ρ := by
  refine ⟨gfpRel_le a b, fun h ↦ ⟨compStep a b (gfpRel a b), fun σ' ρ' h' ↦ ?_, h⟩⟩
  exact compStep_mono (fun σ'' ρ'' h'' ↦ gfpRel_le a b h'') h'

open scoped Classical in
/-- The greatest comparison relation, as a point of the Cantor space of relations. -/
def gfpComparison (a b : Set (List ℕ)) : List ℕ × List ℕ → Bool :=
  fun p ↦ decide (gfpRel a b p.1 p.2)

/-- The greatest fixed point is a comparison relation. -/
theorem isComparison_gfpComparison (a b : Set (List ℕ)) :
    IsComparison a b (gfpComparison a b) := by
  intro σ ρ
  simp only [gfpComparison, decide_eq_true_eq]
  exact gfpRel_iff a b σ ρ

/-- If `a` has a branch `x` and `[] ∈ b`, the roots are related: `{(σ, x|k) ∣ σ ∈ b}` is a
post-fixed point. -/
theorem gfpComparison_nil {a b : Set (List ℕ)} (ha : HasBranch a) (hb : [] ∈ b) :
    gfpComparison a b ([], []) = true := by
  obtain ⟨x, hx⟩ := ha
  simp only [gfpComparison, decide_eq_true_eq]
  refine ⟨fun σ ρ ↦ σ ∈ b ∧ ∃ k, ρ = pre x k, ?_, hb, 0, by simp [pre]⟩
  rintro σ ρ ⟨hσ, k, rfl⟩
  refine ⟨hσ, hx k, fun n hn ↦ ⟨x k, ?_, hn, k + 1, ?_⟩⟩
  · rw [← pre_succ]
    exact hx (k + 1)
  · rw [pre_succ]

/-- The child relation of a set of words. -/
def childRel (b : Set (List ℕ)) (σ' σ : List ℕ) : Prop := σ' ∈ b ∧ ∃ n, σ' = σ ++ [n]

/-- A prefix-closed set of words without branches has a well-founded child relation. -/
theorem wellFounded_childRel {b : Set (List ℕ)} (hb : ∀ s ∈ b, ∀ m, s.take m ∈ b)
    (hn : ¬ HasBranch b) : WellFounded (childRel b) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ ↦ hn ?_⟩
  choose m hm using fun k ↦ (hf k).2
  set L := (f 0).length with hL
  set z : ℕ → ℕ := fun i ↦ if h : i < L then (f 0)[i] else m (i - L) with hz
  have hfz : ∀ k, f k = pre z (L + k) := by
    intro k
    induction k with
    | zero =>
      apply List.ext_getElem
      · simp [hL]
      · intro i h1 h2
        simp only [pre, List.getElem_ofFn, hz]
        rw [dif_pos h1]
    | succ k ih =>
      rw [hm k, ih, show L + (k + 1) = L + k + 1 by omega, pre_succ]
      congr 2
      simp only [hz, show ¬ (L + k < L) by omega, dite_false, Nat.add_sub_cancel_left]
  refine ⟨z, fun n ↦ ?_⟩
  have h1 := hb _ (hf n).1 n
  rw [hfz, take_pre z (by omega)] at h1
  exact h1

/-- Comparison relations are unique when the child relation of `b` is well founded. -/
theorem isComparison_unique {a b : Set (List ℕ)} (hwf : WellFounded (childRel b))
    {A A' : List ℕ × List ℕ → Bool} (hA : IsComparison a b A) (hA' : IsComparison a b A') :
    A = A' := by
  have key : ∀ σ ρ, A (σ, ρ) = A' (σ, ρ) := by
    intro σ
    refine hwf.induction (C := fun σ ↦ ∀ ρ, A (σ, ρ) = A' (σ, ρ)) σ fun σ ih ρ ↦ ?_
    rw [Bool.eq_iff_iff, hA σ ρ, hA' σ ρ]
    refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall_congr' fun n ↦
      imp_congr_right fun hn ↦ exists_congr fun m ↦ and_congr_right fun _ ↦ ?_
    change A (σ ++ [n], ρ ++ [m]) = true ↔ A' (σ ++ [n], ρ ++ [m]) = true
    rw [ih (σ ++ [n]) ⟨hn, n, rfl⟩ (ρ ++ [m])]
  funext p
  exact key p.1 p.2

/-- A comparison relation relating the roots maps a branch of `b` to a branch of `a`. -/
theorem hasBranch_of_mem_comparisons {a b : Set (List ℕ)} {A : List ℕ × List ℕ → Bool}
    (hA : A ∈ comparisons a b) (hb : HasBranch b) : HasBranch a := by
  obtain ⟨hcomp, hroot⟩ := hA
  obtain ⟨z, hz⟩ := hb
  have step : ∀ k ρ, A (pre z k, ρ) = true →
      ∃ m, ρ ++ [m] ∈ a ∧ A (pre z (k + 1), ρ ++ [m]) = true := by
    intro k ρ h
    obtain ⟨-, -, hc⟩ := (hcomp _ _).1 h
    have := hc (z k) (by rw [← pre_succ]; exact hz (k + 1))
    rwa [← pre_succ] at this
  choose! M hM using step
  set ρ : ℕ → List ℕ := fun k ↦ Nat.rec [] (fun k r ↦ r ++ [M k r]) k with hρdef
  have hρsucc : ∀ k, ρ (k + 1) = ρ k ++ [M k (ρ k)] := fun k ↦ rfl
  have hρ : ∀ k, A (pre z k, ρ k) = true := by
    intro k
    induction k with
    | zero => simpa [pre, hρdef] using hroot
    | succ k ih => rw [hρsucc]; exact (hM k (ρ k) ih).2
  set x : ℕ → ℕ := fun k ↦ M k (ρ k)
  have hρx : ∀ k, ρ k = pre x k := by
    intro k
    induction k with
    | zero => simp [pre, hρdef]
    | succ k ih => rw [hρsucc, pre_succ, ← ih]
  refine ⟨x, fun k ↦ ?_⟩
  rw [← hρx]
  exact ((hcomp _ _).1 (hρ k)).2.1

/-- On `onlyA` there is exactly one comparison relation relating the roots. -/
theorem comparisons_eq_singleton {y : ℕ → ℕ} (hy : y ∈ onlyA) :
    comparisons (treeA y) (treeB y) = {gfpComparison (treeA y) (treeB y)} := by
  have hwf : WellFounded (childRel (treeB y)) :=
    wellFounded_childRel (fun _ hs m ↦ take_mem_tree hs m) hy.2
  ext A
  simp only [mem_singleton_iff]
  constructor
  · rintro ⟨hA, -⟩
    exact isComparison_unique hwf hA (isComparison_gfpComparison _ _)
  · rintro rfl
    exact ⟨isComparison_gfpComparison _ _, gfpComparison_nil hy.1 (nil_mem_tree _ _)⟩

/-- On `onlyB` no comparison relation relates the roots. -/
theorem comparisons_eq_empty {y : ℕ → ℕ} (hy : y ∈ onlyB) :
    comparisons (treeA y) (treeB y) = ∅ :=
  eq_empty_of_forall_notMem fun _ hA ↦ hy.1 (hasBranch_of_mem_comparisons hA hy.2)

/-- The graph `{(y, A) ∣ A ∈ comparisons (treeA y) (treeB y)}` is Borel: membership of fixed words
in the coded trees and the values of `A` are measurable, and the defining conditions quantify over
countably many words. -/
theorem measurableSet_comparisonGraph :
    MeasurableSet {p : (ℕ → ℕ) × (List ℕ × List ℕ → Bool) |
      p.2 ∈ comparisons (treeA p.1) (treeB p.1)} := by
  have hA : ∀ s, Measurable fun p : (ℕ → ℕ) × (List ℕ × List ℕ → Bool) ↦ s ∈ treeA p.1 :=
    fun s ↦ measurableSet_setOf.1
      (measurableSet_mem_tree (measurable_leftCode.comp measurable_fst) measurable_fst s)
  have hB : ∀ s, Measurable fun p : (ℕ → ℕ) × (List ℕ × List ℕ → Bool) ↦ s ∈ treeB p.1 :=
    fun s ↦ measurableSet_setOf.1
      (measurableSet_mem_tree (measurable_rightCode.comp measurable_fst) measurable_fst s)
  have hR : ∀ q : List ℕ × List ℕ,
      Measurable fun p : (ℕ → ℕ) × (List ℕ × List ℕ → Bool) ↦ p.2 q = true :=
    fun q ↦ by
      have hq : Measurable fun p : (ℕ → ℕ) × (List ℕ × List ℕ → Bool) ↦ p.2 q :=
        (measurable_pi_apply q).comp measurable_snd
      exact measurableSet_setOf.1 (hq (measurableSet_singleton true))
  refine measurableSet_setOf.2 (Measurable.and ?_ (hR _))
  refine Measurable.forall fun σ ↦ Measurable.forall fun ρ ↦ (hR _).iff ?_
  exact (hB σ).and ((hA ρ).and (Measurable.forall fun n ↦ (hB _).imp
    (Measurable.exists fun m ↦ (hA _).and (hR _))))

/-! ### The non-standard measurable space and the integrand -/

/-- A measurable embedding of the Cantor space of relations into `ℝ`. -/
def embed : (List ℕ × List ℕ → Bool) → ℝ :=
  (exists_measurableEmbedding_real (List ℕ × List ℕ → Bool)).choose

/-- `embed` is a measurable embedding. -/
theorem measurableEmbedding_embed : MeasurableEmbedding embed :=
  (exists_measurableEmbedding_real (List ℕ × List ℕ → Bool)).choose_spec

/-- The parameter set `onlyA ∪ onlyB ⊆ ℕ → ℕ`, a measurable space with the trace of the Borel
σ-field. -/
def Domain : Set (ℕ → ℕ) := onlyA ∪ onlyB

/-- The closed sets `C(t) ⊆ ℝ`: a single point for `t ∈ onlyA`, empty for `t ∈ onlyB`. -/
def points (t : Domain) : Set ℝ := embed '' comparisons (treeA t.1) (treeB t.1)

/-- Each `C(t)` has at most one point. -/
theorem points_subsingleton (t : Domain) : (points t).Subsingleton := by
  rcases t.2 with h | h
  · rw [points, comparisons_eq_singleton h, image_singleton]
    exact subsingleton_singleton
  · rw [points, comparisons_eq_empty h, image_empty]
    exact subsingleton_empty

/-- `C(t)` is nonempty exactly on `onlyA`. -/
theorem points_nonempty_iff (t : Domain) : (points t).Nonempty ↔ t.1 ∈ onlyA := by
  rcases t.2 with h | h
  · simp only [h, points, comparisons_eq_singleton h, image_singleton, singleton_nonempty]
  · simp only [points, comparisons_eq_empty h, image_empty, Set.not_nonempty_empty, false_iff]
    exact fun h' ↦ Set.disjoint_left.1 disjoint_onlyA_onlyB h' h

/-- The graph of `t ↦ C(t)` is measurable: the image of the Borel comparison graph under the
injective measurable map `id × embed` (Lusin–Souslin), pulled back to `T × ℝ`. -/
theorem measurableSet_svGraph_points : MeasurableSet (svGraph points) := by
  set W : Set ((ℕ → ℕ) × ℝ) :=
    Prod.map id embed '' {p : (ℕ → ℕ) × (List ℕ × List ℕ → Bool) |
      p.2 ∈ comparisons (treeA p.1) (treeB p.1)} with hW
  have hWm : MeasurableSet W := by
    refine measurableSet_comparisonGraph.image_of_measurable_injOn
      (measurable_id.prodMap measurableEmbedding_embed.measurable) ?_
    rintro ⟨y, A⟩ - ⟨y', A'⟩ - h
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h
    rw [h.1, measurableEmbedding_embed.injective h.2]
  have heq : svGraph points = Prod.map Subtype.val id ⁻¹' W := by
    ext ⟨t, r⟩
    simp only [mem_svGraph, points, mem_preimage, Prod.map_apply, id_eq, hW, mem_image,
      Prod.exists, mem_setOf_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact ⟨t.1, A, hA, rfl, rfl⟩
    · rintro ⟨y, A, hA, rfl, rfl⟩
      exact ⟨A, hA, rfl⟩
  rw [heq]
  exact (measurable_subtype_coe.prodMap measurable_id) hWm

/-- The domain of `t ↦ C(t)` is `onlyA`, as a subset of `T`. -/
theorem svDom_points : svDom points = {t : Domain | t.1 ∈ onlyA} := by
  ext t
  exact points_nonempty_iff t

/-- `dom C = onlyA` is not measurable in `T`: a Borel set cutting it out of `T` would separate
`onlyA` from `onlyB`. -/
theorem not_measurableSet_svDom_points : ¬ MeasurableSet (svDom points) := by
  intro h
  obtain ⟨B, hB, hpre⟩ := MeasurableSpace.measurableSet_comap.1 h
  refine not_measurablySeparable_onlyA_onlyB ⟨B, fun y hy ↦ ?_, Set.disjoint_left.2
    fun y hy hyB ↦ ?_, hB⟩
  · have ht : (⟨y, Or.inl hy⟩ : Domain) ∈ svDom points := (points_nonempty_iff _).2 hy
    rw [← hpre] at ht
    exact ht
  · have ht : (⟨y, Or.inr hy⟩ : Domain) ∈ Subtype.val ⁻¹' B := hyB
    rw [hpre] at ht
    exact Set.disjoint_left.1 disjoint_onlyA_onlyB ((points_nonempty_iff _).1 ht) hy

/-- `t ↦ C(t)` is not measurable, since its domain is not (`not_measurableSet_svDom_points`). -/
theorem not_svMeasurable_points : ¬ SvMeasurable points := fun h ↦
  not_measurableSet_svDom_points h.measurableSet_svDom

end InseparablePair

open InseparablePair

/-- **Theorem 14.8**, closed-valued (b) ⇒ (a), fails on a non-standard measurable space:
on `InseparablePair.Domain ⊆ ℕ → ℕ` with the trace of the Borel σ-field, the mapping
`t ↦ C(t) ⊆ ℝ` (a point or empty) has a measurable graph but is not measurable. -/
theorem graph_measurability_nonstandard_counterexample :
    ∃ S : InseparablePair.Domain → Set ℝ, (∀ t, IsClosed (S t)) ∧
      MeasurableSet (svGraph S) ∧ ¬ SvMeasurable S :=
  ⟨points, fun t ↦ (points_subsingleton t).isClosed, measurableSet_svGraph_points,
    not_svMeasurable_points⟩

/-- **Corollary 14.34**, the literal converse fails on a non-standard measurable space: on
`InseparablePair.Domain` with the trace of the Borel σ-field, `f(t, ·) = δ_{C(t)}` is
`A ⊗ B(ℝ)`-measurable, lsc and convex in `x`, but not a normal integrand. -/
theorem joint_measurability_criterion_counterexample :
    ∃ f : InseparablePair.Domain → ℝ → EReal, Measurable (Function.uncurry f) ∧
      (∀ t, LowerSemicontinuous (f t)) ∧ (∀ t, Convex ℝ (epigraph (f t))) ∧
        ¬ IsNormalIntegrand f := by
  classical
  refine ⟨fun t ↦ indicatorVA (points t), ?_, fun t ↦ lowerSemicontinuous_indicatorVA
    (points_subsingleton t).isClosed, fun t ↦ ?_, fun h ↦ not_svMeasurable_points
      (isNormalIntegrand_indicatorVA_iff.1 h).2⟩
  · have : Function.uncurry (fun t ↦ indicatorVA (points t)) =
        fun p : InseparablePair.Domain × ℝ ↦ if p ∈ svGraph points then (0 : EReal) else ⊤ := by
      funext ⟨t, y⟩
      simp only [Function.uncurry, indicatorVA, mem_svGraph]
    rw [this]
    exact Measurable.ite measurableSet_svGraph_points measurable_const measurable_const
  · rw [epigraph_indicatorVA]
    refine Convex.prod ?_ (convex_Ici 0)
    rcases (points_subsingleton t).eq_empty_or_singleton with h | ⟨r, h⟩
    · rw [h]
      exact convex_empty
    · rw [h]
      exact convex_singleton r

/-- The parameter space of `joint_measurability_criterion_counterexample` is not standard Borel
(otherwise `isNormalIntegrand_of_measurable_uncurry_of_standardBorel` would apply). -/
theorem InseparablePair.not_standardBorelSpace : ¬ StandardBorelSpace InseparablePair.Domain := by
  intro h
  obtain ⟨f, hf, hl, -, hn⟩ := joint_measurability_criterion_counterexample
  exact hn (isNormalIntegrand_of_measurable_uncurry_of_standardBorel hf hl)

/-- The parameter space of `joint_measurability_criterion_counterexample` is complete for no
s-finite measure (otherwise `isNormalIntegrand_of_measurable_uncurry` would apply). -/
theorem InseparablePair.not_isComplete (μ : Measure InseparablePair.Domain) [SFinite μ] :
    ¬ μ.IsComplete := by
  intro h
  obtain ⟨f, hf, hl, -, hn⟩ := joint_measurability_criterion_counterexample
  exact hn (isNormalIntegrand_of_measurable_uncurry μ hf hl)

end RW
