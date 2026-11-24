/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: cyclical monotonicity

This file formalizes Definition 12.24 and Theorem 12.25.

A cycle `x₀, …, x_m` is a family `x : Fin (m + 1) → E`, and `x_{i+1}` with
`x_{m+1} = x₀` is `x (finRotate (m + 1) i)`.  The cyclic sum of 12(7) is
`cyclicSum x v = Σᵢ ⟪vᵢ, x_{i+1} - xᵢ⟫`.

For the converse half of 12.25 we use Rockafellar's function
`f(x) = sup {⟪v_m, x - x_m⟫ + ⟪v_{m-1}, x_m - x_{m-1}⟫ + ⋯ + ⟪v₀, x₁ - x₀⟫}`
over chains `(x₀, v₀), (x₁, v₁), …, (x_m, v_m)` in `gph T` starting at a fixed
pair `(x₀, v₀)`.  The supremum also allows `m = 0`, which does not change it
(repeat the pair `(x₀, v₀)`).  Appending a pair `(x̄, v̄) ∈ gph T` to a chain
gives `f(x) ≥ f(x̄) + ⟪v̄, x - x̄⟫`, and closing a chain at `x₀` gives a cyclic
sum, so `f(x₀) = 0`.  Uniqueness up to a constant comes from 12.19 and the
exact form of Corollary 3.37.
-/

import RockafellarWets.Chapter12.ProximalMappingMonotonicity
import RockafellarWets.Chapter3.Pointwise
import RockafellarWets.Chapter3.ExtendedProximalCancellationExact

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Definitions

/-- The cyclic sum `Σᵢ ⟪vᵢ, x_{i+1} - xᵢ⟫` of 12(7), with `x_{m+1} = x₀`. -/
def cyclicSum {n : ℕ} (x v : Fin n → E) : ℝ :=
  ∑ i, ⟪v i, x (finRotate n i) - x i⟫_ℝ

/-- **Definition 12.24 (cyclical monotonicity).**  For every `m ≥ 1`, points
`x₀, …, x_m` and `vᵢ ∈ T(xᵢ)`, the cyclic sum 12(7) is nonpositive. -/
def SvCyclicallyMonotone (T : E → Set E) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ x v : Fin (m + 1) → E, (∀ i, v i ∈ T (x i)) → cyclicSum x v ≤ 0

/-- **Definition 12.24 (maximal cyclical monotonicity).**  `T` is cyclically
monotone and its graph cannot be enlarged without destroying this property. -/
def SvMaximalCyclicallyMonotone (T : E → Set E) : Prop :=
  SvCyclicallyMonotone T ∧
    ∀ T' : E → Set E, SvCyclicallyMonotone T' → (∀ x, T x ⊆ T' x) → T' = T

theorem cyclicSum_of_le_one {n : ℕ} (hn : n ≤ 1) (x v : Fin n → E) : cyclicSum x v = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · simp [cyclicSum]
  · simp [cyclicSum]

/-- Cycles of any length, including the trivial ones, have nonpositive sums. -/
theorem SvCyclicallyMonotone.cyclicSum_nonpos {T : E → Set E} (hT : SvCyclicallyMonotone T)
    {n : ℕ} (x v : Fin n → E) (hv : ∀ i, v i ∈ T (x i)) : cyclicSum x v ≤ 0 := by
  rcases le_or_gt n 1 with hn | hn
  · rw [cyclicSum_of_le_one hn]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hT m (by omega) x v hv

/-- The cyclic sum of a two-point cycle. -/
theorem cyclicSum_two (x v : Fin 2 → E) :
    cyclicSum x v = ⟪v 0, x 1 - x 0⟫_ℝ + ⟪v 1, x 0 - x 1⟫_ℝ := by
  simp [cyclicSum, Fin.sum_univ_two]

/-- The case `m = 1` of 12(7): cyclically monotone mappings are monotone. -/
theorem SvCyclicallyMonotone.svMonotone {T : E → Set E} (hT : SvCyclicallyMonotone T) :
    SvMonotone T := by
  intro x₀ v₀ h₀ x₁ v₁ h₁
  have h := hT 1 le_rfl ![x₀, x₁] ![v₀, v₁] (fun i ↦ by fin_cases i <;> assumption)
  rw [cyclicSum_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have e : ⟪v₁ - v₀, x₁ - x₀⟫_ℝ = -(⟪v₀, x₁ - x₀⟫_ℝ + ⟪v₁, x₀ - x₁⟫_ℝ) := by
    rw [inner_sub_left, ← neg_sub x₁ x₀, inner_neg_right]
    ring
  rw [e]
  linarith

/-- Cyclical monotonicity passes to subgraphs. -/
theorem SvCyclicallyMonotone.mono {T T' : E → Set E} (hT : SvCyclicallyMonotone T)
    (h : ∀ x, T' x ⊆ T x) : SvCyclicallyMonotone T' :=
  fun m hm x v hv ↦ hT m hm x v fun i ↦ h _ (hv i)

end Definitions

section ConvexSubgradients

variable [FiniteDimensional ℝ E]

/-- **Theorem 12.25**, first step: the subgradient mapping of a proper convex
function is cyclically monotone. -/
theorem svCyclicallyMonotone_subdifferential_of_convex {f : E → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) : SvCyclicallyMonotone (subdifferential f) := by
  intro m _ x v hv
  choose a ha using fun i ↦ (hv i).1
  have hineq : ∀ i, ⟪v i, x (finRotate _ i) - x i⟫_ℝ ≤ a (finRotate _ i) - a i := by
    intro i
    have h := (mem_subdifferential_iff_of_convex hc hp (ha i)).1 (hv i) (x (finRotate _ i))
    rw [ha (finRotate _ i), EReal.coe_le_coe_iff] at h
    linarith
  calc cyclicSum x v ≤ ∑ i, (a (finRotate _ i) - a i) :=
        Finset.sum_le_sum fun i _ ↦ hineq i
    _ = 0 := by rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]

/-- **Theorem 12.25**: for a proper lsc convex `f`, `∂f` is maximal cyclically
monotone, since it is maximal monotone (12.17). -/
theorem svMaximalCyclicallyMonotone_subdifferential_of_convex {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    SvMaximalCyclicallyMonotone (subdifferential f) :=
  ⟨svCyclicallyMonotone_subdifferential_of_convex hp hc, fun _ hT' hsub ↦
    (svMaximalMonotone_subdifferential_of_convex hp hl hc).eq_of_subset hT'.svMonotone hsub⟩

end ConvexSubgradients

section Rockafellar

/-- The value at `x` of a chain `(x₀, v₀), …, (x_m, v_m)`:
`⟪v_m, x - x_m⟫ + Σ_{i<m} ⟪vᵢ, x_{i+1} - xᵢ⟫`. -/
def chainValue {m : ℕ} (xs vs : Fin (m + 1) → E) (x : E) : ℝ :=
  ⟪vs (Fin.last m), x - xs (Fin.last m)⟫_ℝ +
    ∑ i : Fin m, ⟪vs i.castSucc, xs i.succ - xs i.castSucc⟫_ℝ

/-- Closing a chain at its starting point gives its cyclic sum. -/
theorem chainValue_self_eq_cyclicSum {m : ℕ} (xs vs : Fin (m + 1) → E) :
    chainValue xs vs (xs 0) = cyclicSum xs vs := by
  rw [cyclicSum, Fin.sum_univ_castSucc, finRotate_last, chainValue, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finRotate_succ_apply, Fin.coeSucc_eq_succ]

/-- Appending a pair `(y, w)` to a chain. -/
theorem chainValue_snoc {m : ℕ} (xs vs : Fin (m + 1) → E) (y w x : E) :
    chainValue (Fin.snoc xs y : Fin (m + 2) → E) (Fin.snoc vs w : Fin (m + 2) → E) x =
      ⟪w, x - y⟫_ℝ + chainValue xs vs y := by
  simp only [chainValue, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.succ_last,
    Fin.succ_castSucc]
  ring

/-- A chain value is an affine function of `x`, hence convex. -/
theorem convexOn_chainValue {m : ℕ} (xs vs : Fin (m + 1) → E) :
    ConvexOn ℝ univ (chainValue xs vs) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ le_of_eq ?_⟩
  have h : a • x + b • y - xs (Fin.last m) =
      a • (x - xs (Fin.last m)) + b • (y - xs (Fin.last m)) := by
    simp only [smul_sub]
    conv_lhs => rw [← one_smul ℝ (xs (Fin.last m)), ← hab, add_smul]
    abel
  simp only [chainValue, smul_eq_mul, h, inner_add_right, real_inner_smul_right]
  linear_combination (-(∑ i : Fin m, ⟪vs i.castSucc, xs i.succ - xs i.castSucc⟫_ℝ)) * hab

/-- The epigraph of a chain value is convex. -/
theorem convex_epigraph_chainValue {m : ℕ} (xs vs : Fin (m + 1) → E) :
    Convex ℝ (epigraph fun x ↦ (chainValue xs vs x : EReal)) := by
  have he : epigraph (fun x ↦ (chainValue xs vs x : EReal)) =
      {p : E × ℝ | p.1 ∈ univ ∧ chainValue xs vs p.1 ≤ p.2} := by
    ext p
    simp only [epigraph, mem_setOf_eq, mem_univ, true_and, ge_iff_le, EReal.coe_le_coe_iff]
  rw [he]
  exact (convexOn_chainValue xs vs).convex_epigraph

theorem continuous_chainValue {m : ℕ} (xs vs : Fin (m + 1) → E) :
    Continuous (chainValue xs vs) := by
  unfold chainValue
  fun_prop

/-- Chains `(x₀, v₀), …, (x_m, v_m)` in `gph T` starting at `(x₀, v₀)`. -/
def SvChain (T : E → Set E) (x₀ v₀ : E) :=
  Σ m : ℕ, {p : (Fin (m + 1) → E) × (Fin (m + 1) → E) //
    p.1 0 = x₀ ∧ p.2 0 = v₀ ∧ ∀ i, p.2 i ∈ T (p.1 i)}

/-- Rockafellar's function of Theorem 12.25. -/
noncomputable def rockafellarFunction (T : E → Set E) (x₀ v₀ x : E) : EReal :=
  ⨆ c : SvChain T x₀ v₀, (chainValue c.2.1.1 c.2.1.2 x : EReal)

variable {T : E → Set E} {x₀ v₀ : E}

theorem chainValue_le_rockafellarFunction (c : SvChain T x₀ v₀) (x : E) :
    (chainValue c.2.1.1 c.2.1.2 x : EReal) ≤ rockafellarFunction T x₀ v₀ x :=
  le_iSup (fun c : SvChain T x₀ v₀ ↦ (chainValue c.2.1.1 c.2.1.2 x : EReal)) c

/-- The one-pair chain `(x₀, v₀)`. -/
def SvChain.base (h₀ : v₀ ∈ T x₀) : SvChain T x₀ v₀ :=
  ⟨0, ⟨(fun _ ↦ x₀, fun _ ↦ v₀), rfl, rfl, fun _ ↦ h₀⟩⟩

/-- Appending a pair of `gph T` to a chain. -/
def SvChain.snoc (c : SvChain T x₀ v₀) {y w : E} (h : w ∈ T y) : SvChain T x₀ v₀ :=
  ⟨c.1 + 1, ⟨(Fin.snoc c.2.1.1 y, Fin.snoc c.2.1.2 w), by
    refine ⟨?_, ?_, fun i ↦ ?_⟩
    · exact (Fin.snoc_castSucc (α := fun _ ↦ E) (p := c.2.1.1) (x := y) (i := 0)).trans c.2.2.1
    · exact (Fin.snoc_castSucc (α := fun _ ↦ E) (p := c.2.1.2) (x := w) (i := 0)).trans c.2.2.2.1
    · induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using h
      | cast j => simpa only [Fin.snoc_castSucc] using c.2.2.2.2 j⟩⟩

theorem lt_rockafellarFunction (h₀ : v₀ ∈ T x₀) (x : E) :
    ((⟪v₀, x - x₀⟫_ℝ : ℝ) : EReal) ≤ rockafellarFunction T x₀ v₀ x := by
  have h := chainValue_le_rockafellarFunction (SvChain.base h₀) x
  simpa [SvChain.base, chainValue] using h

theorem bot_lt_rockafellarFunction (h₀ : v₀ ∈ T x₀) (x : E) :
    ⊥ < rockafellarFunction T x₀ v₀ x :=
  (EReal.bot_lt_coe _).trans_le (lt_rockafellarFunction h₀ x)

/-- Appending `(x̄, v̄) ∈ gph T`: `chainValue(c)(x̄) + ⟪v̄, x - x̄⟫ ≤ f(x)`. -/
theorem chainValue_add_inner_le_rockafellarFunction (c : SvChain T x₀ v₀) {y w : E}
    (h : w ∈ T y) (x : E) :
    ((chainValue c.2.1.1 c.2.1.2 y + ⟪w, x - y⟫_ℝ : ℝ) : EReal) ≤
      rockafellarFunction T x₀ v₀ x := by
  have hc := chainValue_le_rockafellarFunction (c.snoc h) x
  simp only [SvChain.snoc] at hc
  rw [chainValue_snoc, add_comm] at hc
  exact hc

/-- If `f(x) ≤ b` and `(x̄, v̄) ∈ gph T`, then `f(x̄) ≤ b - ⟪v̄, x - x̄⟫`. -/
theorem rockafellarFunction_le_of_le {y w : E} (h : w ∈ T y) {x : E} {b : ℝ}
    (hb : rockafellarFunction T x₀ v₀ x ≤ b) :
    rockafellarFunction T x₀ v₀ y ≤ ((b - ⟪w, x - y⟫_ℝ : ℝ) : EReal) := by
  refine iSup_le fun c ↦ ?_
  have := (chainValue_add_inner_le_rockafellarFunction c h x).trans hb
  rw [EReal.coe_le_coe_iff] at this
  rw [EReal.coe_le_coe_iff]
  linarith

theorem rockafellarFunction_self (hT : SvCyclicallyMonotone T) (h₀ : v₀ ∈ T x₀) :
    rockafellarFunction T x₀ v₀ x₀ = 0 := by
  refine le_antisymm (iSup_le fun c ↦ ?_) ?_
  · have e := chainValue_self_eq_cyclicSum c.2.1.1 c.2.1.2
    rw [c.2.2.1] at e
    rw [e, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    exact hT.cyclicSum_nonpos _ _ c.2.2.2.2
  · have := lt_rockafellarFunction h₀ x₀
    simpa using this

theorem isProper_rockafellarFunction (hT : SvCyclicallyMonotone T) (h₀ : v₀ ∈ T x₀) :
    IsProper (rockafellarFunction T x₀ v₀) :=
  ⟨⟨x₀, by rw [rockafellarFunction_self hT h₀]; exact EReal.zero_lt_top⟩,
    bot_lt_rockafellarFunction h₀⟩

theorem lowerSemicontinuous_rockafellarFunction :
    LowerSemicontinuous (rockafellarFunction T x₀ v₀) :=
  lowerSemicontinuous_iSup fun _ ↦
    (continuous_coe_real_ereal.comp (continuous_chainValue _ _)).lowerSemicontinuous

theorem convex_epigraph_rockafellarFunction :
    Convex ℝ (epigraph (rockafellarFunction T x₀ v₀)) :=
  convex_epigraph_iSup fun _ ↦ convex_epigraph_chainValue _ _

variable [FiniteDimensional ℝ E]

/-- Every pair of `gph T` is a subgradient pair of Rockafellar's function. -/
theorem mem_subdifferential_rockafellarFunction (hT : SvCyclicallyMonotone T)
    (h₀ : v₀ ∈ T x₀) {y w : E} (h : w ∈ T y) :
    w ∈ subdifferential (rockafellarFunction T x₀ v₀) y := by
  have hp := isProper_rockafellarFunction hT h₀
  have hytop : rockafellarFunction T x₀ v₀ y < ⊤ := by
    have h1 := rockafellarFunction_le_of_le h (x := x₀) (b := 0)
      (by rw [rockafellarFunction_self hT h₀]; exact EReal.coe_zero.symm.le)
    exact h1.trans_lt (EReal.coe_lt_top _)
  have hFy : rockafellarFunction T x₀ v₀ y =
      ((rockafellarFunction T x₀ v₀ y).toReal : EReal) :=
    (EReal.coe_toReal hytop.ne (hp.2 y).ne').symm
  refine (mem_subdifferential_iff_of_convex convex_epigraph_rockafellarFunction hp hFy).2
    fun x ↦ ?_
  by_cases hxtop : rockafellarFunction T x₀ v₀ x = ⊤
  · rw [hxtop]
    exact le_top
  have hFx : rockafellarFunction T x₀ v₀ x =
      ((rockafellarFunction T x₀ v₀ x).toReal : EReal) :=
    (EReal.coe_toReal hxtop (hp.2 x).ne').symm
  have h1 := rockafellarFunction_le_of_le h (x := x)
    (b := (rockafellarFunction T x₀ v₀ x).toReal) hFx.le
  rw [hFy, EReal.coe_le_coe_iff] at h1
  rw [hFx, EReal.coe_le_coe_iff]
  linarith

end Rockafellar

section Characterization

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A maximal cyclically monotone mapping has a nonempty graph. -/
theorem SvMaximalCyclicallyMonotone.exists_mem {T : E → Set E}
    (hT : SvMaximalCyclicallyMonotone T) : ∃ x v, v ∈ T x := by
  by_contra hne
  push_neg at hne
  have hsingle : SvCyclicallyMonotone (fun x : E ↦ {v : E | x = 0 ∧ v = 0}) := by
    intro m _ x v hv
    have hx : ∀ i, x i = 0 := fun i ↦ (hv i).1
    simp [cyclicSum, hx]
  have h := hT.2 _ hsingle fun x v hv ↦ absurd hv (hne x v)
  have h0 : (0 : E) ∈ (fun x : E ↦ {v : E | x = 0 ∧ v = 0}) 0 := ⟨rfl, rfl⟩
  rw [h] at h0
  exact hne 0 0 h0

/-- **Theorem 12.25 (characterization of convex subgradient mappings).**  A
mapping is `∂f` for some proper lsc convex `f` exactly when it is maximal
cyclically monotone. -/
theorem exists_eq_subdifferential_iff_svMaximalCyclicallyMonotone (T : E → Set E) :
    (∃ f : E → EReal, IsProper f ∧ LowerSemicontinuous f ∧ Convex ℝ (epigraph f) ∧
        T = subdifferential f) ↔ SvMaximalCyclicallyMonotone T := by
  constructor
  · rintro ⟨f, hp, hl, hc, rfl⟩
    exact svMaximalCyclicallyMonotone_subdifferential_of_convex hp hl hc
  · intro hT
    obtain ⟨x₀, v₀, h₀⟩ := hT.exists_mem
    refine ⟨rockafellarFunction T x₀ v₀, isProper_rockafellarFunction hT.1 h₀,
      lowerSemicontinuous_rockafellarFunction, convex_epigraph_rockafellarFunction, ?_⟩
    exact (hT.2 _ (svCyclicallyMonotone_subdifferential_of_convex
      (isProper_rockafellarFunction hT.1 h₀) convex_epigraph_rockafellarFunction)
      fun y w h ↦ mem_subdifferential_rockafellarFunction hT.1 h₀ h).symm

/-- **Theorem 12.25**, uniqueness: two proper lsc convex functions with the
same subgradient mapping differ by a constant (through 12.19 and 3.37). -/
theorem exists_eq_add_const_of_subdifferential_eq {f₁ f₂ : E → EReal} (hp₁ : IsProper f₁)
    (hl₁ : LowerSemicontinuous f₁) (hc₁ : Convex ℝ (epigraph f₁)) (hp₂ : IsProper f₂)
    (hl₂ : LowerSemicontinuous f₂) (hc₂ : Convex ℝ (epigraph f₂))
    (h : subdifferential f₁ = subdifferential f₂) : ∃ c : ℝ, f₁ = fun x ↦ f₂ x + (c : EReal) := by
  refine corollary337_eq_add_const_of_proximalMappingEReal_eq hc₁ hl₁ hp₁ hc₂ hl₂ hp₂ one_pos ?_
  rw [proximalMappingEReal_eq_svResolvent_of_convex hp₁ hc₁ one_pos,
    proximalMappingEReal_eq_svResolvent_of_convex hp₂ hc₂ one_pos, h]

/-- **Theorem 12.25**, collected: `T = ∂f` for a proper lsc convex `f` exactly
when `T` is maximal cyclically monotone, and then `f` is unique up to an
additive constant. -/
theorem characterization_of_convex_subgradient_mappings (T : E → Set E) :
    ((∃ f : E → EReal, IsProper f ∧ LowerSemicontinuous f ∧ Convex ℝ (epigraph f) ∧
        T = subdifferential f) ↔ SvMaximalCyclicallyMonotone T) ∧
      ∀ f₁ f₂ : E → EReal, IsProper f₁ → LowerSemicontinuous f₁ → Convex ℝ (epigraph f₁) →
        IsProper f₂ → LowerSemicontinuous f₂ → Convex ℝ (epigraph f₂) →
        T = subdifferential f₁ → T = subdifferential f₂ →
        ∃ c : ℝ, f₁ = fun x ↦ f₂ x + (c : EReal) :=
  ⟨exists_eq_subdifferential_iff_svMaximalCyclicallyMonotone T,
    fun _ _ hp₁ hl₁ hc₁ hp₂ hl₂ hc₂ h₁ h₂ ↦
      exists_eq_add_const_of_subdifferential_eq hp₁ hl₁ hc₁ hp₂ hl₂ hc₂ (h₁.symm.trans h₂)⟩

/-- After 12.24: a maximal cyclically monotone mapping is maximal monotone
(12.25 with 12.17). -/
theorem SvMaximalCyclicallyMonotone.svMaximalMonotone {T : E → Set E}
    (hT : SvMaximalCyclicallyMonotone T) : SvMaximalMonotone T := by
  obtain ⟨f, hp, hl, hc, rfl⟩ := (exists_eq_subdifferential_iff_svMaximalCyclicallyMonotone T).2 hT
  exact svMaximalMonotone_subdifferential_of_convex hp hl hc

end Characterization

end RW
