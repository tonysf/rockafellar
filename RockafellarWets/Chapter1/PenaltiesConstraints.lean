/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1A: Penalties and constraints

* **Example 1.1**: equality and inequality constraints, represented by the objective
  `f = f₀ + δ_C` (`constrainedObjective`, Chapter 7) on the constraint set `C`.
* **Example 1.2**: boxes (`finiteBox` of nonempty closed intervals, Chapter 6).
* **Example 1.3**: penalties and barriers: linear and quadratic penalties, their limit `δ_(-∞,0]`,
  and the barriers `ε/|t|` and `-ε log|t|`.
* **Example 1.4**: the principle of abstract minimization, as an equivalence between problems
  `(C, f₀)` with finite `f₀` and functions `f : ℝⁿ → ℝ̄` that never take the value `-∞`.
-/

import RockafellarWets.Chapter1.Attainment
import RockafellarWets.Chapter6.FiniteBoxes
import RockafellarWets.Chapter7.ConstrainedSolutionMappings
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Filter Topology

noncomputable section

namespace RW

variable {E ι : Type*}

/-! ## Example 1.1 -/

section Constraints

/-- The constraint set of Example 1.1: `x ∈ X` with `fᵢ(x) ≤ 0` for `i ∈ I₁` and `fᵢ(x) = 0` for
`i ∈ I₂`. -/
def constraintSystemSet (X : Set E) (fs : ι → E → ℝ) (I₁ I₂ : Set ι) : Set E :=
  {x | x ∈ X ∧ (∀ i ∈ I₁, fs i x ≤ 0) ∧ ∀ i ∈ I₂, fs i x = 0}

/-- **Example 1.1**: the objective `f`, equal to `f₀` on the constraint set and `∞` elsewhere, is
`f₀ + δ_C`. -/
theorem constrainedObjective_eq_add_indicatorVA (f₀ : E → ℝ) (C : Set E) :
    constrainedObjective (fun x ↦ (f₀ x : EReal)) C = fun x ↦ (f₀ x : EReal) + indicatorVA C x := by
  classical
  funext x
  by_cases hx : x ∈ C <;> simp [constrainedObjective, hx]

/-- **Example 1.1**: `inf f = ∞` exactly when the constraints are inconsistent (`C = ∅`). -/
theorem iInf_constrainedObjective_eq_top_iff (f₀ : E → ℝ) (C : Set E) :
    (⨅ x, constrainedObjective (fun x ↦ (f₀ x : EReal)) C x) = ⊤ ↔ C = ∅ := by
  classical
  rw [iInf_eq_top, eq_empty_iff_forall_notMem]
  refine forall_congr' fun x ↦ ?_
  by_cases hx : x ∈ C <;> simp [constrainedObjective, hx]

/-- **Example 1.1**: minimizing `f` over `ℝⁿ` is minimizing `f₀` over `C`: the infima agree. -/
theorem iInf_constrainedObjective (f₀ : E → ℝ) (C : Set E) :
    (⨅ x, constrainedObjective (fun x ↦ (f₀ x : EReal)) C x) = ⨅ x ∈ C, (f₀ x : EReal) := by
  rw [constrainedObjective_eq_add_indicatorVA]
  exact iInf_restrictedObjective f₀ C

/-- **Example 1.1**: constraints `fᵢ(x) ≤ cᵢ`, `fᵢ(x) = cᵢ`, `fᵢ(x) ≥ cᵢ` reduce to the standard
form by replacing `fᵢ` with `fᵢ - cᵢ` or `cᵢ - fᵢ`. -/
theorem constraint_shift (g : E → ℝ) (c : ℝ) (x : E) :
    (g x ≤ c ↔ (fun y ↦ g y - c) x ≤ 0) ∧ (g x = c ↔ (fun y ↦ g y - c) x = 0) ∧
      (c ≤ g x ↔ (fun y ↦ c - g y) x ≤ 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sub_eq_zero]

end Constraints

/-! ## Example 1.2 -/

section Boxes

/-- **Example 1.2**: `X ⊂ ℝⁿ` is a box if it is a product `X₁ × ⋯ × Xₙ` of closed intervals,
not necessarily bounded (`IsNonemptyClosedInterval`, Chapter 6). -/
def IsBox (X : Set (EuclideanSpace ℝ ι)) : Prop :=
  ∃ C : ι → Set ℝ, (∀ j, IsNonemptyClosedInterval (C j)) ∧ X = finiteBox C

/-- **Example 1.2**: a box is closed. -/
theorem IsBox.isClosed {X : Set (EuclideanSpace ℝ ι)} (h : IsBox X) : IsClosed X := by
  obtain ⟨C, hC, rfl⟩ := h
  exact finiteBox_isClosed fun j ↦ (hC j).isClosed

/-- **Example 1.2**: the nonnegative orthant `ℝⁿ₊ = [0, ∞)ⁿ` is a box. -/
theorem isBox_nonnegOrthant : IsBox {x : EuclideanSpace ℝ ι | ∀ j, 0 ≤ x j} :=
  ⟨fun _ ↦ Ici 0, fun _ ↦ isNonemptyClosedInterval_Ici 0, by ext x; simp⟩

/-- **Example 1.2**: `[0, ∞)^s × (-∞, ∞)^{n-s}`, where only the variables indexed by `s` must be
nonnegative, is a box. -/
theorem isBox_partialOrthant (s : Set ι) :
    IsBox {x : EuclideanSpace ℝ ι | ∀ j ∈ s, 0 ≤ x j} := by
  classical
  refine ⟨fun j ↦ if j ∈ s then Ici 0 else univ, fun j ↦ ?_, ?_⟩
  · by_cases hj : j ∈ s
    · simp only [hj, if_true]; exact isNonemptyClosedInterval_Ici 0
    · simp only [hj, if_false]; exact isNonemptyClosedInterval_univ
  · ext x
    simp only [mem_setOf_eq, mem_finiteBox]
    constructor
    · intro h j
      by_cases hj : j ∈ s
      · simp only [hj, if_true, mem_Ici]; exact h j hj
      · simp [hj]
    · intro h j hj
      simpa [hj] using h j

/-- **Example 1.2**: a degenerate interval `[cⱼ, cⱼ]` forces `xⱼ = cⱼ`. -/
theorem eq_of_mem_finiteBox_singleton {C : ι → Set ℝ} {x : EuclideanSpace ℝ ι} {j : ι} {c : ℝ}
    (hC : C j = Icc c c) (hx : x ∈ finiteBox C) : x j = c := by
  have := hx j
  rw [hC, Icc_self, mem_singleton_iff] at this
  exact this

end Boxes

/-! ## Example 1.3 -/

section PenaltiesBarriers

/-- **Example 1.3**: a penalty function for a constraint `fᵢ(x) ≤ 0`: zero for `t ≤ 0` and positive
for the violating values `t > 0`. -/
def IsInequalityPenalty (θ : ℝ → EReal) : Prop := (∀ t ≤ 0, θ t = 0) ∧ ∀ t > 0, 0 < θ t

/-- **Example 1.3**: a penalty function for a constraint `fᵢ(x) = 0`. -/
def IsEqualityPenalty (θ : ℝ → EReal) : Prop := θ 0 = 0 ∧ ∀ t ≠ 0, 0 < θ t

/-- **Example 1.3**: a barrier function for `fᵢ(x) ≤ 0`: `θ(t) = ∞` for `t ≥ 0` and
`θ(t) → ∞` as `t ↗ 0`. -/
def IsBarrier (θ : ℝ → EReal) : Prop := (∀ t ≥ 0, θ t = ⊤) ∧ Tendsto θ (𝓝[<] 0) (𝓝 ⊤)

/-- The linear penalty `θ(t) = λ t₊`. -/
def linearPenalty (lam t : ℝ) : EReal := ((lam * max t 0 : ℝ) : EReal)

/-- The quadratic penalty `θ(t) = ½ λ t₊²`. -/
def quadraticPenaltyFn (lam t : ℝ) : EReal := ((lam / 2 * max t 0 ^ 2 : ℝ) : EReal)

/-- The barrier `θ(t) = ε/|t|` for `t < 0`, `∞` for `t ≥ 0`. -/
def inverseBarrier (ε t : ℝ) : EReal := if t < 0 then ((ε / |t| : ℝ) : EReal) else ⊤

/-- The barrier `θ(t) = -ε log|t|` for `t < 0`, `∞` for `t ≥ 0`. -/
def logBarrier (ε t : ℝ) : EReal := if t < 0 then ((-ε * Real.log |t| : ℝ) : EReal) else ⊤

theorem isInequalityPenalty_linearPenalty {lam : ℝ} (hlam : 0 < lam) :
    IsInequalityPenalty (linearPenalty lam) := by
  refine ⟨fun t ht ↦ by simp [linearPenalty, max_eq_right ht], fun t ht ↦ ?_⟩
  simp only [linearPenalty, max_eq_left ht.le]
  exact EReal.coe_pos.2 (mul_pos hlam ht)

theorem isInequalityPenalty_quadraticPenaltyFn {lam : ℝ} (hlam : 0 < lam) :
    IsInequalityPenalty (quadraticPenaltyFn lam) := by
  refine ⟨fun t ht ↦ by simp [quadraticPenaltyFn, max_eq_right ht], fun t ht ↦ ?_⟩
  simp only [quadraticPenaltyFn, max_eq_left ht.le]
  exact EReal.coe_pos.2 (by positivity)

/-- **Example 1.3**: the penalty `0` for `t ≤ 0`, `∞` for `t > 0` is `δ_(-∞,0]`. -/
theorem isInequalityPenalty_indicatorVA : IsInequalityPenalty (indicatorVA (Iic (0 : ℝ))) :=
  ⟨fun t ht ↦ indicatorVA_apply_mem (show t ∈ Iic (0 : ℝ) from ht),
    fun t ht ↦ by
      rw [indicatorVA_apply_not_mem (show t ∉ Iic (0 : ℝ) from not_le.2 ht)]
      exact EReal.zero_lt_top⟩

/-- **Example 1.3**: `δ_(-∞,0]` is the limit of linear penalties as `λ → ∞`. -/
theorem tendsto_linearPenalty (t : ℝ) :
    Tendsto (fun lam ↦ linearPenalty lam t) atTop (𝓝 (indicatorVA (Iic (0 : ℝ)) t)) := by
  by_cases ht : t ≤ 0
  · rw [indicatorVA_apply_mem (show t ∈ Iic (0 : ℝ) from ht)]
    simp only [linearPenalty, max_eq_right ht, mul_zero, EReal.coe_zero]
    exact tendsto_const_nhds
  · rw [indicatorVA_apply_not_mem (show t ∉ Iic (0 : ℝ) from ht)]
    simp only [linearPenalty, max_eq_left (not_le.1 ht).le]
    exact EReal.tendsto_coe_nhds_top_iff.2 (tendsto_id.atTop_mul_const (not_le.1 ht))

/-- **Example 1.3**: `δ_(-∞,0]` is the limit of quadratic penalties as `λ → ∞`. -/
theorem tendsto_quadraticPenaltyFn (t : ℝ) :
    Tendsto (fun lam ↦ quadraticPenaltyFn lam t) atTop (𝓝 (indicatorVA (Iic (0 : ℝ)) t)) := by
  by_cases ht : t ≤ 0
  · rw [indicatorVA_apply_mem (show t ∈ Iic (0 : ℝ) from ht)]
    simp only [quadraticPenaltyFn, max_eq_right ht]
    simp
  · rw [indicatorVA_apply_not_mem (show t ∉ Iic (0 : ℝ) from ht)]
    simp only [quadraticPenaltyFn, max_eq_left (not_le.1 ht).le]
    refine EReal.tendsto_coe_nhds_top_iff.2 ?_
    have h : Tendsto (fun lam : ℝ ↦ lam * (t ^ 2 / 2)) atTop atTop :=
      tendsto_id.atTop_mul_const (by have := not_le.1 ht; positivity)
    refine h.congr fun lam ↦ ?_
    ring

/-- **Example 1.3**: `ε/|t|` (with `∞` for `t ≥ 0`) is a barrier for every `ε > 0`. -/
theorem isBarrier_inverseBarrier {ε : ℝ} (hε : 0 < ε) : IsBarrier (inverseBarrier ε) := by
  refine ⟨fun t ht ↦ by simp [inverseBarrier, not_lt.2 ht], ?_⟩
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), inverseBarrier ε t = ((ε / |t| : ℝ) : EReal) :=
    eventually_mem_nhdsWithin.mono fun t ht ↦ if_pos ht
  refine Tendsto.congr' (EventuallyEq.symm hev) (EReal.tendsto_coe_nhds_top_iff.2 ?_)
  have habs : Tendsto (fun t : ℝ ↦ |t|) (𝓝[<] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun t ht ↦
      show |t| ∈ Ioi 0 from abs_pos.2 (ne_of_lt (show t < 0 from ht))⟩
    have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 0))
    simpa using this
  exact (tendsto_inv_nhdsGT_zero.comp habs).const_mul_atTop hε |>.congr fun t ↦ by
    simp [div_eq_mul_inv]

/-- **Example 1.3**: `-ε log|t|` (with `∞` for `t ≥ 0`) is a barrier for every `ε > 0`. -/
theorem isBarrier_logBarrier {ε : ℝ} (hε : 0 < ε) : IsBarrier (logBarrier ε) := by
  refine ⟨fun t ht ↦ by simp [logBarrier, not_lt.2 ht], ?_⟩
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), logBarrier ε t = ((-ε * Real.log |t| : ℝ) : EReal) :=
    eventually_mem_nhdsWithin.mono fun t ht ↦ if_pos ht
  refine Tendsto.congr' (EventuallyEq.symm hev) (EReal.tendsto_coe_nhds_top_iff.2 ?_)
  have habs : Tendsto (fun t : ℝ ↦ |t|) (𝓝[<] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun t ht ↦
      show |t| ∈ Ioi 0 from abs_pos.2 (ne_of_lt (show t < 0 from ht))⟩
    have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 0))
    simpa using this
  have hlog : Tendsto (fun t : ℝ ↦ -Real.log |t|) (𝓝[<] 0) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp habs)
  exact (hlog.const_mul_atTop hε).congr fun t ↦ by ring

/-- **Example 1.3**: the penalized problem: minimize `f₀(x) + θ₁(f₁(x)) + ⋯ + θₘ(fₘ(x))` over
`x ∈ X`. -/
def penalizedObjective [Fintype ι] (f₀ : E → ℝ) (θs : ι → ℝ → EReal) (fs : ι → E → ℝ)
    (X : Set E) : E → EReal :=
  constrainedObjective (fun x ↦ (f₀ x : EReal) + ∑ i, θs i (fs i x)) X

/-- **Example 1.3**: with the infinite penalties `δ_(-∞,0]`, the penalized problem is the
constrained problem of Example 1.1 with inequality constraints only. -/
theorem penalizedObjective_indicatorVA [Fintype ι] (f₀ : E → ℝ) (fs : ι → E → ℝ) (X : Set E) :
    penalizedObjective f₀ (fun _ ↦ indicatorVA (Iic (0 : ℝ))) fs X =
      constrainedObjective (fun x ↦ (f₀ x : EReal)) (constraintSystemSet X fs univ ∅) := by
  classical
  funext x
  simp only [penalizedObjective, constrainedObjective, constraintSystemSet, mem_setOf_eq, mem_univ,
    true_implies, mem_empty_iff_false, false_implies, implies_true, and_true]
  by_cases hX : x ∈ X
  · by_cases hc : ∀ i, fs i x ≤ 0
    · have hsum : ∑ i, indicatorVA (Iic (0 : ℝ)) (fs i x) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ indicatorVA_apply_mem (show fs i x ∈ Iic (0 : ℝ) from hc i)
      rw [if_pos hX, if_pos ⟨hX, hc⟩, hsum, add_zero]
    · push_neg at hc
      obtain ⟨i, hi⟩ := hc
      have hsum : ∑ j, indicatorVA (Iic (0 : ℝ)) (fs j x) = ⊤ := by
        refine top_le_iff.1 ?_
        rw [← indicatorVA_apply_not_mem (C := Iic (0 : ℝ))
          (show fs i x ∉ Iic (0 : ℝ) from not_le.2 hi)]
        exact Finset.single_le_sum (f := fun j ↦ indicatorVA (Iic (0 : ℝ)) (fs j x))
          (fun j _ ↦ by
            change (0 : EReal) ≤ indicatorVA (Iic (0 : ℝ)) (fs j x)
            unfold indicatorVA; split_ifs <;> simp) (Finset.mem_univ i)
      have hnot : ¬ (∀ i, fs i x ≤ 0) := fun h ↦ absurd (h i) (not_le.2 hi)
      simp [hX, hnot, hsum]
  · simp [hX]

end PenaltiesBarriers

/-! ## Example 1.4 -/

section AbstractMinimization

/-- A problem of minimizing a finite function over a subset `C`: the set `C` and the values
`f₀ : E → ℝ`, normalized to `0` off `C`. -/
def FiniteConstrainedProblem (E : Type*) : Type _ :=
  {p : Set E × (E → ℝ) // ∀ x ∉ p.1, p.2 x = 0}

/-- The extended-real function `f` attached to a problem: `f₀` on `C`, `∞` off `C`. -/
def FiniteConstrainedProblem.objective (P : FiniteConstrainedProblem E) : E → EReal :=
  constrainedObjective (fun x ↦ (P.1.2 x : EReal)) P.1.1

theorem FiniteConstrainedProblem.objective_ne_bot (P : FiniteConstrainedProblem E) (x : E) :
    P.objective x ≠ ⊥ := by
  classical
  unfold objective constrainedObjective
  split_ifs <;> simp

/-- **Example 1.4** (principle of abstract minimization): problems of minimizing a finite function
over a subset of `ℝⁿ` correspond one-to-one with functions `f : ℝⁿ → ℝ̄` that never take the
value `-∞`. -/
def abstractMinimizationEquiv : FiniteConstrainedProblem E ≃ {f : E → EReal // ∀ x, f x ≠ ⊥} where
  toFun P := ⟨P.objective, P.objective_ne_bot⟩
  invFun f := ⟨(effectiveDomain f.1, fun x ↦ (f.1 x).toReal), fun x hx ↦ by
    have : f.1 x = ⊤ := by
      by_contra h
      exact hx (lt_top_iff_ne_top.2 h)
    simp [this]⟩
  left_inv P := by
    classical
    obtain ⟨⟨C, f₀⟩, hf₀⟩ := P
    have hdom : effectiveDomain (FiniteConstrainedProblem.objective ⟨(C, f₀), hf₀⟩) = C := by
      ext x
      simp only [mem_effectiveDomain_iff, FiniteConstrainedProblem.objective, constrainedObjective]
      by_cases hx : x ∈ C <;> simp [hx]
    apply Subtype.ext
    simp only
    refine Prod.ext hdom (funext fun x ↦ ?_)
    simp only [FiniteConstrainedProblem.objective, constrainedObjective]
    by_cases hx : x ∈ C
    · simp [hx]
    · have h0 : f₀ x = 0 := hf₀ x hx
      simp [hx, h0]
  right_inv f := by
    classical
    obtain ⟨f, hf⟩ := f
    apply Subtype.ext
    funext x
    simp only [FiniteConstrainedProblem.objective, constrainedObjective, mem_effectiveDomain_iff]
    by_cases hx : f x < ⊤
    · simp [hx, EReal.coe_toReal hx.ne (hf x)]
    · simp [not_lt.1 hx |> top_le_iff.1]

/-- **Example 1.4**: `dom f` is the set of feasible solutions. -/
theorem FiniteConstrainedProblem.effectiveDomain_objective (P : FiniteConstrainedProblem E) :
    effectiveDomain P.objective = P.1.1 := by
  classical
  ext x
  simp only [mem_effectiveDomain_iff, objective, constrainedObjective]
  by_cases hx : x ∈ P.1.1 <;> simp [hx]

/-- **Example 1.4**: `inf f` is the optimal value; it is `∞` exactly when there is no feasible
solution. -/
theorem FiniteConstrainedProblem.iInf_objective (P : FiniteConstrainedProblem E) :
    (⨅ x, P.objective x) = ⨅ x ∈ P.1.1, (P.1.2 x : EReal) ∧
      ((⨅ x, P.objective x) = ⊤ ↔ P.1.1 = ∅) :=
  ⟨iInf_constrainedObjective P.1.2 P.1.1, iInf_constrainedObjective_eq_top_iff P.1.2 P.1.1⟩

/-- **Example 1.4**: `argmin f` is the set of optimal solutions (empty when there is no feasible
solution). -/
theorem FiniteConstrainedProblem.argmin_objective (P : FiniteConstrainedProblem E) :
    argmin P.objective = {x ∈ P.1.1 | IsMinOn P.1.2 P.1.1 x} := by
  classical
  have hval : ∀ x, P.objective x = if x ∈ P.1.1 then (P.1.2 x : EReal) else ⊤ := fun x ↦ rfl
  ext x
  simp only [mem_argmin_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hx, hlt⟩
    have hxC : x ∈ P.1.1 := by
      by_contra h
      rw [hval, if_neg h] at hx
      exact (ne_of_lt hlt) hx.symm
    refine ⟨hxC, fun y hy ↦ ?_⟩
    have h1 : P.objective x ≤ P.objective y := hx ▸ iInf_le _ y
    rw [hval, hval, if_pos hxC, if_pos hy] at h1
    exact EReal.coe_le_coe_iff.1 h1
  · rintro ⟨hxC, hmin⟩
    have hx : P.objective x = (P.1.2 x : EReal) := by rw [hval, if_pos hxC]
    refine ⟨le_antisymm ?_ (iInf_le _ x), ?_⟩
    · refine le_iInf fun y ↦ ?_
      rw [hx, hval]
      split_ifs with hy
      · exact EReal.coe_le_coe_iff.2 (hmin hy)
      · exact le_top
    · exact lt_of_le_of_lt (iInf_le _ x) (by rw [hx]; exact EReal.coe_lt_top _)

end AbstractMinimization

end RW
