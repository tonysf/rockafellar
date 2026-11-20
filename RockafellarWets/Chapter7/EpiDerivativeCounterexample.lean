/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: A counterexample to a remark after Definition 7.23

The paragraph after Definition 7.23 asserts that "`f` is semidifferentiable
at `x̄` if and only if both `f` and `-f` are properly epi-differentiable at
`x̄`".  The forward implication holds
(`SemidifferentiableAt.properlyEpiDifferentiableAt` and
`SemidifferentiableAt.neg`), but the converse fails.

Take `f(x) = |x|` at rational `x` and `f(x) = -|x|` at irrational `x`.  At
`x̄ = 0` the difference quotients are `Δ_τ f(0)(w) = ±|w|`, the sign depending
on whether `τw` is rational.  Since irrational points are dense, the quotients
epi-converge to `-|w|`, a proper function; since rational points are dense, the
quotients of `-f` epi-converge to `-|w|` as well.  Yet along `w = 1` the
quotients take both values `1` and `-1` for arbitrarily small `τ`, so `f` is
not semidifferentiable at `0`.  What the book's appeal to 7.21 and 7.11 does
give is the corrected statement in which the epi-limit of `Δ_τ f(x̄)` and the
hypo-limit (`-` the epi-limit of `Δ_τ (-f)(x̄)`) coincide.
-/

import RockafellarWets.Chapter7.EpiDerivatives
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.Irrational

open Filter Set Topology Metric

namespace RW

/-! ### Negation preserves semidifferentiability -/

section Negation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem differenceQuotient_neg {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) (τ : ℝ)
    (w : E) :
    differenceQuotient (fun y ↦ -f y) x τ w = -differenceQuotient f x τ w := by
  show ((τ⁻¹ : ℝ) : EReal) * (-f (x + τ • w) - -f x) =
    -(((τ⁻¹ : ℝ) : EReal) * (f (x + τ • w) - f x))
  rw [hx, ← mul_neg]
  congr 1
  cases f (x + τ • w) with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_neg]
    congr 1
    ring

/-- If `f` has semiderivative `β` at `x̄` for `w`, then `-f` has semiderivative
`-β`. -/
theorem HasSemiderivative.neg {f : E → EReal} {x w : E} {β : EReal}
    (h : HasSemiderivative f x w β) : HasSemiderivative (fun y ↦ -f y) x w (-β) := by
  obtain ⟨hx1, hx2, hlim⟩ := h
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx2 hx1).symm
  refine ⟨?_, ?_, ?_⟩
  · simpa [EReal.neg_eq_bot_iff] using hx2
  · simpa [EReal.neg_eq_top_iff] using hx1
  · simp only [differenceQuotient_neg hxc]
    exact (continuous_neg.tendsto β).comp hlim

/-- The valid half of the remark after 7.23: semidifferentiability passes to
`-f`. -/
theorem SemidifferentiableAt.neg {f : E → EReal} {x : E} (hs : SemidifferentiableAt f x) :
    SemidifferentiableAt (fun y ↦ -f y) x := fun w ↦
  let ⟨β, hβ⟩ := hs w
  ⟨-β, hβ.neg⟩

end Negation

/-! ### The counterexample -/

open Classical in
/-- `|x|` at rational points and `-|x|` at irrational points. -/
noncomputable def rationalSignAbs (x : ℝ) : EReal :=
  if Irrational x then ((-|x| : ℝ) : EReal) else ((|x| : ℝ) : EReal)

theorem rationalSignAbs_of_irrational {x : ℝ} (hx : Irrational x) :
    rationalSignAbs x = ((-|x| : ℝ) : EReal) := by
  simp [rationalSignAbs, hx]

theorem rationalSignAbs_of_not_irrational {x : ℝ} (hx : ¬Irrational x) :
    rationalSignAbs x = ((|x| : ℝ) : EReal) := by
  simp [rationalSignAbs, hx]

theorem rationalSignAbs_zero : rationalSignAbs 0 = ((0 : ℝ) : EReal) := by
  rw [rationalSignAbs_of_not_irrational not_irrational_zero, abs_zero]

open Classical in
/-- The difference quotients of `rationalSignAbs` at `0`. -/
theorem differenceQuotient_rationalSignAbs {τ : ℝ} (hτ : 0 < τ) (w : ℝ) :
    differenceQuotient rationalSignAbs 0 τ w =
      if Irrational (τ * w) then ((-|w| : ℝ) : EReal) else ((|w| : ℝ) : EReal) := by
  have h0 : (0 : ℝ) + τ • w = τ * w := by rw [zero_add, smul_eq_mul]
  by_cases hirr : Irrational (τ * w)
  · rw [if_pos hirr, differenceQuotient_eq_coe rationalSignAbs_zero
      (by rw [h0, rationalSignAbs_of_irrational hirr])]
    congr 1
    rw [abs_mul, abs_of_pos hτ, sub_zero]
    field_simp
  · rw [if_neg hirr, differenceQuotient_eq_coe rationalSignAbs_zero
      (by rw [h0, rationalSignAbs_of_not_irrational hirr])]
    congr 1
    rw [abs_mul, abs_of_pos hτ, sub_zero]
    field_simp

open Classical in
/-- The difference quotients of `-rationalSignAbs` at `0`. -/
theorem differenceQuotient_neg_rationalSignAbs {τ : ℝ} (hτ : 0 < τ) (w : ℝ) :
    differenceQuotient (fun y ↦ -rationalSignAbs y) 0 τ w =
      if Irrational (τ * w) then ((|w| : ℝ) : EReal) else ((-|w| : ℝ) : EReal) := by
  rw [differenceQuotient_neg rationalSignAbs_zero, differenceQuotient_rationalSignAbs hτ]
  split_ifs <;> simp

/-- Near any `w`, for any `τ > 0`, both kinds of points `τw'` occur. -/
theorem exists_irrational_mul_near {τ : ℝ} (hτ : 0 < τ) (w : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w', |w' - w| < δ ∧ Irrational (τ * w') := by
  obtain ⟨s, hsirr, hs⟩ := dense_irrational.exists_between
    (show τ * (w - δ) < τ * (w + δ) by nlinarith)
  refine ⟨s / τ, ?_, by rwa [mul_div_cancel₀ s hτ.ne']⟩
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hτ]
    nlinarith [hs.1]
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hτ]
    nlinarith [hs.2]

theorem exists_rational_mul_near {τ : ℝ} (hτ : 0 < τ) (w : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w', |w' - w| < δ ∧ ¬Irrational (τ * w') := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show τ * (w - δ) < τ * (w + δ) by nlinarith)
  refine ⟨(q : ℝ) / τ, ?_, by rw [mul_div_cancel₀ _ hτ.ne']; exact Rat.not_irrational q⟩
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hτ]
    nlinarith [hq1]
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hτ]
    nlinarith [hq2]

/-- The common epi-limit `w ↦ -|w|`. -/
noncomputable def negAbs (w : ℝ) : EReal := ((-|w| : ℝ) : EReal)

theorem isClosed_epigraph_negAbs : IsClosed (epigraph negAbs) := by
  have h : epigraph negAbs = {p : ℝ × ℝ | -|p.1| ≤ p.2} := by
    ext ⟨w, α⟩
    rw [mem_epigraph_iff, negAbs, EReal.coe_le_coe_iff]
    rfl
  rw [h]
  exact isClosed_le (continuous_abs.comp continuous_fst).neg continuous_snd

theorem isProper_negAbs : IsProper negAbs :=
  ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩

/-- A family of epigraphs that eventually lies above `-|w|`, and that near every
point of `epi(-|·|)` contains a point at the lower bound, converges to
`epi(-|·|)`. -/
theorem pkConvergesAlong_epigraph_negAbs {g : ℝ → ℝ → EReal}
    (hlow : ∀ τ > 0, ∀ w, negAbs w ≤ g τ w)
    (hhit : ∀ τ > 0, ∀ w, ∀ δ > 0, ∃ w', |w' - w| < δ ∧ g τ w' = negAbs w') :
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (g τ)) (epigraph negAbs) := by
  have hinner : epigraph negAbs ⊆
      innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (g τ)) := by
    rintro ⟨w, α⟩ hwα N hN
    rw [mem_epigraph_iff, negAbs, EReal.coe_le_coe_iff] at hwα
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hN
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    obtain ⟨w', hw', hgw'⟩ := hhit τ hτ w δ hδ
    refine ⟨(w', α + |w' - w|), ?_, hball ?_⟩
    · show g τ w' ≤ ((α + |w' - w| : ℝ) : EReal)
      rw [hgw', negAbs, EReal.coe_le_coe_iff]
      have := abs_sub_abs_le_abs_sub w w'
      rw [abs_sub_comm w w'] at this
      linarith
    · rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, add_sub_cancel_left,
        abs_abs]
      exact ⟨hw', hw'⟩
  have houter : outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (g τ)) ⊆
      epigraph negAbs := by
    intro p hp
    by_contra hnot
    have hopen : (epigraph negAbs)ᶜ ∈ 𝓝 p := isClosed_epigraph_negAbs.isOpen_compl.mem_nhds hnot
    obtain ⟨τ, ⟨q, hq, hqc⟩, hτ⟩ := ((hp _ hopen).and_eventually self_mem_nhdsWithin).exists
    exact hqc ((hlow τ hτ q.1).trans hq)
  have hsub := innerSetLimitAlong_subset_outerSetLimitAlong
    (l := 𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (g τ))
  exact ⟨Subset.antisymm (hsub.trans houter) hinner,
    Subset.antisymm houter (hinner.trans hsub)⟩

/-- `rationalSignAbs` is properly epi-differentiable at `0`, with epi-derivative
`-|w|`. -/
theorem properlyEpiDifferentiableAt_rationalSignAbs :
    ProperlyEpiDifferentiableAt rationalSignAbs 0 := by
  refine ⟨by rw [rationalSignAbs_zero]; exact EReal.coe_ne_bot _,
    by rw [rationalSignAbs_zero]; exact EReal.coe_ne_top _, negAbs, isProper_negAbs, ?_⟩
  apply pkConvergesAlong_epigraph_negAbs
  · intro τ hτ w
    rw [differenceQuotient_rationalSignAbs hτ]
    split_ifs
    · exact le_rfl
    · exact EReal.coe_le_coe_iff.2 (by linarith [abs_nonneg w])
  · intro τ hτ w δ hδ
    obtain ⟨w', hw', hirr⟩ := exists_irrational_mul_near hτ w hδ
    exact ⟨w', hw', by rw [differenceQuotient_rationalSignAbs hτ, if_pos hirr]; rfl⟩

/-- `-rationalSignAbs` is properly epi-differentiable at `0`, with
epi-derivative `-|w|`. -/
theorem properlyEpiDifferentiableAt_neg_rationalSignAbs :
    ProperlyEpiDifferentiableAt (fun y ↦ -rationalSignAbs y) 0 := by
  refine ⟨by simp [rationalSignAbs_zero], by simp [rationalSignAbs_zero], negAbs,
    isProper_negAbs, ?_⟩
  apply pkConvergesAlong_epigraph_negAbs
  · intro τ hτ w
    rw [differenceQuotient_neg_rationalSignAbs hτ]
    split_ifs
    · exact EReal.coe_le_coe_iff.2 (by linarith [abs_nonneg w])
    · exact le_rfl
  · intro τ hτ w δ hδ
    obtain ⟨w', hw', hrat⟩ := exists_rational_mul_near hτ w hδ
    exact ⟨w', hw', by rw [differenceQuotient_neg_rationalSignAbs hτ, if_neg hrat]; rfl⟩

/-- `rationalSignAbs` is not semidifferentiable at `0`: along `w = 1` the
difference quotients equal `1` at rational `τ` and `-1` at irrational `τ`. -/
theorem not_semidifferentiableAt_rationalSignAbs :
    ¬SemidifferentiableAt rationalSignAbs 0 := by
  intro hs
  obtain ⟨β, hβ⟩ := hs 1
  have hray := hβ.hasOneSidedDirDeriv.2.2
  have hτ0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun n ↦ mem_Ioi.2 (by positivity))
  have hσ0 : Tendsto (fun n : ℕ ↦ Real.sqrt 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n ↦ mem_Ioi.2 (by positivity))
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.sqrt 2)
  have hrat : ∀ n : ℕ, ¬Irrational (1 / ((n : ℝ) + 1) * 1) := by
    intro n
    have : (1 / ((n : ℝ) + 1) * 1) = ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) := by push_cast; ring
    rw [this]
    exact Rat.not_irrational _
  have hirr : ∀ n : ℕ, Irrational (Real.sqrt 2 * (1 / ((n : ℝ) + 1)) * 1) := by
    intro n
    have h1 : Real.sqrt 2 * (1 / ((n : ℝ) + 1)) * 1 = Real.sqrt 2 / ((n + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [h1]
    exact irrational_sqrt_two.div_natCast (Nat.succ_ne_zero n)
  have h1 : Tendsto (fun n : ℕ ↦ differenceQuotient rationalSignAbs 0 (1 / ((n : ℝ) + 1)) 1)
      atTop (𝓝 ((1 : ℝ) : EReal)) := by
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [differenceQuotient_rationalSignAbs (τ := 1 / ((n : ℝ) + 1)) (by positivity),
      if_neg (hrat n), abs_one]
  have h2 : Tendsto (fun n : ℕ ↦
      differenceQuotient rationalSignAbs 0 (Real.sqrt 2 * (1 / ((n : ℝ) + 1))) 1)
      atTop (𝓝 ((-1 : ℝ) : EReal)) := by
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [differenceQuotient_rationalSignAbs (τ := Real.sqrt 2 * (1 / ((n : ℝ) + 1)))
      (by positivity), if_pos (hirr n), abs_one]
  have hβ1 := tendsto_nhds_unique (hray.comp hτ0) h1
  have hβ2 := tendsto_nhds_unique (hray.comp hσ0) h2
  rw [hβ1] at hβ2
  have := EReal.coe_injective hβ2
  norm_num at this

/-- The remark after Definition 7.23 ("`f` is semidifferentiable at `x̄` if
and only if both `f` and `-f` are properly epi-differentiable at `x̄`") fails in
the converse direction. -/
theorem not_semidifferentiable_of_properlyEpiDifferentiable_neg :
    ProperlyEpiDifferentiableAt rationalSignAbs 0 ∧
      ProperlyEpiDifferentiableAt (fun y ↦ -rationalSignAbs y) 0 ∧
      ¬SemidifferentiableAt rationalSignAbs 0 :=
  ⟨properlyEpiDifferentiableAt_rationalSignAbs,
    properlyEpiDifferentiableAt_neg_rationalSignAbs, not_semidifferentiableAt_rationalSignAbs⟩

end RW
