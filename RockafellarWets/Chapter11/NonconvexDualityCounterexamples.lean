/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Counterexamples for duality without convexity

Three integrands on `ℝ × ℝ` show that the adaptations of Theorems 11.59 and
11.61 cannot be dropped.

* `f(x,u) = c(x) + δ_{x}(u)`, with `c(0) = 1` and `c = 0` elsewhere, is a
  dualizing parameterization that is level-bounded in `x` locally uniformly
  in `u`, but it is not jointly lsc and the proximal augmented dual has a
  duality gap.
* `f = δ_{\{0\} × [1,∞)}` gives an infeasible problem for which the local
  criterion 11(33) holds at `ȳ = 0` although no exact penalty exists.
* `f = δ_{\{(0,1)\}}` with the augmenting function `δ_{\{0\}}` makes every
  augmented Lagrangian value infinite, so the saddle condition of 11(31)
  holds while the primal problem has no minimizer.
-/
import RockafellarWets.Chapter11.ExactPenaltyExamples

open Set Filter Topology Metric
open scoped InnerProductSpace
namespace RW
noncomputable section

/-- Level boundedness in `x`, locally uniformly in `u`, when every finite
value occurs on a bounded set of `x` controlled by `u`. -/
theorem isParametricallyLevelBounded_of_subset {f : WithLp 2 (ℝ × ℝ) → EReal}
    (h : ∀ q : WithLp 2 (ℝ × ℝ), f q < ⊤ → |q.fst| ≤ |q.snd| + 1) :
    IsParametricallyLevelBounded f := by
  intro uBar α
  refine ⟨1, one_pos, (isBounded_closedBall (x := ((0 : ℝ), (0 : ℝ)))
    (r := |uBar| + 2)).subset ?_⟩
  rintro ⟨x, u⟩ ⟨⟨-, hu⟩, hα⟩
  have hu' : |u - uBar| ≤ 1 := by simpa [Real.dist_eq] using hu
  have hlt : f (WithLp.toLp 2 (x, u)) < ⊤ :=
    lt_of_le_of_lt (show f (WithLp.toLp 2 (x, u)) ≤ (α : EReal) from hα) (EReal.coe_lt_top α)
  have hx := h _ hlt
  change |x| ≤ |u| + 1 at hx
  have hu2 : |u| ≤ |uBar| + 1 := by
    have := abs_sub_abs_le_abs_sub u uBar
    linarith
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
  exact max_le (by linarith) (by linarith)

section DualityGap

/-- `f(x,u) = c(x) + δ_{x}(u)` with `c(0) = 1` and `c(x) = 0` for `x ≠ 0`. -/
def diagonalGapIntegrand : WithLp 2 (ℝ × ℝ) → EReal :=
  fun q ↦ ((if q.fst = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {q.fst} q.snd

theorem diagonalGapIntegrand_nonneg (q : WithLp 2 (ℝ × ℝ)) : 0 ≤ diagonalGapIntegrand q := by
  unfold diagonalGapIntegrand
  have hc : (0 : EReal) ≤ ((if q.fst = 0 then 1 else 0 : ℝ) : EReal) := by
    split_ifs <;> norm_num
  by_cases h : q.snd ∈ ({q.fst} : Set ℝ)
  · rw [indicatorVA_apply_mem h, add_zero]
    exact hc
  · rw [indicatorVA_apply_not_mem h, EReal.coe_add_top]
    exact le_top

theorem diagonalGapIntegrand_isDualizing :
    IsDualizingParameterization (primalObjective diagonalGapIntegrand) diagonalGapIntegrand := by
  refine ⟨rfl, ⟨⟨WithLp.toLp 2 (1, 1), ?_⟩, fun q ↦ ?_⟩, fun x ↦ ?_, fun x ↦ ?_⟩
  · change ((if (1 : ℝ) = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {(1 : ℝ)} (1 : ℝ) < ⊤
    rw [indicatorVA_apply_mem (mem_singleton 1), add_zero]
    exact EReal.coe_lt_top _
  · exact EReal.bot_lt_zero.trans_le (diagonalGapIntegrand_nonneg q)
  · change LowerSemicontinuous fun u : ℝ ↦
      ((if x = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {x} u
    exact lowerSemicontinuous_const.add' (lowerSemicontinuous_indicatorVA isClosed_singleton)
      fun u ↦ EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  · rintro ⟨u₁, a₁⟩ h₁ ⟨u₂, a₂⟩ h₂ s t hs ht hst
    change ((if x = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {x} u₁ ≤ (a₁ : EReal) at h₁
    change ((if x = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {x} u₂ ≤ (a₂ : EReal) at h₂
    have hmem : ∀ (u a : ℝ), ((if x = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {x} u ≤
        (a : EReal) → u = x ∧ (if x = 0 then 1 else 0 : ℝ) ≤ a := by
      intro u a h
      by_cases hu : u ∈ ({x} : Set ℝ)
      · rw [indicatorVA_apply_mem hu, add_zero, EReal.coe_le_coe_iff] at h
        exact ⟨hu, h⟩
      · rw [indicatorVA_apply_not_mem hu, EReal.coe_add_top, top_le_iff] at h
        exact absurd h (EReal.coe_ne_top _)
    obtain ⟨hu₁, hc₁⟩ := hmem u₁ a₁ h₁
    obtain ⟨hu₂, hc₂⟩ := hmem u₂ a₂ h₂
    change ((if x = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {x} (s • u₁ + t • u₂) ≤
      ((s * a₁ + t * a₂ : ℝ) : EReal)
    rw [hu₁, hu₂, ← add_smul, hst, one_smul, indicatorVA_apply_mem (mem_singleton x), add_zero,
      EReal.coe_le_coe_iff]
    generalize (if x = 0 then 1 else 0 : ℝ) = c at hc₁ hc₂ ⊢
    have e1 := mul_le_mul_of_nonneg_left hc₁ hs
    have e2 := mul_le_mul_of_nonneg_left hc₂ ht
    have e3 : c = s * c + t * c := by rw [← add_mul, hst, one_mul]
    linarith

theorem diagonalGapIntegrand_isParametricallyLevelBounded :
    IsParametricallyLevelBounded diagonalGapIntegrand := by
  refine isParametricallyLevelBounded_of_subset fun q hq ↦ ?_
  unfold diagonalGapIntegrand at hq
  by_cases h : q.snd ∈ ({q.fst} : Set ℝ)
  · rw [mem_singleton_iff] at h
    rw [h]
    linarith
  · rw [indicatorVA_apply_not_mem h, EReal.coe_add_top] at hq
    exact absurd hq (lt_irrefl _)

/-- **Theorem 11.59** needs joint lower semicontinuity: `diagonalGapIntegrand` is a
dualizing parameterization, level-bounded in `x` locally uniformly in `u`, with
a finite proximal augmented dual value, yet `inf φ = 1` exceeds every value of
the augmented dual objective, so the integrand cannot be lsc. -/
theorem duality_gap_of_not_lowerSemicontinuous :
    IsDualizingParameterization (primalObjective diagonalGapIntegrand) diagonalGapIntegrand ∧
    IsParametricallyLevelBounded diagonalGapIntegrand ∧
    (∃ (y : ℝ) (r : ℝ), 0 < r ∧
      ⊥ < augmentedDualObjective diagonalGapIntegrand (proximalAugmentingFunction ℝ) y r) ∧
    (⨆ (y : ℝ) (r : ℝ) (_ : 0 < r),
      augmentedDualObjective diagonalGapIntegrand (proximalAugmentingFunction ℝ) y r) <
      ⨅ x, primalObjective diagonalGapIntegrand x ∧
    ¬ LowerSemicontinuous diagonalGapIntegrand := by
  have hσ := isAugmentingFunction_proximal (P := ℝ)
  have hdp := diagonalGapIntegrand_isDualizing
  have hlb := diagonalGapIntegrand_isParametricallyLevelBounded
  have hψ : ∃ (y : ℝ) (r : ℝ), 0 < r ∧
      ⊥ < augmentedDualObjective diagonalGapIntegrand (proximalAugmentingFunction ℝ) y r := by
    refine ⟨0, 1, one_pos, EReal.bot_lt_zero.trans_le (le_iInf fun x ↦ le_iInf fun u ↦ ?_)⟩
    rw [inner_zero_left, EReal.coe_zero, sub_zero]
    exact add_nonneg (diagonalGapIntegrand_nonneg _)
      (EReal.mul_nonneg (EReal.coe_nonneg.mpr zero_le_one) (hσ.nonneg u))
  have hinf : (⨅ x, primalObjective diagonalGapIntegrand x) = 1 := by
    apply le_antisymm
    · refine (iInf_le _ 0).trans (le_of_eq ?_)
      change ((if (0 : ℝ) = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {(0 : ℝ)} (0 : ℝ) = 1
      rw [if_pos rfl, indicatorVA_apply_mem (mem_singleton 0), add_zero, EReal.coe_one]
    · refine le_iInf fun x ↦ ?_
      change (1 : EReal) ≤ ((if x = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {x} 0
      by_cases hx : x = 0
      · rw [hx, if_pos rfl, indicatorVA_apply_mem (mem_singleton 0), add_zero, EReal.coe_one]
      · rw [indicatorVA_apply_not_mem (fun h ↦ hx (mem_singleton_iff.mp h).symm),
          EReal.coe_add_top]
        exact le_top
  have hsup : (⨆ (y : ℝ) (r : ℝ) (_ : 0 < r),
      augmentedDualObjective diagonalGapIntegrand (proximalAugmentingFunction ℝ) y r) ≤ 0 := by
    refine iSup_le fun y ↦ iSup₂_le fun r hr ↦ ?_
    rw [← EReal.le_of_forall_lt_iff_le]
    intro δ hδ
    have hδ' : (0 : ℝ) < δ := EReal.coe_pos.mp hδ
    set t := min 1 (δ / (r + |y| + 1)) with htdef
    have ht0 : 0 < t := lt_min one_pos (div_pos hδ' (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htδ : t * (r + |y| + 1) ≤ δ := by
      have := min_le_right 1 (δ / (r + |y| + 1))
      rw [le_div_iff₀ (by positivity)] at this
      exact this
    refine (iInf_le _ t).trans ((iInf_le _ t).trans ?_)
    change ((if t = 0 then 1 else 0 : ℝ) : EReal) + indicatorVA {t} t +
      (r : EReal) * ((‖t‖ ^ 2 / 2 : ℝ) : EReal) - (⟪y, t⟫_ℝ : EReal) ≤ (δ : EReal)
    rw [if_neg ht0.ne', indicatorVA_apply_mem (mem_singleton t), add_zero, EReal.coe_zero,
      zero_add, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_le_coe_iff, Real.norm_eq_abs,
      abs_of_pos ht0]
    have hin : ⟪y, t⟫_ℝ = y * t := by simp [mul_comm]
    rw [hin]
    have h1 : t ^ 2 ≤ t := by nlinarith
    have h2 : -(y * t) ≤ |y| * t := by nlinarith [neg_abs_le y]
    nlinarith
  have hgap : (⨆ (y : ℝ) (r : ℝ) (_ : 0 < r),
      augmentedDualObjective diagonalGapIntegrand (proximalAugmentingFunction ℝ) y r) <
      ⨅ x, primalObjective diagonalGapIntegrand x := by
    rw [hinf]
    exact hsup.trans_lt (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1))
  refine ⟨hdp, hlb, hψ, hgap, fun hl ↦ ?_⟩
  have heq := iInf_primalObjective_eq_iSup_augmentedDualObjective hdp hl hlb hσ hψ
  exact absurd heq hgap.ne'

end DualityGap

section Infeasible

/-- `f = δ_C` for `C = {(x,u) | x = 0, u ≥ 1}`: no feasible point at `u = 0`. -/
def infeasibleIntegrand : WithLp 2 (ℝ × ℝ) → EReal :=
  indicatorVA {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ 1 ≤ q.snd}

theorem isClosed_infeasibleSet :
    IsClosed {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ 1 ≤ q.snd} :=
  (isClosed_eq (WithLp.continuous_fst 2 ℝ ℝ) continuous_const).inter
    (isClosed_le continuous_const (WithLp.continuous_snd 2 ℝ ℝ))

theorem infeasibleIntegrand_isDualizing :
    IsDualizingParameterization (primalObjective infeasibleIntegrand) infeasibleIntegrand := by
  refine ⟨rfl, ⟨⟨WithLp.toLp 2 (0, 1), ?_⟩, fun q ↦ ?_⟩, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [infeasibleIntegrand, indicatorVA_apply_mem (show (WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))) ∈
      {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ 1 ≤ q.snd} from ⟨rfl, le_rfl⟩)]
    exact EReal.zero_lt_top
  · unfold infeasibleIntegrand indicatorVA
    split_ifs
    · exact EReal.bot_lt_zero
    · exact bot_lt_top
  · exact (lowerSemicontinuous_indicatorVA isClosed_infeasibleSet).comp (by fun_prop)
  · rintro ⟨u₁, a₁⟩ h₁ ⟨u₂, a₂⟩ h₂ s t hs ht hst
    have hmem : ∀ (u a : ℝ), infeasibleIntegrand (WithLp.toLp 2 (x, u)) ≤ (a : EReal) →
        x = 0 ∧ 1 ≤ u ∧ 0 ≤ a := by
      intro u a h
      unfold infeasibleIntegrand at h
      by_cases hu : WithLp.toLp 2 (x, u) ∈ {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ 1 ≤ q.snd}
      · rw [indicatorVA_apply_mem hu] at h
        exact ⟨hu.1, hu.2, EReal.coe_nonneg.mp h⟩
      · rw [indicatorVA_apply_not_mem hu, top_le_iff] at h
        exact absurd h (EReal.coe_ne_top _)
    obtain ⟨hx, hu₁, ha₁⟩ := hmem u₁ a₁ h₁
    obtain ⟨-, hu₂, ha₂⟩ := hmem u₂ a₂ h₂
    change infeasibleIntegrand (WithLp.toLp 2 (x, s • u₁ + t • u₂)) ≤ ((s * a₁ + t * a₂ : ℝ) : EReal)
    have hm : WithLp.toLp 2 (x, s • u₁ + t • u₂) ∈
        {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ 1 ≤ q.snd} := by
      refine ⟨hx, ?_⟩
      change 1 ≤ s * u₁ + t * u₂
      nlinarith
    rw [infeasibleIntegrand, indicatorVA_apply_mem hm]
    exact EReal.coe_nonneg.mpr (by positivity)

/-- **Theorem 11.61** needs a feasible problem for the local criterion: for
`f = δ_{\{0\} × [1,∞)}` with the proximal augmenting function, all hypotheses of
Theorem 11.59 hold and 11(33) holds at `ȳ = 0` near `0`, but `0` supports no
exact penalty representation. -/
theorem localCriterion_without_exactPenalty :
    IsDualizingParameterization (primalObjective infeasibleIntegrand) infeasibleIntegrand ∧
    LowerSemicontinuous infeasibleIntegrand ∧
    IsParametricallyLevelBounded infeasibleIntegrand ∧
    (∃ (y : ℝ) (r : ℝ), 0 < r ∧
      ⊥ < augmentedDualObjective infeasibleIntegrand (proximalAugmentingFunction ℝ) y r) ∧
    (∃ W ∈ 𝓝 (0 : ℝ), ∃ rh : ℝ, 0 < rh ∧ ∀ u ∈ W,
      parametricValue infeasibleIntegrand 0 + (⟪(0 : ℝ), u⟫_ℝ : EReal) ≤
        parametricValue infeasibleIntegrand u + (rh : EReal) * proximalAugmentingFunction ℝ u) ∧
    ¬ SupportsExactPenaltyRepresentation infeasibleIntegrand (proximalAugmentingFunction ℝ) 0 := by
  have hσ := isAugmentingFunction_proximal (P := ℝ)
  have hnonneg : ∀ q, 0 ≤ infeasibleIntegrand q := fun q ↦ by
    unfold infeasibleIntegrand indicatorVA
    split_ifs
    · exact le_rfl
    · exact le_top
  have htop : ∀ x u : ℝ, u < 1 → infeasibleIntegrand (WithLp.toLp 2 (x, u)) = ⊤ :=
    fun x u hu ↦ indicatorVA_apply_not_mem fun h ↦ (not_le.mpr hu) h.2
  refine ⟨infeasibleIntegrand_isDualizing, lowerSemicontinuous_indicatorVA isClosed_infeasibleSet,
    isParametricallyLevelBounded_of_subset fun q hq ↦ ?_, ⟨0, 1, one_pos, ?_⟩,
    ⟨Iio 1, Iio_mem_nhds one_pos, 1, one_pos, fun u hu ↦ ?_⟩, ?_⟩
  · by_contra hx
    have hq0 : q.fst ≠ 0 := fun h ↦ by rw [h, abs_zero] at hx; linarith [abs_nonneg q.snd]
    have := indicatorVA_apply_not_mem (C := {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ 1 ≤ q.snd})
      (x := q) fun h ↦ hq0 h.1
    rw [infeasibleIntegrand, this] at hq
    exact lt_irrefl _ hq
  · refine EReal.bot_lt_zero.trans_le (le_iInf fun x ↦ le_iInf fun u ↦ ?_)
    rw [inner_zero_left, EReal.coe_zero, sub_zero]
    exact add_nonneg (hnonneg _)
      (EReal.mul_nonneg (EReal.coe_nonneg.mpr zero_le_one) (hσ.nonneg u))
  · have hp : parametricValue infeasibleIntegrand u = ⊤ :=
      top_le_iff.mp (le_iInf fun x ↦ (htop x u hu).ge)
    rw [hp, EReal.top_add_of_ne_bot (hσ.coe_mul_ne_bot zero_le_one u)]
    exact le_top
  · rintro ⟨rb, hrb, hpen⟩
    have h := (hpen (rb + 1) (by linarith)).1
    have hinf : (⨅ x, primalObjective infeasibleIntegrand x) = ⊤ :=
      top_le_iff.mp (le_iInf fun x ↦ (htop x 0 one_pos).ge)
    have hle : (⨅ x, augmentedLagrangian infeasibleIntegrand (proximalAugmentingFunction ℝ) x 0
        (rb + 1)) ≤ (((rb + 1) * (1 / 2) : ℝ) : EReal) := by
      refine (iInf_le _ 0).trans ((iInf_le _ 1).trans (le_of_eq ?_))
      rw [infeasibleIntegrand, indicatorVA_apply_mem (show (WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))) ∈
        {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ 1 ≤ q.snd} from ⟨rfl, le_rfl⟩), zero_add,
        inner_zero_left, EReal.coe_zero, sub_zero]
      change ((rb + 1 : ℝ) : EReal) * ((‖(1 : ℝ)‖ ^ 2 / 2 : ℝ) : EReal) = _
      rw [← EReal.coe_mul, norm_one]
      norm_num
    rw [← h, hinf, top_le_iff] at hle
    exact EReal.coe_ne_top _ hle

end Infeasible

section InfiniteSaddle

/-- The augmenting function `δ_{\{0\}}` on `ℝ`. -/
theorem isAugmentingFunction_indicator_zero : IsAugmentingFunction (indicatorVA ({0} : Set ℝ)) where
  isProper := ⟨⟨0, by rw [indicatorVA_apply_mem (mem_singleton 0)]; exact EReal.zero_lt_top⟩,
    fun u ↦ by unfold indicatorVA; split_ifs; exacts [EReal.bot_lt_zero, bot_lt_top]⟩
  lowerSemicontinuous := lowerSemicontinuous_indicatorVA isClosed_singleton
  convex := by
    rintro ⟨u₁, a₁⟩ h₁ ⟨u₂, a₂⟩ h₂ s t hs ht hst
    have hmem : ∀ (u a : ℝ), indicatorVA ({0} : Set ℝ) u ≤ (a : EReal) → u = 0 ∧ 0 ≤ a := by
      intro u a h
      by_cases hu : u ∈ ({0} : Set ℝ)
      · rw [indicatorVA_apply_mem hu] at h
        exact ⟨hu, EReal.coe_nonneg.mp h⟩
      · rw [indicatorVA_apply_not_mem hu, top_le_iff] at h
        exact absurd h (EReal.coe_ne_top _)
    obtain ⟨rfl, ha₁⟩ := hmem u₁ a₁ h₁
    obtain ⟨rfl, ha₂⟩ := hmem u₂ a₂ h₂
    change indicatorVA ({0} : Set ℝ) (s • (0 : ℝ) + t • (0 : ℝ)) ≤ ((s * a₁ + t * a₂ : ℝ) : EReal)
    rw [smul_zero, smul_zero, add_zero, indicatorVA_apply_mem (mem_singleton 0)]
    exact EReal.coe_nonneg.mpr (by positivity)
  zero := indicatorVA_apply_mem (mem_singleton 0)
  pos := fun u hu ↦ by
    rw [indicatorVA_apply_not_mem (fun h ↦ hu (mem_singleton_iff.mp h))]
    exact EReal.zero_lt_top

/-- `f = δ_{\{(0,1)\}}`: the primal problem `φ = f(·,0)` is infeasible. -/
def pointIntegrand : WithLp 2 (ℝ × ℝ) → EReal :=
  indicatorVA {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ q.snd = 1}

/-- **Theorem 11.59**, 11(31) needs a finite saddle value: with `f = δ_{\{(0,1)\}}`
and the augmenting function `δ_{\{0\}}`, all hypotheses of Theorem 11.59 hold and
`(0, 0, 1)` satisfies the saddle condition with value `∞`, but the infeasible
primal problem has no minimizer. -/
theorem saddle_condition_without_minimizer :
    IsDualizingParameterization (primalObjective pointIntegrand) pointIntegrand ∧
    LowerSemicontinuous pointIntegrand ∧
    IsParametricallyLevelBounded pointIntegrand ∧
    (∃ (y : ℝ) (r : ℝ), 0 < r ∧
      ⊥ < augmentedDualObjective pointIntegrand (indicatorVA ({0} : Set ℝ)) y r) ∧
    (⨅ x, augmentedLagrangian pointIntegrand (indicatorVA ({0} : Set ℝ)) x 0 1) =
      augmentedLagrangian pointIntegrand (indicatorVA ({0} : Set ℝ)) 0 0 1 ∧
    augmentedLagrangian pointIntegrand (indicatorVA ({0} : Set ℝ)) 0 0 1 =
      ⨆ (y : ℝ) (r : ℝ) (_ : 0 < r),
        augmentedLagrangian pointIntegrand (indicatorVA ({0} : Set ℝ)) 0 y r ∧
    (0 : ℝ) ∉ argmin (primalObjective pointIntegrand) := by
  set S := {q : WithLp 2 (ℝ × ℝ) | q.fst = 0 ∧ q.snd = 1} with hSdef
  have hS : IsClosed S := (isClosed_eq (WithLp.continuous_fst 2 ℝ ℝ) continuous_const).inter
    (isClosed_eq (WithLp.continuous_snd 2 ℝ ℝ) continuous_const)
  have hσ := isAugmentingFunction_indicator_zero
  have htop0 : ∀ x : ℝ, pointIntegrand (WithLp.toLp 2 (x, 0)) = ⊤ :=
    fun x ↦ indicatorVA_apply_not_mem fun h ↦ zero_ne_one h.2
  have hnb : ∀ q, pointIntegrand q ≠ ⊥ := fun q ↦ by
    unfold pointIntegrand indicatorVA
    split_ifs
    · exact EReal.zero_ne_bot
    · exact top_ne_bot
  -- every augmented Lagrangian value is `∞`
  have hL : ∀ x y : ℝ, ∀ r : ℝ, 0 < r →
      augmentedLagrangian pointIntegrand (indicatorVA ({0} : Set ℝ)) x y r = ⊤ := by
    intro x y r hr
    refine top_le_iff.mp (le_iInf fun u ↦ ?_)
    by_cases hu : u = 0
    · subst hu
      rw [htop0, EReal.top_add_of_ne_bot (hσ.coe_mul_ne_bot hr.le 0), EReal.top_sub_coe]
    · rw [indicatorVA_apply_not_mem (fun h ↦ hu (mem_singleton_iff.mp h)),
        EReal.coe_mul_top_of_pos hr, EReal.add_top_of_ne_bot (hnb _), EReal.top_sub_coe]
  refine ⟨⟨rfl, ⟨⟨WithLp.toLp 2 (0, 1), ?_⟩, fun q ↦ bot_lt_iff_ne_bot.mpr (hnb q)⟩,
      fun x ↦ (lowerSemicontinuous_indicatorVA hS).comp (by fun_prop), fun x ↦ ?_⟩,
    lowerSemicontinuous_indicatorVA hS, isParametricallyLevelBounded_of_subset fun q hq ↦ ?_,
    ⟨0, 1, one_pos, ?_⟩, ?_, ?_, ?_⟩
  · rw [pointIntegrand, indicatorVA_apply_mem (show WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)) ∈ S from
      ⟨rfl, rfl⟩)]
    exact EReal.zero_lt_top
  · rintro ⟨u₁, a₁⟩ h₁ ⟨u₂, a₂⟩ h₂ s t hs ht hst
    have hmem : ∀ (u a : ℝ), pointIntegrand (WithLp.toLp 2 (x, u)) ≤ (a : EReal) →
        x = 0 ∧ u = 1 ∧ 0 ≤ a := by
      intro u a h
      by_cases hu : WithLp.toLp 2 (x, u) ∈ S
      · rw [pointIntegrand, indicatorVA_apply_mem hu] at h
        exact ⟨hu.1, hu.2, EReal.coe_nonneg.mp h⟩
      · rw [pointIntegrand, indicatorVA_apply_not_mem hu, top_le_iff] at h
        exact absurd h (EReal.coe_ne_top _)
    obtain ⟨hx, rfl, ha₁⟩ := hmem u₁ a₁ h₁
    obtain ⟨-, rfl, ha₂⟩ := hmem u₂ a₂ h₂
    change pointIntegrand (WithLp.toLp 2 (x, s • (1 : ℝ) + t • (1 : ℝ))) ≤
      ((s * a₁ + t * a₂ : ℝ) : EReal)
    rw [← add_smul, hst, one_smul, pointIntegrand,
      indicatorVA_apply_mem (show WithLp.toLp 2 (x, (1 : ℝ)) ∈ S from ⟨hx, rfl⟩)]
    exact EReal.coe_nonneg.mpr (by positivity)
  · by_contra hx
    have hq0 : q.fst ≠ 0 := fun h ↦ by rw [h, abs_zero] at hx; linarith [abs_nonneg q.snd]
    rw [pointIntegrand, indicatorVA_apply_not_mem (fun h ↦ hq0 h.1)] at hq
    exact lt_irrefl _ hq
  · rw [augmentedDualObjective_eq_iInf_augmentedLagrangian]
    refine EReal.bot_lt_zero.trans_le (le_iInf fun x ↦ ?_)
    rw [hL x 0 1 one_pos]
    exact le_top
  · rw [hL 0 0 1 one_pos]
    exact top_le_iff.mp (le_iInf fun x ↦ (hL x 0 1 one_pos).ge)
  · rw [hL 0 0 1 one_pos]
    exact le_antisymm (le_iSup_of_le 0 (le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 < r) ↦
      augmentedLagrangian pointIntegrand (indicatorVA ({0} : Set ℝ)) 0 0 r) 1 one_pos
      (hL 0 0 1 one_pos).ge)) le_top
  · rw [mem_argmin_iff]
    rintro ⟨-, hlt⟩
    have hinf : (⨅ x, primalObjective pointIntegrand x) = ⊤ :=
      top_le_iff.mp (le_iInf fun x ↦ (htop0 x).ge)
    exact lt_irrefl _ (hinf ▸ hlt)

end InfiniteSaddle

end
end RW
