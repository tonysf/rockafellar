/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2F: Example 2.38 (discontinuity and unboundedness)

On `ℝ²` the function `f(x₁, x₂) = x₁²/(2x₂)` for `x₂ > 0`, `f(0, 0) = 0`, and
`f = ∞` otherwise, is lsc, proper, convex and positively homogeneous; its
epigraph is the rotated cone `{x₂ ≥ 0, α ≥ 0, x₁² ≤ 2x₂α}`.  It is continuous
relative to every line segment in the compact convex set
`C = {x₁⁴ ≤ x₂ ≤ 1} ⊆ dom f`, but neither continuous relative to `C` nor bounded
above on `C`: along `(t, t⁴)`, `f = 1/(2t²)`.
-/

import RockafellarWets.Chapter2.ConvexFunctions
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

open Set Filter Topology

noncomputable section

namespace RW

open Classical in
/-- The function of Example 2.38. -/
def discontinuityExample (p : ℝ × ℝ) : EReal :=
  if 0 < p.2 then ((p.1 ^ 2 / (2 * p.2) : ℝ) : EReal) else if p = 0 then 0 else ⊤

/-- The compact convex set `C = {x₁⁴ ≤ x₂ ≤ 1}` of Example 2.38. -/
def discontinuitySet : Set (ℝ × ℝ) := {p | p.1 ^ 4 ≤ p.2 ∧ p.2 ≤ 1}

theorem epigraph_discontinuityExample :
    epigraph discontinuityExample =
      {q : (ℝ × ℝ) × ℝ | 0 ≤ q.1.2 ∧ 0 ≤ q.2 ∧ q.1.1 ^ 2 ≤ 2 * q.1.2 * q.2} := by
  ext ⟨⟨x₁, x₂⟩, α⟩
  rw [mem_epigraph_iff]
  simp only [discontinuityExample, mem_setOf_eq]
  by_cases h2 : 0 < x₂
  · rw [if_pos h2, EReal.coe_le_coe_iff, div_le_iff₀ (by positivity)]
    constructor
    · intro h
      refine ⟨h2.le, ?_, by linarith⟩
      nlinarith [sq_nonneg x₁]
    · rintro ⟨-, -, h⟩
      linarith
  · rw [if_neg h2]
    by_cases h0 : (x₁, x₂) = 0
    · rw [if_pos h0]
      simp only [Prod.mk_eq_zero] at h0
      obtain ⟨rfl, rfl⟩ := h0
      simp
    · rw [if_neg h0]
      simp only [top_le_iff, EReal.coe_ne_top, false_iff, not_and, not_le]
      intro hx₂ hα
      have hx₂0 : x₂ = 0 := le_antisymm (not_lt.mp h2) hx₂
      subst hx₂0
      have hx₁ : x₁ ≠ 0 := fun h ↦ h0 (by simp [h])
      simp only [mul_zero, zero_mul]
      positivity

/-- **Example 2.38**: `f` is lower semicontinuous. -/
theorem lowerSemicontinuous_discontinuityExample : LowerSemicontinuous discontinuityExample := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [epigraph_discontinuityExample]
  have h1 : IsClosed {q : (ℝ × ℝ) × ℝ | 0 ≤ q.1.2} :=
    isClosed_le continuous_const (continuous_snd.comp continuous_fst)
  have h2 : IsClosed {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2} := isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 ≤ 2 * q.1.2 * q.2} :=
    isClosed_le ((continuous_fst.comp continuous_fst).pow 2)
      ((continuous_const.mul (continuous_snd.comp continuous_fst)).mul continuous_snd)
  have := h1.inter (h2.inter h3)
  simpa only [← setOf_and] using this

/-- **Example 2.38**: `f` is convex. -/
theorem isConvexRelative_discontinuityExample : IsConvexRelative univ discontinuityExample := by
  rw [isConvexRelative_univ_iff, epigraph_discontinuityExample]
  rintro ⟨⟨p₁, p₂⟩, α⟩ ⟨hp₂, hα, hp⟩ ⟨⟨q₁, q₂⟩, β⟩ ⟨hq₂, hβ, hq⟩ a b ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mem_setOf_eq] at hp hq ⊢
  refine ⟨by positivity, by positivity, ?_⟩
  have hprod : (p₁ * q₁) ^ 2 ≤ (p₂ * β + q₂ * α) ^ 2 := by
    have h1 : (p₁ * q₁) ^ 2 ≤ (2 * p₂ * α) * (2 * q₂ * β) := by
      rw [mul_pow]
      exact mul_le_mul hp hq (sq_nonneg _) (by positivity)
    nlinarith [sq_nonneg (p₂ * β - q₂ * α)]
  have hpq : p₁ * q₁ ≤ p₂ * β + q₂ * α := by
    have hnn : 0 ≤ p₂ * β + q₂ * α := by positivity
    nlinarith [sq_nonneg (p₁ * q₁ - (p₂ * β + q₂ * α)), sq_nonneg (p₁ * q₁ + (p₂ * β + q₂ * α))]
  nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg a), mul_le_mul_of_nonneg_left hq (sq_nonneg b),
    mul_le_mul_of_nonneg_left hpq (mul_nonneg ha hb)]

/-- **Example 2.38**: `f` is proper. -/
theorem isProper_discontinuityExample : IsProper discontinuityExample := by
  refine ⟨⟨0, by simp [discontinuityExample]⟩, fun p ↦ ?_⟩
  unfold discontinuityExample
  split_ifs <;> simp

/-- **Example 2.38**: `f` is positively homogeneous. -/
theorem discontinuityExample_smul {t : ℝ} (ht : 0 < t) (p : ℝ × ℝ) :
    discontinuityExample (t • p) = (t : EReal) * discontinuityExample p := by
  obtain ⟨p₁, p₂⟩ := p
  simp only [discontinuityExample, Prod.smul_mk, smul_eq_mul]
  by_cases h2 : 0 < p₂
  · rw [if_pos (mul_pos ht h2), if_pos h2, ← EReal.coe_mul]
    congr 1
    field_simp
  · rw [if_neg (by nlinarith), if_neg h2]
    by_cases h0 : ((p₁, p₂) : ℝ × ℝ) = 0
    · have h0' : ((t * p₁, t * p₂) : ℝ × ℝ) = 0 := by
        simp only [Prod.mk_eq_zero] at h0 ⊢
        simp [h0.1, h0.2]
      rw [if_pos h0, if_pos h0', mul_zero]
    · have h0' : ((t * p₁, t * p₂) : ℝ × ℝ) ≠ 0 := by
        intro h
        apply h0
        simp only [Prod.mk_eq_zero, mul_eq_zero, ht.ne', false_or] at h ⊢
        exact h
      rw [if_neg h0, if_neg h0', EReal.coe_mul_top_of_pos ht]

theorem discontinuitySet_subset_dom :
    discontinuitySet ⊆ effectiveDomain discontinuityExample := by
  rintro ⟨x₁, x₂⟩ ⟨h4, -⟩
  change discontinuityExample (x₁, x₂) < ⊤
  unfold discontinuityExample
  by_cases h2 : 0 < x₂
  · rw [if_pos h2]; exact EReal.coe_lt_top _
  · have hx₂ : x₂ = 0 := le_antisymm (not_lt.mp h2) (le_trans (by positivity) h4)
    have hx₁ : x₁ = 0 := by
      subst hx₂
      exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp (le_antisymm h4 (by positivity))
    rw [if_neg h2, if_pos (by simp [hx₁, hx₂])]
    exact EReal.zero_lt_top

/-- **Example 2.38**: `C = {x₁⁴ ≤ x₂ ≤ 1}` is compact and convex. -/
theorem isCompact_convex_discontinuitySet :
    IsCompact discontinuitySet ∧ Convex ℝ discontinuitySet := by
  constructor
  · apply Metric.isCompact_of_isClosed_isBounded
    · have h1 : IsClosed {p : ℝ × ℝ | p.1 ^ 4 ≤ p.2} :=
        isClosed_le (continuous_fst.pow 4) continuous_snd
      have h2 : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := isClosed_le continuous_snd continuous_const
      exact h1.inter h2
    · refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1)).subset ?_
      rintro ⟨x₁, x₂⟩ ⟨h4, h1⟩
      have hx₂ : 0 ≤ x₂ := le_trans (by positivity) h4
      have hx₁ : |x₁| ≤ 1 := by
        have h41 : |x₁| ^ 4 ≤ 1 := by
          rw [pow_abs, abs_of_nonneg (by positivity)]
          exact h4.trans h1
        exact (pow_le_one_iff_of_nonneg (abs_nonneg x₁) (by norm_num)).mp h41
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hx₂]
      exact max_le hx₁ h1
  · have h4 : ConvexOn ℝ univ (fun x : ℝ ↦ x ^ 4) :=
      (Even.strictConvexOn_pow (by decide) (by decide)).convexOn
    intro p hp q hq a b ha hb hab
    refine ⟨?_, ?_⟩
    · have := h4.2 (mem_univ p.1) (mem_univ q.1) ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Prod.smul_fst, Prod.fst_add, Prod.smul_snd, Prod.snd_add, smul_eq_mul]
      nlinarith [hp.1, hq.1]
    · simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
      nlinarith [hp.2, hq.2]

/-- **Example 2.38**: `f` is not bounded above on `C`, and is not continuous at
`0` relative to `C`. -/
theorem discontinuityExample_unbounded_not_continuous :
    (∀ M : ℝ, ∃ p ∈ discontinuitySet, (M : EReal) < discontinuityExample p) ∧
      ¬ContinuousWithinAt discontinuityExample discontinuitySet 0 := by
  have hval : ∀ t : ℝ, 0 < t →
      discontinuityExample (t, t ^ 4) = ((1 / (2 * t ^ 2) : ℝ) : EReal) := by
    intro t ht
    simp only [discontinuityExample, if_pos (pow_pos ht 4)]
    congr 1
    field_simp
  have hmem : ∀ t : ℝ, 0 < t → t ≤ 1 → (t, t ^ 4) ∈ discontinuitySet := fun t ht ht1 ↦
    ⟨le_rfl, pow_le_one₀ ht.le ht1⟩
  have hbig : ∀ M : ℝ, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ M < 1 / (2 * t ^ 2) := by
    intro M
    refine ⟨1 / (|M| + 1), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]; linarith [abs_nonneg M]
    · have h1 : 0 < |M| + 1 := by positivity
      rw [div_pow, one_pow, mul_one_div, one_div_div]
      nlinarith [abs_nonneg M, le_abs_self M, sq_nonneg (|M| + 1)]
  constructor
  · intro M
    obtain ⟨t, ht, ht1, hM⟩ := hbig M
    exact ⟨_, hmem t ht ht1, by rw [hval t ht]; exact_mod_cast hM⟩
  · intro hc
    have h0 : discontinuityExample 0 = 0 := by simp [discontinuityExample]
    rw [ContinuousWithinAt, h0] at hc
    have hev := hc.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.mpr (zero_lt_one' ℝ) :
      ((0 : ℝ) : EReal) < (1 : ℝ)))
    have hpath : Tendsto (fun t : ℝ ↦ ((t, t ^ 4) : ℝ × ℝ)) (𝓝[>] 0) (𝓝[discontinuitySet] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Continuous (fun t : ℝ ↦ ((t, t ^ 4) : ℝ × ℝ)) := by fun_prop
        have h := this.tendsto 0
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
        exact hmem t ht.1 ht.2.le
    obtain ⟨t, ht, htpos⟩ := ((hpath.eventually hev).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
    rw [hval t htpos.1] at ht
    have : (1 / (2 * t ^ 2) : ℝ) < 1 := by exact_mod_cast ht
    have ht2 : t ^ 2 < 1 / 4 := by nlinarith [htpos.1, htpos.2]
    rw [div_lt_one (mul_pos two_pos (pow_pos htpos.1 2))] at this
    linarith

/-- On `{x₂ > 0}` the function is the continuous `x₁²/(2x₂)`. -/
theorem continuousOn_discontinuityExample_pos :
    ContinuousOn discontinuityExample {p : ℝ × ℝ | 0 < p.2} := by
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦ ((p.1 ^ 2 / (2 * p.2) : ℝ) : EReal))
      {p : ℝ × ℝ | 0 < p.2} := by
    refine continuous_coe_real_ereal.comp_continuousOn ?_
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ by
      have : (0 : ℝ) < p.2 := hp
      positivity
  exact hc.congr fun p hp ↦ by simp [discontinuityExample, show (0 : ℝ) < p.2 from hp]

/-- **Example 2.38**: `f` is continuous relative to every line segment in `C`. -/
theorem continuousOn_segment_discontinuityExample {p q : ℝ × ℝ} (hp : p ∈ discontinuitySet)
    (hq : q ∈ discontinuitySet) : ContinuousOn discontinuityExample (segment ℝ p q) := by
  have hC := isCompact_convex_discontinuitySet.2
  have hsub : segment ℝ p q ⊆ discontinuitySet := hC.segment_subset hp hq
  have hpos : ∀ r ∈ discontinuitySet, r ≠ 0 → 0 < r.2 := by
    rintro ⟨r₁, r₂⟩ ⟨h4, -⟩ hr
    by_contra h
    have hr₂ : r₂ = 0 := le_antisymm (not_lt.mp h) (le_trans (by positivity) h4)
    have hr₁ : r₁ = 0 := by
      subst hr₂
      exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp (le_antisymm h4 (by positivity))
    exact hr (by simp [hr₁, hr₂])
  -- along a segment from `0`, the function is linear in the distance to `0`
  have hray : ∀ q ∈ discontinuitySet, ContinuousOn discontinuityExample (segment ℝ 0 q) := by
    intro q hq
    by_cases hq0 : q = 0
    · subst hq0
      rw [segment_same]
      exact continuousOn_singleton _ _
    have hqf : discontinuityExample q ≠ ⊤ := (discontinuitySet_subset_dom hq).ne
    have hqb : discontinuityExample q ≠ ⊥ := (isProper_discontinuityExample.2 q).ne'
    set c := (discontinuityExample q).toReal
    have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hform : ∀ r ∈ segment ℝ 0 q, discontinuityExample r = ((‖r‖ / ‖q‖ * c : ℝ) : EReal) := by
      intro r hr
      obtain ⟨a, t, ha, ht, hat, rfl⟩ := hr
      rw [smul_zero, zero_add, norm_smul, Real.norm_of_nonneg ht, mul_div_assoc,
        div_self hqn.ne', mul_one]
      rcases ht.eq_or_lt with rfl | ht'
      · simp [discontinuityExample]
      · rw [discontinuityExample_smul ht', EReal.coe_mul, EReal.coe_toReal hqf hqb]
    refine ContinuousOn.congr ?_ hform
    exact continuous_coe_real_ereal.comp_continuousOn (by fun_prop)
  by_cases hp0 : p = 0
  · subst hp0
    exact hray q hq
  by_cases hq0 : q = 0
  · subst hq0
    rw [segment_symm]
    exact hray p hp
  have h0 : (0 : ℝ × ℝ) ∉ segment ℝ p q := by
    intro h0
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := h0
    have h2 := congrArg Prod.snd hcomb
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero] at h2
    have hp2 := hpos p hp hp0
    have hq2 := hpos q hq hq0
    rcases ha.eq_or_lt with rfl | ha'
    · simp only [zero_add] at hab
      subst hab
      linarith
    · nlinarith
  exact continuousOn_discontinuityExample_pos.mono fun r hr ↦
    hpos r (hsub hr) (fun h ↦ h0 (h ▸ hr))

end RW
