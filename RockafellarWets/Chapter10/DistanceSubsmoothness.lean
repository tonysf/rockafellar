/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: subsmoothness of distance functions

**Example 10.57** (first assertion): for a nonempty closed set `C`, `d_C²` is upper-`C²` — in
fact upper-`C^∞` (`isUpperCOn_sq_infDist`).  As the book notes, `d_C² = e_{1/2} δ_C`
(`moreauEnvelopeReal_indicatorVA_half`), so this is the case `f = δ_C`, `λ = 1/2` of the
Moreau envelope result 10.32 (with the epigraph-indexed representation used there); `δ_C` is
proper, lsc and has prox-threshold above `1/2` because it is nonnegative.

**Example 10.57** (second assertion): on the complement of `C`, `d_C` itself is upper-`C²` —
in fact upper-`C^∞` (`isUpperCOn_infDist_compl`).  The book takes the square root of `d_C²`; we
do this inside the epigraph-indexed representation of `-d_C²` from 10.32: near `x₀ ∉ C` all
`β + |y - x|²` (with `y ∈ C`, `β ≥ 0`) stay above `(d_C(x₀)/2)²`, so
`-d_C(x) = max_{(y, β)} -√(β + |y - x|²)`, and composing with a smooth positive function that is
the identity above that level (`floorSmooth`, built from `Real.smoothTransition`) keeps the model
jointly smooth.
-/

import RockafellarWets.Chapter10.SubsmoothMoreauEnvelopes
import RockafellarWets.Chapter10.SubsmoothCalculus
import RockafellarWets.Chapter1.Semicontinuity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `e_{1/2} δ_C = d_C²` for a nonempty closed set `C`. -/
theorem moreauEnvelopeEReal_indicatorVA_half {C : Set E} (hC : IsClosed C) (hne : C.Nonempty)
    (x : E) :
    moreauEnvelopeEReal (indicatorVA C) (1 / 2) x = ((infDist x C ^ 2 : ℝ) : EReal) := by
  have hcoef : (1 : ℝ) / (2 * (1 / 2)) = 1 := by norm_num
  apply le_antisymm
  · obtain ⟨y, hyC, hy⟩ := hC.exists_infDist_eq_dist hne x
    refine (iInf_le _ y).trans (le_of_eq ?_)
    simp only [indicatorVA, hyC, if_true, hcoef, one_mul, zero_add]
    rw [hy, dist_comm, dist_eq_norm]
  · refine le_iInf fun w ↦ ?_
    by_cases hw : w ∈ C
    · simp only [indicatorVA, hw, if_true, hcoef, one_mul, zero_add, EReal.coe_le_coe_iff]
      have h1 : infDist x C ≤ ‖w - x‖ := by
        rw [← dist_eq_norm, dist_comm]
        exact infDist_le_dist_of_mem hw
      exact pow_le_pow_left₀ infDist_nonneg h1 2
    · simp only [indicatorVA, hw, if_false, EReal.top_add_coe]
      exact le_top

theorem moreauEnvelopeReal_indicatorVA_half {C : Set E} (hC : IsClosed C) (hne : C.Nonempty)
    (x : E) : moreauEnvelopeReal (indicatorVA C) (1 / 2) x = infDist x C ^ 2 := by
  rw [moreauEnvelopeReal, moreauEnvelopeEReal_indicatorVA_half hC hne, EReal.toReal_coe]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem isProper_indicatorVA {C : Set E} (hne : C.Nonempty) : IsProper (indicatorVA C) := by
  obtain ⟨c, hc⟩ := hne
  refine ⟨⟨c, by simp [indicatorVA, hc]⟩, fun x ↦ ?_⟩
  by_cases hx : x ∈ C
  · simp [indicatorVA, hx]
  · simp [indicatorVA, hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The indicator of a nonempty set has prox-threshold at least `1`. -/
theorem one_le_proxThreshold_indicatorVA {C : Set E} (hne : C.Nonempty) :
    ((1 : ℝ) : EReal) ≤ proxThreshold (indicatorVA C) := by
  obtain ⟨c, hc⟩ := hne
  refine le_iSup₂_of_le (1 : ℝ) ⟨one_pos, c, ?_⟩ le_rfl
  refine lt_of_lt_of_le (EReal.bot_lt_coe 0) (le_iInf fun w ↦ ?_)
  by_cases hw : w ∈ C
  · simp only [indicatorVA, hw, if_true, zero_add, EReal.coe_le_coe_iff]
    positivity
  · show ((0 : ℝ) : EReal) ≤ indicatorVA C w + _
    rw [show indicatorVA C w = ⊤ from if_neg hw, EReal.top_add_coe]
    exact le_top

/-- **Example 10.57**: for a nonempty closed set `C`, `d_C²` is upper-`C^∞` (in particular
upper-`C²`) on the whole space. -/
theorem isUpperCOn_sq_infDist {C : Set E} (hC : IsClosed C) (hne : C.Nonempty) :
    IsUpperCOn ⊤ (fun x ↦ infDist x C ^ 2) univ := by
  have hthr : (((1 / 2 : ℝ)) : EReal) < proxThreshold (indicatorVA C) :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by norm_num)) (one_le_proxThreshold_indicatorVA hne)
  have h := neg_moreauEnvelope_isLowerCOn (isProper_indicatorVA hne)
    (lowerSemicontinuous_indicatorVA hC) (by norm_num : (0 : ℝ) < 1 / 2) hthr
  exact h.congr fun x _ ↦ by rw [moreauEnvelopeReal_indicatorVA_half hC hne]

/-- **Example 10.57**: `d_C²` is upper-`C²`. -/
theorem isUpperCOn_two_sq_infDist {C : Set E} (hC : IsClosed C) (hne : C.Nonempty) :
    IsUpperCOn 2 (fun x ↦ infDist x C ^ 2) univ :=
  (isUpperCOn_sq_infDist hC hne).mono le_top

/-- A smooth function that equals `s` for `s ≥ r` and is bounded below by `r / 2`. -/
noncomputable def floorSmooth (r s : ℝ) : ℝ :=
  r / 2 + (s - r / 2) * Real.smoothTransition ((s - r / 2) / (r / 2))

theorem floorSmooth_of_le {r s : ℝ} (hr : 0 < r) (hs : r ≤ s) : floorSmooth r s = s := by
  have h1 : 1 ≤ (s - r / 2) / (r / 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [floorSmooth, Real.smoothTransition.one_of_one_le h1]
  ring

theorem half_le_floorSmooth {r : ℝ} (hr : 0 < r) (s : ℝ) : r / 2 ≤ floorSmooth r s := by
  unfold floorSmooth
  by_cases hs : s ≤ r / 2
  · have h1 : (s - r / 2) / (r / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [Real.smoothTransition.zero_of_nonpos h1]
    simp
  · push_neg at hs
    have := Real.smoothTransition.nonneg ((s - r / 2) / (r / 2))
    nlinarith

theorem contDiff_floorSmooth (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (floorSmooth r) := by
  unfold floorSmooth
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)))

/-- **Example 10.57**: on the complement of a nonempty closed set `C`, `d_C` is upper-`C^∞`
(in particular upper-`C²`). -/
theorem isUpperCOn_infDist_compl {C : Set E} (hC : IsClosed C) (hne : C.Nonempty) :
    IsUpperCOn ⊤ (fun x ↦ infDist x C) Cᶜ := by
  intro x₀ hx₀
  have hthr : (((1 / 2 : ℝ)) : EReal) < proxThreshold (indicatorVA C) :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by norm_num)) (one_le_proxThreshold_indicatorVA hne)
  obtain ⟨V, hV, hx₀V, T, hT, hTepi, -, hle, heq⟩ := exists_moreau_representation
    (isProper_indicatorVA hne) (lowerSemicontinuous_indicatorVA hC) (by norm_num : (0 : ℝ) < 1 / 2)
    hthr x₀
  set d := infDist x₀ C with hd
  have hd0 : 0 < d := (hC.notMem_iff_infDist_pos hne).1 hx₀
  set r := (d / 2) ^ 2 with hr
  have hr0 : 0 < r := by positivity
  -- points of the index set lie in `C × [0, ∞)`
  have hTC : ∀ q ∈ T, q.1 ∈ C ∧ 0 ≤ q.2 := by
    intro q hq
    have h1 := hTepi q hq
    by_cases hqC : q.1 ∈ C
    · refine ⟨hqC, ?_⟩
      simp only [indicatorVA, hqC, if_true] at h1
      exact_mod_cast h1
    · simp only [indicatorVA, hqC, if_false, top_le_iff] at h1
      exact absurd h1 (EReal.coe_ne_top _)
  -- the distance stays above `d / 2` near `x₀`
  have hfar : ∀ x ∈ ball x₀ (d / 2), d / 2 < infDist x C := by
    intro x hx
    have h1 := infDist_le_infDist_add_dist (x := x₀) (y := x) (s := C)
    rw [mem_ball, dist_comm] at hx
    linarith
  have hcoef : (1 : ℝ) / (2 * (1 / 2)) = 1 := by norm_num
  have hmodel : ∀ q : E × ℝ, ∀ x, moreauModel (1 / 2) ((q.2, q.1), x) = -(q.2 + ‖q.1 - x‖ ^ 2) := by
    intro q x
    simp only [moreauModel, hcoef, one_mul]
    ring
  have harg : ∀ q ∈ T, ∀ x ∈ ball x₀ (d / 2), r ≤ q.2 + ‖q.1 - x‖ ^ 2 := by
    intro q hq x hx
    obtain ⟨hqC, hq0⟩ := hTC q hq
    have h1 : infDist x C ≤ ‖q.1 - x‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact infDist_le_dist_of_mem hqC
    have h2 := hfar x hx
    have h3 : (d / 2) ^ 2 ≤ ‖q.1 - x‖ ^ 2 := pow_le_pow_left₀ (by positivity) (h2.le.trans h1) 2
    linarith
  set Q : (ℝ × E) × E → ℝ := fun p ↦ -√(floorSmooth r (p.1.1 + ‖p.1.2 - p.2‖ ^ 2)) with hQ
  have hQc : ContDiff ℝ (⊤ : ℕ∞) Q := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : (ℝ × E) × E ↦ p.1.1 + ‖p.1.2 - p.2‖ ^ 2 :=
      (contDiff_fst.comp contDiff_fst).add
        (((contDiff_snd.comp contDiff_fst).sub contDiff_snd).norm_sq ℝ)
    exact ((contDiff_floorSmooth r).comp h1).sqrt
      (fun p ↦ ne_of_gt (lt_of_lt_of_le (by positivity) (half_le_floorSmooth hr0 _))) |>.neg
  have hQval : ∀ q ∈ T, ∀ x ∈ ball x₀ (d / 2), Q ((q.2, q.1), x) = -√(q.2 + ‖q.1 - x‖ ^ 2) := by
    intro q hq x hx
    simp only [hQ]
    rw [floorSmooth_of_le hr0 (harg q hq x hx)]
  have hsq : ∀ x, moreauEnvelopeReal (indicatorVA C) (1 / 2) x = infDist x C ^ 2 :=
    moreauEnvelopeReal_indicatorVA_half hC hne
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  set V' := V ∩ ball x₀ (d / 2) with hV'
  have hV'C : V' ⊆ Cᶜ := fun x hx hxC ↦ by
    have h1 := hfar x hx.2
    rw [infDist_zero_of_mem hxC] at h1
    linarith
  refine ⟨V', hV.inter isOpen_ball, ⟨hx₀V, mem_ball_self (by positivity)⟩, hV'C,
    ⟨LowerRepresentation.ofParam T (fun q ↦ (((q : E × ℝ).2, (q : E × ℝ).1) : ℝ × E))
      ((continuous_snd.comp continuous_subtype_val).prodMk
        (continuous_fst.comp continuous_subtype_val)) Q hQc (fun q x hx ↦ ?_) (fun x hx ↦ ?_)⟩⟩
  · -- the representing functions lie below `-d_C`
    show Q (((q : E × ℝ).2, (q : E × ℝ).1), x) ≤ -infDist x C
    rw [hQval q q.2 x hx.2, neg_le_neg_iff]
    have h1 := hle x hx.1 q q.2
    rw [hmodel, hsq] at h1
    rw [Real.le_sqrt infDist_nonneg (by nlinarith [hTC q q.2, sq_nonneg ‖(q : E × ℝ).1 - x‖])]
    linarith
  · -- the maximum is attained
    obtain ⟨q, hq, hqval⟩ := heq x hx.1
    refine ⟨⟨q, hq⟩, ?_⟩
    show Q ((q.2, q.1), x) = -infDist x C
    rw [hQval q hq x hx.2]
    rw [hmodel, hsq] at hqval
    have h1 : q.2 + ‖q.1 - x‖ ^ 2 = infDist x C ^ 2 := by linarith
    rw [h1, Real.sqrt_sq infDist_nonneg]

end RW
