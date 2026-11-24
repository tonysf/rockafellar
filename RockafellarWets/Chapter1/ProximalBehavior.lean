/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1G: Moreau envelopes

* **Definition 1.22**: `eλ f ≤ f`, and for an indicator `δ_C` the proximal mapping is the projection
  `P_C` while `eλ δ_C = (1/2λ) d_C²` (`moreauEnvelopeEReal`, `proximalMappingEReal`).
* **Exercise 1.24**: the characteristics of prox-boundedness, the formula `-½ r_f` for the lower
  limit of `f(x)/|x|²`, the threshold formula `λ_f = 1/max{0, r_f}`, and `λ_f = ∞` for `f` bounded
  below.
* **Theorem 1.25**: proximal behavior.

The book's `ℝⁿ` is a finite-dimensional real inner product space `E`.
-/

import RockafellarWets.Chapter1.ParametricMinimization
import RockafellarWets.Chapter5.ProximalMappings
import RockafellarWets.Chapter7.EventualProxBoundedness
import RockafellarWets.Chapter14.MoreauIntegrands

open Set Filter Topology Metric Bornology
open scoped InnerProductSpace

noncomputable section

namespace RW

variable {E : Type*}

/-! ## Definition 1.22 -/

section Definition

variable [NormedAddCommGroup E]

/-- **Definition 1.22**: `eλ f(x) ≤ f(x)`. -/
theorem moreauEnvelopeEReal_le (f : E → EReal) (lam : ℝ) (x : E) :
    moreauEnvelopeEReal f lam x ≤ f x :=
  (iInf_le _ x).trans_eq (by simp)

/-- The remark after Definition 1.22: `eλ δ_C = (1/2λ) d_C²` for nonempty `C`. -/
theorem moreauEnvelopeEReal_indicatorVA_eq_sq_infDist {C : Set E} (hC : C.Nonempty) {lam : ℝ}
    (hlam : 0 < lam) (x : E) :
    moreauEnvelopeEReal (indicatorVA C) lam x =
      (((1 / (2 * lam)) * infDist x C ^ 2 : ℝ) : EReal) := by
  have hc : 0 < 1 / (2 * lam) := by positivity
  apply le_antisymm
  · refine ereal_le_coe_of_forall_pos fun ε hε ↦ ?_
    -- a point of `C` almost realizing the distance
    set d := infDist x C with hddef
    have hd : 0 ≤ d := infDist_nonneg
    set K := (1 / (2 * lam)) * (2 * d + 1) with hKdef
    have hK : 0 < K := by positivity
    set δ := min 1 (ε / K) with hδdef
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδK : δ * K ≤ ε := (le_div_iff₀ hK).1 (min_le_right _ _)
    have hδε : (1 / (2 * lam)) * (d + δ) ^ 2 ≤ (1 / (2 * lam)) * d ^ 2 + ε := by
      have h1 : δ ^ 2 ≤ δ := by nlinarith
      have h2 : (1 / (2 * lam)) * (d + δ) ^ 2 =
          (1 / (2 * lam)) * d ^ 2 + (1 / (2 * lam)) * (2 * d * δ + δ ^ 2) := by ring
      have h3 : (1 / (2 * lam)) * (2 * d * δ + δ ^ 2) ≤ δ * K := by
        rw [hKdef]
        have : 2 * d * δ + δ ^ 2 ≤ δ * (2 * d + 1) := by nlinarith
        nlinarith
      linarith
    obtain ⟨w, hwC, hw⟩ := (infDist_lt_iff hC).1 (show infDist x C < infDist x C + δ by linarith)
    refine (iInf_le _ w).trans ?_
    rw [indicatorVA_apply_mem hwC, zero_add, EReal.coe_le_coe_iff]
    refine le_trans ?_ hδε
    rw [← dist_eq_norm, dist_comm]
    gcongr
  · refine le_iInf fun w ↦ ?_
    by_cases hw : w ∈ C
    · rw [indicatorVA_apply_mem hw, zero_add, EReal.coe_le_coe_iff, ← dist_eq_norm, dist_comm]
      gcongr
      · exact infDist_nonneg
      · exact infDist_le_dist_of_mem hw
    · rw [indicatorVA_apply_not_mem hw, EReal.top_add_coe]
      exact le_top

/-- The remark after Definition 1.22: `Pλ δ_C = P_C` for nonempty `C`. -/
theorem proximalMappingEReal_indicatorVA_eq_projMapping {C : Set E} (hC : C.Nonempty) {lam : ℝ}
    (hlam : 0 < lam) (x : E) : proximalMappingEReal (indicatorVA C) lam x = projMapping C x := by
  ext w
  rw [mem_proximalMappingEReal_iff, moreauEnvelopeEReal_indicatorVA_eq_sq_infDist hC hlam,
    mem_projMapping_iff_norm_eq_infDist hC, proximalObjectiveEReal]
  have hc : 0 < 1 / (2 * lam) := by positivity
  by_cases hw : w ∈ C
  · rw [indicatorVA_apply_mem hw, zero_add, EReal.coe_eq_coe_iff]
    simp only [EReal.coe_lt_top, and_true, hw, true_and]
    constructor
    · intro h
      have h2 : ‖w - x‖ ^ 2 = infDist x C ^ 2 := mul_left_cancel₀ hc.ne' h
      exact (sq_eq_sq₀ (norm_nonneg _) infDist_nonneg).1 h2
    · intro h; rw [h]
  · rw [indicatorVA_apply_not_mem hw, EReal.top_add_coe]
    constructor
    · rintro ⟨h, -⟩; exact absurd h.symm (EReal.coe_ne_top _)
    · rintro ⟨hw', -⟩; exact absurd hw' hw

end Definition

/-! ## Exercise 1.24 -/

section ProxBoundedness

/-- `m ≤ a + t` iff `m - t ≤ a`, for real `m`, `t` and extended real `a`. -/
theorem coe_le_add_coe_iff_coe_sub_le {a : EReal} {m t : ℝ} :
    (m : EReal) ≤ a + t ↔ ((m - t : ℝ) : EReal) ≤ a := by
  induction a using EReal.rec with
  | bot =>
    rw [EReal.bot_add]
    simp only [le_bot_iff, EReal.coe_ne_bot]
  | top => simp
  | coe a =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

/-- Completing the square: `d s² - 2 e s ≥ -e²/d` for `d > 0`. -/
theorem neg_sq_div_le_quadratic {d e s : ℝ} (hd : 0 < d) :
    -(e ^ 2 / d) ≤ d * s ^ 2 - 2 * e * s := by
  have h : d * s ^ 2 - 2 * e * s + e ^ 2 / d = d * (s - e / d) ^ 2 := by field_simp; ring
  have : 0 ≤ d * (s - e / d) ^ 2 := by positivity
  linarith

variable [NormedAddCommGroup E]

/-- The set of `r ∈ ℝ` for which `f + ½ r|·|²` is bounded from below (condition (c) of 1.24). -/
def quadraticShiftSet (f : E → EReal) : Set ℝ :=
  {r | ∃ m : ℝ, ∀ x, (m : EReal) ≤ f x + ((r / 2 * ‖x‖ ^ 2 : ℝ) : EReal)}

/-- `r_f` of Exercise 1.24: the infimum of all `r` for which condition (c) holds. -/
def quadraticShiftInf (f : E → EReal) : EReal := ⨅ r ∈ quadraticShiftSet f, (r : EReal)

theorem quadraticShiftSet_mono {f : E → EReal} {r r' : ℝ} (hr : r ∈ quadraticShiftSet f)
    (h : r ≤ r') : r' ∈ quadraticShiftSet f := by
  obtain ⟨m, hm⟩ := hr
  refine ⟨m, fun x ↦ (hm x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_))⟩
  have := sq_nonneg ‖x‖
  nlinarith

theorem mem_quadraticShiftSet_of_quadraticShiftInf_lt {f : E → EReal} {r : ℝ}
    (h : quadraticShiftInf f < r) : r ∈ quadraticShiftSet f := by
  obtain ⟨r', hr'⟩ := iInf_lt_iff.1 h
  obtain ⟨hmem, hlt⟩ := iInf_lt_iff.1 hr'
  exact quadraticShiftSet_mono hmem (EReal.coe_lt_coe_iff.1 hlt).le

/-- Condition (c) with `r < 1/λ` makes `eλ f(x) > -∞` at every `x`. -/
theorem bot_lt_moreauEnvelopeEReal_of_mem_quadraticShiftSet {f : E → EReal} {r lam : ℝ}
    (hr : r ∈ quadraticShiftSet f) (hlam : 0 < lam) (hrl : r < 1 / lam) (x : E) :
    ⊥ < moreauEnvelopeEReal f lam x := by
  obtain ⟨m, hm⟩ := hr
  set c := 1 / (2 * lam) with hc
  have hc' : 1 / lam = 2 * c := by rw [hc]; field_simp
  have hd : 0 < c - r / 2 := by linarith
  set K := c * ‖x‖ ^ 2 - (c * ‖x‖) ^ 2 / (c - r / 2)
  refine (EReal.bot_lt_coe (m + K)).trans_le (le_iInf fun w ↦ ?_)
  have hq : r / 2 * ‖w‖ ^ 2 + K ≤ c * ‖w - x‖ ^ 2 := by
    have h1 : (‖w‖ - ‖x‖) ^ 2 ≤ ‖w - x‖ ^ 2 := by
      have := abs_norm_sub_norm_le w x
      nlinarith [abs_nonneg (‖w‖ - ‖x‖), sq_abs (‖w‖ - ‖x‖)]
    have h2 := neg_sq_div_le_quadratic (e := c * ‖x‖) (s := ‖w‖) hd
    have hcpos : 0 < c := by positivity
    nlinarith
  calc ((m + K : ℝ) : EReal) = (m : EReal) + K := EReal.coe_add _ _
    _ ≤ (f w + ((r / 2 * ‖w‖ ^ 2 : ℝ) : EReal)) + K := add_le_add (hm w) le_rfl
    _ = f w + ((r / 2 * ‖w‖ ^ 2 + K : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]
    _ ≤ f w + ((c * ‖w - x‖ ^ 2 : ℝ) : EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.2 hq)

/-- `eλ f(x) > -∞` at some `x` gives condition (c) for every `r > 1/λ`. -/
theorem mem_quadraticShiftSet_of_bot_lt {f : E → EReal} {lam : ℝ} (hlam : 0 < lam) {x : E}
    (hx : ⊥ < moreauEnvelopeEReal f lam x) {r : ℝ} (hr : 1 / lam < r) :
    r ∈ quadraticShiftSet f := by
  obtain ⟨β, -, hβ⟩ := EReal.exists_between_coe_real hx
  set c := 1 / (2 * lam) with hc
  have hc' : 1 / lam = 2 * c := by rw [hc]; field_simp
  have hd : 0 < r / 2 - c := by linarith
  set K := -((c * ‖x‖) ^ 2 / (r / 2 - c)) - c * ‖x‖ ^ 2
  refine ⟨β + K, fun w ↦ ?_⟩
  have hw : (β : EReal) ≤ f w + ((c * ‖w - x‖ ^ 2 : ℝ) : EReal) := hβ.le.trans (iInf_le _ w)
  have hq : c * ‖w - x‖ ^ 2 + K ≤ r / 2 * ‖w‖ ^ 2 := by
    have h1 : ‖w - x‖ ^ 2 ≤ (‖w‖ + ‖x‖) ^ 2 := by
      have := norm_sub_le w x
      nlinarith [norm_nonneg (w - x)]
    have h2 := neg_sq_div_le_quadratic (e := c * ‖x‖) (s := ‖w‖) hd
    have hcpos : 0 < c := by positivity
    nlinarith
  calc ((β + K : ℝ) : EReal) = (β : EReal) + K := EReal.coe_add _ _
    _ ≤ (f w + ((c * ‖w - x‖ ^ 2 : ℝ) : EReal)) + K := add_le_add hw le_rfl
    _ = f w + ((c * ‖w - x‖ ^ 2 + K : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]
    _ ≤ f w + ((r / 2 * ‖w‖ ^ 2 : ℝ) : EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.2 hq)

/-- **Exercise 1.24**, (a) ⇔ (c). -/
theorem isProxBounded_iff_exists_quadraticShift {f : E → EReal} :
    IsProxBounded f ↔ (quadraticShiftSet f).Nonempty := by
  constructor
  · rintro ⟨lam, hlam, x, hx⟩
    exact ⟨2 / lam, mem_quadraticShiftSet_of_bot_lt hlam hx (by
      rw [div_lt_div_iff_of_pos_right hlam]; norm_num)⟩
  · rintro ⟨r, hr⟩
    have hpos : 0 < |r| + 1 := by positivity
    refine ⟨1 / (|r| + 1), by positivity, 0,
      bot_lt_moreauEnvelopeEReal_of_mem_quadraticShiftSet hr (by positivity) ?_ 0⟩
    rw [one_div_one_div]
    linarith [le_abs_self r]

/-- The lower growth set of Exercise 1.14 with `p = 2` is the reflection of the set in (c). -/
theorem growth_two_iff_mem_quadraticShiftSet {f : E → EReal} (γ : ℝ) :
    (∃ β : ℝ, ∀ x, ((γ * ‖x‖ ^ (2 : ℝ) + β : ℝ) : EReal) ≤ f x) ↔
      -2 * γ ∈ quadraticShiftSet f := by
  simp only [quadraticShiftSet, mem_setOf_eq, Real.rpow_two, coe_le_add_coe_iff_coe_sub_le]
  refine exists_congr fun β ↦ forall_congr' fun x ↦ ?_
  rw [show β - -2 * γ / 2 * ‖x‖ ^ 2 = γ * ‖x‖ ^ 2 + β by ring]

theorem exists_mem_quadraticShiftSet_lt {f : E → EReal} {t : ℝ}
    (h : quadraticShiftInf f < t) : ∃ r ∈ quadraticShiftSet f, r < t := by
  obtain ⟨r, hr⟩ := iInf_lt_iff.1 h
  obtain ⟨hmem, hlt⟩ := iInf_lt_iff.1 hr
  exact ⟨r, hmem, EReal.coe_lt_coe_iff.1 hlt⟩

/-- A parameter `λ > 0` with `r_f < 1/λ` lies below the threshold. -/
theorem coe_le_proxThreshold_of_quadraticShiftInf_lt {f : E → EReal} {lam : ℝ} (hlam : 0 < lam)
    (h : quadraticShiftInf f < ((1 / lam : ℝ) : EReal)) : (lam : EReal) ≤ proxThreshold f := by
  obtain ⟨r, hr, hrl⟩ := exists_mem_quadraticShiftSet_lt h
  exact le_iSup₂_of_le lam ⟨hlam, 0,
    bot_lt_moreauEnvelopeEReal_of_mem_quadraticShiftSet hr hlam hrl 0⟩ le_rfl

/-- A parameter `λ > 0` with `eλ f(x) > -∞` somewhere has `r_f ≤ 1/λ`. -/
theorem quadraticShiftInf_le_of_bot_lt {f : E → EReal} {lam : ℝ} (hlam : 0 < lam) {x : E}
    (hx : ⊥ < moreauEnvelopeEReal f lam x) : quadraticShiftInf f ≤ ((1 / lam : ℝ) : EReal) :=
  ereal_le_coe_of_forall_pos fun ε hε ↦
    iInf₂_le _ (mem_quadraticShiftSet_of_bot_lt hlam hx (by linarith))

/-- Prox-boundedness makes `r_f < ∞`, so one of the two cases of
`proxThreshold_eq_of_quadraticShiftInf` applies. -/
theorem quadraticShiftInf_lt_top_of_isProxBounded {f : E → EReal} (hpb : IsProxBounded f) :
    quadraticShiftInf f < ⊤ := by
  obtain ⟨r, hr⟩ := isProxBounded_iff_exists_quadraticShift.1 hpb
  exact (iInf₂_le _ hr).trans_lt (EReal.coe_lt_top r)

/-- **Exercise 1.24**: the threshold is `λ_f = 1/max{0, r_f}` with the convention `1/0 = ∞`:
it is `∞` when `r_f ≤ 0` and `1/r_f` when `r_f > 0` is finite. -/
theorem proxThreshold_eq_of_quadraticShiftInf {f : E → EReal} :
    (quadraticShiftInf f ≤ 0 → proxThreshold f = ⊤) ∧
      ∀ r : ℝ, quadraticShiftInf f = r → 0 < r → proxThreshold f = ((1 / r : ℝ) : EReal) := by
  refine ⟨fun h ↦ ?_, fun r hr hrpos ↦ ?_⟩
  · refine (EReal.eq_top_iff_forall_lt _).2 fun y ↦ ?_
    have hpos : 0 < max y 0 + 1 := by positivity
    refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith [le_max_left y 0]))
      (coe_le_proxThreshold_of_quadraticShiftInf_lt hpos ?_)
    exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.2 (by positivity) |>.trans_eq' EReal.coe_zero.symm)
  · apply le_antisymm
    · refine iSup₂_le fun lam ⟨hlam, x, hx⟩ ↦ ?_
      have h := quadraticShiftInf_le_of_bot_lt hlam hx
      rw [hr, EReal.coe_le_coe_iff] at h
      exact EReal.coe_le_coe_iff.2 ((le_div_iff₀ hrpos).2 (by
        rw [le_div_iff₀ hlam] at h; linarith))
    · refine ereal_le_of_forall_coe_lt fun c hc ↦ ?_
      have hc' : c < 1 / r := EReal.coe_lt_coe_iff.1 hc
      by_cases hc0 : 0 < c
      · refine coe_le_proxThreshold_of_quadraticShiftInf_lt hc0 ?_
        rw [hr]
        have hcr : c * r < 1 := (lt_div_iff₀ hrpos).1 hc'
        exact EReal.coe_lt_coe_iff.2 ((lt_div_iff₀ hc0).2 (by linarith))
      · have hlam : 0 < 1 / (2 * r) := by positivity
        refine le_trans (EReal.coe_le_coe_iff.2 (le_trans (not_lt.1 hc0) hlam.le))
          (coe_le_proxThreshold_of_quadraticShiftInf_lt hlam ?_)
        rw [hr, one_div_one_div]
        exact EReal.coe_lt_coe_iff.2 (by linarith)

/-- **Exercise 1.24**: if `inf f > -∞`, then `f` is prox-bounded with threshold `λ_f = ∞`. -/
theorem isProxBounded_and_proxThreshold_eq_top_of_bot_lt_iInf {f : E → EReal}
    (hf : ⊥ < ⨅ x, f x) : IsProxBounded f ∧ proxThreshold f = ⊤ := by
  obtain ⟨m, -, hm⟩ := EReal.exists_between_coe_real hf
  have h0 : (0 : ℝ) ∈ quadraticShiftSet f :=
    ⟨m, fun x ↦ by simpa using hm.le.trans (iInf_le f x)⟩
  have hpb : IsProxBounded f := isProxBounded_iff_exists_quadraticShift.2 ⟨0, h0⟩
  exact ⟨hpb, proxThreshold_eq_of_quadraticShiftInf.1 ((iInf₂_le _ h0).trans_eq (by simp))⟩

variable [InnerProductSpace ℝ E]

/-- **Exercise 1.24** (characteristics of prox-boundedness): for a proper lsc `f` on a
finite-dimensional inner product space, the following are equivalent: (a) `f` is prox-bounded;
(b) `f` majorizes a quadratic function `⟨Ax,x⟩ + ⟨b,x⟩ + c`; (c) `f + ½ r|·|²` is bounded below for
some `r ∈ ℝ`; (d) `liminf_{|x|→∞} f(x)/|x|² > -∞`. -/
theorem prox_boundedness_tfae [FiniteDimensional ℝ E] {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) :
    List.TFAE [IsProxBounded f,
      ∃ (A : E →L[ℝ] E) (b : E) (c : ℝ), ∀ x, ((⟪A x, x⟫_ℝ + ⟪b, x⟫_ℝ + c : ℝ) : EReal) ≤ f x,
      ∃ r m : ℝ, ∀ x, (m : EReal) ≤ f x + ((r / 2 * ‖x‖ ^ 2 : ℝ) : EReal),
      ⊥ < liminfAtInfinity (growthQuotient f 2)] := by
  tfae_have 1 ↔ 3 := by
    rw [isProxBounded_iff_exists_quadraticShift]
    exact ⟨fun ⟨r, hr⟩ ↦ ⟨r, hr⟩, fun ⟨r, hr⟩ ↦ ⟨r, hr⟩⟩
  tfae_have 3 → 2 := by
    rintro ⟨r, m, hm⟩
    refine ⟨(-(r / 2)) • ContinuousLinearMap.id ℝ E, 0, m, fun x ↦ ?_⟩
    have h := coe_le_add_coe_iff_coe_sub_le.1 (hm x)
    convert h using 2
    simp [real_inner_smul_left]
    ring
  tfae_have 2 → 3 := by
    rintro ⟨A, b, c, hq⟩
    refine ⟨2 * (‖A‖ + 1), c - ‖b‖ ^ 2 / 4, fun x ↦ ?_⟩
    rw [coe_le_add_coe_iff_coe_sub_le]
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hq x)
    have h1 : -(‖A‖ * ‖x‖ ^ 2) ≤ ⟪A x, x⟫_ℝ := by
      have := abs_real_inner_le_norm (A x) x
      have h2 := A.le_opNorm x
      have h3 : ‖A x‖ * ‖x‖ ≤ ‖A‖ * ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg x)
      nlinarith [abs_le.1 this]
    have h4 : -(‖b‖ * ‖x‖) ≤ ⟪b, x⟫_ℝ := by
      have := abs_real_inner_le_norm b x
      linarith [(abs_le.1 this).1]
    have h5 : ‖b‖ * ‖x‖ ≤ ‖x‖ ^ 2 + ‖b‖ ^ 2 / 4 := by nlinarith [sq_nonneg (‖x‖ - ‖b‖ / 2)]
    nlinarith
  tfae_have 3 ↔ 4 := by
    rw [liminfAtInfinity_growthQuotient two_pos hl hp.2]
    constructor
    · rintro ⟨r, hr⟩
      have hmem : ∃ β : ℝ, ∀ x, ((-(r / 2) * ‖x‖ ^ (2 : ℝ) + β : ℝ) : EReal) ≤ f x := by
        rw [growth_two_iff_mem_quadraticShiftSet, show -2 * -(r / 2) = r by ring]
        exact hr
      exact (EReal.bot_lt_coe _).trans_le (le_iSup₂_of_le (-(r / 2)) hmem le_rfl)
    · intro h
      obtain ⟨γ, hγ⟩ := lt_iSup_iff.1 h
      obtain ⟨hmem, -⟩ := lt_iSup_iff.1 hγ
      exact ⟨_, (growth_two_iff_mem_quadraticShiftSet γ).1 hmem⟩
  tfae_finish

/-- **Exercise 1.24**: `liminf_{|x|→∞} f(x)/|x|² = -½ r_f`. -/
theorem liminfAtInfinity_growthQuotient_two [FiniteDimensional ℝ E] {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) :
    liminfAtInfinity (growthQuotient f 2) = ((-(1 / 2) : ℝ) : EReal) * quadraticShiftInf f := by
  rw [liminfAtInfinity_growthQuotient two_pos hl hp.2]
  apply le_antisymm
  · refine iSup₂_le fun γ hγ ↦ ?_
    have hr := (growth_two_iff_mem_quadraticShiftSet γ).1 hγ
    have hle : quadraticShiftInf f ≤ ((-2 * γ : ℝ) : EReal) := iInf₂_le _ hr
    calc (γ : EReal) = ((-2 * γ : ℝ) : EReal) * ((-(1 / 2) : ℝ) : EReal) := by
          rw [← EReal.coe_mul]; congr 1; ring
      _ ≤ quadraticShiftInf f * ((-(1 / 2) : ℝ) : EReal) :=
          EReal.mul_le_mul_of_nonpos_right hle
            (EReal.coe_nonpos.2 (by norm_num : (-(1 / 2) : ℝ) ≤ 0))
      _ = ((-(1 / 2) : ℝ) : EReal) * quadraticShiftInf f := mul_comm _ _
  · refine ereal_le_of_forall_coe_lt fun c hc ↦ ?_
    have hlt : quadraticShiftInf f < ((-2 * c : ℝ) : EReal) := by
      induction h : quadraticShiftInf f using EReal.rec with
      | bot => exact EReal.bot_lt_coe _
      | top =>
        rw [h, EReal.coe_mul_top_of_neg (by norm_num)] at hc
        exact absurd hc (not_lt_bot)
      | coe t =>
        rw [h, ← EReal.coe_mul, EReal.coe_lt_coe_iff] at hc
        exact EReal.coe_lt_coe_iff.2 (by linarith)
    refine le_iSup₂_of_le c ?_ le_rfl
    exact (growth_two_iff_mem_quadraticShiftSet c).2
      (mem_quadraticShiftSet_of_quadraticShiftInf_lt hlt)

end ProxBoundedness

/-! ## Theorem 1.25 -/

section Behavior

variable [NormedAddCommGroup E]

/-- `λ ↦ eλ f(x)` is nonincreasing on `(0, ∞)`: `eλ f(x)` increases as `λ ↘ 0`. -/
theorem antitoneOn_moreauEnvelopeEReal (f : E → EReal) (x : E) :
    AntitoneOn (fun lam ↦ moreauEnvelopeEReal f lam x) (Ioi 0) := by
  intro a ha b _ hab
  refine iInf_mono fun w ↦ add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
  have ha' : (0 : ℝ) < a := ha
  have : 1 / (2 * b) ≤ 1 / (2 * a) := one_div_le_one_div_of_le (by positivity) (by linarith)
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- Along `xν → x̄` and `λν ↘ 0`, `f(x̄) ≤ liminf eλν f(xν)` for a prox-bounded lsc `f`. -/
theorem le_liminf_moreauEnvelopeEReal {f : E → EReal} (hl : LowerSemicontinuous f)
    (hpb : IsProxBounded f) {xs : ℕ → E} {x : E} (hxs : Tendsto xs atTop (𝓝 x)) {ls : ℕ → ℝ}
    (hls : Tendsto ls atTop (𝓝[>] 0)) :
    f x ≤ liminf (fun n ↦ moreauEnvelopeEReal f (ls n) (xs n)) atTop := by
  obtain ⟨lam₁, hlam₁, x₁, hx₁⟩ := hpb
  obtain ⟨β, -, hβ⟩ := EReal.exists_between_coe_real hx₁
  set c₁ := 1 / (2 * lam₁) with hc₁
  have hc₁pos : 0 < c₁ := by positivity
  have hminor : ∀ w, (β : EReal) ≤ f w + ((c₁ * ‖w - x₁‖ ^ 2 : ℝ) : EReal) := fun w ↦
    hβ.le.trans (iInf_le _ w)
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hls0 : Tendsto ls atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin hls
  have hpos : ∀ᶠ n in atTop, 0 < ls n := (tendsto_nhdsWithin_iff.1 hls).2
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop
    ((frequently_lt_of_liminf_lt (by isBoundedDefault) hc1).and_eventually hpos)
  have hw : ∀ k, ∃ w, f w + (((1 / (2 * ls (φ k))) * ‖w - xs (φ k)‖ ^ 2 : ℝ) : EReal) < c :=
    fun k ↦ iInf_lt_iff.1 (hφP k).1
  choose ws hws using hw
  obtain ⟨M, hM⟩ : ∃ M, ∀ n, ‖xs n - x₁‖ ≤ M := by
    obtain ⟨M, hM⟩ :=
      isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto _ (hxs.sub_const x₁))
    exact ⟨M, fun n ↦ hM _ ⟨n, rfl⟩⟩
  set K := c - β + 2 * c₁ * M ^ 2 with hK
  have hreal : ∀ k, f (ws k) ≤ c ∧
      (1 / (2 * ls (φ k)) - 2 * c₁) * ‖ws k - xs (φ k)‖ ^ 2 < K := by
    intro k
    have h1 := hws k
    have h2 := hminor (ws k)
    have hlk : 0 < ls (φ k) := (hφP k).2
    have hfle : f (ws k) ≤ c :=
      le_trans (le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity))) h1.le
    refine ⟨hfle, ?_⟩
    have htop : f (ws k) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top c) hfle
    have hbot : f (ws k) ≠ ⊥ := by
      intro h
      rw [h, EReal.bot_add] at h2
      exact absurd h2 (by simp)
    have ha : f (ws k) = ((f (ws k)).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
    rw [ha, ← EReal.coe_add, EReal.coe_lt_coe_iff] at h1
    rw [ha, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    have h3 : ‖ws k - x₁‖ ≤ ‖ws k - xs (φ k)‖ + M := by
      calc ‖ws k - x₁‖ = ‖(ws k - xs (φ k)) + (xs (φ k) - x₁)‖ := by congr 1; abel
        _ ≤ ‖ws k - xs (φ k)‖ + ‖xs (φ k) - x₁‖ := norm_add_le _ _
        _ ≤ ‖ws k - xs (φ k)‖ + M := by linarith [hM (φ k)]
    have h4 : ‖ws k - x₁‖ ^ 2 ≤ 2 * ‖ws k - xs (φ k)‖ ^ 2 + 2 * M ^ 2 := by
      have h5 : ‖ws k - x₁‖ ^ 2 ≤ (‖ws k - xs (φ k)‖ + M) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith [sq_nonneg (‖ws k - xs (φ k)‖ - M)]
    have h6 := mul_le_mul_of_nonneg_left h4 hc₁pos.le
    nlinarith
  have hd : Tendsto (fun k ↦ ‖ws k - xs (φ k)‖) atTop (𝓝 0) := by
    have hlsφ : Tendsto (fun k ↦ ls (φ k)) atTop (𝓝 0) := hls0.comp hφ.tendsto_atTop
    have hsmall : ∀ᶠ k in atTop, ls (φ k) ≤ 1 / (8 * c₁) :=
      hlsφ.eventually (ge_mem_nhds (by positivity))
    have hbound : ∀ᶠ k in atTop, ‖ws k - xs (φ k)‖ ^ 2 ≤ 4 * |K| * ls (φ k) := by
      filter_upwards [hsmall] with k hk
      have hlk : 0 < ls (φ k) := (hφP k).2
      have h := (hreal k).2
      have ht : 4 * c₁ ≤ 1 / (2 * ls (φ k)) := by
        rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ (by positivity)] at hk
        nlinarith
      have hd0 : 0 ≤ ‖ws k - xs (φ k)‖ ^ 2 := by positivity
      have h7 : 1 / (2 * ls (φ k)) / 2 * ‖ws k - xs (φ k)‖ ^ 2 < |K| := by
        have : 1 / (2 * ls (φ k)) / 2 * ‖ws k - xs (φ k)‖ ^ 2 ≤
            (1 / (2 * ls (φ k)) - 2 * c₁) * ‖ws k - xs (φ k)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hd0
        linarith [le_abs_self K]
      have h8 : 1 / (2 * ls (φ k)) / 2 = 1 / (4 * ls (φ k)) := by field_simp; ring
      rw [h8, div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)] at h7
      nlinarith
    have hsq : Tendsto (fun k ↦ ‖ws k - xs (φ k)‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun k ↦ by positivity) hbound ?_
      simpa using hlsφ.const_mul (4 * |K|)
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  have hwlim : Tendsto ws atTop (𝓝 x) := by
    have h1 : Tendsto (fun k ↦ xs (φ k)) atTop (𝓝 x) := hxs.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun k ↦ ws k - xs (φ k)) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.2 hd
    simpa using h2.add h1
  have hlow : f x ≤ liminf (fun k ↦ f (ws k)) atTop :=
    (lowerSemicontinuousAt_iff_le_liminf.1 (hl x)).trans (liminf_le_liminf_of_le hwlim)
  have hup : liminf (fun k ↦ f (ws k)) atTop ≤ c :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun k ↦ (hreal k).1)
  exact absurd (hlow.trans hup) (not_le.2 hc2)

/-- **Theorem 1.25**: `eλν f(xν) → f(x̄)` whenever `xν → x̄` while `λν ↘ 0` with `|xν - x̄|/λν`
bounded. -/
theorem tendsto_moreauEnvelopeEReal_of_ratio_bounded {f : E → EReal} (hl : LowerSemicontinuous f)
    (hpb : IsProxBounded f) {xs : ℕ → E} {x : E} (hxs : Tendsto xs atTop (𝓝 x)) {ls : ℕ → ℝ}
    (hls : Tendsto ls atTop (𝓝[>] 0)) {ρ : ℝ} (hρ : ∀ᶠ n in atTop, ‖xs n - x‖ ≤ ρ * ls n) :
    Tendsto (fun n ↦ moreauEnvelopeEReal f (ls n) (xs n)) atTop (𝓝 (f x)) := by
  have hlow := le_liminf_moreauEnvelopeEReal hl hpb hxs hls
  refine tendsto_order.2 ⟨fun a ha ↦
    eventually_lt_of_lt_liminf (lt_of_lt_of_le ha hlow) (by isBoundedDefault), fun b hb ↦ ?_⟩
  obtain ⟨b', hb'1, hb'2⟩ := EReal.exists_between_coe_real hb
  have hpos : ∀ᶠ n in atTop, 0 < ls n := (tendsto_nhdsWithin_iff.1 hls).2
  have hls0 : Tendsto ls atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin hls
  have hupper : ∀ᶠ n in atTop, moreauEnvelopeEReal f (ls n) (xs n) ≤
      f x + ((ρ ^ 2 / 2 * ls n : ℝ) : EReal) := by
    filter_upwards [hpos, hρ] with n hn hρn
    refine (iInf_le _ x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_))
    rw [norm_sub_rev]
    have h0 : 0 ≤ ‖xs n - x‖ := norm_nonneg _
    have hsq : ‖xs n - x‖ ^ 2 ≤ (ρ * ls n) ^ 2 := pow_le_pow_left₀ h0 hρn 2
    calc 1 / (2 * ls n) * ‖xs n - x‖ ^ 2 ≤ 1 / (2 * ls n) * (ρ * ls n) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = ρ ^ 2 / 2 * ls n := by field_simp
  induction hfx : f x using EReal.rec with
  | bot =>
    filter_upwards [hupper] with n hn
    rw [hfx, EReal.bot_add, le_bot_iff] at hn
    rw [hn]
    exact lt_of_le_of_lt bot_le (lt_trans (EReal.bot_lt_coe b') hb'2)
  | top =>
    rw [hfx] at hb
    exact absurd hb not_top_lt
  | coe r =>
    rw [hfx] at hb'1
    have hr : r < b' := EReal.coe_lt_coe_iff.1 hb'1
    have hsmall : ∀ᶠ n in atTop, ρ ^ 2 / 2 * ls n < b' - r := by
      have := hls0.const_mul (ρ ^ 2 / 2)
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hupper, hsmall] with n hn hn'
    rw [hfx, ← EReal.coe_add] at hn
    exact lt_of_le_of_lt hn (lt_trans (EReal.coe_lt_coe_iff.2 (by linarith)) hb'2)

/-- **Theorem 1.25**: `eλ f(x) ↗ f(x)` as `λ ↘ 0` (monotonicity is
`antitoneOn_moreauEnvelopeEReal`). -/
theorem tendsto_moreauEnvelopeEReal_nhdsGT_zero {f : E → EReal} (hl : LowerSemicontinuous f)
    (hpb : IsProxBounded f) (x : E) :
    Tendsto (fun lam ↦ moreauEnvelopeEReal f lam x) (𝓝[>] 0) (𝓝 (f x)) :=
  tendsto_iff_seq_tendsto.2 fun ls hls ↦
    tendsto_moreauEnvelopeEReal_of_ratio_bounded hl hpb tendsto_const_nhds hls (ρ := 0)
      (Eventually.of_forall fun n ↦ by simp)

end Behavior

/-! ### Theorem 1.25: nonemptiness, finiteness and continuity -/

section BehaviorFinite

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 1.25**: for `λ ∈ (0, λ_f)`, `Pλ f(x)` is nonempty and compact. -/
theorem proximalMappingEReal_nonempty_isCompact {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (hthr : (lam : EReal) < proxThreshold f) (x : E) :
    (proximalMappingEReal f lam x).Nonempty ∧ IsCompact (proximalMappingEReal f lam x) :=
  (parametric_minimization_a (lowerSemicontinuous_proxIntegrand hl lam)
    (isProper_proxIntegrand hp) (isLevelBoundedInXLocallyUniformly_proxIntegrand hlam hthr)).2.2.1
    x (valueFunction_proxIntegrand_lt_top hp lam x)

/-- **Theorem 1.25**: for `λ ∈ (0, λ_f)`, `eλ f(x)` is finite. -/
theorem moreauEnvelopeEReal_eq_coe {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (hthr : (lam : EReal) < proxThreshold f) (x : E) :
    ∃ a : ℝ, moreauEnvelopeEReal f lam x = a := by
  have hpp := (parametric_minimization_a (lowerSemicontinuous_proxIntegrand hl lam)
    (isProper_proxIntegrand hp) (isLevelBoundedInXLocallyUniformly_proxIntegrand hlam hthr)).1
  exact ⟨_, (EReal.coe_toReal (valueFunction_proxIntegrand_lt_top hp lam x).ne
    (hpp.2 x).ne').symm⟩

/-- Sequential continuity of `(λ, x) ↦ eλ f(x)` below the threshold (7.37 for a constant
sequence). -/
theorem tendsto_moreauEnvelopeEReal_param {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (hthr : (lam : EReal) < proxThreshold f) {xs : ℕ → E} {x : E} (hxs : Tendsto xs atTop (𝓝 x))
    {ls : ℕ → ℝ} (hls : Tendsto ls atTop (𝓝 lam)) :
    Tendsto (fun n ↦ moreauEnvelopeEReal f (ls n) (xs n)) atTop
      (𝓝 (moreauEnvelopeEReal f lam x)) := by
  have hthr' : (lam : EReal) < eventualProxThreshold (fun _ : ℕ ↦ f) := by
    rw [eventualProxThreshold_const]; exact hthr
  exact (tendsto_moreauEnvelopeEReal_of_epiConverges (epiConverges_const_of_lowerSemicontinuous hl)
    (fun _ ↦ hl) hp hxs hls hlam hthr').2

/-- **Theorem 1.25**: `eλ f(x)` depends continuously on `(λ, x) ∈ (0, λ_f) × ℝⁿ`. -/
theorem continuousOn_moreauEnvelopeEReal {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) :
    ContinuousOn (fun q : ℝ × E ↦ moreauEnvelopeEReal f q.1 q.2)
      {q | 0 < q.1 ∧ (q.1 : EReal) < proxThreshold f} := by
  intro q hq
  refine ContinuousAt.continuousWithinAt (tendsto_nhds_iff_seq_tendsto.2 fun u hu ↦ ?_)
  exact tendsto_moreauEnvelopeEReal_param hp hl hq.1 hq.2 ((continuous_snd.tendsto q).comp hu)
    ((continuous_fst.tendsto q).comp hu)

/-- The proximal objective with its parameter confined to a window `[a, b]`, `∞` outside. -/
def proxWindowIntegrand (f : E → EReal) (a b : ℝ) (q : E × (E × ℝ)) : EReal :=
  if q.2.2 ∈ Icc a b then f q.1 + (((1 / (2 * q.2.2)) * ‖q.1 - q.2.1‖ ^ 2 : ℝ) : EReal) else ⊤

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem valueFunction_proxWindowIntegrand {f : E → EReal} {a b lam : ℝ} (h : lam ∈ Icc a b)
    (x : E) : valueFunction (proxWindowIntegrand f a b) (x, lam) = moreauEnvelopeEReal f lam x := by
  simp only [valueFunction, proxWindowIntegrand, if_pos h]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem paramArgmin_proxWindowIntegrand {f : E → EReal} {a b lam : ℝ} (h : lam ∈ Icc a b)
    (x : E) : paramArgmin (proxWindowIntegrand f a b) (x, lam) = proximalMappingEReal f lam x := by
  ext w
  rw [mem_paramArgmin_iff, valueFunction_proxWindowIntegrand h, mem_proximalMappingEReal_iff]
  simp only [proxWindowIntegrand, if_pos h]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem lowerSemicontinuous_proxWindowIntegrand {f : E → EReal} (hl : LowerSemicontinuous f)
    {a b : ℝ} (ha : 0 < a) : LowerSemicontinuous (proxWindowIntegrand f a b) := by
  rw [lowerSemicontinuous_iff_isClosed_levelSet]
  intro α
  set ψ : E × (E × ℝ) → ℝ := fun q ↦ (1 / (2 * max q.2.2 a)) * ‖q.1 - q.2.1‖ ^ 2 with hψdef
  have hψ : Continuous ψ := by
    refine Continuous.mul ?_ ((continuous_fst.sub (continuous_fst.comp continuous_snd)).norm.pow 2)
    refine continuous_const.div (continuous_const.mul
      ((continuous_snd.comp continuous_snd).max continuous_const)) fun q ↦ ?_
    have : 0 < max q.2.2 a := lt_of_lt_of_le ha (le_max_right _ _)
    positivity
  have hG : LowerSemicontinuous (fun q : E × (E × ℝ) ↦ f q.1 + ((ψ q : ℝ) : EReal)) :=
    lowerSemicontinuous_add_coe (hl.comp continuous_fst) hψ
  have heq : levelSet (proxWindowIntegrand f a b) α =
      {q | q.2.2 ∈ Icc a b} ∩ levelSet (fun q ↦ f q.1 + ((ψ q : ℝ) : EReal)) α := by
    ext q
    simp only [levelSet, mem_setOf_eq, mem_inter_iff]
    by_cases hq : q.2.2 ∈ Icc a b
    · have hmax : max q.2.2 a = q.2.2 := max_eq_left hq.1
      have hψq : ψ q = (1 / (2 * q.2.2)) * ‖q.1 - q.2.1‖ ^ 2 := by simp only [hψdef, hmax]
      rw [proxWindowIntegrand, if_pos hq, hψq]
      exact ⟨fun h ↦ ⟨hq, h⟩, fun h ↦ h.2⟩
    · rw [proxWindowIntegrand, if_neg hq]
      exact ⟨fun h ↦ absurd h (by simp), fun h ↦ absurd h.1 hq⟩
  rw [heq]
  exact (isClosed_Icc.preimage (continuous_snd.comp continuous_snd)).inter
    (lowerSemicontinuous_iff_isClosed_levelSet.1 hG α)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem isProper_proxWindowIntegrand {f : E → EReal} (hp : IsProper f) {a b : ℝ} (hab : a ≤ b) :
    IsProper (proxWindowIntegrand f a b) := by
  obtain ⟨w₀, hw₀⟩ := hp.1
  refine ⟨⟨(w₀, (w₀, a)), ?_⟩, fun q ↦ ?_⟩
  · rw [proxWindowIntegrand, if_pos ⟨le_rfl, hab⟩]
    simpa using hw₀
  · unfold proxWindowIntegrand
    split_ifs
    · exact EReal.bot_lt_add_iff.2 ⟨hp.2 _, EReal.bot_lt_coe _⟩
    · exact bot_lt_top

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem isLevelBoundedInXLocallyUniformly_proxWindowIntegrand {f : E → EReal} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hthr : (b : EReal) < proxThreshold f) :
    IsLevelBoundedInXLocallyUniformly (proxWindowIntegrand f a b) := by
  intro u α
  obtain ⟨ε, hε, hS⟩ :=
    isLevelBoundedInXLocallyUniformly_proxIntegrand (lt_of_lt_of_le ha hab) hthr u.1 α
  refine ⟨ε, hε, (hS.image_fst.prod ((isBounded_closedBall (x := u.1) (r := ε)).prod
    (isBounded_Icc a b))).subset ?_⟩
  rintro ⟨w, x, lam⟩ ⟨⟨-, hq⟩, hlev⟩
  have hlev' : proxWindowIntegrand f a b (w, (x, lam)) ≤ α := hlev
  have hlam : lam ∈ Icc a b := by
    by_contra h
    rw [proxWindowIntegrand, if_neg h] at hlev'
    exact absurd hlev' (by simp)
  have hx : x ∈ closedBall u.1 ε := by
    rw [mem_closedBall] at hq ⊢
    exact (le_max_left _ _).trans hq
  have hprox : proxIntegrand f b (w, x) ≤ α := by
    refine le_trans ?_ hlev'
    rw [proxWindowIntegrand, if_pos hlam, proxIntegrand_apply, proximalObjectiveEReal]
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
    have hlam0 : 0 < lam := lt_of_lt_of_le ha hlam.1
    exact mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le (by positivity) (by linarith [hlam.2])) (sq_nonneg _)
  exact ⟨⟨(w, x), ⟨⟨mem_univ _, hx⟩, hprox⟩, rfl⟩, hx, hlam⟩

/-- **Theorem 1.25**: if `wν ∈ Pλν f(xν)`, `xν → x̄` and `λν → λ ∈ (0, λ_f)`, then `{wν}` is
bounded and all its cluster points lie in `Pλ f(x̄)`. -/
theorem proximalMappingEReal_cluster {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (hthr : (lam : EReal) < proxThreshold f) {xs ws : ℕ → E} {x : E} {ls : ℕ → ℝ}
    (hws : ∀ n, ws n ∈ proximalMappingEReal f (ls n) (xs n)) (hxs : Tendsto xs atTop (𝓝 x))
    (hls : Tendsto ls atTop (𝓝 lam)) :
    IsBounded (range ws) ∧ ∀ w, MapClusterPt w atTop ws → w ∈ proximalMappingEReal f lam x := by
  obtain ⟨b, hb1, hb2⟩ := EReal.exists_between_coe_real hthr
  have hlb : lam < b := EReal.coe_lt_coe_iff.1 hb1
  have ha : 0 < lam / 2 := by positivity
  have hab : lam / 2 ≤ b := by linarith
  have hwin : ∀ᶠ n in atTop, ls n ∈ Icc (lam / 2) b :=
    hls.eventually (Icc_mem_nhds (by linarith) hlb)
  have hlamwin : lam ∈ Icc (lam / 2) b := ⟨by linarith, hlb.le⟩
  have hdom : (x, lam) ∈ effectiveDomain (valueFunction (proxWindowIntegrand f (lam / 2) b)) := by
    rw [mem_effectiveDomain_iff, valueFunction_proxWindowIntegrand hlamwin]
    exact valueFunction_proxIntegrand_lt_top hp lam x
  have hcont : Tendsto (fun n ↦ valueFunction (proxWindowIntegrand f (lam / 2) b) (xs n, ls n))
      atTop (𝓝 (valueFunction (proxWindowIntegrand f (lam / 2) b) (x, lam))) := by
    rw [valueFunction_proxWindowIntegrand hlamwin]
    refine (tendsto_moreauEnvelopeEReal_param hp hl hlam hthr hxs hls).congr' ?_
    filter_upwards [hwin] with n hn
    rw [valueFunction_proxWindowIntegrand hn]
  have hmem : ∀ᶠ n in atTop,
      ws n ∈ paramArgmin (proxWindowIntegrand f (lam / 2) b) (xs n, ls n) := by
    filter_upwards [hwin] with n hn
    rw [paramArgmin_proxWindowIntegrand hn]
    exact hws n
  obtain ⟨hbdd, hcl⟩ := parametric_minimization_b (lowerSemicontinuous_proxWindowIntegrand hl ha)
    (isProper_proxWindowIntegrand hp hab)
    (isLevelBoundedInXLocallyUniformly_proxWindowIntegrand ha hab hb2) hmem (hxs.prodMk_nhds hls)
    hdom hcont
  exact ⟨hbdd, fun w hw ↦ by rw [← paramArgmin_proxWindowIntegrand hlamwin]; exact hcl w hw⟩

end BehaviorFinite

end RW
