/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: piecewise linear-quadratic penalties

**Example 11.18**: for a nonempty polyhedral set `Y` and a symmetric positive-semidefinite `B`,
the penalty `θ_{Y,B}(u) = sup_{y ∈ Y} ⟪y, u⟫ - ½⟪y, By⟫` (`plqPenalty`) is the conjugate of
`δ_Y + j_B` (`plqPenalty_eq_fenchelConjugate`), hence proper, convex and piecewise
linear-quadratic by 11.14(b) (`plqPenalty_properties`); `θ_{Y,0} = σ_Y` is piecewise linear
(`plqPenalty_zero`); its domain is the polar of `Y^∞ ∩ ker B`, all of the space exactly when that
cone is `{0}` (`effectiveDomain_plqPenalty`, `effectiveDomain_plqPenalty_eq_univ_iff`); its
subgradients are the maximizers in the definition, i.e. `(N_Y + B)⁻¹(u)`
(`mem_subdifferential_plqPenalty_iff`, `subdifferential_plqPenalty`); its horizon subgradients are
`{y ∈ Y^∞ ∩ ker B | ⟪y, u⟫ = 0} = N_{dom θ}(u)` (`horizonSubdifferential_plqPenalty`); and these
sets are polyhedral, with a piecewise linear subderivative that is the support function of
`∂θ(u)` (`plqPenalty_subgradient_properties`).
-/

import RockafellarWets.Chapter11.PiecewiseLinearQuadraticConjugacy
import RockafellarWets.Chapter10.PLQCalculus
import RockafellarWets.Chapter3.HorizonCones
import RockafellarWets.Chapter6.Polarity

open Set Classical
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The piecewise linear-quadratic penalty `θ_{Y,B}(u) = sup_{y ∈ Y} ⟪y, u⟫ - ½⟪y, By⟫` of
Example 11.18. -/
noncomputable def plqPenalty (Y : Set E) (B : E →L[ℝ] E) (u : E) : EReal :=
  ⨆ y ∈ Y, ((⟪y, u⟫_ℝ - (1 / 2) * ⟪y, B y⟫_ℝ : ℝ) : EReal)

/-- The function `δ_Y + j_B`, with `j_B(y) = ½⟪y, By⟫`, conjugate to `θ_{Y,B}`. -/
noncomputable def plqPenaltyPrimal (Y : Set E) (B : E →L[ℝ] E) (y : E) : EReal :=
  indicatorVA Y y + (((1 / 2) * ⟪y, B y⟫_ℝ : ℝ) : EReal)

omit [FiniteDimensional ℝ E] in
theorem plqPenaltyPrimal_eq_ite (Y : Set E) (B : E →L[ℝ] E) (y : E) :
    plqPenaltyPrimal Y B y = if y ∈ Y then (((1 / 2) * ⟪y, B y⟫_ℝ : ℝ) : EReal) else ⊤ := by
  by_cases hy : y ∈ Y
  · simp only [plqPenaltyPrimal, indicatorVA, if_pos hy, zero_add]
  · simp only [plqPenaltyPrimal, indicatorVA, if_neg hy]
    exact EReal.top_add_coe _

omit [FiniteDimensional ℝ E] in
/-- **Example 11.18**, `θ_{Y,B} = (δ_Y + j_B)*`. -/
theorem plqPenalty_eq_fenchelConjugate (Y : Set E) (B : E →L[ℝ] E) :
    plqPenalty Y B = fenchelConjugate (plqPenaltyPrimal Y B) := by
  funext u
  simp only [plqPenalty, fenchelConjugate]
  apply le_antisymm
  · refine iSup₂_le fun y hy ↦ le_iSup_of_le y (le_of_eq ?_)
    rw [plqPenaltyPrimal_eq_ite, if_pos hy, ← EReal.coe_sub, real_inner_comm]
  · refine iSup_le fun x ↦ ?_
    by_cases hx : x ∈ Y
    · refine le_iSup₂_of_le x hx (le_of_eq ?_)
      rw [plqPenaltyPrimal_eq_ite, if_pos hx, ← EReal.coe_sub, real_inner_comm]
    · rw [plqPenaltyPrimal_eq_ite, if_neg hx]
      simp

section Penalty

variable {Y : Set E} {B : E →L[ℝ] E}

/-- The quadratic `j_B` as a linear-quadratic formula. -/
def plqPenaltyPiece (B : E →L[ℝ] E) (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) : QuadraticPiece E :=
  ⟨B, hB, 0, 0⟩

omit [FiniteDimensional ℝ E] in
theorem plqPenaltyPiece_eval (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) (y : E) :
    (plqPenaltyPiece B hB).eval y = (1 / 2) * ⟪y, B y⟫_ℝ := by
  simp [plqPenaltyPiece, QuadraticPiece.eval]

theorem isPiecewiseLinearQuadratic_plqPenaltyPrimal (hY : IsPolyhedral Y)
    (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) : IsPiecewiseLinearQuadratic (plqPenaltyPrimal Y B) := by
  have h := isPiecewiseLinearQuadratic_piece hY (plqPenaltyPiece B hB)
  convert h using 1
  funext y
  rw [plqPenaltyPrimal_eq_ite, plqPenaltyPiece_eval]

omit [FiniteDimensional ℝ E] in
theorem isProper_plqPenaltyPrimal (hne : Y.Nonempty) : IsProper (plqPenaltyPrimal Y B) := by
  obtain ⟨y₀, hy₀⟩ := hne
  refine ⟨⟨y₀, ?_⟩, fun y ↦ ?_⟩
  · change plqPenaltyPrimal Y B y₀ < ⊤
    rw [plqPenaltyPrimal_eq_ite, if_pos hy₀]
    exact EReal.coe_lt_top _
  · rw [plqPenaltyPrimal_eq_ite]
    split_ifs
    · exact EReal.bot_lt_coe _
    · exact bot_lt_top

omit [FiniteDimensional ℝ E] in
theorem convex_epigraph_plqPenaltyPrimal (hYc : Convex ℝ Y)
    (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) :
    Convex ℝ (epigraph (plqPenaltyPrimal Y B)) := by
  rintro ⟨y₁, r₁⟩ h₁ ⟨y₂, r₂⟩ h₂ a b ha hb hab
  simp only [epigraph, mem_setOf_eq, ge_iff_le, plqPenaltyPrimal_eq_ite, Prod.fst_add,
    Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h₁ h₂ ⊢
  split_ifs at h₁ h₂ with hy₁ hy₂ hy₂
  · rw [if_pos (hYc hy₁ hy₂ ha hb hab)]
    rw [EReal.coe_le_coe_iff] at h₁ h₂ ⊢
    have hsym : ⟪y₂, B y₁⟫_ℝ = ⟪y₁, B y₂⟫_ℝ := by rw [← hB y₂ y₁, real_inner_comm]
    have hX : ⟪a • y₁ + b • y₂, B (a • y₁ + b • y₂)⟫_ℝ
        = a ^ 2 * ⟪y₁, B y₁⟫_ℝ + 2 * a * b * ⟪y₁, B y₂⟫_ℝ + b ^ 2 * ⟪y₂, B y₂⟫_ℝ := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hsym]
      ring
    have hd : ⟪y₁ - y₂, B (y₁ - y₂)⟫_ℝ
        = ⟪y₁, B y₁⟫_ℝ - 2 * ⟪y₁, B y₂⟫_ℝ + ⟪y₂, B y₂⟫_ℝ := by
      simp only [map_sub, inner_sub_left, inner_sub_right, hsym]
      ring
    have hpsd := hBpos (y₁ - y₂)
    rw [hd] at hpsd
    have hb' : b = 1 - a := by linarith
    have key : a * ⟪y₁, B y₁⟫_ℝ + b * ⟪y₂, B y₂⟫_ℝ
        - ⟪a • y₁ + b • y₂, B (a • y₁ + b • y₂)⟫_ℝ
        = a * b * (⟪y₁, B y₁⟫_ℝ - 2 * ⟪y₁, B y₂⟫_ℝ + ⟪y₂, B y₂⟫_ℝ) := by
      rw [hX, hb']
      ring
    nlinarith [mul_nonneg (mul_nonneg ha hb) hpsd, mul_le_mul_of_nonneg_left h₁ ha,
      mul_le_mul_of_nonneg_left h₂ hb]
  all_goals first
    | exact absurd h₁ (not_le.2 (EReal.coe_lt_top r₁))
    | exact absurd h₂ (not_le.2 (EReal.coe_lt_top r₂))

variable (hY : IsPolyhedral Y) (hne : Y.Nonempty) (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ)
  (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ)
include hY hne hB hBpos

/-- **Example 11.18**: `θ_{Y,B}` is proper, lower semicontinuous, convex and piecewise
linear-quadratic. -/
theorem plqPenalty_properties :
    IsProper (plqPenalty Y B) ∧ LowerSemicontinuous (plqPenalty Y B) ∧
      Convex ℝ (epigraph (plqPenalty Y B)) ∧ IsPiecewiseLinearQuadratic (plqPenalty Y B) := by
  have hplq := isPiecewiseLinearQuadratic_plqPenaltyPrimal hY hB
  have hp := isProper_plqPenaltyPrimal (B := B) hne
  have hc := convex_epigraph_plqPenaltyPrimal hY.convex hB hBpos
  rw [plqPenalty_eq_fenchelConjugate]
  exact ⟨isProper_fenchelConjugate hp hplq.lowerSemicontinuous hc,
    lowerSemicontinuous_fenchelConjugate _, convex_epigraph_fenchelConjugate _,
    hplq.isPiecewiseLinearQuadratic_fenchelConjugate hp hplq.lowerSemicontinuous hc⟩

/-- **Example 11.18**, the subgradients of `θ_{Y,B}` at `u` are the maximizers in its
definition. -/
theorem mem_subdifferential_plqPenalty_iff (u y : E) :
    y ∈ subdifferential (plqPenalty Y B) u ↔
      y ∈ Y ∧ ∀ z ∈ Y, ⟪z, u⟫_ℝ - (1 / 2) * ⟪z, B z⟫_ℝ ≤ ⟪y, u⟫_ℝ - (1 / 2) * ⟪y, B y⟫_ℝ := by
  have hplq := isPiecewiseLinearQuadratic_plqPenaltyPrimal hY hB
  have hp := isProper_plqPenaltyPrimal (B := B) hne
  have hc := convex_epigraph_plqPenaltyPrimal hY.convex hB hBpos
  rw [plqPenalty_eq_fenchelConjugate,
    mem_subdifferential_fenchelConjugate_iff hp hplq.lowerSemicontinuous hc]
  constructor
  · intro hu
    obtain ⟨c, hc'⟩ := hu.1
    have hyY : y ∈ Y := by
      by_contra hy
      rw [plqPenaltyPrimal_eq_ite, if_neg hy] at hc'
      exact EReal.coe_ne_top c hc'.symm
    have hy' : plqPenaltyPrimal Y B y = (((1 / 2) * ⟪y, B y⟫_ℝ : ℝ) : EReal) := by
      rw [plqPenaltyPrimal_eq_ite, if_pos hyY]
    refine ⟨hyY, fun z hz ↦ ?_⟩
    have h := (mem_subdifferential_iff_of_convex hc hp hy').1 hu z
    rw [plqPenaltyPrimal_eq_ite, if_pos hz, EReal.coe_le_coe_iff, inner_sub_right,
      real_inner_comm z u, real_inner_comm y u] at h
    linarith
  · rintro ⟨hyY, hmax⟩
    have hy' : plqPenaltyPrimal Y B y = (((1 / 2) * ⟪y, B y⟫_ℝ : ℝ) : EReal) := by
      rw [plqPenaltyPrimal_eq_ite, if_pos hyY]
    refine (mem_subdifferential_iff_of_convex hc hp hy').2 fun z ↦ ?_
    by_cases hz : z ∈ Y
    · rw [plqPenaltyPrimal_eq_ite, if_pos hz, EReal.coe_le_coe_iff, inner_sub_right]
      have h := hmax z hz
      rw [real_inner_comm z u, real_inner_comm y u]
      linarith
    · rw [plqPenaltyPrimal_eq_ite, if_neg hz]
      exact le_top

/-- **Example 11.18**, `∂θ_{Y,B}(u) = {y | u - By ∈ N_Y(y)} = (N_Y + B)⁻¹(u)`. -/
theorem subdifferential_plqPenalty (u : E) :
    subdifferential (plqPenalty Y B) u = {y | y ∈ Y ∧ u - B y ∈ normalCone Y y} := by
  have hplq := isPiecewiseLinearQuadratic_plqPenaltyPrimal hY hB
  have hp := isProper_plqPenaltyPrimal (B := B) hne
  have hc := convex_epigraph_plqPenaltyPrimal hY.convex hB hBpos
  have hdom : effectiveDomain (plqPenaltyPrimal Y B) = ⋃ _ : Fin 1, Y := by
    ext y
    constructor
    · intro hy
      change plqPenaltyPrimal Y B y < ⊤ at hy
      rw [plqPenaltyPrimal_eq_ite] at hy
      split_ifs at hy with h
      · exact mem_iUnion.2 ⟨0, h⟩
      · exact absurd hy (lt_irrefl _)
    · intro hy
      obtain ⟨_, hy⟩ := mem_iUnion.1 hy
      change plqPenaltyPrimal Y B y < ⊤
      rw [plqPenaltyPrimal_eq_ite, if_pos hy]
      exact EReal.coe_lt_top _
  have hfq : ∀ (i : Fin 1) x, x ∈ (fun _ : Fin 1 ↦ Y) i →
      plqPenaltyPrimal Y B x = ((fun _ : Fin 1 ↦ plqPenaltyPiece B hB) i).eval x := by
    intro i x hx
    rw [plqPenaltyPrimal_eq_ite, if_pos hx, plqPenaltyPiece_eval]
  ext y
  rw [plqPenalty_eq_fenchelConjugate,
    mem_subdifferential_fenchelConjugate_iff hp hplq.lowerSemicontinuous hc, mem_setOf_eq]
  constructor
  · intro hu
    obtain ⟨c, hc'⟩ := hu.1
    have hyd : y ∈ effectiveDomain (plqPenaltyPrimal Y B) := by
      change plqPenaltyPrimal Y B y < ⊤
      rw [hc']
      exact EReal.coe_lt_top _
    have hyY : y ∈ Y := by simpa [hdom] using hyd
    have h := (plq_mem_subdifferential_iff hp hc (fun _ ↦ hY) hdom hfq hyd).1 hu 0 hyY
    simpa [plqPenaltyPiece] using And.intro hyY h
  · rintro ⟨hyY, hn⟩
    have hyd : y ∈ effectiveDomain (plqPenaltyPrimal Y B) := by
      rw [hdom]
      exact mem_iUnion.2 ⟨0, hyY⟩
    refine (plq_mem_subdifferential_iff hp hc (fun _ ↦ hY) hdom hfq hyd).2 fun _ _ ↦ ?_
    simpa [plqPenaltyPiece] using hn

end Penalty

omit [FiniteDimensional ℝ E] in
/-- **Example 11.18**, the case `B = 0`: `θ_{Y,0} = σ_Y`. -/
theorem plqPenalty_zero (Y : Set E) : plqPenalty Y 0 = supportFunction Y := by
  funext u
  simp only [plqPenalty, supportFunction, ContinuousLinearMap.zero_apply, inner_zero_right,
    mul_zero, sub_zero]
  rw [iSup_subtype']

/-- **Example 11.18**, the case `B = 0`: `θ_{Y,0}` is piecewise linear. -/
theorem isPiecewiseLinear_plqPenalty_zero {Y : Set E} (hY : IsPolyhedral Y) (hne : Y.Nonempty) :
    IsPiecewiseLinear (plqPenalty Y 0) := by
  rw [plqPenalty_zero]
  exact (isPolyhedral_iff_isPiecewiseLinear_supportFunction hne hY.isClosed hY.convex).1 hY

omit [FiniteDimensional ℝ E] in
/-- A positive-semidefinite symmetric map vanishes on the vectors where its form vanishes. -/
theorem eq_zero_of_inner_map_self_eq_zero {B : E →L[ℝ] E} (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ)
    (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) {w : E} (hw : ⟪w, B w⟫_ℝ = 0) : B w = 0 := by
  have hc0 : 0 ≤ ⟪B w, B (B w)⟫_ℝ := hBpos (B w)
  have hexp : ∀ t : ℝ, ⟪w - t • B w, B (w - t • B w)⟫_ℝ
      = -2 * t * ⟪B w, B w⟫_ℝ + t ^ 2 * ⟪B w, B (B w)⟫_ℝ := by
    intro t
    have h1 : ⟪w, B (B w)⟫_ℝ = ⟪B w, B w⟫_ℝ := (hB w (B w)).symm
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, h1, hw]
    ring
  have hN0 : 0 ≤ ⟪B w, B w⟫_ℝ := real_inner_self_nonneg
  by_contra hne
  have hNpos : 0 < ⟪B w, B w⟫_ℝ :=
    lt_of_le_of_ne hN0 (Ne.symm fun h ↦ hne (inner_self_eq_zero.1 h))
  set t := ⟪B w, B w⟫_ℝ / (⟪B w, B (B w)⟫_ℝ + 1) with ht
  have htpos : 0 < t := by positivity
  have htc : t * ⟪B w, B (B w)⟫_ℝ ≤ ⟪B w, B w⟫_ℝ := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h := hBpos (w - t • B w)
  rw [hexp t] at h
  nlinarith [mul_le_mul_of_nonneg_left htc htpos.le, mul_pos htpos hNpos]

/-- A real number whose nonnegative multiples are bounded above is nonpositive. -/
theorem nonpos_of_forall_mul_le {x r : ℝ} (h : ∀ s : ℝ, 0 ≤ s → s * x ≤ r) : x ≤ 0 := by
  by_contra hx
  push_neg at hx
  have := h ((|r| + 1) / x) (by positivity)
  rw [div_mul_cancel₀ _ hx.ne'] at this
  linarith [le_abs_self r]

section PenaltyDomain

variable {Y : Set E} {B : E →L[ℝ] E}
  (hY : IsPolyhedral Y) (hne : Y.Nonempty) (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ)
  (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ)

omit [FiniteDimensional ℝ E] in
theorem plqPenalty_le_coe {v : E} {c : ℝ}
    (h : ∀ y ∈ Y, ⟪y, v⟫_ℝ - (1 / 2) * ⟪y, B y⟫_ℝ ≤ c) : plqPenalty Y B v ≤ c :=
  iSup₂_le fun y hy ↦ EReal.coe_le_coe_iff.2 (h y hy)

omit [FiniteDimensional ℝ E] in
theorem mem_effectiveDomain_plqPenalty_of_le {v : E} {c : ℝ}
    (h : ∀ y ∈ Y, ⟪y, v⟫_ℝ - (1 / 2) * ⟪y, B y⟫_ℝ ≤ c) :
    v ∈ effectiveDomain (plqPenalty Y B) :=
  lt_of_le_of_lt (plqPenalty_le_coe h) (EReal.coe_lt_top c)

omit [FiniteDimensional ℝ E] in
include hBpos in
theorem zero_mem_effectiveDomain_plqPenalty : (0 : E) ∈ effectiveDomain (plqPenalty Y B) :=
  mem_effectiveDomain_plqPenalty_of_le (c := 0) fun y _ ↦ by
    rw [inner_zero_right]
    nlinarith [hBpos y]

include hY hne hB hBpos in
/-- If a linear form is bounded above on `dom θ_{Y,B}`, its vector lies in `Y^∞ ∩ ker B`. -/
theorem mem_horizonCone_and_ker_of_bddAbove {w : E} {r : ℝ}
    (hr : ∀ d ∈ effectiveDomain (plqPenalty Y B), ⟪w, d⟫_ℝ ≤ r) :
    w ∈ horizonCone Y ∧ B w = 0 := by
  constructor
  · obtain ⟨n, a, b, hrep⟩ := hY.isHPolyhedral.exists_inner_representation
    obtain ⟨y₀, hy₀⟩ := hne
    by_contra hw
    have hray : ¬ ∀ τ : ℝ, 0 ≤ τ → τ • w + y₀ ∈ Y := fun h ↦
      hw (mem_horizonCone_of_forall_smul_add_mem fun τ hτ ↦ h τ hτ)
    push_neg at hray
    obtain ⟨τ, hτ, hnot⟩ := hray
    rw [hrep] at hnot hy₀
    simp only [mem_setOf_eq, not_forall, not_le] at hnot hy₀
    obtain ⟨i, hi⟩ := hnot
    have hai : 0 < ⟪a i, w⟫_ℝ := by
      rw [inner_add_right, real_inner_smul_right] at hi
      have := hy₀ i
      exact pos_of_mul_pos_right (by linarith) hτ
    have hbound : ∀ s : ℝ, 0 ≤ s → s * ⟪a i, w⟫_ℝ ≤ r := by
      intro s hs
      have hd : s • a i ∈ effectiveDomain (plqPenalty Y B) :=
        mem_effectiveDomain_plqPenalty_of_le (c := s * b i) fun y hy ↦ by
          rw [hrep] at hy
          rw [real_inner_smul_right, real_inner_comm]
          nlinarith [hBpos y, mul_le_mul_of_nonneg_left (hy i) hs]
      have := hr _ hd
      rwa [real_inner_smul_right, real_inner_comm] at this
    linarith [nonpos_of_forall_mul_le hbound]
  · apply eq_zero_of_inner_map_self_eq_zero hB hBpos
    have hbound : ∀ s : ℝ, 0 ≤ s → s * ⟪w, B w⟫_ℝ ≤ r := by
      intro s hs
      have hd : s • B w ∈ effectiveDomain (plqPenalty Y B) :=
        mem_effectiveDomain_plqPenalty_of_le (c := (1 / 2) * s ^ 2 * ⟪w, B w⟫_ℝ) fun y _ ↦ by
          have hpsd := hBpos (y - s • w)
          have hwy : ⟪w, B y⟫_ℝ = ⟪y, B w⟫_ℝ := by rw [← hB, real_inner_comm]
          simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
            real_inner_smul_right, hwy] at hpsd
          rw [real_inner_smul_right]
          nlinarith
      have := hr _ hd
      rwa [real_inner_smul_right] at this
    exact le_antisymm (nonpos_of_forall_mul_le hbound) (hBpos w)

include hY hne hB in
/-- Along `Y^∞ ∩ ker B` the penalty objective grows linearly, so points of `dom θ_{Y,B}` lie in
the polar cone. -/
theorem effectiveDomain_plqPenalty_subset_polarCone :
    effectiveDomain (plqPenalty Y B) ⊆ polarCone (horizonCone Y ∩ {w | B w = 0}) := by
  intro u hu w ⟨hw, hBw⟩
  obtain ⟨y₀, hy₀⟩ := hne
  have hval : ∀ t : ℝ, 0 ≤ t → ((t * ⟪w, u⟫_ℝ + (⟪y₀, u⟫_ℝ - (1 / 2) * ⟪y₀, B y₀⟫_ℝ) : ℝ) : EReal)
      ≤ plqPenalty Y B u := by
    intro t ht
    have hyt := smul_add_mem_of_mem_horizonCone hY.convex hY.isClosed hy₀ hw ht
    refine le_trans (le_of_eq ?_) (le_iSup₂_of_le (t • w + y₀) hyt le_rfl)
    have hBw' : B w = 0 := hBw
    have hwy : ⟪w, B y₀⟫_ℝ = 0 := by rw [← hB, hBw', inner_zero_left]
    simp only [map_add, map_smul, hBw', smul_zero, zero_add, inner_add_left,
      real_inner_smul_left, hwy]
    congr 1
    ring
  have hne_bot : plqPenalty Y B u ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hval 0 le_rfl)
  set R := (plqPenalty Y B u).toReal with hR
  have hRe : plqPenalty Y B u = R := (EReal.coe_toReal hu.ne hne_bot).symm
  have hbound : ∀ t : ℝ, 0 ≤ t →
      t * ⟪w, u⟫_ℝ ≤ R - (⟪y₀, u⟫_ℝ - (1 / 2) * ⟪y₀, B y₀⟫_ℝ) := by
    intro t ht
    have := hval t ht
    rw [hRe, EReal.coe_le_coe_iff] at this
    linarith
  rw [real_inner_comm]
  exact nonpos_of_forall_mul_le hbound

include hY hne hB hBpos in
/-- **Example 11.18**, `dom θ_{Y,B} = (Y^∞ ∩ ker B)*`. -/
theorem effectiveDomain_plqPenalty :
    effectiveDomain (plqPenalty Y B) = polarCone (horizonCone Y ∩ {w | B w = 0}) := by
  refine Subset.antisymm (effectiveDomain_plqPenalty_subset_polarCone hY hne hB) ?_
  intro u hu
  have hpoly := (plqPenalty_properties hY hne hB hBpos).2.2.2.isPolyhedral_effectiveDomain
    (plqPenalty_properties hY hne hB hBpos).2.2.1
  obtain ⟨n, c, e, hrep⟩ := hpoly.isHPolyhedral.exists_inner_representation
  by_contra hnot
  rw [hrep] at hnot
  simp only [mem_setOf_eq, not_forall, not_le] at hnot
  obtain ⟨j, hj⟩ := hnot
  have h0 := zero_mem_effectiveDomain_plqPenalty (Y := Y) hBpos
  rw [hrep] at h0
  have hej : 0 ≤ e j := by simpa using h0 j
  have hK := mem_horizonCone_and_ker_of_bddAbove hY hne hB hBpos (w := c j) (r := e j)
    fun d hd ↦ by rw [hrep] at hd; exact hd j
  have := hu (c j) hK
  rw [real_inner_comm] at this
  linarith

include hY hne hB hBpos in
/-- **Example 11.18**, the domain of `θ_{Y,B}` is a polyhedral cone. -/
theorem isPolyhedral_effectiveDomain_plqPenalty :
    IsPolyhedral (effectiveDomain (plqPenalty Y B)) ∧
      ∀ u ∈ effectiveDomain (plqPenalty Y B), ∀ t : ℝ, 0 ≤ t →
        t • u ∈ effectiveDomain (plqPenalty Y B) := by
  refine ⟨(plqPenalty_properties hY hne hB hBpos).2.2.2.isPolyhedral_effectiveDomain
    (plqPenalty_properties hY hne hB hBpos).2.2.1, fun u hu t ht ↦ ?_⟩
  rw [effectiveDomain_plqPenalty hY hne hB hBpos] at hu ⊢
  intro w hw
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos ht (hu w hw)

include hY hne hB hBpos in
/-- **Example 11.18**, `dom θ_{Y,B}` is the whole space iff `Y^∞ ∩ ker B = {0}`. -/
theorem effectiveDomain_plqPenalty_eq_univ_iff :
    effectiveDomain (plqPenalty Y B) = univ ↔ horizonCone Y ∩ {w | B w = 0} = {0} := by
  rw [effectiveDomain_plqPenalty hY hne hB hBpos]
  constructor
  · intro h
    refine Subset.antisymm (fun w hw ↦ ?_) ?_
    · have hw' : w ∈ polarCone (horizonCone Y ∩ {w | B w = 0}) := h ▸ mem_univ w
      have := hw' w hw
      exact mem_singleton_iff.2 (real_inner_self_nonpos.1 this)
    · rintro w rfl
      exact ⟨zero_mem_horizonCone Y, map_zero B⟩
  · intro h
    rw [h]
    ext u
    simp [polarCone]

include hY hne hB hBpos in
/-- **Example 11.18**, `∂^∞θ_{Y,B}(u) = N_{dom θ}(u) = {y ∈ Y^∞ ∩ ker B | ⟪y, u⟫ = 0}`. -/
theorem horizonSubdifferential_plqPenalty {u : E} (hu : u ∈ effectiveDomain (plqPenalty Y B)) :
    horizonSubdifferential (plqPenalty Y B) u = normalCone (effectiveDomain (plqPenalty Y B)) u ∧
      horizonSubdifferential (plqPenalty Y B) u =
        {y | (y ∈ horizonCone Y ∧ B y = 0) ∧ ⟪y, u⟫_ℝ = 0} := by
  obtain ⟨hp, hl, hc, hplq⟩ := plqPenalty_properties hY hne hB hBpos
  have hfin : plqPenalty Y B u = ((plqPenalty Y B u).toReal : EReal) :=
    (EReal.coe_toReal hu.ne (hp.2 u).ne').symm
  have hll : IsLocallyLscAt (plqPenalty Y B) u :=
    isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin (RW.IsClosed.isLocallyClosedAt
      (isClosed_epigraph_of_lsc_ereal _ hl) _)
  have hN := horizonSubdifferential_eq_normalCone_domain_of_locallyLsc hc hp hll hfin
  refine ⟨hN, ?_⟩
  have hconv := (hplq.isPolyhedral_effectiveDomain hc).convex
  rw [hN, normalCone_eq_regularNormalCone_of_convex hconv hu,
    regularNormalCone_eq_of_convex hconv hu]
  have hdom := effectiveDomain_plqPenalty hY hne hB hBpos
  ext y
  simp only [mem_setOf_eq]
  constructor
  · intro h
    have h0 := h 0 (zero_mem_effectiveDomain_plqPenalty hBpos)
    have h2 := h ((2 : ℝ) • u) ((isPolyhedral_effectiveDomain_plqPenalty hY hne hB hBpos).2 u hu 2
      (by norm_num))
    rw [zero_sub, inner_neg_right] at h0
    rw [show (2 : ℝ) • u - u = u by module] at h2
    have hyu : ⟪y, u⟫_ℝ = 0 := le_antisymm h2 (by linarith)
    refine ⟨mem_horizonCone_and_ker_of_bddAbove hY hne hB hBpos (r := 0) fun d hd ↦ ?_, hyu⟩
    have := h d hd
    rwa [inner_sub_right, hyu, sub_zero] at this
  · rintro ⟨hK, hyu⟩ d hd
    rw [hdom] at hd
    rw [inner_sub_right, hyu, sub_zero, real_inner_comm]
    exact hd y hK

include hY hne hB hBpos in
/-- **Example 11.18**, for `u ∈ dom θ_{Y,B}` the sets `∂θ(u)` and `∂^∞θ(u)` are polyhedral, and
`dθ(u)` is piecewise linear and is the support function of `∂θ(u) = (N_Y + B)⁻¹(u)`. -/
theorem plqPenalty_subgradient_properties {u : E}
    (hu : u ∈ effectiveDomain (plqPenalty Y B)) :
    IsPolyhedral (subdifferential (plqPenalty Y B) u) ∧
      IsPolyhedral (horizonSubdifferential (plqPenalty Y B) u) ∧
      IsPiecewiseLinear (subderivative (plqPenalty Y B) u) ∧
      subderivative (plqPenalty Y B) u =
        supportFunction {y | y ∈ Y ∧ u - B y ∈ normalCone Y y} := by
  obtain ⟨-, -, hc, hplq⟩ := plqPenalty_properties hY hne hB hBpos
  obtain ⟨-, hpoly, hhpoly⟩ := hplq.convex_subgradient_properties hc hu
  refine ⟨hpoly, hhpoly, (hplq.subderivative_piecewiseLinear hu).1, ?_⟩
  rw [hplq.subderivative_eq_support hc hu, subdifferential_plqPenalty hY hne hB hBpos]

end PenaltyDomain

end RW
