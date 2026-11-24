/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dual formulas for augmented Lagrangians

Formula 11(28) of Exercise 11.56 and the dual expressions for the proximal
and sharp Lagrangians of Examples 11.57 and 11.58. For each `x`, `-l̄(x,·,r)`
is conjugate to `f(x,·) + rσ`; when `σ` is finite the interior form of the
sum rule in 11.23(a) splits that conjugate into an infimal convolution of
`-l(x,·)` and `(rσ)* = rσ*(·/r)`.
-/
import RockafellarWets.Chapter11.ExactPenaltyExamples
import RockafellarWets.Chapter11.SelfConjugacy
import RockafellarWets.Chapter11.DualOperationQualifications

open Set Filter Topology Metric
open scoped InnerProductSpace Pointwise
namespace RW
noncomputable section

section Scaling

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- Positive scaling commutes with the subtraction in a conjugate term. -/
theorem ereal_coe_sub_coe_mul {r : ℝ} (hr : 0 < r) (t : ℝ) (a : EReal) :
    (t : EReal) - (r : EReal) * a = (r : EReal) * (((r⁻¹ * t : ℝ) : EReal) - a) := by
  induction a using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hr, EReal.sub_bot (EReal.coe_ne_bot _),
      EReal.sub_bot (EReal.coe_ne_bot _), EReal.coe_mul_top_of_pos hr]
  | top => rw [EReal.coe_mul_top_of_pos hr, EReal.sub_top, EReal.sub_top,
      EReal.coe_mul_bot_of_pos hr]
  | coe a =>
    rw [← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul]
    congr 1
    field_simp

theorem fenchelConjugate_coe_mul_le (g : P → EReal) {r : ℝ} (hr : 0 < r) (w : P) :
    fenchelConjugate (fun u ↦ (r : EReal) * g u) w ≤
      (r : EReal) * fenchelConjugate g (r⁻¹ • w) := by
  rw [fenchelConjugate_le_iff]
  intro u
  have h := mul_le_mul_of_nonneg_left (le_fenchelConjugate g u (r⁻¹ • w))
    (EReal.coe_nonneg.mpr hr.le)
  refine le_trans (le_of_eq ?_) h
  rw [real_inner_smul_left, ereal_coe_sub_coe_mul hr]

/-- The conjugate of a positive multiple, `(rg)*(w) = r g*(w/r)`, as in 11(3). -/
theorem fenchelConjugate_coe_mul (g : P → EReal) {r : ℝ} (hr : 0 < r) (w : P) :
    fenchelConjugate (fun u ↦ (r : EReal) * g u) w =
      (r : EReal) * fenchelConjugate g (r⁻¹ • w) := by
  apply le_antisymm (fenchelConjugate_coe_mul_le g hr w)
  have h := fenchelConjugate_coe_mul_le (fun u ↦ (r : EReal) * g u) (inv_pos.mpr hr) (r⁻¹ • w)
  have hg : (fun u ↦ ((r⁻¹ : ℝ) : EReal) * ((r : EReal) * g u)) = g := by
    funext u
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hr.ne', EReal.coe_one, one_mul]
  rw [hg, inv_inv] at h
  calc (r : EReal) * fenchelConjugate g (r⁻¹ • w)
      ≤ (r : EReal) * (((r⁻¹ : ℝ) : EReal) *
          fenchelConjugate (fun u ↦ (r : EReal) * g u) (r • r⁻¹ • w)) :=
        mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hr.le)
    _ = fenchelConjugate (fun u ↦ (r : EReal) * g u) w := by
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, ← mul_assoc, ← EReal.coe_mul,
          mul_inv_cancel₀ hr.ne', EReal.coe_one, one_mul]

theorem IsAugmentingFunction.fenchelConjugate_zero {σ : P → EReal} (hσ : IsAugmentingFunction σ) :
    fenchelConjugate σ 0 = 0 := by
  apply le_antisymm
  · rw [fenchelConjugate_le_iff]
    intro u
    rw [inner_zero_left, EReal.coe_zero, zero_sub]
    simpa using EReal.neg_le_neg_iff.mpr (hσ.nonneg u)
  · have h := le_fenchelConjugate σ 0 0
    rwa [inner_zero_left, hσ.zero, EReal.coe_zero, sub_zero] at h

theorem IsAugmentingFunction.fenchelConjugate_nonneg {σ : P → EReal}
    (hσ : IsAugmentingFunction σ) (v : P) : 0 ≤ fenchelConjugate σ v := by
  have h := le_fenchelConjugate σ 0 v
  rwa [inner_zero_right, hσ.zero, EReal.coe_zero, sub_zero] at h

end Scaling

section Formula

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  {f : WithLp 2 (E × P) → EReal} {σ : P → EReal}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exercise 11.56**, formula 11(28): for a finite augmenting function,
`l̄(x,y,r) = sup_z {l(x,y-z) - rσ*(r⁻¹z)}`. -/
theorem augmentedLagrangian_eq_iSup_lagrangian
    (hf : IsDualizingParameterization (primalObjective f) f) (hσ : IsAugmentingFunction σ)
    (hσt : ∀ u, σ u ≠ ⊤) {r : ℝ} (hr : 0 < r) (x : E) (y : P) :
    augmentedLagrangian f σ x y r =
      ⨆ z, lagrangian f x (y - z) - (r : EReal) * fenchelConjugate σ (r⁻¹ • z) := by
  rcases hf.slice_cases x with ⟨hp, hl, hc⟩ | htop
  · have hq : IsProper (fun u ↦ (r : EReal) * σ u) :=
      ⟨⟨0, by change (r : EReal) * σ 0 < ⊤; rw [hσ.zero, mul_zero]; exact EReal.zero_lt_top⟩,
        fun u ↦ bot_lt_iff_ne_bot.mpr (hσ.coe_mul_ne_bot hr.le u)⟩
    have hk := lowerSemicontinuous_const_mul hσ.lowerSemicontinuous hr
    have hd := convex_epigraph_coe_mul hσ.convex hr
    have hdom : effectiveDomain (fun u ↦ (r : EReal) * σ u) = univ := by
      refine eq_univ_of_forall fun u ↦ ?_
      obtain ⟨s, hs⟩ : ∃ s : ℝ, σ u = s :=
        ⟨_, (EReal.coe_toReal (hσt u) (hσ.isProper.2 u).ne').symm⟩
      change (r : EReal) * σ u < ⊤
      rw [hs, ← EReal.coe_mul]
      exact EReal.coe_lt_top _
    have h0 : (0 : P) ∈ interior (effectiveDomain (parameterSlice f x) -
        effectiveDomain (fun u ↦ (r : EReal) * σ u)) := by
      obtain ⟨u₀, hu₀⟩ := hp.1
      have he : effectiveDomain (parameterSlice f x) -
          effectiveDomain (fun u ↦ (r : EReal) * σ u) = univ := by
        rw [hdom]
        exact eq_univ_of_forall fun v ↦ ⟨u₀, hu₀, u₀ - v, mem_univ _, sub_sub_cancel u₀ v⟩
      rw [he, interior_univ]
      exact mem_univ _
    have hconj := fenchelConjugate_add_of_interior hp hq hl hk hc hd h0
    rw [augmentedLagrangian_eq_neg_fenchelConjugate]
    change -fenchelConjugate (fun u ↦ parameterSlice f x u + (r : EReal) * σ u) y = _
    rw [hconj, epiSum_apply, show ∀ g : P → EReal, -(⨅ w, g w) = ⨆ w, -g w from
      fun g ↦ EReal.negOrderIso.map_iInf g]
    refine iSup_congr fun z ↦ ?_
    change -(fenchelConjugate (parameterSlice f x) (y - z) +
      fenchelConjugate (fun u ↦ (r : EReal) * σ u) z) = _
    have hgb : fenchelConjugate (parameterSlice f x) (y - z) ≠ ⊥ := by
      obtain ⟨u₀, hu₀⟩ := hp.1
      obtain ⟨a, ha⟩ : ∃ a : ℝ, parameterSlice f x u₀ = a :=
        ⟨_, (EReal.coe_toReal hu₀.ne (hp.2 u₀).ne').symm⟩
      have h := le_fenchelConjugate (parameterSlice f x) u₀ (y - z)
      rw [ha, ← EReal.coe_sub] at h
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h
    rw [fenchelConjugate_coe_mul σ hr, lagrangian_eq_neg_fenchelConjugate,
      EReal.neg_add (Or.inl hgb) (Or.inr ((EReal.mul_nonneg (EReal.coe_nonneg.mpr hr.le)
        (hσ.fenchelConjugate_nonneg _)).trans_lt' EReal.bot_lt_zero).ne'), sub_eq_add_neg]
  · have hl : lagrangian f x y = ⊤ := by
      rw [lagrangian_eq_neg_fenchelConjugate]
      rw [htop, identically_top_conjugates.1]
      rfl
    have hL : augmentedLagrangian f σ x y r = ⊤ := by
      refine le_antisymm le_top (le_iInf fun u ↦ ?_)
      have h := congrFun htop u
      change f (WithLp.toLp 2 (x, u)) = ⊤ at h
      rw [h, EReal.top_add_of_ne_bot (hσ.coe_mul_ne_bot hr.le u), EReal.top_sub_coe]
    rw [hL]
    refine le_antisymm (le_iSup_of_le 0 ?_) le_top
    rw [sub_zero, hl, smul_zero, hσ.fenchelConjugate_zero, mul_zero, sub_zero]

end Formula

end
end RW
