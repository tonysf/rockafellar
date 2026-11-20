/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Vertical epigraph tangents in Exercises 8.35 and 8.44
-/

import RockafellarWets.Chapter8.GraphicalDerivatives
import RockafellarWets.Chapter8.EpigraphNormals

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

/-- A continuous, finite function which is flat on the positive half-line
and decreases as a negative square root on the negative half-line. -/
noncomputable def downwardCusp (x : ℝ) : EReal := ((-Real.sqrt (-x) : ℝ) : EReal)

theorem continuous_downwardCusp : Continuous downwardCusp :=
  continuous_coe_real_ereal.comp (Real.continuous_sqrt.comp continuous_neg).neg

/-- The full vertical line lies in the tangent epigraph for any extension
of the negative square-root branch. -/
private theorem subderivative_zero_of_negative_cusp {f : ℝ → EReal}
    (hc : ∀ x ≤ 0, f x = downwardCusp x) : subderivative f 0 0 = ⊥ := by
  have h₀ : f 0 = ((0 : ℝ) : EReal) := by simp [hc 0 le_rfl, downwardCusp]
  have hepi (b : ℝ) : subderivative f 0 0 ≤ (b : EReal) := by
    change ((0:ℝ), b) ∈ epigraph (subderivative f 0)
    rw [epigraph_subderivative_eq_tangentCone h₀]
    let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
    have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    have ht₀ : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    let p (n : ℕ) : ℝ × ℝ := (-((t n*b)^2), t n*b)
    have hp (n : ℕ) : p n ∈ epigraph f := by
      change f (-((t n*b)^2)) ≤ ((t n*b : ℝ) : EReal)
      rw [hc _ (neg_nonpos.mpr (sq_nonneg _)), downwardCusp, neg_neg, Real.sqrt_sq_eq_abs,
        EReal.coe_le_coe_iff]
      exact neg_abs_le _
    apply mem_tangentCone_of_forall hp ht ht₀
    have hq (n : ℕ) : (t n)⁻¹ • (p n - ((0:ℝ),0)) = (-t n*b^2,b) := by
      apply Prod.ext
      · change (t n)⁻¹ * (-((t n*b)^2) - 0) = -t n*b^2
        field_simp [(ht n).ne']; ring
      · change (t n)⁻¹ * (t n*b-0) = b
        field_simp [(ht n).ne']; ring
    simp_rw [hq]
    exact (by simpa using (ht₀.neg.mul_const (b^2)).prodMk_nhds (tendsto_const_nhds (x := b)))
  by_contra h
  obtain ⟨b,_,hb⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr h)
  exact hb.not_ge (hepi b)

theorem subderivative_downwardCusp_zero : subderivative downwardCusp 0 0 = ⊥ :=
  subderivative_zero_of_negative_cusp (fun _ _ ↦ rfl)

theorem subderivative_downwardCusp_of_pos {w : ℝ} (hw : 0 < w) :
    subderivative downwardCusp 0 w = 0 := by
  have h₀ : downwardCusp 0 = 0 := by simp [downwardCusp]
  apply HasSemiderivative.subderivative_eq
  refine ⟨by simp [h₀],by simp [h₀],tendsto_const_nhds.congr' ?_⟩
  filter_upwards [prod_mem_prod (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0) (Ioi_mem_nhds hw)]
    with p hp
  have hneg : -(p.1 * p.2) ≤ 0 := neg_nonpos.mpr (mul_nonneg hp.1.le hp.2.le)
  simp [differenceQuotient, downwardCusp, smul_eq_mul, Real.sqrt_eq_zero_of_nonpos hneg]

/-- **Obstruction to the printed 8.44(b)**. The subderivative is finite and
locally constant at direction one, but has value minus infinity at zero.
Both subdifferentials in the claimed first inclusions can therefore fail. -/
theorem subdifferentials_of_subderivative_counterexample :
    let h := subderivative downwardCusp 0
    Continuous downwardCusp ∧ downwardCusp 0 = 0 ∧ h 1 = 0 ∧ h 0 = ⊥ ∧
      (0:ℝ) ∈ subdifferential h 1 ∧ subdifferential h 0 = ∅ ∧
      (0:ℝ) ∈ horizonSubdifferential h 1 ∧ horizonSubdifferential h 0 = ∅ := by
  let h := subderivative downwardCusp 0
  have h₁ : h 1 = ((0:ℝ) : EReal) := subderivative_downwardCusp_of_pos zero_lt_one
  have hr : 0 ∈ regularSubdifferential h 1 := by
    refine ⟨0,h₁,fun ε hε ↦ ?_⟩
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0:ℝ) < 1)] with y hy
    rw [show h y = ((0:ℝ) : EReal) from subderivative_downwardCusp_of_pos hy, EReal.coe_le_coe_iff]
    simp [mul_nonneg hε.le (abs_nonneg (y-1))]
  have hnf : ¬ ∃ c : ℝ, h 0 = c := by
    rintro ⟨c,hc⟩
    exact (EReal.coe_ne_bot c) (hc.symm.trans subderivative_downwardCusp_zero)
  exact ⟨continuous_downwardCusp,by simp [downwardCusp],h₁,subderivative_downwardCusp_zero,
    regularSubdifferential_subset_subdifferential _ _ hr,eq_empty_iff_forall_notMem.mpr fun _ hv ↦ hnf hv.1,
    (subdifferential_properties h₁).2.2.2.2.1.1,eq_empty_iff_forall_notMem.mpr fun _ hv ↦ hnf hv.1⟩

/-- The same downward cusp restricted to the closed negative half-line. -/
noncomputable def restrictedDownwardCusp (x : ℝ) : EReal := if x ≤ 0 then downwardCusp x else ⊤

theorem lowerSemicontinuous_restrictedDownwardCusp : LowerSemicontinuous restrictedDownwardCusp := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  have he : epigraph restrictedDownwardCusp = epigraph downwardCusp ∩
      (Prod.fst ⁻¹' Iic (0:ℝ)) := by
    ext p
    change (if p.1 ≤ 0 then downwardCusp p.1 else ⊤) ≤ (p.2:EReal) ↔
      downwardCusp p.1 ≤ (p.2:EReal) ∧ p.1 ≤ 0
    by_cases hx : p.1 ≤ 0 <;> simp [hx, (EReal.coe_lt_top p.2).not_ge]
  rw [he]
  exact (isClosed_epigraph_of_lsc_ereal _ continuous_downwardCusp.lowerSemicontinuous).inter
    (isClosed_Iic.preimage continuous_fst)

/-- **Obstruction to the printed 8.35 zero-height regular coderivative
branch**. A missing affine minorant does not rule out a nonzero horizontal
normal. -/
theorem regularCoderivative_emptySubgradient_counterexample :
    let f := restrictedDownwardCusp
    LowerSemicontinuous f ∧ f 0 = 0 ∧ regularSubdifferential f 0 = ∅ ∧
      (1:ℝ) ∈ regularCoderivative (epiProfile f) 0 0 0 := by
  have h₀ : restrictedDownwardCusp 0 = ((0:ℝ) : EReal) := by simp [restrictedDownwardCusp, downwardCusp]
  refine ⟨lowerSemicontinuous_restrictedDownwardCusp,h₀,eq_empty_iff_forall_notMem.mpr ?_,?_⟩
  · intro v hv
    have hh := (mem_regularSubdifferential_iff_inner_le_subderivative h₀).mp hv 0
    rw [subderivative_zero_of_negative_cusp (f := restrictedDownwardCusp) (fun y hy ↦ if_pos hy)] at hh
    exact (EReal.bot_lt_coe _).not_ge hh
  · refine ⟨h₀.le,fun ε hε ↦ ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : restrictedDownwardCusp q.fst ≤ (q.snd : EReal) := hq
    have hfst : q.fst ≤ 0 := by
      by_contra hn
      rw [restrictedDownwardCusp,if_neg hn] at hq'
      exact (EReal.coe_lt_top _).not_ge hq'
    apply le_trans _ (mul_nonneg hε.le (norm_nonneg _))
    change (q.fst - 0) * 1 + (q.snd - 0) * -(0:ℝ) ≤ 0
    simpa using hfst

end RW
