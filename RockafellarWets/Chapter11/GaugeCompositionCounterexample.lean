/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# An infinite-gauge obstruction to Proposition 11.21

For the epigraph of the square and the even closed convex function δ_{0},
the conjugate of the gauge composite takes different values at two vectors
having the same infinite polar gauge. Thus no choice of the value of the
outer conjugate at infinity can give the displayed formula in full generality.
-/
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter10.MonotoneRescalingRepresentation

open Set
open scoped InnerProductSpace
namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem extendedRescaling_indicator_zero_gaugeFunction {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0:E) ∈ C) :
    extendedRescaling (indicatorVA ({0}:Set ℝ)) (gaugeFunction C) = indicatorVA (horizonCone C) := by
  funext x
  have he := gaugeFunction_eq_zero_iff_mem_horizonCone hc hclosed h0 (x := x)
  by_cases hx : x ∈ horizonCone C
  · simp [extendedRescaling,he.mpr hx,indicatorVA_apply_mem hx]
  · rw [indicatorVA_apply_not_mem hx]
    have hn : gaugeFunction C x ≠ 0 := fun h ↦ hx (he.mp h)
    cases hval : gaugeFunction C x with
    | bot => exact ((nonneg_gaugeFunction C x).not_gt (by simp [hval])).elim
    | top => simp [extendedRescaling,hval]
    | coe r =>
      have hr : r ≠ 0 := fun h ↦ hn (by simpa [h] using hval)
      simp [extendedRescaling,hval,indicatorVA,hr]

abbrev GaugeCounterPlane := WithLp 2 (ℝ × ℝ)

def squareGaugeSet : Set GaugeCounterPlane := {p | p.fst^2 ≤ p.snd}

theorem squareGaugeSet_closed : IsClosed squareGaugeSet :=
  isClosed_le (by fun_prop) (by fun_prop)

theorem squareGaugeSet_zero : (0:GaugeCounterPlane) ∈ squareGaugeSet := by
  norm_num [squareGaugeSet]

theorem squareGaugeSet_convex : Convex ℝ squareGaugeSet := by
  intro p hp q hq a b ha hb hab
  change (a*p.fst+b*q.fst)^2 ≤ a*p.snd+b*q.snd
  change p.fst^2 ≤ p.snd at hp
  change q.fst^2 ≤ q.snd at hq
  have he : a*p.fst^2+b*q.fst^2-(a*p.fst+b*q.fst)^2 = a*b*(p.fst-q.fst)^2 := by
    have hb' : b=1-a := by linarith
    rw [hb']; ring
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.fst-q.fst)),
    mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hq hb]

theorem fst_eq_zero_of_mem_horizonCone_squareGaugeSet {p : GaugeCounterPlane}
    (hp : p ∈ horizonCone squareGaugeSet) : p.fst = 0 := by
  have hall (t : ℝ) (ht : 0 ≤ t) : (t*p.fst)^2 ≤ t*p.snd := by
    have h := smul_add_mem_of_mem_horizonCone squareGaugeSet_convex squareGaugeSet_closed
      squareGaugeSet_zero hp ht
    simpa [squareGaugeSet] using h
  by_contra hn
  have hsq : 0 < p.fst^2 := sq_pos_of_ne_zero hn
  let t : ℝ := (|p.snd|+1)/p.fst^2
  have ht : 0 < t := div_pos (by positivity) hsq
  have h := hall t ht.le
  have he : t*p.fst^2 = |p.snd|+1 := div_mul_cancel₀ _ hsq.ne'
  have hmul : t*(t*p.fst^2) ≤ t*p.snd := by nlinarith only [h]
  have hb : t*p.fst^2 ≤ p.snd :=
    (mul_le_mul_iff_right₀ ht).mp (by nlinarith only [hmul])
  nlinarith [le_abs_self p.snd]

theorem vertical_mem_horizonCone_squareGaugeSet {r : ℝ} (hr : 0 ≤ r) :
    WithLp.toLp 2 (0,r) ∈ horizonCone squareGaugeSet := by
  apply mem_horizonCone_of_forall_smul_add_mem (x := (0:GaugeCounterPlane))
  intro t ht
  change (t*0+0)^2 ≤ t*r+0
  nlinarith [mul_nonneg ht hr]

def squareGaugeHorizontal : GaugeCounterPlane := WithLp.toLp 2 (1,0)
def squareGaugeVertical : GaugeCounterPlane := WithLp.toLp 2 (0,1)

noncomputable def squareGaugeComposite : GaugeCounterPlane → EReal :=
  extendedRescaling (indicatorVA ({0}:Set ℝ)) (gaugeFunction squareGaugeSet)

theorem squareGaugeComposite_eq : squareGaugeComposite = indicatorVA (horizonCone squareGaugeSet) :=
  extendedRescaling_indicator_zero_gaugeFunction squareGaugeSet_convex squareGaugeSet_closed squareGaugeSet_zero

theorem squareGaugeHorizontal_polarGauge :
    gaugeFunction (polarSet squareGaugeSet) squareGaugeHorizontal = ⊤ := by
  rw [gaugeFunction_polarSet_eq_supportFunction squareGaugeSet_convex squareGaugeSet_closed squareGaugeSet_zero]
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  have hm : WithLp.toLp 2 (r+1,(r+1)^2) ∈ squareGaugeSet := by
    change (r+1)^2 ≤ (r+1)^2; exact le_rfl
  have h := inner_le_supportFunction hm squareGaugeHorizontal
  simp only [squareGaugeHorizontal,WithLp.prod_inner_apply,WithLp.toLp_fst,WithLp.toLp_snd,
    RCLike.inner_apply, conj_trivial, mul_one,mul_zero,one_mul,zero_mul,add_zero] at h
  exact (EReal.coe_lt_coe_iff.mpr (by linarith : r < r+1)).trans_le h

theorem squareGaugeVertical_polarGauge :
    gaugeFunction (polarSet squareGaugeSet) squareGaugeVertical = ⊤ := by
  rw [gaugeFunction_polarSet_eq_supportFunction squareGaugeSet_convex squareGaugeSet_closed squareGaugeSet_zero]
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  have hm : WithLp.toLp 2 (0,|r|+1) ∈ squareGaugeSet := by
    change (0:ℝ)^2 ≤ |r|+1; nlinarith [abs_nonneg r]
  have h := inner_le_supportFunction hm squareGaugeVertical
  simp only [squareGaugeVertical,WithLp.prod_inner_apply,WithLp.toLp_fst,WithLp.toLp_snd,
    RCLike.inner_apply, conj_trivial,mul_one,mul_zero,one_mul,zero_mul,zero_add] at h
  exact (EReal.coe_lt_coe_iff.mpr (by linarith [le_abs_self r] : r < |r|+1)).trans_le h

theorem squareGaugeComposite_conjugate_horizontal :
    fenchelConjugate squareGaugeComposite squareGaugeHorizontal = 0 := by
  rw [squareGaugeComposite_eq,fenchelConjugate_indicatorVA]
  apply le_antisymm
  · apply (supportFunction_le_iff _ _ _).mpr
    intro p hp
    simp [squareGaugeHorizontal,WithLp.prod_inner_apply,RCLike.inner_apply,
      fst_eq_zero_of_mem_horizonCone_squareGaugeSet hp]
  · simpa using inner_le_supportFunction (zero_mem_horizonCone squareGaugeSet) squareGaugeHorizontal

theorem squareGaugeComposite_conjugate_vertical :
    fenchelConjugate squareGaugeComposite squareGaugeVertical = ⊤ := by
  rw [squareGaugeComposite_eq,fenchelConjugate_indicatorVA]
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  have h := inner_le_supportFunction (vertical_mem_horizonCone_squareGaugeSet
    (show 0 ≤ |r|+1 by positivity)) squareGaugeVertical
  simp only [squareGaugeVertical,WithLp.prod_inner_apply,WithLp.toLp_fst,WithLp.toLp_snd,
    RCLike.inner_apply, conj_trivial,mul_one,mul_zero,one_mul,zero_mul,zero_add] at h
  exact (EReal.coe_lt_coe_iff.mpr (by linarith [le_abs_self r] : r < |r|+1)).trans_le h

/-- No scalar extension at infinity repairs 11.21 for the square epigraph and δ₀. -/
theorem gaugeComposition_no_scalar_extension :
    ¬ ∃ Θ : EReal → EReal, fenchelConjugate squareGaugeComposite =
      fun v ↦ Θ (gaugeFunction (polarSet squareGaugeSet) v) := by
  rintro ⟨Θ,hΘ⟩
  have hh := congrFun hΘ squareGaugeHorizontal
  have hv := congrFun hΘ squareGaugeVertical
  rw [squareGaugeHorizontal_polarGauge,squareGaugeComposite_conjugate_horizontal] at hh
  rw [squareGaugeVertical_polarGauge,squareGaugeComposite_conjugate_vertical] at hv
  exact (show (0:EReal) ≠ ⊤ by simp) (hh.trans hv.symm)

/-- All the set and outer-function hypotheses printed in 11.21 hold. -/
theorem gaugeComposition_counterexample_hypotheses :
    IsClosed squareGaugeSet ∧ Convex ℝ squareGaugeSet ∧ (0:GaugeCounterPlane) ∈ squareGaugeSet ∧
      IsProper (indicatorVA ({0}:Set ℝ)) ∧ LowerSemicontinuous (indicatorVA ({0}:Set ℝ)) ∧
      Convex ℝ (epigraph (indicatorVA ({0}:Set ℝ))) ∧
      (∀r:ℝ, indicatorVA ({0}:Set ℝ) (-r) = indicatorVA ({0}:Set ℝ) r) := by
  refine ⟨squareGaugeSet_closed,squareGaugeSet_convex,squareGaugeSet_zero,
    (indicatorVA_isProper_iff _).mpr ⟨0,by simp⟩,
    lowerSemicontinuous_indicatorVA isClosed_singleton, ?_, ?_⟩
  · rw [epigraph_indicatorVA]
    exact (convex_singleton 0).prod (convex_Ici 0)
  · intro r; simp [indicatorVA]

end RW
