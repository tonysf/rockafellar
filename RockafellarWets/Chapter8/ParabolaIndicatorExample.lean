/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The parabola example printed after Definition 7.23

For the indicator `f = δ_C` of `C = {(x₁, x₂) | x₂ = x₁²}` at `x̄ = (0, 0)`:

* `df(x̄)(w) = 0` if `w₂ = 0` and `∞` otherwise;
* the one-sided directional derivative is `f'(x̄; w) = 0` if `w = 0` and `∞`
  otherwise.

So at `w = (1, 0)` the one-sided directional derivative exists but differs
from `df(x̄)(w)`, and `f` is not semidifferentiable there; directional
derivatives along rays miss the curved set entirely.  The computation of
`df(x̄)` uses Theorem 8.2(b), `dδ_C(x̄) = δ_{T_C(x̄)}`, with
`T_C(x̄) = {w | w₂ = 0}`.  The file sits in Chapter 8 only because it uses
8.2(b).
-/

import RockafellarWets.Chapter8.SubderivativeFormulas

open Filter Set Topology Metric

namespace RW

/-- The parabola `x₂ = x₁²` in `ℝ × ℝ`. -/
def parabola : Set (ℝ × ℝ) := {p | p.2 = p.1 ^ 2}

theorem zero_mem_parabola : (0 : ℝ × ℝ) ∈ parabola := by
  simp [parabola]

/-- The tangent cone to the parabola at the origin is the horizontal axis. -/
theorem tangentCone_parabola_zero : tangentCone parabola 0 = {w | w.2 = 0} := by
  ext w
  constructor
  · rintro ⟨xs, τs, hxC, hxto, hτ, hτ0, hq⟩
    simp only [sub_zero] at hq
    have h1 : Tendsto (fun n ↦ (τs n)⁻¹ * (xs n).1) atTop (𝓝 w.1) := by
      have := (continuous_fst.tendsto w).comp hq
      simpa using this
    have h2 : Tendsto (fun n ↦ (τs n)⁻¹ * (xs n).2) atTop (𝓝 w.2) := by
      have := (continuous_snd.tendsto w).comp hq
      simpa using this
    have h3 : Tendsto (fun n ↦ (xs n).1) atTop (𝓝 0) := by
      have := (continuous_fst.tendsto (0 : ℝ × ℝ)).comp hxto
      simpa using this
    have h4 : Tendsto (fun n ↦ (τs n)⁻¹ * (xs n).2) atTop (𝓝 (w.1 * 0)) := by
      refine (h1.mul h3).congr fun n ↦ ?_
      have hn : (xs n).2 = (xs n).1 ^ 2 := hxC n
      rw [hn]
      ring
    rw [mul_zero] at h4
    exact tendsto_nhds_unique h2 h4
  · intro hw
    have hw2 : w.2 = 0 := hw
    set τs : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hτs_def
    have hτ : ∀ n, 0 < τs n := fun n ↦ by positivity
    refine mem_tangentCone_of_forall (xs := fun n ↦ (τs n * w.1, (τs n * w.1) ^ 2)) (τs := τs)
      (fun n ↦ rfl) hτ tendsto_one_div_add_atTop_nhds_zero_nat ?_
    have hlim : Tendsto (fun n ↦ (w.1, τs n * w.1 ^ 2)) atTop (𝓝 (w.1, (0 : ℝ) * w.1 ^ 2)) :=
      tendsto_const_nhds.prodMk_nhds (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _)
    rw [zero_mul] at hlim
    have hw' : (w.1, (0 : ℝ)) = w := by
      ext
      · rfl
      · exact hw2.symm
    rw [hw'] at hlim
    refine hlim.congr fun n ↦ ?_
    have hne : τs n ≠ 0 := (hτ n).ne'
    simp only [sub_zero, Prod.smul_mk, smul_eq_mul]
    ext
    · field_simp
    · field_simp

/-- The example after Definition 7.23: `df(x̄)(w) = 0` if `w₂ = 0` and `∞`
otherwise. -/
theorem subderivative_indicatorVA_parabola (w : ℝ × ℝ) :
    subderivative (indicatorVA parabola) 0 w = if w.2 = 0 then 0 else ⊤ := by
  rw [subderivative_indicatorVA zero_mem_parabola, tangentCone_parabola_zero]
  by_cases h : w.2 = 0
  · rw [if_pos h, indicatorVA_apply_mem (show w ∈ {w : ℝ × ℝ | w.2 = 0} from h)]
  · rw [if_neg h, indicatorVA_apply_not_mem (show w ∉ {w : ℝ × ℝ | w.2 = 0} from h)]

/-- The example after Definition 7.23: `f'(x̄; w) = 0` if `w = 0` and `∞`
otherwise. -/
theorem hasOneSidedDirDeriv_indicatorVA_parabola (w : ℝ × ℝ) :
    HasOneSidedDirDeriv (indicatorVA parabola) 0 w (if w = 0 then 0 else ⊤) := by
  have hf0 : indicatorVA parabola 0 = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem zero_mem_parabola, EReal.coe_zero]
  refine ⟨by rw [hf0]; exact EReal.coe_ne_bot 0, by rw [hf0]; exact EReal.coe_ne_top 0, ?_⟩
  by_cases hw : w = 0
  · rw [if_pos hw]
    subst hw
    refine tendsto_const_nhds.congr fun τ ↦ ?_
    rw [differenceQuotient_zero_right hf0]
  · rw [if_neg hw]
    refine tendsto_nhds_of_eventually_eq ?_
    have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), (0 : ℝ × ℝ) + τ • w ∉ parabola ∧ 0 < τ := by
      by_cases hw2 : w.2 = 0
      · have hw1 : w.1 ≠ 0 := by
          intro h1
          exact hw (Prod.ext h1 hw2)
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        refine ⟨fun hmem ↦ ?_, hτ⟩
        have hτ' : (0 : ℝ) < τ := hτ
        simp only [parabola, mem_setOf_eq, zero_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          hw2, mul_zero] at hmem
        have : τ * w.1 = 0 := by nlinarith [sq_nonneg (τ * w.1)]
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hτ'.ne'
        · exact hw1 h
      · have hpos : 0 < |w.2| / (w.1 ^ 2 + 1) := by
          have : 0 < |w.2| := abs_pos.2 hw2
          positivity
        filter_upwards [Ioo_mem_nhdsGT hpos] with τ hτ
        refine ⟨fun hmem ↦ ?_, hτ.1⟩
        simp only [parabola, mem_setOf_eq, zero_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul] at hmem
        -- `τ w₂ = τ² w₁²` forces `w₂ = τ w₁²`, too small in absolute value
        have hτpos : 0 < τ := hτ.1
        have h1 : w.2 = τ * w.1 ^ 2 := by
          have : τ * (w.2 - τ * w.1 ^ 2) = 0 := by rw [mul_sub]; nlinarith [hmem]
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hτpos.ne'
          · linarith
        have h2 : |w.2| < |w.2| := by
          calc |w.2| = τ * w.1 ^ 2 := by rw [h1, abs_of_nonneg (by positivity)]
            _ ≤ τ * (w.1 ^ 2 + 1) := by nlinarith
            _ < |w.2| / (w.1 ^ 2 + 1) * (w.1 ^ 2 + 1) :=
                mul_lt_mul_of_pos_right hτ.2 (by positivity)
            _ = |w.2| := by field_simp
        exact lt_irrefl _ h2
    filter_upwards [hev] with τ hτ
    exact differenceQuotient_eq_top hτ.2 hf0 (indicatorVA_apply_not_mem hτ.1)

/-- The example after Definition 7.23: at `w = (1, 0)` the one-sided
directional derivative `∞` differs from `df(x̄)(w) = 0`, so the indicator of
the parabola is not semidifferentiable at the origin for this `w`. -/
theorem parabola_example :
    subderivative (indicatorVA parabola) 0 (1, 0) = 0 ∧
      HasOneSidedDirDeriv (indicatorVA parabola) 0 (1, 0) ⊤ ∧
      ¬SemidifferentiableFor (indicatorVA parabola) 0 (1, 0) := by
  have h1 : subderivative (indicatorVA parabola) 0 (1, 0) = 0 := by
    rw [subderivative_indicatorVA_parabola, if_pos rfl]
  have h2 : HasOneSidedDirDeriv (indicatorVA parabola) 0 (1, 0) ⊤ := by
    have := hasOneSidedDirDeriv_indicatorVA_parabola (1, 0)
    rwa [if_neg (by simp)] at this
  refine ⟨h1, h2, fun ⟨β, hβ⟩ ↦ ?_⟩
  have hβ0 : β = 0 := by rw [← hβ.subderivative_eq, h1]
  have hβtop : β = ⊤ := tendsto_nhds_unique hβ.hasOneSidedDirDeriv.2.2 h2.2.2
  rw [hβ0] at hβtop
  exact EReal.zero_ne_top hβtop

end RW
