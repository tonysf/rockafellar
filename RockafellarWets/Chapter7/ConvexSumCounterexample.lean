/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Opposite infinities in the convex sum rule
-/

import RockafellarWets.Chapter7.ConvexSums
import RockafellarWets.Chapter7.InfAdditionLimits

open Filter Set Topology
open scoped Pointwise

namespace RW

/-- **Obstruction to the unrestricted convergence claim in Exercise 7.47.**
The hinges `n max(x,0)` epi-converge to the indicator of the negative
half-line, and the constants `-n` tend to minus infinity. Their sum vanishes
at 1 for every index, although the pointwise inf-sum of the limits is plus
infinity there. The approximating functions are finite, convex and continuous,
and the effective domains of the two limits satisfy the required qualification. -/
theorem infAddition_convex_epiConvergence_counterexample :
    ∃ (f h : ℕ → ℝ → ℝ) (G H : ℝ → EReal),
      (∀ n, ConvexOn ℝ univ (f n) ∧ Continuous (f n) ∧
        ConvexOn ℝ univ (h n) ∧ Continuous (h n)) ∧
      EpiConverges (fun n x ↦ (f n x : EReal)) G ∧
      EpiConverges (fun n x ↦ (h n x : EReal)) H ∧
      CannotBeSeparated (effectiveDomain G) (effectiveDomain H) ∧
      ¬ EpiConverges (fun n x ↦ infAddition (f n x) (h n x))
        (fun x ↦ infAddition (G x) (H x)) := by
  let f (n : ℕ) (x : ℝ) := (n : ℝ) * max x 0
  let h (n : ℕ) (_ : ℝ) := -(n : ℝ)
  let G := indicatorVA (Iic (0 : ℝ))
  let H := fun _ : ℝ ↦ (⊥ : EReal)
  have hcont (n : ℕ) : Continuous (f n) :=
    continuous_const.mul (continuous_id.max continuous_const)
  have hmono : Monotone (fun n x ↦ (f n x : EReal)) := by
    intro i j hij x
    exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (le_max_right _ _))
  have clim (n : ℕ) : epiClosure (fun x ↦ (f n x : EReal)) = fun x ↦ (f n x : EReal) :=
    epiClosure_eq_of_lowerSemicontinuous (continuous_coe_real_ereal.comp (hcont n)).lowerSemicontinuous
  have hlim (x : ℝ) : Tendsto (fun n ↦ (f n x : EReal)) atTop (𝓝 (G x)) := by
    by_cases hx : x ≤ 0
    · simp [f, G, hx]
    · have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) * x) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (lt_of_not_ge hx)
      simpa [f, G, indicatorVA, hx, max_eq_left (le_of_not_ge hx), Function.comp_def] using
        EReal.tendsto_coe_atTop.comp ht
  have hG : EpiConverges (fun n x ↦ (f n x : EReal)) G := by
    have he := epiConverges_of_monotone hmono
    have hsup : (fun x ↦ ⨆ n, epiClosure (fun x ↦ (f n x : EReal)) x) = G := by
      funext x
      simp only [clim]
      exact tendsto_nhds_unique (tendsto_atTop_iSup (fun i j hij ↦ hmono hij x)) (hlim x)
    rwa [← hsup]
  have hH : EpiConverges (fun n x ↦ (h n x : EReal)) H := by
    apply epiConverges_const_values (v := fun n : ℕ ↦ ((-(n : ℝ) : ℝ) : EReal)) (a := ⊥)
    simpa [h, H, Function.comp_def] using
      (EReal.tendsto_coe_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).neg
  have hd : effectiveDomain G - effectiveDomain H = univ := by
    apply eq_univ_of_forall
    intro x
    exact ⟨0, by simp [G, effectiveDomain, indicatorVA], -x,
      by simp [H, effectiveDomain], by simp⟩
  refine ⟨f, h, G, H, ?_, hG, hH, by simp [CannotBeSeparated, hd], ?_⟩
  · intro n
    have hc := (convexOn_id (convex_univ : Convex ℝ (univ : Set ℝ))).sup (convexOn_const 0 convex_univ)
    exact ⟨hc.smul (Nat.cast_nonneg n), hcont n, convexOn_const _ convex_univ, continuous_const⟩
  · intro hc
    have hlow := (epiConverges_iff_liminf_limsup.mp hc 1).1 (fun _ ↦ 1) tendsto_const_nhds
    have hvan (n : ℕ) : infAddition (f n 1) (h n 1) = 0 := by
      rw [infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _), ← EReal.coe_add]
      simp [f, h]
    change infAddition (G 1) (H 1) ≤ liminf (fun n ↦ infAddition (f n 1) (h n 1)) atTop at hlow
    simp only [hvan, liminf_const] at hlow
    simp [G, H, infAddition] at hlow

end RW
