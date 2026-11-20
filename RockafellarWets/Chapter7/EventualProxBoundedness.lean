/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eventual prox-boundedness

Definition 7.35 and Exercise 7.36. The inequality for an envelope gives a
common centered quadratic minorant. Conversely an arbitrary quadratic
polynomial is bounded below by a constant minus a multiple of the squared
norm, giving the full quadratic characterization.
-/

import RockafellarWets.Chapter1.Proximal
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Instances.EReal.Lemmas

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- **Definition 7.35**, a uniform eventual lower bound on one Moreau envelope. -/
def IsEventuallyProxBounded (f : ℕ → E → EReal) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∃ x : E, ⊥ < liminf (fun n ↦ moreauEnvelopeEReal (f n) lam x) atTop

/-- **Definition 7.35**, supremum of all admissible positive parameters. -/
noncomputable def eventualProxThreshold (f : ℕ → E → EReal) : EReal :=
  ⨆ (lam : ℝ) (_ : 0 < lam ∧ ∃ x : E,
    ⊥ < liminf (fun n ↦ moreauEnvelopeEReal (f n) lam x) atTop), (lam : EReal)

/-- The epigraph inequality for the Moreau envelope, rewritten as a lower
bound on the underlying function. -/
theorem le_moreauEnvelopeEReal_iff_quadratic_minorant {f : E → EReal} (lam β : ℝ) (b : E) :
    (β : EReal) ≤ moreauEnvelopeEReal f lam b ↔
      ∀ w, ((β - (1 / (2 * lam)) * ‖w - b‖ ^ 2 : ℝ) : EReal) ≤ f w := by
  simp only [moreauEnvelopeEReal, le_iInf_iff, EReal.coe_sub]
  exact forall_congr' fun w ↦ (EReal.sub_le_iff_le_add
    (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).symm

/-- **Exercise 7.36**, with a centered downward quadratic as common minorant. -/
theorem isEventuallyProxBounded_iff_centered_quadratic {f : ℕ → E → EReal} :
    IsEventuallyProxBounded f ↔ ∃ (lam : ℝ) (_ : 0 < lam) (b : E) (β : ℝ),
      ∀ᶠ n in atTop, ∀ w, ((β - (1 / (2 * lam)) * ‖w - b‖ ^ 2 : ℝ) : EReal) ≤ f n w := by
  constructor
  · rintro ⟨lam, hlam, b, hb⟩
    obtain ⟨β, _, hβ⟩ := EReal.exists_between_coe_real hb
    exact ⟨lam, hlam, b, β, (eventually_lt_of_lt_liminf hβ).mono fun n hn ↦
      (le_moreauEnvelopeEReal_iff_quadratic_minorant lam β b).1 hn.le⟩
  · rintro ⟨lam, hlam, b, β, hβ⟩
    exact ⟨lam, hlam, b, (EReal.bot_lt_coe β).trans_le (le_liminf_of_le (by isBoundedDefault)
      (hβ.mono fun n hn ↦ (le_moreauEnvelopeEReal_iff_quadratic_minorant lam β b).2 hn))⟩

/-- **Exercise 7.36**, stated with a general quadratic polynomial, represented
by a bilinear quadratic part, a linear part, and a constant. -/
theorem isEventuallyProxBounded_iff_quadratic [InnerProductSpace ℝ E] {f : ℕ → E → EReal} :
    IsEventuallyProxBounded f ↔
      ∃ (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] ℝ) (c : ℝ),
        ∀ᶠ n in atTop, ∀ w, ((B w w + L w + c : ℝ) : EReal) ≤ f n w := by
  rw [isEventuallyProxBounded_iff_centered_quadratic]
  constructor
  · rintro ⟨lam, _, b, β, hβ⟩
    let k := 1 / (2 * lam)
    refine ⟨(-k) • innerSL ℝ, (2 * k) • innerSL ℝ b, β - k * ‖b‖ ^ 2, ?_⟩
    filter_upwards [hβ] with n hn
    intro w
    apply le_trans _ (hn w)
    apply EReal.coe_le_coe_iff.2
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, norm_sub_sq_real]
    rw [real_inner_comm b w]
    dsimp [k]
    linarith
  · rintro ⟨B, L, c, hq⟩
    let K := ‖B‖ + ‖L‖ + 1
    have hK : 0 < K := by dsimp [K]; positivity
    refine ⟨1 / (2 * K), by positivity, 0, c - ‖L‖, ?_⟩
    filter_upwards [hq] with n hn
    intro w
    apply le_trans _ (hn w)
    apply EReal.coe_le_coe_iff.2
    have hscale : 1 / (2 * (1 / (2 * K))) = K := by field_simp
    rw [hscale, sub_zero]
    have hB : |B w w| ≤ ‖B‖ * ‖w‖ ^ 2 := calc
      |B w w| = ‖B w w‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B w‖ * ‖w‖ := (B w).le_opNorm w
      _ ≤ (‖B‖ * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right (B.le_opNorm w) (norm_nonneg _)
      _ = _ := by ring
    have hL : |L w| ≤ ‖L‖ * ‖w‖ := L.le_opNorm w
    have hnorm : 0 ≤ 1 + ‖w‖ ^ 2 - ‖w‖ := by nlinarith [sq_nonneg (‖w‖ - 1/2)]
    dsimp [K]
    nlinarith [(abs_le.1 hB).1, (abs_le.1 hL).1, mul_nonneg (norm_nonneg L) hnorm,
      sq_nonneg ‖w‖]

end RW
