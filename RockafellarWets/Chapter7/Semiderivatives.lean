/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Semiderivatives

Section 7D opens with the difference-quotient functions of formula 7(15), the
semiderivatives of Definition 7.20, the one-sided directional derivatives of
formula 7(20) and the lower limit `df(x̄)(w)` of formula 7(21).

All of these limits are taken along the joint filter "`τ ↓ 0` and `w' → w`",
that is `𝓝[>] 0 ×ˢ 𝓝 w` on `ℝ × E`.  Division by `τ` is multiplication by
the real number `τ⁻¹`, so the quotients live in `EReal` even when
`f(x̄ + τw) = ±∞`.  The book always assumes `f(x̄)` finite; the two limit
predicates below carry that assumption explicitly.

The paragraph after Definition 7.20 is formalized in full:
* `hasSemiderivative_iff_seq` is its sequential reading ("whenever `xν`
  converges to `x̄` from the direction of `w` ...");
* `HasSemiderivative.hasOneSidedDirDeriv` is the remark that a semiderivative
  is also a one-sided directional derivative;
* `HasSemiderivative.subderivative_eq` and
  `semidifferentiableFor_iff_subderivative_eq_limsup` are the remarks on
  formula 7(21).
The converse of the second remark fails; the parabola example after 7.23 is
formalized in `EpiDerivatives.lean`.
-/

import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Module.Basic

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Formula 7(15): difference quotients -/

/-- Formula 7(15): the difference quotient `Δ_τ f(x̄)(w) = [f(x̄ + τw) - f(x̄)]/τ`,
division by `τ` being multiplication by the real number `τ⁻¹`. -/
noncomputable def differenceQuotient (f : E → EReal) (x : E) (τ : ℝ) (w : E) : EReal :=
  ((τ⁻¹ : ℝ) : EReal) * (f (x + τ • w) - f x)

/-- In real arithmetic: the difference quotient between two finite values. -/
theorem differenceQuotient_eq_coe {f : E → EReal} {x w : E} {τ c r : ℝ}
    (hx : f x = c) (hy : f (x + τ • w) = r) :
    differenceQuotient f x τ w = ((τ⁻¹ * (r - c) : ℝ) : EReal) := by
  rw [differenceQuotient, hx, hy, ← EReal.coe_sub, ← EReal.coe_mul]

/-- A difference quotient at a positive scale is `∞` exactly where the value
of `f` is `∞`. -/
theorem differenceQuotient_eq_top {f : E → EReal} {x w : E} {τ c : ℝ} (hτ : 0 < τ)
    (hx : f x = c) (hy : f (x + τ • w) = ⊤) :
    differenceQuotient f x τ w = ⊤ := by
  rw [differenceQuotient, hx, hy, EReal.top_sub_coe, EReal.coe_mul_top_of_pos (inv_pos.2 hτ)]

/-- A difference quotient at a positive scale is `-∞` exactly where the value
of `f` is `-∞`. -/
theorem differenceQuotient_eq_bot {f : E → EReal} {x w : E} {τ c : ℝ} (hτ : 0 < τ)
    (hx : f x = c) (hy : f (x + τ • w) = ⊥) :
    differenceQuotient f x τ w = ⊥ := by
  rw [differenceQuotient, hx, hy, EReal.bot_sub, EReal.coe_mul_bot_of_pos (inv_pos.2 hτ)]

/-- The difference quotient vanishes in the direction `0`. -/
theorem differenceQuotient_zero_right {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    (τ : ℝ) : differenceQuotient f x τ 0 = 0 := by
  rw [differenceQuotient_eq_coe (r := c) hx (by rw [smul_zero, add_zero, hx])]
  simp

/-- Rescaling the direction: `Δ_τ f(x̄)(cw) = c Δ_{cτ} f(x̄)(w)`. -/
theorem differenceQuotient_smul_right (f : E → EReal) (x w : E) (τ : ℝ) {c : ℝ}
    (hc : c ≠ 0) :
    differenceQuotient f x τ (c • w) =
      (c : EReal) * differenceQuotient f x (c * τ) w := by
  have hinv : ((τ⁻¹ : ℝ) : EReal) = (c : EReal) * (((c * τ)⁻¹ : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    rcases eq_or_ne τ 0 with rfl | hτ
    · simp
    · field_simp
  rw [differenceQuotient, differenceQuotient, smul_smul, mul_comm τ c, hinv, mul_assoc]

/-! ### Definition 7.20: semiderivatives -/

/-- **Definition 7.20**, formula 7(19): `β` is the (possibly infinite)
semiderivative of `f` at `x̄` for `w`.  The book's standing assumption that
`f(x̄)` is finite is part of the predicate. -/
def HasSemiderivative (f : E → EReal) (x w : E) (β : EReal) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧
    Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 β)

/-- **Definition 7.20**: `f` is semidifferentiable at `x̄` for `w`. -/
def SemidifferentiableFor (f : E → EReal) (x w : E) : Prop :=
  ∃ β, HasSemiderivative f x w β

/-- **Definition 7.20**: `f` is semidifferentiable at `x̄` when it is
semidifferentiable at `x̄` for every `w`. -/
def SemidifferentiableAt (f : E → EReal) (x : E) : Prop :=
  ∀ w, SemidifferentiableFor f x w

/-- Formula 7(20): `β` is the one-sided directional derivative `f'(x̄; w)`. -/
def HasOneSidedDirDeriv (f : E → EReal) (x w : E) (β : EReal) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧
    Tendsto (fun τ : ℝ ↦ differenceQuotient f x τ w) (𝓝[>] (0 : ℝ)) (𝓝 β)

/-- Formula 7(21): the lower limit `df(x̄)(w)` of the difference quotients,
which exists always. -/
noncomputable def subderivative (f : E → EReal) (x w : E) : EReal :=
  liminf (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)

/-- The upper counterpart of formula 7(21). -/
noncomputable def upperSemiderivative (f : E → EReal) (x w : E) : EReal :=
  limsup (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)

omit [NormedSpace ℝ E] in
/-- The path `τ ↦ (τ, w)` approaches the joint filter of 7(19). -/
theorem tendsto_pair_const (w : E) :
    Tendsto (fun τ : ℝ ↦ (τ, w)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
  tendsto_id.prodMk tendsto_const_nhds

/-- A semiderivative is unique. -/
theorem HasSemiderivative.unique {f : E → EReal} {x w : E} {β γ : EReal}
    (hβ : HasSemiderivative f x w β) (hγ : HasSemiderivative f x w γ) : β = γ :=
  tendsto_nhds_unique hβ.2.2 hγ.2.2

/-- The paragraph after Definition 7.20: a semiderivative is also the
one-sided directional derivative 7(20). -/
theorem HasSemiderivative.hasOneSidedDirDeriv {f : E → EReal} {x w : E} {β : EReal}
    (h : HasSemiderivative f x w β) : HasOneSidedDirDeriv f x w β :=
  ⟨h.1, h.2.1, h.2.2.comp (tendsto_pair_const w)⟩

/-- Formula 7(21): a semiderivative, when it exists, equals `df(x̄)(w)`. -/
theorem HasSemiderivative.subderivative_eq {f : E → EReal} {x w : E} {β : EReal}
    (h : HasSemiderivative f x w β) : subderivative f x w = β :=
  h.2.2.liminf_eq

/-- Formula 7(21): a semiderivative, when it exists, equals the upper limit. -/
theorem HasSemiderivative.upperSemiderivative_eq {f : E → EReal} {x w : E} {β : EReal}
    (h : HasSemiderivative f x w β) : upperSemiderivative f x w = β :=
  h.2.2.limsup_eq

/-- The lower limit 7(21) never exceeds the upper one. -/
theorem subderivative_le_upperSemiderivative (f : E → EReal) (x w : E) :
    subderivative f x w ≤ upperSemiderivative f x w :=
  liminf_le_limsup

/-- The paragraph after formula 7(21): semidifferentiability for `w` is the
case where the value `df(x̄)(w)` is a full limit, i.e. where the lower and
upper limits of the difference quotients agree. -/
theorem semidifferentiableFor_iff_subderivative_eq_limsup {f : E → EReal} {x w : E}
    (hx : f x ≠ ⊥) (hx' : f x ≠ ⊤) :
    SemidifferentiableFor f x w ↔ subderivative f x w = upperSemiderivative f x w := by
  constructor
  · rintro ⟨β, hβ⟩
    rw [hβ.subderivative_eq, hβ.upperSemiderivative_eq]
  · intro h
    exact ⟨subderivative f x w, hx, hx', tendsto_of_liminf_eq_limsup rfl h.symm⟩

/-- When `f` is semidifferentiable for `w`, its semiderivative is `df(x̄)(w)`. -/
theorem SemidifferentiableFor.hasSemiderivative {f : E → EReal} {x w : E}
    (h : SemidifferentiableFor f x w) : HasSemiderivative f x w (subderivative f x w) := by
  obtain ⟨β, hβ⟩ := h
  rwa [hβ.subderivative_eq]

/-- The paragraph after Definition 7.20, sequential form: the semiderivative
limit exists and equals `β` exactly when `[f(xν) - f(x̄)]/τν → β` whenever
`τν ↓ 0` and `[xν - x̄]/τν → w`. -/
theorem hasSemiderivative_iff_seq {f : E → EReal} {x w : E} {β : EReal}
    (hx : f x ≠ ⊥) (hx' : f x ≠ ⊤) :
    HasSemiderivative f x w β ↔
      ∀ (xs : ℕ → E) (τs : ℕ → ℝ), (∀ n, 0 < τs n) → Tendsto τs atTop (𝓝 0) →
        Tendsto (fun n ↦ (τs n)⁻¹ • (xs n - x)) atTop (𝓝 w) →
        Tendsto (fun n ↦ (((τs n)⁻¹ : ℝ) : EReal) * (f (xs n) - f x)) atTop (𝓝 β) := by
  constructor
  · intro h xs τs hτ hτ0 hq
    have hp : Tendsto (fun n ↦ (τs n, (τs n)⁻¹ • (xs n - x))) atTop
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0
        (Eventually.of_forall hτ)).prodMk hq
    refine (h.2.2.comp hp).congr fun n ↦ ?_
    have hxs : x + τs n • (τs n)⁻¹ • (xs n - x) = xs n := by
      rw [smul_smul, mul_inv_cancel₀ (hτ n).ne', one_smul, add_sub_cancel]
    simp only [Function.comp, differenceQuotient, hxs]
  · intro h
    refine ⟨hx, hx', tendsto_iff_seq_tendsto.2 fun p hp ↦ ?_⟩
    have hpos : ∀ᶠ n in atTop, 0 < (p n).1 :=
      ((tendsto_fst.comp hp) : Tendsto (fun n ↦ (p n).1) atTop (𝓝[>] (0 : ℝ)))
        self_mem_nhdsWithin
    obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
    have hp' : Tendsto (fun n ↦ p (n + N)) atTop (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
      hp.comp (tendsto_add_atTop_nat N)
    have hτ : ∀ n, 0 < (p (n + N)).1 := fun n ↦ hN _ (Nat.le_add_left N n)
    have hτ0 : Tendsto (fun n ↦ (p (n + N)).1) atTop (𝓝 0) :=
      (tendsto_fst.comp hp').mono_right nhdsWithin_le_nhds
    have hq : Tendsto (fun n ↦ ((p (n + N)).1)⁻¹ • ((x + (p (n + N)).1 • (p (n + N)).2) - x))
        atTop (𝓝 w) := by
      refine (tendsto_snd.comp hp').congr fun n ↦ ?_
      simp only [Function.comp, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ (hτ n).ne', one_smul]
    have := h (fun n ↦ x + (p (n + N)).1 • (p (n + N)).2) (fun n ↦ (p (n + N)).1) hτ hτ0 hq
    exact (tendsto_add_atTop_iff_nat N).1 this

/-- Positive homogeneity of semiderivatives in the direction. -/
theorem HasSemiderivative.smul {f : E → EReal} {x w : E} {β : EReal}
    (h : HasSemiderivative f x w β) {c : ℝ} (hc : 0 < c) :
    HasSemiderivative f x (c • w) ((c : EReal) * β) := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hm : Tendsto (fun p : ℝ × E ↦ (c * p.1, c⁻¹ • p.2))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (c • w)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := by
    refine Tendsto.prodMk ?_ ?_
    · have h1 : Tendsto (fun τ : ℝ ↦ c * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · exact ((continuous_mul_left c).tendsto' 0 0 (mul_zero c)).mono_left
            nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with τ hτ
          exact mul_pos hc hτ
      exact h1.comp tendsto_fst
    · have h2 : Tendsto (fun u : E ↦ c⁻¹ • u) (𝓝 (c • w)) (𝓝 w) := by
        have := ((continuous_const_smul c⁻¹).tendsto (c • w))
        rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
      exact h2.comp tendsto_snd
  have hmul : Tendsto (fun a : EReal ↦ (c : EReal) * a) (𝓝 β) (𝓝 ((c : EReal) * β)) := by
    have hcont := EReal.continuousAt_mul (p := ((c : EReal), β))
      (Or.inl (EReal.coe_ne_zero.2 hc.ne')) (Or.inl (EReal.coe_ne_zero.2 hc.ne'))
        (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))
    exact hcont.tendsto.comp (tendsto_const_nhds.prodMk_nhds tendsto_id)
  refine (hmul.comp (h.2.2.comp hm)).congr fun p ↦ ?_
  simp only [Function.comp]
  rw [← differenceQuotient_smul_right f x (c⁻¹ • p.2) p.1 hc.ne', smul_smul,
    mul_inv_cancel₀ hc.ne', one_smul]

end RW
