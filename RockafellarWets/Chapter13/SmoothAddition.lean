/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Addition of a twice smooth function

Exercise 13.18.  The smooth summand `f₀` enters through the data of classical
twice differentiability at `x̄` (13.1(a)): a derivative `f₀'` near `x̄`, its
derivative `f₀''` at `x̄`, and the gradient `v₀ = ∇f₀(x̄)`; the quadratic
form `⟪w, ∇²f₀(x̄)w⟫` is `f₀''(w)(w)`.  The headline statements specialize to
`f₀` of class `C²`.  The formulas for the second subderivatives hold without
any epi-differentiability assumption.
-/

import RockafellarWets.Chapter13.SecondOrderExpansions
import RockafellarWets.Chapter10.SubderivativeSmoothAddition
import RockafellarWets.Chapter7.SemidifferentiabilityCharacterizations
import Mathlib.Analysis.Calculus.Gradient.Basic

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inf-addition with a real second summand is ordinary addition. -/
theorem infAddition_coe_right (a : EReal) (b : ℝ) : infAddition a b = a + b := by
  unfold infAddition
  split_ifs with h
  · rcases h with h | h
    · rw [h, EReal.top_add_coe]
    · exact absurd h (EReal.coe_ne_top b)
  · rfl

section Data

variable {f : E → EReal} {x v : E} {c : ℝ} {f₀ : E → ℝ} {f₀' : E → E →L[ℝ] ℝ}
  {f₀'' : E →L[ℝ] E →L[ℝ] ℝ} {v₀ : E}

/-- The real second-order quotient of the smooth summand. -/
noncomputable def smoothSecondQuotient (f₀ : E → ℝ) (x v₀ : E) (τ : ℝ) (w : E) : ℝ :=
  2 / τ ^ 2 * (f₀ (x + τ • w) - f₀ x - τ * ⟪v₀, w⟫_ℝ)

/-- The quotients 13(5) add over a smooth summand. -/
theorem secondDifferenceQuotient_add_smooth (hx : f x = c) {τ : ℝ} (hτ : τ ≠ 0) (w : E) :
    secondDifferenceQuotient (fun y ↦ f y + (f₀ y : EReal)) x (v + v₀) τ w =
      secondDifferenceQuotient f x v τ w + (smoothSecondQuotient f₀ x v₀ τ w : EReal) := by
  set F : E → EReal := fun y ↦ f y + (f₀ y : EReal) with hF
  have hxF : F x = ((c + f₀ x : ℝ) : EReal) := by
    change f x + (f₀ x : EReal) = _
    rw [hx, EReal.coe_add]
  rcases ereal_trichotomy (f (x + τ • w)) with h | h | ⟨r, h⟩
  · rw [secondDifferenceQuotient_of_bot hτ hx h, EReal.bot_add,
      secondDifferenceQuotient_of_bot (f := F) hτ hxF
        (show f (x + τ • w) + (f₀ (x + τ • w) : EReal) = ⊥ by rw [h, EReal.bot_add])]
  · rw [secondDifferenceQuotient_of_top hτ hx h, EReal.top_add_coe,
      secondDifferenceQuotient_of_top (f := F) hτ hxF
        (show f (x + τ • w) + (f₀ (x + τ • w) : EReal) = ⊤ by rw [h, EReal.top_add_coe])]
  · rw [secondDifferenceQuotient_of_coe hx h,
      secondDifferenceQuotient_of_coe (f := F) hxF (r := r + f₀ (x + τ • w))
        (show f (x + τ • w) + (f₀ (x + τ • w) : EReal) = _ by rw [h, EReal.coe_add]),
      ← EReal.coe_add, smoothSecondQuotient, inner_add_left]
    congr 1
    ring

variable (hf₀ : ∀ᶠ y in 𝓝 x, HasFDerivAt f₀ (f₀' y) y) (hf₀' : HasFDerivAt f₀' f₀'' x)
  (hv₀ : ∀ w, f₀' x w = ⟪v₀, w⟫_ℝ)
include hf₀ hf₀' hv₀

/-- **Exercise 13.18**, the formula `d²(f + f₀)(x̄ | v + v₀)(w) = d²f(x̄ | v)(w) + ⟪w, ∇²f₀(x̄)w⟫`,
valid at every point where `f` is finite. -/
theorem secondSubderivative_add_smooth (hx : f x = c) (w : E) :
    secondSubderivative (fun y ↦ f y + (f₀ y : EReal)) x (v + v₀) w =
      secondSubderivative f x v w + ((f₀'' w w : ℝ) : EReal) := by
  have hQ : Tendsto (fun p : ℝ × E ↦ (smoothSecondQuotient f₀ x v₀ p.1 p.2 : EReal))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((f₀'' w w : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 (tendsto_secondDifferenceQuotient_of_hasFDerivAt hf₀ hf₀' hv₀ w)
  have heq : (fun p : ℝ × E ↦ secondDifferenceQuotient (fun y ↦ f y + (f₀ y : EReal)) x (v + v₀)
      p.1 p.2) =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 w] fun p ↦ secondDifferenceQuotient f x v p.1 p.2 +
        (smoothSecondQuotient f₀ x v₀ p.1 p.2 : EReal) := by
    filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
    exact secondDifferenceQuotient_add_smooth hx (ne_of_gt hp) p.2
  rw [secondSubderivative, liminf_congr heq, liminf_add_of_tendsto_coe hQ]
  rfl

/-- **Exercise 13.18**: twice epi-differentiability is preserved under adding `f₀`. -/
theorem TwiceEpiDifferentiableAt.add_smooth (hf : TwiceEpiDifferentiableAt f x v) :
    TwiceEpiDifferentiableAt (fun y ↦ f y + (f₀ y : EReal)) x (v + v₀) := by
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hf.2.1 hf.1).symm
  rw [twiceEpiDifferentiableAt_iff_subset] at hf ⊢
  obtain ⟨-, -, hsub⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [hxc, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  · rw [hxc, ← EReal.coe_add]
    exact EReal.coe_ne_top _
  have hfun : secondSubderivative (fun y ↦ f y + (f₀ y : EReal)) x (v + v₀) =
      fun w ↦ secondSubderivative f x v w + ((f₀'' w w : ℝ) : EReal) :=
    funext fun w ↦ secondSubderivative_add_smooth hf₀ hf₀' hv₀ hxc w
  have hcongr : (fun τ ↦ epigraph (fun w ↦ secondDifferenceQuotient f x v τ w +
      (smoothSecondQuotient f₀ x v₀ τ w : EReal))) =ᶠ[𝓝[>] (0 : ℝ)]
      fun τ ↦ epigraph (secondDifferenceQuotient (fun y ↦ f y + (f₀ y : EReal)) x (v + v₀) τ) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    congr 1
    funext w
    exact (secondDifferenceQuotient_add_smooth hxc (ne_of_gt hτ) w).symm
  rw [hfun, ← innerSetLimitAlong_congr hcongr]
  exact epigraph_add_subset_innerSetLimitAlong hsub fun w ↦
    tendsto_secondDifferenceQuotient_of_hasFDerivAt hf₀ hf₀' hv₀ w

/-- **Exercise 13.18**: proper twice epi-differentiability is preserved under adding `f₀`. -/
theorem ProperlyTwiceEpiDifferentiableAt.add_smooth (hf : ProperlyTwiceEpiDifferentiableAt f x v) :
    ProperlyTwiceEpiDifferentiableAt (fun y ↦ f y + (f₀ y : EReal)) x (v + v₀) := by
  obtain ⟨he, hp⟩ := hf
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal he.2.1 he.1).symm
  refine ⟨he.add_smooth hf₀ hf₀' hv₀, ?_, fun w ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hp.1
    refine ⟨w, ?_⟩
    rw [secondSubderivative_add_smooth hf₀ hf₀' hv₀ hxc]
    exact EReal.add_lt_top hw.ne (EReal.coe_ne_top _)
  · rw [secondSubderivative_add_smooth hf₀ hf₀' hv₀ hxc]
    have hw := hp.2 w
    rcases ereal_trichotomy (secondSubderivative f x v w) with h | h | ⟨r, h⟩
    · rw [h] at hw
      exact absurd hw (lt_irrefl _)
    · rw [h, EReal.top_add_coe]
      exact bot_lt_top
    · rw [h, ← EReal.coe_add]
      exact EReal.bot_lt_coe _

omit hf₀' in
/-- The quotients 13(4) add over a smooth summand when `df(x̄)(w)` is finite. -/
theorem secondDifferenceQuotientAt_add_smooth (hx : f x = c) {τ : ℝ} (hτ : 0 < τ) {w : E} {d : ℝ}
    (hd : subderivative f x w = d) :
    secondDifferenceQuotientAt (fun y ↦ f y + (f₀ y : EReal)) x τ w =
      secondDifferenceQuotientAt f x τ w + (smoothSecondQuotient f₀ x v₀ τ w : EReal) := by
  have hdF : subderivative (fun y ↦ f y + (f₀ y : EReal)) x w =
      ((d + ⟪v₀, w⟫_ℝ : ℝ) : EReal) := by
    rw [subderivative_add_differentiable hx (hf₀.self_of_nhds), hd, hv₀, EReal.coe_add]
  have h2 : (0 : ℝ) < 2 / τ ^ 2 := by positivity
  rw [secondDifferenceQuotientAt, secondDifferenceQuotientAt, hdF, hd, ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_neg, infAddition_coe_right,
    infAddition_coe_right, hx]
  rcases ereal_trichotomy (f (x + τ • w)) with h | h | ⟨r, h⟩
  · rw [h, EReal.bot_add, EReal.bot_sub, EReal.bot_add, EReal.coe_mul_bot_of_pos h2,
      EReal.bot_sub, EReal.bot_add, EReal.coe_mul_bot_of_pos h2, EReal.bot_add]
  · rw [h, EReal.top_add_coe, ← EReal.coe_add, EReal.top_sub_coe, EReal.top_add_coe,
      EReal.coe_mul_top_of_pos h2, EReal.top_sub_coe, EReal.top_add_coe,
      EReal.coe_mul_top_of_pos h2, EReal.top_add_coe]
  · rw [h]
    simp only [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_eq_coe_iff,
      smoothSecondQuotient]
    ring

/-- **Exercise 13.18**, the twice semidifferentiable case: `f + f₀` is twice
semidifferentiable with `d²(f + f₀)(x̄)(w) = d²f(x̄)(w) + ⟪w, ∇²f₀(x̄)w⟫`. -/
theorem TwiceSemidifferentiableAt.add_smooth (hf : TwiceSemidifferentiableAt f x) :
    TwiceSemidifferentiableAt (fun y ↦ f y + (f₀ y : EReal)) x ∧ ∀ w,
      secondSubderivativeAt (fun y ↦ f y + (f₀ y : EReal)) x w =
        secondSubderivativeAt f x w + ((f₀'' w w : ℝ) : EReal) := by
  obtain ⟨hs, hconv⟩ := hf
  obtain ⟨g, -, -, hall⟩ := hs.exists_semiderivative
  have hx1 : f x ≠ ⊥ := (hall 0).1.1
  have hx2 : f x ≠ ⊤ := (hall 0).1.2.1
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx2 hx1).symm
  have hxF : f x + (f₀ x : EReal) = (((f x).toReal + f₀ x : ℝ) : EReal) := by
    rw [hxc, EReal.coe_add, EReal.toReal_coe]
  have hsF : SemidifferentiableAt (fun y ↦ f y + (f₀ y : EReal)) x := by
    intro w
    refine ⟨((g w + f₀' x w : ℝ) : EReal),
      show f x + (f₀ x : EReal) ≠ ⊥ by rw [hxF]; exact EReal.coe_ne_bot _,
      show f x + (f₀ x : EReal) ≠ ⊤ by rw [hxF]; exact EReal.coe_ne_top _, ?_⟩
    have h1 : Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
        (𝓝 (g w : EReal)) := (hall w).1.2.2
    have h2 : Tendsto (fun p : ℝ × E ↦ differenceQuotient (fun y ↦ (f₀ y : EReal)) x p.1 p.2)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (f₀' x w : EReal)) :=
      (hasDirectionalSemiderivative_iff.mp
        ((hf₀.self_of_nhds).hasDirectionalSemiderivative w)).2.2
    have hsum := ((EReal.continuousAt_add (p := ((g w : EReal), (f₀' x w : EReal)))
      (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))).tendsto).comp
      (h1.prodMk_nhds h2)
    rw [EReal.coe_add]
    refine hsum.congr' ?_
    filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
    exact (differenceQuotient_add_real hxc hp p.2).symm
  have hlim : ∀ w, Tendsto (fun p : ℝ × E ↦
      secondDifferenceQuotientAt (fun y ↦ f y + (f₀ y : EReal)) x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (secondSubderivativeAt f x w + ((f₀'' w w : ℝ) : EReal))) := by
    intro w
    have hQ : Tendsto (fun p : ℝ × E ↦ (smoothSecondQuotient f₀ x v₀ p.1 p.2 : EReal))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((f₀'' w w : ℝ) : EReal)) :=
      EReal.tendsto_coe.2 (tendsto_secondDifferenceQuotient_of_hasFDerivAt hf₀ hf₀' hv₀ w)
    have hsum := ((EReal.continuousAt_add
      (p := (secondSubderivativeAt f x w, ((f₀'' w w : ℝ) : EReal)))
      (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto).comp
      ((hconv w).prodMk_nhds hQ)
    refine hsum.congr' ?_
    filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
    exact (secondDifferenceQuotientAt_add_smooth hf₀ hv₀ hxc hp (hall p.2).2.1).symm
  have heq : ∀ w, secondSubderivativeAt (fun y ↦ f y + (f₀ y : EReal)) x w =
      secondSubderivativeAt f x w + ((f₀'' w w : ℝ) : EReal) := fun w ↦ (hlim w).liminf_eq
  exact ⟨⟨hsF, fun w ↦ by rw [heq w]; exact hlim w⟩, heq⟩

end Data

/-! ### The `C²` specialization -/

section ContDiffTwo

variable {f : E → EReal} {x v : E} {f₀ : E → ℝ}

theorem hasFDerivAt_fderiv_of_contDiff_two (h₀ : ContDiff ℝ 2 f₀) (y : E) :
    HasFDerivAt f₀ (fderiv ℝ f₀ y) y :=
  (h₀.differentiable (by norm_num) y).hasFDerivAt

theorem hasFDerivAt_fderiv_fderiv_of_contDiff_two (h₀ : ContDiff ℝ 2 f₀) (x : E) :
    HasFDerivAt (fderiv ℝ f₀) (fderiv ℝ (fderiv ℝ f₀) x) x :=
  ((h₀.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt

variable [CompleteSpace E]

theorem fderiv_apply_eq_inner_gradient (f₀ : E → ℝ) (x w : E) :
    fderiv ℝ f₀ x w = ⟪gradient f₀ x, w⟫_ℝ := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

/-- **Exercise 13.18**: if `f` is properly twice epi-differentiable at `x̄` for `v` and `f₀`
is `C²`, then `f + f₀` is properly twice epi-differentiable at `x̄` for `v + ∇f₀(x̄)`, with
`d²(f + f₀)(x̄ | v + ∇f₀(x̄))(w) = d²f(x̄ | v)(w) + ⟪w, ∇²f₀(x̄)w⟫`.  Likewise twice
semidifferentiability is preserved, with the same correction term for `d²f(x̄)`. -/
theorem addition_of_twice_smooth (h₀ : ContDiff ℝ 2 f₀) :
    (ProperlyTwiceEpiDifferentiableAt f x v →
      ProperlyTwiceEpiDifferentiableAt (fun y ↦ f y + (f₀ y : EReal)) x (v + gradient f₀ x) ∧
      ∀ w, secondSubderivative (fun y ↦ f y + (f₀ y : EReal)) x (v + gradient f₀ x) w =
        secondSubderivative f x v w + ((fderiv ℝ (fderiv ℝ f₀) x w w : ℝ) : EReal)) ∧
    (TwiceSemidifferentiableAt f x →
      TwiceSemidifferentiableAt (fun y ↦ f y + (f₀ y : EReal)) x ∧
      ∀ w, secondSubderivativeAt (fun y ↦ f y + (f₀ y : EReal)) x w =
        secondSubderivativeAt f x w + ((fderiv ℝ (fderiv ℝ f₀) x w w : ℝ) : EReal)) := by
  have hf₀ : ∀ᶠ y in 𝓝 x, HasFDerivAt f₀ (fderiv ℝ f₀ y) y :=
    Eventually.of_forall (hasFDerivAt_fderiv_of_contDiff_two h₀)
  have hf₀' := hasFDerivAt_fderiv_fderiv_of_contDiff_two h₀ x
  have hv₀ := fderiv_apply_eq_inner_gradient f₀ x
  refine ⟨fun hf ↦ ⟨hf.add_smooth hf₀ hf₀' hv₀, fun w ↦ ?_⟩,
    fun hf ↦ hf.add_smooth hf₀ hf₀' hv₀⟩
  have hxc : f x = (((f x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hf.1.2.1 hf.1.1).symm
  exact secondSubderivative_add_smooth hf₀ hf₀' hv₀ hxc w

end ContDiffTwo

end RW
