/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Prox-regularity of second subderivatives

Proposition 13.49.  In the proof of Theorem 13.40 (`ProxCore`), twice epi-differentiability gives
`½d²f(x̄ | 0) + μ/2‖·‖² = Φ̃`, a supremum of affine functions, whose subgradient mapping
`DT(x̄ | 0) + μI` is maximal monotone (Minty).  Thus `d²f(x̄ | v̄) + ρ‖·‖²` is convex for `ρ = μ`,
`DT(x̄ | v̄) + ρI` is maximal monotone, and `d²f(x̄ | v̄)` is prox-regular everywhere (13.30,
13.35).

**Correction.**  The printed statement asserts that `D(∂f)(x̄ | v̄) + ρI` is maximal monotone for
`f` prox-regular and properly twice epi-differentiable at `x̄` for `v̄`.  Without subdifferential
continuity this fails: for `f = 0` on `(-∞, 0]` and `f = 1` on `(0, ∞)` at `x̄ = v̄ = 0`, `f` is
prox-regular and properly twice epi-differentiable (`d²f(0 | 0) = δ_{(-∞, 0]}`), but
`gph D(∂f)(0 | 0) = (ℝ × {0}) ∪ ({0} × [0, ∞))`, so `D(∂f)(0 | 0) + ρI` is not monotone for any `ρ`
(`SecondSubderivativeConvexityCounterexample.printed_1349_counterexample`, which also shows that
the step function is not subdifferentially continuous at `0` for `0`).
As in the proof of the book, the conclusion holds for the derivatives `DT(x̄ | v̄)` of sufficiently
close `f`-attentive localizations `T` of `∂f`, and for `D(∂f)(x̄ | v̄)` itself under subdifferential
continuity (in particular in the fully amenable case).
-/

import RockafellarWets.Chapter13.SubgradientProtoDifferentiability
import RockafellarWets.Chapter13.AmenableProtoDifferentiability

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem ereal_two_mul_le_coe_iff {a : EReal} (ha : a ≠ ⊥) (b : ℝ) :
    ((2 : ℝ) : EReal) * a ≤ (b : EReal) ↔ a ≤ ((b / 2 : ℝ) : EReal) := by
  rcases ereal_trichotomy a with h | h | ⟨r, hr⟩
  · exact absurd h ha
  · rw [h, EReal.coe_mul_top_of_pos (by norm_num)]
    simp
  · rw [hr, ← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

namespace ProxCore

variable {f : E → EReal} {x : E} {ε : ℝ} (K : ProxCore f x ε)

theorem secondSubderivative_add_eq_two_mul {G₀ : E → E}
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (w : E) :
    secondSubderivative f x 0 w + ((K.mu * ‖w‖ ^ 2 : ℝ) : EReal) =
      ((2 : ℝ) : EReal) * K.convexMinorant G₀ w := by
  rw [← K.half_secondSubderivative_add_eq hG₀ w]
  rcases ereal_trichotomy (secondSubderivative f x 0 w) with h | h | ⟨r, hr⟩
  · exact absurd h (K.secondSubderivative_ne_bot w)
  · rw [h, EReal.top_add_coe, EReal.coe_mul_top_of_pos (by norm_num), EReal.top_add_coe,
      EReal.coe_mul_top_of_pos (by norm_num)]
  · rw [hr, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul,
      EReal.coe_eq_coe_iff]
    ring

/-- Under twice epi-differentiability, `d²f(x̄ | 0) + μ‖·‖²` is convex. -/
theorem convex_epigraph_secondSubderivative_add (hte : TwiceEpiDifferentiableAt f x 0) :
    Convex ℝ (epigraph (fun w ↦ secondSubderivative f x 0 w + ((K.mu * ‖w‖ ^ 2 : ℝ) : EReal))) := by
  choose G₀ hG₀ using K.tendsto_Gs_of_twiceEpi hte
  have hne : ∀ w, K.convexMinorant G₀ w ≠ ⊥ := fun w ↦ ((K.isProper_convexMinorant hG₀).2 w).ne'
  have hmem : ∀ p : E × ℝ, p ∈ epigraph (fun w ↦ secondSubderivative f x 0 w +
      ((K.mu * ‖w‖ ^ 2 : ℝ) : EReal)) ↔ (p.1, p.2 / 2) ∈ epigraph (K.convexMinorant G₀) := by
    intro p
    change secondSubderivative f x 0 p.1 + ((K.mu * ‖p.1‖ ^ 2 : ℝ) : EReal) ≤ (p.2 : EReal) ↔
      K.convexMinorant G₀ p.1 ≤ ((p.2 / 2 : ℝ) : EReal)
    rw [K.secondSubderivative_add_eq_two_mul hG₀, ereal_two_mul_le_coe_iff (hne p.1)]
  intro p hp q hq a b ha hb hab
  rw [hmem] at hp hq ⊢
  have h := K.convex_epigraph_convexMinorant hp hq ha hb hab
  convert h using 1
  ext
  · simp
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    ring

/-- Under twice epi-differentiability, `DT(x̄ | 0) + μI` is maximal monotone. -/
theorem svMaximalMonotone_graphicalDerivative_add (hte : TwiceEpiDifferentiableAt f x 0) :
    SvMaximalMonotone (fun w ↦
      (fun z ↦ z + K.mu • w) '' graphicalDerivative (proxLocalization f x ε) x 0 w) := by
  choose G₀ hG₀ using K.tendsto_Gs_of_twiceEpi hte
  have heq : (fun w ↦
      (fun z ↦ z + K.mu • w) '' graphicalDerivative (proxLocalization f x ε) x 0 w) =
      K.slopeMap G₀ := by
    funext w
    ext v
    rw [K.graphicalDerivative_eq hG₀]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [K.mem_subdifferential_half_iff hG₀] at hz
      refine ⟨w + K.lam • z, ?_, ?_⟩
      · simp only [w0, hz, add_sub_cancel_right]
      · simp only [w0, hz, add_sub_cancel_right]
    · rintro ⟨u, rfl, rfl⟩
      refine ⟨G₀ u, ?_, rfl⟩
      rw [K.mem_subdifferential_half_iff hG₀]
      simp only [w0, sub_add_cancel]
  rw [heq]
  exact K.svMaximalMonotone_slopeMap hG₀

include K in
/-- Under twice epi-differentiability, `d²f(x̄ | 0)` is prox-regular at every point for every
subgradient. -/
theorem isProxRegularAtPoint_secondSubderivative (hte : TwiceEpiDifferentiableAt f x 0) (w : E) :
    IsProxRegularAtPoint (secondSubderivative f x 0) w := by
  choose G₀ hG₀ using K.tendsto_Gs_of_twiceEpi hte
  set Ψ : E → EReal := fun w ↦ secondSubderivative f x 0 w + ((K.mu * ‖w‖ ^ 2 : ℝ) : EReal)
    with hΨ
  have hΨeq : Ψ = fun w ↦ ((2 : ℝ) : EReal) * K.convexMinorant G₀ w :=
    funext fun w ↦ K.secondSubderivative_add_eq_two_mul hG₀ w
  have hconv : Convex ℝ (epigraph Ψ) := K.convex_epigraph_secondSubderivative_add hte
  have hlsc : LowerSemicontinuous Ψ := by
    rw [hΨeq]
    intro w₁
    have h1 := K.lowerSemicontinuous_convexMinorant (G₀ := G₀) w₁
    have hcont : ContinuousAt (fun a : EReal ↦ ((2 : ℝ) : EReal) * a) (K.convexMinorant G₀ w₁) := by
      have hc0 : ((2 : ℝ) : EReal) ≠ 0 := by norm_num
      exact (EReal.continuousAt_mul (p := (((2 : ℝ) : EReal), K.convexMinorant G₀ w₁))
        (Or.inl hc0) (Or.inl hc0) (Or.inl (EReal.coe_ne_bot 2)) (Or.inl (EReal.coe_ne_top 2))).comp
        (continuousAt_const.prodMk continuousAt_id)
    exact hcont.comp_lowerSemicontinuousAt h1 fun a b hab ↦
      mul_le_mul_of_nonneg_left hab (by norm_num)
  have hprop : IsProper Ψ := by
    refine ⟨⟨0, ?_⟩, fun w₁ ↦ ?_⟩
    · simp only [hΨ, K.secondSubderivative_zero, norm_zero]
      norm_num
    · exact lt_of_lt_of_le (EReal.bot_lt_coe _) (le_trans (le_of_eq (by
        rw [EReal.coe_add])) (add_le_add (K.neg_le_secondSubderivative w₁) le_rfl))
  intro z hz
  obtain ⟨⟨c, hc⟩, -⟩ := mem_subdifferential_iff_exists_seq.1 hz
  have hgrad : ∀ (a : ℝ) (y : E), HasGradientAt (fun y ↦ a * ‖y‖ ^ 2) ((2 * a) • y) y :=
    fun a y ↦ by
      rw [hasGradientAt_iff_hasFDerivAt]
      have h := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt).const_mul a
      convert h using 1
      ext u
      simp [InnerProductSpace.toDual_apply_apply]
      ring
  have hlip : ∀ a : ℝ, ∀ y ∈ ball w 1, ∀ y' ∈ ball w 1,
      ‖(2 * a) • y - (2 * a) • y'‖ ≤ |2 * a| * ‖y - y'‖ := by
    intro a y _ y' _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  -- `z + 2μw ∈ ∂Ψ(w)`
  have hzΨ : z + (2 * K.mu) • w ∈ subdifferential Ψ w := by
    have h := subdifferential_add_lipschitz_gradient (f := secondSubderivative f x 0)
      (g := fun y ↦ K.mu * ‖y‖ ^ 2) (abs_nonneg (2 * K.mu)) (fun y _ ↦ hgrad K.mu y)
      (hlip K.mu) (mem_ball_self one_pos) hc
    have : subdifferential Ψ w = (fun u ↦ u + (2 * K.mu) • w) '' subdifferential
        (secondSubderivative f x 0) w := h
    rw [this]
    exact ⟨z, hz, rfl⟩
  have hwdom : w ∈ effectiveDomain Ψ := by
    obtain ⟨⟨c', hc'⟩, -⟩ := mem_subdifferential_iff_exists_seq.1 hzΨ
    change Ψ w < ⊤
    rw [hc']; exact EReal.coe_lt_top _
  have hpr := (prox_regularity_from_convexity hprop hlsc hconv hwdom).1 _ hzΨ
  have h := hpr.add_lipschitz_gradient (g := fun y ↦ (-K.mu) * ‖y‖ ^ 2) one_pos
    (abs_nonneg (2 * -K.mu)) (fun y _ ↦ hgrad (-K.mu) y) (hlip (-K.mu))
  have hfun : (fun y ↦ Ψ y + (((-K.mu) * ‖y‖ ^ 2 : ℝ) : EReal)) = secondSubderivative f x 0 := by
    funext y
    simp only [hΨ]
    rw [add_assoc, ← EReal.coe_add]
    ring_nf
    simp
  have hvec : z + (2 * K.mu) • w + (2 * -K.mu) • w = z := by
    rw [add_assoc, ← add_smul]; simp
  rw [hfun, hvec] at h
  exact h

end ProxCore

/-- **Proposition 13.49** (prox-regularity and amenability of second subderivatives), corrected.
If `f` is prox-regular and twice epi-differentiable at `x̄` for `v̄` (then `d²f(x̄ | v̄)` is
proper), there is `ρ ≥ 0` such that `d²f(x̄ | v̄) + ρ‖·‖²` is convex, `DT(x̄ | v̄) + ρI` is maximal
monotone for every sufficiently close `f`-attentive localization `T` of `∂f` around `(x̄, v̄)`, as
is `D(∂f)(x̄ | v̄) + ρI` when `f` is subdifferentially continuous at `x̄` for `v̄`, and `d²f(x̄ |
v̄)` is prox-regular everywhere. -/
theorem prox_regularity_of_second_subderivatives {f : E → EReal} {x v : E}
    (hf : IsProxRegularAt f x v) (hte : TwiceEpiDifferentiableAt f x v) :
    ∃ ρ ≥ 0,
      Convex ℝ (epigraph (fun w ↦ secondSubderivative f x v w + ((ρ * ‖w‖ ^ 2 : ℝ) : EReal))) ∧
      IsProper (secondSubderivative f x v) ∧
      (∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → SvMaximalMonotone (fun w ↦
        (fun z ↦ z + ρ • w) '' graphicalDerivative (attentiveLocalization f x v ε) x v w)) ∧
      (IsSubdifferentiallyContinuousAt f x v → SvMaximalMonotone (fun w ↦
        (fun z ↦ z + ρ • w) '' graphicalDerivative (subdifferential f) x v w)) ∧
      ∀ w, IsProxRegularAtPoint (secondSubderivative f x v) w := by
  obtain ⟨f₁, ε, K, hd2, hte₁, hsc_agree, ε₀, hε₀, hatt⟩ := hf.exists_proxCore
  have hte' : TwiceEpiDifferentiableAt f₁ x 0 := hte₁.2 hte
  have hmax := K.svMaximalMonotone_graphicalDerivative_add hte'
  have hD : ∀ S : E → Set E,
      (∀ᶠ p in 𝓝 (x, v), p.2 ∈ S p.1 ↔ p.2 - v ∈ proxLocalization f₁ x ε p.1) →
      SvMaximalMonotone (fun w ↦ (fun z ↦ z + K.mu • w) '' graphicalDerivative S x v w) := by
    intro S hS
    rw [(isProtoDifferentiableAt_iff_of_eventually hS).2]
    exact hmax
  have hprop : IsProper (secondSubderivative f x v) := by
    have h := K.isProper_half
    rw [hd2] at h
    refine ⟨⟨0, ?_⟩, fun w ↦ ?_⟩
    · rw [← hd2, K.secondSubderivative_zero]; exact EReal.zero_lt_top
    · rw [← hd2]; exact lt_of_lt_of_le (EReal.bot_lt_coe _) (K.neg_le_secondSubderivative w)
  refine ⟨K.mu, K.hmu.le, ?_, hprop, ⟨ε₀, hε₀, fun ε' h1 h2 ↦ hD _ (hatt ε' h1 h2)⟩,
    fun hsc ↦ hD _ (hsc_agree hsc), fun w ↦ ?_⟩
  · rw [← hd2]; exact K.convex_epigraph_secondSubderivative_add hte'
  · rw [← hd2]; exact K.isProxRegularAtPoint_secondSubderivative hte' w

/-- **Proposition 13.49**, the fully amenable case: then `f` is prox-regular, subdifferentially
continuous and properly twice epi-differentiable, so `d²f(x̄ | v̄) + ρ‖·‖²` is convex,
`D(∂f)(x̄ | v̄) + ρI` is maximal monotone and `d²f(x̄ | v̄)` is prox-regular everywhere. -/
theorem FullyAmenableAt.secondSubderivative_convexity {f : E → EReal} {x v : E}
    (hf : FullyAmenableAt f x) (hv : v ∈ subdifferential f x) :
    ∃ ρ ≥ 0,
      Convex ℝ (epigraph (fun w ↦ secondSubderivative f x v w + ((ρ * ‖w‖ ^ 2 : ℝ) : EReal))) ∧
      SvMaximalMonotone (fun w ↦
        (fun z ↦ z + ρ • w) '' graphicalDerivative (subdifferential f) x v w) ∧
      ∀ w, IsProxRegularAtPoint (secondSubderivative f x v) w := by
  obtain ⟨hpr, hsc⟩ := hf.stronglyAmenableAt.isProxRegularAt hv
  obtain ⟨ρ, hρ, h1, -, -, h4, h5⟩ :=
    prox_regularity_of_second_subderivatives hpr (hf.properlyTwiceEpiDifferentiableAt hv).1
  exact ⟨ρ, hρ, h1, h4 hsc, h5⟩

end RW
