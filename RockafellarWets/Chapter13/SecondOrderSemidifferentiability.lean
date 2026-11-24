/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Characterizations of second-order semidifferentiability

Exercise 13.7, following the proof of Theorem 7.21 as the book's guide says.
Uniform convergence on bounded sets is the extended uniform convergence of
Definition 7.12 used in 7.21; the second-order expansion is read with
Mathlib's little-o.  Since `f` is semidifferentiable at `x̄`, `df(x̄)` is
finite and `f` is finite near `x̄`.
-/

import RockafellarWets.Chapter13.SmoothAddition
import RockafellarWets.Chapter7.SemidifferentiabilityCharacterizations

open Filter Set Topology Metric Asymptotics
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Helpers

variable {f : E → EReal} {x : E} {c : ℝ}

/-- With `df(x̄)(w) = d` finite, the quotient 13(4) as a real number. -/
theorem secondDifferenceQuotientAt_of_coe {τ r d : ℝ} {w : E} (hx : f x = c)
    (hd : subderivative f x w = d) (hr : f (x + τ • w) = r) :
    secondDifferenceQuotientAt f x τ w = ((2 / τ ^ 2 * (r - c - τ * d) : ℝ) : EReal) := by
  rw [secondDifferenceQuotientAt, hd, hr, hx, ← EReal.coe_mul, ← EReal.coe_neg,
    infAddition_coe_right, ← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_mul]
  ring_nf

/-- Under semidifferentiability `df(x̄)(0) = 0`, so the quotients 13(4) vanish at `0`. -/
theorem secondDifferenceQuotientAt_zero_of_semidifferentiableAt (hx : f x = c)
    (hs : SemidifferentiableAt f x) (τ : ℝ) : secondDifferenceQuotientAt f x τ 0 = 0 := by
  obtain ⟨g, -, hgs, hall⟩ := hs.exists_semiderivative
  have hg0 : g 0 = 0 := by
    have := hgs 2 two_pos 0
    rw [smul_zero] at this
    linarith
  have hd0 : subderivative f x 0 = 0 := by rw [(hall 0).2.1, hg0, EReal.coe_zero]
  exact secondDifferenceQuotientAt_zero_right hx hd0 τ

end Helpers

theorem mem_compl_bot_top_of_ne {a : EReal} (h1 : a ≠ ⊤) (h2 : a ≠ ⊥) :
    a ∈ ({⊥, ⊤} : Set EReal)ᶜ := by
  simp [h1, h2]

/-! ### Exercise 13.7 -/

section Exercise137

variable [FiniteDimensional ℝ E] {f : E → EReal} {x : E}

omit [FiniteDimensional ℝ E] in
/-- Under twice semidifferentiability `d²f(x̄)` is finite and continuous (the last sentence
of 13.7). -/
theorem TwiceSemidifferentiableAt.finite_continuous (h : TwiceSemidifferentiableAt f x) :
    Continuous (secondSubderivativeAt f x) ∧
      ∀ w, secondSubderivativeAt f x w ≠ ⊤ ∧ secondSubderivativeAt f x w ≠ ⊥ := by
  obtain ⟨hs, hconv⟩ := h
  obtain ⟨β, hβ⟩ := hs 0
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hβ.2.1 hβ.1).symm
  set H := secondSubderivativeAt f x
  have hcont : Continuous H := continuous_of_forall_tendsto_prod hconv
  have h0 : H 0 = 0 := by
    have h1 := (hconv 0).comp (tendsto_pair_const (0 : E))
    have h2 : Tendsto (fun τ : ℝ ↦ secondDifferenceQuotientAt f x τ 0) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simp only [secondDifferenceQuotientAt_zero_of_semidifferentiableAt hxc hs]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  refine ⟨hcont, fun w ↦ ?_⟩
  have hU : H ⁻¹' Ioo ((-1 : ℝ) : EReal) ((1 : ℝ) : EReal) ∈ 𝓝 (0 : E) := by
    apply hcont.continuousAt.preimage_mem_nhds
    rw [h0]
    exact Ioo_mem_nhds
      (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (show (-1 : ℝ) < 0 by norm_num))
        (le_of_eq EReal.coe_zero))
      (lt_of_le_of_lt (le_of_eq EReal.coe_zero.symm)
        (EReal.coe_lt_coe_iff.2 (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  rcases eq_or_ne w 0 with rfl | hw
  · rw [h0]
    exact ⟨EReal.zero_ne_top, EReal.zero_ne_bot⟩
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
    set s : ℝ := δ / (2 * ‖w‖) with hs_def
    have hs : 0 < s := by positivity
    have hu : s • w ∈ ball (0 : E) δ := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hs.le, hs_def]
      have : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 := by field_simp
      rw [this]
      linarith
    have hmem : H (s • w) ∈ Ioo ((-1 : ℝ) : EReal) ((1 : ℝ) : EReal) := hball hu
    have hne_top : H (s • w) ≠ ⊤ := ne_top_of_lt hmem.2
    have hne_bot : H (s • w) ≠ ⊥ := ne_bot_of_gt hmem.1
    have hw' : w = s⁻¹ • (s • w) := by rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    rw [hw']
    change secondSubderivativeAt f x (s⁻¹ • s • w) ≠ ⊤ ∧ secondSubderivativeAt f x (s⁻¹ • s • w) ≠ ⊥
    rw [secondSubderivativeAt_smul hxc (inv_pos.2 hs)]
    change ((s⁻¹ ^ 2 : ℝ) : EReal) * H (s • w) ≠ ⊤ ∧ ((s⁻¹ ^ 2 : ℝ) : EReal) * H (s • w) ≠ ⊥
    rw [← EReal.coe_toReal hne_top hne_bot, ← EReal.coe_mul]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- **Exercise 13.7**, `(a) ⇒ (c)`: twice semidifferentiability gives the second-order
expansion with `h = d²f(x̄)`. -/
theorem TwiceSemidifferentiableAt.isLittleO (h : TwiceSemidifferentiableAt f x) :
    (∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤) ∧
      (fun y ↦ (f y).toReal - (f x).toReal - (subderivative f x (y - x)).toReal -
        1 / 2 * (secondSubderivativeAt f x (y - x)).toReal) =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2) := by
  obtain ⟨hcont, hfinite⟩ := h.finite_continuous
  obtain ⟨hs, hconv⟩ := h
  obtain ⟨g, hg, hgs, hall⟩ := hs.exists_semiderivative
  obtain ⟨β, hβ⟩ := hs 0
  set c := (f x).toReal
  have hxc : f x = (c : EReal) := (EReal.coe_toReal hβ.2.1 hβ.1).symm
  have hd : ∀ w, subderivative f x w = (g w : EReal) := fun w ↦ (hall w).2.1
  obtain ⟨hfin, -⟩ := isLittleO_of_forall_tendsto hxc hg hgs fun w ↦ (hall w).1.2.2
  refine ⟨hfin, ?_⟩
  set H : E → ℝ := fun w ↦ (secondSubderivativeAt f x w).toReal with hHdef
  have hHc : Continuous H := EReal.continuousOn_toReal.comp_continuous hcont
    fun w ↦ mem_compl_bot_top_of_ne (hfinite w).1 (hfinite w).2
  have hHe : ∀ w, secondSubderivativeAt f x w = (H w : EReal) := fun w ↦
    (EReal.coe_toReal (hfinite w).1 (hfinite w).2).symm
  have hHs : ∀ a : ℝ, 0 < a → ∀ w, H (a • w) = a ^ 2 * H w := by
    intro a ha w
    simp only [hHdef]
    rw [secondSubderivativeAt_smul hxc ha, hHe w, ← EReal.coe_mul, EReal.toReal_coe,
      EReal.toReal_coe]
  have hg0 : g 0 = 0 := by
    have := hgs 2 two_pos 0
    rw [smul_zero] at this
    linarith
  have hH0 : H 0 = 0 := by
    have := hHs 2 two_pos 0
    rw [smul_zero] at this
    nlinarith
  have hF : ∀ w ∈ sphere (0 : E) 1, Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (H w : EReal)) := fun w _ ↦ by
    rw [← hHe w]
    exact hconv w
  rw [isLittleO_iff]
  intro ε hε
  have hU := eventually_forall_mem_of_forall_tendsto (isCompact_sphere 0 1) hHc hF
    (show 0 < 2 * ε by positivity)
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  obtain ⟨δ₂, hδ₂, hball⟩ := Metric.mem_nhds_iff.1 hfin
  filter_upwards [ball_mem_nhds x (lt_min hδ₁ hδ₂)] with y hy
  rw [mem_ball, dist_eq_norm] at hy
  rcases eq_or_ne y x with rfl | hyx
  · simp [hxc, hd, hg0, hHe, hH0]
  have hτ : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  set τ := ‖y - x‖ with hτdef
  set w : E := τ⁻¹ • (y - x) with hwdef
  have hw : w ∈ sphere (0 : E) 1 := by
    simp only [hwdef, mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.2 hτ.le), ← hτdef, inv_mul_cancel₀ hτ.ne']
  have hyw : x + τ • w = y := by
    rw [hwdef, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
  have hyw' : y - x = τ • w := by rw [← hyw, add_sub_cancel_left]
  obtain ⟨hb, ht⟩ := hball (show y ∈ ball x δ₂ by
    rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_right _ _))
  set r := (f y).toReal
  have hfy : f y = (r : EReal) := (EReal.coe_toReal ht hb).symm
  have hbound := hδ₁U ⟨hτ, lt_of_lt_of_le hy (min_le_left _ _)⟩ w hw
  rw [secondDifferenceQuotientAt_of_coe hxc (hd w) (by rw [hyw, hfy]),
    EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff] at hbound
  rw [hyw']
  change ‖r - c - (subderivative f x (τ • w)).toReal - 1 / 2 * H (τ • w)‖ ≤ ε * ‖τ ^ 2‖
  rw [hd, EReal.toReal_coe, hgs τ hτ, hHs τ hτ, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg τ)]
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hkey : |2 / τ ^ 2 * (r - c - τ * g w) - H w| < 2 * ε := by
    rw [abs_lt]
    constructor <;> linarith [hbound.1, hbound.2]
  have heq : r - c - τ * g w - 1 / 2 * (τ ^ 2 * H w) =
      τ ^ 2 / 2 * (2 / τ ^ 2 * (r - c - τ * g w) - H w) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < τ ^ 2 / 2)]
  nlinarith [abs_nonneg (2 / τ ^ 2 * (r - c - τ * g w) - H w)]

omit [FiniteDimensional ℝ E] in
/-- **Exercise 13.7**, `(c) ⇒ (b)`: a second-order expansion gives uniform convergence of the
quotients on bounded sets. -/
theorem extendedTendstoUniformlyOn_of_secondOrder_isLittleO {f : E → EReal} {x : E}
    (hs : SemidifferentiableAt f x) {H : E → ℝ}
    (hHs : ∀ a : ℝ, 0 < a → ∀ w, H (a • w) = a ^ 2 * H w)
    (hfin : ∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤)
    (ho : (fun y ↦ (f y).toReal - (f x).toReal - (subderivative f x (y - x)).toReal -
        1 / 2 * H (y - x)) =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2))
    {B : Set E} (hB : Bornology.IsBounded B) :
    ExtendedTendstoUniformlyOn (fun τ ↦ secondDifferenceQuotientAt f x τ) (fun w ↦ (H w : EReal))
      (𝓝[>] (0 : ℝ)) B := by
  obtain ⟨g, -, hgs, hall⟩ := hs.exists_semiderivative
  obtain ⟨β, hβ⟩ := hs 0
  set c := (f x).toReal
  have hxc : f x = (c : EReal) := (EReal.coe_toReal hβ.2.1 hβ.1).symm
  have hd : ∀ w, subderivative f x w = (g w : EReal) := fun w ↦ (hall w).2.1
  intro ρ hρ ε hε
  obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : E)
  set R' : ℝ := max R 1 with hR'_def
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hkey : ∀ᶠ y in 𝓝 x, (f y ≠ ⊥ ∧ f y ≠ ⊤) ∧
      ‖(f y).toReal - c - (subderivative f x (y - x)).toReal - 1 / 2 * H (y - x)‖ ≤
        ε / (2 * R' ^ 2) * ‖‖y - x‖ ^ 2‖ :=
    hfin.and (isLittleO_iff.1 ho (by positivity))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hkey
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR')] with τ hτ w hw
  have hτ0 : 0 < τ := hτ.1
  have hwR : ‖w‖ ≤ R' := by
    have := hR hw
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hy : x + τ • w ∈ ball x δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le]
    calc τ * ‖w‖ ≤ τ * R' := mul_le_mul_of_nonneg_left hwR hτ0.le
      _ < δ / R' * R' := mul_lt_mul_of_pos_right hτ.2 hR'
      _ = δ := by field_simp
  obtain ⟨⟨hb, ht⟩, hest⟩ := hball hy
  set r := (f (x + τ • w)).toReal
  have hfy : f (x + τ • w) = (r : EReal) := (EReal.coe_toReal ht hb).symm
  change |erealTrunc ρ (secondDifferenceQuotientAt f x τ w) - erealTrunc ρ (H w)| ≤ ε
  rw [secondDifferenceQuotientAt_of_coe hxc (hd w) hfy, erealTrunc_coe hρ.le,
    erealTrunc_coe hρ.le]
  refine (abs_clamp_sub_clamp_le ρ _ _).trans ?_
  rw [add_sub_cancel_left, hd, EReal.toReal_coe, hgs τ hτ0, hHs τ hτ0, norm_smul,
    Real.norm_of_nonneg hτ0.le, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (τ * ‖w‖) ^ 2)] at hest
  have hτ2 : 0 < τ ^ 2 := by positivity
  have heq : 2 / τ ^ 2 * (r - c - τ * g w) - H w =
      2 / τ ^ 2 * (r - c - τ * g w - 1 / 2 * (τ ^ 2 * H w)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / τ ^ 2)]
  have hw2 : ‖w‖ ^ 2 ≤ R' ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hwR 2
  calc 2 / τ ^ 2 * |r - c - τ * g w - 1 / 2 * (τ ^ 2 * H w)|
      ≤ 2 / τ ^ 2 * (ε / (2 * R' ^ 2) * (τ * ‖w‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hest (by positivity)
    _ = ε * (‖w‖ ^ 2 / R' ^ 2) := by field_simp
    _ ≤ ε * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hε.le
        rw [div_le_one (by positivity)]
        exact hw2
    _ = ε := mul_one ε

/-- **Exercise 13.7**: for `f` semidifferentiable at `x̄`, the following are equivalent:
(a) `f` is twice semidifferentiable at `x̄`;
(b) as `τ ↓ 0` the quotients `Δ²_τ f(x̄)` converge uniformly on bounded sets to a continuous `h`;
(c) there is a finite continuous `h`, positively homogeneous of degree 2, with
`f(x) = f(x̄) + df(x̄)(x - x̄) + ½h(x - x̄) + o(‖x - x̄‖²)`. -/
theorem characterizations_of_second_order_semidifferentiability (hs : SemidifferentiableAt f x) :
    List.TFAE [
      TwiceSemidifferentiableAt f x,
      ∃ h : E → EReal, Continuous h ∧ ∀ B : Set E, Bornology.IsBounded B →
        ExtendedTendstoUniformlyOn (fun τ ↦ secondDifferenceQuotientAt f x τ) h (𝓝[>] (0 : ℝ)) B,
      ∃ h : E → ℝ, Continuous h ∧ (∀ a : ℝ, 0 < a → ∀ w, h (a • w) = a ^ 2 * h w) ∧
        (∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤) ∧
        (fun y ↦ (f y).toReal - (f x).toReal - (subderivative f x (y - x)).toReal -
          1 / 2 * h (y - x)) =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2)] := by
  obtain ⟨β, hβ⟩ := hs 0
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hβ.2.1 hβ.1).symm
  tfae_have 1 → 3 := by
    intro h
    obtain ⟨hcont, hfinite⟩ := h.finite_continuous
    obtain ⟨hfin, ho⟩ := h.isLittleO
    refine ⟨fun w ↦ (secondSubderivativeAt f x w).toReal,
      EReal.continuousOn_toReal.comp_continuous hcont fun w ↦
        mem_compl_bot_top_of_ne (hfinite w).1 (hfinite w).2,
      fun a ha w ↦ ?_, hfin, ho⟩
    change (secondSubderivativeAt f x (a • w)).toReal = a ^ 2 * (secondSubderivativeAt f x w).toReal
    rw [secondSubderivativeAt_smul hxc ha,
      ← EReal.coe_toReal (hfinite w).1 (hfinite w).2, ← EReal.coe_mul, EReal.toReal_coe,
      EReal.toReal_coe]
  tfae_have 3 → 2 := by
    rintro ⟨H, hHc, hHs, hfin, ho⟩
    exact ⟨fun w ↦ (H w : EReal), continuous_coe_real_ereal.comp hHc, fun B hB ↦
      extendedTendstoUniformlyOn_of_secondOrder_isLittleO hs hHs hfin ho hB⟩
  tfae_have 2 → 1 := by
    rintro ⟨h, hh, hu⟩
    have hlim := tendsto_of_extendedTendstoUniformlyOn hh hu
    exact ⟨hs, fun w ↦ by
      have heq : secondSubderivativeAt f x w = h w := (hlim w).liminf_eq
      rw [heq]
      exact hlim w⟩
  tfae_finish

omit [FiniteDimensional ℝ E] in
/-- **Exercise 13.7**, the uniqueness clause: in (b), and in (c), the function `h` must be
`d²f(x̄)`. -/
theorem eq_secondSubderivativeAt_of_extendedTendstoUniformlyOn {h : E → EReal}
    (hh : Continuous h) (hu : ∀ B : Set E, Bornology.IsBounded B →
      ExtendedTendstoUniformlyOn (fun τ ↦ secondDifferenceQuotientAt f x τ) h (𝓝[>] (0 : ℝ)) B) :
    secondSubderivativeAt f x = h :=
  funext fun w ↦ (tendsto_of_extendedTendstoUniformlyOn hh hu w).liminf_eq

omit [FiniteDimensional ℝ E] in
theorem eq_secondSubderivativeAt_of_secondOrder_isLittleO (hs : SemidifferentiableAt f x)
    {H : E → ℝ} (hHc : Continuous H) (hHs : ∀ a : ℝ, 0 < a → ∀ w, H (a • w) = a ^ 2 * H w)
    (hfin : ∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤)
    (ho : (fun y ↦ (f y).toReal - (f x).toReal - (subderivative f x (y - x)).toReal -
        1 / 2 * H (y - x)) =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2)) :
    secondSubderivativeAt f x = fun w ↦ (H w : EReal) :=
  eq_secondSubderivativeAt_of_extendedTendstoUniformlyOn (continuous_coe_real_ereal.comp hHc)
    fun _ hB ↦ extendedTendstoUniformlyOn_of_secondOrder_isLittleO hs hHs hfin ho hB

end Exercise137

end RW
