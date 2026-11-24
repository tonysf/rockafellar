/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order Lipschitz continuity

Exercise 13.55 and Proposition 13.56, partially.

* Necessity in 13.55 (`IsC1PlusOn.exists_mixed_difference_bound`): a `C¹⁺` function satisfies the
  second-order Lipschitz condition 13(35), by the mean value theorem along `t ↦ f(x + w + tz) - f(x + tz)`.
* Proposition 13.56, (a) ⇒ (c) with the value `⟪z, ∇²f(x̄)w⟫` of the limit
  (`tendsto_mixedSecondDifference_of_hasStrictFDerivAt`), by the mean value step of 13.52.
* **Correction.**  The sufficiency in 13.55, and the implication (c) ⇒ (a) in 13.56, fail for
functions
  that are merely finite: a `ℚ`-linear coordinate functional `h : ℝ → ℝ` for a Hamel basis
  (`hamelFunction`) is additive, so all its mixed second differences vanish (13(35) holds with `κ = 0`
  and the limits in 13.56(c) exist and equal `0`), but `h` is not continuous, let alone `C¹⁺`
  (`hamelFunction_counterexample`).  The guide's step bounding the quotients `d_w(x)` needs `f`
  bounded around `x̄`.
-/

import RockafellarWets.Chapter13.GeneralizedHessians

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

/-! ### Necessity in Exercise 13.55 -/

section Necessity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 13.55**, necessity: a function of class `C¹⁺` around `x̄` satisfies 13(35): for some
`ε > 0` and `κ ≥ 0`, `|f(x + w + z) - f(x + w) - f(x + z) + f(x)| ≤ κ‖w‖‖z‖` when `‖x - x̄‖ ≤ ε`,
`‖w‖ ≤ ε`, `‖z‖ ≤ ε`. -/
theorem IsC1PlusOn.exists_mixed_difference_bound {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : IsC1PlusOn f O) {x : E} (hx : x ∈ O) :
    ∃ ε > 0, ∃ κ ≥ 0, ∀ y w z : E, ‖y - x‖ ≤ ε → ‖w‖ ≤ ε → ‖z‖ ≤ ε →
      |f (y + w + z) - f (y + w) - f (y + z) + f y| ≤ κ * ‖w‖ * ‖z‖ := by
  obtain ⟨L, U, hU, hL⟩ := strictlyContinuousAt_iff.1 (hf x hx).2
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 (inter_mem hU (hO.mem_nhds hx))
  refine ⟨r / 4, by positivity, L, L.coe_nonneg, fun y w z hy hw hz ↦ ?_⟩
  have hmem : ∀ a : E, ‖a - x‖ < r → a ∈ U ∩ O := fun a ha ↦ hrU (by rwa [mem_ball, dist_eq_norm])
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c : E, ‖c‖ ≤ r / 4 → ‖y + c + t • z - x‖ < r := by
    intro t ht c hc
    have h1 : ‖t • z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]; exact mul_le_of_le_one_left (norm_nonneg z) ht.2
    calc ‖y + c + t • z - x‖ = ‖(y - x) + c + t • z‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖c‖ + ‖t • z‖ := norm_add₃_le
      _ < r := by linarith
  set g : ℝ → ℝ := fun t ↦ f (y + w + t • z) - f (y + t • z) with hg
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g
      (⟪gradient f (y + w + t • z) - gradient f (y + t • z), z⟫_ℝ) (Icc 0 1) t := by
    intro t ht
    have hd : ∀ c : E, ‖c‖ ≤ r / 4 → HasDerivAt (fun t : ℝ ↦ f (y + c + t • z))
        ⟪gradient f (y + c + t • z), z⟫_ℝ t := by
      intro c hc
      have hdiff := (hf _ (hmem _ (hpt t ht c hc)).2).1
      have hgr := hdiff.hasGradientAt
      rw [hasGradientAt_iff_hasFDerivAt] at hgr
      have hp : HasDerivAt (fun t : ℝ ↦ y + c + t • z) z t := by
        simpa using ((hasDerivAt_id t).smul_const z).const_add (y + c)
      have := hgr.comp_hasDerivAt t hp
      simpa [InnerProductSpace.toDual_apply_apply] using this
    have h1 := hd w hw
    have h2 := hd 0 (by rw [norm_zero]; positivity)
    simp only [add_zero] at h2
    rw [inner_sub_left]
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖⟪gradient f (y + w + t • z) - gradient f (y + t • z), z⟫_ℝ‖ ≤ L * ‖w‖ * ‖z‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have h1 := hL.norm_sub_le (hmem _ (hpt t ht' w hw)).1
      (hmem _ (by simpa using hpt t ht' 0 (by rw [norm_zero]; positivity))).1
    rw [show y + w + t • z - (y + t • z) = w by abel] at h1
    rw [Real.norm_eq_abs]
    calc |⟪gradient f (y + w + t • z) - gradient f (y + t • z), z⟫_ℝ| ≤
          ‖gradient f (y + w + t • z) - gradient f (y + t • z)‖ * ‖z‖ := abs_real_inner_le_norm _ _
      _ ≤ L * ‖w‖ * ‖z‖ := by gcongr
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 (by simp)
  simp only [hg, one_smul, zero_smul, add_zero, sub_zero, mul_one, Real.norm_eq_abs] at h
  calc |f (y + w + z) - f (y + w) - f (y + z) + f y| =
        |f (y + w + z) - f (y + z) - (f (y + w) - f y)| := by ring_nf
    _ ≤ L * ‖w‖ * ‖z‖ := h

/-- **Proposition 13.56**, (a) ⇒ (c) with the value of the limit: if `f` is differentiable around
`x̄` and `∇f` is strictly differentiable at `x̄` with derivative `A`, the mixed second differences
`[f(x + τw + σz) - f(x + τw) - f(x + σz) + f(x)]/(τσ)` converge to `⟪z, Aw⟫` as `x → x̄`,
`τ ↓ 0`, `σ ↓ 0`. -/
theorem tendsto_mixedSecondDifference_of_hasStrictFDerivAt {f : E → ℝ} {x : E} {A : E →L[ℝ] E}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hA : HasStrictFDerivAt (gradient f) A x)
    (w z : E) :
    Tendsto (fun p : E × ℝ × ℝ ↦ mixedSecondDifference f p.1 w z p.2.1 p.2.2)
      (𝓝 x ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 ⟪z, A w⟫_ℝ) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set η' := η / (2 * (‖z‖ * ‖w‖ + 1)) with hη'
  have hη'0 : 0 < η' := by positivity
  have hstrict := hasStrictFDerivAt_iff_isLittleO.1 hA
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.1 (hstrict.def hη'0)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.1 hf
  set r := min r₁ r₂ with hr
  have hr0 : 0 < r := lt_min hr₁ hr₂
  have hU : ball x (r / 3) ×ˢ (Ioo 0 (r / (3 * (‖w‖ + 1))) ×ˢ Ioo 0 (r / (3 * (‖z‖ + 1)))) ∈
      𝓝 x ×ˢ (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) :=
    prod_mem_prod (ball_mem_nhds _ (by positivity)) (prod_mem_prod
      (Ioo_mem_nhdsGT (by positivity)) (Ioo_mem_nhdsGT (by positivity)))
  filter_upwards [hU] with p hp
  obtain ⟨y, τ, σ⟩ := p
  obtain ⟨hy, ⟨hτ0, hτ1⟩, ⟨hσ0, hσ1⟩⟩ := hp
  rw [mem_ball, dist_eq_norm] at hy
  have hτw : τ * ‖w‖ < r / 3 := by
    rw [lt_div_iff₀ (by positivity)] at hτ1; nlinarith [norm_nonneg w]
  have hσz : σ * ‖z‖ < r / 3 := by
    rw [lt_div_iff₀ (by positivity)] at hσ1; nlinarith [norm_nonneg z]
  have hnorm : ∀ s ∈ Icc (0 : ℝ) σ, ‖y + s • z - x‖ < 2 * r / 3 := by
    intro s hs
    have := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg z)
    calc ‖y + s • z - x‖ = ‖(y - x) + s • z‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + s * ‖z‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg hs.1]
      _ < 2 * r / 3 := by linarith
  have hnorm' : ∀ s ∈ Icc (0 : ℝ) σ, ‖y + s • z + τ • w - x‖ < r := by
    intro s hs
    calc ‖y + s • z + τ • w - x‖ = ‖(y + s • z - x) + τ • w‖ := by congr 1; abel
      _ ≤ ‖y + s • z - x‖ + τ * ‖w‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg hτ0.le]
      _ < r := by linarith [hnorm s hs]
  have hO : ∀ a ∈ ball x r, DifferentiableAt ℝ f a := fun a ha ↦
    hball₂ (ball_subset_ball (min_le_right r₁ r₂) ha)
  have hseg : ∀ s ∈ Icc (0 : ℝ) σ, y + s • z ∈ ball x r ∧ y + s • z + τ • w ∈ ball x r := by
    intro s hs
    refine ⟨?_, ?_⟩ <;> rw [mem_ball, dist_eq_norm]
    · linarith [hnorm s hs]
    · exact hnorm' s hs
  obtain ⟨s, hs, heq⟩ := mixedSecondDifference_eq_mvt hO hτ0 hσ0 hseg
  have hs' : s ∈ Icc (0 : ℝ) σ := Ioo_subset_Icc_self hs
  have hpair : ((y + s • z + τ • w, y + s • z) : E × E) ∈ ball (x, x) r₁ := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
    exact ⟨lt_of_lt_of_le (hnorm' s hs') (min_le_left _ _),
      by linarith [hnorm s hs', min_le_left r₁ r₂]⟩
  have hest := hball₁ hpair
  simp only [mem_setOf_eq] at hest
  rw [show y + s • z + τ • w - (y + s • z) = τ • w by abel, norm_smul,
    Real.norm_of_nonneg hτ0.le, map_smul] at hest
  rw [Real.dist_eq, heq]
  have hkey : (⟪z, gradient f (y + s • z + τ • w)⟫_ℝ - ⟪z, gradient f (y + s • z)⟫_ℝ) / τ -
      ⟪z, A w⟫_ℝ =
      ⟪z, gradient f (y + s • z + τ • w) - gradient f (y + s • z) - τ • A w⟫_ℝ / τ := by
    rw [inner_sub_right, inner_sub_right, inner_smul_right]
    field_simp
  rw [hkey, abs_div, abs_of_pos hτ0, div_lt_iff₀ hτ0]
  calc |⟪z, gradient f (y + s • z + τ • w) - gradient f (y + s • z) - τ • A w⟫_ℝ| ≤
        ‖z‖ * ‖gradient f (y + s • z + τ • w) - gradient f (y + s • z) - τ • A w‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖z‖ * (η' * (τ * ‖w‖)) := by gcongr
    _ < η * τ := by
        have h1 : ‖z‖ * (η' * (τ * ‖w‖)) = τ * (η' * (‖z‖ * ‖w‖)) := by ring
        have h2 : η' * (‖z‖ * ‖w‖) < η := by
          rw [hη']
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [mul_nonneg (norm_nonneg z) (norm_nonneg w)]
        rw [h1]; nlinarith

end Necessity

/-! ### A discontinuous additive function -/

section Hamel

/-- The index of a fixed vector of a Hamel basis of `ℝ` over `ℚ`. -/
noncomputable def hamelIndex : Module.Basis.ofVectorSpaceIndex ℚ ℝ :=
  Classical.choice (Module.Basis.ofVectorSpace ℚ ℝ).index_nonempty

/-- A `ℚ`-linear coordinate functional `h : ℝ → ℝ` for a Hamel basis. -/
noncomputable def hamelFunction (x : ℝ) : ℝ :=
  ((Module.Basis.ofVectorSpace ℚ ℝ).coord hamelIndex x : ℝ)

theorem hamelFunction_add (x y : ℝ) :
    hamelFunction (x + y) = hamelFunction x + hamelFunction y := by
  simp [hamelFunction]

theorem hamelFunction_basis : hamelFunction ((Module.Basis.ofVectorSpace ℚ ℝ) hamelIndex) = 1 := by
  rw [hamelFunction, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    Rat.cast_one]

theorem hamelFunction_mixed (x w z : ℝ) :
    hamelFunction (x + w + z) - hamelFunction (x + w) - hamelFunction (x + z) +
      hamelFunction x = 0 := by
  simp only [hamelFunction_add]; ring

/-- The additive homomorphism underlying `hamelFunction`. -/
noncomputable def hamelAddHom : ℝ →+ ℝ where
  toFun := hamelFunction
  map_zero' := by simp [hamelFunction]
  map_add' := hamelFunction_add

theorem not_continuous_hamelFunction : ¬ Continuous hamelFunction := by
  intro hc
  set φ := hamelAddHom.toRealLinearMap hc
  have hφ : ∀ r : ℝ, hamelFunction r = r * hamelFunction 1 := by
    intro r
    have h := φ.map_smul r 1
    simpa [φ, hamelAddHom, smul_eq_mul] using h
  have h1 : hamelFunction 1 ≠ 0 := by
    intro h0
    have := hφ ((Module.Basis.ofVectorSpace ℚ ℝ) hamelIndex)
    rw [hamelFunction_basis, h0, mul_zero] at this
    exact one_ne_zero this
  have hq : ∀ r, ∃ q : ℚ, hamelFunction r = q := fun r ↦ ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hq (Real.sqrt 2 / hamelFunction 1)
  rw [hφ, div_mul_cancel₀ _ h1] at hq
  exact irrational_sqrt_two ⟨q, hq.symm⟩

/-- **Counterexample to the sufficiency in Exercise 13.55 and to 13.56 (c) ⇒ (a)** as printed:
`hamelFunction` is finite everywhere, satisfies 13(35) with `κ = 0` around every point, and its
mixed second differences converge (to `0`) for all directions, yet it is not differentiable
anywhere (indeed not continuous), so it is not of class `C¹⁺` around any point. -/
theorem hamelFunction_counterexample :
    (∀ x w z : ℝ, |hamelFunction (x + w + z) - hamelFunction (x + w) - hamelFunction (x + z) +
      hamelFunction x| ≤ 0 * ‖w‖ * ‖z‖) ∧
    (∀ x₀ w z : ℝ, Tendsto
      (fun p : ℝ × ℝ × ℝ ↦ mixedSecondDifference hamelFunction p.1 w z p.2.1 p.2.2)
      (𝓝 x₀ ×ˢ (𝓝[>] 0 ×ˢ 𝓝[>] 0)) (𝓝 0)) ∧
    (∀ x : ℝ, ¬ DifferentiableAt ℝ hamelFunction x) ∧
    (∀ x : ℝ, ∀ O : Set ℝ, x ∈ O → ¬ IsC1PlusOn hamelFunction O) := by
  have hnd : ∀ x : ℝ, ¬ DifferentiableAt ℝ hamelFunction x := by
    intro x hx
    have hcx : ContinuousAt hamelFunction x := hx.continuousAt
    apply not_continuous_hamelFunction
    have h0 : ContinuousAt hamelAddHom 0 := by
      have heq : (hamelAddHom : ℝ → ℝ) = fun y ↦ hamelFunction (y + x) - hamelFunction x := by
        funext y; simp [hamelAddHom, hamelFunction_add]
      rw [heq]
      have hc : ContinuousAt (fun y : ℝ ↦ y + x) 0 := (continuous_add_right x).continuousAt
      exact (hcx.comp_of_eq hc (zero_add x)).sub continuousAt_const
    exact continuous_of_continuousAt_zero hamelAddHom h0
  refine ⟨fun x w z ↦ by rw [hamelFunction_mixed]; simp, fun x₀ w z ↦ ?_, hnd,
    fun x O hx hC ↦ hnd x (hC x hx).1⟩
  refine tendsto_const_nhds.congr fun p ↦ ?_
  rw [mixedSecondDifference, hamelFunction_mixed, zero_div]

end Hamel

end RW
