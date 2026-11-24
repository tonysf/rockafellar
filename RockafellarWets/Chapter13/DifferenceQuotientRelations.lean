/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Difference quotient relations

Lemma 13.39.  The halved quotient `½Δ²_τ f(x̄ | v̄)` is an affine
reparametrization of `f`, so its subgradients are the difference quotients of
`∂f`; in the normalized case its Moreau envelopes and proximal mappings are
the corresponding quotients of `e_λ f` and `P_λ f`.
-/

import RockafellarWets.Chapter13.SecondOrderDuality
import RockafellarWets.Chapter8.ProtoDifferentiability
import RockafellarWets.Chapter1.Proximal

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Multiplication by a positive real commutes with infima in `EReal`. -/
theorem ereal_coe_mul_iInf {ι : Sort*} (a : ι → EReal) {c : ℝ} (hc : 0 < c) :
    (c : EReal) * (⨅ i, a i) = ⨅ i, (c : EReal) * a i := by
  apply le_antisymm
  · refine le_iInf fun i ↦ ?_
    gcongr
    exact iInf_le a i
  · have hinv : ((c⁻¹ : ℝ) : EReal) * (⨅ i, (c : EReal) * a i) ≤ ⨅ i, a i := by
      refine le_iInf fun i ↦ ?_
      calc ((c⁻¹ : ℝ) : EReal) * (⨅ j, (c : EReal) * a j)
          ≤ ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * a i) := by
            gcongr
            exact iInf_le (fun j ↦ (c : EReal) * a j) i
        _ = a i := by
          rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
    calc ⨅ i, (c : EReal) * a i
        = (c : EReal) * (((c⁻¹ : ℝ) : EReal) * (⨅ i, (c : EReal) * a i)) := by
          rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul]
      _ ≤ (c : EReal) * (⨅ i, a i) := by gcongr

/-! ### Affine reparametrization of subgradients -/

section Reparam

variable {f : E → EReal} {x u : E} {a b τ : ℝ}

/-- The reparametrized function `y ↦ a f(x + τy) + b + ⟪u, y⟫`. -/
noncomputable def affineReparam (f : E → EReal) (x u : E) (a b τ : ℝ) (y : E) : EReal :=
  (a : EReal) * f (x + τ • y) + ((b + ⟪u, y⟫_ℝ : ℝ) : EReal)

/-- The value of the reparametrized function as a real number. -/
theorem affineReparam_of_coe {y : E} {r : ℝ} (h : f (x + τ • y) = r) :
    affineReparam f x u a b τ y = ((a * r + b + ⟪u, y⟫_ℝ : ℝ) : EReal) := by
  rw [affineReparam, h, ← EReal.coe_mul, ← EReal.coe_add, add_assoc]

theorem affineReparam_of_top (ha : 0 < a) {y : E} (h : f (x + τ • y) = ⊤) :
    affineReparam f x u a b τ y = ⊤ := by
  rw [affineReparam, h, EReal.coe_mul_top_of_pos ha, EReal.top_add_coe]

theorem affineReparam_of_bot (ha : 0 < a) {y : E} (h : f (x + τ • y) = ⊥) :
    affineReparam f x u a b τ y = ⊥ := by
  rw [affineReparam, h, EReal.coe_mul_bot_of_pos ha, EReal.bot_add]

/-- Lower bounds transfer between `f` and its reparametrization. -/
theorem coe_le_affineReparam_iff (ha : 0 < a) {y : E} {s : ℝ} :
    (s : EReal) ≤ affineReparam f x u a b τ y ↔
      (((s - b - ⟪u, y⟫_ℝ) / a : ℝ) : EReal) ≤ f (x + τ • y) := by
  rcases ereal_trichotomy (f (x + τ • y)) with h | h | ⟨r, h⟩
  · rw [affineReparam_of_bot ha h, h]
    exact iff_of_false (fun h' ↦ EReal.coe_ne_bot _ (le_bot_iff.1 h'))
      (fun h' ↦ EReal.coe_ne_bot _ (le_bot_iff.1 h'))
  · rw [affineReparam_of_top ha h, h]
    exact iff_of_true le_top le_top
  · rw [affineReparam_of_coe h, h, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, div_le_iff₀ ha]
    constructor <;> intro h' <;> linarith

theorem affineReparam_eq_coe_iff (ha : 0 < a) {y : E} {s : ℝ} :
    affineReparam f x u a b τ y = s ↔ f (x + τ • y) = (((s - b - ⟪u, y⟫_ℝ) / a : ℝ) : EReal) := by
  rcases ereal_trichotomy (f (x + τ • y)) with h | h | ⟨r, h⟩
  · rw [affineReparam_of_bot ha h, h]
    exact iff_of_false (fun h' ↦ EReal.coe_ne_bot _ h'.symm) (fun h' ↦ EReal.coe_ne_bot _ h'.symm)
  · rw [affineReparam_of_top ha h, h]
    exact iff_of_false (fun h' ↦ EReal.coe_ne_top _ h'.symm) (fun h' ↦ EReal.coe_ne_top _ h'.symm)
  · rw [affineReparam_of_coe h, h, EReal.coe_eq_coe_iff, EReal.coe_eq_coe_iff, eq_div_iff ha.ne']
    constructor <;> intro h' <;> linarith

/-- Regular subgradients of `y ↦ a f(x + τy) + b + ⟪u, y⟫`. -/
theorem mem_regularSubdifferential_affineReparam_iff (ha : 0 < a) (hτ : 0 < τ) {w p : E} :
    p ∈ regularSubdifferential (affineReparam f x u a b τ) w ↔
      (a * τ)⁻¹ • (p - u) ∈ regularSubdifferential f (x + τ • w) := by
  have hT : Continuous fun y : E ↦ x + τ • y := by fun_prop
  have hS : Continuous fun z : E ↦ τ⁻¹ • (z - x) := by fun_prop
  have hTS : ∀ z, x + τ • (τ⁻¹ • (z - x)) = z := fun z ↦ by
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
  have hST : ∀ y, τ⁻¹ • (x + τ • y - x) = y := fun y ↦ by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
  have hdiff : ∀ z, τ⁻¹ • (z - x) - w = τ⁻¹ • (z - (x + τ • w)) := fun z ↦ by
    rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
    abel
  constructor
  · rintro ⟨c', hgw, hreg⟩
    have hfw := (affineReparam_eq_coe_iff ha).1 hgw
    refine ⟨_, hfw, fun ε hε ↦ ?_⟩
    have h1 := hreg (ε * a * τ) (by positivity)
    have h2 : Tendsto (fun z : E ↦ τ⁻¹ • (z - x)) (𝓝 (x + τ • w)) (𝓝 w) := by
      have := hS.tendsto (x + τ • w)
      rwa [hST] at this
    filter_upwards [h2.eventually h1] with z hz
    rw [coe_le_affineReparam_iff ha, hTS] at hz
    refine le_trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_)) hz
    rw [hdiff, real_inner_smul_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hτ.le),
      real_inner_smul_left, inner_sub_left]
    have hux : ⟪u, τ⁻¹ • (z - x)⟫_ℝ = ⟪u, w⟫_ℝ + τ⁻¹ * ⟪u, z - (x + τ • w)⟫_ℝ := by
      rw [← real_inner_smul_right, ← inner_add_right, ← hdiff]
      congr 1
      abel
    rw [hux]
    field_simp
    ring
  · rintro ⟨d, hfw, hreg⟩
    refine ⟨a * d + b + ⟪u, w⟫_ℝ, ?_, fun ε hε ↦ ?_⟩
    · rw [affineReparam_eq_coe_iff ha, hfw]
      congr 1
      field_simp
      ring
    have h1 := hreg (ε / (a * τ)) (by positivity)
    have h2 : Tendsto (fun y : E ↦ x + τ • y) (𝓝 w) (𝓝 (x + τ • w)) := hT.tendsto w
    filter_upwards [h2.eventually h1] with y hy
    rw [coe_le_affineReparam_iff ha]
    refine le_trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_)) hy
    have hd : x + τ • y - (x + τ • w) = τ • (y - w) := by
      rw [smul_sub]
      abel
    rw [hd, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hτ.le, real_inner_smul_left,
      inner_sub_left, inner_sub_right, inner_sub_right]
    field_simp
    ring

/-- `f(x + τy) = a⁻¹ [g(y) - b - ⟪u, y⟫]` for the reparametrization `g`, in `EReal`. -/
theorem f_eq_affineReparam (ha : 0 < a) (y : E) :
    f (x + τ • y) = ((a⁻¹ : ℝ) : EReal) *
      (affineReparam f x u a b τ y - ((b + ⟪u, y⟫_ℝ : ℝ) : EReal)) := by
  rcases ereal_trichotomy (f (x + τ • y)) with h | h | ⟨r, h⟩
  · rw [affineReparam_of_bot ha h, h, EReal.bot_sub, EReal.coe_mul_bot_of_pos (inv_pos.2 ha)]
  · rw [affineReparam_of_top ha h, h, EReal.top_sub_coe, EReal.coe_mul_top_of_pos (inv_pos.2 ha)]
  · rw [affineReparam_of_coe h, h, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_eq_coe_iff]
    field_simp
    ring

/-- Limiting subgradients of `y ↦ a f(x + τy) + b + ⟪u, y⟫`. -/
theorem mem_subdifferential_affineReparam_iff (ha : 0 < a) (hτ : 0 < τ) {w p : E} :
    p ∈ subdifferential (affineReparam f x u a b τ) w ↔
      (a * τ)⁻¹ • (p - u) ∈ subdifferential f (x + τ • w) := by
  have hT : Continuous fun y : E ↦ x + τ • y := by fun_prop
  have hS : Continuous fun z : E ↦ τ⁻¹ • (z - x) := by fun_prop
  have hTS : ∀ z, x + τ • (τ⁻¹ • (z - x)) = z := fun z ↦ by
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
  have hST : ∀ y, τ⁻¹ • (x + τ • y - x) = y := fun y ↦ by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
  have hB : Continuous fun y : E ↦ ((b + ⟪u, y⟫_ℝ : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp (continuous_const.add (continuous_const.inner continuous_id))
  have haτ : a * τ ≠ 0 := (mul_pos ha hτ).ne'
  rw [mem_subdifferential_iff_exists_seq, mem_subdifferential_iff_exists_seq]
  constructor
  · rintro ⟨⟨c', hgw⟩, ys, ps, hys, hgys, hps, hlim⟩
    have hfw := (affineReparam_eq_coe_iff ha).1 hgw
    refine ⟨⟨_, hfw⟩, fun n ↦ x + τ • ys n, fun n ↦ (a * τ)⁻¹ • (ps n - u),
      (hT.tendsto w).comp hys, ?_, fun n ↦ (mem_regularSubdifferential_affineReparam_iff ha hτ).1
        (hps n), ((hlim.sub tendsto_const_nhds).const_smul _)⟩
    -- function values converge
    have hsum : Tendsto (fun n ↦ affineReparam f x u a b τ (ys n) -
        ((b + ⟪u, ys n⟫_ℝ : ℝ) : EReal)) atTop
        (𝓝 (affineReparam f x u a b τ w - ((b + ⟪u, w⟫_ℝ : ℝ) : EReal))) := by
      rw [hgw]
      have h1 : Tendsto (fun n ↦ affineReparam f x u a b τ (ys n)) atTop (𝓝 (c' : EReal)) := by
        rw [← hgw]
        exact hgys
      have h2 : Tendsto (fun n ↦ ((-(b + ⟪u, ys n⟫_ℝ) : ℝ) : EReal)) atTop
          (𝓝 ((-(b + ⟪u, w⟫_ℝ) : ℝ) : EReal)) :=
        EReal.tendsto_coe.2 (((continuous_const.add (continuous_const.inner continuous_id)).tendsto
          w).comp hys).neg
      have := ((EReal.continuousAt_add (p := ((c' : EReal), ((-(b + ⟪u, w⟫_ℝ) : ℝ) : EReal)))
        (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))).tendsto).comp
        (h1.prodMk_nhds h2)
      simp only [sub_eq_add_neg, ← EReal.coe_neg]
      exact this
    have hmul := ((EReal.continuousAt_mul (p := (((a⁻¹ : ℝ) : EReal),
      affineReparam f x u a b τ w - ((b + ⟪u, w⟫_ℝ : ℝ) : EReal)))
      (Or.inl (show ((a⁻¹ : ℝ) : EReal) ≠ 0 by exact_mod_cast (inv_pos.2 ha).ne'))
      (Or.inl (show ((a⁻¹ : ℝ) : EReal) ≠ 0 by exact_mod_cast (inv_pos.2 ha).ne'))
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).tendsto).comp
      (tendsto_const_nhds.prodMk_nhds hsum)
    rw [f_eq_affineReparam (f := f) (x := x) (τ := τ) (u := u) (b := b) ha w]
    refine hmul.congr fun n ↦ ?_
    exact (f_eq_affineReparam (f := f) (x := x) (τ := τ) (u := u) (b := b) ha (ys n)).symm
  · rintro ⟨⟨d, hfw⟩, zs, qs, hzs, hfzs, hqs, hlim⟩
    have hgw : affineReparam f x u a b τ w = ((a * d + b + ⟪u, w⟫_ℝ : ℝ) : EReal) := by
      rw [affineReparam_eq_coe_iff ha, hfw]
      congr 1
      field_simp
      ring
    refine ⟨⟨_, hgw⟩, fun n ↦ τ⁻¹ • (zs n - x), fun n ↦ (a * τ) • qs n + u, ?_, ?_, fun n ↦ ?_, ?_⟩
    · have := (hS.tendsto (x + τ • w)).comp hzs
      rwa [hST] at this
    · have hys : Tendsto (fun n ↦ τ⁻¹ • (zs n - x)) atTop (𝓝 w) := by
        have := (hS.tendsto (x + τ • w)).comp hzs
        rwa [hST] at this
      have h1 : Tendsto (fun n ↦ f (zs n)) atTop (𝓝 (d : EReal)) := by
        rw [← hfw]
        exact hfzs
      have h2 := (hB.tendsto w).comp hys
      have hmul := ((EReal.continuousAt_mul (p := ((a : EReal), (d : EReal)))
        (Or.inl (show (a : EReal) ≠ 0 by exact_mod_cast ha.ne'))
        (Or.inl (show (a : EReal) ≠ 0 by exact_mod_cast ha.ne'))
        (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).tendsto).comp
        (tendsto_const_nhds.prodMk_nhds h1)
      have hadd := ((EReal.continuousAt_add (p := ((a : EReal) * d, ((b + ⟪u, w⟫_ℝ : ℝ) : EReal)))
        (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto).comp
        (hmul.prodMk_nhds h2)
      rw [hgw, show a * d + b + ⟪u, w⟫_ℝ = a * d + (b + ⟪u, w⟫_ℝ) by ring, EReal.coe_add,
        EReal.coe_mul]
      refine hadd.congr fun n ↦ ?_
      simp only [Function.comp_apply, affineReparam, hTS]
    · rw [mem_regularSubdifferential_affineReparam_iff ha hτ, hTS, add_sub_cancel_right, smul_smul,
        inv_mul_cancel₀ haτ, one_smul]
      exact hqs n
    · have := (hlim.const_smul (a * τ)).add_const u
      rwa [smul_smul, mul_inv_cancel₀ haτ, one_smul, sub_add_cancel] at this

end Reparam

/-! ### Lemma 13.39 -/

section Lemma1339

variable {f : E → EReal} {x v : E} {c : ℝ}

/-- The halved quotient is an affine reparametrization of `f`. -/
theorem halfSecondDifferenceQuotient_eq_affineReparam (hx : f x = c) {τ : ℝ} (hτ : 0 < τ) :
    halfSecondDifferenceQuotient f x v τ =
      affineReparam f x (-(τ⁻¹ • v)) (τ ^ 2)⁻¹ (-((τ ^ 2)⁻¹ * c)) τ := by
  funext w
  have hτ2 : (0 : ℝ) < (τ ^ 2)⁻¹ := by positivity
  rcases ereal_trichotomy (f (x + τ • w)) with h | h | ⟨r, h⟩
  · rw [affineReparam_of_bot hτ2 h, halfSecondDifferenceQuotient,
      secondDifferenceQuotient_of_bot hτ.ne' hx h, EReal.coe_mul_bot_of_pos (by norm_num)]
  · rw [affineReparam_of_top hτ2 h, halfSecondDifferenceQuotient,
      secondDifferenceQuotient_of_top hτ.ne' hx h, EReal.coe_mul_top_of_pos (by norm_num)]
  · rw [affineReparam_of_coe h, halfSecondDifferenceQuotient,
      secondDifferenceQuotient_of_coe hx h, ← EReal.coe_mul, EReal.coe_eq_coe_iff, inner_neg_left,
      real_inner_smul_left]
    field_simp
    ring

/-- **Lemma 13.39**, first formula: `∂[½Δ²_τ f(x̄ | v̄)] = [Δ_τ ∂f](x̄ | v̄)` for `τ > 0`. -/
theorem subdifferential_halfSecondDifferenceQuotient (hx : f x = c) {τ : ℝ} (hτ : 0 < τ) (w : E) :
    subdifferential (halfSecondDifferenceQuotient f x v τ) w =
      mappingDifferenceQuotient (subdifferential f) x v τ w := by
  ext p
  rw [halfSecondDifferenceQuotient_eq_affineReparam hx hτ,
    mem_subdifferential_affineReparam_iff (by positivity) hτ,
    mem_mappingDifferenceQuotient_iff hτ.ne']
  have : ((τ ^ 2)⁻¹ * τ)⁻¹ • (p - -(τ⁻¹ • v)) = v + τ • p := by
    rw [sub_neg_eq_add, smul_add, smul_smul, show ((τ ^ 2)⁻¹ * τ)⁻¹ * τ⁻¹ = 1 by field_simp,
      one_smul, show ((τ ^ 2)⁻¹ * τ)⁻¹ = τ by field_simp, add_comm]
  rw [this]

/-- In the normalized case the halved quotient is `w ↦ τ⁻² f(τw)`. -/
theorem halfSecondDifferenceQuotient_zero (hx : f 0 = 0) {τ : ℝ} (hτ : 0 < τ) (w : E) :
    halfSecondDifferenceQuotient f 0 0 τ w = (((τ ^ 2)⁻¹ : ℝ) : EReal) * f (τ • w) := by
  have := congrFun (halfSecondDifferenceQuotient_eq_affineReparam (f := f) (x := 0) (v := 0)
    (c := 0) (by rw [hx, EReal.coe_zero]) hτ) w
  rw [this, affineReparam]
  simp

/-- The proximal objective of `w ↦ τ⁻² f(τw)` is `τ⁻²` times that of `f` at the scaled points. -/
theorem proximalObjectiveEReal_halfSecond (hx : f 0 = 0) {τ lam : ℝ} (hτ : 0 < τ) (u w : E) :
    proximalObjectiveEReal (halfSecondDifferenceQuotient f 0 0 τ) lam u w =
      (((τ ^ 2)⁻¹ : ℝ) : EReal) * proximalObjectiveEReal f lam (τ • u) (τ • w) := by
  rw [proximalObjectiveEReal, proximalObjectiveEReal, halfSecondDifferenceQuotient_zero hx hτ,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 (by positivity))
      (EReal.coe_ne_top _), ← EReal.coe_mul, ← smul_sub, norm_smul, Real.norm_of_nonneg hτ.le]
  congr 2
  field_simp

theorem ereal_coe_mul_eq_iff {c : ℝ} (hc : 0 < c) {a b : EReal} :
    (c : EReal) * a = (c : EReal) * b ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  have := congrArg (fun t ↦ ((c⁻¹ : ℝ) : EReal) * t) h
  simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
    using this

theorem ereal_coe_mul_lt_top_iff {c : ℝ} (hc : 0 < c) {a : EReal} :
    (c : EReal) * a < ⊤ ↔ a < ⊤ := by
  rcases ereal_trichotomy a with h | h | ⟨r, h⟩
  · rw [h, EReal.coe_mul_bot_of_pos hc]
  · rw [h, EReal.coe_mul_top_of_pos hc]
  · rw [h, ← EReal.coe_mul]
    exact iff_of_true (EReal.coe_lt_top _) (EReal.coe_lt_top _)

omit [InnerProductSpace ℝ E] in
/-- In the normalized case `e_λ f(0) = 0`. -/
theorem moreauEnvelopeEReal_zero_of_min (hx : f 0 = 0) (hmin : ∀ z, 0 ≤ f z) {lam : ℝ}
    (hlam : 0 < lam) : moreauEnvelopeEReal f lam 0 = 0 := by
  apply le_antisymm
  · refine (iInf_le _ 0).trans ?_
    simp [hx]
  · refine le_iInf fun w ↦ ?_
    exact add_nonneg (hmin w) (EReal.coe_nonneg.2 (by positivity))

/-- **Lemma 13.39**, envelope formula: in the normalized case
`e_λ[½Δ²_τ f(0 | 0)] = [½Δ²_τ e_λ f](0 | 0)`. -/
theorem moreauEnvelopeEReal_halfSecondDifferenceQuotient (hx : f 0 = 0) (hmin : ∀ z, 0 ≤ f z)
    {τ lam : ℝ} (hτ : 0 < τ) (hlam : 0 < lam) :
    moreauEnvelopeEReal (halfSecondDifferenceQuotient f 0 0 τ) lam =
      halfSecondDifferenceQuotient (moreauEnvelopeEReal f lam) 0 0 τ := by
  funext u
  have he0 := moreauEnvelopeEReal_zero_of_min hx hmin hlam
  rw [halfSecondDifferenceQuotient_zero he0 hτ, moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal]
  simp_rw [proximalObjectiveEReal_halfSecond hx hτ u]
  rw [← ereal_coe_mul_iInf _ (by positivity), moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal]
  congr 1
  exact Function.Surjective.iInf_comp (fun z ↦ ⟨τ⁻¹ • z, by
    simp only [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]⟩) _

/-- **Lemma 13.39**, proximal formula: in the normalized case
`P_λ[½Δ²_τ f(0 | 0)] = [Δ_τ P_λ f](0 | 0)`. -/
theorem proximalMappingEReal_halfSecondDifferenceQuotient (hx : f 0 = 0) (hmin : ∀ z, 0 ≤ f z)
    {τ lam : ℝ} (hτ : 0 < τ) (hlam : 0 < lam) (u : E) :
    proximalMappingEReal (halfSecondDifferenceQuotient f 0 0 τ) lam u =
      mappingDifferenceQuotient (proximalMappingEReal f lam) 0 0 τ u := by
  have he0 := moreauEnvelopeEReal_zero_of_min hx hmin hlam
  have henv : moreauEnvelopeEReal (halfSecondDifferenceQuotient f 0 0 τ) lam u =
      (((τ ^ 2)⁻¹ : ℝ) : EReal) * moreauEnvelopeEReal f lam (τ • u) := by
    rw [moreauEnvelopeEReal_halfSecondDifferenceQuotient hx hmin hτ hlam,
      halfSecondDifferenceQuotient_zero he0 hτ]
  have hc : (0 : ℝ) < (τ ^ 2)⁻¹ := by positivity
  ext w
  rw [mem_mappingDifferenceQuotient_iff hτ.ne', zero_add, zero_add, mem_proximalMappingEReal_iff,
    mem_proximalMappingEReal_iff, proximalObjectiveEReal_halfSecond hx hτ, henv,
    ereal_coe_mul_eq_iff hc, ereal_coe_mul_lt_top_iff hc]

/-- **Lemma 13.39**, all three formulas. -/
theorem difference_quotient_relations (hx : f x = c) {τ : ℝ} (hτ : 0 < τ) :
    (∀ w, subdifferential (halfSecondDifferenceQuotient f x v τ) w =
      mappingDifferenceQuotient (subdifferential f) x v τ w) ∧
    (∀ {g : E → EReal}, g 0 = 0 → (∀ z, 0 ≤ g z) → ∀ {lam : ℝ}, 0 < lam →
      moreauEnvelopeEReal (halfSecondDifferenceQuotient g 0 0 τ) lam =
        halfSecondDifferenceQuotient (moreauEnvelopeEReal g lam) 0 0 τ ∧
      ∀ u, proximalMappingEReal (halfSecondDifferenceQuotient g 0 0 τ) lam u =
        mappingDifferenceQuotient (proximalMappingEReal g lam) 0 0 τ u) :=
  ⟨subdifferential_halfSecondDifferenceQuotient hx hτ, fun hg0 hmin _ hlam ↦
    ⟨moreauEnvelopeEReal_halfSecondDifferenceQuotient hg0 hmin hτ hlam,
      proximalMappingEReal_halfSecondDifferenceQuotient hg0 hmin hτ hlam⟩⟩

end Lemma1339

end RW
