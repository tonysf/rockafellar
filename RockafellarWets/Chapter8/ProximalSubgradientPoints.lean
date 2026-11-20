/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Proximal subgradients and proximal points

Proposition 8.46(f).  If `x̄ ∈ P_λ f(w)` with `λ > 0` (and `f(x̄) > -∞`),
then `v = λ⁻¹(w - x̄)` satisfies the global quadratic inequality
`f(x) ≥ f(x̄) + ⟪v, x - x̄⟫ - (1/2λ)|x - x̄|²` and is a proximal subgradient.
Conversely, when `f` is prox-bounded, every point carrying a proximal
subgradient is `λ`-proximal for some `λ > 0`: the local inequality 8(30) is
globalized with the quadratic minorant supplied by prox-boundedness, exactly
as in the book's proof.
-/

import RockafellarWets.Chapter8.ProximalSubgradients
import RockafellarWets.Chapter1.Proximal

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Proposition 8.46(f)**, the explicit formula: a point of `P_λ f(w)` where
`f` is not `-∞` carries the proximal subgradient `λ⁻¹(w - x̄)`, with the
quadratic inequality holding globally. -/
theorem global_inequality_of_mem_proximalMappingEReal {f : E → EReal} {lam : ℝ} (hlam : 0 < lam)
    {w x : E} (hx : x ∈ proximalMappingEReal f lam w) (hbot : f x ≠ ⊥) :
    ∃ c : ℝ, f x = c ∧
      (∀ y, ((c + ⟪lam⁻¹ • (w - x), y - x⟫_ℝ - 1 / (2 * lam) * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y) ∧
      lam⁻¹ • (w - x) ∈ proximalSubdifferential f x := by
  rw [mem_proximalMappingEReal_iff] at hx
  obtain ⟨heq, hlt⟩ := hx
  have hmin : ∀ y, proximalObjectiveEReal f lam w x ≤ proximalObjectiveEReal f lam w y := by
    intro y
    rw [heq]
    exact iInf_le _ y
  have hxtop : f x ≠ ⊤ := by
    intro htop
    rw [← heq, proximalObjectiveEReal, htop, EReal.top_add_coe] at hlt
    exact lt_irrefl _ hlt
  set c := (f x).toReal with hc_def
  have hxc : f x = (c : EReal) := (EReal.coe_toReal hxtop hbot).symm
  have hglob : ∀ y, ((c + ⟪lam⁻¹ • (w - x), y - x⟫_ℝ - 1 / (2 * lam) * ‖y - x‖ ^ 2 : ℝ) :
      EReal) ≤ f y := by
    intro y
    have h := hmin y
    simp only [proximalObjectiveEReal] at h
    rw [hxc] at h
    by_cases htop : f y = ⊤
    · rw [htop]
      exact le_top
    have hbot' : f y ≠ ⊥ := by
      intro hb
      rw [hb, EReal.bot_add] at h
      exact EReal.coe_ne_bot _ (le_bot_iff.1 (by exact_mod_cast h))
    have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal htop hbot').symm
    rw [hfy, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [hfy, EReal.coe_le_coe_iff]
    have hexp : ‖y - w‖ ^ 2 = ‖y - x‖ ^ 2 + 2 * ⟪y - x, x - w⟫_ℝ + ‖x - w‖ ^ 2 := by
      have : y - w = (y - x) + (x - w) := by abel
      rw [this, norm_add_sq_real]
    have hinner : ⟪lam⁻¹ • (w - x), y - x⟫_ℝ = -(lam⁻¹ * ⟪y - x, x - w⟫_ℝ) := by
      rw [real_inner_smul_left, real_inner_comm, ← neg_sub x w, inner_neg_right]
      ring
    rw [hexp] at h
    rw [hinner]
    have hl : 1 / (2 * lam) * (2 * ⟪y - x, x - w⟫_ℝ) = lam⁻¹ * ⟪y - x, x - w⟫_ℝ := by
      field_simp
    nlinarith [hl]
  refine ⟨c, hxc, hglob, c, hxc, 1 / lam, by positivity, 1, one_pos, fun y _ ↦ ?_⟩
  have h := hglob y
  have : 1 / lam / 2 = 1 / (2 * lam) := by
    field_simp
  rwa [this]

omit [InnerProductSpace ℝ E] in
/-- Prox-boundedness excludes the value `-∞`. -/
theorem ne_bot_of_isProxBounded {f : E → EReal} (hf : IsProxBounded f) (x : E) : f x ≠ ⊥ := by
  obtain ⟨lam, -, x₀, hx₀⟩ := hf
  intro hx
  have h := iInf_le (fun w : E ↦ f w + (((1 / (2 * lam)) * ‖w - x₀‖ ^ 2 : ℝ) : EReal)) x
  simp only [hx, EReal.bot_add] at h
  exact lt_irrefl _ (lt_of_lt_of_le hx₀ h)

/-- **Proposition 8.46(f)**: for a prox-bounded `f`, the points at which `f`
has a proximal subgradient are exactly the points that are `λ`-proximal for
some `λ > 0`. -/
theorem exists_mem_proximalSubdifferential_iff_exists_mem_proximalMappingEReal {f : E → EReal}
    (hf : IsProxBounded f) {x : E} :
    (∃ v, v ∈ proximalSubdifferential f x) ↔
      ∃ lam > 0, ∃ w, x ∈ proximalMappingEReal f lam w := by
  constructor
  · rintro ⟨v, c, hxc, ρ, hρ, δ, hδ, hle⟩
    obtain ⟨lam₀, hlam₀, x₀, hx₀⟩ := hf
    set e : EReal := ⨅ w : E, f w + (((1 / (2 * lam₀)) * ‖w - x₀‖ ^ 2 : ℝ) : EReal) with he_def
    have hle₀ : ∀ y, e ≤ f y + (((1 / (2 * lam₀)) * ‖y - x₀‖ ^ 2 : ℝ) : EReal) := fun y ↦
      iInf_le (fun w : E ↦ f w + (((1 / (2 * lam₀)) * ‖w - x₀‖ ^ 2 : ℝ) : EReal)) y
    have hetop : e ≠ ⊤ := by
      intro htop
      have h := hle₀ x
      rw [htop, hxc, ← EReal.coe_add] at h
      exact EReal.coe_ne_top _ (top_le_iff.1 h)
    set e₀ := e.toReal with he₀_def
    have he : e = (e₀ : EReal) := (EReal.coe_toReal hetop (ne_of_gt hx₀)).symm
    set μ : ℝ := 1 / lam₀ with hμ_def
    have hμ : 0 < μ := by positivity
    set K : ℝ := e₀ - μ * ‖x - x₀‖ ^ 2 with hK_def
    -- the quadratic minorant centred at `x`
    have hminor : ∀ y, ((K - μ * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y := by
      intro y
      have h := hle₀ y
      rw [he] at h
      by_cases htop : f y = ⊤
      · rw [htop]
        exact le_top
      have hbot : f y ≠ ⊥ := by
        intro hb
        rw [hb, EReal.bot_add] at h
        exact EReal.coe_ne_bot _ (le_bot_iff.1 h)
      have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
      rw [hfy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
      rw [hfy, EReal.coe_le_coe_iff]
      have htri : ‖y - x₀‖ ^ 2 ≤ 2 * ‖y - x‖ ^ 2 + 2 * ‖x - x₀‖ ^ 2 := by
        have h1 : ‖y - x₀‖ ≤ ‖y - x‖ + ‖x - x₀‖ := norm_sub_le_norm_sub_add_norm_sub y x x₀
        have h2 := norm_nonneg (y - x₀)
        nlinarith [sq_nonneg (‖y - x‖ - ‖x - x₀‖)]
      have h3 : 1 / (2 * lam₀) * ‖y - x₀‖ ^ 2 ≤ μ * ‖y - x‖ ^ 2 + μ * ‖x - x₀‖ ^ 2 := by
        rw [hμ_def]
        have h4 : 1 / (2 * lam₀) * ‖y - x₀‖ ^ 2 ≤ 1 / (2 * lam₀) * (2 * ‖y - x‖ ^ 2 + 2 * ‖x - x₀‖ ^ 2) :=
          mul_le_mul_of_nonneg_left htri (by positivity)
        have h5 : 1 / (2 * lam₀) * (2 * ‖y - x‖ ^ 2 + 2 * ‖x - x₀‖ ^ 2) =
            1 / lam₀ * ‖y - x‖ ^ 2 + 1 / lam₀ * ‖x - x₀‖ ^ 2 := by
          field_simp
        linarith
      linarith
    -- globalize the proximal inequality
    set A : ℝ := (‖v‖ + |K - c| / δ) / δ with hA_def
    have hA : 0 ≤ A := by positivity
    set ρ' : ℝ := max ρ (2 * (μ + A)) with hρ'_def
    have hρ' : 0 < ρ' := lt_max_of_lt_left hρ
    have hglob : ∀ y, ((c + ⟪v, y - x⟫_ℝ - ρ' / 2 * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y := by
      intro y
      have hq : 0 ≤ ‖y - x‖ ^ 2 := by positivity
      rcases le_or_gt ‖y - x‖ δ with hyδ | hyδ
      · refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hle y hyδ)
        have : ρ / 2 * ‖y - x‖ ^ 2 ≤ ρ' / 2 * ‖y - x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_left ρ (2 * (μ + A))]) hq
        linarith
      · refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hminor y)
        set r := ‖y - x‖ with hr_def
        have hr : 0 < r := lt_trans hδ hyδ
        have k0 : ⟪v, y - x⟫_ℝ ≤ ‖v‖ * r := real_inner_le_norm v (y - x)
        have k1 : (μ + A) * r ^ 2 ≤ ρ' / 2 * r ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_right ρ (2 * (μ + A))]) hq
        have k2 : (‖v‖ + |K - c| / δ) * r ≤ A * r ^ 2 := by
          rw [hA_def, div_mul_eq_mul_div, le_div_iff₀ hδ, pow_two]
          have : 0 ≤ ‖v‖ + |K - c| / δ := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hyδ.le (mul_nonneg this hr.le)]
        have k3 : |K - c| ≤ |K - c| / δ * r := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
          exact mul_le_mul_of_nonneg_left hyδ.le (abs_nonneg _)
        have k4 := neg_abs_le (K - c)
        nlinarith
    -- the proximal point
    refine ⟨ρ'⁻¹, inv_pos.2 hρ', x + ρ'⁻¹ • v, ?_⟩
    rw [mem_proximalMappingEReal_iff]
    have hcoef : 1 / (2 * ρ'⁻¹) = ρ' / 2 := by
      field_simp
    have hobj_x : proximalObjectiveEReal f ρ'⁻¹ (x + ρ'⁻¹ • v) x =
        ((c + ρ' / 2 * ‖ρ'⁻¹ • v‖ ^ 2 : ℝ) : EReal) := by
      simp only [proximalObjectiveEReal, hxc, hcoef]
      rw [← EReal.coe_add]
      congr 2
      rw [sub_add_cancel_left, norm_neg]
    have hbelow : ∀ y, proximalObjectiveEReal f ρ'⁻¹ (x + ρ'⁻¹ • v) x ≤
        proximalObjectiveEReal f ρ'⁻¹ (x + ρ'⁻¹ • v) y := by
      intro y
      rw [hobj_x]
      simp only [proximalObjectiveEReal, hcoef]
      have h := hglob y
      by_cases htop : f y = ⊤
      · rw [htop, EReal.top_add_coe]
        exact le_top
      have hbot : f y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h
      have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
      rw [hfy, EReal.coe_le_coe_iff] at h
      rw [hfy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hexp : ‖y - (x + ρ'⁻¹ • v)‖ ^ 2 =
          ‖y - x‖ ^ 2 - 2 * ρ'⁻¹ * ⟪y - x, v⟫_ℝ + ‖ρ'⁻¹ • v‖ ^ 2 := by
        have : y - (x + ρ'⁻¹ • v) = (y - x) - ρ'⁻¹ • v := by abel
        rw [this, norm_sub_sq_real, real_inner_smul_right]
        ring
      rw [hexp]
      have h' : c + ⟪y - x, v⟫_ℝ - ρ' / 2 * ‖y - x‖ ^ 2 ≤ (f y).toReal := by
        rwa [real_inner_comm] at h
      have hcancel : ρ' / 2 * (2 * ρ'⁻¹ * ⟪y - x, v⟫_ℝ) = ⟪y - x, v⟫_ℝ := by
        field_simp
      linarith [hcancel, h']
    have henv : moreauEnvelopeEReal f ρ'⁻¹ (x + ρ'⁻¹ • v) =
        proximalObjectiveEReal f ρ'⁻¹ (x + ρ'⁻¹ • v) x := by
      apply le_antisymm
      · exact iInf_le (fun y ↦ proximalObjectiveEReal f ρ'⁻¹ (x + ρ'⁻¹ • v) y) x
      · exact le_iInf hbelow
    refine ⟨henv.symm, ?_⟩
    rw [henv, hobj_x]
    exact EReal.coe_lt_top _
  · rintro ⟨lam, hlam, w, hx⟩
    obtain ⟨c, -, -, hv⟩ :=
      global_inequality_of_mem_proximalMappingEReal hlam hx (ne_bot_of_isProxBounded hf x)
    exact ⟨_, hv⟩

end RW
