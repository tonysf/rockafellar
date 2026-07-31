/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: General Level-Coercivity Consequences

This file records the nonconvex first clause of Corollary 3.27 in the
project's affine-minorant encoding of level coercivity.  No semicontinuity,
properness, convexity, or finite-dimensionality is needed: a positive-slope
affine norm minorant directly bounds every finite lower level set.
-/

import RockafellarWets.Chapter3.Coercivity

open Bornology EReal Set

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **Corollary 3.27 (general clause).** Every level-coercive function is
level-bounded.  Because `IsLevelCoercive` is defined by the equivalent
positive-slope affine-minorant condition from Theorem 3.26(a), the proof is
purely algebraic and holds without the book's otherwise ambient proper/lsc
hypotheses. -/
theorem IsLevelCoercive.isLevelBounded {f : E → EReal}
    (hf : IsLevelCoercive f) :
    IsLevelBounded f := by
  rcases hf with ⟨γ, hγ, β, hminor⟩
  intro α
  rw [isBounded_iff_forall_norm_le]
  refine ⟨(α - β) / γ, ?_⟩
  intro x hx
  have hchain :
      (((γ * ‖x‖ + β : ℝ) : EReal) ≤ (α : EReal)) :=
    (hminor x).trans (by simpa [levelSet] using hx)
  have hreal : γ * ‖x‖ + β ≤ α := by
    exact_mod_cast hchain
  apply (le_div_iff₀ hγ).2
  linarith

section Convex

variable [FiniteDimensional ℝ E] [CompleteSpace E]

/-- A proper closed convex extended-real function admits a continuous affine
minorant.  This is the separation ingredient behind the final assertion of
Corollary 3.27. -/
theorem exists_continuousAffineMinorant_of_convex_lsc_isProper
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) :
    ∃ l : E →L[ℝ] ℝ, ∃ b : ℝ,
      ∀ y : E, ((l y + b : ℝ) : EReal) ≤ f y := by
  rcases hproper.1 with ⟨x, hx_top⟩
  have hx_bot : f x ≠ ⊥ := ne_of_gt (hproper.2 x)
  let fx : ℝ := (f x).toReal
  let r : ℝ := fx - 1
  let p : E × ℝ := (x, r)
  have hfx : f x = (fx : EReal) := by
    exact (EReal.coe_toReal (ne_of_lt hx_top) hx_bot).symm
  have hr : r < fx := by
    simp [r]
  have hTne : (epigraph f).Nonempty := by
    refine ⟨(x, fx), ?_⟩
    rw [mem_epigraph_iff, hfx]
  have hdisj : Disjoint ({p} : Set (E × ℝ)) (epigraph f) := by
    rw [Set.disjoint_singleton_left]
    intro hp
    rw [mem_epigraph_iff] at hp
    have : (r : EReal) < f x := by
      rw [hfx]
      exact_mod_cast hr
    exact (not_le_of_gt this) hp
  obtain ⟨φ, c₁, c₂, hc, hpoint, hepigraph⟩ :=
    strict_separation_of_convex_compact
      (E := E × ℝ)
      (S := ({p} : Set (E × ℝ)))
      (T := epigraph f)
      (convex_singleton p)
      (by simp)
      isCompact_singleton
      hconv
      hTne
      (isClosed_epigraph_of_lsc_ereal f hlsc)
      hdisj
  let l₀ : E →L[ℝ] ℝ :=
    φ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let a : ℝ := φ (0, 1)
  have hφ_apply : ∀ y : E, ∀ s : ℝ,
      φ (y, s) = l₀ y + a * s := by
    intro y s
    have hsplit : (y, s) = (y, (0 : ℝ)) + (0, s) := by
      ext <;> simp
    rw [hsplit, map_add]
    have hright : φ (0, s) = a * s := by
      have hs : ((0 : E), s) = s • ((0 : E), (1 : ℝ)) := by
        ext <;> simp
      rw [hs, map_smul]
      simp [a, mul_comm]
    simp [l₀, hright]
  have hpoint_apply : φ (x, r) < c₁ :=
    hpoint p (by simp [p])
  have hepi_apply : c₂ < φ (x, fx) :=
    hepigraph (x, fx) (by
      rw [mem_epigraph_iff, hfx])
  have ha_pos : 0 < a := by
    rw [hφ_apply x r] at hpoint_apply
    rw [hφ_apply x fx] at hepi_apply
    have hmul : 0 < a * fx - a * r := by
      linarith
    have hfr : 0 < fx - r := sub_pos.mpr hr
    have hmul' : 0 < a * (fx - r) := by
      simpa [mul_sub] using hmul
    by_contra ha_nonpos
    have ha_le : a ≤ 0 := le_of_not_gt ha_nonpos
    have hnonpos : a * (fx - r) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha_le hfr.le
    exact not_le_of_gt hmul' hnonpos
  refine ⟨(-a⁻¹ : ℝ) • l₀, c₂ / a, ?_⟩
  intro y
  by_cases hy_top : f y = ⊤
  · simp [hy_top]
  have hy_bot : f y ≠ ⊥ := ne_of_gt (hproper.2 y)
  let fy : ℝ := (f y).toReal
  have hfy : f y = (fy : EReal) := by
    exact (EReal.coe_toReal hy_top hy_bot).symm
  have hyepi : c₂ < φ (y, fy) :=
    hepigraph (y, fy) (by
      rw [mem_epigraph_iff, hfy])
  rw [hφ_apply y fy] at hyepi
  have hlt : c₂ - l₀ y < a * fy := by
    linarith
  have hdiv : (c₂ - l₀ y) / a < fy := by
    exact (div_lt_iff₀ ha_pos).2 (by simpa [mul_comm] using hlt)
  have hform :
      (((-a⁻¹ : ℝ) • l₀) y + c₂ / a) =
        (c₂ - l₀ y) / a := by
    simp [ContinuousLinearMap.smul_apply, div_eq_mul_inv,
      sub_eq_add_neg]
    ring
  rw [hfy]
  exact_mod_cast (le_of_lt (hform ▸ hdiv))

/-- **Corollary 3.27 (no counter-coercive closed convex function).** In the
project's affine-minorant encoding, every proper lsc convex function has a
radial affine lower bound and therefore cannot be counter-coercive. -/
theorem not_isCounterCoercive_of_convex_lsc_isProper
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) :
    ¬ IsCounterCoercive f := by
  obtain ⟨l, b, hminor⟩ :=
    exists_continuousAffineMinorant_of_convex_lsc_isProper
      hconv hlsc hproper
  intro hcounter
  apply hcounter (-‖l‖)
  refine ⟨b, ?_⟩
  intro x
  have hlower : -‖l‖ * ‖x‖ ≤ l x := by
    have habs : ‖l x‖ ≤ ‖l‖ * ‖x‖ :=
      l.le_opNorm x
    have hneg : -‖l‖ * ‖x‖ ≤ -‖l x‖ := by
      linarith
    exact hneg.trans (by
      simpa [Real.norm_eq_abs] using neg_abs_le (l x))
  have hreal : -‖l‖ * ‖x‖ + b ≤ l x + b := by
    linarith
  have hcoe :
      (((-‖l‖ * ‖x‖ + b : ℝ) : EReal) ≤
        ((l x + b : ℝ) : EReal)) := by
    exact_mod_cast hreal
  exact hcoe.trans (hminor x)

end Convex

end RW
