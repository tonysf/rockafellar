/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Extended-real Moreau cancellation

This file supplies the extended-real endpoint of Corollary 3.36.  Unlike the
earlier real-valued cancellation wrapper, it neither assumes that the
functions have full domain nor that either function is coercive.
-/

import RockafellarWets.Chapter3.CoercivityCompletion
import Mathlib.Analysis.InnerProductSpace.Dual

open EReal Set Topology

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Moreau envelope with its natural extended-real codomain. -/
def moreauEnvelopeEReal (f : E → EReal) (lam : ℝ) (x : E) : EReal :=
  ⨅ w : E, f w + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)

/-- A finite point strictly below a proper closed convex extended-real
function can be strictly separated by a continuous affine minorant. -/
theorem exists_affine_minorant_gt_of_lt_of_convex_lsc_ereal
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    {x : E} {r : ℝ} (hr : (r : EReal) < f x) :
    ∃ l : E →L[ℝ] ℝ, ∃ b : ℝ,
      r < l x + b ∧ ∀ y : E, ((l y + b : ℝ) : EReal) ≤ f y := by
  let p : E × ℝ := (x, r)
  have hTne : (epigraph f).Nonempty := by
    rcases hproper.1 with ⟨y, hy⟩
    have hybot : f y ≠ ⊥ := ne_of_gt (hproper.2 y)
    refine ⟨(y, (f y).toReal), ?_⟩
    rw [mem_epigraph_iff]
    simp [EReal.coe_toReal (ne_of_lt hy) hybot]
  have hdisj : Disjoint ({p} : Set (E × ℝ)) (epigraph f) := by
    rw [Set.disjoint_singleton_left]
    intro hp
    rw [mem_epigraph_iff] at hp
    exact (not_le_of_gt hr) hp
  obtain ⟨φ, c₁, c₂, hc, hpoint, hepigraph⟩ :=
    strict_separation_of_convex_compact
      (E := E × ℝ)
      (S := ({p} : Set (E × ℝ)))
      (T := epigraph f)
      (convex_singleton p)
      (by simp)
      isCompact_singleton
      hconv hTne
      (isClosed_epigraph_of_lsc_ereal f hlsc)
      hdisj
  let l₀ : E →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let a : ℝ := φ (0, 1)
  have hφ_apply : ∀ y : E, ∀ s : ℝ, φ (y, s) = l₀ y + a * s := by
    intro y s
    have hsplit : (y, s) = (y, (0 : ℝ)) + (0, s) := by ext <;> simp
    rw [hsplit, map_add]
    have hright : φ (0, s) = a * s := by
      have hs : ((0 : E), s) = s • ((0 : E), (1 : ℝ)) := by ext <;> simp
      rw [hs, map_smul]
      simp [a, mul_comm]
    simp [l₀, hright]
  have ha : 0 ≤ a := by
    by_contra ha'
    have ha_neg : a < 0 := lt_of_not_ge ha'
    rcases hproper.1 with ⟨y, hy⟩
    have hybot : f y ≠ ⊥ := ne_of_gt (hproper.2 y)
    let fy : ℝ := (f y).toReal
    have hfy : f y = (fy : EReal) :=
      (EReal.coe_toReal (ne_of_lt hy) hybot).symm
    have hbase : c₂ < l₀ y + a * fy := by
      have := hepigraph (y, fy) (by rw [mem_epigraph_iff, hfy])
      simpa [hφ_apply] using this
    let d : ℝ := l₀ y + a * fy - c₂
    have hd : 0 < d := by simpa [d] using sub_pos.mpr hbase
    let t : ℝ := d / (-a) + 1
    have ht : 0 ≤ t := by
      have : 0 < d / (-a) := div_pos hd (neg_pos.mpr ha_neg)
      dsimp [t]
      linarith
    have hepi : (y, fy + t) ∈ epigraph f := by
      rw [mem_epigraph_iff, hfy]
      exact_mod_cast (le_add_of_nonneg_right ht)
    have hhigh := hepigraph (y, fy + t) hepi
    rw [hφ_apply] at hhigh
    have hcalc : l₀ y + a * (fy + t) = c₂ + a := by
      dsimp [t, d]
      field_simp [ne_of_lt ha_neg]
      ring
    rw [hcalc] at hhigh
    linarith
  by_cases ha0 : a = 0
  · obtain ⟨m, d, hminor⟩ :=
      exists_continuousAffineMinorant_of_convex_lsc_isProper hconv hlsc hproper
    have hpx : l₀ x < c₂ := by
      have hp := (hpoint p (by simp [p])).trans hc
      rw [hφ_apply, ha0] at hp
      simpa [p] using hp
    let gap : ℝ := c₂ - l₀ x
    have hgap : 0 < gap := sub_pos.mpr hpx
    let D : ℝ := r - (m x + d)
    let t : ℝ := (|D| + 1) / gap
    have ht : 0 < t := div_pos (by positivity) hgap
    refine ⟨m - t • l₀, d + t * c₂, ?_, ?_⟩
    · have htgap : D < t * gap := by
        have hD : D < |D| + 1 := (le_abs_self D).trans_lt (lt_add_one _)
        simpa [t, ne_of_gt hgap] using hD
      dsimp [D, gap] at htgap
      simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
      linarith
    · intro y
      by_cases hytop : f y = ⊤
      · simp [hytop]
      have hybot : f y ≠ ⊥ := ne_of_gt (hproper.2 y)
      let fy : ℝ := (f y).toReal
      have hfy : f y = (fy : EReal) :=
        (EReal.coe_toReal hytop hybot).symm
      have hepi : (y, fy) ∈ epigraph f := by rw [mem_epigraph_iff, hfy]
      have hsep := hepigraph (y, fy) hepi
      rw [hφ_apply, ha0] at hsep
      have hcorr : t * (c₂ - l₀ y) ≤ 0 := by
        have : c₂ - l₀ y ≤ 0 := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos ht.le this
      have hm := hminor y
      rw [hfy] at hm ⊢
      exact_mod_cast (show (m - t • l₀) y + (d + t * c₂) ≤ fy by
        simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
        have hmreal : m y + d ≤ fy := by exact_mod_cast hm
        linarith)
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    refine ⟨(-a⁻¹ : ℝ) • l₀, c₂ / a, ?_, ?_⟩
    · have hxr : φ (x, r) < c₂ := (hpoint p (by simp [p])).trans hc
      rw [hφ_apply] at hxr
      have hdiv : r < (c₂ - l₀ x) / a := by
        apply (lt_div_iff₀ ha_pos).2
        linarith
      convert hdiv using 1
      simp [ContinuousLinearMap.smul_apply, div_eq_mul_inv, sub_eq_add_neg]
      ring
    · intro y
      by_cases hytop : f y = ⊤
      · simp [hytop]
      have hybot : f y ≠ ⊥ := ne_of_gt (hproper.2 y)
      let fy : ℝ := (f y).toReal
      have hfy : f y = (fy : EReal) :=
        (EReal.coe_toReal hytop hybot).symm
      have hyepi : c₂ < φ (y, fy) :=
        hepigraph (y, fy) (by rw [mem_epigraph_iff, hfy])
      rw [hφ_apply] at hyepi
      rw [hfy]
      exact_mod_cast (show ((-a⁻¹ : ℝ) • l₀) y + c₂ / a ≤ fy by
        have hdiv : (c₂ - l₀ y) / a < fy :=
          (div_lt_iff₀ ha_pos).2 (by linarith)
        have hform : ((-a⁻¹ : ℝ) • l₀) y + c₂ / a =
            (c₂ - l₀ y) / a := by
          simp [ContinuousLinearMap.smul_apply, div_eq_mul_inv, sub_eq_add_neg]
          ring
        exact le_of_lt (hform.symm ▸ hdiv))

private theorem affine_add_quadratic_lower_bound
    [CompleteSpace E]
    (l : E →L[ℝ] ℝ) (b lam : ℝ) (hlam : 0 < lam) (x w : E) :
    l x + b + lam / 2 * ‖(InnerProductSpace.toDual ℝ E).symm l‖ ^ 2 ≤
      l w + b + (1 / (2 * lam)) *
        ‖w - (x + lam • (InnerProductSpace.toDual ℝ E).symm l)‖ ^ 2 := by
  let v : E := (InnerProductSpace.toDual ℝ E).symm l
  have hlv : ∀ z : E, l z = (InnerProductSpace.toDual ℝ E v) z := by
    intro z
    simp [v]
  have hid :
      l w + b + (1 / (2 * lam)) * ‖w - (x + lam • v)‖ ^ 2 =
        l x + b + lam / 2 * ‖v‖ ^ 2 +
          (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by
    rw [hlv w, hlv x]
    rw [show w - (x + lam • v) = (w - x) + (-lam) • v by module]
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    have habs : |(-lam)| = lam := by rw [abs_neg, abs_of_pos hlam]
    rw [habs]
    simp only [InnerProductSpace.toDual_apply_apply]
    rw [inner_sub_left, real_inner_comm w v, real_inner_comm x v]
    field_simp [ne_of_gt hlam]
    ring
  rw [hid]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))

/-- **Corollary 3.36 (exact extended-real form).** A proper lower-semicontinuous
convex function on a finite-dimensional real Hilbert space is determined by
one Moreau envelope with positive parameter. -/
theorem corollary336_eq_of_moreauEnvelopeEReal_eq
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁))
    (hlsc₁ : LowerSemicontinuous f₁)
    (hproper₁ : IsProper f₁)
    (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₂ : IsProper f₂)
    {lam : ℝ} (hlam : 0 < lam)
    (hEq : moreauEnvelopeEReal f₁ lam = moreauEnvelopeEReal f₂ lam) :
    f₁ = f₂ := by
  apply funext
  intro x
  apply le_antisymm
  · by_contra hle
    have hxlt : f₂ x < f₁ x := lt_of_not_ge hle
    have h₂top : f₂ x ≠ ⊤ := ne_of_lt (hxlt.trans_le le_top)
    have h₂bot : f₂ x ≠ ⊥ := ne_of_gt (hproper₂.2 x)
    let r : ℝ := (f₂ x).toReal
    have h₂x : f₂ x = (r : EReal) :=
      (EReal.coe_toReal h₂top h₂bot).symm
    obtain ⟨l, b, hr, hminor⟩ :=
      exists_affine_minorant_gt_of_lt_of_convex_lsc_ereal
        hconv₁ hlsc₁ hproper₁ (x := x) (r := r) (by simpa [← h₂x])
    let v : E := (InnerProductSpace.toDual ℝ E).symm l
    let y : E := x + lam • v
    let c : ℝ := lam / 2 * ‖v‖ ^ 2
    have hlower : ((l x + b + c : ℝ) : EReal) ≤ moreauEnvelopeEReal f₁ lam y := by
      rw [moreauEnvelopeEReal]
      refine le_iInf fun w ↦ ?_
      have hreal := affine_add_quadratic_lower_bound l b lam hlam x w
      have hcoe : ((l x + b + c : ℝ) : EReal) ≤
          ((l w + b + (1 / (2 * lam)) * ‖w - y‖ ^ 2 : ℝ) : EReal) := by
        exact_mod_cast (by simpa [c, v, y] using hreal)
      refine hcoe.trans ?_
      simpa [EReal.coe_add] using
        (add_le_add (hminor w)
          (le_refl (((1 / (2 * lam)) * ‖w - y‖ ^ 2 : ℝ) : EReal)))
    have hupper : moreauEnvelopeEReal f₂ lam y ≤ ((r + c : ℝ) : EReal) := by
      rw [moreauEnvelopeEReal]
      refine (iInf_le _ x).trans_eq ?_
      have hpen : (1 / (2 * lam)) * ‖x - y‖ ^ 2 = c := by
        simp [y, c, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        field_simp [ne_of_gt hlam]
      rw [h₂x, hpen, EReal.coe_add]
    have hchain : ((l x + b + c : ℝ) : EReal) ≤ ((r + c : ℝ) : EReal) :=
      hlower.trans ((congrFun hEq y) ▸ hupper)
    have : l x + b ≤ r := by
      have : l x + b + c ≤ r + c := by exact_mod_cast hchain
      linarith
    exact (not_le_of_gt hr) this
  · by_contra hle
    have hxlt : f₁ x < f₂ x := lt_of_not_ge hle
    have h₁top : f₁ x ≠ ⊤ := ne_of_lt (hxlt.trans_le le_top)
    have h₁bot : f₁ x ≠ ⊥ := ne_of_gt (hproper₁.2 x)
    let r : ℝ := (f₁ x).toReal
    have h₁x : f₁ x = (r : EReal) :=
      (EReal.coe_toReal h₁top h₁bot).symm
    obtain ⟨l, b, hr, hminor⟩ :=
      exists_affine_minorant_gt_of_lt_of_convex_lsc_ereal
        hconv₂ hlsc₂ hproper₂ (x := x) (r := r) (by simpa [← h₁x])
    let v : E := (InnerProductSpace.toDual ℝ E).symm l
    let y : E := x + lam • v
    let c : ℝ := lam / 2 * ‖v‖ ^ 2
    have hlower : ((l x + b + c : ℝ) : EReal) ≤ moreauEnvelopeEReal f₂ lam y := by
      rw [moreauEnvelopeEReal]
      refine le_iInf fun w ↦ ?_
      have hreal := affine_add_quadratic_lower_bound l b lam hlam x w
      have hcoe : ((l x + b + c : ℝ) : EReal) ≤
          ((l w + b + (1 / (2 * lam)) * ‖w - y‖ ^ 2 : ℝ) : EReal) := by
        exact_mod_cast (by simpa [c, v, y] using hreal)
      exact hcoe.trans (by
        simpa [EReal.coe_add] using
          (add_le_add (hminor w)
            (le_refl (((1 / (2 * lam)) * ‖w - y‖ ^ 2 : ℝ) : EReal))))
    have hupper : moreauEnvelopeEReal f₁ lam y ≤ ((r + c : ℝ) : EReal) := by
      rw [moreauEnvelopeEReal]
      refine (iInf_le _ x).trans_eq ?_
      have hpen : (1 / (2 * lam)) * ‖x - y‖ ^ 2 = c := by
        simp [y, c, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        field_simp [ne_of_gt hlam]
      rw [h₁x, hpen, EReal.coe_add]
    have hchain : ((l x + b + c : ℝ) : EReal) ≤ ((r + c : ℝ) : EReal) :=
      hlower.trans ((congrFun hEq y).symm ▸ hupper)
    have : l x + b ≤ r := by
      have : l x + b + c ≤ r + c := by exact_mod_cast hchain
      linarith
    exact (not_le_of_gt hr) this

end RW
