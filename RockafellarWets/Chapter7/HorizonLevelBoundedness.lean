/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Horizon criteria for bounded levels and minimization
-/

import RockafellarWets.Chapter3.Coercivity
import RockafellarWets.Chapter7.ConvergenceInMinimization
import RockafellarWets.Chapter7.HorizonEpiProperties

open Bornology Filter Function Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common affine norm minorant gives a homogeneous lower bound for every
outer horizon direction of the epigraphs. -/
theorem norm_le_horizon_height_of_eventual_minorant {f : ℕ → E → EReal} {γ β : ℝ}
    (hf : ∀ᶠ n in atTop, HasAffineNormLowerBound (f n) γ β) {w : E} {a : ℝ}
    (hw : (w, a) ∈ horizonOuterSetLimit (fun n ↦ epigraph (f n))) : γ * ‖w‖ ≤ a := by
  rcases mem_horizonOuterSetLimit_iff_zero_or_scaling.mp hw with h0 | ⟨φ, z, s, hφ, hz, hs, hs0, ht⟩
  · have hw0 : w = 0 := congrArg Prod.fst h0
    have ha0 : a = 0 := congrArg Prod.snd h0
    simp [hw0, ha0]
  · have hleft := (tendsto_const_nhds (x := γ)).mul (((continuous_fst.tendsto _).comp ht).norm)
    have hsum := hleft.add (hs0.mul_const β)
    have hright := (continuous_snd.tendsto _).comp ht
    suffices hi : ∀ᶠ n in atTop, γ * ‖(s n • z n).1‖ + s n * β ≤ (s n • z n).2 by
      simpa using le_of_tendsto_of_tendsto hsum hright hi
    filter_upwards [hφ.tendsto_atTop.eventually hf] with n hn
    have hb : γ * ‖(z n).1‖ + β ≤ (z n).2 :=
      EReal.coe_le_coe_iff.mp ((hn (z n).1).trans (hz n))
    change γ * ‖s n • (z n).1‖ + s n * β ≤ s n * (z n).2
    rw [norm_smul_of_nonneg (hs n).le]
    nlinarith [mul_le_mul_of_nonneg_left hb (hs n).le]

variable [FiniteDimensional ℝ E]

theorem norm_le_horizonCone_epigraph_height {g : E → EReal} {γ β : ℝ}
    (hg : HasAffineNormLowerBound g γ β) {w : E} {a : ℝ}
    (hw : (w, a) ∈ horizonCone (epigraph g)) : γ * ‖w‖ ≤ a := by
  rw [← horizonOuterSetLimit_const] at hw
  exact norm_le_horizon_height_of_eventual_minorant (Eventually.of_forall fun _ ↦ hg) hw

/-- **Theorem 7.53(d)**, a common coercive minorant makes epi-convergence
to a function with nonempty epigraph total. -/
theorem EpiConverges.total_of_equiCoercive {f : ℕ → E → EReal} {g h : E → EReal}
    (hc : EpiConverges f g) (hg : (epigraph g).Nonempty) (hh : IsCoercive h)
    (hbound : ∀ᶠ n in atTop, h ≤ f n) : TotalEpiConverges f g := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.mpr
  refine ⟨hc, ?_⟩
  rintro ⟨w, a⟩ hw
  have hle (γ : ℝ) (hγ : 0 < γ) : γ * ‖w‖ ≤ a := by
    obtain ⟨β, hβ⟩ := hh γ hγ
    exact norm_le_horizon_height_of_eventual_minorant
      (hbound.mono fun n hn x ↦ (hβ x).trans (hn x)) hw
  have hw0 : w = 0 := by
    by_contra hw'
    have hn := norm_pos_iff.mpr hw'
    have h := hle ((|a| + 1) / ‖w‖) (by positivity)
    rw [div_mul_cancel₀ _ hn.ne'] at h
    linarith [le_abs_self a]
  subst w
  have ha : 0 ≤ a := by simpa using hle 1 zero_lt_one
  rw [← epigraph_horizonFunction_eq_horizonCone_epigraph hg]
  exact (horizonFunction_le_of_mem_horizonCone_epigraph (f := g)
    (show ((0 : E), (0 : ℝ)) ∈ horizonCone (epigraph g) from zero_mem_horizonCone _)).trans
      (EReal.coe_le_coe_iff.mpr ha)

/-- **Theorem 7.54.** The strict horizontal horizon criterion yields
eventual level boundedness. No termwise properness is needed. -/
theorem isEventuallyLevelBounded_of_lowerHorizonEpiLimit_pos {f : ℕ → E → EReal}
    (hf : ∀ w : E, w ≠ 0 → 0 < lowerHorizonEpiLimit f w) : IsEventuallyLevelBounded f := by
  intro a
  apply (horizonOuterSetLimit_eq_singleton_zero_iff_eventuallyBounded _).mp
  apply Set.Subset.antisymm _ (singleton_subset_iff.mpr (isCone_horizonOuterSetLimit _).1)
  intro w hw
  by_contra h
  have hw0 : w ≠ 0 := h
  obtain h0 | ⟨φ, z, s, hφ, hz, hs, hs0, ht⟩ := mem_horizonOuterSetLimit_iff_zero_or_scaling.mp hw
  · exact hw0 h0
  have hwa : (w, (0 : ℝ)) ∈ horizonOuterSetLimit (fun n ↦ epigraph (f n)) := by
    apply mem_horizonOuterSetLimit_iff_zero_or_scaling.mpr
    refine Or.inr ⟨φ, fun n ↦ (z n, a), s, hφ, hz, hs, hs0, ?_⟩
    simpa only [Prod.smul_mk, smul_eq_mul, zero_mul] using ht.prodMk_nhds (hs0.mul_const a)
  rw [horizonOuterSetLimit_epigraph_eq_insert, mem_insert_iff] at hwa
  rcases hwa with hz | hepi
  · exact hw0 (congrArg Prod.fst hz)
  · exact (hf w hw0).not_ge (by simpa only [mem_epigraph_iff, EReal.coe_zero] using hepi)

/-- Uniformly positive affine growth of the limit controls the level sets
of a totally epi-convergent sequence. -/
theorem TotalEpiConverges.isEventuallyLevelBounded {f : ℕ → E → EReal} {g : E → EReal}
    (hc : TotalEpiConverges f g) (hg : IsProper g) (hco : IsLevelCoercive g) :
    IsEventuallyLevelBounded f := by
  obtain ⟨γ, hγ, β, hβ⟩ := hco
  apply isEventuallyLevelBounded_of_lowerHorizonEpiLimit_pos
  intro w hw
  by_contra! h
  have hw0 : (w, (0 : ℝ)) ∈ epigraph (lowerHorizonEpiLimit f) := by simpa [mem_epigraph_iff] using h
  rw [epigraph_lowerHorizonEpiLimit (hc.epiConverges.eventually_nonempty_epigraph
    (epigraph_nonempty_of_isProper hg)).frequently] at hw0
  exact (mul_pos hγ (norm_pos_iff.mpr hw)).not_ge
    (norm_le_horizonCone_epigraph_height hβ (TotalConverges.horizonOuter_subset hc hw0))

/-- **Corollary 7.55**, convergence of optimal values and outer inclusion
for minimizers at a proper, level-coercive limit. -/
theorem TotalEpiConverges.tendsto_iInf_and_outer_argmin {f : ℕ → E → EReal} {g : E → EReal}
    (hc : TotalEpiConverges f g) (hf : ∀ n, LowerSemicontinuous (f n))
    (hg : IsProper g) (hco : IsLevelCoercive g) :
    Tendsto (fun n ↦ ⨅ x, f n x) atTop (𝓝 (⨅ x, g x)) ∧
      outerSetLimit (fun n ↦ argmin (f n)) ⊆ argmin g := by
  obtain ⟨_, _, hval, _, _, hmin⟩ := convergence_in_minimization
    (hc.isEventuallyLevelBounded hg hco) hc.epiConverges hf hg
  exact ⟨hval, hmin⟩


/-- In a totally epi-convergent sequence, every positive slope strictly
below an affine minorant slope of the limit gives a common affine norm
minorant of all sufficiently late terms. -/
theorem TotalEpiConverges.eventual_affineNormLowerBound {f : ℕ → E → EReal} {g : E → EReal}
    (hc : TotalEpiConverges f g) {c γ β : ℝ} (hc0 : 0 < c) (hcγ : c < γ)
    (hg : HasAffineNormLowerBound g γ β) :
    ∃ b : ℝ, ∀ᶠ n in atTop, HasAffineNormLowerBound (f n) c b := by
  by_contra! hn
  have hbad (k : ℕ) : ∃ᶠ n in atTop, ∃ x, f n x < ((c * ‖x‖ - k : ℝ) : EReal) := by
    apply (hn (-(k : ℝ))).mono
    intro n h
    simpa only [HasAffineNormLowerBound, not_forall, not_le, sub_eq_add_neg] using h
  obtain ⟨φ, hφ, hp⟩ := extraction_forall_of_frequently hbad
  choose x hx using hp
  let z := fun n : ℕ ↦ (x n, c * ‖x n‖ - n)
  have hz (n : ℕ) : z n ∈ epigraph (f (φ n)) := (hx n).le
  have hu : ¬ IsBounded (range z) := by
    intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    obtain ⟨k, hk⟩ := exists_nat_gt ((c + 1) * R)
    have hnorm := hR (z k) (mem_range_self k)
    have h1 : ‖x k‖ ≤ R := (norm_fst_le _).trans hnorm
    have h2 := (norm_snd_le _).trans hnorm
    change ‖c * ‖x k‖ - k‖ ≤ R at h2
    rw [Real.norm_eq_abs, abs_le] at h2
    nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le]
  obtain ⟨u, ψ, hψ, hl⟩ := exists_cosmicDirection_subsequence_of_not_isBounded hu
  obtain ⟨s, hs, hs0, hsu⟩ := exists_scaling_of_tendsto_cosmicDirection hl
  have hmem : (u : E × ℝ) ∈ horizonOuterSetLimit (fun n ↦ epigraph (f n)) :=
    mem_horizonOuterSetLimit_iff_zero_or_scaling.mpr
      (Or.inr ⟨φ ∘ ψ, z ∘ ψ, s, hφ.comp hψ, fun n ↦ hz (ψ n), hs, hs0, hsu⟩)
  have huγ := norm_le_horizonCone_epigraph_height hg (TotalConverges.horizonOuter_subset hc hmem)
  have huc : (u : E × ℝ).2 ≤ c * ‖(u : E × ℝ).1‖ := by
    apply le_of_tendsto_of_tendsto' ((continuous_snd.tendsto _).comp hsu)
      ((tendsto_const_nhds (x := c)).mul (((continuous_fst.tendsto _).comp hsu).norm))
    intro n
    change s n * (c * ‖x (ψ n)‖ - ψ n) ≤ c * ‖s n • x (ψ n)‖
    rw [norm_smul_of_nonneg (hs n).le]
    nlinarith [mul_nonneg (hs n).le (Nat.cast_nonneg (ψ n) : (0 : ℝ) ≤ _)]
  have hu1 : (u : E × ℝ).1 = 0 := by
    by_contra hu'
    exact (mul_lt_mul_of_pos_right hcγ (norm_pos_iff.mpr hu')).not_ge (huγ.trans huc)
  have hu2 : (u : E × ℝ).2 = 0 := le_antisymm (by simpa [hu1] using huc) (by simpa [hu1] using huγ)
  have hzero : (u : E × ℝ) = 0 := Prod.ext hu1 hu2
  have hnorm := mem_sphere_zero_iff_norm.mp u.property
  simp [hzero] at hnorm

/-- **Corollary 7.55**, sequential openness of proper, level-coercive
functions for total epi-convergence. -/
theorem TotalEpiConverges.eventually_isProper_isLevelCoercive {f : ℕ → E → EReal} {g : E → EReal}
    (hc : TotalEpiConverges f g) (hg : IsProper g) (hco : IsLevelCoercive g) :
    ∀ᶠ n in atTop, IsProper (f n) ∧ IsLevelCoercive (f n) := by
  obtain ⟨γ, hγ, β, hβ⟩ := hco
  obtain ⟨b, hb⟩ := hc.eventual_affineNormLowerBound (half_pos hγ) (half_lt_self hγ) hβ
  filter_upwards [hb, hc.epiConverges.eventually_nonempty_epigraph (epigraph_nonempty_of_isProper hg)]
    with n hn hne
  obtain ⟨p, hp⟩ := hne
  exact ⟨⟨⟨p.1, hp.trans_lt (EReal.coe_lt_top _)⟩,
    fun x ↦ (EReal.bot_lt_coe _).trans_le (hn x)⟩, γ / 2, half_pos hγ, b, hn⟩

end RW
