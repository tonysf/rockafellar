/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Regular Tangents under a Change of Coordinates

Exercise 6.32, the regular-tangent companion of the tangent formula in 6.7.

The difference from 6.7 is that Definition 6.25 lets the *base point* move as
well as the scale, so the difference quotients compared here are
`[H(p) - H(q)]/τ` with both `p` and `q` tending to `x̄`.  That is exactly what
strict differentiability controls, and `tendsto_smul_sub_of_hasStrictFDerivAt`
isolates it once: a moving-base difference quotient converging to `w` is
carried by `∇H(x̄)` to one converging to `∇H(x̄)w`.
-/

import RockafellarWets.Chapter6.LocalSubmersion
import RockafellarWets.Chapter6.RegularTangents

open Filter Metric Set Topology

namespace RW

section MovingBase

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A difference quotient with a *moving* base point is carried by the strict
derivative.  This is the moving-base form of `image_tangentCone_subset`, and
it is where strict differentiability is genuinely needed: ordinary Frechet
differentiability controls only quotients based at `x̄` itself. -/
theorem tendsto_smul_sub_of_hasStrictFDerivAt {H : E → F} {H' : E →L[ℝ] F} {a : E}
    (hH : HasStrictFDerivAt H H' a) {τs : ℕ → ℝ} (hτpos : ∀ n, 0 < τs n)
    {ps qs : ℕ → E} (hp : Tendsto ps atTop (nhds a)) (hq : Tendsto qs atTop (nhds a))
    {w : E} (hw : Tendsto (fun n ↦ (τs n)⁻¹ • (ps n - qs n)) atTop (nhds w)) :
    Tendsto (fun n ↦ (τs n)⁻¹ • (H (ps n) - H (qs n))) atTop (nhds (H' w)) := by
  have hdecomp : ∀ n, (τs n)⁻¹ • (H (ps n) - H (qs n))
      = H' ((τs n)⁻¹ • (ps n - qs n))
        + (τs n)⁻¹ • (H (ps n) - H (qs n) - H' (ps n - qs n)) := by
    intro n
    rw [map_smul]
    module
  have hlin : Tendsto (fun n ↦ H' ((τs n)⁻¹ • (ps n - qs n))) atTop (nhds (H' w)) :=
    (H'.continuous.tendsto w).comp hw
  have hpair : Tendsto (fun n ↦ (ps n, qs n)) atTop (nhds (a, a)) := hp.prodMk_nhds hq
  have herr : Tendsto
      (fun n ↦ (τs n)⁻¹ • (H (ps n) - H (qs n) - H' (ps n - qs n))) atTop (nhds 0) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro η hη
    have hpos : (0 : ℝ) < ‖w‖ + 1 := by positivity
    have hε : (0 : ℝ) < η / (2 * (‖w‖ + 1)) := by positivity
    have hbound : ∀ᶠ n in atTop, ‖(τs n)⁻¹ • (ps n - qs n)‖ < ‖w‖ + 1 :=
      hw.norm.eventually_lt_const (lt_add_one ‖w‖)
    filter_upwards [hpair (hH.isLittleO.def hε), hbound] with n hn hb
    have hτ : (0 : ℝ) < τs n := hτpos n
    have hnorm : ‖(τs n)⁻¹ • (H (ps n) - H (qs n) - H' (ps n - qs n))‖
        = (τs n)⁻¹ * ‖H (ps n) - H (qs n) - H' (ps n - qs n)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hτ)]
    have hq' : ‖(τs n)⁻¹ • (ps n - qs n)‖ = (τs n)⁻¹ * ‖ps n - qs n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hτ)]
    rw [hnorm]
    have hstep : (τs n)⁻¹ * ‖H (ps n) - H (qs n) - H' (ps n - qs n)‖
        ≤ (τs n)⁻¹ * (η / (2 * (‖w‖ + 1)) * ‖ps n - qs n‖) :=
      mul_le_mul_of_nonneg_left hn (inv_pos.2 hτ).le
    have hstep2 : (τs n)⁻¹ * (η / (2 * (‖w‖ + 1)) * ‖ps n - qs n‖)
        = η / (2 * (‖w‖ + 1)) * ((τs n)⁻¹ * ‖ps n - qs n‖) := by ring
    rw [← hq'] at hstep2
    have hlt : η / (2 * (‖w‖ + 1)) * ‖(τs n)⁻¹ • (ps n - qs n)‖
        < η / (2 * (‖w‖ + 1)) * (‖w‖ + 1) := mul_lt_mul_of_pos_left hb hε
    have hval : η / (2 * (‖w‖ + 1)) * (‖w‖ + 1) = η / 2 := by field_simp
    linarith
  have hsum := hlin.add herr
  rw [add_zero] at hsum
  exact hsum.congr fun n ↦ (hdecomp n).symm

end MovingBase

section RegularTangentPreimage

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Exercise 6.32**, the inclusion `⊆`: the strict derivative carries regular
tangent vectors of `G⁻¹(D)` to regular tangent vectors of `D`.  The base
sequences in `D` are lifted to `C` by the local section of the submersion
theorem, and the moving-base quotient lemma transports the result. -/
theorem regularTangentCone_preimage_subset {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G') {D : Set F}
    (hx : x ∈ G ⁻¹' D) :
    regularTangentCone (G ⁻¹' D) x ⊆ (G' : E →L[ℝ] F) ⁻¹' regularTangentCone D (G x) := by
  classical
  intro w hw
  have hxD : G x ∈ D := hx
  refine mem_preimage.2 ((mem_regularTangentCone_iff_forall_sequences hxD).2 ?_)
  intro σs us hσpos hσ0 husD husto
  obtain ⟨R, s, hR, hs, hsx, hright⟩ :=
    RW.HasStrictFDerivAt.exists_local_rightInverse_of_surjective hG hsurj
  have hsto : Tendsto s (nhds (G x)) (nhds x) := by
    simpa [hsx] using hs.continuousAt.tendsto
  have hgood : ∀ᶠ n in atTop, G (s (us n)) = us n := husto hright
  have hqsC : ∀ n, (if s (us n) ∈ G ⁻¹' D then s (us n) else x) ∈ G ⁻¹' D := by
    intro n
    by_cases h : s (us n) ∈ G ⁻¹' D
    · simp [h]
    · simpa [h] using hx
  have hseq : ∀ᶠ n in atTop,
      (if s (us n) ∈ G ⁻¹' D then s (us n) else x) = s (us n) := by
    filter_upwards [hgood] with n hn
    have hmem : s (us n) ∈ G ⁻¹' D := by
      rw [mem_preimage, hn]
      exact husD n
    simp [hmem]
  have hqsto : Tendsto (fun n ↦ if s (us n) ∈ G ⁻¹' D then s (us n) else x)
      atTop (nhds x) :=
    (hsto.comp husto).congr' (hseq.mono fun n hn ↦ hn.symm)
  obtain ⟨ys, hysC, hysto, hyq⟩ :=
    (mem_regularTangentCone_iff_forall_sequences hx).1 hw σs _ hσpos hσ0 hqsC hqsto
  refine ⟨fun n ↦ G (ys n), fun n ↦ hysC n, (hG.continuousAt.tendsto).comp hysto, ?_⟩
  have hmain := tendsto_smul_sub_of_hasStrictFDerivAt hG hσpos hysto hqsto hyq
  refine hmain.congr' ?_
  filter_upwards [hseq, hgood] with n hn hn2
  rw [hn, hn2]

/-- **Exercise 6.32**, the inclusion `⊇`.  Given a base sequence `qν →_C x̄` and
scales `τν ↓ 0`, the images `G(qν)` and the scales feed the hypothesis
`∇G(x̄)w ∈ T̂_D(ū)`, producing `zν ∈ D` with `[zν - G(qν)]/τν → ∇G(x̄)w`.  The
uniform local solvability of the submersion then solves `G y = zν` starting
from `qν + τνw`, with an error controlled by
`‖zν - G(qν + τνw)‖ = o(τν)` -- which is exactly the statement that the two
difference quotients above have the same limit. -/
theorem regularTangentCone_preimage_superset {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G') {D : Set F}
    (hx : x ∈ G ⁻¹' D) :
    (G' : E →L[ℝ] F) ⁻¹' regularTangentCone D (G x) ⊆ regularTangentCone (G ⁻¹' D) x := by
  classical
  intro w hw
  have hxD : G x ∈ D := hx
  refine (mem_regularTangentCone_iff_forall_sequences hx).2 ?_
  intro τs qs hτpos hτ0 hqsC hqsto
  have husD : ∀ n, G (qs n) ∈ D := fun n ↦ hqsC n
  have husto : Tendsto (fun n ↦ G (qs n)) atTop (nhds (G x)) :=
    (hG.continuousAt.tendsto).comp hqsto
  obtain ⟨zs, hzsD, hzsto, hzq⟩ :=
    (mem_regularTangentCone_iff_forall_sequences hxD).1 hw τs (fun n ↦ G (qs n))
      hτpos hτ0 husD husto
  obtain ⟨κ, sol, hκ, hsolve⟩ :=
    RW.HasStrictFDerivAt.exists_uniform_local_solve_of_surjective hG hsurj
  have hpto : Tendsto (fun n ↦ qs n + τs n • w) atTop (nhds x) := by
    have hc : Continuous fun c : ℝ ↦ c • w := continuous_id.smul continuous_const
    have h := (hc.tendsto 0).comp hτ0
    have h0 : Tendsto (fun n ↦ τs n • w) atTop (nhds 0) := by simpa using h
    simpa using hqsto.add h0
  have hrto : Tendsto (fun n ↦ ((zs n, qs n + τs n • w) : F × E)) atTop
      (nhds ((G x, x) : F × E)) := hzsto.prodMk_nhds hpto
  have hgood := hrto hsolve
  -- the residual is `o(τν)`
  have hquot : Tendsto (fun n ↦ (τs n)⁻¹ • (zs n - G (qs n + τs n • w)))
      atTop (nhds 0) := by
    have h2 : Tendsto (fun n ↦ (τs n)⁻¹ • (G (qs n + τs n • w) - G (qs n))) atTop
        (nhds (G' w)) := by
      refine tendsto_smul_sub_of_hasStrictFDerivAt hG hτpos hpto hqsto ?_
      have hid : ∀ n, (τs n)⁻¹ • ((qs n + τs n • w) - qs n) = w := by
        intro n
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (hτpos n).ne', one_smul]
      exact tendsto_const_nhds.congr fun n ↦ (hid n).symm
    have h3 := hzq.sub h2
    rw [sub_self] at h3
    refine h3.congr fun n ↦ ?_
    rw [← smul_sub]
    congr 1
    abel
  have hnormquot : Tendsto (fun n ↦ (τs n)⁻¹ * ‖zs n - G (qs n + τs n • w)‖)
      atTop (nhds 0) := by
    have hn : ∀ n, ‖(τs n)⁻¹ • (zs n - G (qs n + τs n • w))‖
        = (τs n)⁻¹ * ‖zs n - G (qs n + τs n • w)‖ := by
      intro n
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hτpos n))]
    have h := hquot.norm
    rw [norm_zero] at h
    exact h.congr hn
  -- the corrected solution sequence
  have hyC : ∀ n, (if sol (zs n, qs n + τs n • w) ∈ G ⁻¹' D
      then sol (zs n, qs n + τs n • w) else x) ∈ G ⁻¹' D := by
    intro n
    by_cases h : sol (zs n, qs n + τs n • w) ∈ G ⁻¹' D
    · simp [h]
    · simpa [h] using hx
  have hyeq : ∀ᶠ n in atTop, (if sol (zs n, qs n + τs n • w) ∈ G ⁻¹' D
      then sol (zs n, qs n + τs n • w) else x) = sol (zs n, qs n + τs n • w) := by
    filter_upwards [hgood] with n hn
    have hmem : sol (zs n, qs n + τs n • w) ∈ G ⁻¹' D := by
      rw [mem_preimage, hn.1]
      exact hzsD n
    simp [hmem]
  -- the difference quotient of the corrected sequence tends to `w`
  have hdiff : Tendsto (fun n ↦ (τs n)⁻¹ •
      (sol (zs n, qs n + τs n • w) - (qs n + τs n • w))) atTop (nhds 0) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro η hη
    have hlim : Tendsto (fun n ↦ κ * ((τs n)⁻¹ * ‖zs n - G (qs n + τs n • w)‖))
        atTop (nhds 0) := by
      have h := Filter.Tendsto.const_mul κ hnormquot
      simpa using h
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hlim
    filter_upwards [hgood, hlim η hη] with n hn hlt
    have hτ : (0 : ℝ) < τs n := hτpos n
    have hnorm : ‖(τs n)⁻¹ • (sol (zs n, qs n + τs n • w) - (qs n + τs n • w))‖
        = (τs n)⁻¹ * ‖sol (zs n, qs n + τs n • w) - (qs n + τs n • w)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hτ)]
    have hle : (τs n)⁻¹ * ‖sol (zs n, qs n + τs n • w) - (qs n + τs n • w)‖
        ≤ (τs n)⁻¹ * (κ * ‖zs n - G (qs n + τs n • w)‖) :=
      mul_le_mul_of_nonneg_left hn.2 (inv_pos.2 hτ).le
    have hcomm : (τs n)⁻¹ * (κ * ‖zs n - G (qs n + τs n • w)‖)
        = κ * ((τs n)⁻¹ * ‖zs n - G (qs n + τs n • w)‖) := by ring
    have hpos : (0 : ℝ) ≤ κ * ((τs n)⁻¹ * ‖zs n - G (qs n + τs n • w)‖) := by
      have : (0 : ℝ) ≤ (τs n)⁻¹ * ‖zs n - G (qs n + τs n • w)‖ :=
        mul_nonneg (inv_pos.2 hτ).le (norm_nonneg _)
      positivity
    rw [hnorm]
    have habs : ‖κ * ((τs n)⁻¹ * ‖zs n - G (qs n + τs n • w)‖)‖
        = κ * ((τs n)⁻¹ * ‖zs n - G (qs n + τs n • w)‖) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    rw [habs] at hlt
    linarith
  refine ⟨fun n ↦ if sol (zs n, qs n + τs n • w) ∈ G ⁻¹' D
      then sol (zs n, qs n + τs n • w) else x, hyC, ?_, ?_⟩
  · -- the corrected sequence tends to `x`
    have hstep : Tendsto (fun n ↦ sol (zs n, qs n + τs n • w) - (qs n + τs n • w))
        atTop (nhds 0) := by
      have hc : Tendsto (fun n ↦ τs n • ((τs n)⁻¹ •
          (sol (zs n, qs n + τs n • w) - (qs n + τs n • w)))) atTop (nhds ((0 : ℝ) • (0 : E))) :=
        hτ0.smul hdiff
      rw [zero_smul] at hc
      refine hc.congr fun n ↦ ?_
      rw [smul_smul, mul_inv_cancel₀ (hτpos n).ne', one_smul]
    have hto : Tendsto (fun n ↦ sol (zs n, qs n + τs n • w)) atTop (nhds x) := by
      have h := hstep.add hpto
      simpa using h
    exact hto.congr' (hyeq.mono fun n hn ↦ hn.symm)
  · have hmain : Tendsto (fun n ↦ (τs n)⁻¹ •
        (sol (zs n, qs n + τs n • w) - qs n)) atTop (nhds w) := by
      have hsplit : ∀ n, (τs n)⁻¹ • (sol (zs n, qs n + τs n • w) - qs n)
          = (τs n)⁻¹ • (sol (zs n, qs n + τs n • w) - (qs n + τs n • w)) + w := by
        intro n
        have hne : τs n ≠ 0 := (hτpos n).ne'
        match_scalars <;> field_simp
        ring
      have h := hdiff.add (tendsto_const_nhds (x := w) (f := atTop (α := ℕ)))
      rw [zero_add] at h
      exact h.congr fun n ↦ (hsplit n).symm
    refine hmain.congr' ?_
    filter_upwards [hyeq] with n hn
    rw [hn]

/-- **Exercise 6.32**: regular tangent vectors transform under a change of
coordinates exactly as tangent vectors do in 6.7. -/
theorem regularTangentCone_preimage_of_surjective {G : E → F} {G' : E →L[ℝ] F}
    {x : E} (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G')
    {D : Set F} (hx : x ∈ G ⁻¹' D) :
    regularTangentCone (G ⁻¹' D) x
      = (G' : E →L[ℝ] F) ⁻¹' regularTangentCone D (G x) :=
  Subset.antisymm (regularTangentCone_preimage_subset hG hsurj hx)
    (regularTangentCone_preimage_superset hG hsurj hx)

end RegularTangentPreimage

end RW
