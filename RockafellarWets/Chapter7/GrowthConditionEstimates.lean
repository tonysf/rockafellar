/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Solution estimates from a growth condition
-/

import RockafellarWets.Chapter7.SolutionStability

open Filter Function Metric Set Topology
open scoped NNReal

namespace RW

/-- The inverse used in Example 7.63, on the indicated interval. -/
noncomputable def growthSolutionRadius (ψ : ℝ → ℝ) (ε d : ℝ) : ℝ :=
  d + Function.invFunOn ψ (Icc 0 ε) (2*d)

private theorem growthValue_mem_image {ψ : ℝ → ℝ} {ε e : ℝ} (hε : 0 ≤ ε)
    (hc : ContinuousOn ψ (Icc 0 ε)) (h0 : ψ 0 = 0) (he : e ∈ Icc 0 (ψ ε)) :
    e ∈ ψ '' Icc 0 ε := by
  apply isPreconnected_Icc.intermediate_value (a := 0) (b := ε) (left_mem_Icc.mpr hε) (right_mem_Icc.mpr hε) hc
  simpa only [h0] using he

/-- The inverse-based solution radius is continuous and strictly increasing
on its domain, and it vanishes at zero. -/
theorem growthSolutionRadius_properties {ψ : ℝ → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hψ : StrictMonoOn ψ (Icc 0 ε)) (hc : ContinuousOn ψ (Icc 0 ε)) (h0 : ψ 0 = 0) :
    ContinuousOn (growthSolutionRadius ψ ε) (Icc 0 (ψ ε / 2)) ∧
      StrictMonoOn (growthSolutionRadius ψ ε) (Icc 0 (ψ ε / 2)) ∧ growthSolutionRadius ψ ε 0 = 0 := by
  let S := Icc 0 ε
  let T := Icc 0 (ψ ε)
  have hmap : MapsTo ψ S T := by
    intro x hx
    exact ⟨h0 ▸ hψ.monotoneOn (left_mem_Icc.mpr hε) hx hx.1,
      hψ.monotoneOn hx (right_mem_Icc.mpr hε) hx.2⟩
  have hsur : SurjOn ψ S T := fun _ he ↦ growthValue_mem_image hε hc h0 he
  let φ := Function.invFunOn ψ S
  have him : MapsTo φ T S := hsur.mapsTo_invFunOn
  have hright : RightInvOn φ ψ T := hsur.rightInvOn_invFunOn
  have hleft : LeftInvOn φ ψ S := hψ.injOn.leftInvOn_invFunOn
  let F : S → T := fun x ↦ ⟨ψ x, hmap x.property⟩
  have hFcont : Continuous F := (continuousOn_iff_continuous_restrict.mp hc).subtype_mk _
  have hFbij : Function.Bijective F := by
    refine ⟨fun x y h ↦ Subtype.ext (hψ.injOn x.property y.property (congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx, hxy⟩ := hsur y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  letI : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_Icc
  let H : S ≃ₜ T := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hFbij) hFcont
  have hφcont : ContinuousOn φ T := by
    rw [continuousOn_iff_continuous_restrict]
    have hcomp := continuous_subtype_val.comp H.symm.continuous
    apply hcomp.congr
    intro y
    have heq : ψ (H.symm y) = y := congrArg Subtype.val (H.apply_symm_apply y)
    exact hψ.injOn (H.symm y).property (him y.property) (heq.trans (hright y.property).symm)
  have hdouble : MapsTo (fun x : ℝ ↦ 2*x) (Icc 0 (ψ ε/2)) T := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨continuousOn_id.add (hφcont.comp (continuous_const.mul continuous_id).continuousOn hdouble),
    ?_, ?_⟩
  · intro x hx y hy hxy
    apply add_lt_add_of_lt_of_le hxy
    apply (hψ.le_iff_le (him (hdouble hx)) (him (hdouble hy))).mp
    rw [hright (hdouble hx), hright (hdouble hy)]
    linarith
  · unfold growthSolutionRadius
    rw [mul_zero, zero_add]
    simpa only [h0] using hleft (left_mem_Icc.mpr hε)

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A capped global growth bound excludes competing wells outside the
neighborhood of the solution set. This supplies the missing hypothesis
for the inverse-function estimate in Examples 7.63 and 7.65. -/
theorem growth_minimizer_estimate {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hp : IsProper f) (hq : IsProper g)
    {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) {r₀ r : ℝ≥0}
    (hA : (argmin f ∩ closedBall (0 : E) (r₀ : ℝ)).Nonempty) (hm₀ : -(r₀ : ℝ) ≤ m)
    {ψ : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hψ : StrictMonoOn ψ (Icc 0 ε))
    (hc : ContinuousOn ψ (Icc 0 ε)) (h0 : ψ 0 = 0)
    (hgrowth : ∀ y, ((m + ψ (min (infDist y (argmin f)) ε) : ℝ) : EReal) ≤ f y)
    (hclose : auxEpiDistance r f g < (r : ℝ) - r₀)
    (hgap : 2 * auxEpiDistance r f g < ψ ε) :
    let d := auxEpiDistance r f g
    let B := closedBall (0 : E) (r : ℝ)
    ∃ k : ℝ, infimumOn g B = (k : EReal) ∧ |k - m| ≤ d ∧ (argminOn g B).Nonempty ∧
      ∀ x ∈ argminOn g B, infDist x (argmin f) ≤ growthSolutionRadius ψ ε d := by
  let d := auxEpiDistance r f g
  have hd : 0 ≤ d := auxEpiDistance_nonneg hp.1 hq.1
  change 2*d < ψ ε at hgap
  have hrange := growthValue_mem_image hε.le hc h0 ⟨mul_nonneg (by norm_num) hd, hgap.le⟩
  obtain ⟨hinv, hinv_eq⟩ := Function.invFunOn_pos hrange
  obtain ⟨k, hk, hkm, hne, hall⟩ := ball_minimizer_stability_witness hf hg hp hq hm hA hm₀ hclose
  refine ⟨k, hk, hkm, hne, fun x hx ↦ ?_⟩
  obtain ⟨y, hxy, hy⟩ := hall x hx
  let A := argmin f
  have hΨ : ψ (min (infDist y A) ε) ≤ 2*d := by
    have hval := EReal.coe_le_coe_iff.mp ((hgrowth y).trans hy)
    linarith
  have hlt : infDist y A < ε := by
    by_contra! h
    rw [min_eq_right h] at hΨ
    exact hgap.not_ge hΨ
  rw [min_eq_left hlt.le] at hΨ
  have hbound := (hψ.le_iff_le ⟨infDist_nonneg, hlt.le⟩ hinv).mp (hΨ.trans hinv_eq.ge)
  calc
    infDist x A ≤ infDist y A + dist x y := infDist_le_infDist_add_dist
    _ ≤ _ := by dsimp [growthSolutionRadius]; linarith

/-- **Example 7.63**, with global capped growth about the unique minimizer. -/
theorem origin_growth_minimizer_estimate {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hp : IsProper f) (hq : IsProper g)
    (hm : (⨅ x, f x) = 0) (hA : argmin f = {0}) {r : ℝ≥0}
    {ψ : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hψ : StrictMonoOn ψ (Icc 0 ε))
    (hc : ContinuousOn ψ (Icc 0 ε)) (h0 : ψ 0 = 0)
    (hgrowth : ∀ y, (ψ (min ‖y‖ ε) : EReal) ≤ f y)
    (hclose : auxEpiDistance r f g < (r : ℝ)) (hgap : 2 * auxEpiDistance r f g < ψ ε) :
    let d := auxEpiDistance r f g
    let B := closedBall (0 : E) (r : ℝ)
    ∃ k : ℝ, infimumOn g B = (k : EReal) ∧ |k| ≤ d ∧ (argminOn g B).Nonempty ∧
      ∀ x ∈ argminOn g B, ‖x‖ ≤ growthSolutionRadius ψ ε d := by
  simpa only [hA, infDist_singleton, dist_zero_right, sub_zero] using
    growth_minimizer_estimate hf hg hp hq (m := 0) (by simpa using hm) (r₀ := 0) (r := r)
      (by simp [hA]) (by simp) hε hψ hc h0 (fun y ↦ by simpa [hA] using hgrowth y)
      (by simpa using hclose) hgap

/-- **Corollary 7.65(a)** with the cap condition needed away from the argmin. -/
theorem linear_growth_minimizer_estimate {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hp : IsProper f) (hq : IsProper g)
    {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) {r₀ r : ℝ≥0}
    (hA : (argmin f ∩ closedBall (0 : E) (r₀ : ℝ)).Nonempty) (hm₀ : -(r₀ : ℝ) ≤ m)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ)
    (hgrowth : ∀ y, ((m + γ * min (infDist y (argmin f)) ε : ℝ) : EReal) ≤ f y)
    (hclose : auxEpiDistance r f g < (r : ℝ) - r₀) (hgap : 2 * auxEpiDistance r f g < γ*ε)
    {x : E} (hx : x ∈ argminOn g (closedBall 0 (r : ℝ))) :
    infDist x (argmin f) ≤ (1 + 2/γ) * auxEpiDistance r f g := by
  let d := auxEpiDistance r f g
  have hd : 0 ≤ d := auxEpiDistance_nonneg hp.1 hq.1
  obtain ⟨_, _, _, _, hall⟩ := growth_minimizer_estimate hf hg hp hq hm hA hm₀ hε
    (ψ := fun t ↦ γ*t) (fun _ _ _ _ h ↦ mul_lt_mul_of_pos_left h hγ)
    (continuous_const.mul continuous_id).continuousOn (mul_zero _) hgrowth hclose hgap
  have hinv := Function.invFunOn_eq (f := fun t ↦ γ*t) (s := Icc 0 ε) (b := 2*d)
    (growthValue_mem_image hε.le (continuous_const.mul continuous_id).continuousOn (mul_zero _)
      ⟨mul_nonneg (by norm_num) hd, hgap.le⟩)
  have hbound := hall x hx
  change _ ≤ d + Function.invFunOn (fun t ↦ γ*t) (Icc 0 ε) (2*d) at hbound
  have hval : Function.invFunOn (fun t ↦ γ*t) (Icc 0 ε) (2*d) = 2*d/γ :=
    (eq_div_iff hγ.ne').mpr (by simpa only [mul_comm] using hinv)
  rw [hval] at hbound
  convert hbound using 1; ring

/-- **Corollary 7.65(b)** with global capped quadratic growth. -/
theorem quadratic_growth_minimizer_estimate {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hp : IsProper f) (hq : IsProper g)
    {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) {r₀ r : ℝ≥0}
    (hA : (argmin f ∩ closedBall (0 : E) (r₀ : ℝ)).Nonempty) (hm₀ : -(r₀ : ℝ) ≤ m)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ)
    (hgrowth : ∀ y, ((m + γ * (min (infDist y (argmin f)) ε)^2 : ℝ) : EReal) ≤ f y)
    (hclose : auxEpiDistance r f g < (r : ℝ) - r₀) (hgap : 2 * auxEpiDistance r f g < γ * ε^2)
    {x : E} (hx : x ∈ argminOn g (closedBall 0 (r : ℝ))) :
    infDist x (argmin f) ≤ auxEpiDistance r f g + Real.sqrt (2 * auxEpiDistance r f g / γ) := by
  let d := auxEpiDistance r f g
  have hd : 0 ≤ d := auxEpiDistance_nonneg hp.1 hq.1
  let ψ (t : ℝ) := γ*t^2
  have h0 : ψ 0 = 0 := by simp [ψ]
  have hc : ContinuousOn ψ (Icc 0 ε) := (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hmono : StrictMonoOn ψ (Icc 0 ε) := by
    intro a ha b _ hab
    exact mul_lt_mul_of_pos_left (sq_lt_sq' (by linarith [ha.1]) hab) hγ
  obtain ⟨_, _, _, _, hall⟩ := growth_minimizer_estimate hf hg hp hq hm hA hm₀ hε hmono hc h0
    hgrowth hclose hgap
  obtain ⟨hmem, hval⟩ := Function.invFunOn_pos (growthValue_mem_image hε.le hc h0
    ⟨mul_nonneg (by norm_num) hd, hgap.le⟩)
  have hsq : (Function.invFunOn ψ (Icc 0 ε) (2*d))^2 = 2*d/γ :=
    (eq_div_iff hγ.ne').mpr (by simpa [ψ, mul_comm] using hval)
  have heq := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq hmem.1] at heq
  exact (hall x hx).trans_eq (congrArg (d + ·) heq)

/-- The simplified square-root estimate under the final cutoff in 7.65(b). -/
theorem quadratic_growth_sqrt_bound {d γ : ℝ} (hd : 0 ≤ d) (hγ : 0 < γ)
    (hsmall : d ≤ 1 / (4*γ)) :
    d + Real.sqrt (2*d/γ) ≤ 2 * Real.sqrt (d/γ) := by
  let a := Real.sqrt (d/γ)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = d/γ := Real.sq_sqrt (div_nonneg hd hγ.le)
  have hsm := (le_div_iff₀ (by positivity : 0 < 4*γ)).mp hsmall
  have hprod : d^2 ≤ (a/2)^2 := by
    have h := mul_le_mul_of_nonneg_right hsm hd
    have heq := (eq_div_iff hγ.ne').mp ha2
    apply (mul_le_mul_iff_of_pos_right hγ).mp
    nlinarith
  have hda : d ≤ a/2 := by nlinarith [sq_nonneg (d + a/2)]
  have heq : Real.sqrt (2*d/γ) = Real.sqrt 2 * a := by rw [mul_div_assoc, Real.sqrt_mul (by norm_num)]
  have hroot : Real.sqrt 2 ≤ 3/2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_right hroot ha]

end RW
