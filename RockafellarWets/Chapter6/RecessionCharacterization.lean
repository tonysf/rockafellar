/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Recession Vectors from Tangents and Normals

Proposition 6.35.  A vector recedes locally at `x̄` exactly when it is tangent,
or polar to the normals, at *every* point of `C` near `x̄`.

The substance is the failure direction.  If `w` does not recede at `x̄`, a ray
from a point of `C` near `x̄` leaves `C`, and at the last point `x̃` of `C` on
that ray a whole interval `(0, δ]w` is outside `C`.  The book then projects
onto `wᗮ` with a matrix `A` and penalizes `|A(x - x̃)|²`, relying on
`A*A = A`.  Here the penalty is written as the scalar
`q(u) = ‖u - x̃‖² - ⟪w, u - x̃⟫²`, which *is* `‖P(u - x̃)‖²` for the orthogonal
projection `P` onto `wᗮ`; no projection operator has to be constructed, its
gradient comes from two ordinary product rules, and the decisive identity
`⟪∇h, w⟫ = 1` is a cancellation using `‖w‖ = 1`.
-/

import RockafellarWets.Chapter6.RecessionCones
import RockafellarWets.Chapter6.GradientNormals
import RockafellarWets.Chapter6.NormalsToTangentCones
import Mathlib.Analysis.InnerProductSpace.Calculus

open Filter Metric Set Topology
open scoped InnerProductSpace

noncomputable section

namespace RW

section PenaltyFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The objective maximized in the proof of 6.35: move along `w` while paying a
quadratic penalty for leaving the line through `c` in the direction `w`. -/
def linePenalty (c w : E) (r : ℝ) (u : E) : ℝ :=
  ⟪w, u - c⟫_ℝ - r / 2 * (‖u - c‖ ^ 2 - ⟪w, u - c⟫_ℝ ^ 2)

omit [CompleteSpace E] in
/-- The penalty is the squared distance to the line: it is the squared norm of
the component of `u - c` orthogonal to a unit vector `w`. -/
theorem norm_sub_inner_smul_sq {w : E} (hw : ‖w‖ = 1) (u : E) :
    ‖u - ⟪w, u⟫_ℝ • w‖ ^ 2 = ‖u‖ ^ 2 - ⟪w, u⟫_ℝ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hw,
    mul_one, real_inner_comm]
  rw [sq_abs]
  ring

omit [CompleteSpace E] in
/-- The penalty is nonnegative, and vanishes exactly on the line. -/
theorem linePenalty_quadratic_nonneg {w : E} (hw : ‖w‖ = 1) (u : E) :
    0 ≤ ‖u‖ ^ 2 - ⟪w, u⟫_ℝ ^ 2 := by
  rw [← norm_sub_inner_smul_sq hw u]
  positivity

omit [CompleteSpace E] in
theorem eq_inner_smul_of_quadratic_eq_zero {w : E} (hw : ‖w‖ = 1) {u : E}
    (hu : ‖u‖ ^ 2 - ⟪w, u⟫_ℝ ^ 2 = 0) : u = ⟪w, u⟫_ℝ • w := by
  have hzero : ‖u - ⟪w, u⟫_ℝ • w‖ ^ 2 = 0 := by
    rw [norm_sub_inner_smul_sq hw u]
    exact hu
  have hnorm : ‖u - ⟪w, u⟫_ℝ • w‖ = 0 := by
    have := sq_eq_zero_iff.mp hzero
    exact this
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

omit [CompleteSpace E] in
theorem continuous_linePenalty (c w : E) (r : ℝ) : Continuous (linePenalty c w r) := by
  unfold linePenalty
  fun_prop

/-- The gradient of the penalized objective: `w` minus `r` times the component
of `u - c` orthogonal to `w`. -/
theorem hasGradientAt_linePenalty (c w : E) (r : ℝ) (z : E) :
    HasGradientAt (linePenalty c w r)
      (w - r • ((z - c) - ⟪w, z - c⟫_ℝ • w)) z := by
  have hshift : HasFDerivAt (fun u : E ↦ u - c) (ContinuousLinearMap.id ℝ E) z :=
    (hasFDerivAt_id z).sub_const c
  have hlin : HasFDerivAt (fun u : E ↦ ⟪w, u - c⟫_ℝ) (innerSL ℝ w) z := by
    have hcomp := (innerSL ℝ w).hasFDerivAt.comp z hshift
    simpa using hcomp
  have hsq : HasFDerivAt (fun u : E ↦ ‖u - c‖ ^ 2)
      ((2 : ℕ) • (innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ E)) z :=
    hshift.norm_sq
  have hmul : HasFDerivAt (fun u : E ↦ ⟪w, u - c⟫_ℝ * ⟪w, u - c⟫_ℝ)
      (⟪w, z - c⟫_ℝ • innerSL ℝ w + ⟪w, z - c⟫_ℝ • innerSL ℝ w) z := hlin.mul hlin
  have hpow : HasFDerivAt (fun u : E ↦ ⟪w, u - c⟫_ℝ ^ 2)
      (⟪w, z - c⟫_ℝ • innerSL ℝ w + ⟪w, z - c⟫_ℝ • innerSL ℝ w) z := by
    refine hmul.congr_of_eventuallyEq ?_
    filter_upwards with u using sq _
  have htot := hlin.sub (((hsq.sub hpow)).const_mul (r / 2))
  rw [hasGradientAt_iff_hasFDerivAt]
  refine htot.congr_fderiv ?_
  ext u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_id', id_eq, innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply, inner_sub_left, real_inner_smul_left,
    smul_eq_mul]
  ring

omit [CompleteSpace E] in
/-- The decisive identity: the gradient pairs with `w` to `1`, because the
penalty term is orthogonal to `w`. -/
theorem inner_gradient_linePenalty {w : E} (hw : ‖w‖ = 1) (c : E) (r : ℝ) (z : E) :
    ⟪w - r • ((z - c) - ⟪w, z - c⟫_ℝ • w), w⟫_ℝ = 1 := by
  have hww : ⟪w, w⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hw]
    norm_num
  rw [inner_sub_left, real_inner_smul_left, inner_sub_left, real_inner_smul_left, hww]
  rw [real_inner_comm (z - c) w]
  ring

end PenaltyFunction

section LastPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} {x w : E}

/-- If `w` does not recede locally at `x̄` then arbitrarily near `x̄` there are
points of `C` from which a whole initial segment in the direction `w` lies
outside `C`.  Such a point is the last point of `C` on a ray that leaves it,
supplied by the supremum of the compact set of parameters that stay in `C`. -/
theorem exists_ray_outside_of_notMem_localRecessionCone (hC : IsClosed C)
    (hwnorm : ‖w‖ = 1) (hw : w ∉ localRecessionCone C x) {η : ℝ} (hη : 0 < η) :
    ∃ y ∈ C, ‖y - x‖ < η ∧ ∃ δ > 0, ∀ s ∈ Ioc (0 : ℝ) δ, y + s • w ∉ C := by
  rw [mem_localRecessionCone] at hw
  push_neg at hw
  obtain ⟨p, hpC, τ, hτ, hout⟩ :=
    hw (ball x (η / 2)) (ball_mem_nhds x (by linarith)) (η / 2) (by linarith)
  have hpmem : p ∈ C := hpC.1
  have hpball : p ∈ ball x (η / 2) := hpC.2
  set T : Set ℝ := {t | t ∈ Icc (0 : ℝ) τ ∧ p + t • w ∈ C} with hTdef
  have hTclosed : IsClosed T := by
    have hcont : Continuous fun t : ℝ ↦ p + t • w :=
      continuous_const.add (continuous_id.smul continuous_const)
    have : T = Icc (0 : ℝ) τ ∩ (fun t : ℝ ↦ p + t • w) ⁻¹' C := rfl
    rw [this]
    exact isClosed_Icc.inter (hC.preimage hcont)
  have hTcompact : IsCompact T :=
    isCompact_Icc.of_isClosed_subset hTclosed fun t ht ↦ ht.1
  have hTne : T.Nonempty := ⟨0, ⟨left_mem_Icc.2 hτ.1, by simpa using hpmem⟩⟩
  have hsup : sSup T ∈ T := hTcompact.sSup_mem hTne
  set t₀ : ℝ := sSup T with ht₀def
  have ht₀mem : t₀ ∈ Icc (0 : ℝ) τ := hsup.1
  have ht₀C : p + t₀ • w ∈ C := hsup.2
  have ht₀lt : t₀ < τ := by
    rcases lt_or_eq_of_le ht₀mem.2 with h | h
    · exact h
    · exact absurd (h ▸ ht₀C) hout
  refine ⟨p + t₀ • w, ht₀C, ?_, τ - t₀, by linarith, ?_⟩
  · have hpx : ‖p - x‖ < η / 2 := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hpball
    have hstep : ‖t₀ • w‖ ≤ η / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀mem.1, hwnorm, mul_one]
      exact le_trans ht₀mem.2 hτ.2
    have hsplit : p + t₀ • w - x = (p - x) + t₀ • w := by abel
    rw [hsplit]
    calc ‖(p - x) + t₀ • w‖ ≤ ‖p - x‖ + ‖t₀ • w‖ := norm_add_le _ _
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring
  · intro s hs hmem
    have hsum : p + t₀ • w + s • w = p + (t₀ + s) • w := by
      rw [add_smul]
      abel
    rw [hsum] at hmem
    have hin : t₀ + s ∈ T := ⟨⟨by linarith [ht₀mem.1, hs.1], by linarith [hs.2]⟩, hmem⟩
    have hle : t₀ + s ≤ t₀ := le_csSup hTcompact.bddAbove hin
    linarith [hs.1]

end LastPoint

section Construction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E} {y w : E}

omit [FiniteDimensional ℝ E] in
theorem linePenalty_self (c w : E) (r : ℝ) : linePenalty c w r c = 0 := by
  simp [linePenalty]

/-- **The construction in the proof of 6.35.**  At a point `y ∈ C` from which a
whole segment `(0, δ]w` lies outside `C`, there are points of `C` arbitrarily
close to `y` carrying a regular normal that pairs positively with `w`. -/
theorem exists_mem_regularNormalCone_inner_pos (hC : IsClosed C) (hy : y ∈ C)
    (hwnorm : ‖w‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (hout : ∀ s ∈ Ioc (0 : ℝ) δ, y + s • w ∉ C) {η : ℝ} (hη : 0 < η) :
    ∃ z ∈ C, ‖z - y‖ < η ∧ ∃ v ∈ regularNormalCone C z, 0 < ⟪v, w⟫_ℝ := by
  set β : ℝ := min (δ / 2) (η / 2) with hβdef
  have hβpos : 0 < β := lt_min (by linarith) (by linarith)
  have hβδ : β < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hβη : β < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set K : Set E := C ∩ closedBall y β with hKdef
  have hKcompact : IsCompact K := (isCompact_closedBall y β).inter_left hC
  have hKne : K.Nonempty := ⟨y, hy, mem_closedBall_self hβpos.le⟩
  obtain ⟨zs, hzsK, hzsmax⟩ : ∃ zs : ℕ → E, (∀ n : ℕ, zs n ∈ K) ∧
      ∀ n : ℕ, IsMaxOn (linePenalty y w ((n : ℝ) + 1)) K (zs n) := by
    have hstep : ∀ n : ℕ, ∃ z, z ∈ K ∧
        IsMaxOn (linePenalty y w ((n : ℝ) + 1)) K z := by
      intro n
      obtain ⟨z, hz, hmax⟩ := hKcompact.exists_isMaxOn hKne
        (continuous_linePenalty y w ((n : ℝ) + 1)).continuousOn
      exact ⟨z, hz, hmax⟩
    choose zs hzsK hzsmax using hstep
    exact ⟨zs, hzsK, hzsmax⟩
  set qval : E → ℝ := fun u ↦ ‖u - y‖ ^ 2 - ⟪w, u - y⟫_ℝ ^ 2 with hqdef
  have hqcont : Continuous qval := by
    rw [hqdef]
    fun_prop
  have hqnonneg : ∀ u, 0 ≤ qval u := fun u ↦ linePenalty_quadratic_nonneg hwnorm (u - y)
  have hrpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n ↦ by positivity
  -- the maximum value is at least the value at `y`
  have hge : ∀ n, 0 ≤ ⟪w, zs n - y⟫_ℝ - ((n : ℝ) + 1) / 2 * qval (zs n) := by
    intro n
    have hval := isMaxOn_iff.mp (hzsmax n) y ⟨hy, mem_closedBall_self hβpos.le⟩
    rw [linePenalty_self] at hval
    exact hval
  have hinner_le : ∀ n, ⟪w, zs n - y⟫_ℝ ≤ β := by
    intro n
    have hball : ‖zs n - y‖ ≤ β := by
      rw [← dist_eq_norm]
      exact mem_closedBall.1 (hzsK n).2
    calc ⟪w, zs n - y⟫_ℝ ≤ ‖w‖ * ‖zs n - y‖ := real_inner_le_norm _ _
      _ = ‖zs n - y‖ := by rw [hwnorm, one_mul]
      _ ≤ β := hball
  have hqle : ∀ n, qval (zs n) ≤ 2 * β / ((n : ℝ) + 1) := by
    intro n
    have hr := hrpos n
    have h1 : ((n : ℝ) + 1) / 2 * qval (zs n) ≤ β := by
      linarith [hge n, hinner_le n]
    rw [le_div_iff₀ hr]
    linarith
  have hqto : Tendsto (fun n ↦ qval (zs n)) atTop (nhds 0) := by
    refine squeeze_zero (fun n ↦ hqnonneg _) hqle ?_
    have hbase : Tendsto (fun n : ℕ ↦ 2 * β * (1 / ((n : ℝ) + 1))) atTop (nhds (2 * β * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    refine Tendsto.congr' ?_ (by simpa using hbase)
    filter_upwards with n
    ring
  -- a convergent subsequence of maximizers must return to `y`
  obtain ⟨zstar, hzstarK, φ, hφ, hφto⟩ := hKcompact.tendsto_subseq hzsK
  have hφat : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hqstar : qval zstar = 0 :=
    tendsto_nhds_unique ((hqcont.tendsto zstar).comp hφto) (hqto.comp hφat)
  have hline : zstar - y = ⟪w, zstar - y⟫_ℝ • w :=
    eq_inner_smul_of_quadratic_eq_zero hwnorm hqstar
  have htnonneg : 0 ≤ ⟪w, zstar - y⟫_ℝ := by
    have hcont : Continuous fun u : E ↦ ⟪w, u - y⟫_ℝ := by fun_prop
    have hto : Tendsto (fun k ↦ ⟪w, zs (φ k) - y⟫_ℝ) atTop
        (nhds ⟪w, zstar - y⟫_ℝ) := (hcont.tendsto zstar).comp hφto
    refine ge_of_tendsto' hto fun k ↦ ?_
    have hq := hqnonneg (zs (φ k))
    have hr := hrpos (φ k)
    nlinarith [hge (φ k)]
  have htle : ⟪w, zstar - y⟫_ℝ ≤ β := by
    have hball : ‖zstar - y‖ ≤ β := by
      rw [← dist_eq_norm]
      exact mem_closedBall.1 hzstarK.2
    calc ⟪w, zstar - y⟫_ℝ ≤ ‖w‖ * ‖zstar - y‖ := real_inner_le_norm _ _
      _ = ‖zstar - y‖ := by rw [hwnorm, one_mul]
      _ ≤ β := hball
  have hzstar_eq : zstar = y := by
    rcases htnonneg.eq_or_lt with hzero | hpos
    · have : zstar - y = 0 := by rw [hline, ← hzero, zero_smul]
      exact sub_eq_zero.mp this
    · exfalso
      have hmem : y + ⟪w, zstar - y⟫_ℝ • w = zstar := by
        rw [← hline]
        abel
      refine hout ⟪w, zstar - y⟫_ℝ ⟨hpos, le_of_lt (lt_of_le_of_lt htle hβδ)⟩ ?_
      rw [hmem]
      exact hzstarK.1
  -- a maximizer strictly inside the ball is a local maximizer relative to `C`
  have hzsto : Tendsto (fun k ↦ zs (φ k)) atTop (nhds y) := by
    rw [← hzstar_eq]
    exact hφto
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hzsto β hβpos
  have hk : dist (zs (φ N)) y < β := hN N le_rfl
  set k : ℕ := N with hkdef
  set z : E := zs (φ k) with hzdef
  set r : ℝ := (φ k : ℝ) + 1 with hrdef
  have hzC : z ∈ C := (hzsK (φ k)).1
  have hznear : ‖z - y‖ < β := by
    rw [← dist_eq_norm]
    exact hk
  have hlocal : IsLocalMaxOn (linePenalty y w r) C z := by
    have hzball : z ∈ ball y β := by
      rw [mem_ball, dist_eq_norm]
      exact hznear
    have hnbhd : ball y β ∈ nhds z := isOpen_ball.mem_nhds hzball
    filter_upwards [nhdsWithin_le_nhds hnbhd, self_mem_nhdsWithin] with u hu huC
    exact isMaxOn_iff.mp (hzsmax (φ k)) u ⟨huC, ball_subset_closedBall hu⟩
  refine ⟨z, hzC, lt_trans hznear hβη, w - r • ((z - y) - ⟪w, z - y⟫_ℝ • w), ?_, ?_⟩
  · exact mem_regularNormalCone_of_isLocalMaxOn_hasGradientAt hzC hlocal
      (hasGradientAt_linePenalty y w r z)
  · rw [inner_gradient_linePenalty hwnorm]
    norm_num

end Construction

section Characterization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E} {x w : E}

omit [FiniteDimensional ℝ E] in
/-- A local recession vector is a *regular* tangent vector, directly from
Definition 6.25: the constant selection `w` itself works at every nearby base
point and every small scale.  The book obtains this from the ordinary tangent
statement through 6.26. -/
theorem localRecessionCone_subset_regularTangentCone (C : Set E) (x : E) :
    localRecessionCone C x ⊆ regularTangentCone C x := by
  rintro w ⟨V₀, hV₀, ε, hε, hprop⟩
  rw [mem_regularTangentCone]
  intro V hV
  have h1 : ∀ᶠ y in nhdsWithin x C, y ∈ C ∩ V₀ :=
    Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV₀)
  have h2 : ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)), t ∈ Ioc (0 : ℝ) ε :=
    mem_of_superset (Ioo_mem_nhdsGT hε) Ioo_subset_Ioc_self
  filter_upwards [h1.prod_mk h2] with p hp
  refine ⟨w, ?_, mem_of_mem_nhds hV⟩
  rw [blowUp_eq_preimage (ne_of_gt hp.2.1)]
  exact hprop p.1 hp.1 p.2 ⟨hp.2.1.le, hp.2.2⟩

/-- **Proposition 6.35**, the failure direction for a closed set: if the
regular normals near `x̄` are all polar to `w`, then `w` recedes locally. -/
theorem mem_localRecessionCone_of_forall_inner_nonpos_of_isClosed
    (hC : IsClosed C) {V : Set E} (hV : V ∈ nhds x)
    (hcond : ∀ y ∈ C ∩ V, ∀ v ∈ regularNormalCone C y, ⟪v, w⟫_ℝ ≤ 0) :
    w ∈ localRecessionCone C x := by
  by_contra hw
  have hwne : w ≠ 0 := by
    rintro rfl
    exact hw (isCone_localRecessionCone C x).1
  set u : E := ‖w‖⁻¹ • w with hudef
  have hnpos : 0 < ‖w‖ := norm_pos_iff.2 hwne
  have hunorm : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hnpos)]
    exact inv_mul_cancel₀ hnpos.ne'
  have hune : u ∉ localRecessionCone C x := by
    intro hu
    refine hw ?_
    have hscale := (isCone_localRecessionCone C x).2 hu hnpos
    rw [hudef, smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul] at hscale
    exact hscale
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨y, hyC, hynear, δ, hδ, hout⟩ :=
    exists_ray_outside_of_notMem_localRecessionCone hC hunorm hune (by linarith : 0 < η / 2)
  obtain ⟨z, hzC, hznear, v, hv, hpos⟩ :=
    exists_mem_regularNormalCone_inner_pos hC hyC hunorm hδ hout (by linarith : 0 < η / 2)
  have hzV : z ∈ V := by
    refine hball ?_
    rw [mem_ball, dist_eq_norm]
    have hsplit : z - x = (z - y) + (y - x) := by abel
    rw [hsplit]
    calc ‖(z - y) + (y - x)‖ ≤ ‖z - y‖ + ‖y - x‖ := norm_add_le _ _
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring
  have hle := hcond z ⟨hzC, hzV⟩ v hv
  have hupos : 0 < ⟪v, u⟫_ℝ := hpos
  rw [hudef, real_inner_smul_right] at hupos
  nlinarith [inv_pos.2 hnpos]

/-- **Proposition 6.35**, the failure direction at a point of local
closedness. -/
theorem mem_localRecessionCone_of_forall_inner_nonpos
    (hlc : IsLocallyClosedAt C x) {V : Set E} (hV : V ∈ nhds x)
    (hcond : ∀ y ∈ C ∩ V, ∀ v ∈ regularNormalCone C y, ⟪v, w⟫_ℝ ≤ 0) :
    w ∈ localRecessionCone C x := by
  obtain ⟨W, hW, hWclosed, hCW⟩ := hlc
  have hxW : x ∈ interior W := mem_interior_iff_mem_nhds.2 hW
  have hVW : V ∩ interior W ∈ nhds x :=
    inter_mem hV (isOpen_interior.mem_nhds hxW)
  have hcond' : ∀ y ∈ (C ∩ W) ∩ (V ∩ interior W),
      ∀ v ∈ regularNormalCone (C ∩ W) y, ⟪v, w⟫_ℝ ≤ 0 := by
    intro y hy v hv
    have hyW : W ∈ nhds y :=
      mem_of_superset (isOpen_interior.mem_nhds hy.2.2) interior_subset
    rw [regularNormalCone_inter_nhds hyW] at hv
    exact hcond y ⟨hy.1.1, hy.2.1⟩ v hv
  have hmain := mem_localRecessionCone_of_forall_inner_nonpos_of_isClosed hCW hVW hcond'
  rwa [localRecessionCone_inter_nhds hW] at hmain

/-- **Proposition 6.35**, condition (d): `w` recedes locally at `x̄` exactly
when it is polar to the regular normals at all nearby points of `C`. -/
theorem mem_localRecessionCone_iff_forall_inner_nonpos_regularNormalCone
    (hlc : IsLocallyClosedAt C x) :
    w ∈ localRecessionCone C x ↔
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ C ∩ V, ∀ v ∈ regularNormalCone C y, ⟪v, w⟫_ℝ ≤ 0 := by
  constructor
  · intro hw
    obtain ⟨V, hVopen, hxV, hprop⟩ := exists_isOpen_forall_mem_localRecessionCone hw
    refine ⟨V, hVopen, hxV, fun y hy v hv ↦ ?_⟩
    have htan : w ∈ tangentCone C y :=
      localRecessionCone_subset_tangentCone hy.1 (hprop y hy)
    exact inner_nonpos_of_mem_regularNormalCone hv htan
  · rintro ⟨V, hVopen, hxV, hprop⟩
    exact mem_localRecessionCone_of_forall_inner_nonpos hlc (hVopen.mem_nhds hxV) hprop

/-- **Proposition 6.35**, condition (a): the ordinary tangent form. -/
theorem mem_localRecessionCone_iff_forall_mem_tangentCone
    (hlc : IsLocallyClosedAt C x) :
    w ∈ localRecessionCone C x ↔
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ C ∩ V, w ∈ tangentCone C y := by
  constructor
  · intro hw
    obtain ⟨V, hVopen, hxV, hprop⟩ := exists_isOpen_forall_mem_localRecessionCone hw
    exact ⟨V, hVopen, hxV, fun y hy ↦
      localRecessionCone_subset_tangentCone hy.1 (hprop y hy)⟩
  · rintro ⟨V, hVopen, hxV, hprop⟩
    refine mem_localRecessionCone_of_forall_inner_nonpos hlc (hVopen.mem_nhds hxV)
      fun y hy v hv ↦ ?_
    exact inner_nonpos_of_mem_regularNormalCone hv (hprop y hy)

/-- **Proposition 6.35**, condition (b): the regular tangent form. -/
theorem mem_localRecessionCone_iff_forall_mem_regularTangentCone
    (hlc : IsLocallyClosedAt C x) :
    w ∈ localRecessionCone C x ↔
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ C ∩ V, w ∈ regularTangentCone C y := by
  constructor
  · intro hw
    obtain ⟨V, hVopen, hxV, hprop⟩ := exists_isOpen_forall_mem_localRecessionCone hw
    exact ⟨V, hVopen, hxV, fun y hy ↦
      localRecessionCone_subset_regularTangentCone C y (hprop y hy)⟩
  · rintro ⟨V, hVopen, hxV, hprop⟩
    refine (mem_localRecessionCone_iff_forall_mem_tangentCone hlc).2
      ⟨V, hVopen, hxV, fun y hy ↦ ?_⟩
    exact regularTangentCone_subset_tangentCone hy.1 (hprop y hy)

/-- **Proposition 6.35**, condition (c): the limiting-normal form. -/
theorem mem_localRecessionCone_iff_forall_inner_nonpos_normalCone
    (hlc : IsLocallyClosedAt C x) :
    w ∈ localRecessionCone C x ↔
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ C ∩ V, ∀ v ∈ normalCone C y, ⟪v, w⟫_ℝ ≤ 0 := by
  obtain ⟨W, hW, hWclosed, hCW⟩ := hlc
  have hxW : x ∈ interior W := mem_interior_iff_mem_nhds.2 hW
  constructor
  · intro hw
    obtain ⟨V, hVopen, hxV, hprop⟩ := exists_isOpen_forall_mem_localRecessionCone hw
    refine ⟨V ∩ interior W, hVopen.inter isOpen_interior, ⟨hxV, hxW⟩, fun y hy v hv ↦ ?_⟩
    have hyW : W ∈ nhds y :=
      mem_of_superset (isOpen_interior.mem_nhds hy.2.2) interior_subset
    have hylc : IsLocallyClosedAt C y := ⟨W, hyW, hWclosed, hCW⟩
    have hpolar : regularTangentCone C y = polarCone (normalCone C y) :=
      regularTangentCone_eq_polarCone_normalCone hy.1 hylc
    have hmem : w ∈ regularTangentCone C y :=
      localRecessionCone_subset_regularTangentCone C y (hprop y ⟨hy.1, hy.2.1⟩)
    rw [hpolar] at hmem
    have := hmem v hv
    rwa [real_inner_comm] at this
  · rintro ⟨V, hVopen, hxV, hprop⟩
    refine (mem_localRecessionCone_iff_forall_inner_nonpos_regularNormalCone
      ⟨W, hW, hWclosed, hCW⟩).2 ⟨V, hVopen, hxV, fun y hy v hv ↦ ?_⟩
    exact hprop y hy v (regularNormalCone_subset_normalCone C y hv)

end Characterization

end RW
