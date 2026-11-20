/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: subdifferential regularity under strict continuity

**Theorem 9.16.** For `f` finite on an open set `O`, `f` is strictly continuous
and regular on `O` if and only if for every `x ∈ O` and `w` the one-sided
directional derivative `h(x, w) = lim_{τ ↘ 0} [f(x + τw) - f(x)]/τ` exists, is
finite, and is usc in `x` for each fixed `w`
(`strictlyContinuous_regular_iff_hasOneSidedDirDeriv_usc`).  Then `f` is
semidifferentiable on `O`, `h = df = d̂f` is the limsup of difference quotients
with moving base point and the maximum of `⟪v, w⟫` over `v ∈ ∂f(x)`, `h` is usc
jointly in `(x, w)`, and `∂f` is nonempty-convex-compact-valued, osc and locally
bounded on `O` (`strictlyContinuous_regular_properties`).

Finiteness of `f` on `O` follows from either side, so it is not a hypothesis.

The book derives strict continuity in the direction (⇐) from criterion 9.13(f),
which presupposes local lower semicontinuity.  Here strict continuity is proved
directly: along each coordinate direction a Dini mean value estimate bounds the
increments of `f`, and coordinate paths give a Lipschitz bound.
-/

import RockafellarWets.Chapter9.LipschitzSubderivatives
import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion
import RockafellarWets.Chapter8.SubgradientLimits
import RockafellarWets.Chapter8.RegularSupportDuality
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter Set Topology Metric
open scoped ENNReal NNReal InnerProductSpace

namespace RW

section OneSided

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite one-sided directional derivative forces finite values along the ray. -/
theorem HasOneSidedDirDeriv.eventually_eq_coe_toReal {f : E → EReal} {p u : E} {β : ℝ}
    (h : HasOneSidedDirDeriv f p u β) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), f (p + τ • u) = ((f (p + τ • u)).toReal : EReal) := by
  have hp : f p = ((f p).toReal : EReal) := (EReal.coe_toReal h.2.1 h.1).symm
  have hev := h.2.2.eventually (Ioo_mem_nhds (EReal.coe_lt_coe_iff.2 (sub_one_lt β))
    (EReal.coe_lt_coe_iff.2 (lt_add_one β)))
  filter_upwards [hev, self_mem_nhdsWithin] with τ hτ hpos
  have hpos' : (0 : ℝ) < τ := hpos
  refine (EReal.coe_toReal ?_ ?_).symm
  · intro htop
    rw [differenceQuotient_eq_top hpos' hp htop] at hτ
    exact absurd hτ.2 (not_lt.2 le_top)
  · intro hbot
    rw [differenceQuotient_eq_bot hpos' hp hbot] at hτ
    exact absurd hτ.1 (not_lt.2 bot_le)

/-- The real difference quotients behind a finite one-sided directional derivative. -/
theorem HasOneSidedDirDeriv.tendsto_toReal_slope {f : E → EReal} {p u : E} {β : ℝ}
    (h : HasOneSidedDirDeriv f p u β) :
    Tendsto (fun τ : ℝ ↦ τ⁻¹ * ((f (p + τ • u)).toReal - (f p).toReal)) (𝓝[>] 0) (𝓝 β) := by
  have hp : f p = ((f p).toReal : EReal) := (EReal.coe_toReal h.2.1 h.1).symm
  have h1 : Tendsto (fun τ : ℝ ↦ (differenceQuotient f p τ u).toReal) (𝓝[>] 0) (𝓝 β) := by
    have h2 := (EReal.tendsto_toReal (EReal.coe_ne_top β) (EReal.coe_ne_bot β)).comp h.2.2
    simpa [Function.comp_def] using h2
  refine h1.congr' ?_
  filter_upwards [h.eventually_eq_coe_toReal] with τ hτ
  rw [differenceQuotient_eq_coe hp hτ, EReal.toReal_coe]

/-- A finite one-sided directional derivative gives continuity along the ray. -/
theorem HasOneSidedDirDeriv.tendsto_toReal {f : E → EReal} {p u : E} {β : ℝ}
    (h : HasOneSidedDirDeriv f p u β) :
    Tendsto (fun τ : ℝ ↦ (f (p + τ • u)).toReal) (𝓝[>] 0) (𝓝 (f p).toReal) := by
  have h1 : Tendsto
      (fun τ : ℝ ↦ (f p).toReal + τ * (τ⁻¹ * ((f (p + τ • u)).toReal - (f p).toReal)))
      (𝓝[>] 0) (𝓝 ((f p).toReal + 0 * β)) :=
    tendsto_const_nhds.add ((tendsto_id.mono_left nhdsWithin_le_nhds).mul h.tendsto_toReal_slope)
  rw [zero_mul, add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ' : τ ≠ 0 := ne_of_gt hτ
  rw [← mul_assoc, mul_inv_cancel₀ hτ', one_mul]
  ring

private theorem tendsto_sub_nhdsGT (t : ℝ) : Tendsto (fun z : ℝ ↦ z - t) (𝓝[>] t) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun z : ℝ ↦ z - t) (𝓝 t) (𝓝 (t - t)) :=
      (continuous_id.sub continuous_const).tendsto t
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_pos.2 (mem_Ioi.1 hz)

private theorem tendsto_rsub_nhdsLT (t : ℝ) : Tendsto (fun z : ℝ ↦ t - z) (𝓝[<] t) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun z : ℝ ↦ t - z) (𝓝 t) (𝓝 (t - t)) :=
      (continuous_const.sub continuous_id).tendsto t
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_pos.2 (mem_Iio.1 hz)

/-- Dini mean value estimate along a segment.  If at every point `y + t • u`,
`t ∈ [0, s]`, the function `f` has finite one-sided directional derivatives in the
directions `u` and `-u`, and those in direction `u` are at most `M`, then
`f(y + s u) ≤ f(y) + M s`. -/
theorem toReal_le_add_mul_of_hasOneSidedDirDeriv {f : E → EReal} {g : E → E → ℝ} {y u : E}
    {s M : ℝ} (hs : 0 ≤ s)
    (hd : ∀ t ∈ Icc (0 : ℝ) s, HasOneSidedDirDeriv f (y + t • u) u (g (y + t • u) u))
    (hd' : ∀ t ∈ Icc (0 : ℝ) s, HasOneSidedDirDeriv f (y + t • u) (-u) (g (y + t • u) (-u)))
    (hM : ∀ t ∈ Icc (0 : ℝ) s, g (y + t • u) u ≤ M) :
    (f (y + s • u)).toReal ≤ (f y).toReal + M * s := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, ∀ t, φ t = (f (y + t • u)).toReal := ⟨_, fun _ ↦ rfl⟩
  have hcont : ∀ t ∈ Icc (0 : ℝ) s, ContinuousAt φ t := by
    intro t ht
    refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
    · have h1 := (hd' t ht).tendsto_toReal.comp (tendsto_rsub_nhdsLT t)
      have h2 : ((fun τ : ℝ ↦ (f (y + t • u + τ • -u)).toReal) ∘ fun z ↦ t - z) = φ := by
        funext z
        simp only [Function.comp_apply, hφ]
        congr 2
        rw [smul_neg, sub_smul]
        abel
      rw [h2, ← hφ t] at h1
      exact h1
    · have h1 := (hd t ht).tendsto_toReal.comp (tendsto_sub_nhdsGT t)
      have h2 : ((fun τ : ℝ ↦ (f (y + t • u + τ • u)).toReal) ∘ fun z ↦ z - t) = φ := by
        funext z
        simp only [Function.comp_apply, hφ]
        congr 2
        rw [sub_smul]
        abel
      rw [h2, ← hφ t] at h1
      exact h1
  have hcontOn : ContinuousOn φ (Icc 0 s) := fun t ht ↦ (hcont t ht).continuousWithinAt
  have hB' : ∀ t ∈ Ico (0 : ℝ) s, HasDerivWithinAt (fun t ↦ φ 0 + M * t) M (Ici t) t := by
    intro t _
    have h1 := ((hasDerivAt_id t).const_mul M).const_add (φ 0)
    simp only [mul_one] at h1
    exact h1.hasDerivWithinAt
  have bound : ∀ t ∈ Ico (0 : ℝ) s, ∀ r, M < r → ∃ᶠ z in 𝓝[>] t, slope φ t z < r := by
    intro t ht r hr
    have ht' : t ∈ Icc (0 : ℝ) s := Ico_subset_Icc_self ht
    have h1 := ((hd t ht').tendsto_toReal_slope.comp (tendsto_sub_nhdsGT t)).eventually
      (gt_mem_nhds (lt_of_le_of_lt (hM t ht') hr))
    refine (h1.mono fun z hz ↦ ?_).frequently
    simp only [Function.comp_apply] at hz
    have e : y + t • u + (z - t) • u = y + z • u := by
      rw [sub_smul]
      abel
    rw [e] at hz
    rw [slope_def_field, hφ, hφ, div_eq_inv_mul]
    exact hz
  have key : φ s ≤ φ 0 + M * s :=
    image_le_of_liminf_slope_right_le_deriv_boundary hcontOn (B := fun t ↦ φ 0 + M * t)
      (B' := fun _ ↦ M) (by simp)
      ((continuous_const.add (continuous_const.mul continuous_id)).continuousOn) hB' bound
      (right_mem_Icc.2 hs)
  rw [hφ, hφ, zero_smul, add_zero] at key
  exact key

end OneSided

section Finite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- One coordinate step of the path argument: moving by `c • d`, `‖d‖ = 1`, inside a
ball where `f` has finite directional derivatives and those in the directions `±d`
are below `M`. -/
private theorem toReal_step_le {f : E → EReal} {O : Set E} {g : E → E → ℝ}
    (hg : ∀ x ∈ O, ∀ w, HasOneSidedDirDeriv f x w (g x w)) {x d : E} {ρ M : ℝ}
    (hd1 : ‖d‖ = 1) (hball : ∀ y ∈ ball x ρ, y ∈ O ∧ g y d < M ∧ g y (-d) < M) {q : E}
    {c : ℝ} (hq : ‖q - x‖ + |c| < ρ) :
    (f (q + c • d)).toReal ≤ (f q).toReal + M * |c| := by
  have hseg : ∀ u : E, ‖u‖ = 1 → ∀ t ∈ Icc (0 : ℝ) |c|, q + t • u ∈ ball x ρ := by
    intro u hu t ht
    rw [mem_ball, dist_eq_norm]
    have e : q + t • u - x = (q - x) + t • u := by abel
    calc ‖q + t • u - x‖ = ‖(q - x) + t • u‖ := by rw [e]
      _ ≤ ‖q - x‖ + ‖t • u‖ := norm_add_le _ _
      _ = ‖q - x‖ + t := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg ht.1]
      _ ≤ ‖q - x‖ + |c| := by linarith [ht.2]
      _ < ρ := hq
  rcases le_or_gt 0 c with hc | hc
  · have h1 := toReal_le_add_mul_of_hasOneSidedDirDeriv (abs_nonneg c) (y := q) (u := d)
      (g := g) (M := M)
      (fun t ht ↦ hg _ (hball _ (hseg d hd1 t ht)).1 d)
      (fun t ht ↦ hg _ (hball _ (hseg d hd1 t ht)).1 (-d))
      (fun t ht ↦ (hball _ (hseg d hd1 t ht)).2.1.le)
    rw [abs_of_nonneg hc] at h1 ⊢
    exact h1
  · have hnd : ‖-d‖ = 1 := by rw [norm_neg, hd1]
    have h1 := toReal_le_add_mul_of_hasOneSidedDirDeriv (abs_nonneg c) (y := q) (u := -d)
      (g := g) (M := M)
      (fun t ht ↦ hg _ (hball _ (hseg (-d) hnd t ht)).1 (-d))
      (fun t ht ↦ hg _ (hball _ (hseg (-d) hnd t ht)).1 (-(-d)))
      (fun t ht ↦ (hball _ (hseg (-d) hnd t ht)).2.2.le)
    rw [abs_of_neg hc, neg_smul_neg] at h1
    rw [abs_of_neg hc]
    exact h1

omit [FiniteDimensional ℝ E] in
/-- The path argument: along the coordinate path from `y` to `z` given by an
orthonormal basis, the increments of `f` add up. -/
private theorem toReal_le_of_path {ι : Type*} [Fintype ι] [DecidableEq ι] {f : E → EReal}
    {O : Set E} {g : E → E → ℝ} (hg : ∀ x ∈ O, ∀ w, HasOneSidedDirDeriv f x w (g x w))
    (b : OrthonormalBasis ι ℝ E) {x : E} {ρ M : ℝ}
    (hball : ∀ y ∈ ball x ρ, y ∈ O ∧ ∀ i, g y (b i) < M ∧ g y (-b i) < M) {y z : E}
    (hyz : ‖y - x‖ + ∑ i, |⟪b i, z - y⟫_ℝ| < ρ) :
    (f z).toReal ≤ (f y).toReal + M * ∑ i, |⟪b i, z - y⟫_ℝ| := by
  have hstep : ∀ S : Finset ι, (f (y + ∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i)).toReal ≤
      (f y).toReal + M * ∑ i ∈ S, |⟪b i, z - y⟫_ℝ| := by
    intro S
    refine Finset.induction_on S (by simp) ?_
    intro a S haS ih
    rw [Finset.sum_insert haS, Finset.sum_insert haS]
    have h1 : ‖∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i‖ ≤ ∑ i ∈ S, |⟪b i, z - y⟫_ℝ| := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
      rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]
    have h2 : ∑ i ∈ insert a S, |⟪b i, z - y⟫_ℝ| ≤ ∑ i, |⟪b i, z - y⟫_ℝ| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ abs_nonneg _
    rw [Finset.sum_insert haS] at h2
    have h0 : ‖(y + ∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i) - x‖ ≤
        ‖y - x‖ + ‖∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i‖ := by
      rw [show (y + ∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i) - x =
        (y - x) + ∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i by abel]
      exact norm_add_le _ _
    have hq : ‖(y + ∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i) - x‖ + |⟪b a, z - y⟫_ℝ| < ρ := by
      linarith
    have h3 := toReal_step_le hg (b.orthonormal.1 a)
      (fun y' hy' ↦ ⟨(hball y' hy').1, (hball y' hy').2 a⟩) hq
    have e : y + (⟪b a, z - y⟫_ℝ • b a + ∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i) =
        (y + ∑ i ∈ S, ⟪b i, z - y⟫_ℝ • b i) + ⟪b a, z - y⟫_ℝ • b a := by abel
    rw [e, mul_add]
    linarith
  have h := hstep Finset.univ
  rw [b.sum_repr'] at h
  simpa using h

/-- **Theorem 9.16**, (⇐), strict continuity: finite one-sided directional derivatives
on an open set `O`, usc in the base point for each direction, make `f` strictly
continuous on `O`. -/
theorem eRealStrictlyContinuousAt_of_hasOneSidedDirDeriv_usc {f : E → EReal} {O : Set E}
    (hO : IsOpen O) {g : E → E → ℝ} (hg : ∀ x ∈ O, ∀ w, HasOneSidedDirDeriv f x w (g x w))
    (husc : ∀ w, UpperSemicontinuousOn (fun x ↦ g x w) O) {x : E} (hx : x ∈ O) :
    ERealStrictlyContinuousAt f x := by
  classical
  let b := stdOrthonormalBasis ℝ E
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + ∑ i, (|g x (b i)| + |g x (-b i)|) := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ i, (|g x (b i)| + |g x (-b i)|) :=
      Finset.sum_nonneg fun i _ ↦ by positivity
    linarith
  have hgM : ∀ i, g x (b i) < M ∧ g x (-b i) < M := by
    intro i
    have hle : |g x (b i)| + |g x (-b i)| ≤ ∑ j, (|g x (b j)| + |g x (-b j)|) :=
      Finset.single_le_sum (f := fun j ↦ |g x (b j)| + |g x (-b j)|)
        (fun j _ ↦ by positivity) (Finset.mem_univ i)
    constructor <;> linarith [le_abs_self (g x (b i)), le_abs_self (g x (-b i)),
      abs_nonneg (g x (b i)), abs_nonneg (g x (-b i))]
  have hOx : O ∈ 𝓝 x := hO.mem_nhds hx
  have hev : ∀ᶠ y in 𝓝 x, y ∈ O ∧ ∀ i, g y (b i) < M ∧ g y (-b i) < M := by
    refine Filter.eventually_and.2 ⟨hOx, Filter.eventually_all.2 fun i ↦ ?_⟩
    have h1 := husc (b i) x hx M (hgM i).1
    have h2 := husc (-b i) x hx M (hgM i).2
    rw [nhdsWithin_eq_nhds.2 hOx] at h1 h2
    exact h1.and h2
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.1 hev
  have hn0 : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < 1 + 2 * Module.finrank ℝ E := by positivity
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ρ / (1 + 2 * Module.finrank ℝ E) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  have hrmul : r * (1 + 2 * Module.finrank ℝ E) = ρ := by
    rw [hr_def]
    exact div_mul_cancel₀ ρ hpos.ne'
  have hsum : ∀ y z : E, ∑ i, |⟪b i, z - y⟫_ℝ| ≤ Module.finrank ℝ E * ‖z - y‖ := by
    intro y z
    calc ∑ i, |⟪b i, z - y⟫_ℝ| ≤ ∑ _i : Fin (Module.finrank ℝ E), ‖z - y‖ :=
          Finset.sum_le_sum fun i _ ↦ (abs_real_inner_le_norm _ _).trans
            (le_of_eq (by rw [b.orthonormal.1 i, one_mul]))
      _ = Module.finrank ℝ E * ‖z - y‖ := by simp
  have hbound : ∀ y ∈ ball x r, ∀ z ∈ ball x r,
      (f z).toReal ≤ (f y).toReal + M * Module.finrank ℝ E * ‖z - y‖ := by
    intro y hy z hz
    have hyx : ‖y - x‖ < r := by rw [← dist_eq_norm]; exact hy
    have hzy : ‖z - y‖ < 2 * r := by
      have h1 : dist z y ≤ dist z x + dist y x := dist_triangle_right z y x
      rw [dist_eq_norm] at h1
      have h2 : dist z x < r := hz
      have h3 : dist y x < r := hy
      linarith
    have h3 : (Module.finrank ℝ E : ℝ) * ‖z - y‖ ≤ Module.finrank ℝ E * (2 * r) :=
      mul_le_mul_of_nonneg_left hzy.le hn0
    have h4 : r + Module.finrank ℝ E * (2 * r) = ρ := by rw [← hrmul]; ring
    have hpath := toReal_le_of_path hg b
      (fun y' hy' ↦ hρsub hy') (y := y) (z := z) (by linarith [hsum y z])
    have h5 : M * ∑ i, |⟪b i, z - y⟫_ℝ| ≤ M * Module.finrank ℝ E * ‖z - y‖ := by
      calc M * ∑ i, |⟪b i, z - y⟫_ℝ| ≤ M * (Module.finrank ℝ E * ‖z - y‖) :=
            mul_le_mul_of_nonneg_left (hsum y z) (by linarith)
        _ = M * Module.finrank ℝ E * ‖z - y‖ := by ring
    linarith
  have hfin : ∀ y ∈ O, f y = ((f y).toReal : EReal) := fun y hy ↦
    (EReal.coe_toReal (hg y hy 0).2.1 (hg y hy 0).1).symm
  have hK : (0 : ℝ) ≤ M * Module.finrank ℝ E := mul_nonneg (by linarith) hn0
  refine ⟨Filter.mem_of_superset hOx fun y hy ↦ hfin y hy, strictlyContinuousAt_iff.2
    ⟨⟨M * Module.finrank ℝ E, hK⟩, ball x r, ball_mem_nhds x hr,
      LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_⟩⟩
  rw [Real.dist_eq, abs_le, NNReal.coe_mk, dist_eq_norm]
  have h1 := hbound y hy z hz
  have h2 := hbound z hz y hy
  rw [norm_sub_rev] at h1
  constructor <;> linarith

/-- **Theorem 9.16**, (⇐), regularity. -/
theorem isSubdifferentiallyRegularAt_of_hasOneSidedDirDeriv_usc {f : E → EReal} {O : Set E}
    (hO : IsOpen O) {g : E → E → ℝ} (hg : ∀ x ∈ O, ∀ w, HasOneSidedDirDeriv f x w (g x w))
    (husc : ∀ w, UpperSemicontinuousOn (fun x ↦ g x w) O) {x : E} (hx : x ∈ O) :
    IsSubdifferentiallyRegularAt f x := by
  have hsc : ∀ y ∈ O, ERealStrictlyContinuousAt f y := fun y hy ↦
    eRealStrictlyContinuousAt_of_hasOneSidedDirDeriv_usc hO hg husc hy
  have hdf : ∀ y ∈ O, ∀ w, subderivative f y w = (g y w : EReal) := fun y hy w ↦ by
    rw [(hsc y hy).subderivative_eq_liminf w]
    exact (hg y hy w).2.2.liminf_eq
  rw [isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative]
  refine ⟨(hsc x hx).isLocallyLscAt, funext fun w ↦ le_antisymm ?_ ?_⟩
  · exact subderivative_le_regularSubderivative (hsc x hx).finite w
  · rw [(hsc x hx).regularSubderivative_eq_limsup_subderivative w, hdf x hx w]
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨a, ha1, ha2⟩ := EReal.exists_between_coe_real hlt
    have hev := husc w x hx a (EReal.coe_lt_coe_iff.1 ha1)
    rw [nhdsWithin_eq_nhds.2 (hO.mem_nhds hx)] at hev
    have hle : limsup (fun y ↦ subderivative f y w) (𝓝 x) ≤ (a : EReal) := by
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hev, hO.mem_nhds hx] with y hy hyO
      rw [hdf y hyO w]
      exact EReal.coe_le_coe_iff.2 hy.le
    exact absurd (lt_of_lt_of_le ha2 hle) (lt_irrefl _)

/-- **Theorem 9.16**: at a point of strict continuity and regularity, `f` is
semidifferentiable, its semiderivative being `df(x)(w)`. -/
theorem hasSemiderivative_of_strictlyContinuous_regular {f : E → EReal} {x : E}
    (hsc : ERealStrictlyContinuousAt f x) (hreg : IsSubdifferentiallyRegularAt f x) (w : E) :
    HasSemiderivative f x w (subderivative f x w) := by
  have heq := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.1 hreg).2
  have hmap : Tendsto (fun p : ℝ × E ↦ ((x, p.1), p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      ((attentiveNhds f x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w) :=
    ((tendsto_const_pure.mono_right (pure_le_attentiveNhds f x)).prodMk tendsto_fst).prodMk
      tendsto_snd
  have hup : upperSemiderivative f x w ≤ subderivative f x w := by
    rw [congrFun heq w, hsc.regularSubderivative_eq_upperDirectionalSlope w, upperDirectionalSlope,
      upperSemiderivative]
    have h1 : (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) =
        (fun q : (E × ℝ) × E ↦ differenceQuotient f q.1.1 q.1.2 q.2) ∘
          fun p : ℝ × E ↦ ((x, p.1), p.2) := rfl
    rw [h1, limsup_comp]
    exact limsup_le_limsup_of_le hmap
  have hsd := (semidifferentiableFor_iff_subderivative_eq_limsup hsc.isLocallyLscAt.1
    hsc.isLocallyLscAt.2.1).2 (le_antisymm (subderivative_le_upperSemiderivative f x w) hup)
  exact hsd.hasSemiderivative

/-- **Theorem 9.16**, (⇒): strict continuity and regularity on `O` give finite
one-sided directional derivatives, usc in the base point. -/
theorem hasOneSidedDirDeriv_usc_of_strictlyContinuous_regular {f : E → EReal} {O : Set E}
    (hO : IsOpen O)
    (h : ∀ x ∈ O, ERealStrictlyContinuousAt f x ∧ IsSubdifferentiallyRegularAt f x) :
    (∀ x ∈ O, ∀ w, HasOneSidedDirDeriv f x w ((subderivative f x w).toReal : EReal)) ∧
      ∀ w, UpperSemicontinuousOn (fun x ↦ (subderivative f x w).toReal) O := by
  refine ⟨fun x hx w ↦ ?_, ?_⟩
  · have h1 := (hasSemiderivative_of_strictlyContinuous_regular (h x hx).1 (h x hx).2
      w).hasOneSidedDirDeriv
    rw [← (h x hx).1.subderivative_finite w]
    exact h1
  · intro w x hx a ha
    have hreg := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.1
      (h x hx).2).2
    have hlim : limsup (fun y ↦ subderivative f y w) (𝓝 x) < (a : EReal) := by
      rw [← (h x hx).1.regularSubderivative_eq_limsup_subderivative w, ← congrFun hreg w,
        (h x hx).1.subderivative_finite w]
      exact EReal.coe_lt_coe_iff.2 ha
    have hev := (eventually_lt_of_limsup_lt hlim).and (hO.mem_nhds hx)
    refine (hev.filter_mono nhdsWithin_le_nhds).mono fun y hy ↦ ?_
    have h1 := hy.1
    rw [(h y hy.2).1.subderivative_finite w] at h1
    exact EReal.coe_lt_coe_iff.1 h1

/-- **Theorem 9.16**: for `f` on an open set `O`, `f` is strictly continuous and
regular on `O` if and only if the one-sided directional derivative
`h(x, w) = lim_{τ ↘ 0} [f(x + τw) - f(x)]/τ` exists and is finite for every
`x ∈ O` and every `w`, and depends upper semicontinuously on `x ∈ O` for each
fixed `w`. -/
theorem strictlyContinuous_regular_iff_hasOneSidedDirDeriv_usc {f : E → EReal} {O : Set E}
    (hO : IsOpen O) :
    (∀ x ∈ O, ERealStrictlyContinuousAt f x ∧ IsSubdifferentiallyRegularAt f x) ↔
      ∃ g : E → E → ℝ, (∀ x ∈ O, ∀ w, HasOneSidedDirDeriv f x w (g x w)) ∧
        ∀ w, UpperSemicontinuousOn (fun x ↦ g x w) O := by
  constructor
  · intro h
    exact ⟨fun x w ↦ (subderivative f x w).toReal,
      hasOneSidedDirDeriv_usc_of_strictlyContinuous_regular hO h⟩
  · rintro ⟨g, hg, husc⟩ x hx
    exact ⟨eRealStrictlyContinuousAt_of_hasOneSidedDirDeriv_usc hO hg husc hx,
      isSubdifferentiallyRegularAt_of_hasOneSidedDirDeriv_usc hO hg husc hx⟩

/-- **Theorem 9.16**: `df(x)(w)` is the upper limit of difference quotients with
moving base point. -/
theorem subderivative_eq_limsup_of_strictlyContinuous_regular {f : E → EReal} {x : E}
    (hsc : ERealStrictlyContinuousAt f x) (hreg : IsSubdifferentiallyRegularAt f x) (w : E) :
    subderivative f x w = limsup (fun q : (E × ℝ) × E ↦ differenceQuotient f q.1.1 q.1.2 q.2)
      ((𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w) := by
  rw [congrFun (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.1 hreg).2 w,
    hsc.regularSubderivative_eq_upperDirectionalSlope w, upperDirectionalSlope,
    hsc.attentiveNhds_eq]

/-- **Theorem 9.16**: `h(x, w) = df(x)(w)` is usc jointly in `(x, w)` on `O × ℝⁿ`. -/
theorem upperSemicontinuousOn_subderivative_of_strictlyContinuous_regular {f : E → EReal}
    {O : Set E}
    (h : ∀ x ∈ O, ERealStrictlyContinuousAt f x ∧ IsSubdifferentiallyRegularAt f x) :
    UpperSemicontinuousOn (fun p : E × E ↦ subderivative f p.1 p.2) (O ×ˢ univ) := by
  rintro ⟨x, w⟩ ⟨hx, -⟩ a ha
  obtain ⟨a', ha1, ha2⟩ := exists_between ha
  have ha1' : limsup (fun q : (E × ℝ) × E ↦ differenceQuotient f q.1.1 q.1.2 q.2)
      ((𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w) < a' := by
    rw [← subderivative_eq_limsup_of_strictlyContinuous_regular (h x hx).1 (h x hx).2 w]
    exact ha1
  obtain ⟨P, hP, W, hW, hPW⟩ := mem_prod_iff.1 (eventually_lt_of_limsup_lt ha1')
  obtain ⟨Y, hY, T, hT, hYT⟩ := mem_prod_iff.1 hP
  have hnhds : interior Y ×ˢ interior W ∈ 𝓝 (x, w) :=
    prod_mem_nhds (interior_mem_nhds.2 hY) (interior_mem_nhds.2 hW)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hnhds, self_mem_nhdsWithin] with p hp hpO
  show subderivative f p.1 p.2 < a
  have hp1 : p.1 ∈ O := hpO.1
  rw [subderivative_eq_limsup_of_strictlyContinuous_regular (h p.1 hp1).1 (h p.1 hp1).2 p.2]
  refine lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) ?_) ha2
  have hmem : (Y ×ˢ T) ×ˢ W ∈ (𝓝 p.1 ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 p.2 :=
    prod_mem_prod (prod_mem_prod (mem_interior_iff_mem_nhds.1 hp.1) hT)
      (mem_interior_iff_mem_nhds.1 hp.2)
  refine Filter.mem_of_superset hmem fun q hq ↦ ?_
  have h1 : differenceQuotient f q.1.1 q.1.2 q.2 < a' := hPW ⟨hYT hq.1, hq.2⟩
  show differenceQuotient f q.1.1 q.1.2 q.2 ≤ a'
  exact h1.le

omit [FiniteDimensional ℝ E] in
/-- At a point of strict continuity the limiting subdifferential is osc. -/
theorem svOscAt_subdifferential_of_eRealStrictlyContinuousAt {f : E → EReal} {x : E}
    (hsc : ERealStrictlyContinuousAt f x) : SvOscAt (subdifferential f) x := by
  intro v hv
  have h1 : v ∈ outerSetLimitAlong (attentiveNhds f x) (subdifferential f) := by
    rw [hsc.attentiveNhds_eq]
    exact hv
  exact outerSetLimitAlong_subdifferential_subset hsc.finite h1

/-- **Theorem 9.16**, the conclusions under strict continuity and regularity on an
open set `O`: semidifferentiability with `h = df = d̂f`, the limsup and maximum
formulas, joint upper semicontinuity of `df`, and the properties of `∂f`. -/
theorem strictlyContinuous_regular_properties {f : E → EReal} {O : Set E}
    (h : ∀ x ∈ O, ERealStrictlyContinuousAt f x ∧ IsSubdifferentiallyRegularAt f x) :
    (∀ x ∈ O, SemidifferentiableAt f x) ∧
    (∀ x ∈ O, ∀ w, HasSemiderivative f x w (subderivative f x w) ∧
      subderivative f x w = regularSubderivative f x w ∧
      subderivative f x w = limsup (fun q : (E × ℝ) × E ↦ differenceQuotient f q.1.1 q.1.2 q.2)
        ((𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w) ∧
      ∃ v ∈ subdifferential f x, subderivative f x w = (⟪v, w⟫_ℝ : EReal) ∧
        ∀ u ∈ subdifferential f x, ⟪u, w⟫_ℝ ≤ ⟪v, w⟫_ℝ) ∧
    UpperSemicontinuousOn (fun p : E × E ↦ subderivative f p.1 p.2) (O ×ˢ univ) ∧
    (∀ x ∈ O, (subdifferential f x).Nonempty ∧ Convex ℝ (subdifferential f x) ∧
      IsCompact (subdifferential f x)) ∧
    SvOscOn (subdifferential f) O ∧ ∀ x ∈ O, SvLocallyBoundedAt (subdifferential f) x := by
  have hdf : ∀ x ∈ O, subderivative f x = regularSubderivative f x := fun x hx ↦
    (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.1 (h x hx).2).2
  refine ⟨fun x hx w ↦ ⟨_, hasSemiderivative_of_strictlyContinuous_regular (h x hx).1
      (h x hx).2 w⟩, fun x hx w ↦ ⟨hasSemiderivative_of_strictlyContinuous_regular (h x hx).1
      (h x hx).2 w, congrFun (hdf x hx) w,
      subderivative_eq_limsup_of_strictlyContinuous_regular (h x hx).1 (h x hx).2 w, ?_⟩,
    upperSemicontinuousOn_subderivative_of_strictlyContinuous_regular h, fun x hx ↦ ?_,
    fun x hx ↦ (svOscAt_subdifferential_of_eRealStrictlyContinuousAt (h x hx).1).svOscWithinAt O,
    fun x hx ↦ (h x hx).1.locallyBoundedAt_subdifferential⟩
  · obtain ⟨v, hv, hval, hmax⟩ := (h x hx).1.exists_max_inner_subdifferential w
    exact ⟨v, hv, (congrFun (hdf x hx) w).trans hval, hmax⟩
  · obtain ⟨hne, hcomp⟩ := (h x hx).1.subdifferential_nonempty_compact
    refine ⟨hne, ?_, hcomp⟩
    rw [(h x hx).2.subdifferential_eq_linearMinorantSet]
    exact convex_linearMinorantSet _

end Finite

end RW
