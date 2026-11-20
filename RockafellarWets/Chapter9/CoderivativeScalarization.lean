/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: coderivatives of single-valued mappings by scalarization

**Proposition 9.24(b)**, the scalarization formulas: for a single-valued mapping
`G : E → F` that is strictly continuous at `x̄`, with `(yG)(x) = ⟪y, G x⟫`,

* `D̂*G(x̄)(y) = ∂̂(yG)(x̄)` for every `y`
  (`regularCoderivative_svSingleton_eq_regularSubdifferential`);
* `D*G(x̄)(y) = ∂(yG)(x̄)` for every `y`, `E` finite-dimensional
  (`coderivative_svSingleton_eq_subdifferential`).

The mapping is `svSingleton G = fun x ↦ {G x}`.

For the limiting formula the book combines the graphical limit 8(22) with the
estimate `∂̂[yνG](xν) ⊂ ∂̂[yG](xν) + ∂̂[(yν - y)G](xν)`, which is not an exact
inclusion for regular subgradients in general.  Here the covector perturbation
`yν → y` is absorbed by `exists_mem_regularSubdifferential_of_inner_error`: a
subgradient inequality with error `ε` on a closed ball yields an exact regular
subgradient within `2ε` at a point of the half-radius ball (quadratic penalty and
a minimizer on the compact ball).

The other statements of 9.24 (nonemptiness, osc and local boundedness of
`DG(x̄)` and `D*G(x̄)`, and the norm formulas) are not formalized here.
-/

import RockafellarWets.Chapter8.GraphicalDerivatives
import RockafellarWets.Chapter8.SubderivativeFormulas
import RockafellarWets.Chapter9.LipschitzModulus
import RockafellarWets.Chapter5.LocallyBoundedContinuity

open Filter Set Topology Metric
open scoped ENNReal NNReal InnerProductSpace

namespace RW

section Approximation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- A subgradient inequality with error `ε` on a closed ball yields an exact regular
subgradient within `2ε`, at a point of the half-radius ball. -/
theorem exists_mem_regularSubdifferential_of_inner_error {φ : E → ℝ} {x₀ v₀ : E} {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hcont : ContinuousOn φ (closedBall x₀ δ))
    (hineq : ∀ z ∈ closedBall x₀ δ, φ x₀ + ⟪v₀, z - x₀⟫_ℝ - ε * ‖z - x₀‖ ≤ φ z) :
    ∃ x' v' : E, ‖x' - x₀‖ ≤ δ / 2 ∧ ‖v' - v₀‖ ≤ 2 * ε ∧
      v' ∈ regularSubdifferential (fun z ↦ (φ z : EReal)) x' := by
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 4 * ε / δ := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : E → ℝ, ∀ z, θ z = φ z - ⟪v₀, z - x₀⟫_ℝ + c / 2 * ‖z - x₀‖ ^ 2 :=
    ⟨_, fun _ ↦ rfl⟩
  have hθc : ContinuousOn θ (closedBall x₀ δ) := by
    have h1 : ContinuousOn (fun z ↦ φ z - ⟪v₀, z - x₀⟫_ℝ + c / 2 * ‖z - x₀‖ ^ 2)
        (closedBall x₀ δ) :=
      (hcont.sub (continuous_const.inner (continuous_id.sub continuous_const)).continuousOn).add
        (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)).continuousOn
    exact h1.congr fun z _ ↦ hθ z
  obtain ⟨x', hx', hmin⟩ := (isCompact_closedBall x₀ δ).exists_isMinOn
    (nonempty_closedBall.2 hδ.le) hθc
  have hx0 : x₀ ∈ closedBall x₀ δ := mem_closedBall_self hδ.le
  have hθ0 : θ x₀ = φ x₀ := by rw [hθ]; simp
  have hθle : θ x' ≤ φ x₀ := hθ0 ▸ isMinOn_iff.1 hmin x₀ hx0
  rw [hθ] at hθle
  have h1 := hineq x' hx'
  have ht : c * ‖x' - x₀‖ ≤ 2 * ε := by
    rcases (norm_nonneg (x' - x₀)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      positivity
    · nlinarith
  have ht' : ‖x' - x₀‖ ≤ δ / 2 := by
    rw [hc_def, div_mul_eq_mul_div, div_le_iff₀ hδ] at ht
    nlinarith
  have hx'ball : x' ∈ ball x₀ δ := by
    rw [mem_ball, dist_eq_norm]
    linarith
  refine ⟨x', v₀ - c • (x' - x₀), ht', ?_, φ x', rfl, fun ε' hε' ↦ ?_⟩
  · rw [show v₀ - c • (x' - x₀) - v₀ = -(c • (x' - x₀)) by abel, norm_neg, norm_smul,
      Real.norm_of_nonneg hc.le]
    exact ht
  · have hnear : closedBall x₀ δ ∈ 𝓝 x' :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hx'ball) ball_subset_closedBall
    have hr : 0 < 2 * ε' / c := by positivity
    filter_upwards [hnear, closedBall_mem_nhds x' hr] with z hz hz'
    have hzmin : θ x' ≤ θ z := isMinOn_iff.1 hmin z hz
    rw [hθ, hθ] at hzmin
    have hid := norm_add_sq_real (z - x') (x' - x₀)
    rw [show z - x' + (x' - x₀) = z - x₀ by abel] at hid
    have hid' : c / 2 * ‖z - x₀‖ ^ 2 =
        c / 2 * ‖z - x'‖ ^ 2 + c * ⟪z - x', x' - x₀⟫_ℝ + c / 2 * ‖x' - x₀‖ ^ 2 := by
      rw [hid]
      ring
    have hin1 : ⟪v₀, z - x₀⟫_ℝ = ⟪v₀, z - x'⟫_ℝ + ⟪v₀, x' - x₀⟫_ℝ := by
      rw [← inner_add_right]
      congr 1
      abel
    have hin2 : ⟪v₀ - c • (x' - x₀), z - x'⟫_ℝ = ⟪v₀, z - x'⟫_ℝ - c * ⟪z - x', x' - x₀⟫_ℝ := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_comm (z - x') (x' - x₀)]
    have hdist : ‖z - x'‖ ≤ 2 * ε' / c := by
      rw [← dist_eq_norm]
      exact hz'
    have hq : c / 2 * ‖z - x'‖ ^ 2 ≤ ε' * ‖z - x'‖ := by
      have h2 : c * ‖z - x'‖ ≤ 2 * ε' := by
        rw [le_div_iff₀ hc] at hdist
        linarith
      nlinarith [norm_nonneg (z - x')]
    refine EReal.coe_le_coe_iff.2 ?_
    linarith

end Approximation

section Scalarization

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

private theorem inner_toLp_sub (v : E) (w : F) (p : WithLp 2 (E × F)) (x : E) (u : F) :
    ⟪WithLp.toLp 2 (v, w), p - WithLp.toLp 2 (x, u)⟫_ℝ = ⟪v, p.fst - x⟫_ℝ + ⟪w, p.snd - u⟫_ℝ :=
  WithLp.prod_inner_apply _ _

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
private theorem norm_fst_le_withLp (p : WithLp 2 (E × F)) : ‖p.fst‖ ≤ ‖p‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 p
  nlinarith [norm_nonneg p, norm_nonneg p.fst, sq_nonneg ‖p.snd‖]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
private theorem norm_withLp_le_add (p : WithLp 2 (E × F)) : ‖p‖ ≤ ‖p.fst‖ + ‖p.snd‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 p
  nlinarith [norm_nonneg p, norm_nonneg p.fst, norm_nonneg p.snd]

/-- **Proposition 9.24(b)**, regular level: a regular subgradient of `⟪y, G ·⟫` is a
regular coderivative value of `G` for `y`. -/
theorem mem_regularCoderivative_of_mem_regularSubdifferential {G : E → F} {x v : E} {y : F}
    (hv : v ∈ regularSubdifferential (fun z ↦ ((⟪y, G z⟫_ℝ : ℝ) : EReal)) x) :
    v ∈ regularCoderivative (svSingleton G) x (G x) y := by
  obtain ⟨c, hc, hev⟩ := hv
  have hc' : ⟪y, G x⟫_ℝ = c := EReal.coe_injective hc
  show WithLp.toLp 2 (v, -y) ∈ regularNormalCone (euclideanSvGraph (svSingleton G))
    (WithLp.toLp 2 (x, G x))
  refine ⟨mem_singleton _, fun ε hε ↦ ?_⟩
  have hfst : Tendsto (fun p : WithLp 2 (E × F) ↦ p.fst)
      (𝓝[euclideanSvGraph (svSingleton G)] (WithLp.toLp 2 (x, G x))) (𝓝 x) :=
    ((WithLp.continuous_fst 2 E F).tendsto _).mono_left nhdsWithin_le_nhds
  filter_upwards [hfst.eventually (hev ε hε), self_mem_nhdsWithin] with p hp hpG
  have hpG' : p.snd = G p.fst := mem_singleton_iff.1 hpG
  have hp' : c + ⟪v, p.fst - x⟫_ℝ - ε * ‖p.fst - x‖ ≤ ⟪y, G p.fst⟫_ℝ :=
    EReal.coe_le_coe_iff.1 hp
  have hnorm := norm_fst_le_withLp (p - WithLp.toLp 2 (x, G x))
  have e1 : (p - WithLp.toLp 2 (x, G x)).fst = p.fst - x := rfl
  rw [e1] at hnorm
  rw [inner_toLp_sub, hpG', inner_neg_left, inner_sub_right y (G p.fst) (G x)]
  have h2 := mul_le_mul_of_nonneg_left hnorm hε.le
  linarith

/-- **Proposition 9.24(b)**, regular level: where `G` is Lipschitz on a neighborhood of
`x`, a regular coderivative value for `y` is a regular subgradient of `⟪y, G ·⟫`. -/
theorem mem_regularSubdifferential_of_mem_regularCoderivative {G : E → F} {x v : E} {y : F}
    {k : ℝ≥0} {U : Set E} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith k G U)
    (hv : v ∈ regularCoderivative (svSingleton G) x (G x) y) :
    v ∈ regularSubdifferential (fun z ↦ ((⟪y, G z⟫_ℝ : ℝ) : EReal)) x := by
  have hv' : WithLp.toLp 2 (v, -y) ∈ regularNormalCone (euclideanSvGraph (svSingleton G))
      (WithLp.toLp 2 (x, G x)) := hv
  obtain ⟨-, hev⟩ := hv'
  refine ⟨⟪y, G x⟫_ℝ, rfl, fun ε hε ↦ ?_⟩
  have hk : (0 : ℝ) < 1 + k := by positivity
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hcont : ContinuousAt G x := hL.continuousOn.continuousAt hU
  have hmap : Tendsto (fun z ↦ WithLp.toLp 2 (z, G z)) (𝓝 x)
      (𝓝[euclideanSvGraph (svSingleton G)] (WithLp.toLp 2 (x, G x))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun z ↦ mem_singleton _)
    exact ((WithLp.prod_continuous_toLp 2 E F).tendsto _).comp
      (tendsto_id.prodMk_nhds hcont.tendsto)
  filter_upwards [hmap.eventually (hev (ε / (1 + k)) (by positivity)), hU] with z hz hzU
  have h1 : ⟪WithLp.toLp 2 (v, -y), WithLp.toLp 2 (z, G z) - WithLp.toLp 2 (x, G x)⟫_ℝ =
      ⟪v, z - x⟫_ℝ - (⟪y, G z⟫_ℝ - ⟪y, G x⟫_ℝ) := by
    rw [inner_toLp_sub]
    show ⟪v, z - x⟫_ℝ + ⟪-y, G z - G x⟫_ℝ = _
    rw [inner_neg_left, inner_sub_right y (G z) (G x)]
    ring
  have h2 : ‖WithLp.toLp 2 (z, G z) - WithLp.toLp 2 (x, G x)‖ ≤ (1 + k) * ‖z - x‖ := by
    have h3 := norm_withLp_le_add (WithLp.toLp 2 (z, G z) - WithLp.toLp 2 (x, G x))
    have h4 : ‖G z - G x‖ ≤ k * ‖z - x‖ := by
      have := hL.dist_le_mul z hzU x hxU
      rwa [dist_eq_norm, dist_eq_norm] at this
    have e1 : (WithLp.toLp 2 (z, G z) - WithLp.toLp 2 (x, G x)).fst = z - x := rfl
    have e2 : (WithLp.toLp 2 (z, G z) - WithLp.toLp 2 (x, G x)).snd = G z - G x := rfl
    rw [e1, e2] at h3
    linarith
  have hz' : ⟪v, z - x⟫_ℝ - (⟪y, G z⟫_ℝ - ⟪y, G x⟫_ℝ) ≤ ε * ‖z - x‖ := by
    rw [← h1]
    refine hz.trans ?_
    calc ε / (1 + k) * ‖WithLp.toLp 2 (z, G z) - WithLp.toLp 2 (x, G x)‖
        ≤ ε / (1 + k) * ((1 + k) * ‖z - x‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε * ‖z - x‖ := by field_simp
  show (((⟪y, G x⟫_ℝ + ⟪v, z - x⟫_ℝ - ε * ‖z - x‖ : ℝ)) : EReal) ≤ ((⟪y, G z⟫_ℝ : ℝ) : EReal)
  exact EReal.coe_le_coe_iff.2 (by linarith)

/-- **Proposition 9.24(b)**: for `G` strictly continuous at `x̄`,
`D̂*G(x̄)(y) = ∂̂(yG)(x̄)`. -/
theorem regularCoderivative_svSingleton_eq_regularSubdifferential {G : E → F} {x : E}
    (hG : StrictlyContinuousAt G x) (y : F) :
    regularCoderivative (svSingleton G) x (G x) y =
      regularSubdifferential (fun z ↦ ((⟪y, G z⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 hG
  ext v
  exact ⟨mem_regularSubdifferential_of_mem_regularCoderivative hU hL,
    mem_regularCoderivative_of_mem_regularSubdifferential⟩

private theorem exists_seq_of_mem_coderivative_svSingleton {G : E → F} {x v : E} {y : F}
    (hv : v ∈ coderivative (svSingleton G) x (G x) y) :
    ∃ (xs vs : ℕ → E) (ys : ℕ → F), Tendsto xs atTop (𝓝 x) ∧ Tendsto vs atTop (𝓝 v) ∧
      Tendsto ys atTop (𝓝 y) ∧
      ∀ n, vs n ∈ regularCoderivative (svSingleton G) (xs n) (G (xs n)) (ys n) := by
  have hv' : WithLp.toLp 2 (v, -y) ∈ normalCone (euclideanSvGraph (svSingleton G))
      (WithLp.toLp 2 (x, G x)) := hv
  obtain ⟨-, ps, ws, hps, hpto, hws, hwto⟩ := hv'
  have hpsG : ∀ n, (ps n).snd = G (ps n).fst := fun n ↦ mem_singleton_iff.1 (hps n)
  refine ⟨fun n ↦ (ps n).fst, fun n ↦ (ws n).fst, fun n ↦ -(ws n).snd,
    ((WithLp.continuous_fst 2 E F).tendsto _).comp hpto,
    ((WithLp.continuous_fst 2 E F).tendsto _).comp hwto, ?_, fun n ↦ ?_⟩
  · have h1 := (((WithLp.continuous_snd 2 E F).tendsto _).comp hwto).neg
    simpa [Function.comp_def] using h1
  · show WithLp.toLp 2 ((ws n).fst, -(-(ws n).snd)) ∈
      regularNormalCone (euclideanSvGraph (svSingleton G)) (WithLp.toLp 2 ((ps n).fst, G (ps n).fst))
    rw [neg_neg, ← hpsG n]
    exact hws n

/-- **Proposition 9.24(b)**, the scalarization formula: for a single-valued mapping `G`
strictly continuous at `x̄`, `D*G(x̄)(y) = ∂(yG)(x̄)` for every `y`, where
`(yG)(x) = ⟪y, G x⟫`. -/
theorem coderivative_svSingleton_eq_subdifferential [FiniteDimensional ℝ E] {G : E → F} {x : E}
    (hG : StrictlyContinuousAt G x) (y : F) :
    coderivative (svSingleton G) x (G x) y =
      subdifferential (fun z ↦ ((⟪y, G z⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 hG
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hLr : LipschitzOnWith k G (ball x r) := hL.mono hrU
  have hcontr : ContinuousOn G (ball x r) := hLr.continuousOn
  have hcx : ContinuousAt G x := hcontr.continuousAt (ball_mem_nhds x hr)
  ext v
  constructor
  · intro hv
    obtain ⟨xs, vs, ys, hxs, hvs, hys, hreg⟩ := exists_seq_of_mem_coderivative_svSingleton hv
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (ball_mem_nhds x (half_pos hr)))
    have hstep : ∀ n : ℕ, ∃ x' v' : E, ‖x' - xs (n + N)‖ ≤ 1 / ((n : ℝ) + 1) ∧
        ‖v' - vs (n + N)‖ ≤ 2 * (1 / ((n : ℝ) + 1) + k * ‖ys (n + N) - y‖) ∧
        v' ∈ regularSubdifferential (fun z ↦ ((⟪y, G z⟫_ℝ : ℝ) : EReal)) x' := by
      intro n
      have hm : xs (n + N) ∈ ball x (r / 2) := hN (n + N) (Nat.le_add_left N n)
      have hm' : dist (xs (n + N)) x < r / 2 := hm
      have hball : ball x r ∈ 𝓝 (xs (n + N)) :=
        isOpen_ball.mem_nhds (ball_subset_ball (half_le_self hr.le) hm)
      obtain ⟨c, hc, hev⟩ := mem_regularSubdifferential_of_mem_regularCoderivative hball hLr
        (hreg (n + N))
      have hc' : ⟪ys (n + N), G (xs (n + N))⟫_ℝ = c := EReal.coe_injective hc
      have hη : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.mem_nhds_iff.1 (hev _ hη)
      obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = min (δ₀ / 2) (min (r / 4) (1 / ((n : ℝ) + 1))) :=
        ⟨_, rfl⟩
      have hδ : 0 < δ := by
        rw [hδ_def]
        exact lt_min (half_pos hδ₀) (lt_min (by positivity) hη)
      have hδ1 : δ ≤ δ₀ / 2 := by rw [hδ_def]; exact min_le_left _ _
      have hδ2 : δ ≤ r / 4 := by rw [hδ_def]; exact (min_le_right _ _).trans (min_le_left _ _)
      have hδ3 : δ ≤ 1 / ((n : ℝ) + 1) := by
        rw [hδ_def]; exact (min_le_right _ _).trans (min_le_right _ _)
      have hsub : closedBall (xs (n + N)) δ ⊆ ball x r := by
        intro z hz
        have hz1 : dist z (xs (n + N)) ≤ δ := hz
        rw [mem_ball]
        linarith [dist_triangle z (xs (n + N)) x]
      have hsub0 : closedBall (xs (n + N)) δ ⊆ ball (xs (n + N)) δ₀ := by
        intro z hz
        have hz1 : dist z (xs (n + N)) ≤ δ := hz
        rw [mem_ball]
        linarith
      have hxm : xs (n + N) ∈ ball x r := hsub (mem_closedBall_self hδ.le)
      have hεpos : 0 < 1 / ((n : ℝ) + 1) + k * ‖ys (n + N) - y‖ := by positivity
      have hineq : ∀ z ∈ closedBall (xs (n + N)) δ,
          ⟪y, G (xs (n + N))⟫_ℝ + ⟪vs (n + N), z - xs (n + N)⟫_ℝ -
            (1 / ((n : ℝ) + 1) + k * ‖ys (n + N) - y‖) * ‖z - xs (n + N)‖ ≤ ⟪y, G z⟫_ℝ := by
        intro z hz
        have h1 : c + ⟪vs (n + N), z - xs (n + N)⟫_ℝ - 1 / ((n : ℝ) + 1) * ‖z - xs (n + N)‖ ≤
            ⟪ys (n + N), G z⟫_ℝ := EReal.coe_le_coe_iff.1 (hδ₀sub (hsub0 hz))
        have h2 : ‖G z - G (xs (n + N))‖ ≤ k * ‖z - xs (n + N)‖ := by
          have h3 := hLr.dist_le_mul z (hsub hz) (xs (n + N)) hxm
          rwa [dist_eq_norm, dist_eq_norm] at h3
        have h4 : ⟪ys (n + N) - y, G z - G (xs (n + N))⟫_ℝ ≤
            ‖ys (n + N) - y‖ * (k * ‖z - xs (n + N)‖) :=
          (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
        have h5 : ⟪ys (n + N) - y, G z - G (xs (n + N))⟫_ℝ =
            (⟪ys (n + N), G z⟫_ℝ - ⟪ys (n + N), G (xs (n + N))⟫_ℝ) -
              (⟪y, G z⟫_ℝ - ⟪y, G (xs (n + N))⟫_ℝ) := by
          rw [inner_sub_left, inner_sub_right, inner_sub_right]
        rw [hc'] at h5
        nlinarith [norm_nonneg (z - xs (n + N)), norm_nonneg (ys (n + N) - y)]
      have hcont : ContinuousOn (fun z ↦ ⟪y, G z⟫_ℝ) (closedBall (xs (n + N)) δ) :=
        continuousOn_const.inner (hcontr.mono hsub)
      obtain ⟨x', v', hx', hv', hreg'⟩ :=
        exists_mem_regularSubdifferential_of_inner_error hδ hεpos hcont hineq
      exact ⟨x', v', hx'.trans (by linarith), hv', hreg'⟩
    choose x' v' hx' hv' hreg' using hstep
    have hxN : Tendsto (fun n ↦ xs (n + N)) atTop (𝓝 x) := hxs.comp (tendsto_add_atTop_nat N)
    have hvN : Tendsto (fun n ↦ vs (n + N)) atTop (𝓝 v) := hvs.comp (tendsto_add_atTop_nat N)
    have hyN : Tendsto (fun n ↦ ys (n + N)) atTop (𝓝 y) := hys.comp (tendsto_add_atTop_nat N)
    have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hx'lim : Tendsto x' atTop (𝓝 x) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 := h0.add (tendsto_iff_norm_sub_tendsto_zero.1 hxN)
      rw [add_zero] at h1
      refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) h1
      calc ‖x' n - x‖ = ‖(x' n - xs (n + N)) + (xs (n + N) - x)‖ := by congr 1; abel
        _ ≤ ‖x' n - xs (n + N)‖ + ‖xs (n + N) - x‖ := norm_add_le _ _
        _ ≤ 1 / ((n : ℝ) + 1) + ‖xs (n + N) - x‖ := by linarith [hx' n]
    have hv'lim : Tendsto v' atTop (𝓝 v) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hyn : Tendsto (fun n ↦ ‖ys (n + N) - y‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 hyN
      have h1 := ((h0.add (hyn.const_mul (k : ℝ))).const_mul 2).add
        (tendsto_iff_norm_sub_tendsto_zero.1 hvN)
      simp only [mul_zero, add_zero] at h1
      refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) h1
      calc ‖v' n - v‖ = ‖(v' n - vs (n + N)) + (vs (n + N) - v)‖ := by congr 1; abel
        _ ≤ ‖v' n - vs (n + N)‖ + ‖vs (n + N) - v‖ := norm_add_le _ _
        _ ≤ 2 * (1 / ((n : ℝ) + 1) + k * ‖ys (n + N) - y‖) + ‖vs (n + N) - v‖ := by
          linarith [hv' n]
    have hφ : Tendsto ((fun z ↦ ((⟪y, G z⟫_ℝ : ℝ) : EReal)) ∘ x') atTop
        (𝓝 ((⟪y, G x⟫_ℝ : ℝ) : EReal)) := by
      have h1 : ContinuousAt (fun z ↦ ((⟪y, G z⟫_ℝ : ℝ) : EReal)) x :=
        continuous_coe_real_ereal.continuousAt.comp
          ((continuous_const.inner continuous_id).continuousAt.comp hcx)
      exact h1.tendsto.comp hx'lim
    exact mem_subdifferential_iff_exists_seq.2 ⟨⟨_, rfl⟩, x', v', hx'lim, hφ, hreg', hv'lim⟩
  · intro hv
    obtain ⟨-, xs, vs, hxs, -, hvs, hvto⟩ := mem_subdifferential_iff_exists_seq.1 hv
    show WithLp.toLp 2 (v, -y) ∈ normalCone (euclideanSvGraph (svSingleton G))
      (WithLp.toLp 2 (x, G x))
    refine mem_normalCone_of_forall (mem_singleton _)
      (xs := fun n ↦ WithLp.toLp 2 (xs n, G (xs n))) (vs := fun n ↦ WithLp.toLp 2 (vs n, -y))
      ?_ (fun n ↦ mem_regularCoderivative_of_mem_regularSubdifferential (hvs n)) ?_
    · exact ((WithLp.prod_continuous_toLp 2 E F).tendsto _).comp
        (hxs.prodMk_nhds (hcx.tendsto.comp hxs))
    · exact ((WithLp.prod_continuous_toLp 2 E F).tendsto _).comp
        (hvto.prodMk_nhds tendsto_const_nhds)

end Scalarization

end RW
