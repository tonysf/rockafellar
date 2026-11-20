/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bounds on epi-converging convex functions

Example 7.34. A compact test ball gives a uniform lower bound, while a
recovery sequence supplies bounded heights near its center. Convexity extends
these estimates from the ball to a common affine lower bound in the norm.
-/

import RockafellarWets.Chapter7.InfimaAndMinimizers
import RockafellarWets.Chapter3.CoercivityCompletion

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem exists_pos_norm_minorant {f : E → EReal} {γ β : ℝ}
    (hf : HasAffineNormLowerBound f γ β) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : E, ((-r * (‖w‖ + 1) : ℝ) : EReal) ≤ f w := by
  let r := max 0 (max (-γ) (-β)) + 1
  have hγ : -r ≤ γ := by dsimp [r]; linarith [le_max_left (-γ) (-β), le_max_right 0 (max (-γ) (-β))]
  have hβ : -r ≤ β := by dsimp [r]; linarith [le_max_right (-γ) (-β), le_max_right 0 (max (-γ) (-β))]
  refine ⟨r, by dsimp [r]; positivity, fun w ↦ le_trans ?_ (hf w)⟩
  apply EReal.coe_le_coe_iff.2
  linarith [mul_le_mul_of_nonneg_right hγ (norm_nonneg w)]

/-- A convex function bounded below on a unit ball has an explicit lower
bound along every ray from the center once its height at the center is known. -/
private theorem radial_bound_of_unit_ball {f : E → EReal} (hc : Convex ℝ (epigraph f))
    (hproper : IsProper f) {x : E} {L M : ℝ} (hx : f x ≤ (M : EReal))
    (hball : ∀ z ∈ closedBall x 1, (L : EReal) ≤ f z) (w : E) :
    ((L - (M - L) * ‖w - x‖ : ℝ) : EReal) ≤ f w := by
  by_cases htop : f w = ⊤
  · simp [htop]
  let s := (f w).toReal
  have hs : (s : EReal) = f w := EReal.coe_toReal htop (hproper.2 w).ne'
  let d := ‖w - x‖
  let t := (1 + d)⁻¹
  have hd : 0 ≤ d := norm_nonneg _
  have hden : 0 < 1 + d := by positivity
  have ht : 0 < t := inv_pos.mpr hden
  have ht1 : t ≤ 1 := (inv_le_one₀ hden).mpr (by linarith)
  let z := (1 - t) • x + t • w
  have hz : z ∈ closedBall x 1 := by
    rw [mem_closedBall, dist_eq_norm]
    have he : z - x = t • (w - x) := by dsimp [z]; module
    rw [he, norm_smul_of_nonneg ht.le]
    change (1 + d)⁻¹ * d ≤ 1
    rw [← div_eq_inv_mul, div_le_one hden]
    linarith
  have hep := hc (show (x, M) ∈ epigraph f from hx)
    (show (w, s) ∈ epigraph f from hs.ge) (sub_nonneg.2 ht1) ht.le (sub_add_cancel 1 t)
  have hval : f z ≤ (((1 - t) * M + t * s : ℝ) : EReal) := hep
  have hineq := EReal.coe_le_coe_iff.1 ((hball z hz).trans hval)
  dsimp [t] at hineq
  field_simp [hden.ne'] at hineq
  rw [← hs, EReal.coe_le_coe_iff]
  change L - (M - L) * d ≤ s
  linarith

/-- **Example 7.34**. A common positive linear-growth constant works for the
limit and for every term, including the finite initial segment. -/
theorem exists_uniform_linear_lower_bound_of_convex_epiConverges [FiniteDimensional ℝ E]
    {f : ℕ → E → EReal} {g : E → EReal} (h : EpiConverges f g)
    (hc : ∀ n, Convex ℝ (epigraph (f n))) (hlsc : ∀ n, LowerSemicontinuous (f n))
    (hp : ∀ n, IsProper (f n)) (hg : IsProper g) :
    ∃ r : ℝ, 0 < r ∧ (∀ w, ((-r * (‖w‖ + 1) : ℝ) : EReal) ≤ g w) ∧
      ∀ n w, ((-r * (‖w‖ + 1) : ℝ) : EReal) ≤ f n w := by
  obtain ⟨x, hx⟩ := hg.1
  obtain ⟨M, hxM, _⟩ := EReal.exists_between_coe_real hx
  obtain ⟨ys, hys, hfys⟩ := h.exists_tendsto_values x
  let B := closedBall x 2
  have hB : IsCompact B := isCompact_closedBall _ _
  have hxB : x ∈ B := mem_closedBall_self (by norm_num)
  have hl := lowerSemicontinuous_of_isClosed_epigraph_ereal g (PKConverges.isClosed h)
  obtain ⟨z, hz, hmin⟩ := (hl.lowerSemicontinuousOn _).exists_isMinOn ⟨x, hxB⟩ hB
  obtain ⟨L, _, hL⟩ := EReal.exists_between_coe_real (hg.2 z)
  have hLM : L ≤ M := (EReal.coe_le_coe_iff.1 (hL.le.trans ((hmin hxB).trans hxM.le)))
  have hcrit := (le_epiLowerLimit_iff_infimumOn_compact hl).1
    (epiConverges_iff_epiLimits_eq.1 h).1.ge B hB
  have hlow := eventually_lt_of_lt_liminf ((hL.trans_le (le_infimumOn fun w hw ↦ hmin hw)).trans_le hcrit)
  have hnear : ∀ᶠ n in atTop, ys n ∈ closedBall x 1 := hys (closedBall_mem_nhds x zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlow.and (hnear.and (hfys.eventually_lt_const hxM)))
  let γ := -(M - L)
  let β := L - (M - L) * (‖x‖ + 1)
  have htail : ∀ n ≥ N, HasAffineNormLowerBound (f n) γ β := by
    intro n hn w
    obtain ⟨hnL, hnnear, hnM⟩ := hN n hn
    have hball : ∀ q ∈ closedBall (ys n) 1, (L : EReal) ≤ f n q := by
      intro q hq
      apply hnL.le.trans (infimumOn_le (f := f n) ?_)
      change dist q x ≤ 2
      linarith [dist_triangle q (ys n) x, mem_closedBall.1 hq, mem_closedBall.1 hnnear]
    apply le_trans _ (radial_bound_of_unit_ball (hc n) (hp n) hnM.le hball w)
    apply EReal.coe_le_coe_iff.2
    have hyx : ‖ys n‖ ≤ ‖x‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ys n) x
      rw [← dist_eq_norm] at this
      linarith [mem_closedBall.1 hnnear]
    have hnrm : ‖w - ys n‖ ≤ ‖w‖ + (‖x‖ + 1) := (norm_sub_le _ _).trans (add_le_add_right hyx _)
    dsimp [γ, β]
    linarith [mul_le_mul_of_nonneg_left hnrm (sub_nonneg.2 hLM)]
  have hone : ∀ n, ∃ r : ℝ, 0 < r ∧ ∀ w : E, ((-r * (‖w‖ + 1) : ℝ) : EReal) ≤ f n w := by
    intro n
    obtain ⟨a, b, hm⟩ := exists_affineNormLowerBound_of_not_isCounterCoercive
      (not_isCounterCoercive_of_convex_lsc_isProper (hc n) (hlsc n) (hp n))
    exact exists_pos_norm_minorant hm
  choose rs hrs hrsf using hone
  let rt := max 0 (max (-γ) (-β)) + 1
  have hrt : 0 < rt := by dsimp [rt]; positivity
  let r := rt + ∑ k ∈ Finset.range N, rs k
  have hrtr : rt ≤ r := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ (hrs i).le)
  have hfn : ∀ n w, ((-r * (‖w‖ + 1) : ℝ) : EReal) ≤ f n w := by
    intro n w
    by_cases hn : n < N
    · have hrsr : rs n ≤ r := by
        have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.range N) ↦ (hrs k).le)
          (Finset.mem_range.2 hn)
        dsimp [r]; linarith
      exact (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_right (neg_le_neg hrsr) (by positivity))).trans
        (hrsf n w)
    · apply le_trans _ (htail n (by omega) w)
      apply EReal.coe_le_coe_iff.2
      have hγ : -r ≤ γ := by dsimp [rt] at hrtr; linarith [le_max_left (-γ) (-β), le_max_right 0 (max (-γ) (-β))]
      have hβ : -r ≤ β := by dsimp [rt] at hrtr; linarith [le_max_right (-γ) (-β), le_max_right 0 (max (-γ) (-β))]
      linarith [mul_le_mul_of_nonneg_right hγ (norm_nonneg w)]
  refine ⟨r, hrt.trans_le hrtr, fun w ↦ ?_, hfn⟩
  obtain ⟨ws, hws, hfw⟩ := h.exists_tendsto_values w
  apply le_of_tendsto_of_tendsto' _ hfw (fun n ↦ hfn n (ws n))
  exact EReal.tendsto_coe.2 (tendsto_const_nhds.mul (hws.norm.add_const 1))

end RW
