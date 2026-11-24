/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Symmetry of extended Hessians at points of prox-regularity

Corollary 13.42 and Theorem 13.51 assert that the Hessian `∇²f(x̄)` of a prox-regular function,
when it exists in the extended sense, is symmetric.  The book derives this from Theorem 13.40.  We
give a direct argument: the prox-regularity inequality combined with the first-order expansion of
`∂f` at `x̄` bounds discretized line integrals of `y ↦ ⟪∇f(x̄) + ∇²f(x̄)(y - x̄), ·⟫` along
segments (`segment_lower_estimate`).  Around a small parallelogram these sums telescope to `0`,
which forces `⟪∇²f(x̄)u, w⟫ - ⟪∇²f(x̄)w, u⟫ ≤ 0` once the subdivision is fine.
-/

import RockafellarWets.Chapter13.TwiceDifferentiability
import RockafellarWets.Chapter13.ProxRegularity

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Σ_{k<N} k = N(N - 1)/2` over the reals. -/
theorem sum_range_cast_id (N : ℕ) : ∑ k ∈ Finset.range N, (k : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- A discretized line integral of `y ↦ ⟪v + A(y - x̄), ·⟫` along the segment `[c, c + d]`, under
a two-point inequality valid on a ball around `x̄`. -/
theorem segment_lower_estimate {g : E → ℝ} {x v : E} {A : E →L[ℝ] E} {δ ε ρ : ℝ}
    (H : ∀ y ∈ closedBall x δ, ∀ y' ∈ closedBall x δ,
      ⟪v + A (y - x), y' - y⟫_ℝ - ε * ‖y - x‖ * ‖y' - y‖ - ρ / 2 * ‖y' - y‖ ^ 2 ≤ g y' - g y)
    (hε : 0 ≤ ε) {c d : E} (hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → c + s • d ∈ closedBall x δ)
    {N : ℕ} (hN : 0 < N) :
    ⟪v + A (c - x), d⟫_ℝ + ((N : ℝ) - 1) / (2 * N) * ⟪A d, d⟫_ℝ -
      ε * (‖c - x‖ + ‖d‖) * ‖d‖ - ρ / (2 * N) * ‖d‖ ^ 2 ≤ g (c + d) - g c := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set P : ℕ → E := fun k ↦ c + ((k : ℝ) / N) • d with hP
  have hs1 : ∀ k ≤ N, (k : ℝ) / N ≤ 1 := fun k hk ↦ by
    rw [div_le_one hNpos]; exact_mod_cast hk
  have hPmem : ∀ k ≤ N, P k ∈ closedBall x δ := fun k hk ↦ hseg _ (by positivity) (hs1 k hk)
  have hPk : ∀ k, P k - x = (c - x) + ((k : ℝ) / N) • d := fun k ↦ by simp only [hP]; abel
  have hPx : ∀ k ≤ N, ‖P k - x‖ ≤ ‖c - x‖ + ‖d‖ := by
    intro k hk
    rw [hPk]
    calc ‖(c - x) + ((k : ℝ) / N) • d‖ ≤ ‖c - x‖ + ‖((k : ℝ) / N) • d‖ := norm_add_le _ _
      _ ≤ ‖c - x‖ + ‖d‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        nlinarith [norm_nonneg d, hs1 k hk]
  have hstep : ∀ k, P (k + 1) - P k = (1 / (N : ℝ)) • d := by
    intro k
    simp only [hP]
    push_cast
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    ring
  set R := ‖c - x‖ + ‖d‖ with hR
  have hterm : ∀ k ∈ Finset.range N,
      ⟪v + A (c - x), d⟫_ℝ / N + (k : ℝ) / N ^ 2 * ⟪A d, d⟫_ℝ - ε * R * ‖d‖ / N -
        ρ / 2 * ‖d‖ ^ 2 / N ^ 2 ≤ g (P (k + 1)) - g (P k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h := H (P k) (hPmem k hk.le) (P (k + 1)) (hPmem (k + 1) hk)
    have e1 : ⟪v + A (P k - x), P (k + 1) - P k⟫_ℝ =
        ⟪v + A (c - x), d⟫_ℝ / N + (k : ℝ) / N ^ 2 * ⟪A d, d⟫_ℝ := by
      rw [hstep, hPk, map_add, map_smul, real_inner_smul_right, ← add_assoc, inner_add_left,
        real_inner_smul_left]
      field_simp
    have e2 : ‖P (k + 1) - P k‖ = ‖d‖ / N := by
      rw [hstep, norm_smul, Real.norm_of_nonneg (by positivity)]
      ring
    rw [e1, e2] at h
    have h3 : ε * ‖P k - x‖ * (‖d‖ / N) ≤ ε * R * ‖d‖ / N := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hPx k hk.le) hε)
        (by positivity)
    have h4 : ρ / 2 * (‖d‖ / N) ^ 2 = ρ / 2 * ‖d‖ ^ 2 / N ^ 2 := by ring
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_range_sub (fun k ↦ g (P k))] at hsum
  have hPN : P N = c + d := by simp only [hP]; rw [div_self hNpos.ne', one_smul]
  have hP0 : P 0 = c := by simp [hP]
  rw [hPN, hP0] at hsum
  have hval : ∑ k ∈ Finset.range N, (⟪v + A (c - x), d⟫_ℝ / N + (k : ℝ) / N ^ 2 * ⟪A d, d⟫_ℝ -
      ε * R * ‖d‖ / N - ρ / 2 * ‖d‖ ^ 2 / N ^ 2) =
      ⟪v + A (c - x), d⟫_ℝ + ((N : ℝ) - 1) / (2 * N) * ⟪A d, d⟫_ℝ - ε * R * ‖d‖ -
        ρ / (2 * N) * ‖d‖ ^ 2 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.sum_mul, ← Finset.sum_div, sum_range_cast_id]
    field_simp
  linarith

/-- `segment_lower_estimate` for a segment `[x̄ + p, x̄ + p + d]`. -/
theorem segment_lower_estimate' {g : E → ℝ} {x v : E} {A : E →L[ℝ] E} {δ ε ρ : ℝ}
    (H : ∀ y ∈ closedBall x δ, ∀ y' ∈ closedBall x δ,
      ⟪v + A (y - x), y' - y⟫_ℝ - ε * ‖y - x‖ * ‖y' - y‖ - ρ / 2 * ‖y' - y‖ ^ 2 ≤ g y' - g y)
    (hε : 0 ≤ ε) {p d c₀ c₁ : E} (h₀ : x + p = c₀) (h₁ : x + p + d = c₁)
    (hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → x + p + s • d ∈ closedBall x δ)
    {N : ℕ} (hN : 0 < N) :
    ⟪v + A p, d⟫_ℝ + ((N : ℝ) - 1) / (2 * N) * ⟪A d, d⟫_ℝ -
      ε * (‖p‖ + ‖d‖) * ‖d‖ - ρ / (2 * N) * ‖d‖ ^ 2 ≤ g c₁ - g c₀ := by
  subst h₀ h₁
  have h := segment_lower_estimate H hε (c := x + p) (d := d) hseg hN
  simpa only [add_sub_cancel_left] using h

variable [FiniteDimensional ℝ E]

/-- Prox-regularity at `x̄` for `∇f(x̄)` combined with an extended Hessian `A` at `x̄`: a two-point
inequality on small balls with an arbitrarily small first-order error. -/
theorem HasExtendedHessianAt.exists_local_ineq {f : E → EReal} {x : E} {A : E →L[ℝ] E}
    (hA : HasExtendedHessianAt f x A)
    (hpr : IsProxRegularAt f x (gradient (fun z ↦ (f z).toReal) x)) :
    ∃ ρ : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ closedBall x δ, ∀ y' ∈ closedBall x δ,
      ⟪gradient (fun z ↦ (f z).toReal) x + A (y - x), y' - y⟫_ℝ - ε * ‖y - x‖ * ‖y' - y‖ -
        ρ / 2 * ‖y' - y‖ ^ 2 ≤ (f y').toReal - (f y).toReal := by
  set g : E → ℝ := fun z ↦ (f z).toReal with hg
  set v := gradient g x with hv
  obtain ⟨-, -, ε₁, hε₁, ρ, -, hprox⟩ := hpr
  refine ⟨ρ, fun ε hε ↦ ?_⟩
  have hexp := hA.hasMappingFirstOrderExpansion ε hε
  have hfin := hA.1.1
  have hgcont : ContinuousAt g x := hA.1.2.continuousAt
  have hx : f x = (g x : EReal) := hA.1.finite
  have hflt : ∀ᶠ y in 𝓝 x, g y < g x + ε₁ :=
    hgcont.eventually (gt_mem_nhds (by linarith : g x < g x + ε₁))
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.mem_nhds_iff.1 (hexp.and (hfin.and hflt))
  set δ := min (δ₀ / 2) (min (ε₁ / 2) (ε₁ / (2 * (‖A‖ + ε + 1)))) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ₀' : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδ₁ : δ ≤ ε₁ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₂ : δ ≤ ε₁ / (2 * (‖A‖ + ε + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, hδpos, fun y hy y' hy' ↦ ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hy hy'
  have hyb : y ∈ ball x δ₀ := by rw [mem_ball, dist_eq_norm]; linarith
  have hy'b : y' ∈ ball x δ₀ := by rw [mem_ball, dist_eq_norm]; linarith
  obtain ⟨⟨⟨u, hu⟩, hexpy⟩, hfy, hfly⟩ := hball hyb
  obtain ⟨-, hfy', -⟩ := hball hy'b
  have hu1 := hexpy u hu
  change ‖u - v - A (y - x)‖ ≤ ε * ‖y - x‖ at hu1
  have huv : ‖u - v‖ < ε₁ := by
    have h1 : ‖u - v‖ ≤ ‖u - v - A (y - x)‖ + ‖A (y - x)‖ := by
      calc ‖u - v‖ = ‖(u - v - A (y - x)) + A (y - x)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖A (y - x)‖ ≤ ‖A‖ * ‖y - x‖ := A.le_opNorm _
    have h3 : (‖A‖ + ε) * ‖y - x‖ < ε₁ := by
      have hδ₂' : δ * (2 * (‖A‖ + ε + 1)) ≤ ε₁ := by
        rw [le_div_iff₀ (by positivity)] at hδ₂; exact hδ₂
      have h4 : ‖y - x‖ * (2 * (‖A‖ + ε + 1)) ≤ ε₁ :=
        le_trans (mul_le_mul_of_nonneg_right hy (by positivity)) hδ₂'
      have h5 : (‖A‖ + ε) * ‖y - x‖ ≤ ε₁ / 2 := by nlinarith [norm_nonneg (y - x)]
      linarith
    nlinarith
  have hpi := hprox y u hu huv (by linarith) (by
      rw [hfy, hx, ← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 hfly) y'
    (by rw [mem_closedBall, dist_eq_norm]; linarith)
  rw [hfy, hfy', ← EReal.coe_add, EReal.coe_le_coe_iff] at hpi
  change g y + (⟪u, y' - y⟫_ℝ - ρ / 2 * ‖y' - y‖ ^ 2) ≤ g y' at hpi
  have hcs : ⟪v + A (y - x), y' - y⟫_ℝ - ε * ‖y - x‖ * ‖y' - y‖ ≤ ⟪u, y' - y⟫_ℝ := by
    have h1 := neg_abs_le ⟪u - v - A (y - x), y' - y⟫_ℝ
    have h1' := abs_real_inner_le_norm (u - v - A (y - x)) (y' - y)
    have h2 : ⟪u - v - A (y - x), y' - y⟫_ℝ = ⟪u, y' - y⟫_ℝ - ⟪v + A (y - x), y' - y⟫_ℝ := by
      rw [sub_sub, inner_sub_left]
    have h3 : ‖u - v - A (y - x)‖ * ‖y' - y‖ ≤ ε * ‖y - x‖ * ‖y' - y‖ :=
      mul_le_mul_of_nonneg_right hu1 (norm_nonneg _)
    rw [h2] at h1 h1'
    linarith
  linarith

set_option maxHeartbeats 1600000 in
/-- **The Hessian symmetry of 13.42 and 13.51.**  If `f` is prox-regular at `x̄` for
`v̄ = ∇f(x̄)` and twice differentiable at `x̄` in the extended sense with Hessian `A`, then `A` is
symmetric. -/
theorem HasExtendedHessianAt.inner_map_comm_of_isProxRegularAt {f : E → EReal} {x : E}
    {A : E →L[ℝ] E} (hA : HasExtendedHessianAt f x A)
    (hpr : IsProxRegularAt f x (gradient (fun z ↦ (f z).toReal) x)) (u w : E) :
    ⟪A u, w⟫_ℝ = ⟪u, A w⟫_ℝ := by
  obtain ⟨ρ, hρ⟩ := hA.exists_local_ineq hpr
  set g : E → ℝ := fun z ↦ (f z).toReal with hg
  set v := gradient g x with hv
  -- one orientation of the parallelogram
  have key : ∀ u w : E, ⟪A u, w⟫_ℝ - ⟪A w, u⟫_ℝ ≤ 0 := by
    intro u w
    set S := ‖u‖ + ‖w‖ with hS
    set Q := |⟪A u, u⟫_ℝ| + |⟪A w, w⟫_ℝ| + |ρ| * (‖u‖ ^ 2 + ‖w‖ ^ 2) with hQ
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    -- choose the subdivision and the expansion error
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * Q / η)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hN0 : 0 < N := by exact_mod_cast hNpos
    set ε := η / (8 * (S ^ 2 + 1)) with hε
    have hεpos : 0 < ε := by positivity
    obtain ⟨δ, hδ, H⟩ := hρ ε hεpos
    set t := δ / (S + 1) with ht
    have htpos : 0 < t := by positivity
    have htS : t * S ≤ δ := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    -- the parallelogram lies in the ball
    have hpar : ∀ a b : ℝ, 0 ≤ a → a ≤ t → 0 ≤ b → b ≤ t → x + a • u + b • w ∈ closedBall x δ := by
      intro a b ha hat hb hbt
      rw [mem_closedBall, dist_eq_norm, add_assoc, add_sub_cancel_left]
      calc ‖a • u + b • w‖ ≤ ‖a • u‖ + ‖b • w‖ := norm_add_le _ _
        _ = a * ‖u‖ + b * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        _ ≤ t * ‖u‖ + t * ‖w‖ := by gcongr
        _ = t * S := by ring
        _ ≤ δ := htS
    have hε0 : (0 : ℝ) ≤ ε := hεpos.le
    have hpar' : ∀ a b : ℝ, 0 ≤ a → a ≤ t → 0 ≤ b → b ≤ t → ∀ q : E, q = a • u + b • w →
        x + q ∈ closedBall x δ := by
      intro a b ha hat hb hbt q hq
      rw [hq, ← add_assoc]
      exact hpar a b ha hat hb hbt
    -- the four sides
    have s1 := segment_lower_estimate' H hε0 (p := 0) (d := t • u) (c₀ := x) (c₁ := x + t • u)
      (add_zero x) (by rw [add_zero]) (fun s hs0 hs1 ↦ by
      rw [add_zero]
      exact hpar' (s * t) 0 (by positivity) (by nlinarith) le_rfl htpos.le _
        (by rw [zero_smul, add_zero, smul_smul])) hN0
    have s2 := segment_lower_estimate' H hε0 (p := t • u) (d := t • w) (c₀ := x + t • u)
      (c₁ := x + t • u + t • w) rfl rfl (fun s hs0 hs1 ↦ by
      rw [add_assoc]
      exact hpar' t (s * t) htpos.le le_rfl (by positivity) (by nlinarith) _
        (by rw [smul_smul])) hN0
    have s3 := segment_lower_estimate' H hε0 (p := t • u + t • w) (d := -(t • u))
      (c₀ := x + t • u + t • w) (c₁ := x + t • w) (add_assoc _ _ _).symm (by abel)
      (fun s hs0 hs1 ↦ by
        rw [add_assoc]
        exact hpar' ((1 - s) * t) t (by nlinarith) (by nlinarith) htpos.le le_rfl _
          (by rw [smul_neg, smul_smul, sub_mul, one_mul, sub_smul]; abel)) hN0
    have s4 := segment_lower_estimate' H hε0 (p := t • w) (d := -(t • w)) (c₀ := x + t • w)
      (c₁ := x) rfl (add_neg_cancel_right _ _) (fun s hs0 hs1 ↦ by
        rw [add_assoc]
        exact hpar' 0 ((1 - s) * t) le_rfl htpos.le (by nlinarith) (by nlinarith) _
          (by rw [smul_neg, smul_smul, sub_mul, one_mul, sub_smul, zero_smul]; abel)) hN0
    -- the scalar quantities
    have i1 : ⟪v + A 0, t • u⟫_ℝ = t * ⟪v, u⟫_ℝ := by
      rw [map_zero, add_zero, real_inner_smul_right]
    have i2 : ⟪v + A (t • u), t • w⟫_ℝ = t * ⟪v, w⟫_ℝ + t ^ 2 * ⟪A u, w⟫_ℝ := by
      rw [map_smul, inner_add_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_left]; ring
    have i3 : ⟪v + A (t • u + t • w), -(t • u)⟫_ℝ =
        -(t * ⟪v, u⟫_ℝ) - t ^ 2 * ⟪A u, u⟫_ℝ - t ^ 2 * ⟪A w, u⟫_ℝ := by
      rw [map_add, map_smul, map_smul, inner_neg_right, inner_add_left, inner_add_left,
        real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_left]; ring
    have i4 : ⟪v + A (t • w), -(t • w)⟫_ℝ = -(t * ⟪v, w⟫_ℝ) - t ^ 2 * ⟪A w, w⟫_ℝ := by
      rw [map_smul, inner_neg_right, inner_add_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_left]; ring
    have j1 : ⟪A (t • u), t • u⟫_ℝ = t ^ 2 * ⟪A u, u⟫_ℝ := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    have j2 : ⟪A (t • w), t • w⟫_ℝ = t ^ 2 * ⟪A w, w⟫_ℝ := by
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    have j3 : ⟪A (-(t • u)), -(t • u)⟫_ℝ = t ^ 2 * ⟪A u, u⟫_ℝ := by
      rw [map_neg, inner_neg_neg, j1]
    have j4 : ⟪A (-(t • w)), -(t • w)⟫_ℝ = t ^ 2 * ⟪A w, w⟫_ℝ := by
      rw [map_neg, inner_neg_neg, j2]
    have nu : ‖t • u‖ = t * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg htpos.le]
    have nw : ‖t • w‖ = t * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg htpos.le]
    have nuw : ‖t • u + t • w‖ ≤ t * ‖u‖ + t * ‖w‖ := by
      rw [← nu, ← nw]; exact norm_add_le _ _
    rw [i1, j1, norm_zero, nu] at s1
    rw [i2, j2, nu, nw] at s2
    rw [i3, j3, norm_neg, nu] at s3
    rw [i4, j4, norm_neg, nw] at s4
    -- the error terms
    have e3 : ε * (‖t • u + t • w‖ + t * ‖u‖) * (t * ‖u‖) ≤
        ε * (t * ‖u‖ + t * ‖w‖ + t * ‖u‖) * (t * ‖u‖) := by
      gcongr
    set κ : ℝ := ((N : ℝ) - 1) / (2 * N) with hκ
    have h2κ : 2 * κ - 1 = -(1 / N) := by rw [hκ]; field_simp; ring
    have hsum : t ^ 2 * (⟪A u, w⟫_ℝ - ⟪A w, u⟫_ℝ) ≤
        t ^ 2 * ((⟪A u, u⟫_ℝ + ⟪A w, w⟫_ℝ + ρ * (‖u‖ ^ 2 + ‖w‖ ^ 2)) / N) +
          3 * ε * t ^ 2 * S ^ 2 := by
      have hdiv : ρ / (2 * N) * (t * ‖u‖) ^ 2 + ρ / (2 * N) * (t * ‖w‖) ^ 2 +
          ρ / (2 * N) * (t * ‖u‖) ^ 2 + ρ / (2 * N) * (t * ‖w‖) ^ 2 =
          t ^ 2 * (ρ * (‖u‖ ^ 2 + ‖w‖ ^ 2) / N) := by field_simp; ring
      have hε3 : ε * (0 + t * ‖u‖) * (t * ‖u‖) + ε * (t * ‖u‖ + t * ‖w‖) * (t * ‖w‖) +
          ε * (t * ‖u‖ + t * ‖w‖ + t * ‖u‖) * (t * ‖u‖) + ε * (t * ‖w‖ + t * ‖w‖) * (t * ‖w‖) ≤
          3 * ε * t ^ 2 * S ^ 2 := by
        rw [hS]
        have hu0 := norm_nonneg u
        have hw0 := norm_nonneg w
        have : 0 ≤ ε * t ^ 2 * (2 * ‖u‖ * ‖w‖ + 0) := by positivity
        nlinarith
      have hκ1 : κ * (t ^ 2 * ⟪A u, u⟫_ℝ) + κ * (t ^ 2 * ⟪A w, w⟫_ℝ) + κ * (t ^ 2 * ⟪A u, u⟫_ℝ) +
          κ * (t ^ 2 * ⟪A w, w⟫_ℝ) - t ^ 2 * ⟪A u, u⟫_ℝ - t ^ 2 * ⟪A w, w⟫_ℝ =
          t ^ 2 * (-(⟪A u, u⟫_ℝ + ⟪A w, w⟫_ℝ) / N) := by
        have : κ * 2 = 1 - 1 / N := by linarith
        field_simp
        rw [hκ]; field_simp; ring
      linear_combination s1 + s2 + s3 + s4 - hκ1 + hdiv + e3 + hε3
    -- conclude
    have ht2 : 0 < t ^ 2 := by positivity
    have hle : ⟪A u, w⟫_ℝ - ⟪A w, u⟫_ℝ ≤
        (⟪A u, u⟫_ℝ + ⟪A w, w⟫_ℝ + ρ * (‖u‖ ^ 2 + ‖w‖ ^ 2)) / N + 3 * ε * S ^ 2 := by
      have := hsum
      rw [show 3 * ε * t ^ 2 * S ^ 2 = t ^ 2 * (3 * ε * S ^ 2) by ring, ← mul_add] at this
      exact le_of_mul_le_mul_left this ht2
    have hQ1 : (⟪A u, u⟫_ℝ + ⟪A w, w⟫_ℝ + ρ * (‖u‖ ^ 2 + ‖w‖ ^ 2)) / N ≤ Q / N := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      rw [hQ]
      have h1 := le_abs_self ⟪A u, u⟫_ℝ
      have h2 := le_abs_self ⟪A w, w⟫_ℝ
      have h3 : ρ * (‖u‖ ^ 2 + ‖w‖ ^ 2) ≤ |ρ| * (‖u‖ ^ 2 + ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self ρ) (by positivity)
      linarith
    have hQ2 : Q / N < η / 2 := by
      rw [div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ hη] at hN
      nlinarith
    have hε2 : 3 * ε * S ^ 2 ≤ η / 2 := by
      have hpos : 0 < 8 * (S ^ 2 + 1) := by positivity
      have h1 : 3 * ε * S ^ 2 = η * (3 * S ^ 2 / (8 * (S ^ 2 + 1))) := by rw [hε]; ring
      have h2 : 3 * S ^ 2 / (8 * (S ^ 2 + 1)) ≤ 1 / 2 := by
        rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg S]
      rw [h1]
      nlinarith
    linarith
  have h3 : ⟪A w, u⟫_ℝ = ⟪u, A w⟫_ℝ := real_inner_comm _ _
  linarith [key u w, key w u]

end RW
