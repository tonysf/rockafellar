/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Rational hit-and-miss tests

This file proves the countable rational-coordinate reduction in Theorem
4.5(c), specialized to the book's coordinate model `Fin d → ℝ`.
-/

import RockafellarWets.Chapter4.HitAndMiss

open Filter Metric Set Topology

namespace RW

/-- A point all of whose coordinates are rational. -/
def rationalCoordinatePoint {d : ℕ} (q : Fin d → ℚ) : Fin d → ℝ :=
  fun i ↦ (q i : ℝ)

private theorem exists_rationalCoordinatePoint_dist_lt {d : ℕ}
    (x : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Fin d → ℚ, dist x (rationalCoordinatePoint q) < ε := by
  choose q hq using fun i : Fin d ↦ exists_rat_near (x i) hε
  refine ⟨q, (dist_pi_lt_iff hε).2 fun i ↦ ?_⟩
  simpa only [rationalCoordinatePoint, Real.dist_eq] using hq i

/-- **Theorem 4.5(c), hit half.** It suffices to test inner-limit hits on
balls with rational radii and rational-coordinate centers. -/
theorem subset_innerSetLimit_iff_eventually_hits_rational_balls
    {d : ℕ} {C : Set (Fin d → ℝ)} {Cseq : ℕ → Set (Fin d → ℝ)} :
    C ⊆ innerSetLimit Cseq ↔
      ∀ q : Fin d → ℚ, ∀ ρ : ℚ, 0 < ρ →
        (C ∩ ball (rationalCoordinatePoint q) (ρ : ℝ)).Nonempty →
          ∀ᶠ n in atTop,
            (Cseq n ∩ ball (rationalCoordinatePoint q) (ρ : ℝ)).Nonempty := by
  constructor
  · intro h q ρ hρ hhit
    exact (subset_innerSetLimit_iff_eventually_hits_ball.1 h)
      (rationalCoordinatePoint q) (ρ : ℝ) (by exact_mod_cast hρ) hhit
  · intro h
    apply subset_innerSetLimit_iff_eventually_hits_ball.2
    intro x ε hε
    rintro ⟨z, hzC, hzBall⟩
    have hδ : 0 < ε - dist z x := by
      rw [mem_ball] at hzBall
      linarith
    rcases exists_rationalCoordinatePoint_dist_lt z (half_pos hδ) with
      ⟨q, hzq⟩
    let c : Fin d → ℝ := rationalCoordinatePoint q
    have hzc : dist z c < (ε - dist z x) / 2 := by
      simpa only [c] using hzq
    have hinterval : dist z c < ε - dist c x := by
      have htri : dist c x ≤ dist c z + dist z x := dist_triangle _ _ _
      rw [dist_comm c z] at htri
      linarith
    obtain ⟨ρ, hzρ, hρε⟩ := exists_rat_btwn hinterval
    have hρpos : 0 < ρ := by
      exact_mod_cast (dist_nonneg.trans_lt hzρ)
    have hhit :
        (C ∩ ball c (ρ : ℝ)).Nonempty :=
      ⟨z, hzC, by simpa only [mem_ball, dist_comm] using hzρ⟩
    exact (h q ρ hρpos hhit).mono fun n ⟨y, hyC, hyBall⟩ ↦ by
      refine ⟨y, hyC, ?_⟩
      rw [mem_ball] at hyBall ⊢
      have htri : dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
      linarith

/-- **Theorem 4.5(c), miss half.** It suffices to test outer-limit misses on
closed balls with rational radii and rational-coordinate centers. -/
theorem outerSetLimit_subset_iff_eventually_misses_rational_closedBalls
    {d : ℕ} {C : Set (Fin d → ℝ)} {Cseq : ℕ → Set (Fin d → ℝ)}
    (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔
      ∀ q : Fin d → ℚ, ∀ ρ : ℚ, 0 < ρ →
        Disjoint C (closedBall (rationalCoordinatePoint q) (ρ : ℝ)) →
          ∀ᶠ n in atTop,
            Disjoint (Cseq n)
              (closedBall (rationalCoordinatePoint q) (ρ : ℝ)) := by
  constructor
  · intro h q ρ _hρ hdisj
    exact (outerSetLimit_subset_iff_eventually_misses_closedBall hC).1 h
      (rationalCoordinatePoint q) (ρ : ℝ) hdisj
  · intro h x hxOuter
    by_contra hxC
    have hxCompl : Cᶜ ∈ nhds x := hC.isOpen_compl.mem_nhds hxC
    rcases Metric.mem_nhds_iff.1 hxCompl with ⟨δ, hδ, hballCompl⟩
    let ε : ℝ := δ / 4
    have hε : 0 < ε := by dsimp [ε]; positivity
    rcases exists_rationalCoordinatePoint_dist_lt x (half_pos hε) with
      ⟨q, hxq⟩
    let c : Fin d → ℝ := rationalCoordinatePoint q
    have hxc : dist x c < ε / 2 := hxq
    obtain ⟨ρ, hxcρ, hρε⟩ := exists_rat_btwn (hxc.trans (half_lt_self hε))
    have hρpos : 0 < ρ := by
      exact_mod_cast (dist_nonneg.trans_lt hxcρ)
    have hCball : Disjoint C (closedBall c (ρ : ℝ)) := by
      rw [Set.disjoint_left]
      intro y hyC hyBall
      apply hballCompl ?_ hyC
      rw [mem_closedBall] at hyBall
      rw [mem_ball]
      have htri : dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
      rw [dist_comm c x] at htri
      dsimp [ε] at hxc hρε
      linarith
    have hmiss := h q ρ hρpos hCball
    have hxOpen : x ∈ ball c (ρ : ℝ) := by
      simpa only [mem_ball] using hxcρ
    have hhit := hxOuter (ball c (ρ : ℝ)) (isOpen_ball.mem_nhds hxOpen)
    rcases (hhit.and_eventually hmiss).exists with
      ⟨n, ⟨y, hyCseq, hyBall⟩, hn⟩
    exact hn.le_bot ⟨hyCseq, ball_subset_closedBall hyBall⟩

end RW
