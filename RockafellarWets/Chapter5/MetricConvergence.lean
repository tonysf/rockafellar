/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Metric Descriptions of Convergence

Proposition 5.49, which reads Definition 5.41 through the integrated set
metric `dl` of 4(12).

Everything rests on one sandwich, proved once in the opening section and used
in both directions of both clauses.  Above, 4.41(a) says that `dl` dominates
`e^{-ρ} dl_ρ`, so a small `dl` forces the `ε`-inclusions on `ρ IB` -- with no
hypothesis beyond nonemptiness, and with a tolerance that degrades by the
harmless factor `e^{-ρ}`.  Below, 4.41(b) says that `dl` is at most
`dl_ρ` plus the tail `e^{-ρ}(β + ρ + 1)`, where `β` bounds the distances of
the two sets from the origin; the `ε`-inclusions on the larger ball
`(2ρ + β) IB` control `dl_ρ` through 4.37(a), and the tail is made small by
taking `ρ` large.

That asymmetry is the whole story of the proposition.  The upper estimate is
not uniform in the sets: its radius `2ρ + β` and its tail both depend on
`β`.  In clause (a) this costs nothing, because the target `S(x̄)` is *fixed*
and continuous convergence itself bounds `d(0, Sν(x))` near `x̄` -- one
application of the inclusions at radius `d(0, S(x̄)) + 1` does it.  In clause
(b) the target `S(x)` moves with `x`, and there is nothing to stop
`d(0, S(x))` from being unbounded over `X`; the printed statement is then
false, and `svConvergesUniformlyOn_not_integratedSetDistance` exhibits a
uniformly convergent sequence whose `dl`-discrepancies are unbounded on `X`.
The direction that fails is exactly the one the book proves by fixing `x` and
contradicting a *pointwise* statement.  Clause (b) is therefore stated with
`d(0, S(·))` bounded on `X`, which is what the book's `β` silently assumes;
the converse direction needs nothing.
-/

import RockafellarWets.Chapter4.IntegratedSetDistance
import RockafellarWets.Chapter5.ContinuousUniformConvergence

open Filter Metric Set Topology
open scoped NNReal

namespace RW

section Sandwich

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Lemma 4.41(a) in inclusion form.**  A small integrated distance forces
the `ε`-inclusions of Definition 5.41 on `ρ IB`, the tolerance degrading only
by the factor `e^{-ρ}`.  Neither set need be closed. -/
theorem inter_closedBall_subset_thickening_of_integratedSetDistance_le
    {C D : Set F} (hCne : C.Nonempty) (hDne : D.Nonempty)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (h : integratedSetDistance C D ≤ Real.exp (-ρ) * (ε / 2)) :
    C ∩ closedBall 0 ρ ⊆ thickening ε D ∧
      D ∩ closedBall 0 ρ ⊆ thickening ε C := by
  have hexp : 0 < Real.exp (-ρ) := Real.exp_pos _
  -- 4.41(a), with the nonnegative first summand dropped.
  have hlow := integratedSetDistance_ge hρ C D
  have habs : 0 ≤ (1 - Real.exp (-ρ)) * |infDist 0 C - infDist 0 D| := by
    have h1 : Real.exp (-ρ) ≤ 1 := by
      simpa using Real.exp_le_one_iff.2 (neg_nonpos.2 hρ)
    exact mul_nonneg (by linarith) (abs_nonneg _)
  have hrho : rhoDistanceReal ρ C D ≤ ε / 2 := by
    nlinarith [hlow, habs, h, hexp]
  -- Read the uniform bound on the distance functions pointwise.
  have hball : closedBall (0 : F) ((ρ.toNNReal : ℝ)) = closedBall (0 : F) ρ := by
    rw [Real.coe_toNNReal ρ hρ]
  have hkey : ∀ z ∈ closedBall (0 : F) ρ,
      |infDist z C - infDist z D| ≤ ε / 2 := by
    intro z hz
    refine le_trans ?_ hrho
    exact abs_infDist_sub_infDist_le_rhoDistance ρ.toNNReal C D (by rwa [hball])
  constructor
  · rintro z ⟨hzC, hzball⟩
    have h0 : infDist z C = 0 := infDist_zero_of_mem hzC
    have := hkey z hzball
    rw [h0, zero_sub, abs_neg, abs_of_nonneg infDist_nonneg] at this
    exact Metric.mem_thickening_iff.2 ((infDist_lt_iff hDne).1 (by linarith))
  · rintro z ⟨hzD, hzball⟩
    have h0 : infDist z D = 0 := infDist_zero_of_mem hzD
    have := hkey z hzball
    rw [h0, sub_zero, abs_of_nonneg infDist_nonneg] at this
    exact Metric.mem_thickening_iff.2 ((infDist_lt_iff hCne).1 (by linarith))

/-- **Lemma 4.41(b) in inclusion form.**  The `ε`-inclusions on the ball of
radius `2ρ + β`, where `β` bounds both distances from the origin, bound the
integrated distance by the tolerance plus the tail `e^{-ρ}(β + ρ + 1)`. -/
theorem integratedSetDistance_le_of_inter_closedBall_subset
    {C D : Set F} (hC : IsClosed C) (hD : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    {β ρ e : ℝ} (hρ : 0 ≤ ρ) (he : 0 ≤ e)
    (hβ : max (infDist 0 C) (infDist 0 D) ≤ β)
    (hCD : C ∩ closedBall 0 (2 * ρ + β) ⊆ cthickening e D)
    (hDC : D ∩ closedBall 0 (2 * ρ + β) ⊆ cthickening e C) :
    integratedSetDistance C D ≤ e + Real.exp (-ρ) * (β + ρ + 1) := by
  have hβ0 : 0 ≤ β := le_trans (le_max_of_le_left infDist_nonneg) hβ
  have hs : (0 : ℝ) ≤ 2 * ρ + β := by linarith
  have hscoe : (((2 * ρ + β).toNNReal : ℝ)) = 2 * ρ + β := Real.coe_toNNReal _ hs
  have hrcoe : ((ρ.toNNReal : ℝ)) = ρ := Real.coe_toNNReal ρ hρ
  -- 4.37(a): the truncated-inclusion distance at the larger radius bounds
  -- the uniform distance at the smaller one.
  have hhat : rhoHatDistance (2 * ρ + β).toNNReal C D ≤ e :=
    (rhoHatDistance_le_iff _ hCne hDne he).2 (by rw [hscoe]; exact ⟨hCD, hDC⟩)
  have hrho : rhoDistanceReal ρ C D ≤ e := by
    refine le_trans ?_ hhat
    refine rhoDistance_le_rhoHatDistance_of_two_mul hC hD hCne hDne ?_
    rw [hscoe, hrcoe]
    linarith
  -- 4.41(b), with `β` replacing the maximum and the near part bounded by `e`.
  have hup := integratedSetDistance_le hρ C D
  have hexp : 0 < Real.exp (-ρ) := Real.exp_pos _
  have hexp1 : Real.exp (-ρ) ≤ 1 := by
    simpa using Real.exp_le_one_iff.2 (neg_nonpos.2 hρ)
  nlinarith [hup, hrho, hβ, rhoDistanceReal_nonneg ρ C D]

/-- The tail of 4.41(b) can be made arbitrarily small by taking the
truncation radius large. -/
theorem exists_radius_exp_neg_mul_lt (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ Real.exp (-ρ) * (β + ρ + 1) < ε := by
  have h := (tendsto_affine_mul_exp_neg_atTop β).eventually (gt_mem_nhds hε)
  obtain ⟨ρ, hρ0, hρ⟩ := (h.and (eventually_ge_atTop (0 : ℝ))).exists
  exact ⟨ρ, hρ, by rw [mul_comm]; exact hρ0⟩

end Sandwich

section ContinuousConvergence

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {x : E}

/-- Continuous convergence at `x̄` keeps the values `Sν(x)` for `x` near `x̄` at
a bounded distance from the origin.  This is what supplies the `β` of 4.41(b)
in clause (a) of 5.49, and it is available only because the target `S(x̄)` does
not move. -/
theorem SvConvergesContinuouslyAt.exists_bound_infDist_zero
    (hScl : IsClosed (S x)) (hSne : (S x).Nonempty)
    (h : SvConvergesContinuouslyAt Sseq S x) :
    ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V,
      max (infDist 0 (Sseq n y)) (infDist 0 (S x)) ≤ infDist 0 (S x) + 2 := by
  set b := infDist (0 : F) (S x) with hb
  have hb0 : 0 ≤ b := infDist_nonneg
  obtain ⟨V, hV, hn⟩ :=
    (svConvergesContinuouslyAt_iff hScl).1 h 1 one_pos (b + 1) (by linarith)
  refine ⟨V, hV, hn.mono fun n hn y hy ↦ ?_⟩
  refine max_le ?_ (by linarith)
  obtain ⟨w, hwS, hw⟩ := (infDist_lt_iff hSne).1 (show b < b + 1 by linarith)
  rw [dist_zero_left] at hw
  obtain ⟨z, hz, hwz⟩ := Metric.mem_thickening_iff.1
    ((hn y hy).2 ⟨hwS, by simp only [mem_closedBall, dist_zero_right]; linarith⟩)
  calc infDist (0 : F) (Sseq n y) ≤ dist 0 z := infDist_le_dist_of_mem hz
    _ ≤ dist 0 w + dist w z := dist_triangle _ _ _
    _ = ‖w‖ + dist w z := by rw [dist_zero_left]
    _ ≤ b + 2 := by linarith

/-- **Proposition 5.49(a)**: continuous convergence at `x̄` is uniform
smallness of the integrated distance `dl(Sν(x), S(x̄))` for `x` near `x̄`. -/
theorem svConvergesContinuouslyAt_iff_eventually_integratedSetDistance_le
    (hScl : IsClosed (S x)) (hSne : (S x).Nonempty)
    (hcl : ∀ n y, IsClosed (Sseq n y)) (hne : ∀ n y, (Sseq n y).Nonempty) :
    SvConvergesContinuouslyAt Sseq S x ↔
      ∀ ε > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V,
        integratedSetDistance (Sseq n y) (S x) ≤ ε := by
  constructor
  · intro h ε hε
    set b := infDist (0 : F) (S x) with hb
    have hb0 : 0 ≤ b := infDist_nonneg
    set β := b + 2 with hβdef
    have hβ0 : 0 < β := by simp only [hβdef]; linarith
    obtain ⟨ρ, hρ0, hρ⟩ := exists_radius_exp_neg_mul_lt β (half_pos hε)
    obtain ⟨V₀, hV₀, hn₀⟩ := h.exists_bound_infDist_zero hScl hSne
    obtain ⟨V₁, hV₁, hn₁⟩ := (svConvergesContinuouslyAt_iff hScl).1 h
      (ε / 2) (half_pos hε) (2 * ρ + β) (by linarith)
    refine ⟨V₀ ∩ V₁, Filter.inter_mem hV₀ hV₁, ?_⟩
    filter_upwards [hn₀, hn₁] with n h₀ h₁ y hy
    have hincl := h₁ y hy.2
    have hbound := h₀ y hy.1
    have := integratedSetDistance_le_of_inter_closedBall_subset
      (hcl n y) hScl (hne n y) hSne hρ0 (le_of_lt (half_pos hε)) hbound
      (hincl.1.trans (thickening_subset_cthickening _ _))
      (hincl.2.trans (thickening_subset_cthickening _ _))
    linarith
  · intro h
    refine (svConvergesContinuouslyAt_iff hScl).2 fun ε hε ρ hρ ↦ ?_
    obtain ⟨V, hV, hn⟩ := h (Real.exp (-ρ) * (ε / 2))
      (by positivity)
    exact ⟨V, hV, hn.mono fun n hn y hy ↦
      inter_closedBall_subset_thickening_of_integratedSetDistance_le
        (hne n y) hSne hε hρ.le (hn y hy)⟩

end ContinuousConvergence

section UniformConvergence

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E}

omit [PseudoMetricSpace E] in
/-- **Proposition 5.49(b)**, the direction that holds unconditionally:
uniformly small integrated distances give uniform convergence.  This is
4.41(a) alone, so neither mapping need be closed-valued. -/
theorem svConvergesUniformlyOn_of_eventually_integratedSetDistance_le
    (hSne : ∀ z ∈ X, (S z).Nonempty) (hne : ∀ n, ∀ z ∈ X, (Sseq n z).Nonempty)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ X,
      integratedSetDistance (Sseq n z) (S z) ≤ ε) :
    SvConvergesUniformlyOn Sseq S X := by
  intro ε hε ρ hρ
  filter_upwards [h (Real.exp (-ρ) * (ε / 2)) (by positivity)] with n hn z hz
  exact inter_closedBall_subset_thickening_of_integratedSetDistance_le
    (hne n z hz) (hSne z hz) hε hρ.le (hn z hz)

omit [PseudoMetricSpace E] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Under uniform convergence, a bound on `d(0, S(x))` over `X` spreads to the
approximating values.  This supplies the `β` of 4.41(b) uniformly in `x`. -/
theorem SvConvergesUniformlyOn.eventually_bound_infDist_zero
    (hSne : ∀ z ∈ X, (S z).Nonempty) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z ∈ X, infDist 0 (S z) ≤ b)
    (h : SvConvergesUniformlyOn Sseq S X) :
    ∀ᶠ n in atTop, ∀ z ∈ X,
      max (infDist 0 (Sseq n z)) (infDist 0 (S z)) ≤ b + 2 := by
  filter_upwards [h 1 one_pos (b + 1) (by linarith)] with n hn z hz
  refine max_le ?_ (le_trans (hb z hz) (by linarith))
  obtain ⟨w, hwS, hw⟩ := (infDist_lt_iff (hSne z hz)).1
    (show infDist (0 : F) (S z) < b + 1 from lt_of_le_of_lt (hb z hz) (by linarith))
  rw [dist_zero_left] at hw
  obtain ⟨v, hv, hwv⟩ := Metric.mem_thickening_iff.1
    ((hn z hz).2 ⟨hwS, by simp only [mem_closedBall, dist_zero_right]; linarith⟩)
  calc infDist (0 : F) (Sseq n z) ≤ dist 0 v := infDist_le_dist_of_mem hv
    _ ≤ dist 0 w + dist w v := dist_triangle _ _ _
    _ = ‖w‖ + dist w v := by rw [dist_zero_left]
    _ ≤ b + 2 := by linarith

omit [PseudoMetricSpace E] in
/-- **Proposition 5.49(b)**, the direction the book proves, with the
hypothesis its proof silently uses: `d(0, S(·))` bounded on `X`.  Without it
the statement is false; see
`svConvergesUniformlyOn_not_integratedSetDistance`. -/
theorem eventually_integratedSetDistance_le_of_svConvergesUniformlyOn
    (hScl : ∀ z ∈ X, IsClosed (S z)) (hSne : ∀ z ∈ X, (S z).Nonempty)
    (hcl : ∀ n, ∀ z ∈ X, IsClosed (Sseq n z))
    (hne : ∀ n, ∀ z ∈ X, (Sseq n z).Nonempty)
    {b : ℝ} (hb : ∀ z ∈ X, infDist 0 (S z) ≤ b)
    (h : SvConvergesUniformlyOn Sseq S X) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ X,
      integratedSetDistance (Sseq n z) (S z) ≤ ε := by
  intro ε hε
  set c := max b 0 with hc
  have hc0 : (0 : ℝ) ≤ c := le_max_right _ _
  have hcb : ∀ z ∈ X, infDist 0 (S z) ≤ c :=
    fun z hz ↦ (hb z hz).trans (le_max_left _ _)
  obtain ⟨ρ, hρ0, hρ⟩ := exists_radius_exp_neg_mul_lt (c + 2) (half_pos hε)
  have hβ0 : (0 : ℝ) < 2 * ρ + (c + 2) := by linarith
  filter_upwards [h.eventually_bound_infDist_zero hSne hc0 hcb,
    h (ε / 2) (half_pos hε) (2 * ρ + (c + 2)) hβ0] with n h₀ h₁ z hz
  have hincl := h₁ z hz
  have := integratedSetDistance_le_of_inter_closedBall_subset
    (hcl n z hz) (hScl z hz) (hne n z hz) (hSne z hz) hρ0
    (le_of_lt (half_pos hε)) (h₀ z hz)
    (hincl.1.trans (thickening_subset_cthickening _ _))
    (hincl.2.trans (thickening_subset_cthickening _ _))
  linarith

omit [PseudoMetricSpace E] in
/-- **Proposition 5.49(b)** under the hypothesis its proof needs. -/
theorem svConvergesUniformlyOn_iff_eventually_integratedSetDistance_le
    (hScl : ∀ z ∈ X, IsClosed (S z)) (hSne : ∀ z ∈ X, (S z).Nonempty)
    (hcl : ∀ n, ∀ z ∈ X, IsClosed (Sseq n z))
    (hne : ∀ n, ∀ z ∈ X, (Sseq n z).Nonempty)
    {b : ℝ} (hb : ∀ z ∈ X, infDist 0 (S z) ≤ b) :
    SvConvergesUniformlyOn Sseq S X ↔
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ X,
        integratedSetDistance (Sseq n z) (S z) ≤ ε :=
  ⟨eventually_integratedSetDistance_le_of_svConvergesUniformlyOn hScl hSne hcl
      hne hb,
    svConvergesUniformlyOn_of_eventually_integratedSetDistance_le hSne hne⟩

omit [PseudoMetricSpace E] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The bound required by 5.49(b) holds whenever the limit mapping carries `X`
into a bounded set -- in particular whenever `X` is bounded and `S` is locally
bounded, by 5.15. -/
theorem forall_infDist_zero_le_of_forall_norm_le {b : ℝ} (hb0 : 0 ≤ b)
    (h : ∀ z ∈ X, ∀ u ∈ S z, ‖u‖ ≤ b) : ∀ z ∈ X, infDist 0 (S z) ≤ b := by
  intro z hz
  rcases eq_empty_or_nonempty (S z) with hSz | ⟨u, hu⟩
  · rw [hSz, infDist_empty]
    exact hb0
  · calc infDist (0 : F) (S z) ≤ dist 0 u := infDist_le_dist_of_mem hu
      _ = ‖u‖ := by rw [dist_zero_left]
      _ ≤ b := h z hz u hu

end UniformConvergence

section Necessity

/-- The witness for 5.49(b): on `X = [1, ∞)`, the mapping `S(x) = {2x}` is
approximated by `Sν(x) = {x}` once `x ≥ ν`, and by `S(x)` itself before that.
The discrepancy is pushed out of every fixed ball as `ν` grows, so the
convergence is uniform on all of `X`; but at `x = ν` the two values sit at
distances `ν` and `2ν` from the origin, and `dl` sees that gap at every
radius. -/
noncomputable def escapingUniformWitness (n : ℕ) (z : ℝ) : Set ℝ :=
  if (n : ℝ) ≤ z then {z} else {2 * z}

/-- **5.49(b) is false as printed.**  A sequence converging uniformly on `X`
whose integrated distances `dl(Sν(x), S(x))` are unbounded over `X` for every
`ν`.  What fails is the direction proved in the book by fixing `x`: the
argument's `β = d(0, S(x))` is a bound only at that one point, and here it is
unbounded over `X`. -/
theorem svConvergesUniformlyOn_not_integratedSetDistance :
    ∃ (Sseq : ℕ → ℝ → Set ℝ) (S : ℝ → Set ℝ) (X : Set ℝ),
      (∀ n z, IsClosed (Sseq n z)) ∧ (∀ z, IsClosed (S z)) ∧
        (∀ n z, (Sseq n z).Nonempty) ∧ (∀ z, (S z).Nonempty) ∧
        SvConvergesUniformlyOn Sseq S X ∧
        ¬ ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ X,
            integratedSetDistance (Sseq n z) (S z) ≤ ε := by
  refine ⟨escapingUniformWitness, fun z ↦ {2 * z}, Ici 1, ?_, fun _ ↦
    isClosed_singleton, ?_, fun _ ↦ singleton_nonempty _, ?_, ?_⟩
  · intro n z
    rw [escapingUniformWitness]
    split <;> exact isClosed_singleton
  · intro n z
    rw [escapingUniformWitness]
    split <;> exact singleton_nonempty _
  · -- Uniform convergence: past the radius `ρ`, the discrepancy is invisible.
    intro ε hε ρ hρ
    obtain ⟨N, hN⟩ := exists_nat_gt ρ
    filter_upwards [eventually_ge_atTop N] with n hn z hz
    rw [mem_Ici] at hz
    have hnρ : ρ < (n : ℝ) := lt_of_lt_of_le hN (Nat.cast_le.2 hn)
    rw [escapingUniformWitness]
    split
    · rename_i hnz
      have hzρ : ρ < z := lt_of_lt_of_le hnρ hnz
      constructor
      · rintro w ⟨rfl, hwb⟩
        rw [mem_closedBall_zero_iff, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)] at hwb
        linarith
      · rintro w ⟨rfl, hwb⟩
        rw [mem_closedBall_zero_iff, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)] at hwb
        linarith
    · exact ⟨inter_subset_left.trans (self_subset_thickening hε _),
        inter_subset_left.trans (self_subset_thickening hε _)⟩
  · -- At `x = ν` the two values are `{ν}` and `{2ν}`, so `dl ≥ ν`.
    intro hcon
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hcon 1 one_pos)
    set n := max N 2 with hn
    have hn2 : 2 ≤ n := le_max_right _ _
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hmem : (n : ℝ) ∈ Ici (1 : ℝ) := mem_Ici.2 (by linarith)
    have hval : escapingUniformWitness n (n : ℝ) = {(n : ℝ)} := by
      rw [escapingUniformWitness, if_pos le_rfl]
    have hle := hN n (le_max_left _ _) (n : ℝ) hmem
    rw [hval] at hle
    have hgap := abs_infDist_zero_sub_le_integratedSetDistance
      ({(n : ℝ)} : Set ℝ) ({2 * (n : ℝ)} : Set ℝ)
    rw [infDist_singleton, infDist_singleton, Real.dist_eq, Real.dist_eq,
      zero_sub, zero_sub, abs_neg, abs_neg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ)),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (n : ℝ)),
      abs_of_nonpos (by linarith : (n : ℝ) - 2 * (n : ℝ) ≤ 0)] at hgap
    linarith

end Necessity

end RW
