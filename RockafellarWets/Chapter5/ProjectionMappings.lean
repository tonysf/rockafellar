/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Projection Mappings

Example 5.23(a) says that the projection mapping `P_C`, sending a point to
the points of `C` nearest to it, is everywhere outer semicontinuous and
locally bounded.

The book obtains this by specializing 5.22 to the integrand
`f(w,x) = |w - x| + δ_C(w)` of 1.20.  Going through the extended-real
integrand is not necessary: outer semicontinuity is closedness of the graph
by 5.7(a), and the graph of `P_C` is visibly an intersection of closed sets,
one for each competitor `w' ∈ C`.  Local boundedness is the observation that
a nearest point cannot be farther from `x` than a fixed point of `C` is.

The printed statement of 5.23(a) asks only that `C` be nonempty, but the
result it specializes -- 1.20 -- asks for `C` nonempty *and closed*, and
closedness is genuinely needed: for `C = (0,1) ⊂ IR` the projection mapping
is the identity on `C` and empty elsewhere, so its graph is not closed.  That
counterexample is formalized below.
-/

import RockafellarWets.Chapter5.LocalBoundedness

open Bornology Filter Metric Set Topology

namespace RW

section Projections

variable {E : Type*} [NormedAddCommGroup E]

/-- **Example 1.20 / 5.23(a)**: the projection mapping `P_C(x)`, consisting of
the points of `C` nearest to `x`. -/
def projMapping (C : Set E) : E → Set E :=
  fun x ↦ {w | w ∈ C ∧ ∀ w' ∈ C, ‖w - x‖ ≤ ‖w' - x‖}

@[simp]
theorem mem_projMapping {C : Set E} {x w : E} :
    w ∈ projMapping C x ↔ w ∈ C ∧ ∀ w' ∈ C, ‖w - x‖ ≤ ‖w' - x‖ := Iff.rfl

/-- The graph of `P_C` cut out by the competitor conditions: one closed set
for membership in `C`, and one for each `w' ∈ C`. -/
theorem svGraph_projMapping (C : Set E) :
    svGraph (projMapping C) =
      {p : E × E | p.2 ∈ C} ∩ ⋂ w' ∈ C, {p : E × E | ‖p.2 - p.1‖ ≤ ‖w' - p.1‖} := by
  ext p
  simp only [mem_svGraph, mem_projMapping, mem_inter_iff, mem_setOf_eq, mem_iInter]

/-- For a closed set the graph of the projection mapping is closed. -/
theorem isClosed_svGraph_projMapping {C : Set E} (hC : IsClosed C) :
    IsClosed (svGraph (projMapping C)) := by
  rw [svGraph_projMapping]
  refine IsClosed.inter (hC.preimage continuous_snd) (isClosed_biInter fun w' _ ↦ ?_)
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- **Example 5.23(a)**: the projection mapping onto a closed set is
everywhere outer semicontinuous.  This is 5.7(a) applied to the closed graph
above; nonemptiness of `C` is not needed. -/
theorem svOsc_projMapping {C : Set E} (hC : IsClosed C) : SvOsc (projMapping C) :=
  isClosed_svGraph_iff_svOsc.1 (isClosed_svGraph_projMapping hC)

/-- **Example 5.23(a)**: the projection mapping onto a nonempty set is
everywhere locally bounded.  A nearest point to `x` is no farther from `x`
than a fixed point of `C` is, so it stays in a ball whose radius depends only
on the neighborhood.  Closedness of `C` is not needed. -/
theorem svLocallyBounded_projMapping {C : Set E} (hC : C.Nonempty) :
    SvLocallyBounded (projMapping C) := by
  obtain ⟨w₀, hw₀⟩ := hC
  intro x
  refine ⟨ball x 1, ball_mem_nhds x one_pos,
    (isBounded_closedBall (x := (0 : E)) (r := 2 * (‖x‖ + 1) + ‖w₀‖)).subset ?_⟩
  rintro w hw
  obtain ⟨z, hzball, hzC, hzmin⟩ := mem_svImage.1 hw
  have hz : ‖z‖ < ‖x‖ + 1 := by
    have h₁ : dist z x < 1 := mem_ball.1 hzball
    have h₂ : ‖z‖ ≤ ‖x‖ + dist z x := by
      simpa [dist_eq_norm] using norm_le_norm_add_norm_sub' z x
    linarith
  have hmin : ‖w - z‖ ≤ ‖w₀ - z‖ := hzmin w₀ hw₀
  have h₃ : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
  have h₄ : ‖w₀ - z‖ ≤ ‖w₀‖ + ‖z‖ := (norm_sub_le _ _).trans_eq rfl
  rw [mem_closedBall, dist_zero_right]
  linarith

variable [ProperSpace E]

/-- **Example 1.20**, the nonemptiness clause: a nonempty closed set contains a
point nearest to any given one. -/
theorem projMapping_nonempty {C : Set E} (hC : IsClosed C) (hne : C.Nonempty)
    (x : E) : (projMapping C x).Nonempty := by
  obtain ⟨w, hwC, hw⟩ := hC.exists_infDist_eq_dist hne x
  refine ⟨w, hwC, fun w' hw' ↦ ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm, dist_comm w x, dist_comm w' x, ← hw]
  exact infDist_le_dist_of_mem hw'

end Projections

section ClosednessIsNeeded

/-- The projection onto the open interval `(0,1)` is the identity on it. -/
theorem projMapping_Ioo_of_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    projMapping (Ioo (0 : ℝ) 1) x = {x} := by
  ext w
  simp only [mem_projMapping, mem_singleton_iff]
  constructor
  · rintro ⟨-, hmin⟩
    have := hmin x hx
    simpa [sub_self, norm_le_zero_iff, sub_eq_zero] using this
  · rintro rfl
    exact ⟨hx, fun w' _ ↦ by simp [sub_self]⟩

/-- The projection onto the open interval `(0,1)` is empty at `0`: no point of
the interval is nearest to `0`. -/
theorem projMapping_Ioo_zero : projMapping (Ioo (0 : ℝ) 1) 0 = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro w ⟨⟨hw0, hw1⟩, hmin⟩
  have hhalf : w / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have := hmin _ hhalf
  rw [sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hw0, abs_of_pos (by linarith)] at this
  linarith

/-- Closedness of `C` cannot be dropped from 5.23(a): the projection onto
`(0,1)` is not outer semicontinuous at `0`, since points of the interval
approaching `0` are their own projections while `P_C(0)` is empty. -/
theorem not_svOsc_projMapping_Ioo : ¬ SvOsc (projMapping (Ioo (0 : ℝ) 1)) := by
  intro h
  have hmem : (0 : ℝ) ∈ svOuterLimit (projMapping (Ioo (0 : ℝ) 1)) 0 := by
    intro W hW
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hW)
    refine ⟨min (ε / 2) (1 / 2), ?_, ?_⟩
    · exact (hεsub (by
        rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith))).1
    · have hx : min (ε / 2) (1 / 2) ∈ Ioo (0 : ℝ) 1 :=
        ⟨by positivity, lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
      rw [projMapping_Ioo_of_mem hx]
      refine ⟨min (ε / 2) (1 / 2), rfl, ?_⟩
      exact (hεsub (by
        rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith))).2
  have := h 0 hmem
  rw [projMapping_Ioo_zero] at this
  exact this

end ClosednessIsNeeded

end RW
