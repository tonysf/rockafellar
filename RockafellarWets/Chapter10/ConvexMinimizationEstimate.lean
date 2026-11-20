/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: a minimization estimate for convex functions

**Proposition 10.59**: for a proper lsc convex `f` with `argmin f ≠ ∅` and any `x`,
`f(x) - inf f ≤ d(x, argmin f) · d(0, ∂f(x))` (`sub_inf_le_infDist_mul_infDist`), stated for
`x` with `f(x)` finite and `∂f(x) ≠ ∅`, and at every `x` in `ℝ≥0∞`
(`sub_inf_toENNReal_le_infEDist_mul_infEDist`) with the book's conventions `d(0, ∅) = ∞` and
`0 · ∞ = 0`: if `∂f(x) = ∅` then either `x ∈ argmin f` (left side `0`) or `d(x, argmin f) > 0`
(right side `∞`).

The proof uses the convex subgradient inequality 8.12 directly, with points of `argmin f` and
of `∂f(x)` attaining the two distances (both sets are closed and nonempty); the book derives the
same inequality through 10.9, 8.27 and 10.1.
-/

import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.SubgradientRelationships

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The minimizers of a function with finite infimum form its lowest sublevel set. -/
theorem argmin_eq_sublevel {f : E → EReal} {m : ℝ} (hm : ⨅ y, f y = (m : EReal)) :
    argmin f = {y | f y ≤ (m : EReal)} := by
  ext y
  simp only [mem_argmin_iff, mem_setOf_eq, hm]
  constructor
  · rintro ⟨h, -⟩
    exact h.le
  · intro h
    exact ⟨le_antisymm h (hm ▸ iInf_le f y), EReal.coe_lt_top m⟩

/-- **Proposition 10.59** (minimization estimate for a convex function). -/
theorem sub_inf_le_infDist_mul_infDist {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (hne : (argmin f).Nonempty)
    {x : E} {a : ℝ} (hx : f x = a) (hsub : (subdifferential f x).Nonempty) :
    a - (⨅ y, f y).toReal ≤ infDist x (argmin f) * infDist 0 (subdifferential f x) := by
  obtain ⟨y₀, hy₀⟩ := hne
  have hy₀' := (mem_argmin_iff f y₀).1 hy₀
  have hbot : (⨅ y, f y) ≠ ⊥ := by rw [← hy₀'.1]; exact ne_of_gt (hp.2 y₀)
  set m := (⨅ y, f y).toReal with hmdef
  have hm : ⨅ y, f y = (m : EReal) := (EReal.coe_toReal (ne_of_lt hy₀'.2) hbot).symm
  have hargmin := argmin_eq_sublevel hm
  have hclosed : IsClosed (argmin f) := by
    rw [hargmin]
    exact hl.isClosed_preimage (m : EReal)
  obtain ⟨y, hy, hyd⟩ := hclosed.exists_infDist_eq_dist ⟨y₀, hy₀⟩ x
  have hsubclosed : IsClosed (subdifferential f x) :=
    (subdifferential_properties (f := f) (x := x) (c := a) hx).2.2.1
  obtain ⟨v, hv, hvd⟩ := hsubclosed.exists_infDist_eq_dist hsub 0
  have hfy : f y = (m : EReal) := by
    have h1 := (mem_argmin_iff f y).1 hy
    rw [h1.1, hm]
  have hineq := (mem_subdifferential_iff_of_convex hc hp hx).1 hv y
  rw [hfy, EReal.coe_le_coe_iff] at hineq
  rw [hyd, hvd, dist_zero_left, dist_comm, dist_eq_norm]
  have hcs : -⟪v, y - x⟫_ℝ ≤ ‖v‖ * ‖y - x‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm v (y - x))
  nlinarith

/-- **Proposition 10.59** at every point `x`, in `ℝ≥0∞` with the book's conventions: the left side
is `f(x) - inf f` (`∞` when `f(x) = ∞`), distances to the empty set are `∞`, and `0 · ∞ = 0`. -/
theorem sub_inf_toENNReal_le_infEDist_mul_infEDist {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (hne : (argmin f).Nonempty)
    (x : E) :
    (f x - ⨅ y, f y).toENNReal ≤ infEDist x (argmin f) * infEDist 0 (subdifferential f x) := by
  obtain ⟨y₀, hy₀⟩ := id hne
  have hy₀' := (mem_argmin_iff f y₀).1 hy₀
  have hbot : (⨅ y, f y) ≠ ⊥ := by rw [← hy₀'.1]; exact ne_of_gt (hp.2 y₀)
  set m := (⨅ y, f y).toReal with hmdef
  have hm : ⨅ y, f y = (m : EReal) := (EReal.coe_toReal (ne_of_lt hy₀'.2) hbot).symm
  have hargmin := argmin_eq_sublevel hm
  have hclosed : IsClosed (argmin f) := by
    rw [hargmin]
    exact hl.isClosed_preimage (m : EReal)
  have hempty : ∀ v, v ∈ subdifferential f x → ∃ c : ℝ, f x = c := fun v hv ↦ hv.1
  by_cases hxtop : f x = ⊤
  · have hsub : subdifferential f x = ∅ := by
      ext v
      simp only [mem_empty_iff_false, iff_false]
      intro hv
      obtain ⟨c', hc'⟩ := hempty v hv
      rw [hxtop] at hc'
      exact EReal.coe_ne_top c' hc'.symm
    have hxA : x ∉ argmin f := by
      rw [hargmin, mem_setOf_eq, hxtop, top_le_iff]
      exact EReal.coe_ne_top m
    have hd : infEDist x (argmin f) ≠ 0 := fun h ↦ hxA ((mem_iff_infEDist_zero_of_closed hclosed).2 h)
    rw [hsub, infEDist_empty, ENNReal.mul_top hd]
    exact le_top
  · obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = a :=
      ⟨(f x).toReal, (EReal.coe_toReal hxtop (ne_of_gt (hp.2 x))).symm⟩
    rw [ha, hm, ← EReal.coe_sub, EReal.real_coe_toENNReal]
    by_cases hsub : (subdifferential f x).Nonempty
    · have h := sub_inf_le_infDist_mul_infDist hp hl hc hne ha hsub
      rw [← hmdef] at h
      calc ENNReal.ofReal (a - m) ≤ ENNReal.ofReal (infDist x (argmin f) *
            infDist 0 (subdifferential f x)) := ENNReal.ofReal_le_ofReal h
        _ = infEDist x (argmin f) * infEDist 0 (subdifferential f x) := by
          rw [ENNReal.ofReal_mul infDist_nonneg, infDist, infDist,
            ENNReal.ofReal_toReal (infEDist_ne_top hne),
            ENNReal.ofReal_toReal (infEDist_ne_top hsub)]
    · rw [not_nonempty_iff_eq_empty.1 hsub, infEDist_empty]
      by_cases hxA : x ∈ argmin f
      · have hle : a ≤ m := by
          have h := hxA
          rw [hargmin, mem_setOf_eq, ha, EReal.coe_le_coe_iff] at h
          exact h
        rw [ENNReal.ofReal_of_nonpos (by linarith)]
        exact zero_le _
      · have hd : infEDist x (argmin f) ≠ 0 := fun h ↦
          hxA ((mem_iff_infEDist_zero_of_closed hclosed).2 h)
        rw [ENNReal.mul_top hd]
        exact le_top

end RW
