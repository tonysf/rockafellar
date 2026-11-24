/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: piecewise linear-quadratic optimization

**Theorem 11.42**: for a proper, convex, piecewise linear-quadratic `f` on `E × P`, with primal
problem `φ = f(·, 0)`, dual problem `ψ = -f*(0, ·)`, and value functions `p(u) = inf_x f(x, u)`,
`q(v) = inf_y f*(v, y)`: if `inf φ` or `sup ψ` is finite, then both are finite and equal and both
are attained, and the optimal pairs are characterized by `(0, ȳ) ∈ ∂f(x̄, 0)`, by
`(x̄, 0) ∈ ∂f*(0, ȳ)`, and by `argmin φ = ∂q(0)`, `argmax ψ = ∂p(0)`
(`piecewiseLinearQuadratic_optimization`).

As in the book, this parallels Theorem 11.39, the closedness `p** = p` or `q** = q` coming from
Proposition 11.32(c) (applied to `f` and to `f*`) instead of interiority conditions.
-/

import RockafellarWets.Chapter11.PiecewiseLinearQuadraticOperations
import RockafellarWets.Chapter11.PrimalDualOptimality

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Maximizers of `-g` are minimizers of `g`. -/
theorem argmax_neg_eq_argmin (g : P → EReal) : argmax (fun y ↦ -g y) = argmin g := by
  have he : (⨆ y, -g y) = -(⨅ y, g y) := by
    simpa using (ereal_coe_sub_iInf 0 g).symm
  ext y
  change ((-g y = ⨆ z, -g z) ∧ ⊥ < ⨆ z, -g z) ↔ (g y = ⨅ z, g z ∧ (⨅ z, g z) < ⊤)
  rw [he, neg_inj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [← EReal.neg_lt_neg_iff, neg_neg, EReal.neg_bot] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [← EReal.neg_lt_neg_iff, neg_neg, EReal.neg_bot]⟩

/-- The coordinate swap `(y, x) ↦ (x, y)` of Euclidean products. -/
noncomputable def l2Swap (P E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] : WithLp 2 (P × E) →L[ℝ] WithLp 2 (E × P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.snd ℝ P E).prod (ContinuousLinearMap.fst ℝ P E)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ P E).toContinuousLinearMap)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
@[simp] theorem l2Swap_toLp (y : P) (x : E) :
    l2Swap P E (WithLp.toLp 2 (y, x)) = WithLp.toLp 2 (x, y) := rfl

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
/-- The dual value function is the inf-projection of the swapped conjugate. -/
theorem dualParametricValue_eq_parametricValue_swap (f : WithLp 2 (E × P) → EReal) :
    dualParametricValue f = parametricValue (fun q ↦ fenchelConjugate f (l2Swap P E q)) := by
  funext v
  rfl

section Optimization

variable {f : WithLp 2 (E × P) → EReal} (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f)
  (hc : Convex ℝ (epigraph f))
include hf hp hc

/-- When the primal value function `p` is finite at `0` it is proper, lower semicontinuous and
convex (11.32(c)). -/
theorem parametricValue_closed_of_finite {a : ℝ} (ha : parametricValue f 0 = a) :
    IsProper (parametricValue f) ∧ LowerSemicontinuous (parametricValue f) ∧
      Convex ℝ (epigraph (parametricValue f)) := by
  obtain ⟨hconv, hlsc, -, halt⟩ := hf.parametricValue_properties hp hc
  rcases halt with ⟨hpp, -⟩ | hbot
  · exact ⟨hpp, hlsc, hconv⟩
  · exfalso
    have h0 : (0 : P) ∈ effectiveDomain (parametricValue f) := by
      change parametricValue f 0 < ⊤
      rw [ha]
      exact EReal.coe_lt_top a
    have := hbot 0 h0
    rw [ha] at this
    exact EReal.coe_ne_bot a this

/-- When the dual value function `q` is finite at `0` it is proper, lower semicontinuous and
convex (11.32(c) applied to the conjugate). -/
theorem dualParametricValue_closed_of_finite {b : ℝ} (hb : dualParametricValue f 0 = b) :
    IsProper (dualParametricValue f) ∧ LowerSemicontinuous (dualParametricValue f) ∧
      Convex ℝ (epigraph (dualParametricValue f)) := by
  have hl := hf.lowerSemicontinuous
  set g : WithLp 2 (P × E) → EReal := fun q ↦ fenchelConjugate f (l2Swap P E q) with hg
  have hstar := hf.isPiecewiseLinearQuadratic_fenchelConjugate hp hl hc
  have hpc := isProper_fenchelConjugate hp hl hc
  have hgplq : IsPiecewiseLinearQuadratic g := by
    simpa [hg] using hstar.compAffine (l2Swap P E) 0
  have hgp : IsProper g := by
    obtain ⟨w, hw⟩ := hpc.1
    refine ⟨⟨WithLp.toLp 2 ((WithLp.ofLp w).2, (WithLp.ofLp w).1), ?_⟩, fun q ↦ hpc.2 _⟩
    change fenchelConjugate f (l2Swap P E _) < ⊤
    rw [l2Swap_toLp, Prod.mk.eta, WithLp.toLp_ofLp]
    exact hw
  have hgc : Convex ℝ (epigraph g) := by
    simpa [hg] using convex_epigraph_compAffine (convex_epigraph_fenchelConjugate f)
      (l2Swap P E) 0
  rw [dualParametricValue_eq_parametricValue_swap] at hb ⊢
  exact parametricValue_closed_of_finite hgplq hgp hgc hb

/-- **Theorem 11.42** (piecewise linear-quadratic optimization). -/
theorem piecewiseLinearQuadratic_optimization
    (hfin : (∃ a : ℝ, (⨅ x, primalObjective f x) = a) ∨ ∃ b : ℝ, (⨆ y, dualObjective f y) = b) :
    (∃ a : ℝ, (⨅ x, primalObjective f x) = a ∧ (⨆ y, dualObjective f y) = a) ∧
      (argmin (primalObjective f)).Nonempty ∧ (argmax (dualObjective f)).Nonempty ∧
      (∀ x y, (x ∈ argmin (primalObjective f) ∧ y ∈ argmax (dualObjective f)) ↔
        WithLp.toLp 2 (0, y) ∈ subdifferential f (WithLp.toLp 2 (x, 0))) ∧
      (∀ x y, (x ∈ argmin (primalObjective f) ∧ y ∈ argmax (dualObjective f)) ↔
        WithLp.toLp 2 (x, 0) ∈ subdifferential (fenchelConjugate f) (WithLp.toLp 2 (0, y))) ∧
      argmin (primalObjective f) = subdifferential (dualParametricValue f) 0 ∧
      argmax (dualObjective f) = subdifferential (parametricValue f) 0 := by
  have hl := hf.lowerSemicontinuous
  have hpinf : parametricValue f 0 = ⨅ x, primalObjective f x :=
    (primal_dual_value_identities f).1
  have hpsup : fenchelConjugate (fenchelConjugate (parametricValue f)) 0 =
      ⨆ y, dualObjective f y := (primal_dual_value_identities f).2
  have hqsup := iSup_dualObjective_eq_neg_dualParametricValue f
  have hqconj := fenchelConjugate_dualParametricValue hp hl hc
  -- a common finite value
  obtain ⟨a, hainf, hasup⟩ : ∃ a : ℝ, (⨅ x, primalObjective f x) = a ∧
      (⨆ y, dualObjective f y) = a := by
    rcases hfin with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine ⟨a, ha, ?_⟩
      obtain ⟨hpp, hpl, hpc⟩ := parametricValue_closed_of_finite hf hp hc (hpinf.trans ha)
      rw [← hpsup, fenchelConjugate_fenchelConjugate_eq hpp hpl hpc, hpinf, ha]
    · refine ⟨b, ?_, hb⟩
      have hq0 : dualParametricValue f 0 = ((-b : ℝ) : EReal) := by
        rw [EReal.coe_neg, ← hb, hqsup, neg_neg]
      obtain ⟨hqp, hql, hqc⟩ := dualParametricValue_closed_of_finite hf hp hc hq0
      have h := iInf_eq_neg_fenchelConjugate_zero (fenchelConjugate (dualParametricValue f))
      rw [fenchelConjugate_fenchelConjugate_eq hqp hql hqc, hq0, hqconj] at h
      rw [h, EReal.coe_neg, neg_neg]
  have hp0 : parametricValue f 0 = a := hpinf.trans hainf
  have hq0 : dualParametricValue f 0 = ((-a : ℝ) : EReal) := by
    rw [EReal.coe_neg, ← hasup, hqsup, neg_neg]
  obtain ⟨hpp, hpl, hpc⟩ := parametricValue_closed_of_finite hf hp hc hp0
  obtain ⟨hqp, hql, hqc⟩ := dualParametricValue_closed_of_finite hf hp hc hq0
  have hgap : (⨅ x, primalObjective f x) = ⨆ y, dualObjective f y := by rw [hainf, hasup]
  -- `argmin φ = ∂q(0)` and `argmax ψ = ∂p(0)`
  have hargmin : argmin (primalObjective f) = subdifferential (dualParametricValue f) 0 := by
    rw [← hqconj, argmin_eq_subdifferential_fenchelConjugate_zero
      (isProper_fenchelConjugate hqp hql hqc) (lowerSemicontinuous_fenchelConjugate _)
      (convex_epigraph_fenchelConjugate _),
      fenchelConjugate_fenchelConjugate_eq hqp hql hqc]
  have hψ : dualObjective f = fun y ↦ -fenchelConjugate (parametricValue f) y := by
    funext y
    rw [fenchelConjugate_parametricValue]
    rfl
  have hargmax : argmax (dualObjective f) = subdifferential (parametricValue f) 0 := by
    rw [hψ, argmax_neg_eq_argmin, argmin_eq_subdifferential_fenchelConjugate_zero
      (isProper_fenchelConjugate hpp hpl hpc) (lowerSemicontinuous_fenchelConjugate _)
      (convex_epigraph_fenchelConjugate _), fenchelConjugate_fenchelConjugate_eq hpp hpl hpc]
  -- attainment
  have hφne : (argmin (primalObjective f)).Nonempty := by
    rw [hargmin]
    have h0 : (0 : E) ∈ effectiveDomain (dualParametricValue f) := by
      change dualParametricValue f 0 < ⊤
      rw [hq0]
      exact EReal.coe_lt_top _
    -- `∂q(0)` is nonempty: `q` is the inf-projection of a piecewise linear-quadratic function
    have hgplq : IsPiecewiseLinearQuadratic (dualParametricValue f) := by
      rw [dualParametricValue_eq_parametricValue_swap]
      have hstar := hf.isPiecewiseLinearQuadratic_fenchelConjugate hp hl hc
      have hpc' := isProper_fenchelConjugate hp hl hc
      have hgplq : IsPiecewiseLinearQuadratic
          (fun q : WithLp 2 (P × E) ↦ fenchelConjugate f (l2Swap P E q)) := by
        simpa using hstar.compAffine (l2Swap P E) 0
      have hgp : IsProper (fun q : WithLp 2 (P × E) ↦ fenchelConjugate f (l2Swap P E q)) := by
        obtain ⟨w, hw⟩ := hpc'.1
        refine ⟨⟨WithLp.toLp 2 ((WithLp.ofLp w).2, (WithLp.ofLp w).1), ?_⟩, fun q ↦ hpc'.2 _⟩
        change fenchelConjugate f (l2Swap P E _) < ⊤
        rw [l2Swap_toLp, Prod.mk.eta, WithLp.toLp_ofLp]
        exact hw
      have hgc : Convex ℝ (epigraph
          (fun q : WithLp 2 (P × E) ↦ fenchelConjugate f (l2Swap P E q))) := by
        simpa using convex_epigraph_compAffine (convex_epigraph_fenchelConjugate f)
          (l2Swap P E) 0
      rcases (hgplq.parametricValue_properties hgp hgc).2.2.2 with ⟨-, h⟩ | hbot
      · exact h
      · exfalso
        have := hbot 0 (by rw [← dualParametricValue_eq_parametricValue_swap]; exact h0)
        rw [← dualParametricValue_eq_parametricValue_swap, hq0] at this
        exact EReal.coe_ne_bot _ this
    exact (hgplq.convex_subgradient_properties hqc h0).1
  have hψne : (argmax (dualObjective f)).Nonempty := by
    rw [hargmax]
    have h0 : (0 : P) ∈ effectiveDomain (parametricValue f) := by
      change parametricValue f 0 < ⊤
      rw [hp0]
      exact EReal.coe_lt_top _
    have hplq : IsPiecewiseLinearQuadratic (parametricValue f) := by
      rcases (hf.parametricValue_properties hp hc).2.2.2 with ⟨-, h⟩ | hbot
      · exact h
      · exfalso
        have := hbot 0 h0
        rw [hp0] at this
        exact EReal.coe_ne_bot _ this
    exact (hplq.convex_subgradient_properties hpc h0).1
  refine ⟨⟨a, hainf, hasup⟩, hφne, hψne, fun x y ↦ ?_, fun x y ↦ ?_, hargmin, hargmax⟩
  · rw [← primal_dual_optimality_iff_subgradient hp hl hc x y]
    exact ⟨fun h ↦ ⟨h.1, h.2, hgap⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩
  · rw [← primal_dual_optimality_iff_conjugate_subgradient hp hl hc x y]
    exact ⟨fun h ↦ ⟨h.1, h.2, hgap⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩

end Optimization

end RW
