/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Saddle point conditions in the piecewise linear-quadratic case

Corollary 11.51, the alternative hypothesis `0 ∈ U` with `f` piecewise linear-quadratic.
-/
import RockafellarWets.Chapter11.ConvexSaddlePoints
import RockafellarWets.Chapter11.PiecewiseLinearQuadraticOptimization

open Set
namespace RW
noncomputable section
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- **Corollary 11.51**, piecewise linear-quadratic case: for proper convex piecewise
linear-quadratic `f` with `0 ∈ U`, a vector `x₀` is optimal exactly when some `y₀`
makes `(x₀,y₀)` a saddle point of the Lagrangian, and its partners are exactly the
dual optima. (Optimality of `x₀` already forces `0 ∈ U`.) -/
theorem convex_saddle_point_conditions_of_piecewiseLinearQuadratic {f : WithLp 2 (E × P) → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hu : (0 : P) ∈ effectiveDomain (parametricValue f)) (x₀ : E) :
    (x₀ ∈ argmin (primalObjective f) ↔ ∃ y₀, (x₀, y₀) ∈ argminimax (lagrangian f)) ∧
    (x₀ ∈ argmin (primalObjective f) →
      ∀ y₀, ((x₀, y₀) ∈ argminimax (lagrangian f) ↔ y₀ ∈ argmax (dualObjective f))) := by
  have hl := hf.lowerSemicontinuous
  have hfd := isDualizingParameterization_of_convex hp hl hc
  have hU : (⨅ x, primalObjective f x) < ⊤ :=
    ((primal_dual_finite_sided_value_iff f).1).mpr hu
  have hfin (hx : x₀ ∈ argmin (primalObjective f)) :
      ∃ a : ℝ, (⨅ x, primalObjective f x) = a := by
    have hb : ⊥ < (⨅ x, primalObjective f x) := by
      rw [← hx.1]
      exact hp.2 _
    exact ⟨_, (EReal.coe_toReal hU.ne hb.ne').symm⟩
  have hpair (hx : x₀ ∈ argmin (primalObjective f)) (y₀ : P) :
      (x₀, y₀) ∈ argminimax (lagrangian f) ↔ y₀ ∈ argmax (dualObjective f) := by
    obtain ⟨⟨a, ha₁, ha₂⟩, -⟩ := piecewiseLinearQuadratic_optimization hf hp hc (.inl (hfin hx))
    exact ⟨fun h ↦ ((hfd.minimax_relations x₀ y₀).1.mpr h).2.1,
      fun hy ↦ (hfd.minimax_relations x₀ y₀).1.mp ⟨hx, hy, ha₁.trans ha₂.symm⟩⟩
  refine ⟨⟨fun hx ↦ ?_, fun ⟨y₀, h⟩ ↦ ((hfd.minimax_relations x₀ y₀).1.mpr h).1⟩, hpair⟩
  obtain ⟨-, -, ⟨y₀, hy⟩, -⟩ := piecewiseLinearQuadratic_optimization hf hp hc (.inl (hfin hx))
  exact ⟨y₀, (hpair hx y₀).mpr hy⟩

end
end RW
