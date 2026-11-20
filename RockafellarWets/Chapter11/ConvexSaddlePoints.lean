/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Saddle point conditions for convex problems

Corollary 11.51 under the interior condition `0 ∈ int U`.
-/
import RockafellarWets.Chapter11.MinimaxRelations

open Set
namespace RW
noncomputable section
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- **Corollary 11.51** under `0 ∈ int U`: a vector `x₀` is optimal exactly when
some `y₀` makes `(x₀,y₀)` a saddle point of the Lagrangian, and the vectors
appearing in this role with an optimal `x₀` are exactly the dual optima. -/
theorem convex_saddle_point_conditions {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hu : (0 : P) ∈ interior (effectiveDomain (parametricValue f))) (x₀ : E) :
    (x₀ ∈ argmin (primalObjective f) ↔ ∃ y₀, (x₀, y₀) ∈ argminimax (lagrangian f)) ∧
    (x₀ ∈ argmin (primalObjective f) →
      ∀ y₀, ((x₀, y₀) ∈ argminimax (lagrangian f) ↔ y₀ ∈ argmax (dualObjective f))) := by
  have hf := isDualizingParameterization_of_convex hp hl hc
  have he := primal_dual_strong_duality_of_primal_interior hp hl hc hu
  have hpair (hx : x₀ ∈ argmin (primalObjective f)) (y₀ : P) :
      (x₀, y₀) ∈ argminimax (lagrangian f) ↔ y₀ ∈ argmax (dualObjective f) :=
    ⟨fun h ↦ ((hf.minimax_relations x₀ y₀).1.mpr h).2.1,
      fun hy ↦ (hf.minimax_relations x₀ y₀).1.mp ⟨hx, hy, he⟩⟩
  refine ⟨⟨fun hx ↦ ?_, fun ⟨y₀, h⟩ ↦ ((hf.minimax_relations x₀ y₀).1.mpr h).1⟩, hpair⟩
  have hb : ⊥ < parametricValue f 0 := by
    rw [(primal_dual_value_identities f).1, ← hx.1]
    exact hp.2 _
  have ht : parametricValue f 0 < ⊤ := by
    rw [(primal_dual_value_identities f).1]
    exact hx.2
  obtain ⟨y₀, hy⟩ := ((dual_optima_nonempty_bounded_iff hp hc).mpr
    ⟨hu, _, (EReal.coe_toReal ht.ne hb.ne').symm⟩).1
  exact ⟨y₀, (hpair hx y₀).mpr hy⟩

end
end RW
