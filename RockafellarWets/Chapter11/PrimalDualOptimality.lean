/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Joint primal and dual optimality
-/
import RockafellarWets.Chapter11.PrimalDualValues

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- Equality of a primal and dual objective value entails attainment of
both optima and a zero duality gap. -/
theorem primal_dual_optimality_iff_values_equal {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hpc : IsProper (fenchelConjugate f)) (x : E) (y : P) :
    (x ∈ argmin (primalObjective f) ∧ y ∈ argmax (dualObjective f) ∧
      (⨅ z, primalObjective f z) = (⨆ v, dualObjective f v)) ↔
      primalObjective f x = dualObjective f y := by
  constructor
  · rintro ⟨hx,hy,he⟩
    exact hx.1.trans (he.trans hy.1.symm)
  · intro he
    have hx : primalObjective f x = ⨅ z, primalObjective f z := by
      apply le_antisymm _ (iInf_le _ x)
      apply le_iInf
      intro z
      rw [he]
      exact dualObjective_le_primalObjective f z y
    have hy : dualObjective f y = ⨆ v, dualObjective f v := by
      apply le_antisymm (le_iSup _ y)
      apply iSup_le
      intro v
      rw [← he]
      exact dualObjective_le_primalObjective f x v
    have hfin : primalObjective f x < ⊤ := by
      rw [he]
      change -fenchelConjugate f (WithLp.toLp 2 (0,y)) < ⊤
      rw [EReal.neg_lt_comm,EReal.neg_top]
      exact hpc.2 _
    have hbot : ⊥ < dualObjective f y := by
      rw [← he]
      exact hp.2 _
    exact ⟨⟨hx,hx ▸ hfin⟩,⟨hy,hy ▸ hbot⟩,hx.symm.trans (he.trans hy)⟩

/-- The first Fermat equivalence in **Theorem 11.39(d)**. -/
theorem primal_dual_optimality_iff_subgradient {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (x : E) (y : P) :
    (x ∈ argmin (primalObjective f) ∧ y ∈ argmax (dualObjective f) ∧
      (⨅ z, primalObjective f z) = (⨆ v, dualObjective f v)) ↔
      WithLp.toLp 2 (0,y) ∈ subdifferential f (WithLp.toLp 2 (x,0)) := by
  have hpc := isProper_fenchelConjugate hp hl hc
  rw [primal_dual_optimality_iff_values_equal hp hpc,
    mem_subdifferential_iff_fenchel_equality hp hc]
  have he := ereal_coe_sub_eq_iff_add_eq 0 (hp.2 (WithLp.toLp 2 (x,0)))
    (hpc.2 (WithLp.toLp 2 (0,y)))
  simpa only [primalObjective,partialFunction,dualObjective,EReal.coe_zero,zero_sub,
    WithLp.prod_inner_apply,WithLp.toLp_fst,WithLp.toLp_snd,inner_zero_left,
    inner_zero_right,zero_add,eq_comm] using he

/-- The equivalent dual Fermat condition in **11.39(d)**. -/
theorem primal_dual_optimality_iff_conjugate_subgradient {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (x : E) (y : P) :
    (x ∈ argmin (primalObjective f) ∧ y ∈ argmax (dualObjective f) ∧
      (⨅ z, primalObjective f z) = (⨆ v, dualObjective f v)) ↔
      WithLp.toLp 2 (x,0) ∈ subdifferential (fenchelConjugate f) (WithLp.toLp 2 (0,y)) := by
  rw [mem_subdifferential_fenchelConjugate_iff hp hl hc]
  exact primal_dual_optimality_iff_subgradient hp hl hc x y

end
end RW
