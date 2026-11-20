/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nonseparated convex domains qualify the sum rule
-/

import RockafellarWets.Chapter10.FiniteSumSubderivatives
import RockafellarWets.Chapter10.CompositeMultipliers
import RockafellarWets.Chapter6.IntersectionCones

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f g : E → EReal} {x : E} {c d : ℝ}

/-- **Corollary 10.9**, the parenthetical convex nonseparation condition. -/
theorem convex_sum_qualification_of_not_separated
    (hf : Convex ℝ (epigraph f)) (hg : Convex ℝ (epigraph g))
    (hpf : IsProper f) (hpg : IsProper g) (hx : f x = c) (hy : g x = d)
    (hsep : ¬ ∃ v : E, v ≠ 0 ∧ ∀ y ∈ effectiveDomain f, ∀ z ∈ effectiveDomain g,
      ⟪v,y⟫_ℝ ≤ ⟪v,z⟫_ℝ) :
    ∀ u ∈ horizonSubdifferential f x, ∀ v ∈ horizonSubdifferential g x,
      u+v = 0 → u = 0 ∧ v = 0 := by
  intro u hu v hv he
  have huf := horizonSubdifferential_subset_normalCone_domain hf hpf hx hu
  have hvg := horizonSubdifferential_subset_normalCone_domain hg hpg hy hv
  have hq := intersectionConstraintQualification_of_not_separated
    (convex_effectiveDomain_of_convex_epigraph hf) (convex_effectiveDomain_of_convex_epigraph hg)
    (hx.trans_lt (EReal.coe_lt_top _)) (hy.trans_lt (EReal.coe_lt_top _)) hsep
  have hz := hq (![u,v] : Fin 2 → E)
    (by intro i; fin_cases i <;> assumption) (by simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using he)
  exact ⟨hz 0,hz 1⟩

/-- A sufficient condition that makes the unconditional lower sum bound
valid with the book's inf-addition convention. -/
theorem subderivative_finiteSum_ge_finiteInfAddition_of_calm {ι : Type*} [Fintype ι]
    {f : ι → E → EReal} {c : ι → ℝ} (hx : ∀ i, f i x = c i)
    (h0 : ∀ i, subderivative (f i) x 0 = 0) (w : E) :
    finiteInfAddition (fun i ↦ subderivative (f i) x w) ≤ subderivative (fun z ↦ ∑ i, f i z) x w := by
  have hn (i : ι) : subderivative (f i) x w ≠ ⊥ :=
    ((isCalmFromBelowAt_iff_subderivative_ne_bot (hx i)).mp
      ((isCalmFromBelowAt_iff_subderivative_zero (hx i)).mpr (h0 i)) w).ne'
  rw [finiteInfAddition_eq_sum_of_ne_bot _ hn]
  exact subderivative_finiteSum_ge hx w

end RW
