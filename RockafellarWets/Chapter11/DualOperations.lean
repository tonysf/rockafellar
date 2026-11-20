/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dual operations under Legendre–Fenchel conjugation
-/

import RockafellarWets.Chapter11.ConjugateGeometry
import RockafellarWets.Chapter11.ProductConjugacy
import RockafellarWets.Chapter3.EpiAddition
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Set
open scoped InnerProductSpace

namespace RW

/-- Reflection about a real scalar changes an arbitrary infimum into a
supremum, including the empty fiber. -/
theorem ereal_coe_sub_iInf {ι : Sort*} (r : ℝ) (g : ι → EReal) :
    (r : EReal) - (⨅ i, g i) = ⨆ i, (r : EReal) - g i := by
  apply eq_of_forall_ge_iff
  intro b
  rw [ereal_coe_sub_le_comm,le_iInf_iff,iSup_le_iff]
  exact forall_congr' fun i ↦ ereal_coe_sub_le_comm r b (g i)

/-- Infimum of the objective on each fiber. It takes value `⊤` on an
empty fiber. -/
noncomputable def fiberInfimum {X Y : Type*} (A : X → Y) (f : X → EReal) (u : Y) : EReal :=
  ⨅ x : {x // A x = u}, f x

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Theorem 11.23(d)**, conjugating any pointwise infimum. -/
theorem fenchelConjugate_iInf {ι : Sort*} (f : ι → E → EReal) :
    fenchelConjugate (fun x ↦ ⨅ i, f i x) = fun v ↦ ⨆ i, fenchelConjugate (f i) v := by
  funext v
  simp only [fenchelConjugate,ereal_coe_sub_iInf]
  exact iSup_comm

/-- **Theorem 11.23(b)**, conjugation changes the infimum on the fibers
of a linear map into precomposition with its adjoint. -/
theorem fenchelConjugate_fiberInfimum [CompleteSpace E] [CompleteSpace F]
    (A : E →L[ℝ] F) (f : E → EReal) :
    fenchelConjugate (fiberInfimum A f) = fun v ↦ fenchelConjugate f (A.adjoint v) := by
  funext v
  simp only [fenchelConjugate,fiberInfimum,ereal_coe_sub_iInf]
  refine le_antisymm (iSup_le fun u ↦ iSup_le fun x ↦ le_iSup_of_le x.val ?_)
    (iSup_le fun x ↦ le_iSup_of_le (A x) (le_iSup_of_le ⟨x,rfl⟩ ?_))
  · rw [A.adjoint_inner_left,x.property]
  · rw [A.adjoint_inner_left]

/-- **Theorem 11.23(c)**, the conjugate of a marginal value is a zero
section of the joint conjugate. -/
theorem fenchelConjugate_valueFunction (f : E × F → EReal) (v : F) :
    fenchelConjugate (valueFunction f) v =
      fenchelConjugate (fun p : WithLp 2 (E × F) ↦ f (WithLp.ofLp p)) (WithLp.toLp 2 (0,v)) := by
  simp only [fenchelConjugate,valueFunction,ereal_coe_sub_iInf]
  refine le_antisymm (iSup_le fun u ↦ iSup_le fun x ↦ le_iSup_of_le (WithLp.toLp 2 (x,u)) ?_)
    (iSup_le fun q ↦ le_iSup_of_le q.snd (le_iSup_of_le q.fst ?_))
  · simp [WithLp.prod_inner_apply]
  · simp only [WithLp.prod_inner_apply,inner_zero_left,zero_add]
    exact le_rfl

/-- **Theorem 11.23(a)**, the conjugate of an infimal convolution.
No convexity, lower semicontinuity or attainment is required. -/
theorem fenchelConjugate_epiSum {f g : E → EReal} (hf : IsProper f) (hg : IsProper g) :
    fenchelConjugate (epiSum f g) = fun v ↦ fenchelConjugate f v + fenchelConjugate g v := by
  funext v
  simp only [fenchelConjugate,epiSum_apply,ereal_coe_sub_iInf]
  rw [ereal_iSup_add]
  simp_rw [ereal_add_iSup]
  have he (z w : E) :
      (⟪v,z+w⟫_ℝ : EReal) - (f z + g w) =
        ((⟪v,z⟫_ℝ : EReal) - f z) + ((⟪v,w⟫_ℝ : EReal) - g w) := by
    rw [inner_add_right,EReal.coe_add]
    simp only [sub_eq_add_neg,EReal.neg_add (Or.inl ((hf.2 z).ne')) (Or.inr ((hg.2 w).ne'))]
    exact add_add_add_comm _ _ _ _
  refine le_antisymm (iSup_le fun x ↦ iSup_le fun w ↦ le_iSup_of_le (x-w) (le_iSup_of_le w ?_))
    (iSup_le fun z ↦ iSup_le fun w ↦ le_iSup_of_le (z+w) (le_iSup_of_le w ?_))
  · simpa only [sub_add_cancel] using (he (x-w) w).le
  · simpa only [add_sub_cancel_right] using (he z w).symm.le

end RW
