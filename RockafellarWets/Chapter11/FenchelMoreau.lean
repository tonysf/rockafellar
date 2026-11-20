/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Fenchel–Moreau identity
-/

import RockafellarWets.Chapter11.ConjugateGeometry
import RockafellarWets.Chapter8.ConvexEnvelopes

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem fenchelConjugate_le_of_affineMinorant {f : E → EReal} {l : E →L[ℝ] ℝ} {b : ℝ}
    (hl : ∀ x, ((l x+b:ℝ):EReal) ≤ f x) :
    fenchelConjugate f ((InnerProductSpace.toDual ℝ E).symm l) ≤ ((-b:ℝ):EReal) := by
  apply (fenchelConjugate_le_coe_iff _ _ _).mpr
  intro x
  simpa only [InnerProductSpace.toDual_symm_apply,sub_neg_eq_add] using hl x

/-- Every continuous affine minorant lies below the biconjugate. -/
theorem affineMinorant_le_biconjugate {f : E → EReal} {l : E →L[ℝ] ℝ} {b : ℝ}
    (hl : ∀ x, ((l x+b:ℝ):EReal) ≤ f x) (x : E) :
    ((l x+b:ℝ):EReal) ≤ fenchelConjugate (fenchelConjugate f) x := by
  let v := (InnerProductSpace.toDual ℝ E).symm l
  have hb := fenchelConjugate_le_of_affineMinorant hl
  calc
    ((l x+b:ℝ):EReal) = (⟪x,v⟫_ℝ:EReal)-((-b:ℝ):EReal) := by
      rw [real_inner_comm v x]
      simp [v,InnerProductSpace.toDual_symm_apply,sub_eq_add_neg]
    _ ≤ (⟪x,v⟫_ℝ:EReal)-fenchelConjugate f v := by
      simpa only [sub_eq_add_neg] using add_le_add (le_refl (⟪x,v⟫_ℝ:EReal)) (EReal.neg_le_neg_iff.mpr hb)
    _ ≤ _ := le_fenchelConjugate _ v x

/-- Proper closed convex functions have proper conjugates. -/
theorem isProper_fenchelConjugate {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) : IsProper (fenchelConjugate f) := by
  obtain ⟨x,hxt⟩ := hp.1
  let a := (f x).toReal
  have hx : f x = (a:EReal) := (EReal.coe_toReal hxt.ne (hp.2 x).ne').symm
  have hlow : ((a-1:ℝ):EReal) < f x := by rw [hx]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨l,b,hs,_⟩ := exists_affineSupport_gt_of_lt hc hl hp hlow
  exact ⟨⟨(InnerProductSpace.toDual ℝ E).symm l,
    (fenchelConjugate_le_of_affineMinorant hs.1).trans_lt (EReal.coe_lt_top _)⟩,
    bot_lt_fenchelConjugate_of_finite hx⟩

/-- **Theorem 11.1**, the Fenchel–Moreau identity for proper closed convex functions. -/
theorem fenchelConjugate_fenchelConjugate_eq {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    fenchelConjugate (fenchelConjugate f) = f := by
  apply le_antisymm (fenchelConjugate_fenchelConjugate_le f)
  intro x
  calc
    f x = ⨆ p : {p : (E →L[ℝ] ℝ) × ℝ // IsAffineSupport f p.1 p.2},
        ((p.val.1 x+p.val.2:ℝ):EReal) := eq_iSup_affineSupports hc hl hp x
    _ ≤ _ := iSup_le (fun p ↦ affineMinorant_le_biconjugate p.property.1 x)

/-- Conjugation preserves the class of proper lower semicontinuous convex functions. -/
theorem fenchelConjugate_properties {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    IsProper (fenchelConjugate f) ∧ LowerSemicontinuous (fenchelConjugate f) ∧
      Convex ℝ (epigraph (fenchelConjugate f)) ∧ fenchelConjugate (fenchelConjugate f) = f :=
  ⟨isProper_fenchelConjugate hp hl hc,lowerSemicontinuous_fenchelConjugate f,
    convex_epigraph_fenchelConjugate f,fenchelConjugate_fenchelConjugate_eq hp hl hc⟩

end
end RW
