/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Affine minorants and conjugate epigraphs
-/
import RockafellarWets.Chapter11.FenchelConjugate

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reflection about a finite number reverses an extended-real inequality. -/
theorem ereal_coe_sub_le_comm (r : ℝ) (a b : EReal) :
    (r:EReal)-a ≤ b ↔ (r:EReal)-b ≤ a := by
  cases a <;> cases b <;> simp [← EReal.coe_sub,EReal.coe_le_coe_iff] <;>
    constructor <;> intro h <;> linarith

/-- The epigraph of the conjugate parameterizes affine minorants. -/
theorem fenchelConjugate_le_coe_iff (f : E → EReal) (v : E) (b : ℝ) :
    fenchelConjugate f v ≤ (b:EReal) ↔ ∀ x, ((⟪v,x⟫_ℝ-b:ℝ):EReal) ≤ f x := by
  rw [fenchelConjugate_le_iff]
  apply forall_congr'
  intro x
  simpa only [EReal.coe_sub] using ereal_coe_sub_le_comm ⟪v,x⟫_ℝ (f x) b

/-- Biconjugation always gives a minorant, including both improper cases. -/
theorem fenchelConjugate_fenchelConjugate_le (f : E → EReal) :
    fenchelConjugate (fenchelConjugate f) ≤ f := by
  intro x
  apply iSup_le
  intro v
  rw [real_inner_comm v x]
  exact (ereal_coe_sub_le_comm ⟪v,x⟫_ℝ (f x) (fenchelConjugate f v)).mp (le_fenchelConjugate f x v)

theorem lowerSemicontinuous_fenchelConjugate (f : E → EReal) :
    LowerSemicontinuous (fenchelConjugate f) := by
  apply lowerSemicontinuous_iSup
  intro x
  cases h : f x with
  | bot => simpa [h] using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : E ↦ (⊤:EReal)))
  | top => simpa [h] using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : E ↦ (⊥:EReal)))
  | coe a =>
    have hc : Continuous (fun v : E ↦ ((⟪v,x⟫_ℝ-a:ℝ):EReal)) :=
      continuous_coe_real_ereal.comp (by fun_prop)
    simpa only [h,EReal.coe_sub] using hc.lowerSemicontinuous

theorem convex_epigraph_fenchelConjugate (f : E → EReal) :
    Convex ℝ (epigraph (fenchelConjugate f)) := by
  intro p hp q hq t s ht hs hts
  have hp' := (fenchelConjugate_le_coe_iff f p.1 p.2).mp hp
  have hq' := (fenchelConjugate_le_coe_iff f q.1 q.2).mp hq
  apply (fenchelConjugate_le_coe_iff f (t • p.1+s • q.1) (t*p.2+s*q.2)).mpr
  intro x
  cases hx : f x with
  | bot =>
    have hbad := hp' x
    rw [hx] at hbad
    exact ((EReal.bot_lt_coe (⟪p.1,x⟫_ℝ-p.2)).not_ge hbad).elim
  | top => exact le_top
  | coe a =>
    have hp'' : ⟪p.1,x⟫_ℝ-p.2 ≤ a := EReal.coe_le_coe_iff.mp (hx ▸ hp' x)
    have hq'' : ⟪q.1,x⟫_ℝ-q.2 ≤ a := EReal.coe_le_coe_iff.mp (hx ▸ hq' x)
    apply EReal.coe_le_coe_iff.mpr
    simp only [inner_add_left,real_inner_smul_left]
    have hh := add_le_add (mul_le_mul_of_nonneg_left hp'' ht) (mul_le_mul_of_nonneg_left hq'' hs)
    nlinarith [congrArg (fun z : ℝ ↦ z*a) hts]

theorem bot_lt_fenchelConjugate_of_finite {f : E → EReal} {x : E} {a : ℝ}
    (hx : f x = a) (v : E) : ⊥ < fenchelConjugate f v := by
  apply lt_of_lt_of_le (EReal.bot_lt_coe (⟪v,x⟫_ℝ-a))
  simpa only [hx,EReal.coe_sub] using le_fenchelConjugate f x v

end
end RW
