/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subderivatives under a smooth finite perturbation
-/
import RockafellarWets.Chapter10.SemiderivativeCalculus

open Set Filter Topology

namespace RW
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Difference quotients distribute over addition of a finite perturbation. -/
theorem differenceQuotient_add_real {g : E → EReal} {q : E → ℝ} {x : E} {c : ℝ}
    (hx : g x = c) {t : ℝ} (ht : 0 < t) (w : E) :
    differenceQuotient (fun y ↦ g y + (q y : EReal)) x t w =
      differenceQuotient g x t w + differenceQuotient (fun y ↦ (q y : EReal)) x t w := by
  unfold differenceQuotient
  dsimp only
  rw [hx]
  cases g (x+t • w) using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos (inv_pos.mpr ht)]
  | top => simp only [EReal.top_add_coe,← EReal.coe_add,EReal.top_sub_coe,← EReal.coe_sub,
      EReal.coe_mul_top_of_pos (inv_pos.mpr ht),← EReal.coe_mul,EReal.top_add_coe]
  | coe a => simp only [← EReal.coe_add,← EReal.coe_sub,← EReal.coe_mul]; congr 1; ring

/-- A finite directional semiderivative can be added exactly to every
subderivative; no lower semicontinuity or constraint qualification is needed. -/
theorem subderivative_add_real_of_hasDirectionalSemiderivative
    {g : E → EReal} {q : E → ℝ} {x w : E} {c d : ℝ}
    (hx : g x = c) (hq : HasDirectionalSemiderivative q x w d) :
    subderivative (fun y ↦ g y + (q y : EReal)) x w = subderivative g x w + (d : EReal) := by
  let l := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w
  let u := fun p : ℝ × E ↦ differenceQuotient (fun y ↦ (q y : EReal)) x p.1 p.2
  let v := fun p : ℝ × E ↦ differenceQuotient g x p.1 p.2
  have hu : Tendsto u l (𝓝 (d : EReal)) := (hasDirectionalSemiderivative_iff.mp hq).2.2
  have he : (fun p : ℝ × E ↦ differenceQuotient (fun y ↦ g y+(q y : EReal)) x p.1 p.2) =ᶠ[l] u+v := by
    filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp
    rw [differenceQuotient_add_real hx hp]
    exact add_comm _ _
  unfold subderivative
  rw [Filter.liminf_congr he]
  change liminf (u+v) l = liminf v l + (d : EReal)
  apply le_antisymm
  · have h := EReal.liminf_add_le (u := u) (v := v) (f := l)
      (Or.inl (hu.limsup_eq ▸ EReal.coe_ne_bot d))
      (Or.inl (hu.limsup_eq ▸ EReal.coe_ne_top d))
    simpa [hu.limsup_eq,add_comm] using h
  · simpa [hu.liminf_eq,add_comm] using (EReal.le_liminf_add (u := u) (v := v) (f := l))

/-- The smooth specialization of the exact subderivative addition rule. -/
theorem subderivative_add_differentiable {g : E → EReal} {q : E → ℝ} {x w : E} {c : ℝ}
    {A : E →L[ℝ] ℝ} (hx : g x = c) (hq : HasFDerivAt q A x) :
    subderivative (fun y ↦ g y + (q y : EReal)) x w = subderivative g x w + (A w : EReal) :=
  subderivative_add_real_of_hasDirectionalSemiderivative hx (hq.hasDirectionalSemiderivative w)

end RW
