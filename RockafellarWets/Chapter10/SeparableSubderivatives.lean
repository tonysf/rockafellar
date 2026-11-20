/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Subderivatives of separable functions
-/

import RockafellarWets.Chapter10.SeparableSubgradients
import RockafellarWets.Chapter8.RegularSubderivativeSupport
import RockafellarWets.Chapter8.Calmness

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {f : E → EReal} {g : F → EReal} {x : E} {y : F} {c d : ℝ}

theorem lowerSemicontinuous_separableSum (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) (hpf : IsProper f) (hpg : IsProper g) :
    LowerSemicontinuous (separableSum f g) := by
  apply LowerSemicontinuous.add' (hf.comp (WithLp.fstL 2 ℝ E F).continuous)
    (hg.comp (WithLp.sndL 2 ℝ E F).continuous)
  intro q
  exact EReal.continuousAt_add (.inr (hpg.2 q.snd).ne') (.inl (hpf.2 q.fst).ne')

theorem differenceQuotient_separableSum (hx : f x = c) (hy : g y = d)
    {t : ℝ} (ht : 0 < t) (w : WithLp 2 (E × F)) :
    differenceQuotient (separableSum f g) (WithLp.toLp 2 (x,y)) t w =
      differenceQuotient f x t w.fst + differenceQuotient g y t w.snd := by
  have hpos : 0 < t⁻¹ := inv_pos.mpr ht
  change ((t⁻¹:ℝ):EReal)*((f (x+t • w.fst)+g (y+t • w.snd))-(f x+g y)) =
    ((t⁻¹:ℝ):EReal)*(f (x+t • w.fst)-f x)+((t⁻¹:ℝ):EReal)*(g (y+t • w.snd)-g y)
  rw [hx,hy]
  cases hfv : f (x+t • w.fst) <;> cases hgv : g (y+t • w.snd) <;>
    simp [← EReal.coe_add,← EReal.coe_sub,← EReal.coe_mul,EReal.coe_mul_bot_of_pos hpos,
      EReal.coe_mul_top_of_pos hpos]
  congr 1 <;> ring

/-- **Proposition 10.5**, the lower-subderivative inequality. -/
theorem subderivative_separableSum_ge (hx : f x = c) (hy : g y = d) (w : WithLp 2 (E × F)) :
    subderivative f x w.fst + subderivative g y w.snd ≤
      subderivative (separableSum f g) (WithLp.toLp 2 (x,y)) w := by
  let l := 𝓝[>] (0:ℝ) ×ˢ 𝓝 w
  let a := fun q : ℝ × WithLp 2 (E × F) ↦ differenceQuotient f x q.1 q.2.fst
  let b := fun q : ℝ × WithLp 2 (E × F) ↦ differenceQuotient g y q.1 q.2.snd
  have hfst : Tendsto (fun q : ℝ × WithLp 2 (E × F) ↦ (q.1,q.2.fst)) l (𝓝[>] (0:ℝ) ×ˢ 𝓝 w.fst) :=
    tendsto_fst.prodMk (((WithLp.fstL 2 ℝ E F).continuous.tendsto w).comp tendsto_snd)
  have hsnd : Tendsto (fun q : ℝ × WithLp 2 (E × F) ↦ (q.1,q.2.snd)) l (𝓝[>] (0:ℝ) ×ˢ 𝓝 w.snd) :=
    tendsto_fst.prodMk (((WithLp.sndL 2 ℝ E F).continuous.tendsto w).comp tendsto_snd)
  have ha : subderivative f x w.fst ≤ liminf a l := by
    apply (le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
    intro r hr
    exact hfst.eventually (eventually_lt_of_lt_liminf hr)
  have hb : subderivative g y w.snd ≤ liminf b l := by
    apply (le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
    intro r hr
    exact hsnd.eventually (eventually_lt_of_lt_liminf hr)
  have he : (fun q : ℝ × WithLp 2 (E × F) ↦ differenceQuotient (separableSum f g)
      (WithLp.toLp 2 (x,y)) q.1 q.2) =ᶠ[l] a+b := by
    filter_upwards [tendsto_fst.eventually (show ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t from self_mem_nhdsWithin)] with q hq
    exact differenceQuotient_separableSum hx hy hq q.2
  exact (add_le_add ha hb).trans (EReal.le_liminf_add.trans_eq (liminf_congr he).symm)

end RW
