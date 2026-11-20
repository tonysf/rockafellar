/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A correction to the convex equality claim in Proposition 10.19(b)

For the identity inner and outer functions, the ordinary subdifferential is
{1}. The unconditional union with the inner horizon subdifferential adds 0.
Thus the printed inclusions cannot both be promoted to equalities as stated.
-/

import RockafellarWets.Chapter10.SmoothNonlinearRescaling
import RockafellarWets.Chapter8.SubgradientsAndGradients

open Set
open scoped InnerProductSpace

namespace RW

/-- Both inner and outer functions in the counterexample are the identity. -/
def identityRescaling (x : ℝ) : EReal := x

theorem identityRescaling_proper_lsc_convex : IsProper identityRescaling ∧
    LowerSemicontinuous identityRescaling ∧ Convex ℝ (epigraph identityRescaling) := by
  refine ⟨⟨⟨0,by simp [identityRescaling]⟩,fun x ↦ EReal.bot_lt_coe x⟩,
    continuous_coe_real_ereal.lowerSemicontinuous,?_⟩
  intro p hp q hq a b ha hb hab
  change (a*p.1+b*q.1 : EReal) ≤ ((a*p.2+b*q.2:ℝ):EReal)
  exact EReal.coe_le_coe_iff.mpr (add_le_add
    (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp hp) ha)
    (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp hq) hb))

theorem identityRescaling_strictMono : StrictMono identityRescaling :=
  fun _ _ h ↦ EReal.coe_lt_coe_iff.mpr h

theorem identityRescaling_iSup : (⨆ x : ℝ, identityRescaling x) = ⊤ := by
  by_contra h
  obtain ⟨b,hb,_⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr h)
  exact hb.not_ge (le_iSup identityRescaling b)

theorem identityRescaling_subdifferentials :
    subdifferential identityRescaling 0 = {1} ∧ horizonSubdifferential identityRescaling 0 = {0} := by
  have hh := subdifferentials_of_smooth (k := fun x : ℝ ↦ x) (x := 0) contDiff_id.contDiffAt
  have hg : gradient (fun x : ℝ ↦ x) 0 = 1 := by rw [gradient_eq_deriv',deriv_id'']
  exact ⟨by simpa only [hg] using hh.1,hh.2.1⟩

/-- **Proposition 10.19(b), correction**: even with proper lsc convex,
strictly increasing identity functions and the printed qualification, the
ordinary convex equality fails because the unconditional horizon union adds 0. -/
theorem nonlinear_rescaling_printed_convex_equality_counterexample :
    IsProper identityRescaling ∧ LowerSemicontinuous identityRescaling ∧
    Convex ℝ (epigraph identityRescaling) ∧ Monotone identityRescaling ∧
    (⨆ x : ℝ, identityRescaling x) = ⊤ ∧
    (∀ a : ℝ, 0 < a → identityRescaling 0 < identityRescaling a) ∧
    (0:ℝ) ∉ subdifferential identityRescaling 0 ∧
    subdifferential identityRescaling 0 ≠
      ({z : ℝ | ∃ r ∈ subdifferential identityRescaling 0,
        ∃ v ∈ subdifferential identityRescaling 0, z = r • v} ∪
        horizonSubdifferential identityRescaling 0) := by
  obtain ⟨hp,hl,hc⟩ := identityRescaling_proper_lsc_convex
  obtain ⟨hs,hh⟩ := identityRescaling_subdifferentials
  refine ⟨hp,hl,hc,identityRescaling_strictMono.monotone,identityRescaling_iSup,
    fun a ha ↦ identityRescaling_strictMono ha,?_,?_⟩
  · simp [hs]
  · intro he
    have hz : (0:ℝ) ∈ subdifferential identityRescaling 0 := by
      rw [he]
      exact Or.inr (hh ▸ mem_singleton 0)
    simpa [hs] using hz

end RW
