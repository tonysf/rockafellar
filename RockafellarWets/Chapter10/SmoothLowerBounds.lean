/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: smooth lower bounds on semicontinuous functions

**Lemma 10.55**: for a nonempty open `O ⊂ ℝⁿ` and `f : O → ℝ̄` lsc with `f(x) > -∞` on `O`, there
is a `C^∞` function `h` on `O` with `f ≥ h` (in fact `f > h`) on `O`
(`exists_contDiffOn_lt_of_lowerSemicontinuousOn`).  The book builds `h` from a compact exhaustion
of `O` and smooth cut-off functions; here the same gluing is done by Mathlib's smooth partitions of
unity on the manifold `O` (`exists_contMDiffMap_forall_mem_convex_of_local_const`), the local
lower bounds being constants given by lower semicontinuity.
-/

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real

open Filter Function Set Topology Manifold
open scoped ContDiff

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lemma 10.55** (smooth bounds on semicontinuous functions). -/
theorem exists_contDiffOn_lt_of_lowerSemicontinuousOn {O : Set E} (hO : IsOpen O) {f : E → EReal}
    (hf : LowerSemicontinuousOn f O) (hbot : ∀ x ∈ O, f x ≠ ⊥) :
    ∃ h : E → ℝ, ContDiffOn ℝ ∞ h O ∧ ∀ x ∈ O, ((h x : ℝ) : EReal) < f x := by
  let U : TopologicalSpace.Opens E := ⟨O, hO⟩
  haveI : LocallyCompactSpace U := hO.locallyCompactSpace
  have hconv : ∀ x : U, Convex ℝ {r : ℝ | ((r : ℝ) : EReal) < f x} := fun x ↦
    Set.OrdConnected.convex ⟨fun _ _ _ hb _ hr ↦ lt_of_le_of_lt (EReal.coe_le_coe_iff.2 hr.2) hb⟩
  have hloc : ∀ x : U, ∃ c : ℝ, ∀ᶠ y : U in 𝓝 x,
      c ∈ {r : ℝ | ((r : ℝ) : EReal) < f (y : E)} := by
    intro x
    obtain ⟨c, -, hc⟩ := EReal.lt_iff_exists_real_btwn.1 (bot_lt_iff_ne_bot.2 (hbot x x.2))
    have hl : ∀ᶠ y in 𝓝[O] (x : E), ((c : ℝ) : EReal) < f y := hf x x.2 c hc
    rw [nhdsWithin_eq_nhds.2 (hO.mem_nhds x.2)] at hl
    exact ⟨c, (continuous_subtype_val.tendsto x).eventually hl⟩
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const (I := 𝓘(ℝ, E))
    (M := U) (F := ℝ) (n := (⊤ : ℕ∞)) (t := fun x : U ↦ {r : ℝ | ((r : ℝ) : EReal) < f x})
    hconv hloc
  classical
  let h : E → ℝ := fun y ↦ if hy : y ∈ O then g ⟨y, hy⟩ else 0
  refine ⟨h, ?_, fun y hy ↦ ?_⟩
  · intro y hy
    have hgh : (fun z : U ↦ h z) = g := by
      funext z
      simp [h]
    have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z : U ↦ h z) ⟨y, hy⟩ := by
      rw [hgh]
      exact g.contMDiff.contMDiffAt
    have hc' := (contMDiffAt_subtype_iff (U := U) (f := h) (x := ⟨y, hy⟩)).1 hc
    exact (contMDiffAt_iff_contDiffAt.1 hc').contDiffWithinAt
  · have := hg ⟨y, hy⟩
    simp only [mem_setOf_eq] at this
    simpa [h, hy] using this

end RW
