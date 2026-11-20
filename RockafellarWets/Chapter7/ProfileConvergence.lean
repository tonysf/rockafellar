/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convergence of extended real values and of their profiles

The ordinary set limits of the upper and lower rays detect both halves of
convergence in the order topology on the extended reals, including at infinity.
-/

import RockafellarWets.Chapter5.ProfileMappings
import RockafellarWets.Chapter5.ContinuousUniformConvergence

open Filter Set Topology

namespace RW

private theorem pkConverges_iff_two_inclusions {Y : Type*} [TopologicalSpace Y]
    {C : ℕ → Set Y} {D : Set Y} :
    PKConverges C D ↔ outerSetLimit C ⊆ D ∧ D ⊆ innerSetLimit C := by
  have hi := innerSetLimit_subset_outerSetLimit C
  exact ⟨fun h ↦ ⟨h.outer_eq.subset, h.inner_eq.symm.subset⟩, fun ⟨ho, hd⟩ ↦
    ⟨(hi.trans ho).antisymm hd, ho.antisymm (hd.trans hi)⟩⟩

/-- A sequence of extended real values converges exactly when its
epigraphical profiles converge. -/
theorem pkConverges_epiProfile_iff_tendsto (a : ℕ → EReal) (b : EReal) :
    PKConverges (fun n ↦ {t : ℝ | a n ≤ (t : EReal)}) {t : ℝ | b ≤ (t : EReal)} ↔
      Tendsto a atTop (𝓝 b) := by
  rw [pkConverges_iff_two_inclusions, tendsto_order]
  exact and_congr (outerSetLimitAlong_epiProfile_subset_iff id b (map a atTop))
    (epiProfile_subset_innerSetLimitAlong_iff id b (map a atTop))

/-- The hypographical profiles give the same characterization. -/
theorem pkConverges_hypoProfile_iff_tendsto (a : ℕ → EReal) (b : EReal) :
    PKConverges (fun n ↦ {t : ℝ | (t : EReal) ≤ a n}) {t : ℝ | (t : EReal) ≤ b} ↔
      Tendsto a atTop (𝓝 b) := by
  rw [pkConverges_iff_two_inclusions, tendsto_order, and_comm]
  exact and_congr (hypoProfile_subset_innerSetLimitAlong_iff id b (map a atTop))
    (outerSetLimitAlong_hypoProfile_subset_iff id b (map a atTop))

/-- Continuous convergence of functions at a point relative to a set, as
defined immediately before Theorem 7.11. -/
def ConvergesContinuouslyWithinAt {E : Type*} [TopologicalSpace E]
    (f : ℕ → E → EReal) (g : E → EReal) (X : Set E) (x : E) : Prop :=
  ∀ z : ℕ → E, (∀ n, z n ∈ X) → Tendsto z atTop (𝓝 x) →
    Tendsto (fun n ↦ f n (z n)) atTop (𝓝 (g x))

variable {E : Type*} [PseudoMetricSpace E] {f : ℕ → E → EReal}
variable {g : E → EReal} {X : Set E} {x : E}

theorem svConvergesContinuouslyWithinAt_epiProfile_iff :
    SvConvergesContinuouslyWithinAt (fun n ↦ epiProfile (f n)) (epiProfile g) X x ↔
      ConvergesContinuouslyWithinAt f g X x := by
  exact forall_congr' fun z ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    pkConverges_epiProfile_iff_tendsto (fun n ↦ f n (z n)) (g x)

theorem svConvergesContinuouslyWithinAt_hypoProfile_iff :
    SvConvergesContinuouslyWithinAt (fun n ↦ hypoProfile (f n)) (hypoProfile g) X x ↔
      ConvergesContinuouslyWithinAt f g X x := by
  exact forall_congr' fun z ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    pkConverges_hypoProfile_iff_tendsto (fun n ↦ f n (z n)) (g x)

end RW
