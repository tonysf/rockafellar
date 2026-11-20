/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A smooth global representative of a local smooth mapping
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Filter Topology Metric

namespace RW
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map smooth on an open neighborhood has a globally smooth representative
with the same germ. This allows global chain rules to apply to local models. -/
theorem exists_contDiff_eventuallyEq_of_contDiffOn {f : E → F} {V : Set E} {x : E}
    {n : ℕ∞} (hV : IsOpen V) (hx : x ∈ V) (hf : ContDiffOn ℝ n f V) :
    ∃ g : E → F, ContDiff ℝ n g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hx)
  let b : ContDiffBump x := ⟨r / 4,r / 2,by positivity,by linarith⟩
  let g : E → F := fun y ↦ b y • f y
  have hbsub : tsupport b ⊆ V := by
    rw [b.tsupport_eq]
    exact fun y hy ↦ hsub (lt_of_le_of_lt hy (by change r / 2 < r; linarith))
  refine ⟨g,contDiff_iff_contDiffAt.mpr (fun y ↦ ?_),?_⟩
  · by_cases hy : y ∈ V
    · exact b.contDiff.contDiffAt.smul ((hf y hy).contDiffAt (hV.mem_nhds hy))
    · have hz : b =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hy (hbsub h))
      apply (contDiff_const : ContDiff ℝ n (fun _ : E ↦ (0 : F))).contDiffAt.congr_of_eventuallyEq
      filter_upwards [hz] with z hz
      simp [g,hz]
  · filter_upwards [b.eventuallyEq_one] with y hy
    simp [g,hy]

end RW
