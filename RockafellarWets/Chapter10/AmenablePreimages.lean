/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Qualified preimages of amenable sets
-/
import RockafellarWets.Chapter10.AmenableRegularity
import RockafellarWets.Chapter10.AmenabilityPersistence
import Mathlib.Analysis.Calculus.ContDiff.Comp

open Set Filter Topology

noncomputable section
namespace RW
universe u
variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Exercise 10.26(d)**: composing a set model with a qualified smooth
map preserves its smoothness order and its polyhedral outer constraint. -/
def AmenableSetModel.preimage {D : Set F} {f : E → F} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableSetModel D (f x) r full) (hr : 1 ≤ r) (hf : ContDiff ℝ r f)
    (hQ : ∀ v ∈ normalCone D (f x), (fderiv ℝ f x).adjoint v = 0 → v = 0) :
    AmenableSetModel (f ⁻¹' D) x r full where
  Target := M.Target
  constraint := M.constraint
  inner := M.inner ∘ f
  neighborhood := f ⁻¹' M.neighborhood
  isOpen := M.isOpen.preimage hf.continuous
  mem := M.mem
  base := M.base
  closed := M.closed
  convex := M.convex
  smooth := M.smooth.comp hf.contDiffOn (fun _ hy ↦ hy)
  eqOn := fun y hy ↦ M.eqOn (f y) hy
  qualification := by
    intro v hv hzero
    have hmd : DifferentiableAt ℝ M.inner (f x) :=
      ((M.smooth _ M.mem).contDiffAt (M.isOpen.mem_nhds M.mem)).differentiableAt (by exact_mod_cast (show r ≠ 0 by omega))
    have hfd : DifferentiableAt ℝ f x := hf.differentiable (by exact_mod_cast (show r ≠ 0 by omega)) x
    rw [fderiv_comp x hmd hfd,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply] at hzero
    have hn : (fderiv ℝ M.inner (f x)).adjoint v ∈ normalCone D (f x) := by
      rw [(M.cones hr).2.1]
      exact ⟨v,hv,rfl⟩
    exact M.qualification v hv (hQ _ hn hzero)
  polyhedral := M.polyhedral

/-- **Exercise 10.26(d)**, amenability under C¹ preimages. -/
theorem SetAmenableAt.preimage {D : Set F} {f : E → F} {x : E}
    (hD : SetAmenableAt D (f x)) (hf : ContDiff ℝ 1 f)
    (hQ : ∀ v ∈ normalCone D (f x), (fderiv ℝ f x).adjoint v = 0 → v = 0) :
    SetAmenableAt (f ⁻¹' D) x := by
  obtain ⟨M⟩ := hD
  exact ⟨M.preimage le_rfl hf hQ⟩

theorem SetStronglyAmenableAt.preimage {D : Set F} {f : E → F} {x : E}
    (hD : SetStronglyAmenableAt D (f x)) (hf : ContDiff ℝ 2 f)
    (hQ : ∀ v ∈ normalCone D (f x), (fderiv ℝ f x).adjoint v = 0 → v = 0) :
    SetStronglyAmenableAt (f ⁻¹' D) x := by
  obtain ⟨M⟩ := hD
  exact ⟨M.preimage (by norm_num) hf hQ⟩

theorem SetFullyAmenableAt.preimage {D : Set F} {f : E → F} {x : E}
    (hD : SetFullyAmenableAt D (f x)) (hf : ContDiff ℝ 2 f)
    (hQ : ∀ v ∈ normalCone D (f x), (fderiv ℝ f x).adjoint v = 0 → v = 0) :
    SetFullyAmenableAt (f ⁻¹' D) x := by
  obtain ⟨M⟩ := hD
  exact ⟨M.preimage (by norm_num) hf hQ⟩

/-- **Exercise 10.26(d)**, the exact normal and tangent formulas. -/
theorem SetAmenableAt.preimage_cones {D : Set F} {f : E → F} {x : E}
    (hD : SetAmenableAt D (f x)) (hf : ContDiff ℝ 1 f)
    (hQ : ∀ v ∈ normalCone D (f x), (fderiv ℝ f x).adjoint v = 0 → v = 0) :
    normalCone (f ⁻¹' D) x = (fderiv ℝ f x).adjoint '' normalCone D (f x) ∧
      tangentCone (f ⁻¹' D) x = (fderiv ℝ f x) ⁻¹' tangentCone D (f x) := by
  obtain ⟨M⟩ := hD
  have hmd : DifferentiableAt ℝ M.inner (f x) :=
    ((M.smooth _ M.mem).contDiffAt (M.isOpen.mem_nhds M.mem)).differentiableAt (by norm_num)
  have hfd : DifferentiableAt ℝ f x := hf.differentiable (by norm_num) x
  have hcomp : fderiv ℝ (M.preimage le_rfl hf hQ).inner x =
      (fderiv ℝ M.inner (f x)) ∘L (fderiv ℝ f x) := fderiv_comp x hmd hfd
  have hC := (M.preimage le_rfl hf hQ).cones le_rfl
  have hD := M.cones le_rfl
  constructor
  · rw [hC.2.1,hD.2.1,hcomp,ContinuousLinearMap.adjoint_comp,image_image]
    rfl
  · rw [hC.2.2,hD.2.2,hcomp]
    rfl

end RW
end
