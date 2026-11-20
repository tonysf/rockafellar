/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite intersections of amenable sets
-/
import RockafellarWets.Chapter10.AmenableLocalGeometry
import RockafellarWets.Chapter6.IntersectionCones

open Set Filter Topology
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RW
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type u} [Fintype ι]

/-- **Exercise 10.26(c)**: a qualified finite intersection preserves the
smoothness order and the polyhedral outer constraints of its factors. -/
def AmenableSetModel.iInter {C : ι → Set E} {x : E} {r : ℕ} {full : Bool}
    (M : ∀i, AmenableSetModel (C i) x r full) (hr : 1 ≤ r)
    (hQ : IntersectionConstraintQualification C x) : AmenableSetModel (⋂i,C i) x r full where
  Target := PiLp 2 (fun i ↦ (M i).Target)
  constraint := l2PiSet (fun i ↦ (M i).constraint)
  inner := fun y ↦ WithLp.toLp 2 (fun i ↦ (M i).inner y)
  neighborhood := ⋂i,(M i).neighborhood
  isOpen := isOpen_iInter_of_finite (fun i ↦ (M i).isOpen)
  mem := mem_iInter.mpr (fun i ↦ (M i).mem)
  base := mem_iInter.mpr (fun i ↦ (M i).base)
  closed := isClosed_l2PiSet (fun i ↦ (M i).closed)
  convex := by
    intro v hv w hw a b ha hb hab i
    exact (M i).convex (hv i) (hw i) ha hb hab
  smooth := (PiLp.continuousLinearEquiv 2 ℝ (fun i ↦ (M i).Target)).symm.contDiff.contDiffOn.comp
    (contDiffOn_pi.mpr (fun i ↦ (M i).smooth.mono (iInter_subset _ i))) (fun _ _ ↦ mem_univ _)
  eqOn := by
    intro y hy
    simp only [mem_iInter,mem_l2PiSet]
    exact forall_congr' (fun i ↦ (M i).eqOn y (mem_iInter.mp hy i))
  qualification := by
    intro v hv hz
    rw [normalCone_l2PiSet] at hv
    have hmd (i : ι) := (((M i).smooth x (M i).mem).contDiffAt ((M i).isOpen.mem_nhds (M i).mem)).differentiableAt
      (by exact_mod_cast (show r ≠ 0 by omega))
    have hd := (PiLp.continuousLinearEquiv 2 ℝ (fun i ↦ (M i).Target)).symm.toContinuousLinearMap.hasFDerivAt.comp x
      (hasFDerivAt_pi.mpr (fun i ↦ (hmd i).hasFDerivAt))
    change HasFDerivAt (fun y ↦ WithLp.toLp 2 (fun i ↦ (M i).inner y)) _ x at hd
    have ha : (fderiv ℝ (fun y ↦ WithLp.toLp 2 (fun i ↦ (M i).inner y)) x).adjoint v =
        ∑i,(fderiv ℝ (M i).inner x).adjoint (v i) := by
      rw [hd.fderiv]
      apply ext_inner_right ℝ
      intro w
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp only [sum_inner,ContinuousLinearMap.adjoint_inner_left]
      change ⟪v,WithLp.toLp 2 (fun i ↦ fderiv ℝ (M i).inner x w)⟫_ℝ = _
      simp [PiLp.inner_apply]
    rw [ha] at hz
    have hn (i : ι) : (fderiv ℝ (M i).inner x).adjoint (v i) ∈ normalCone (C i) x := by
      rw [((M i).cones hr).2.1]
      exact ⟨v i,hv i,rfl⟩
    have hh := hQ (fun i ↦ (fderiv ℝ (M i).inner x).adjoint (v i)) hn hz
    ext i
    exact (M i).qualification (v i) (hv i) (hh i)
  polyhedral := by
    intro hf
    have hP (i : ι) : IsPolyhedral ((PiLp.proj (𝕜 := ℝ) 2 (fun i ↦ (M i).Target) i) ⁻¹' (M i).constraint) :=
      ((M i).polyhedral hf).continuousLinear_preimage _
    have hh := IsPolyhedral.iInter_finset Finset.univ
      (fun i ↦ (PiLp.proj (𝕜 := ℝ) 2 (fun i ↦ (M i).Target) i) ⁻¹' (M i).constraint) (fun i _ ↦ hP i)
    convert hh using 1
    ext v
    simp [l2PiSet]

theorem SetAmenableAt.iInter {C : ι → Set E} {x : E}
    (hC : ∀i, SetAmenableAt (C i) x) (hQ : IntersectionConstraintQualification C x) :
    SetAmenableAt (⋂i,C i) x := by
  let M := fun i ↦ Classical.choice (hC i)
  exact ⟨AmenableSetModel.iInter M le_rfl hQ⟩

theorem SetStronglyAmenableAt.iInter {C : ι → Set E} {x : E}
    (hC : ∀i, SetStronglyAmenableAt (C i) x) (hQ : IntersectionConstraintQualification C x) :
    SetStronglyAmenableAt (⋂i,C i) x := by
  let M := fun i ↦ Classical.choice (hC i)
  exact ⟨AmenableSetModel.iInter M (by norm_num) hQ⟩

theorem SetFullyAmenableAt.iInter {C : ι → Set E} {x : E}
    (hC : ∀i, SetFullyAmenableAt (C i) x) (hQ : IntersectionConstraintQualification C x) :
    SetFullyAmenableAt (⋂i,C i) x := by
  let M := fun i ↦ Classical.choice (hC i)
  exact ⟨AmenableSetModel.iInter M (by norm_num) hQ⟩

end RW
end
