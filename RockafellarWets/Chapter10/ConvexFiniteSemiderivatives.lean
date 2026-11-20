/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite convex functions on arbitrary finite-dimensional normed spaces
-/
import RockafellarWets.Chapter10.FiniteExtremumSemiderivatives
import RockafellarWets.Chapter7.SubdifferentialRegularity
import RockafellarWets.Chapter9.LipschitzModulusCalculus
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open Set
open scoped Topology
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem semidifferentiableAt_of_convexOn_univ {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (x : E) :
    SemidifferentiableAt (fun y ↦ (f y:EReal)) x := by
  let L := toEuclidean (E := E)
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := f ∘ L.symm
  have hg : ConvexOn ℝ univ g := by simpa only [preimage_univ] using hf.comp_linearMap L.symm.toLinearMap
  have hp : IsProper (fun y ↦ (g y:EReal)) := ⟨⟨0,EReal.coe_lt_top _⟩,fun _ ↦ EReal.bot_lt_coe _⟩
  have hconv : Convex ℝ (epigraph (fun y ↦ (g y:EReal))) := by
    simpa only [epigraph,mem_univ,true_and,EReal.coe_le_coe_iff] using convexOn_iff_convex_epigraph.mp hg
  have hi : L x ∈ interior (effectiveDomain (fun y ↦ (g y:EReal))) := by
    simp [effectiveDomain]
  have hd := (semidifferentiableAt_of_convex_of_mem_interior hp hconv hi).2.2.2
  have he := hd.comp_hasFDerivAt L.hasFDerivAt
  simpa only [g,Function.comp_apply,L.symm_apply_apply] using he

theorem strictlyContinuousAt_of_convexOn_univ {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (x : E) : StrictlyContinuousAt f x := by
  obtain ⟨k,U,hU,hL⟩ := hf.locallyLipschitzOn isOpen_univ (mem_univ x)
  rw [nhdsWithin_univ] at hU
  exact strictlyContinuousAt_iff.mpr ⟨k,U,hU,hL⟩

/-- Differences of finite convex functions are semidifferentiable. -/
theorem semidifferentiableAt_convex_difference {f g : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g) (x : E) :
    SemidifferentiableAt (fun y ↦ ((f y-g y:ℝ):EReal)) x := by
  apply semidifferentiableAt_coe_iff.mpr
  intro w
  obtain ⟨a,ha⟩ := semidifferentiableAt_coe_iff.mp (semidifferentiableAt_of_convexOn_univ hf x) w
  obtain ⟨b,hb⟩ := semidifferentiableAt_coe_iff.mp (semidifferentiableAt_of_convexOn_univ hg x) w
  exact ⟨a-b,by simpa [sub_eq_add_neg] using ha.add (hb.const_smul (-1))⟩

theorem strictlyContinuousAt_convex_difference {f g : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g) (x : E) :
    StrictlyContinuousAt (fun y ↦ f y-g y) x := by
  obtain ⟨k,U,hU,hfL⟩ := strictlyContinuousAt_iff.mp (strictlyContinuousAt_of_convexOn_univ hf x)
  obtain ⟨l,V,hV,hgL⟩ := strictlyContinuousAt_iff.mp (strictlyContinuousAt_of_convexOn_univ hg x)
  apply strictlyContinuousAt_iff.mpr
  refine ⟨k+l,U∩V,Filter.inter_mem hU hV,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  calc
    dist (f y-g y) (f z-g z) ≤ dist (f y-g y) (f z-g y)+dist (f z-g y) (f z-g z) := dist_triangle ..
    _ = dist (f y) (f z)+dist (g y) (g z) := by
      simp only [sub_eq_add_neg,dist_add_right,dist_add_left,dist_neg_neg]
    _ ≤ (k:ℝ)*dist y z+(l:ℝ)*dist y z :=
      add_le_add (hfL.dist_le_mul y hy.1 z hz.1) (hgL.dist_le_mul y hy.2 z hz.2)
    _ = _ := by simp only [NNReal.coe_add,add_mul]

end
end RW
