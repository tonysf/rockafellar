/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A dimension restriction in inverse localization

The inclusion of a line in a plane has injective strict derivative and convex
singleton fibers, but its inverse has empty values off the line. Thus the
sufficiency assertion of9.54(b) needs an ambient dimension restriction.
-/

import RockafellarWets.Chapter9.SingleValuedLocalizations

open Set Metric

namespace RW

def lineEmbeddingMapping (x : ℝ) : Set (ℝ × ℝ) := {(x,0)}

theorem lineEmbeddingMapping_convexValued (x : ℝ) : Convex ℝ (lineEmbeddingMapping x) :=
  convex_singleton _

theorem lineEmbeddingMapping_continuous : Continuous (fun x : ℝ ↦ (x,(0:ℝ))) :=
  continuous_id.prodMk continuous_const

theorem lineEmbeddingMapping_svIsc : SvIsc lineEmbeddingMapping := by
  intro x u hu
  obtain rfl := mem_singleton_iff.mp hu
  intro V hV
  filter_upwards [lineEmbeddingMapping_continuous.continuousAt hV] with a ha
  exact ⟨(a,0),mem_singleton _,ha⟩

theorem lineEmbeddingMapping_strict_inverse_kernel :
    svInv (strictGraphicalDerivative lineEmbeddingMapping 0 (0,0)) (0,0) = {0} := by
  ext w
  change (0,0) ∈ strictGraphicalDerivative (fun a ↦ {(ContinuousLinearMap.inl ℝ ℝ ℝ) a})
    0 ((ContinuousLinearMap.inl ℝ ℝ ℝ) 0) w ↔ w ∈ ({0} : Set ℝ)
  rw [strictGraphicalDerivative_singleton_continuousLinearMap]
  simp [eq_comm]

/-- Inverse fibers off the embedded line preclude a single-valued local
inverse, despite the zero strict inverse kernel. -/
theorem lineEmbeddingMapping_no_lipschitz_inverse_localization :
    ¬ HasLipschitzSingleValuedLocalization (svInv lineEmbeddingMapping) (0,0) 0 := by
  rintro ⟨g,r,s,k,hr,hs,hg,hlip,hfiber⟩
  let a : ℝ × ℝ := (0,r/2)
  have ha : a ∈ ball (0,0) r := by
    rw [← ball_prod_same]
    refine ⟨mem_ball_self hr,?_⟩
    change dist (r/2) (0:ℝ) < r
    rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)]
    linarith
  have hm : g a ∈ svInv lineEmbeddingMapping a ∩ ball (0:ℝ) s :=
    (hfiber a ha).symm ▸ mem_singleton (g a)
  have he : a = (g a,0) := mem_singleton_iff.mp hm.1
  have he₂ := congrArg Prod.snd he
  change r/2 = 0 at he₂
  linarith

end RW
