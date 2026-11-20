/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Derivatives on one polyhedral piece
-/
import RockafellarWets.Chapter10.PiecewiseLinearQuadratic
import RockafellarWets.Chapter10.FiniteInfimumSubderivatives
import RockafellarWets.Chapter6.PolyhedralCones
import RockafellarWets.Chapter8.IndicatorSubgradients
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Filter Topology Classical
open scoped InnerProductSpace

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Quadratic pieces are smooth of every finite order. -/
theorem QuadraticPiece.contDiff (q : QuadraticPiece E) (n : ℕ) : ContDiff ℝ n q.eval := by
  exact ((contDiff_const.mul (contDiff_id.inner ℝ q.matrix.contDiff)).add
    (contDiff_const.inner ℝ contDiff_id)).add contDiff_const

def restrictedQuadratic (C : Set E) (q : QuadraticPiece E) (x : E) : EReal :=
  indicatorVA C x + (q.eval x : EReal)

@[simp] theorem restrictedQuadratic_of_mem {C : Set E} (q : QuadraticPiece E) {x : E}
    (hx : x ∈ C) : restrictedQuadratic C q x = q.eval x := by simp [restrictedQuadratic,indicatorVA,hx]

@[simp] theorem restrictedQuadratic_of_not_mem {C : Set E} (q : QuadraticPiece E) {x : E}
    (hx : x ∉ C) : restrictedQuadratic C q x = ⊤ := by simp [restrictedQuadratic,indicatorVA,hx]

/-- A fixed ray enters a polyhedron exactly for tangent directions. -/
theorem IsPolyhedral.eventually_ray_mem_iff {C : Set E} (hC : IsPolyhedral C)
    {x : E} (hx : x ∈ C) (w : E) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), x+t • w ∈ C ↔ w ∈ tangentCone C x := by
  have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hy : Tendsto (fun t : ℝ ↦ x+t • w) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add (ht.smul_const w)
  filter_upwards [hy.eventually (hC.eventually_mem_iff_sub_mem_tangentCone hx),self_mem_nhdsWithin] with t he ht
  rw [he,add_sub_cancel_left]
  constructor
  · intro hw
    have h := (isCone_tangentCone hx).2 hw (inv_pos.mpr ht)
    simpa [smul_smul,inv_mul_cancel₀ (ne_of_gt (show 0 < t from ht))] using h
  · exact fun hw ↦ (isCone_tangentCone hx).2 hw ht

/-- The subderivative of a quadratic restricted to a polyhedron. -/
theorem subderivative_restrictedQuadratic {C : Set E} (q : QuadraticPiece E)
    {x : E} (hx : x ∈ C) (w : E) :
    subderivative (restrictedQuadratic C q) x w =
      if w ∈ tangentCone C x then (fderiv ℝ q.eval x w : EReal) else ⊤ := by
  have hd := ((q.contDiff 1).differentiable (by norm_num) x).hasFDerivAt
  unfold restrictedQuadratic
  rw [subderivative_add_differentiable (indicatorVA_apply_mem hx) hd,
    subderivative_indicatorVA hx]
  by_cases hw : w ∈ tangentCone C x <;> simp [indicatorVA,hw]

/-- Polyhedrality turns this subderivative into the fixed-direction limit. -/
theorem hasOneSidedDirDeriv_restrictedQuadratic {C : Set E} (hC : IsPolyhedral C)
    (q : QuadraticPiece E) {x : E} (hx : x ∈ C) (w : E) :
    HasOneSidedDirDeriv (restrictedQuadratic C q) x w
      (subderivative (restrictedQuadratic C q) x w) := by
  rw [subderivative_restrictedQuadratic q hx w]
  have hbase := restrictedQuadratic_of_mem q hx
  refine ⟨by rw [hbase]; exact EReal.coe_ne_bot _,by rw [hbase]; exact EReal.coe_ne_top _,?_⟩
  by_cases hw : w ∈ tangentCone C x
  · rw [if_pos hw]
    have hd := ((q.contDiff 1).differentiable (by norm_num) x).hasFDerivAt.hasDirectionalSemiderivative w
    apply (hasDirectionalSemiderivative_iff.mp hd).hasOneSidedDirDeriv.2.2.congr'
    filter_upwards [hC.eventually_ray_mem_iff hx w] with t ht
    unfold differenceQuotient
    rw [restrictedQuadratic_of_mem q (ht.mpr hw),hbase]
  · rw [if_neg hw]
    apply tendsto_const_nhds.congr'
    filter_upwards [hC.eventually_ray_mem_iff hx w,self_mem_nhdsWithin] with t ht htpos
    exact (differenceQuotient_eq_top htpos hbase (restrictedQuadratic_of_not_mem q (mt ht.mp hw))).symm

end RW
end
