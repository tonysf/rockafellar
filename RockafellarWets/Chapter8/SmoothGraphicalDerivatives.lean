/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Graphical differentiation of smooth mappings
-/

import RockafellarWets.Chapter8.GraphicalRegularity
import RockafellarWets.Chapter6.SmoothManifolds

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Example 8.34**. A smooth graph is regular. Both graphical derivatives
are its ordinary derivative, and both coderivatives are the adjoint. -/
theorem graphicalDerivatives_of_contDiffAt {G : E → F} {x : E} (hG : ContDiffAt ℝ 1 G x) :
    IsGraphicallyRegularAt (svSingleton G) x (G x) ∧
    graphicalDerivative (svSingleton G) x (G x) = svSingleton (fderiv ℝ G x) ∧
    regularGraphicalDerivative (svSingleton G) x (G x) = svSingleton (fderiv ℝ G x) ∧
    coderivative (svSingleton G) x (G x) = svSingleton ((fderiv ℝ G x).adjoint) ∧
    regularCoderivative (svSingleton G) x (G x) = svSingleton ((fderiv ℝ G x).adjoint) := by
  let T := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap
  let P := (ContinuousLinearMap.fst ℝ E F).comp T
  let Q := (ContinuousLinearMap.snd ℝ E F).comp T
  let p := WithLp.toLp 2 (x,G x)
  let C := euclideanSvGraph (svSingleton G)
  let R (q : WithLp 2 (E × F)) := G (P q) - Q q
  let A := fderiv ℝ G x
  let B := A.comp P - Q
  have hp : p ∈ C := rfl
  have hR : ContDiffAt ℝ 1 R p := (hG.comp p P.contDiff.contDiffAt).sub Q.contDiff.contDiffAt
  have hB : fderiv ℝ R p = B :=
    ((hG.differentiableAt one_ne_zero).hasFDerivAt.comp p P.hasFDerivAt |>.sub Q.hasFDerivAt).fderiv
  have hsurj : Function.Surjective (fderiv ℝ R p) := by
    rw [hB]
    intro y
    refine ⟨WithLp.toLp 2 (0, -y), ?_⟩
    change A 0 - -y = y
    simp
  have heq : C = R ⁻¹' {0} := by
    ext q
    change q.snd = G q.fst ↔ G q.fst - q.snd = 0
    rw [sub_eq_zero, eq_comm]
  have hloc := Filter.EventuallyEq.of_eq (l := 𝓝 p) heq
  have hreg : IsGraphicallyRegularAt (svSingleton G) x (G x) :=
    isClarkeRegularAt_smoothManifold hp hloc hR hsurj
  have htan := tangentCone_smoothManifold hp hloc hR hsurj
  have hD : graphicalDerivative (svSingleton G) x (G x) = svSingleton A := by
    ext w z
    change WithLp.toLp 2 (w,z) ∈ tangentCone C p ↔ z = A w
    rw [htan, hB]
    change A w - z = 0 ↔ z = A w
    rw [sub_eq_zero, eq_comm]
  have hn := normalCone_smoothManifold hp hloc hR hsurj
  have hadj (y : F) : B.adjoint y = WithLp.toLp 2 (A.adjoint y, -y) := by
    apply ext_inner_right ℝ
    intro q
    rw [ContinuousLinearMap.adjoint_inner_left, WithLp.prod_inner_apply]
    change ⟪y, A q.fst - q.snd⟫_ℝ = ⟪A.adjoint y, q.fst⟫_ℝ + ⟪-y, q.snd⟫_ℝ
    rw [ContinuousLinearMap.adjoint_inner_left, inner_sub_right, inner_neg_left, sub_eq_add_neg]
  have hN : coderivative (svSingleton G) x (G x) = svSingleton A.adjoint := by
    ext y v
    change WithLp.toLp 2 (v,-y) ∈ normalCone C p ↔ v = A.adjoint y
    rw [hn, hB]
    constructor
    · rintro ⟨y', hym⟩
      rw [hadj] at hym
      have h₁ := congrArg (fun q : WithLp 2 (E × F) ↦ q.fst) hym
      have h₂ := congrArg (fun q : WithLp 2 (E × F) ↦ q.snd) hym
      change -y' = -y at h₂
      change A.adjoint y' = v at h₁
      exact h₁.symm.trans (congrArg (fun t : F ↦ A.adjoint t) (neg_injective h₂))
    · rintro rfl
      exact ⟨y, hadj y⟩
  have hfeas : G x ∈ svSingleton G x := rfl
  have hDr := (isGraphicallyRegularAt_iff_graphicalDerivative_eq_regular hfeas hreg.1).mp hreg
  have hNr := (isGraphicallyRegularAt_iff_coderivative_eq_regular hreg.1).mp hreg
  exact ⟨hreg, hD, hDr.symm.trans hD, hN, hNr.symm.trans hN⟩

end RW
