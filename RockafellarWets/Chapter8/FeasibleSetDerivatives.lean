/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Proto-differentiability of feasible-set mappings
-/

import RockafellarWets.Chapter8.ProtoDifferentiability
import RockafellarWets.Chapter6.ConstraintTangents

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E P G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- The feasible-set mapping with smooth mixed parameter and state constraints. -/
def parameterConstraintMapping (X : Set E) (D : Set G) (F : E × P → G) (t : P) : Set E :=
  {x | x ∈ X ∧ F (x,t) ∈ D}

/-- **Exercise 8.42**. The condition on the two partial adjoints implies
graphical regularity, proto-differentiability, and both multiplier formulas. -/
theorem parameterConstraintMapping_derivatives {X : Set E} {D : Set G} {F : E × P → G}
    (hX : IsClosed X) (hD : IsClosed D) (hF : ContDiff ℝ 1 F) {t : P} {x : E}
    (hx : x ∈ parameterConstraintMapping X D F t) (hXreg : IsClarkeRegularAt X x)
    (hDreg : IsClarkeRegularAt D (F (x,t)))
    (hCQ : let A := fderiv ℝ F (x,t)
      let Ax := A.comp (ContinuousLinearMap.inl ℝ E P)
      let At := A.comp (ContinuousLinearMap.inr ℝ E P)
      ∀ y ∈ normalCone D (F (x,t)), -(Ax.adjoint y) ∈ normalCone X x → At.adjoint y = 0 → y = 0) :
    let S := parameterConstraintMapping X D F
    let A := fderiv ℝ F (x,t)
    let Ax := A.comp (ContinuousLinearMap.inl ℝ E P)
    let At := A.comp (ContinuousLinearMap.inr ℝ E P)
    IsGraphicallyRegularAt S t x ∧ IsProtoDifferentiableAt S t x ∧
      (∀ s, graphicalDerivative S t x s = {w | w ∈ tangentCone X x ∧
        Ax w + At s ∈ tangentCone D (F (x,t))}) ∧
      ∀ v, coderivative S t x v =
        At.adjoint '' {y | y ∈ normalCone D (F (x,t)) ∧ -(v + Ax.adjoint y) ∈ normalCone X x} := by
  let S := parameterConstraintMapping X D F
  let p := WithLp.toLp 2 (t,x)
  let C := l2ProdSet (univ : Set P) X
  let A := fderiv ℝ F (x,t)
  let Ax := A.comp (ContinuousLinearMap.inl ℝ E P)
  let At := A.comp (ContinuousLinearMap.inr ℝ E P)
  let flip : WithLp 2 (P × E) →L[ℝ] E × P :=
    (LinearIsometryEquiv.prodComm ℝ P E).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ P E).toContinuousLinearMap
  let R := F ∘ flip
  let B := A.comp flip
  have hR : ContDiff ℝ 1 R := hF.comp flip.contDiff
  have hp : p ∈ C ∩ R ⁻¹' D := ⟨⟨trivial, hx.1⟩, hx.2⟩
  have heq : euclideanSvGraph S = C ∩ R ⁻¹' D := by
    ext q
    change (_ ∧ _) ↔ ((_ ∧ _) ∧ _)
    tauto
  have hB : fderiv ℝ R p = B := ((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp p
    flip.hasFDerivAt).fderiv
  have hBq (q : WithLp 2 (P × E)) : B q = Ax q.snd + At q.fst := by
    change A (q.snd,q.fst) = A (q.snd,0) + A (0,q.fst)
    rw [← map_add]; simp
  have hBadj (y : G) : B.adjoint y = WithLp.toLp 2 (At.adjoint y, Ax.adjoint y) := by
    apply ext_inner_right ℝ
    intro q
    rw [ContinuousLinearMap.adjoint_inner_left, WithLp.prod_inner_apply, hBq, inner_add_right]
    change _ = ⟪At.adjoint y,q.fst⟫_ℝ + ⟪Ax.adjoint y,q.snd⟫_ℝ
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, add_comm]
  have hNc : normalCone C p = l2ProdSet ({0} : Set P) (normalCone X x) := by
    rw [show normalCone C p = _ from normalCone_l2ProdSet univ X t x, normalCone_univ]
  have hqual : NormalConstraintQualification C D (fderiv ℝ R p) p (R p) := by
    intro y hy hn
    rw [hB, hBadj, hNc] at hn
    have hfst : -At.adjoint y = 0 := hn.1
    exact hCQ y hy hn.2 (neg_eq_zero.mp hfst)
  have hCreg : IsClarkeRegularAt C p := (isClarkeRegularAt_l2ProdSet_iff isClosed_univ hX (mem_univ t) hx.1).mpr
    ⟨isClarkeRegularAt_univ _, hXreg⟩
  have hCcl : IsClosed C := isClosed_l2ProdSet isClosed_univ hX
  obtain ⟨hreg, hnormal⟩ := clarkeRegularity_constraints hCcl hD hR hp hqual hCreg hDreg
  have htangent := (tangentCone_constraints_of_isClarkeRegularAt hCcl hD hR hp hqual hCreg hDreg).1
  have hTc : tangentCone C p = l2ProdSet univ (tangentCone X x) := by
    rw [show tangentCone C p = _ from tangentCone_l2ProdSet univ X (mem_univ t) hx.1
      (isGeometricallyDerivable_univ _) (isGeometricallyDerivable_of_isClarkeRegularAt hx.1 hXreg), tangentCone_univ]
  have hSreg : IsGraphicallyRegularAt S t x := by
    change IsClarkeRegularAt (euclideanSvGraph S) p
    rwa [heq]
  refine ⟨hSreg, hSreg.isProtoDifferentiableAt hx, ?_, ?_⟩
  · intro s
    ext w
    change WithLp.toLp 2 (s,w) ∈ tangentCone (euclideanSvGraph S) p ↔ _
    rw [heq, htangent, hB, hTc]
    change ((True ∧ w ∈ tangentCone X x) ∧ B (WithLp.toLp 2 (s,w)) ∈ tangentCone D (F (x,t))) ↔ _
    rw [hBq]
    simp only [true_and]; rfl
  · intro v
    ext a
    change WithLp.toLp 2 (a,-v) ∈ normalCone (euclideanSvGraph S) p ↔ _
    rw [heq, hnormal, hB, hNc]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, q, hq, he⟩
      rw [hBadj] at he
      have hfst := congrArg (fun q : WithLp 2 (P × E) ↦ q.fst) he
      have hsnd := congrArg (fun q : WithLp 2 (P × E) ↦ q.snd) he
      change At.adjoint y + q.fst = a at hfst
      change Ax.adjoint y + q.snd = -v at hsnd
      have h₀ : q.fst = 0 := hq.1
      have hq' : -(v + Ax.adjoint y) = q.snd := by rw [← neg_inj, neg_neg]; abel_nf at hsnd ⊢; grind
      exact ⟨y, ⟨hy, hq' ▸ hq.2⟩, by simpa only [h₀, add_zero] using hfst⟩
    · rintro ⟨y, ⟨hy, hneg⟩, rfl⟩
      refine ⟨_, ⟨y, hy, rfl⟩, WithLp.toLp 2 (0, -(v + Ax.adjoint y)), ⟨rfl,hneg⟩, ?_⟩
      rw [hBadj]
      apply (WithLp.equiv 2 _).injective
      change (At.adjoint y + 0, Ax.adjoint y + -(v+Ax.adjoint y)) = _
      simp
      rfl

end RW
