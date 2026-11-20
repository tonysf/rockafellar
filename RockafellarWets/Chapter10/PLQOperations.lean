/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Algebraic closure properties of PLQ functions
-/
import RockafellarWets.Chapter10.PiecewiseLinearQuadratic
import Mathlib.Logic.Equiv.Fin.Basic

open Set Classical
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RW
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def QuadraticPiece.add (q r : QuadraticPiece E) : QuadraticPiece E where
  matrix := q.matrix + r.matrix
  symmetric := by intro x y; simp only [ContinuousLinearMap.add_apply,inner_add_left,inner_add_right,q.symmetric,r.symmetric]
  linear := q.linear + r.linear
  constant := q.constant + r.constant

@[simp] theorem QuadraticPiece.add_eval (q r : QuadraticPiece E) (x : E) :
    (q.add r).eval x = q.eval x + r.eval x := by
  simp only [QuadraticPiece.eval,QuadraticPiece.add,ContinuousLinearMap.add_apply,inner_add_left,inner_add_right]
  ring

def QuadraticPiece.compAffine (q : QuadraticPiece F) (A : E →L[ℝ] F) (a : F) : QuadraticPiece E where
  matrix := A.adjoint ∘L q.matrix ∘L A
  symmetric := by
    intro x y
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,q.symmetric]
  linear := A.adjoint (q.matrix a + q.linear)
  constant := q.eval a

@[simp] theorem QuadraticPiece.compAffine_eval (q : QuadraticPiece F) (A : E →L[ℝ] F)
    (a : F) (x : E) : (q.compAffine A a).eval x = q.eval (A x + a) := by
  simp only [QuadraticPiece.eval,QuadraticPiece.compAffine,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_left,
    map_add,inner_add_left,inner_add_right]
  rw [← q.symmetric a (A x),real_inner_comm (A x) (q.matrix a)]
  ring

/-- **Exercise 10.22(a)**, PLQ closure under addition, with no qualification. -/
theorem IsPiecewiseLinearQuadratic.add {f g : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hg : IsPiecewiseLinearQuadratic g) :
    IsPiecewiseLinearQuadratic (fun x ↦ f x + g x) := by
  have hfb := hf.ne_bot
  have hgb := hg.ne_bot
  obtain ⟨m,C,q,hC,hfdom,hf⟩ := hf
  obtain ⟨n,D,r,hD,hgdom,hg⟩ := hg
  let e := (@finProdFinEquiv m n).symm
  refine ⟨m*n,fun k ↦ C (e k).1 ∩ D (e k).2,fun k ↦ (q (e k).1).add (r (e k).2),
    fun k ↦ (hC _).inter (hD _),?_,?_⟩
  · ext x
    constructor
    · intro hx
      have hfx : x ∈ effectiveDomain f := by
        by_contra h
        have he : f x = ⊤ := by simpa [effectiveDomain] using h
        have hsum : f x + g x = ⊤ := by rw [he,EReal.top_add_of_ne_bot (hgb x)]
        exact (ne_of_lt hx) hsum
      have hgx : x ∈ effectiveDomain g := by
        by_contra h
        have he : g x = ⊤ := by simpa [effectiveDomain] using h
        have hsum : f x + g x = ⊤ := by rw [he,EReal.add_top_of_ne_bot (hfb x)]
        exact (ne_of_lt hx) hsum
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hfdom ▸ hfx)
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hgdom ▸ hgx)
      exact mem_iUnion.mpr ⟨finProdFinEquiv (i,j),by simpa [e] using And.intro hi hj⟩
    · intro hx
      obtain ⟨k,hk⟩ := mem_iUnion.mp hx
      change f x + g x < ⊤
      rw [hf _ _ hk.1,hg _ _ hk.2,← EReal.coe_add]
      exact EReal.coe_lt_top _
  · intro k x hx
    change f x + g x = ((q (e k).1).add (r (e k).2)).eval x
    rw [hf _ _ hx.1,hg _ _ hx.2,← EReal.coe_add,QuadraticPiece.add_eval]

/-- Translation followed by a linear inverse image preserves polyhedrality. -/
theorem IsPolyhedral.affine_preimage {D : Set F} (hD : IsPolyhedral D)
    (A : E →L[ℝ] F) (a : F) : IsPolyhedral ((fun x ↦ A x + a) ⁻¹' D) := by
  have htrans := hD.affine_image (AffineEquiv.constVAdd ℝ F (-a) : F →ᵃ[ℝ] F)
  have he : (fun x ↦ A x + a) ⁻¹' D = A ⁻¹' ((AffineEquiv.constVAdd ℝ F (-a) : F →ᵃ[ℝ] F) '' D) := by
    ext x
    constructor
    · intro hx
      exact ⟨A x+a,hx,by simp [AffineEquiv.constVAdd_apply,add_comm]⟩
    · rintro ⟨y,hy,he⟩
      have hh : A x+a = y := by simpa [AffineEquiv.constVAdd_apply,add_comm] using congrArg (fun z ↦ a+z) he.symm
      simpa [hh] using hy
  rw [he]
  exact htrans.continuousLinear_preimage A

/-- **Exercise 10.22(b)**, PLQ closure under arbitrary affine composition. -/
theorem IsPiecewiseLinearQuadratic.compAffine {g : F → EReal}
    (hg : IsPiecewiseLinearQuadratic g) (A : E →L[ℝ] F) (a : F) :
    IsPiecewiseLinearQuadratic (fun x ↦ g (A x+a)) := by
  obtain ⟨m,C,q,hC,hdom,hg⟩ := hg
  refine ⟨m,fun i ↦ (fun x ↦ A x+a) ⁻¹' C i,fun i ↦ (q i).compAffine A a,
    fun i ↦ (hC i).affine_preimage A a,?_,?_⟩
  · ext x
    change A x+a ∈ effectiveDomain g ↔ _
    rw [hdom]
    simp
  · intro i x hx
    change g (A x+a) = ((q i).compAffine A a).eval x
    rw [hg i (A x+a) hx,QuadraticPiece.compAffine_eval]

end RW
end
