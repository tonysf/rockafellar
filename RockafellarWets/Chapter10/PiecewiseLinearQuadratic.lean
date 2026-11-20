/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Piecewise linear-quadratic functions
-/
import RockafellarWets.Chapter1.Defs
import RockafellarWets.Chapter3.MinkowskiWeyl
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.LocallyFinite

open Set Filter Topology Classical
open scoped InnerProductSpace

noncomputable section
namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The finite quadratic expression used on a piece in Definition 10.20. -/
structure QuadraticPiece (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  matrix : E →L[ℝ] E
  symmetric : ∀ x y, ⟪matrix x, y⟫_ℝ = ⟪x, matrix y⟫_ℝ
  linear : E
  constant : ℝ

def QuadraticPiece.eval (q : QuadraticPiece E) (x : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪x, q.matrix x⟫_ℝ + ⟪q.linear, x⟫_ℝ + q.constant

omit [FiniteDimensional ℝ E] in
theorem QuadraticPiece.continuous (q : QuadraticPiece E) : Continuous q.eval := by
  exact ((continuous_const.mul (continuous_id.inner q.matrix.continuous)).add
    (continuous_const.inner continuous_id)).add continuous_const

/-- **Definition 10.20.** The domain is a finite union of polyhedra, with a
symmetric quadratic expression on each piece. The empty-domain case is included. -/
def IsPiecewiseLinearQuadratic (f : E → EReal) : Prop :=
  ∃ m : ℕ, ∃ C : Fin m → Set E, ∃ q : Fin m → QuadraticPiece E,
    (∀ i, IsPolyhedral (C i)) ∧ effectiveDomain f = ⋃ i, C i ∧
    ∀ i x, x ∈ C i → f x = (q i).eval x

/-- The affine special case of Definition 10.20, without any convexity assumption. -/
def IsPiecewiseLinear (f : E → EReal) : Prop :=
  ∃ m : ℕ, ∃ C : Fin m → Set E, ∃ a : Fin m → E, ∃ b : Fin m → ℝ,
    (∀ i, IsPolyhedral (C i)) ∧ effectiveDomain f = ⋃ i, C i ∧
    ∀ i x, x ∈ C i → f x = (⟪a i, x⟫_ℝ + b i : ℝ)

omit [FiniteDimensional ℝ E] in
theorem IsPiecewiseLinear.isPiecewiseLinearQuadratic {f : E → EReal}
    (hf : IsPiecewiseLinear f) : IsPiecewiseLinearQuadratic f := by
  obtain ⟨m,C,a,b,hC,hdom,hf⟩ := hf
  refine ⟨m,C,fun i ↦ ⟨0,by simp,a i,b i⟩,hC,hdom,?_⟩
  intro i x hx
  simpa [QuadraticPiece.eval] using hf i x hx

omit [FiniteDimensional ℝ E] in
theorem IsPiecewiseLinearQuadratic.ne_bot {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (x : E) : f x ≠ ⊥ := by
  obtain ⟨m,C,q,hC,hdom,hf⟩ := hf
  by_cases hx : x ∈ effectiveDomain f
  · obtain ⟨i,hi⟩ := mem_iUnion.mp (hdom ▸ hx)
    rw [hf i x hi]
    exact EReal.coe_ne_bot _
  · have he : f x = ⊤ := by simpa [effectiveDomain] using hx
    simp [he]

/-- **Proposition 10.21**, closedness of the effective domain. -/
theorem IsPiecewiseLinearQuadratic.isClosed_effectiveDomain {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) : IsClosed (effectiveDomain f) := by
  obtain ⟨m,C,q,hC,hdom,hf⟩ := hf
  rw [hdom]
  exact isClosed_iUnion_of_finite fun i ↦ (hC i).isClosed

/-- **Proposition 10.21**, continuity relative to the domain. -/
theorem IsPiecewiseLinearQuadratic.continuousOn {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) : ContinuousOn f (effectiveDomain f) := by
  obtain ⟨m,C,q,hC,hdom,hf⟩ := hf
  rw [hdom]
  apply (locallyFinite_of_finite C).continuousOn_iUnion (fun i ↦ (hC i).isClosed)
  intro i
  exact (continuous_coe_real_ereal.comp (q i).continuous).continuousOn.congr fun x hx ↦ hf i x hx

/-- **Proposition 10.21**, global lower semicontinuity. -/
theorem IsPiecewiseLinearQuadratic.lowerSemicontinuous {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) : LowerSemicontinuous f := by
  obtain ⟨m,C,q,hC,hdom,hf⟩ := hf
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r = ⊤
  · simp [hr]
  · have he : f ⁻¹' Iic r = ⋃ i, C i ∩ {x | ((q i).eval x : EReal) ≤ r} := by
      ext x
      constructor
      · intro hx
        have hd : x ∈ effectiveDomain f := (show f x ≤ r from hx).trans_lt (lt_top_iff_ne_top.mpr hr)
        obtain ⟨i,hi⟩ := mem_iUnion.mp (hdom ▸ hd)
        exact mem_iUnion.mpr ⟨i,hi,by simpa [← hf i x hi] using hx⟩
      · intro hx
        obtain ⟨i,hi,hq⟩ := mem_iUnion.mp hx
        simpa [hf i x hi] using hq
    rw [he]
    exact isClosed_iUnion_of_finite fun i ↦ (hC i).isClosed.inter
      (isClosed_le (continuous_coe_real_ereal.comp (q i).continuous) continuous_const)

/-- A single quadratic expression on a polyhedron gives a PLQ function. -/
theorem isPiecewiseLinearQuadratic_piece {C : Set E} (hC : IsPolyhedral C)
    (q : QuadraticPiece E) :
    IsPiecewiseLinearQuadratic (fun x ↦ if x ∈ C then (q.eval x : EReal) else ⊤) := by
  classical
  refine ⟨1,fun _ ↦ C,fun _ ↦ q,fun _ ↦ hC,?_,?_⟩
  · ext x
    by_cases hx : x ∈ C <;> simp [effectiveDomain,hx]
  · intro i x hx
    simp [hx]

end RW
end
