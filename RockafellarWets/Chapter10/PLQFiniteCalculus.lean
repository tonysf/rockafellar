/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite sums and slices of PLQ functions
-/
import RockafellarWets.Chapter10.PLQCalculus
import RockafellarWets.Chapter10.PartialSubgradients

open Set Classical
open scoped InnerProductSpace Pointwise BigOperators

namespace RW
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- PLQ functions are closed under every finite sum, including the empty sum. -/
theorem IsPiecewiseLinearQuadratic.sum {ι : Type*} (s : Finset ι)
    (f : ι → E → EReal) (hf : ∀i ∈ s, IsPiecewiseLinearQuadratic (f i)) :
    IsPiecewiseLinearQuadratic (fun y ↦ ∑i ∈ s, f i y) := by
  induction s using Finset.cons_induction with
  | empty =>
    let q : QuadraticPiece E := ⟨0,by simp,0,0⟩
    simpa [q,QuadraticPiece.eval] using isPiecewiseLinearQuadratic_piece (E := E) IsPolyhedral.univ q
  | cons i s hi ih =>
    simpa only [Finset.sum_cons] using
      (hf i (by simp)).add (ih (fun j hj ↦ hf j (by simp [hj])))

/-- **Exercise 10.22(a)**: arbitrary nonempty finite sums, including the
exact subderivative and convex subgradient formulas. -/
theorem plq_finite_sum_calculus {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → E → EReal) (x : E)
    (hf : ∀i ∈ s, IsPiecewiseLinearQuadratic (f i))
    (hx : ∀i ∈ s, x ∈ effectiveDomain (f i)) :
    IsPiecewiseLinearQuadratic (fun y ↦ ∑ i ∈ s, f i y) ∧
    x ∈ effectiveDomain (fun y ↦ ∑ i ∈ s, f i y) ∧
    (∀w, subderivative (fun y ↦ ∑ i ∈ s, f i y) x w = ∑ i ∈ s, subderivative (f i) x w) ∧
    ((∀i ∈ s, Convex ℝ (epigraph (f i))) →
      Convex ℝ (epigraph (fun y ↦ ∑ i ∈ s, f i y)) ∧
      subdifferential (fun y ↦ ∑ i ∈ s, f i y) x = ∑ i ∈ s, subdifferential (f i) x) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    simpa using And.intro (hf i (by simp)) (hx i (by simp))
  | cons i s hi hs ih =>
    have hfi := hf i (by simp)
    have hxi := hx i (by simp)
    obtain ⟨hfs,hxs,hds,hcs⟩ := ih (fun j hj ↦ hf j (by simp [hj])) (fun j hj ↦ hx j (by simp [hj]))
    simp only [Finset.sum_cons]
    refine ⟨hfi.add hfs,?_,?_,?_⟩
    · change f i x+(∑j ∈ s,f j x) < ⊤
      have he : (∑j ∈ s,f j x) = ((∑j ∈ s,f j x).toReal:EReal) :=
        (EReal.coe_toReal (ne_of_lt hxs) (hfs.ne_bot x)).symm
      rw [← EReal.coe_toReal (ne_of_lt hxi) (hfi.ne_bot x),he,← EReal.coe_add]
      exact EReal.coe_lt_top _
    · intro w
      rw [hfi.subderivative_add hfs hxi hxs,hds]
    · intro hc
      obtain ⟨hcfs,hsg⟩ := hcs (fun j hj ↦ hc j (by simp [hj]))
      have hci := hc i (by simp)
      exact ⟨convex_epigraph_add_of_ne_bot hci hcfs hfi.ne_bot hfs.ne_bot,
        (hfi.subdifferential_add hfs hci hcfs hxi hxs).trans (by rw [hsg])⟩

private theorem partialEmbedding_affine (p : P) (x : E) :
    partialEmbeddingDerivative x+WithLp.toLp 2 ((0:E),p) = WithLp.toLp 2 (x,p) := by
  apply WithLp.ofLp_injective
  simp [partialEmbeddingDerivative]

/-- **Exercise 10.22(c)**, PLQ closure under freezing a parameter. -/
theorem IsPiecewiseLinearQuadratic.partialFunction {f : WithLp 2 (E × P) → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (p : P) : IsPiecewiseLinearQuadratic (RW.partialFunction f p) := by
  simpa only [partialEmbedding_affine,RW.partialFunction] using
    hf.compAffine partialEmbeddingDerivative (WithLp.toLp 2 ((0:E),p))

/-- **Exercise 10.22(c)**, the exact derivative of a slice. -/
theorem IsPiecewiseLinearQuadratic.subderivative_partialFunction {f : WithLp 2 (E × P) → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (p : P) {x : E}
    (hx : WithLp.toLp 2 (x,p) ∈ effectiveDomain f) (w : E) :
    subderivative (RW.partialFunction f p) x w =
      subderivative f (WithLp.toLp 2 (x,p)) (WithLp.toLp 2 (w,(0:P))) := by
  have hh := hf.subderivative_compAffine partialEmbeddingDerivative (WithLp.toLp 2 ((0:E),p))
    (x := x) (by simpa only [partialEmbedding_affine] using hx) w
  simpa only [partialEmbedding_affine,RW.partialFunction] using hh

/-- **Exercise 10.22(c)**, the exact convex subgradient of a slice. -/
theorem IsPiecewiseLinearQuadratic.subdifferential_partialFunction {f : WithLp 2 (E × P) → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hc : Convex ℝ (epigraph f)) (p : P) {x : E}
    (hx : WithLp.toLp 2 (x,p) ∈ effectiveDomain f) :
    subdifferential (RW.partialFunction f p) x =
      {v | ∃y, WithLp.toLp 2 (v,y) ∈ subdifferential f (WithLp.toLp 2 (x,p))} := by
  have hh := hf.subdifferential_compAffine hc partialEmbeddingDerivative (WithLp.toLp 2 ((0:E),p))
    (x := x) (by simpa only [partialEmbedding_affine] using hx)
  simp only [partialEmbedding_affine] at hh
  change subdifferential (fun y ↦ f (WithLp.toLp 2 (y,p))) x = _
  rw [hh]
  ext v
  constructor
  · rintro ⟨q,hq,he⟩
    rw [partialEmbeddingDerivative_adjoint] at he
    exact ⟨q.snd,he ▸ hq⟩
  · rintro ⟨y,hy⟩
    exact ⟨WithLp.toLp 2 (v,y),hy,by simp⟩

end RW
