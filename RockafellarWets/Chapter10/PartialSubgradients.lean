/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Partial subgradients and subderivatives
-/

import RockafellarWets.Chapter10.BasicChainSubderivatives

open Set
open scoped InnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]

/-- Freeze the parameter in an extended-real function on a Euclidean product. -/
def partialFunction (f : WithLp 2 (E × P) → EReal) (p : P) (x : E) : EReal :=
  f (WithLp.toLp 2 (x,p))

noncomputable def partialEmbeddingDerivative : E →L[ℝ] WithLp 2 (E × P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E P)

theorem hasFDerivAt_partialEmbedding (x : E) (p : P) :
    HasFDerivAt (fun y : E ↦ WithLp.toLp 2 (y,p)) partialEmbeddingDerivative x := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.hasFDerivAt.comp _
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const p x))

theorem contDiff_partialEmbedding (p : P) : ContDiff ℝ 1 (fun y : E ↦ WithLp.toLp 2 (y,p)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.contDiff.comp (contDiff_id.prodMk contDiff_const)

@[simp] theorem partialEmbeddingDerivative_adjoint (q : WithLp 2 (E × P)) :
    (partialEmbeddingDerivative (E := E) (P := P)).adjoint q = q.fst := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪q,WithLp.toLp 2 (w,(0:P))⟫_ℝ = _
  simp [WithLp.prod_inner_apply]

private theorem partial_image_slice (C : Set (WithLp 2 (E × P))) :
    (partialEmbeddingDerivative (E := E) (P := P)).adjoint '' C =
      {v | ∃ y, WithLp.toLp 2 (v,y) ∈ C} := by
  ext v
  constructor
  · rintro ⟨q,hq,he⟩
    rw [partialEmbeddingDerivative_adjoint] at he
    exact ⟨q.snd,he ▸ hq⟩
  · rintro ⟨y,hy⟩
    exact ⟨WithLp.toLp 2 (v,y),hy,by simp⟩

variable {f : WithLp 2 (E × P) → EReal} {x : E} {p : P} {c : ℝ}

private theorem partial_horizon_qualification
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) :
    ∀ q ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)),
      (fderiv ℝ (fun z : E ↦ WithLp.toLp 2 (z,p)) x).adjoint q = 0 → q = 0 := by
  intro q hq he
  rw [(hasFDerivAt_partialEmbedding x p).fderiv,partialEmbeddingDerivative_adjoint] at he
  have hq' : WithLp.toLp 2 ((0:E),q.snd) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) := by
    simpa only [← he] using hq
  apply WithLp.ofLp_injective
  exact Prod.ext he (hQ q.snd hq')

/-- **Corollary 10.11**, the unconditional regular-subgradient inclusion. -/
theorem regularSubdifferential_partial_superset (hx : f (WithLp.toLp 2 (x,p)) = c) :
    {v | ∃ y, WithLp.toLp 2 (v,y) ∈ regularSubdifferential f (WithLp.toLp 2 (x,p))} ⊆
      regularSubdifferential (partialFunction f p) x := by
  rw [← partial_image_slice]
  exact adjoint_regularSubdifferential_subset_comp (hasFDerivAt_partialEmbedding x p) hx

/-- **Corollary 10.11**, the limiting partial-subgradient inclusion. -/
theorem subdifferential_partial_subset (hl : LowerSemicontinuous f)
    (hx : f (WithLp.toLp 2 (x,p)) = c)
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) :
    subdifferential (partialFunction f p) x ⊆
      {v | ∃ y, WithLp.toLp 2 (v,y) ∈ subdifferential f (WithLp.toLp 2 (x,p))} := by
  have hh := subdifferential_comp_subset (G := fun z : E ↦ WithLp.toLp 2 (z,p)) (g := f) (x := x) (contDiff_partialEmbedding p) hl hx (partial_horizon_qualification (f := f) (x := x) (p := p) hQ)
  rwa [(hasFDerivAt_partialEmbedding x p).fderiv,partial_image_slice] at hh

/-- **Corollary 10.11**, the horizon partial-subgradient inclusion. -/
theorem horizonSubdifferential_partial_subset (hl : LowerSemicontinuous f)
    (hx : f (WithLp.toLp 2 (x,p)) = c)
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) :
    horizonSubdifferential (partialFunction f p) x ⊆
      {v | ∃ y, WithLp.toLp 2 (v,y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p))} := by
  have hh := horizonSubdifferential_comp_subset (G := fun z : E ↦ WithLp.toLp 2 (z,p)) (g := f) (x := x) (contDiff_partialEmbedding p) hl hx (partial_horizon_qualification (f := f) (x := x) (p := p) hQ)
  rwa [(hasFDerivAt_partialEmbedding x p).fderiv,partial_image_slice] at hh

/-- **Corollary 10.11**, preservation of regularity. -/
theorem IsSubdifferentiallyRegularAt.partial (hr : IsSubdifferentiallyRegularAt f (WithLp.toLp 2 (x,p)))
    (hl : LowerSemicontinuous f)
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) :
    IsSubdifferentiallyRegularAt (partialFunction f p) x :=
  hr.comp_of_horizon_qualification (G := fun z : E ↦ WithLp.toLp 2 (z,p)) (x := x) (contDiff_partialEmbedding p) hl (partial_horizon_qualification (f := f) (x := x) (p := p) hQ)

/-- **Corollary 10.11**, exact subgradients for a regular function. -/
theorem subdifferential_partial_eq_of_regular (hr : IsSubdifferentiallyRegularAt f (WithLp.toLp 2 (x,p)))
    (hl : LowerSemicontinuous f)
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) :
    subdifferential (partialFunction f p) x =
      {v | ∃ y, WithLp.toLp 2 (v,y) ∈ subdifferential f (WithLp.toLp 2 (x,p))} := by
  have hh := subdifferential_comp_eq_of_regular (G := fun z : E ↦ WithLp.toLp 2 (z,p)) (g := f) (x := x) (contDiff_partialEmbedding p) hl hr (partial_horizon_qualification (f := f) (x := x) (p := p) hQ)
  rwa [(hasFDerivAt_partialEmbedding x p).fderiv,partial_image_slice] at hh

/-- **Corollary 10.11**, exact horizon subgradients for a regular function. -/
theorem horizonSubdifferential_partial_eq_of_regular (hr : IsSubdifferentiallyRegularAt f (WithLp.toLp 2 (x,p)))
    (hl : LowerSemicontinuous f)
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) :
    horizonSubdifferential (partialFunction f p) x =
      {v | ∃ y, WithLp.toLp 2 (v,y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p))} := by
  have hh := horizonSubdifferential_comp_eq_of_regular (G := fun z : E ↦ WithLp.toLp 2 (z,p)) (g := f) (x := x) (contDiff_partialEmbedding p) hl hr (partial_horizon_qualification (f := f) (x := x) (p := p) hQ)
  rwa [(hasFDerivAt_partialEmbedding x p).fderiv,partial_image_slice] at hh

/-- **Corollary 10.11**, the unconditional partial-subderivative inequality. -/
theorem subderivative_partial_ge (hx : f (WithLp.toLp 2 (x,p)) = c) (w : E) :
    subderivative f (WithLp.toLp 2 (x,p)) (WithLp.toLp 2 (w,(0:P))) ≤
      subderivative (partialFunction f p) x w :=
  subderivative_comp_ge (hasFDerivAt_partialEmbedding x p) hx w

/-- **Corollary 10.11**, the regular partial-subderivative inequality. -/
theorem regularSubderivative_partial_le (hl : LowerSemicontinuous f)
    (hx : f (WithLp.toLp 2 (x,p)) = c)
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) (w : E) :
    regularSubderivative (partialFunction f p) x w ≤
      regularSubderivative f (WithLp.toLp 2 (x,p)) (WithLp.toLp 2 (w,(0:P))) := by
  have hh := regularSubderivative_comp_le (G := fun z : E ↦ WithLp.toLp 2 (z,p)) (g := f) (x := x) (contDiff_partialEmbedding p) hl hx (partial_horizon_qualification (f := f) (x := x) (p := p) hQ) w
  rwa [(hasFDerivAt_partialEmbedding x p).fderiv] at hh

/-- **Corollary 10.11**, exact partial subderivatives for a regular function. -/
theorem subderivative_partial_eq_of_regular (hr : IsSubdifferentiallyRegularAt f (WithLp.toLp 2 (x,p)))
    (hl : LowerSemicontinuous f)
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) (w : E) :
    subderivative (partialFunction f p) x w =
      subderivative f (WithLp.toLp 2 (x,p)) (WithLp.toLp 2 (w,(0:P))) := by
  have hh := subderivative_comp_eq_of_regular (G := fun z : E ↦ WithLp.toLp 2 (z,p)) (g := f) (x := x) (contDiff_partialEmbedding p) hl hr (partial_horizon_qualification (f := f) (x := x) (p := p) hQ) w
  rwa [(hasFDerivAt_partialEmbedding x p).fderiv] at hh

end RW
