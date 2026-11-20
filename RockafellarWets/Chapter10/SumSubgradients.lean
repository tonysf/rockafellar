/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Subgradients of sums
-/

import RockafellarWets.Chapter10.SeparableRegularity
import RockafellarWets.Chapter10.BasicChainSubderivatives

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f g : E → EReal} {x : E} {c d : ℝ}

noncomputable def diagonalEmbedding : E →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E))

@[simp] theorem diagonalEmbedding_apply (w : E) : diagonalEmbedding w = WithLp.toLp 2 (w,w) := rfl

@[simp] theorem diagonalEmbedding_adjoint (q : WithLp 2 (E × E)) :
    (diagonalEmbedding (E := E)).adjoint q = q.fst+q.snd := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left,diagonalEmbedding_apply,WithLp.prod_inner_apply,inner_add_left]
  rfl

private theorem diagonal_image_product (A B : Set E) :
    (diagonalEmbedding (E := E)).adjoint '' {q | q.fst ∈ A ∧ q.snd ∈ B} = A+B := by
  ext v
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨q.fst,hq.1,q.snd,hq.2,by simp⟩
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact ⟨WithLp.toLp 2 (a,b),⟨ha,hb⟩,by simp⟩

/-- **Corollary 10.9**, the unconditional regular-subgradient sum inclusion. -/
theorem regularSubdifferential_add_superset (hx : f x = c) (hy : g x = d) :
    regularSubdifferential f x+regularSubdifferential g x ⊆ regularSubdifferential (f+g) x := by
  rw [← diagonal_image_product]
  have he : {q : WithLp 2 (E × E) | q.fst ∈ regularSubdifferential f x ∧ q.snd ∈ regularSubdifferential g x} =
      regularSubdifferential (separableSum f g) (WithLp.toLp 2 (x,x)) := by
    ext q
    exact (mem_regularSubdifferential_separableSum_iff hx hy q).symm
  rw [he]
  exact adjoint_regularSubdifferential_subset_comp (diagonalEmbedding (E := E)).hasFDerivAt
    (show separableSum f g (diagonalEmbedding x) = ((c+d:ℝ):EReal) by simp [separableSum,hx,hy])

private theorem sum_horizon_qualification (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hx : f x = c) (hy : g x = d)
    (hQ : ∀ u ∈ horizonSubdifferential f x, ∀ v ∈ horizonSubdifferential g x, u+v = 0 → u = 0 ∧ v = 0) :
    ∀ q ∈ horizonSubdifferential (separableSum f g) (diagonalEmbedding x),
      (fderiv ℝ diagonalEmbedding x).adjoint q = 0 → q = 0 := by
  intro q hq he
  have hm := horizonSubdifferential_separableSum_subset (hf x) (hg x) hx hy hq
  rw [(diagonalEmbedding (E := E)).fderiv,diagonalEmbedding_adjoint] at he
  have hh := hQ q.fst hm.1 q.snd hm.2 he
  apply WithLp.ofLp_injective
  exact Prod.ext hh.1 hh.2

/-- **Corollary 10.9**, the limiting-subgradient sum inclusion. -/
theorem subdifferential_add_subset (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hpf : IsProper f) (hpg : IsProper g) (hx : f x = c) (hy : g x = d)
    (hQ : ∀ u ∈ horizonSubdifferential f x, ∀ v ∈ horizonSubdifferential g x, u+v = 0 → u = 0 ∧ v = 0) :
    subdifferential (f+g) x ⊆ subdifferential f x+subdifferential g x := by
  have hxy : separableSum f g (diagonalEmbedding x) = ((c+d:ℝ):EReal) := by simp [separableSum,hx,hy]
  have hh := subdifferential_comp_subset (G := diagonalEmbedding) (x := x) (diagonalEmbedding (E := E)).contDiff
    (lowerSemicontinuous_separableSum hf hg hpf hpg) hxy (sum_horizon_qualification hf hg hx hy hQ)
  rw [(diagonalEmbedding (E := E)).fderiv] at hh
  have he : subdifferential (separableSum f g) (diagonalEmbedding x) =
      {q | q.fst ∈ subdifferential f x ∧ q.snd ∈ subdifferential g x} := by
    ext q
    exact mem_subdifferential_separableSum_iff (hf x) (hg x) hx hy q
  rwa [he,diagonal_image_product] at hh

/-- **Corollary 10.9**, the horizon-subgradient sum inclusion. -/
theorem horizonSubdifferential_add_subset (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hpf : IsProper f) (hpg : IsProper g) (hx : f x = c) (hy : g x = d)
    (hQ : ∀ u ∈ horizonSubdifferential f x, ∀ v ∈ horizonSubdifferential g x, u+v = 0 → u = 0 ∧ v = 0) :
    horizonSubdifferential (f+g) x ⊆ horizonSubdifferential f x+horizonSubdifferential g x := by
  have hxy : separableSum f g (diagonalEmbedding x) = ((c+d:ℝ):EReal) := by simp [separableSum,hx,hy]
  have hh := horizonSubdifferential_comp_subset (G := diagonalEmbedding) (x := x) (diagonalEmbedding (E := E)).contDiff
    (lowerSemicontinuous_separableSum hf hg hpf hpg) hxy (sum_horizon_qualification hf hg hx hy hQ)
  rw [(diagonalEmbedding (E := E)).fderiv] at hh
  apply hh.trans
  rw [← diagonal_image_product]
  exact image_mono (horizonSubdifferential_separableSum_subset (hf x) (hg x) hx hy)

/-- **Corollary 10.9**, the unconditional lower-subderivative inequality. -/
theorem subderivative_add_ge (hx : f x = c) (hy : g x = d) (w : E) :
    subderivative f x w+subderivative g x w ≤ subderivative (f+g) x w := by
  exact (subderivative_separableSum_ge hx hy (diagonalEmbedding w)).trans
    (subderivative_comp_ge (diagonalEmbedding (E := E)).hasFDerivAt
      (show separableSum f g (diagonalEmbedding x) = ((c+d:ℝ):EReal) by simp [separableSum,hx,hy]) w)

end RW
