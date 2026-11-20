/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Subgradients under changes of coordinates
-/

import RockafellarWets.Chapter10.BasicChainRule

open Set
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {G : E → F} {g : F → EReal} {x : E} {c : ℝ}

theorem adjoint_injective_of_surjective {A : E →L[ℝ] F} (h : Function.Surjective A) :
    Function.Injective A.adjoint := by
  intro y z he
  apply ext_inner_right ℝ
  intro v
  obtain ⟨w,rfl⟩ := h v
  rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.adjoint_inner_left,he]

theorem mem_adjoint_epigraphChainDerivative_image (A : E →L[ℝ] F)
    (C : Set (WithLp 2 (F × ℝ))) (v : E) (b : ℝ) :
    WithLp.toLp 2 (v,b) ∈ (epigraphChainDerivative A).adjoint '' C ↔
      v ∈ A.adjoint '' {y | WithLp.toLp 2 (y,b) ∈ C} := by
  constructor
  · rintro ⟨q,hq,he⟩
    rw [epigraphChainDerivative_adjoint] at he
    have hs : q.snd = b := congrArg WithLp.snd he
    refine ⟨q.fst,?_,congrArg WithLp.fst he⟩
    simpa only [← hs] using hq
  · rintro ⟨y,hy,rfl⟩
    exact ⟨WithLp.toLp 2 (y,b),hy,epigraphChainDerivative_adjoint _ _⟩

/-- **Exercise 10.7**, exact regular subgradients under a full-rank map. -/
theorem regularSubdifferential_comp_eq_of_surjective (hG : ContDiff ℝ 1 G)
    (hx : g (G x) = c) (hs : Function.Surjective (fderiv ℝ G x)) :
    regularSubdifferential (g ∘ G) x = (fderiv ℝ G x).adjoint '' regularSubdifferential g (G x) := by
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hde := (hasFDerivAt_epigraphChainMap hd c).fderiv
  have ht := (contDiff_epigraphChainMap hG).contDiffAt (x := WithLp.toLp 2 (x,c)) |>.hasStrictFDerivAt (by norm_num : (1:WithTop ℕ∞) ≠ 0)
  rw [hde] at ht
  ext v
  rw [mem_regularSubdifferential_iff_epigraph_normal (f := g ∘ G) (x := x) hx,
    euclideanEpigraph_comp,regularNormalCone_preimage_of_surjective ht (epigraphChainDerivative_surjective hs),
    mem_adjoint_epigraphChainDerivative_image]
  simp only [mem_image,mem_setOf_eq,epigraphChainMap,WithLp.toLp_fst,WithLp.toLp_snd,
    ← mem_regularSubdifferential_iff_epigraph_normal hx]

/-- **Exercise 10.7**, exact limiting subgradients under a full-rank map. -/
theorem subdifferential_comp_eq_of_surjective (hG : ContDiff ℝ 1 G)
    (hx : g (G x) = c) (hs : Function.Surjective (fderiv ℝ G x)) :
    subdifferential (g ∘ G) x = (fderiv ℝ G x).adjoint '' subdifferential g (G x) := by
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hde := (hasFDerivAt_epigraphChainMap hd c).fderiv
  have hsur : Function.Surjective (fderiv ℝ (epigraphChainMap G) (WithLp.toLp 2 (x,c))) := by
    rw [hde]
    exact epigraphChainDerivative_surjective hs
  ext v
  rw [mem_subdifferential_iff_epigraph_normal (f := g ∘ G) (x := x) hx,
    euclideanEpigraph_comp,normalCone_preimage_of_surjective (contDiff_epigraphChainMap hG).contDiffAt hsur,
    hde,mem_adjoint_epigraphChainDerivative_image]
  simp only [mem_image,mem_setOf_eq,epigraphChainMap,WithLp.toLp_fst,WithLp.toLp_snd,
    ← mem_subdifferential_iff_epigraph_normal hx]

/-- **Exercise 10.7**, exact horizon subgradients under a full-rank map. -/
theorem horizonSubdifferential_comp_eq_of_surjective (hG : ContDiff ℝ 1 G)
    (hl : LowerSemicontinuous g) (hx : g (G x) = c) (hs : Function.Surjective (fderiv ℝ G x)) :
    horizonSubdifferential (g ∘ G) x = (fderiv ℝ G x).adjoint '' horizonSubdifferential g (G x) := by
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hde := (hasFDerivAt_epigraphChainMap hd c).fderiv
  have hsur : Function.Surjective (fderiv ℝ (epigraphChainMap G) (WithLp.toLp 2 (x,c))) := by
    rw [hde]
    exact epigraphChainDerivative_surjective hs
  ext v
  rw [mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
      (locallyLscAt_of_lowerSemicontinuous_finite (hl.comp hG.continuous) (show (g ∘ G) x = c from hx)) hx,
    euclideanEpigraph_comp,normalCone_preimage_of_surjective (contDiff_epigraphChainMap hG).contDiffAt hsur,
    hde,mem_adjoint_epigraphChainDerivative_image]
  simp only [mem_image,mem_setOf_eq,epigraphChainMap,WithLp.toLp_fst,WithLp.toLp_snd,
    ← mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
      (locallyLscAt_of_lowerSemicontinuous_finite hl hx) hx]

end RW
