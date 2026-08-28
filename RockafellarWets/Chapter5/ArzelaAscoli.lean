/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Arzelà--Ascoli for Set-Valued Mappings

Theorem 5.47, assembled exactly as the book says: the compactness property of
5.36, then 5.44, then 5.43.

The one point needing care is the passage from the *absolute* graphical
convergence that 5.36 produces to the convergence *relative to* `X` that 5.44
consumes.  The two are different notions, and neither implies the other, so
5.36 is applied not to `Sν` but to the restrictions `Sν|X` of 5.33: at a point
of `X` the graphical limits of the restrictions are exactly the relative
graphical limits, and that identification needs nothing of `X` -- the
closedness in the paragraph after 5.33 is only needed off `X`, which the
conclusion never looks at.  So `X` here is an arbitrary set, as in the book.

Escape to the horizon is not a case to be excluded: a sequence of graphs
whose outer limit is empty converges, as a whole sequence, to the empty-valued
mapping, so 5.36 yields a graphically convergent subsequence unconditionally.
The limit mapping produced by 5.47 may therefore be empty-valued, which is
correct -- `Sν(x) = {ν}` is asymptotically equicontinuous relative to `IR` and
has no other limit.
-/

import RockafellarWets.Chapter5.GraphicalCompactness
import RockafellarWets.Chapter5.GraphicalFromUniform

open Filter Metric Set Topology

namespace RW

section ArzelaAscoli

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {X : Set E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- A subsequence of the restrictions converging graphically converges
graphically *relative to* `X`, the two limits agreeing at every point of
`X`. -/
theorem graphicalConvergesOn_of_graphicalConverges_svRestrict {φ : ℕ → ℕ}
    {S : E → Set F}
    (h : GraphicalConverges (fun k ↦ svRestrict (Sseq (φ k)) X) S) :
    GraphicalConvergesOn (fun k ↦ Sseq (φ k)) S X := by
  obtain ⟨hout, hin⟩ := graphicalConverges_iff.1 h
  intro x hx
  constructor
  · rw [← graphicalOuterLimit_svRestrict (fun k ↦ Sseq (φ k)) hx]
    exact hout x
  · rw [← graphicalInnerLimit_svRestrict (fun k ↦ Sseq (φ k)) hx]
    exact hin x

/-- **Theorem 5.47 (Arzelà--Ascoli, set-valued version).**  An asymptotically
equicontinuous sequence relative to `X` admits a subsequence converging
uniformly on all compact subsets of `X` to a mapping continuous relative
to `X`. -/
theorem exists_subsequence_svConvergesUniformlyOn_of_svAsymptoticallyEquicontinuous
    (he : ∀ x ∈ X, SvAsymptoticallyEquicontinuousWithinAt Sseq X x) :
    ∃ (φ : ℕ → ℕ) (S : E → Set F), StrictMono φ ∧
      (∀ B ⊆ X, IsCompact B →
        SvConvergesUniformlyOn (fun k ↦ Sseq (φ k)) S B) ∧
      SvContinuousOn S X := by
  obtain ⟨φ, S, hφ, hconv⟩ :=
    exists_graphicalConverges_subsequence fun n ↦ svRestrict (Sseq n) X
  have hrel : GraphicalConvergesOn (fun k ↦ Sseq (φ k)) S X :=
    graphicalConvergesOn_of_graphicalConverges_svRestrict hconv
  have hcc : SvConvergesContinuouslyOn (fun k ↦ Sseq (φ k)) S X := fun x hx ↦
    svConvergesContinuouslyWithinAt_of_graphicalConvergesWithinAt hx (hrel x hx)
      ((he x hx).comp_strictMono hφ)
  obtain ⟨huni, hcont⟩ := svConvergesContinuouslyOn_iff.1 hcc
  exact ⟨φ, S, hφ, huni, hcont⟩

end ArzelaAscoli

end RW
