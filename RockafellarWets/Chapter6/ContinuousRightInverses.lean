/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuous right inverses

A surjective bounded linear operator between real Hilbert spaces has a bounded
linear right inverse.  The construction uses the orthogonal projection onto
the closed kernel to turn the operator into a continuous linear equivalence.
It also gives a right inverse varying continuously with the operator near any
fixed surjective operator.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

open Filter Set Topology
open scoped InnerProduct

namespace RW

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A surjective continuous linear map between real Hilbert spaces admits a
continuous linear right inverse. -/
theorem exists_continuousLinearMap_rightInverse
    (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    ∃ R : F →L[ℝ] E, A.comp R = ContinuousLinearMap.id ℝ F := by
  have hkerclosed :
      IsClosed ((LinearMap.ker (A : E →ₗ[ℝ] F) : Submodule ℝ E) : Set E) :=
    ContinuousLinearMap.isClosed_ker A
  let N : Submodule ℝ E := LinearMap.ker (A : E →ₗ[ℝ] F)
  letI : CompleteSpace N := hkerclosed.completeSpace_coe
  let P : E →L[ℝ] N := N.orthogonalProjection
  have hPself : ∀ (z : E) (hz : z ∈ N), (P z : E) = z := by
    intro z hz
    have hself := Submodule.orthogonalProjection_mem_subspace_eq_self ⟨z, hz⟩
    change ((N.orthogonalProjection z : N) : E) = z
    exact congrArg (fun x : N ↦ (x : E)) hself
  have hPker : ∀ z : E, (P z : E) ∈ N := fun z ↦ (P z).2
  let Q : E →L[ℝ] F × N := A.prod P
  have hkerQ : LinearMap.ker (Q : E →ₗ[ℝ] F × N) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hw1 : A w = 0 := congrArg Prod.fst hw
    have hw2 : P w = 0 := congrArg Prod.snd hw
    have hwN : w ∈ N := hw1
    have hwP : (P w : E) = w := hPself w hwN
    rw [hw2] at hwP
    simpa using hwP.symm
  have hrangeQ : LinearMap.range (Q : E →ₗ[ℝ] F × N) = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨u, n⟩
    obtain ⟨w₀, hw₀⟩ := hA u
    refine ⟨w₀ - (P w₀ : E) + (n : E), ?_⟩
    have hfst : A (w₀ - (P w₀ : E) + (n : E)) = u := by
      have hA₁ : A (P w₀ : E) = 0 := hPker w₀
      have hA₂ : A (n : E) = 0 := n.2
      rw [map_add, map_sub, hA₁, hA₂, hw₀, sub_zero, add_zero]
    have hsnd : P (w₀ - (P w₀ : E) + (n : E)) = n := by
      have hP₁ : P (P w₀ : E) = P w₀ :=
        Subtype.ext (hPself (P w₀ : E) (hPker w₀))
      have hP₂ : P (n : E) = n := Subtype.ext (hPself (n : E) n.2)
      rw [map_add, map_sub, hP₁, hP₂, sub_self, zero_add]
    exact Prod.ext hfst hsnd
  let e : E ≃L[ℝ] F × N := ContinuousLinearEquiv.ofBijective Q hkerQ hrangeQ
  let R : F →L[ℝ] E :=
    e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ F N)
  refine ⟨R, ?_⟩
  ext y
  change A (e.symm (y, 0)) = y
  have heQ : (e : E →L[ℝ] F × N) = Q :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have he : Q (e.symm (y, 0)) = (y, 0) := by
    rw [← heQ]
    exact e.apply_symm_apply (y, 0)
  exact congrArg Prod.fst he

/-- A fixed choice of continuous linear right inverse for a surjective
continuous linear map between real Hilbert spaces. -/
def continuousLinearMapRightInverse (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    F →L[ℝ] E :=
  Classical.choose (exists_continuousLinearMap_rightInverse A hA)

/-- The chosen continuous linear right inverse is a right inverse as an
identity of continuous linear maps. -/
@[simp]
theorem comp_continuousLinearMapRightInverse (A : E →L[ℝ] F)
    (hA : Function.Surjective A) :
    A.comp (continuousLinearMapRightInverse A hA) = ContinuousLinearMap.id ℝ F :=
  Classical.choose_spec (exists_continuousLinearMap_rightInverse A hA)

/-- Pointwise form of the right-inverse identity. -/
@[simp]
theorem continuousLinearMapRightInverse_apply (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (y : F) :
    A (continuousLinearMapRightInverse A hA y) = y := by
  change (A.comp (continuousLinearMapRightInverse A hA)) y = y
  rw [comp_continuousLinearMapRightInverse]
  rfl

/-- A right inverse bounds the norm by the norm of the adjoint.  This is the
adjoint of `A ∘ R = id`, followed by the operator-norm estimate. -/
theorem norm_le_rightInverse_norm_mul_adjoint
    (A : E →L[ℝ] F) (R : F →L[ℝ] E)
    (hR : A.comp R = ContinuousLinearMap.id ℝ F) (y : F) :
    ‖y‖ ≤ ‖R‖ * ‖ContinuousLinearMap.adjoint A y‖ := by
  have hadj : (ContinuousLinearMap.adjoint R).comp
      (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ F := by
    rw [← ContinuousLinearMap.adjoint_comp, hR, ContinuousLinearMap.adjoint_id]
  calc
    ‖y‖ = ‖((ContinuousLinearMap.adjoint R).comp
        (ContinuousLinearMap.adjoint A)) y‖ := by rw [hadj]; rfl
    _ = ‖ContinuousLinearMap.adjoint R (ContinuousLinearMap.adjoint A y)‖ := rfl
    _ ≤ ‖ContinuousLinearMap.adjoint R‖ *
        ‖ContinuousLinearMap.adjoint A y‖ :=
      (ContinuousLinearMap.adjoint R).le_opNorm _
    _ = ‖R‖ * ‖ContinuousLinearMap.adjoint A y‖ := by
      rw [LinearIsometryEquiv.norm_map]

/-- The adjoint estimate specialized to the chosen right inverse. -/
theorem norm_le_continuousLinearMapRightInverse_norm_mul_adjoint
    (A : E →L[ℝ] F) (hA : Function.Surjective A) (y : F) :
    ‖y‖ ≤ ‖continuousLinearMapRightInverse A hA‖ *
      ‖ContinuousLinearMap.adjoint A y‖ :=
  norm_le_rightInverse_norm_mul_adjoint A (continuousLinearMapRightInverse A hA)
    (comp_continuousLinearMapRightInverse A hA) y

/-- Near a fixed surjective operator, right inverses can be chosen continuously.

Starting with a fixed right inverse `R₀`, the choice at `B` is
`R₀ ∘ (B ∘ R₀)⁻¹`.  Inversion is continuous at the identity, and
`B ∘ R₀` is invertible for all `B` in a neighborhood of `A`. -/
theorem exists_continuousAt_rightInverse_of_surjective
    (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    ∃ chooseR : (E →L[ℝ] F) → (F →L[ℝ] E),
      ContinuousAt chooseR A ∧
      A.comp (chooseR A) = ContinuousLinearMap.id ℝ F ∧
      ∀ᶠ B in 𝓝 A,
        B.comp (chooseR B) = ContinuousLinearMap.id ℝ F := by
  obtain ⟨R₀, hR₀⟩ := exists_continuousLinearMap_rightInverse A hA
  let chooseR : (E →L[ℝ] F) → (F →L[ℝ] E) :=
    fun B ↦ R₀.comp (B.comp R₀).inverse
  have hcomp : ContinuousAt (fun B : E →L[ℝ] F ↦ B.comp R₀) A :=
    continuousAt_id.clm_comp continuousAt_const
  have hinv : ContinuousAt (ContinuousLinearMap.inverse :
      (F →L[ℝ] F) → (F →L[ℝ] F)) (ContinuousLinearMap.id ℝ F) := by
    rw [← ContinuousLinearMap.ringInverse_eq_inverse]
    simpa only [ContinuousLinearMap.one_def] using
      (NormedRing.inverse_continuousAt (1 : (F →L[ℝ] F)ˣ))
  have hinvcomp : ContinuousAt
      (fun B : E →L[ℝ] F ↦ (B.comp R₀).inverse) A := by
    have hinvA : ContinuousAt (ContinuousLinearMap.inverse :
        (F →L[ℝ] F) → (F →L[ℝ] F)) (A.comp R₀) := by
      rw [hR₀]
      exact hinv
    exact ContinuousAt.comp' (f := fun B : E →L[ℝ] F ↦ B.comp R₀) hinvA hcomp
  have hchoose : ContinuousAt chooseR A := by
    exact continuousAt_const.clm_comp hinvcomp
  refine ⟨chooseR, hchoose, ?_, ?_⟩
  · simp only [chooseR, hR₀, ContinuousLinearMap.inverse_id,
      ContinuousLinearMap.comp_id]
  · have hcomp_tendsto : Tendsto (fun B : E →L[ℝ] F ↦ B.comp R₀)
        (𝓝 A) (𝓝 (ContinuousLinearMap.id ℝ F)) := by
      have hcomp' := hcomp
      change Tendsto (fun B : E →L[ℝ] F ↦ B.comp R₀)
        (𝓝 A) (𝓝 (A.comp R₀)) at hcomp'
      rw [hR₀] at hcomp'
      exact hcomp'
    have hinvertible_at_id : ∀ᶠ T : F →L[ℝ] F in 𝓝 (ContinuousLinearMap.id ℝ F),
        T.IsInvertible := by
      filter_upwards [(ContinuousLinearEquiv.refl ℝ F).nhds] with T hT
      rcases hT with ⟨e, rfl⟩
      exact ContinuousLinearMap.isInvertible_equiv
    have hinvertible : ∀ᶠ B : E →L[ℝ] F in 𝓝 A, (B.comp R₀).IsInvertible :=
      hcomp_tendsto.eventually hinvertible_at_id
    filter_upwards [hinvertible] with B hB
    change B.comp (R₀.comp (B.comp R₀).inverse) = ContinuousLinearMap.id ℝ F
    rw [← ContinuousLinearMap.comp_assoc, hB.self_comp_inverse]

end

end RW
