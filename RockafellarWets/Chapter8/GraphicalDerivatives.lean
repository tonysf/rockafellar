/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Graphical derivatives and coderivatives
-/

import RockafellarWets.Chapter6.ProductCones
import RockafellarWets.Chapter6.RegularTangents
import RockafellarWets.Chapter5.ConvexSemicontinuity

open Set
open scoped InnerProductSpace

namespace RW

variable {E F : Type*}

/-- The graph of a set-valued mapping in the Euclidean product. -/
def euclideanSvGraph (S : E → Set F) : Set (WithLp 2 (E × F)) :=
  {p | p.snd ∈ S p.fst}

/-- Recover a mapping from its graph in the Euclidean product. -/
def svOfEuclideanGraph (K : Set (WithLp 2 (E × F))) : E → Set F :=
  fun w ↦ {z | WithLp.toLp 2 (w,z) ∈ K}

@[simp] theorem euclideanSvGraph_svOfEuclideanGraph (K : Set (WithLp 2 (E × F))) :
    euclideanSvGraph (svOfEuclideanGraph K) = K := rfl

theorem svOfEuclideanGraph_injective : Function.Injective (svOfEuclideanGraph (E := E) (F := F)) :=
  fun _ _ h ↦ congrArg euclideanSvGraph h

section Tangents

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Definition 8.33**, the graphical derivative. -/
def graphicalDerivative (S : E → Set F) (x : E) (u : F) : E → Set F :=
  svOfEuclideanGraph (tangentCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)))

/-- **Definition 8.33**, the regular graphical derivative. -/
def regularGraphicalDerivative (S : E → Set F) (x : E) (u : F) : E → Set F :=
  svOfEuclideanGraph (regularTangentCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)))

/-- Represent a set of normals as a mapping with transposed variables and
negated output multiplier, as in Definition 8.33. -/
def svOfEuclideanNormals (K : Set (WithLp 2 (E × F))) : F → Set E :=
  fun y ↦ {v | WithLp.toLp 2 (v,-y) ∈ K}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem svOfEuclideanNormals_injective : Function.Injective (svOfEuclideanNormals (E := E) (F := F)) := by
  intro K L h
  ext p
  have hh := congrArg (fun S : F → Set E ↦ p.fst ∈ S (-p.snd)) h
  simpa only [svOfEuclideanNormals, mem_setOf_eq, neg_neg] using Iff.of_eq hh

/-- The map underlying a Euclidean derivative graph in ordinary graph coordinates. -/
def euclideanGraphCoordinates : E × F →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap

/-- The sign change and transposition taking ordinary coderivative graph
coordinates to Euclidean normal vectors. -/
def euclideanNormalCoordinates : F × E →L[ℝ] WithLp 2 (E × F) :=
  euclideanGraphCoordinates.comp ((ContinuousLinearMap.snd ℝ F E).prod (-(ContinuousLinearMap.fst ℝ F E)))

theorem svGraph_svOfEuclideanGraph (K : Set (WithLp 2 (E × F))) :
    svGraph (svOfEuclideanGraph K) = euclideanGraphCoordinates ⁻¹' K := rfl

theorem svGraph_svOfEuclideanNormals (K : Set (WithLp 2 (E × F))) :
    svGraph (svOfEuclideanNormals K) = euclideanNormalCoordinates ⁻¹' K := rfl

end Tangents

section Normals

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Definition 8.33**, the limiting coderivative. -/
def coderivative (S : E → Set F) (x : E) (u : F) : F → Set E :=
  svOfEuclideanNormals (normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)))

/-- **Definition 8.33**, the regular coderivative. -/
def regularCoderivative (S : E → Set F) (x : E) (u : F) : F → Set E :=
  svOfEuclideanNormals (regularNormalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)))

/-- **Definition 8.38**, graphical regularity of a mapping. -/
def IsGraphicallyRegularAt (S : E → Set F) (x : E) (u : F) : Prop :=
  IsClarkeRegularAt (euclideanSvGraph S) (WithLp.toLp 2 (x,u))

/-- Formula 8(27), the upper adjoint of a mapping. -/
def svUpperAdjoint (H : E → Set F) : F → Set E :=
  fun y ↦ {v | ∀ w z, z ∈ H w → ⟪v,w⟫_ℝ ≤ ⟪y,z⟫_ℝ}

/-- Formula 8(28), the lower adjoint. -/
def svLowerAdjoint (H : E → Set F) : F → Set E :=
  fun y ↦ {v | ∀ w z, z ∈ H w → ⟪y,z⟫_ℝ ≤ ⟪v,w⟫_ℝ}

end Normals
end RW
