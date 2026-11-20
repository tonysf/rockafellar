/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Permuting the graph of an implicit mapping
-/

import RockafellarWets.Chapter9.ImplicitMappingDefinitions
import RockafellarWets.Chapter9.MordukhovichCriterion
import RockafellarWets.Chapter9.StrictGraphicalDerivatives
import RockafellarWets.Chapter6.LimitingNormalChangeOfCoordinates

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal

namespace RW

variable {E P F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [FiniteDimensional ℝ F]

/-- The graph-coordinate permutation `(u,p,x) ↦ (x,p,u)` is an isometry. -/
noncomputable def implicitGraphPermutation :
    WithLp 2 (WithLp 2 (F × P) × E) ≃ₗᵢ[ℝ] WithLp 2 (WithLp 2 (E × P) × F) :=
  (LinearIsometryEquiv.withLpProdAssoc 2 ℝ F P E).trans
    ((LinearIsometryEquiv.withLpProdComm 2 ℝ F (WithLp 2 (P × E))).trans
      (LinearIsometryEquiv.withLpProdCongr 2
        (LinearIsometryEquiv.withLpProdComm 2 ℝ P E) (LinearIsometryEquiv.refl ℝ F)))

@[simp] theorem implicitGraphPermutation_apply (q : WithLp 2 (WithLp 2 (F × P) × E)) :
    implicitGraphPermutation q = WithLp.toLp 2 (WithLp.toLp 2 (q.snd,q.fst.snd),q.fst.fst) := rfl

theorem normalCone_preimage_linearIsometryEquiv {A B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    (L : A ≃ₗᵢ[ℝ] B) (C : Set B) (a : A) :
    normalCone (L ⁻¹' C) a = L ⁻¹' normalCone C (L a) := by
  have h := normalCone_preimage_of_surjective (G := (L : A →L[ℝ] B)) (x := a)
    L.toContinuousLinearMap.contDiff.contDiffAt
    (by simpa only [ContinuousLinearMap.fderiv] using L.surjective) C
  rw [ContinuousLinearMap.fderiv,LinearIsometryEquiv.adjoint_eq_symm] at h
  change normalCone (L ⁻¹' C) a = L.symm '' normalCone C (L a) at h
  rw [h]
  ext v
  exact ⟨fun ⟨z,hz,he⟩ ↦ by simpa [← he] using hz,
    fun hv ↦ ⟨L v,hv,L.symm_apply_apply v⟩⟩

variable {S : WithLp 2 (E × P) → Set F} {x : E} {p : P}

/-- The coderivative rule for the auxiliary perturbed solution mapping. -/
theorem mem_coderivative_implicitPerturbation_iff {v : E} {q : WithLp 2 (F × P)} :
    q ∈ coderivative (implicitPerturbationMapping S) (WithLp.toLp 2 (0,p)) x v ↔
      WithLp.toLp 2 (-v,q.snd) ∈ coderivative S (WithLp.toLp 2 (x,p)) 0 (-q.fst) := by
  let L : WithLp 2 (WithLp 2 (F × P) × E) ≃ₗᵢ[ℝ] WithLp 2 (WithLp 2 (E × P) × F) := implicitGraphPermutation
  have heq : euclideanSvGraph (implicitPerturbationMapping S) = L ⁻¹' euclideanSvGraph S := rfl
  change WithLp.toLp 2 (q,-v) ∈ normalCone (euclideanSvGraph (implicitPerturbationMapping S)) _ ↔ _
  rw [heq,normalCone_preimage_linearIsometryEquiv]
  change WithLp.toLp 2 (WithLp.toLp 2 (-v,q.snd),q.fst) ∈
    normalCone (euclideanSvGraph S) (WithLp.toLp 2 (WithLp.toLp 2 (x,p),0)) ↔ _
  simp only [coderivative,svOfEuclideanNormals,mem_setOf_eq,neg_neg]

/-- Permuting the graph also permutes the ordinary graphical derivatives. -/
theorem mem_graphicalDerivative_implicitPerturbation_iff {w : E} {z : F} {q : P} :
    w ∈ graphicalDerivative (implicitPerturbationMapping S) (WithLp.toLp 2 (0,p)) x
      (WithLp.toLp 2 (z,q)) ↔
      z ∈ graphicalDerivative S (WithLp.toLp 2 (x,p)) 0 (WithLp.toLp 2 (w,q)) := by
  let L := (implicitGraphPermutation (E := E) (P := P) (F := F)).toContinuousLinearEquiv
  have heq : euclideanSvGraph (implicitPerturbationMapping S) = L ⁻¹' euclideanSvGraph S := rfl
  change WithLp.toLp 2 (WithLp.toLp 2 (z,q),w) ∈ tangentCone (euclideanSvGraph (implicitPerturbationMapping S)) _ ↔ _
  rw [heq,tangentCone_preimage_continuousLinearEquiv]
  rfl

/-- Proto-differentiability is invariant under the implicit graph permutation. -/
theorem isProtoDifferentiableAt_implicitPerturbation_iff (hx : 0 ∈ S (WithLp.toLp 2 (x,p))) :
    IsProtoDifferentiableAt (implicitPerturbationMapping S) (WithLp.toLp 2 (0,p)) x ↔
      IsProtoDifferentiableAt S (WithLp.toLp 2 (x,p)) 0 := by
  rw [isProtoDifferentiableAt_iff_geometricallyDerivable (show
    x ∈ implicitPerturbationMapping S (WithLp.toLp 2 (0,p)) from hx),
    isProtoDifferentiableAt_iff_geometricallyDerivable hx]
  let L := (implicitGraphPermutation (E := E) (P := P) (F := F)).toContinuousLinearEquiv
  have heq : euclideanSvGraph (implicitPerturbationMapping S) = L ⁻¹' euclideanSvGraph S := rfl
  rw [heq,isGeometricallyDerivable_preimage_continuousLinearEquiv]
  rfl

/-- Zero residual embeds the parameter space isometrically into the auxiliary
input space. -/
def implicitParameterEmbedding : P →L[ℝ] WithLp 2 (F × P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F P).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ F P)

@[simp] theorem implicitParameterEmbedding_apply (q : P) :
    implicitParameterEmbedding (F := F) q = WithLp.toLp 2 (0,q) := rfl

theorem implicitParameterEmbedding_dist (q r : P) :
    dist (implicitParameterEmbedding (F := F) q) (implicitParameterEmbedding (F := F) r) = dist q r := by
  rw [dist_eq_norm,← map_sub,implicitParameterEmbedding_apply,WithLp.norm_toLp_snd,dist_eq_norm]

/-- Outer semicontinuity of the original mapping supplies both closed graphs
needed in Theorem 9.56. -/
theorem SvOsc.implicit_graphs_closed (hS : SvOsc S) :
    IsClosed (svGraph (implicitPerturbationMapping S)) ∧
      IsClosed (svGraph (implicitSolutionMapping S)) := by
  have hc := isClosed_svGraph_iff_svOsc.mpr hS
  constructor
  · have heq : svGraph (implicitPerturbationMapping S) =
        (fun q : WithLp 2 (F × P) × E ↦ (WithLp.toLp 2 (q.2,q.1.snd),q.1.fst)) ⁻¹' svGraph S := rfl
    rw [heq]
    apply hc.preimage
    fun_prop
  · have heq : svGraph (implicitSolutionMapping S) =
        (fun q : P × E ↦ (WithLp.toLp 2 (q.2,q.1),(0:F))) ⁻¹' svGraph S := rfl
    rw [heq]
    apply hc.preimage
    fun_prop

/-- The normal qualification in 9.56(a) is the Mordukhovich criterion for
the auxiliary perturbed solution mapping. -/
theorem hasAubinProperty_implicitPerturbation_of_coderivative (hS : SvOsc S)
    (hx : 0 ∈ S (WithLp.toLp 2 (x,p)))
    (hQ : ∀ (y : F) (r : P), WithLp.toLp 2 (0,r) ∈ coderivative S (WithLp.toLp 2 (x,p)) 0 y → y = 0 ∧ r = 0) :
    HasAubinPropertyAt (implicitPerturbationMapping S) (WithLp.toLp 2 (0,p)) x := by
  apply (hasAubinPropertyAt_iff_coderivative_zero (show
    x ∈ implicitPerturbationMapping S (WithLp.toLp 2 (0,p)) from hx)
      (RW.IsClosed.isLocallyClosedAt hS.implicit_graphs_closed.1 _)).mpr
  apply Subset.antisymm
  · intro q hq
    have hh := mem_coderivative_implicitPerturbation_iff.mp hq
    simp only [neg_zero] at hh
    obtain ⟨hy,hr⟩ := hQ (-q.fst) q.snd hh
    have hfst : q.fst = 0 := neg_eq_zero.mp hy
    apply mem_singleton_iff.mpr
    calc q = WithLp.toLp 2 (q.fst,q.snd) := rfl
         _ = 0 := by rw [hfst,hr]; rfl
  · apply singleton_subset_iff.mpr
    change WithLp.toLp 2 ((0 : WithLp 2 (F × P)),-(0:E)) ∈ normalCone _ _
    simpa only [neg_zero] using (isCone_normalCone
      (show WithLp.toLp 2 (WithLp.toLp 2 (0,p),x) ∈ euclideanSvGraph (implicitPerturbationMapping S) from hx)).1

end RW
