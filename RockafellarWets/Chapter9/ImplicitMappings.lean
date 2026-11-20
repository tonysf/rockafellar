/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Generalized implicit mappings

Theorem 9.56(a–c), by the graph permutation for the auxiliary mapping
T(u,p) = {x | u ∈ S(x,p)} and restriction to zero residual.
-/

import RockafellarWets.Chapter9.ImplicitGraphPermutations
import RockafellarWets.Chapter9.SemidifferentiabilityFromAubin
import RockafellarWets.Chapter9.LocalizationDerivatives
import RockafellarWets.Chapter9.InverseLocalizationDerivatives

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal

namespace RW

variable {E P F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [FiniteDimensional ℝ F]
  {S : WithLp 2 (E × P) → Set F} {x : E} {p : P}

/-- Restriction to zero residual preserves the Aubin estimate with the same
constant, since the parameter embedding is an isometry. -/
theorem AubinEstimate.implicitSolution {k : ℝ≥0}
    (h : AubinEstimate (implicitPerturbationMapping S) univ (WithLp.toLp 2 (0,p)) x k) :
    AubinEstimate (implicitSolutionMapping S) univ p x k := by
  obtain ⟨V,hV,W,hW,h⟩ := h
  let J := implicitParameterEmbedding (F := F) (P := P)
  refine ⟨J ⁻¹' V,J.continuous.continuousAt hV,W,hW,?_⟩
  intro a ha b hb v hv
  obtain ⟨z,hz,hd⟩ := h (J a) ⟨trivial,ha.2⟩ (J b) ⟨trivial,hb.2⟩ v hv
  exact ⟨z,hz,by simpa only [J,implicitParameterEmbedding_dist] using hd⟩

/-- **Theorem 9.56(a)**, the implicit Aubin property. -/
theorem hasAubinProperty_implicitSolution_of_coderivative (hS : SvOsc S)
    (hx : 0 ∈ S (WithLp.toLp 2 (x,p)))
    (hQ : ∀ (y : F) (r : P), WithLp.toLp 2 (0,r) ∈ coderivative S (WithLp.toLp 2 (x,p)) 0 y → y = 0 ∧ r = 0) :
    HasAubinPropertyAt (implicitSolutionMapping S) p x := by
  obtain ⟨_,_,_,k,hk⟩ := hasAubinProperty_implicitPerturbation_of_coderivative hS hx hQ
  exact ⟨trivial,hx,RW.IsClosed.isLocallyClosedAt hS.implicit_graphs_closed.2 _,k,hk.implicitSolution⟩

private theorem aubin_mem_svInnerLimit {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {R : A → Set B} {a : A} {b : B}
    (h : HasAubinPropertyAt R a b) : b ∈ svInnerLimit R a := by
  obtain ⟨_,hb,_,k,V,hV,W,hW,h⟩ := h
  intro Q hQ
  obtain ⟨ε,hε,hεQ⟩ := Metric.mem_nhds_iff.mp hQ
  let δ := ε/((k:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hV,ball_mem_nhds a hδ] with y hy hyd
  obtain ⟨z,hz,hd⟩ := h a ⟨trivial,mem_of_mem_nhds hV⟩ y ⟨trivial,hy⟩ b ⟨hb,mem_of_mem_nhds hW⟩
  refine ⟨z,hz,hεQ ?_⟩
  have hdist : dist a y < δ := by simpa only [mem_ball,dist_comm] using hyd
  rw [mem_ball,dist_comm]
  apply hd.trans_lt
  calc
    (k:ℝ)*dist a y ≤ ((k:ℝ)+1)*dist a y := mul_le_mul_of_nonneg_right (by simp) dist_nonneg
    _ < ((k:ℝ)+1)*δ := mul_lt_mul_of_pos_left hdist (by positivity)
    _ = ε := by dsimp [δ]; field_simp

private theorem strictTangent_linear_image {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (J : A →L[ℝ] B) {C : Set A} {D : Set B}
    (hm : ∀ a ∈ C, J a ∈ D) {a w : A} (hw : w ∈ strictTangentCone C a) :
    J w ∈ strictTangentCone D (J a) := by
  obtain ⟨v,z,t,hv,hz,hvt,ht,htt,hq⟩ := mem_strictTangentCone_iff_exists_sequences.mp hw
  apply mem_strictTangentCone_iff_exists_sequences.mpr
  refine ⟨J ∘ v,J ∘ z,t,fun n ↦ hm _ (hv n),fun n ↦ hm _ (hz n),
    J.continuous.continuousAt.tendsto.comp hvt,ht,htt,?_⟩
  simpa only [Function.comp_def,map_smul,map_sub] using J.continuous.continuousAt.tendsto.comp hq

/-- Every strict derivative of the implicit map lifts to a strict derivative
of the original equation with zero residual. -/
theorem strictGraphicalDerivative_implicitSolution_subset {w : E} {q : P}
    (hw : w ∈ strictGraphicalDerivative (implicitSolutionMapping S) p x q) :
    (0:F) ∈ strictGraphicalDerivative S (WithLp.toLp 2 (x,p)) 0 (WithLp.toLp 2 (w,q)) := by
  let J : (P × E) →L[ℝ] (WithLp 2 (E × P) × F) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.comp
      (ContinuousLinearEquiv.prodComm ℝ P E).toContinuousLinearMap).prod 0
  have hm : ∀ a ∈ svGraph (implicitSolutionMapping S), J a ∈ svGraph S := fun _ h ↦ h
  exact strictTangent_linear_image J hm hw

/-- **Theorem 9.56(b)**, a single-valued Lipschitz localization of the
implicit solution mapping. -/
theorem hasLipschitzSingleValuedLocalization_implicitSolution (hS : SvOsc S)
    (hx : 0 ∈ S (WithLp.toLp 2 (x,p)))
    (hQ : ∀ (y : F) (r : P), WithLp.toLp 2 (0,r) ∈ coderivative S (WithLp.toLp 2 (x,p)) 0 y → y = 0 ∧ r = 0)
    (hK : ∀ w : E, (0:F) ∈ strictGraphicalDerivative S (WithLp.toLp 2 (x,p)) 0
      (WithLp.toLp 2 (w,0)) → w = 0) :
    HasLipschitzSingleValuedLocalization (implicitSolutionMapping S) p x := by
  have hA := hasAubinProperty_implicitSolution_of_coderivative hS hx hQ
  apply (hasLipschitzSingleValuedLocalization_iff_strictGraphicalDerivative_zero
    (show x ∈ implicitSolutionMapping S p from hx) (aubin_mem_svInnerLimit hA)).mpr
  apply Subset.antisymm
  · intro w hw
    exact mem_singleton_iff.mpr (hK w (strictGraphicalDerivative_implicitSolution_subset hw))
  · exact singleton_subset_iff.mpr (svPositivelyHomogeneous_strictGraphicalDerivative
      (show x ∈ implicitSolutionMapping S p from hx)).1

private theorem pkConvergesAlong_comp_tendsto {ι κ B : Type*} [TopologicalSpace B]
    {l : Filter ι} {m : Filter κ} [m.NeBot] {C : ι → Set B} {D : Set B}
    (h : PKConvergesAlong l C D) {φ : κ → ι} (ht : Tendsto φ m l) :
    PKConvergesAlong m (C ∘ φ) D := by
  have hi : D ⊆ innerSetLimitAlong m (C ∘ φ) := h.1.ge.trans (innerSetLimitAlong_mono_filter ht C)
  have ho : outerSetLimitAlong m (C ∘ φ) ⊆ D := (outerSetLimitAlong_mono_filter ht C).trans h.2.le
  have hio := innerSetLimitAlong_subset_outerSetLimitAlong (l := m) (C ∘ φ)
  exact ⟨Subset.antisymm (hio.trans ho) hi,Subset.antisymm ho (hi.trans hio)⟩

/-- Semiderivatives restrict to the zero-residual parameter plane. -/
theorem HasMappingSemiderivative.implicitSolution {H : WithLp 2 (F × P) → Set E}
    (h : HasMappingSemiderivative (implicitPerturbationMapping S) (WithLp.toLp 2 (0,p)) x H) :
    HasMappingSemiderivative (implicitSolutionMapping S) p x
      (fun q ↦ H (WithLp.toLp 2 (0,q))) := by
  let J := implicitParameterEmbedding (F := F) (P := P)
  intro q
  let φ := fun a : ℝ × P ↦ (a.1,J a.2)
  have ht : Tendsto φ ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 q) ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 (J q)) :=
    tendsto_fst.prodMk (J.continuous.continuousAt.tendsto.comp tendsto_snd)
  have hh := pkConvergesAlong_comp_tendsto (h (J q)) ht
  convert hh using 1
  funext a
  change (fun z ↦ a.1⁻¹ • (z-x)) '' implicitSolutionMapping S (p+a.1•a.2) =
    (fun z ↦ a.1⁻¹ • (z-x)) '' implicitPerturbationMapping S (J p+a.1•J a.2)
  rw [← map_smul,← map_add]
  rfl

/-- **Theorem 9.56(c)**, the semiderivative and its exact fiber formula. -/
theorem hasMappingSemiderivative_implicitSolution (hS : SvOsc S)
    (hx : 0 ∈ S (WithLp.toLp 2 (x,p)))
    (hQ : ∀ (y : F) (r : P), WithLp.toLp 2 (0,r) ∈ coderivative S (WithLp.toLp 2 (x,p)) 0 y → y = 0 ∧ r = 0)
    (hp : IsProtoDifferentiableAt S (WithLp.toLp 2 (x,p)) 0) :
    HasMappingSemiderivative (implicitSolutionMapping S) p x
      (fun q ↦ {w | (0:F) ∈ graphicalDerivative S (WithLp.toLp 2 (x,p)) 0 (WithLp.toLp 2 (w,q))}) := by
  have hA := hasAubinProperty_implicitPerturbation_of_coderivative hS hx hQ
  have hT := hA.hasMappingSemiderivative ((isProtoDifferentiableAt_implicitPerturbation_iff hx).mpr hp)
  have hh := hT.implicitSolution
  convert hh using 1
  funext q
  ext w
  exact mem_graphicalDerivative_implicitPerturbation_iff.symm

/-- The displayed derivative formula in Theorem 9.56(c). -/
theorem graphicalDerivative_implicitSolution (hS : SvOsc S)
    (hx : 0 ∈ S (WithLp.toLp 2 (x,p)))
    (hQ : ∀ (y : F) (r : P), WithLp.toLp 2 (0,r) ∈ coderivative S (WithLp.toLp 2 (x,p)) 0 y → y = 0 ∧ r = 0)
    (hp : IsProtoDifferentiableAt S (WithLp.toLp 2 (x,p)) 0) :
    graphicalDerivative (implicitSolutionMapping S) p x =
      fun q ↦ {w | (0:F) ∈ graphicalDerivative S (WithLp.toLp 2 (x,p)) 0 (WithLp.toLp 2 (w,q))} :=
  (hasMappingSemiderivative_implicitSolution hS hx hQ hp).protoDerivative.2

/-- With the strict-kernel condition as well, the implicit derivative is a
single-valued globally Lipschitz mapping. -/
theorem exists_lipschitz_implicit_derivative (hS : SvOsc S)
    (hx : 0 ∈ S (WithLp.toLp 2 (x,p)))
    (hQ : ∀ (y : F) (r : P), WithLp.toLp 2 (0,r) ∈ coderivative S (WithLp.toLp 2 (x,p)) 0 y → y = 0 ∧ r = 0)
    (hK : ∀ w : E, (0:F) ∈ strictGraphicalDerivative S (WithLp.toLp 2 (x,p)) 0
      (WithLp.toLp 2 (w,0)) → w = 0)
    (hp : IsProtoDifferentiableAt S (WithLp.toLp 2 (x,p)) 0) :
    ∃ (A : P → E) (k : ℝ≥0), graphicalDerivative (implicitSolutionMapping S) p x = svSingleton A ∧
      LipschitzWith k A := by
  obtain ⟨g,hg⟩ := hasLipschitzSingleValuedLocalization_implicitSolution hS hx hQ hK
  have hg' : IsLipschitzSingleValuedLocalization (implicitSolutionMapping S) p x g := hg
  have hproto := (hasMappingSemiderivative_implicitSolution hS hx hQ hp).protoDerivative.1
  obtain ⟨A,hA,-,hLip⟩ := hg'.strictlyContinuousAt.exists_lipschitz_semiderivative_of_proto
    ((hg'.proto_iff (show x ∈ implicitSolutionMapping S p from hx)).mp hproto)
  exact ⟨A,_,hg'.graphicalDerivative_eq.trans hA,hLip⟩

end RW
