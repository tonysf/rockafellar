/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Derivatives and exact moduli of single-valued localizations
-/

import RockafellarWets.Chapter9.SingleValuedLocalizations
import RockafellarWets.Chapter9.StrictDerivativeModulus
import RockafellarWets.Chapter9.CoderivativeNorms
import RockafellarWets.Chapter9.MordukhovichCriterion
import RockafellarWets.Chapter9.SingleValuedGraphicalDerivatives

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A specified function representing a set-valued mapping's graph locally. -/
def IsLipschitzSingleValuedLocalization (S : E → Set F) (x : E) (u : F) (g : E → F) : Prop :=
  ∃ (r s : ℝ) (k : ℝ≥0), 0 < r ∧ 0 < s ∧ g x = u ∧
    LipschitzOnWith k g (ball x r) ∧ ∀ a ∈ ball x r, S a ∩ ball u s = {g a}

variable {S : E → Set F} {x : E} {u : F} {g : E → F}

/-- Local closedness is preserved by equality on a neighborhood. -/
theorem IsLocallyClosedAt.congr_nhds {A B : Set E} {a : E}
    (h : IsLocallyClosedAt A a) (he : A =ᶠ[𝓝 a] B) : IsLocallyClosedAt B a := by
  obtain ⟨V,hV,hVc,hAV⟩ := h
  obtain ⟨r,hr,hrE⟩ := Metric.mem_nhds_iff.mp he
  have hsmall {b : E} (hb : b ∈ closedBall a (r/2)) : A b = B b :=
    hrE (lt_of_le_of_lt hb (half_lt_self hr))
  have heq : B ∩ (V ∩ closedBall a (r/2)) = (A ∩ V) ∩ closedBall a (r/2) := by
    ext b
    constructor
    · rintro ⟨hb,hbV,hbr⟩
      exact ⟨⟨Eq.mpr (hsmall hbr) hb,hbV⟩,hbr⟩
    · rintro ⟨⟨hb,hbV⟩,hbr⟩
      exact ⟨Eq.mp (hsmall hbr) hb,hbV,hbr⟩
  exact ⟨V ∩ closedBall a (r/2),inter_mem hV (closedBall_mem_nhds a (half_pos hr)),
    hVc.inter isClosed_closedBall,heq ▸ hAV.inter isClosed_closedBall⟩

theorem IsLipschitzSingleValuedLocalization.base_eq
    (h : IsLipschitzSingleValuedLocalization S x u g) : g x = u := by
  obtain ⟨r,s,k,hr,hs,hg,hL,hf⟩ := h
  exact hg

theorem IsLipschitzSingleValuedLocalization.strictlyContinuousAt
    (h : IsLipschitzSingleValuedLocalization S x u g) : StrictlyContinuousAt g x := by
  obtain ⟨r,s,k,hr,hs,hg,hL,hf⟩ := h
  exact strictlyContinuousAt_iff.mpr ⟨k,ball x r,ball_mem_nhds x hr,hL⟩

theorem IsLipschitzSingleValuedLocalization.graph_eventuallyEq
    (h : IsLipschitzSingleValuedLocalization S x u g) :
    svGraph S =ᶠ[𝓝 (x,u)] svGraph (svSingleton g) := by
  obtain ⟨r,s,k,hr,hs,hg,hL,hf⟩ := h
  filter_upwards [prod_mem_nhds (ball_mem_nhds x hr) (ball_mem_nhds u hs)] with p hp
  apply propext
  change p.2 ∈ S p.1 ↔ p.2 ∈ ({g p.1} : Set F)
  exact ⟨fun hv ↦ (hf p.1 hp.1) ▸ ⟨hv,hp.2⟩,
    fun hv ↦ ((hf p.1 hp.1).symm ▸ hv).1⟩

theorem IsLipschitzSingleValuedLocalization.euclideanGraph_eventuallyEq
    (h : IsLipschitzSingleValuedLocalization S x u g) :
    euclideanSvGraph S =ᶠ[𝓝 (WithLp.toLp 2 (x,u))] euclideanSvGraph (svSingleton g) :=
  h.graph_eventuallyEq.comp_tendsto
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous.continuousAt.tendsto

/-- Ordinary and strict graphical derivatives are unchanged by localization. -/
theorem IsLipschitzSingleValuedLocalization.graphicalDerivative_eq
    (h : IsLipschitzSingleValuedLocalization S x u g) :
    graphicalDerivative S x u = graphicalDerivative (svSingleton g) x (g x) := by
  rw [h.base_eq]
  exact congrArg svOfEuclideanGraph (tangentCone_congr_nhds h.euclideanGraph_eventuallyEq)

theorem IsLipschitzSingleValuedLocalization.strictGraphicalDerivative_eq
    (h : IsLipschitzSingleValuedLocalization S x u g) :
    strictGraphicalDerivative S x u = strictGraphicalDerivative (svSingleton g) x (g x) := by
  rw [h.base_eq]
  unfold strictGraphicalDerivative
  rw [strictTangentCone_congr_nhds h.graph_eventuallyEq]

theorem IsLipschitzSingleValuedLocalization.mem
    (h : IsLipschitzSingleValuedLocalization S x u g) : u ∈ S x := by
  obtain ⟨r,s,k,hr,hs,hg,hL,hf⟩ := h
  have hmem : g x ∈ S x ∩ ball u s := (hf x (mem_ball_self hr)).symm ▸ mem_singleton (g x)
  exact hg ▸ hmem.1

/-- A Lipschitz branch gives both local closedness and an Aubin estimate. -/
theorem IsLipschitzSingleValuedLocalization.hasAubinProperty [FiniteDimensional ℝ E]
    (h : IsLipschitzSingleValuedLocalization S x u g) : HasAubinPropertyAt S x u := by
  have hl := h.strictlyContinuousAt.hasAubinProperty_singleton.2.2.1
  rw [h.base_eq] at hl
  have hc := hl.congr_nhds h.graph_eventuallyEq.symm
  have hu := h.mem
  obtain ⟨r,s,k,hr,hs,hg,hL,hf⟩ := h
  refine ⟨trivial,hu,hc,k,ball x r,ball_mem_nhds x hr,ball u s,ball_mem_nhds u hs,?_⟩
  intro a ha b hb v hv
  have hv' : v = g a := mem_singleton_iff.mp ((hf a ha.2) ▸ hv)
  have hgb : g b ∈ S b ∩ ball u s := (hf b hb.2).symm ▸ mem_singleton (g b)
  exact ⟨g b,hgb.1,hv' ▸ hL.dist_le_mul a ha.2 b hb.2⟩

/-- Proto-differentiability, like both tangent cones, depends only on the graph germ. -/
theorem IsLipschitzSingleValuedLocalization.proto_iff
    (h : IsLipschitzSingleValuedLocalization S x u g) (hu : u ∈ S x) :
    IsProtoDifferentiableAt S x u ↔ IsProtoDifferentiableAt (svSingleton g) x (g x) := by
  rw [isProtoDifferentiableAt_iff_geometricallyDerivable hu,
    isProtoDifferentiableAt_iff_geometricallyDerivable (show g x ∈ svSingleton g x from rfl),h.base_eq]
  unfold IsGeometricallyDerivable
  rw [tangentCone_congr_nhds h.euclideanGraph_eventuallyEq,
    derivableCone_congr_nhds h.euclideanGraph_eventuallyEq]

/-- **Theorem 9.54**, the semiderivative of a localization. -/
theorem IsLipschitzSingleValuedLocalization.hasMappingSemiderivative
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : IsLipschitzSingleValuedLocalization S x u g) (hu : u ∈ S x)
    (hp : IsProtoDifferentiableAt S x u) :
    HasMappingSemiderivative (svSingleton g) x (g x) (graphicalDerivative S x u) := by
  rw [h.graphicalDerivative_eq]
  exact h.strictlyContinuousAt.hasAubinProperty_singleton.hasMappingSemiderivative
    (h.proto_iff hu |>.mp hp)

/-- **Theorem 9.54**, the strict derivative gives the exact branch modulus. -/
theorem IsLipschitzSingleValuedLocalization.strictDerivative_norm
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : IsLipschitzSingleValuedLocalization S x u g) :
    svOuterNorm (strictGraphicalDerivative S x u) = lipschitzModulus g x := by
  rw [h.strictGraphicalDerivative_eq]
  exact svOuterNorm_strictGraphicalDerivative_singleton h.strictlyContinuousAt.continuousAt

section InnerProduct
variable {P Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  {R : P → Set Q} {a : P} {b : Q} {f : P → Q}

theorem IsLipschitzSingleValuedLocalization.coderivative_eq
    (h : IsLipschitzSingleValuedLocalization R a b f) :
    coderivative R a b = coderivative (svSingleton f) a (f a) := by
  rw [h.base_eq]
  exact congrArg svOfEuclideanNormals (normalCone_congr_nhds h.euclideanGraph_eventuallyEq)

/-- **Theorem 9.54**, the coderivative gives the same exact branch modulus. -/
theorem IsLipschitzSingleValuedLocalization.coderivative_norm
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    (h : IsLipschitzSingleValuedLocalization R a b f) :
    svOuterNorm (coderivative R a b) = lipschitzModulus f a := by
  rw [h.coderivative_eq]
  exact svOuterNorm_coderivative_svSingleton h.strictlyContinuousAt

/-- **Theorem 9.54**, the graphical modulus equals the branch modulus. -/
theorem IsLipschitzSingleValuedLocalization.graphical_modulus
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    (h : IsLipschitzSingleValuedLocalization R a b f) :
    graphicalLipschitzModulus R a b = lipschitzModulus f a := by
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative h.mem h.hasAubinProperty.2.2.1]
  exact h.coderivative_norm

/-- The coderivative kernel vanishes for every Lipschitz localization. -/
theorem IsLipschitzSingleValuedLocalization.coderivative_zero
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    (h : IsLipschitzSingleValuedLocalization R a b f) : coderivative R a b 0 = {0} :=
  (hasAubinPropertyAt_iff_coderivative_zero h.mem h.hasAubinProperty.2.2.1).mp h.hasAubinProperty

end InnerProduct
end RW
