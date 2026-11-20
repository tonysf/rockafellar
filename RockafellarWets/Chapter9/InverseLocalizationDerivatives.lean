/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Derivatives of inverse branches
-/

import RockafellarWets.Chapter9.LocalizationDerivatives
import RockafellarWets.Chapter9.StrictInverseLocalizations

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The explicit inverse-function construction is a specified Lipschitz
localization, with derivative the inverse linear equivalence. -/
theorem HasStrictFDerivAt.exists_strict_inverse_localization [CompleteSpace E]
    {f : E → F} {x : E} {A : E ≃L[ℝ] F} (hf : HasStrictFDerivAt f (A : E →L[ℝ] F) x) :
    ∃ g : F → E, IsLipschitzSingleValuedLocalization (svInv (svSingleton f)) (f x) x g ∧
      HasStrictFDerivAt g (A.symm : F →L[ℝ] E) (f x) ∧
      lipschitzModulus g (f x) = (‖(A.symm : F →L[ℝ] E)‖₊ : ℝ≥0∞) := by
  obtain ⟨g,r,s,k,hr,hs,hgx,hLip,hfiber,hg,hmod⟩ :=
    RW.HasStrictFDerivAt.exists_lipschitz_inverse_branch hf
  exact ⟨g,⟨r,s,k,hr,hs,hgx,hLip,hfiber⟩,hg,hmod⟩

/-- Every localized inverse branch has the same strict derivative. -/
theorem IsLipschitzSingleValuedLocalization.hasStrictFDerivAt_inverse [CompleteSpace E]
    {f : E → F} {g : F → E} {x : E} {A : E ≃L[ℝ] F}
    (h : IsLipschitzSingleValuedLocalization (svInv (svSingleton f)) (f x) x g)
    (hf : HasStrictFDerivAt f (A : E →L[ℝ] F) x) :
    HasStrictFDerivAt g (A.symm : F →L[ℝ] E) (f x) := by
  obtain ⟨r,s,k,hr,hs,_,_,hfiber⟩ := h
  apply hf.to_local_left_inverse
  filter_upwards [hf.hasFDerivAt.continuousAt (ball_mem_nhds (f x) hr),
    ball_mem_nhds x hs] with a hfa ha
  exact (mem_singleton_iff.mp ((hfiber (f a) hfa) ▸
    (show a ∈ svInv (svSingleton f) (f a) ∩ ball x s from ⟨rfl,ha⟩))).symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Theorems 9.54(b), 9.55.** Proto-differentiability gives a localized
inverse semiderivative equal to the inverse graphical derivative. -/
theorem IsLipschitzSingleValuedLocalization.hasMappingSemiderivative_inverse
    {S : E → Set F} {x : E} {u : F} {g : F → E}
    (h : IsLipschitzSingleValuedLocalization (svInv S) u x g)
    (hu : u ∈ S x) (hp : IsProtoDifferentiableAt S x u) :
    HasMappingSemiderivative (svSingleton g) u (g u) (svInv (graphicalDerivative S x u)) := by
  rw [← graphicalDerivative_svInv]
  exact h.hasMappingSemiderivative hu ((isProtoDifferentiableAt_svInv_iff hu).mpr hp)

/-- A strictly continuous single-valued map with a proto-derivative has a
single-valued Lipschitz semiderivative, with its sharp local modulus as a
global Lipschitz constant for that derivative. -/
theorem StrictlyContinuousAt.exists_lipschitz_semiderivative_of_proto
    {f : E → F} {x : E} (hf : StrictlyContinuousAt f x)
    (hp : IsProtoDifferentiableAt (svSingleton f) x (f x)) :
    ∃ A : E → F, graphicalDerivative (svSingleton f) x (f x) = svSingleton A ∧
      HasMappingSemiderivative (svSingleton f) x (f x) (svSingleton A) ∧
      LipschitzWith (lipschitzModulus f x).toNNReal A := by
  classical
  have hs := hf.hasAubinProperty_singleton.hasMappingSemiderivative hp
  have hL := hf.graphicalDerivative_lipschitz
  have hne (w : E) : (graphicalDerivative (svSingleton f) x (f x) w).Nonempty :=
    (hL.1 w (mem_univ w)).1
  have hunique (w : E) (z : F) (hz : z ∈ graphicalDerivative (svSingleton f) x (f x) w) :
      Tendsto (fun p : ℝ × E ↦ p.1⁻¹ • (f (x+p.1 • p.2)-f x))
        ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w) (𝓝 z) := by
    have hi := (hs w).1.symm ▸ hz
    intro Q hQ
    simpa [mappingDifferenceQuotient,svSingleton] using hi Q hQ
  choose A hA using hne
  have he : graphicalDerivative (svSingleton f) x (f x) = svSingleton A := by
    funext w
    apply Subset.antisymm
    · intro z hz
      exact mem_singleton_iff.mpr (tendsto_nhds_unique (hunique w z hz) (hunique w (A w) (hA w)))
    · exact singleton_subset_iff.mpr (hA w)
  refine ⟨A,he,he ▸ hs,?_⟩
  have hLA := svLipschitzOnWith_singleton_iff.mp (he ▸ hL)
  exact (lipschitzOnWith_univ).mp hLA

/-- The inverse derivative in 9.55 is itself single-valued and Lipschitz. -/
theorem IsLipschitzSingleValuedLocalization.exists_inverse_semiderivative
    {S : E → Set F} {x : E} {u : F} {g : F → E}
    (h : IsLipschitzSingleValuedLocalization (svInv S) u x g)
    (hu : u ∈ S x) (hp : IsProtoDifferentiableAt S x u) :
    ∃ A : F → E, svInv (graphicalDerivative S x u) = svSingleton A ∧
      HasMappingSemiderivative (svSingleton g) u (g u) (svSingleton A) ∧
      LipschitzWith (lipschitzModulus g u).toNNReal A := by
  obtain ⟨A,hA,hsemi,hLip⟩ := h.strictlyContinuousAt.exists_lipschitz_semiderivative_of_proto
    ((h.proto_iff hu).mp ((isProtoDifferentiableAt_svInv_iff hu).mpr hp))
  refine ⟨A,?_,hsemi,hLip⟩
  rw [← graphicalDerivative_svInv,h.graphicalDerivative_eq,hA]

end RW
