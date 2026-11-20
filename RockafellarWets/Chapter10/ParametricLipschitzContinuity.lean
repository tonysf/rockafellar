/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Parametric Lipschitz continuity and differentiability

Corollary 10.14, including the attained multiplier norm bound and its exact
convex specialization.
-/

import RockafellarWets.Chapter10.ConvexParametricSubgradients
import RockafellarWets.Chapter9.StrictDifferentiability

open Filter Metric Set Topology
open scoped InnerProductSpace ENNReal NNReal

namespace RW

noncomputable section

variable {E P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- **Corollary 10.14(a)**: absence of nonzero horizon multipliers gives
strict continuity of the optimal value. -/
theorem eRealStrictlyContinuousAt_parametricValue {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a)
    (hQ : horizonParametricMultipliers f u = {0}) : ERealStrictlyContinuousAt (parametricValue f) u := by
  have hlu := isLocallyLscAt_of_isLocallyClosedAt_epigraph hu
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _
      (lowerSemicontinuous_parametricValue hl hp hb)) _)
  apply (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hu hlu).mpr
  apply Subset.antisymm
  · rw [← hQ]
    exact horizonSubdifferential_parametricValue_subset hl hb hu
  · exact singleton_subset_iff.mpr (subdifferential_properties hu).2.2.2.2.1.1

/-- The multiplier set is nonempty and compact under the qualification. -/
theorem parametricMultipliers_nonempty_compact {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a)
    (hQ : horizonParametricMultipliers f u = {0}) :
    (parametricMultipliers f u).Nonempty ∧ IsCompact (parametricMultipliers f u) := by
  have hsc := eRealStrictlyContinuousAt_parametricValue hl hp hb hu hQ
  obtain ⟨y,hy⟩ := hsc.subdifferential_nonempty_compact.1
  refine ⟨⟨y,subdifferential_parametricValue_subset hl hb hu hy⟩,?_⟩
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_parametricMultipliers hl hb hu).1
  apply isBounded_iff_horizonCone_eq_singleton_zero.mpr
  apply Subset.antisymm
  · rw [← hQ]
    exact horizonCone_parametricMultipliers_subset hl hb hu
  · exact singleton_subset_iff.mpr (zero_mem_horizonCone _)

/-- **Corollary 10.14(a)**, the multiplier maximum is attained and bounds
the sharp local Lipschitz modulus. -/
theorem parametricValue_modulus_le_max_multiplier {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a)
    (hQ : horizonParametricMultipliers f u = {0}) :
    ∃ y ∈ parametricMultipliers f u,
      lipschitzModulus (fun v ↦ (parametricValue f v).toReal) u ≤ (‖y‖₊ : ℝ≥0∞) ∧
      ∀ z ∈ parametricMultipliers f u, ‖z‖ ≤ ‖y‖ := by
  have hsc := eRealStrictlyContinuousAt_parametricValue hl hp hb hu hQ
  obtain ⟨hne,hcompact⟩ := parametricMultipliers_nonempty_compact hl hp hb hu hQ
  obtain ⟨y,hy,hmax⟩ := hcompact.exists_isMaxOn hne continuous_norm.continuousOn
  obtain ⟨z,hz,he,_⟩ := hsc.exists_subgradient_norm_eq_modulus
  refine ⟨y,hy,?_,isMaxOn_iff.mp hmax⟩
  rw [he]
  exact ENNReal.coe_le_coe.mpr (hmax (subdifferential_parametricValue_subset hl hb hu hz))

/-- **Corollary 10.14(b)**: a unique multiplier gives the strict gradient. -/
theorem hasStrictGradientAt_parametricValue {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f)
    {u y : P} {a : ℝ} (hu : parametricValue f u = a)
    (hQ : horizonParametricMultipliers f u = {0}) (hY : parametricMultipliers f u = {y}) :
    HasStrictGradientAt (parametricValue f) y u := by
  have hsc := eRealStrictlyContinuousAt_parametricValue hl hp hb hu hQ
  apply hasStrictGradientAt_of_subdifferential_eq hsc
  have hsub : subdifferential (parametricValue f) u ⊆ {y} :=
    hY ▸ subdifferential_parametricValue_subset hl hb hu
  apply Subset.antisymm hsub
  apply singleton_subset_iff.mpr
  obtain ⟨z,hz⟩ := hsc.subdifferential_nonempty_compact.1
  exact (mem_singleton_iff.mp (hsub hz)) ▸ hz

/-- **Corollary 10.14**, necessity of the horizon qualification for a convex integrand. -/
theorem eRealStrictlyContinuousAt_parametricValue_iff_of_convex
    {f : WithLp 2 (E × P) → EReal} (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f)
    (hp : IsProper f) (hb : IsParametricallyLevelBounded f) {u : P} {a : ℝ}
    (hu : parametricValue f u = a) :
    ERealStrictlyContinuousAt (parametricValue f) u ↔ horizonParametricMultipliers f u = {0} := by
  have hlu := isLocallyLscAt_of_isLocallyClosedAt_epigraph hu
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _
      (lowerSemicontinuous_parametricValue hl hp hb)) _)
  rw [eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hu hlu,
    (subdifferentials_parametricValue_eq_multipliers_of_convex hc hl hp hb hu).2]

/-- The multiplier norm bound is an equality in the convex case. -/
theorem parametricValue_modulus_eq_max_multiplier_of_convex
    {f : WithLp 2 (E × P) → EReal} (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f)
    (hp : IsProper f) (hb : IsParametricallyLevelBounded f) {u : P} {a : ℝ}
    (hu : parametricValue f u = a) (hQ : horizonParametricMultipliers f u = {0}) :
    ∃ y ∈ parametricMultipliers f u,
      lipschitzModulus (fun v ↦ (parametricValue f v).toReal) u = (‖y‖₊ : ℝ≥0∞) ∧
      ∀ z ∈ parametricMultipliers f u, ‖z‖ ≤ ‖y‖ := by
  rw [← (subdifferentials_parametricValue_eq_multipliers_of_convex hc hl hp hb hu).1]
  exact (eRealStrictlyContinuousAt_parametricValue hl hp hb hu hQ).exists_subgradient_norm_eq_modulus

end

end RW
