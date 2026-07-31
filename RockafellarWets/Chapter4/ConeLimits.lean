/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Limits of Cones

This file proves Theorem 4.14 of Rockafellar--Wets.  Both the inner and
outer Painleve--Kuratowski limits of cones are cones.  In finite dimensions,
if nontrivial cones occur frequently, then their outer limit is nontrivial.
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.MetricSpace.Sequences
import RockafellarWets.Chapter3.Cones
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Function Metric Set Topology

namespace RW

section ConeLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 4.14 (inner-limit clause).** The inner limit of cones is a cone. -/
theorem isCone_innerSetLimit (K : ℕ → Set E) (hK : ∀ n, IsCone (K n)) :
    IsCone (innerSetLimit K) := by
  constructor
  · intro V hV
    have hzeroV : (0 : E) ∈ V := mem_of_mem_nhds hV
    exact Eventually.of_forall fun n ↦ ⟨0, (hK n).1, hzeroV⟩
  · intro x hx c hc V hV
    have hpre : (fun y : E ↦ c • y) ⁻¹' V ∈ nhds x :=
      (continuous_const_smul c).continuousAt hV
    exact (hx _ hpre).mono fun n ⟨y, hyK, hyV⟩ ↦
      ⟨c • y, (hK n).2 hyK hc, hyV⟩

/-- **Theorem 4.14 (outer-limit clause).** The outer limit of cones is a cone. -/
theorem isCone_outerSetLimit (K : ℕ → Set E) (hK : ∀ n, IsCone (K n)) :
    IsCone (outerSetLimit K) := by
  constructor
  · intro V hV
    have hzeroV : (0 : E) ∈ V := mem_of_mem_nhds hV
    exact Frequently.of_forall fun n ↦ ⟨0, (hK n).1, hzeroV⟩
  · intro x hx c hc V hV
    have hpre : (fun y : E ↦ c • y) ⁻¹' V ∈ nhds x :=
      (continuous_const_smul c).continuousAt hV
    exact (hx _ hpre).mono fun n ⟨y, hyK, hyV⟩ ↦
      ⟨c • y, (hK n).2 hyK hc, hyV⟩

/-- **Theorem 4.14 (limit clause).** A Painleve--Kuratowski limit of cones is
a cone. -/
theorem PKConverges.isCone {K : ℕ → Set E} {L : Set E}
    (hlim : PKConverges K L) (hK : ∀ n, IsCone (K n)) : IsCone L := by
  rw [← hlim.inner_eq]
  exact isCone_innerSetLimit K hK

private theorem exists_nonzero_mem_of_isCone_ne_singleton {K : Set E}
    (hK : IsCone K) (hne : K ≠ {0}) : ∃ x ∈ K, x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hne
  exact Set.eq_singleton_iff_unique_mem.2 ⟨hK.1, h⟩

/-- **Theorem 4.14 (nontriviality clause).** If nontrivial cones occur on a
frequent (equivalently, unbounded/infinite) set of indices, then their outer
limit is nontrivial. -/
theorem outerSetLimit_ne_singleton_zero_of_frequently_ne
    [FiniteDimensional ℝ E] (K : ℕ → Set E) (hK : ∀ n, IsCone (K n))
    (hne : ∃ᶠ n in atTop, K n ≠ {0}) : outerSetLimit K ≠ {0} := by
  rcases extraction_of_frequently_atTop hne with ⟨φ, hφ, hφne⟩
  choose x hxK hxne using fun n ↦
    exists_nonzero_mem_of_isCone_ne_singleton (hK (φ n)) (hφne n)
  let u : ℕ → E := fun n ↦ NormedSpace.normalize (x n)
  have huK : ∀ n, u n ∈ K (φ n) := by
    intro n
    exact (hK (φ n)).2 (hxK n) (inv_pos.mpr (norm_pos_iff.mpr (hxne n)))
  have huSphere : ∀ n, u n ∈ sphere (0 : E) 1 := by
    intro n
    simp only [mem_sphere, dist_zero_right, u]
    exact NormedSpace.norm_normalize (hxne n)
  rcases (isCompact_sphere (0 : E) 1).tendsto_subseq huSphere with
    ⟨z, hzSphere, ψ, hψ, hψz⟩
  have hzOuter : z ∈ outerSetLimit K :=
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ ∘ ψ, u ∘ ψ, hφ.comp hψ, fun n ↦ huK (ψ n), hψz⟩
  have hzNe : z ≠ 0 := by
    intro hz
    subst z
    have hzero_one : (0 : ℝ) = 1 := by
      simpa only [mem_sphere, dist_self] using hzSphere
    exact zero_ne_one hzero_one
  intro hsingleton
  have : z = 0 := by
    simpa [hsingleton] using hzOuter
  exact hzNe this

/-- The eventual form of the nontriviality clause in Theorem 4.14. -/
theorem outerSetLimit_ne_singleton_zero_of_eventually_ne
    [FiniteDimensional ℝ E] (K : ℕ → Set E) (hK : ∀ n, IsCone (K n))
    (hne : ∀ᶠ n in atTop, K n ≠ {0}) : outerSetLimit K ≠ {0} :=
  outerSetLimit_ne_singleton_zero_of_frequently_ne K hK hne.frequently

end ConeLimits

section ConeLimitRegressions

/-- Regression: the constant zero cone remains the zero cone. -/
example : IsCone (innerSetLimit (fun _ : ℕ ↦ ({0} : Set ℝ))) := by
  exact isCone_innerSetLimit _ fun _ ↦ ⟨by simp, by simp⟩

/-- Regression: a constant nontrivial cone has nontrivial outer limit. -/
example : outerSetLimit (fun _ : ℕ ↦ Set.Ici (0 : ℝ)) ≠ {0} := by
  apply outerSetLimit_ne_singleton_zero_of_eventually_ne
  · intro n
    exact ⟨by simp, by
      intro x hx c hc
      exact mul_nonneg hc.le hx⟩
  · exact Eventually.of_forall fun _ h ↦ by
      have hmem := congrArg (fun S : Set ℝ ↦ (1 : ℝ) ∈ S) h
      simp at hmem

end ConeLimitRegressions

end RW
