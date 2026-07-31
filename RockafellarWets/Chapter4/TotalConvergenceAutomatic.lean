/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Automatic Total Convergence

Automatic cases from Theorem 4.25, proved through the horizon criterion.
-/

import RockafellarWets.Chapter3.PointedCones
import RockafellarWets.Chapter4.EventuallyBounded
import RockafellarWets.Chapter4.TotalConvergence

open Bornology Filter Function Set Topology

namespace RW

section AutomaticCases

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem horizonOuterSetLimit_subset_outerSetLimit_of_isCone
    {K : ℕ → Set E} (hK : ∀ n, IsCone (K n)) :
    horizonOuterSetLimit K ⊆ outerSetLimit K := by
  intro w hw
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact (isCone_outerSetLimit K hK).1
  · rcases mem_outerSetLimit_iff_exists_subsequence.1 huOuter with
      ⟨φ, z, hφ, hz, hzu⟩
    have hz' : ∀ n, z n ∈ cosmicEmbed '' K (φ n) := by
      intro n
      simpa only [ordinaryCosmicSequence, cosmicSet, cosmicDirections_zero,
        union_empty] using hz n
    choose y hyK hyz using hz'
    have hyu : Tendsto (fun n ↦ cosmicEmbed (y n)) atTop
        (nhds (cosmicDirection u)) := by
      apply hzu.congr'
      exact Eventually.of_forall fun n ↦ (hyz n).symm
    rcases exists_scaling_of_tendsto_cosmicDirection hyu with
      ⟨scale, hscalePos, _, hscaled⟩
    have huOrdinary : (u : E) ∈ outerSetLimit K :=
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ, fun n ↦ scale n • y n, hφ,
          fun n ↦ (hK (φ n)).2 (hyK n) (hscalePos n), hscaled⟩
    exact (isCone_outerSetLimit K hK).2 huOrdinary hr

/-- **Theorem 4.25(b).** Ordinary convergence of cones to a nonempty set is
automatically total convergence. -/
theorem totalConverges_of_isCone
    {K : ℕ → Set E} {C : Set E} (hlim : PKConverges K C)
    (_hCne : C.Nonempty) (hK : ∀ n, IsCone (K n)) :
    TotalConverges K C := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  refine ⟨hlim, ?_⟩
  have hCcone : IsCone C := hlim.isCone hK
  rw [horizonCone_eq_self_of_isClosed_isCone hlim.isClosed hCcone]
  rw [← hlim.outer_eq]
  exact horizonOuterSetLimit_subset_outerSetLimit_of_isCone hK

/-- **Theorem 4.25(c).** Ordinary convergence of an increasing sequence to
a nonempty set is automatically total convergence. -/
theorem totalConverges_of_monotone
    {Cseq : ℕ → Set E} {C : Set E} (hlim : PKConverges Cseq C)
    (_hCne : C.Nonempty) (hmono : Monotone Cseq) :
    TotalConverges Cseq C := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  refine ⟨hlim, ?_⟩
  have hCeq : C = closure (⋃ n, Cseq n) :=
    hlim.unique (pkConverges_of_monotone hmono)
  intro w hw
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact zero_mem_horizonCone C
  · have huUnionClosure : cosmicDirection u ∈
        closure (cosmicSet (⋃ n, Cseq n) ({0} : Set E)) := by
      rw [← outerSetLimit_const]
      have hmonoCosmic : ∀ n, ordinaryCosmicSequence Cseq n ⊆
          cosmicSet (⋃ n, Cseq n) ({0} : Set E) := by
        intro n p hp
        change p ∈ cosmicSet (Cseq n) ({0} : Set E) at hp
        rw [mem_cosmicSet] at hp
        rw [mem_cosmicSet]
        rcases hp with ⟨x, hx, hxp⟩ | ⟨v, hv, hvp⟩
        · exact Or.inl ⟨x, mem_iUnion_of_mem n hx, hxp⟩
        · exact Or.inr ⟨v, hv, hvp⟩
      exact outerSetLimit_mono hmonoCosmic huOuter
    have huHorizonUnion : (u : E) ∈ horizonCone (⋃ n, Cseq n) := by
      have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
      rw [closure_cosmicSet hzero, mem_cosmicSet] at huUnionClosure
      rcases huUnionClosure with ⟨x, _, hxu⟩ | ⟨v, hv, hvu⟩
      · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
      · have hvu' : v = u := injective_cosmicDirection hvu
        rcases hv with hv | hv
        · simpa [hvu'] using hv
        · have hv0 : (v : E) = 0 := by simpa using hv
          have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
          simp [hv0] at hvnorm
    have huC : (u : E) ∈ horizonCone C := by
      rw [hCeq, horizonCone_closure]
      exact huHorizonUnion
    exact (isCone_horizonCone C).2 huC hr

/-- **Theorem 4.25(d).** A common bounded containing set makes ordinary
convergence to a nonempty set automatically total. -/
theorem totalConverges_of_uniformly_bounded
    {Cseq : ℕ → Set E} {C B : Set E} (hlim : PKConverges Cseq C)
    (_hCne : C.Nonempty) (hB : Bornology.IsBounded B) (hCB : ∀ n, Cseq n ⊆ B) :
    TotalConverges Cseq C := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  refine ⟨hlim, ?_⟩
  intro w hw
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact zero_mem_horizonCone C
  · have huBclosure : cosmicDirection u ∈
        closure (cosmicSet B ({0} : Set E)) := by
      rw [← outerSetLimit_const]
      exact outerSetLimit_mono
        (C := ordinaryCosmicSequence Cseq)
        (D := fun _ ↦ cosmicSet B ({0} : Set E))
        (fun n ↦ cosmicSet_mono (hCB n) Subset.rfl) huOuter
    rw [closure_cosmicSet_zero_of_isBounded hB, mem_cosmicSet] at huBclosure
    rcases huBclosure with ⟨x, _, hxu⟩ | ⟨v, hv, hvu⟩
    · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
    · have hv0 : (v : E) = 0 := by simpa using hv
      have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
      simp [hv0] at hvnorm

/-- The eventual-boundedness extension mentioned after Theorem 4.25. -/
theorem totalConverges_of_eventuallyBounded
    {Cseq : ℕ → Set E} {C : Set E} (hlim : PKConverges Cseq C)
    (_hCne : C.Nonempty) (hbdd : EventuallyBounded Cseq) :
    TotalConverges Cseq C := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  refine ⟨hlim, ?_⟩
  rw [(horizonOuterSetLimit_eq_singleton_zero_iff_eventuallyBounded Cseq).2 hbdd]
  intro w hw
  have hw0 : w = 0 := by simpa using hw
  subst w
  exact zero_mem_horizonCone C

end AutomaticCases

end RW
