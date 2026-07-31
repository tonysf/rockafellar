/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Eventually Bounded Set Sequences

Example 4.22, in the equivalent closed-ball formulation of boundedness.
-/

import RockafellarWets.Chapter4.HorizonLimits

open Bornology Filter Function Metric Set Topology

namespace RW

section EventuallyBounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The eventual boundedness condition in Example 4.22. -/
def EventuallyBounded (C : ℕ → Set E) : Prop :=
  ∃ r : ℝ, ∃ N : ℕ, ∀ n ≥ N, C n ⊆ closedBall 0 r

private theorem outerSetLimit_mono_of_eventually {X : Type*} [TopologicalSpace X]
    {A B : ℕ → Set X} (hAB : ∀ᶠ n in atTop, A n ⊆ B n) :
    outerSetLimit A ⊆ outerSetLimit B := by
  intro x hx V hV
  exact (hx V hV).and_eventually hAB |>.mono fun n hn ↦ by
    rcases hn with ⟨⟨y, hyA, hyV⟩, hsub⟩
    exact ⟨y, hsub hyA, hyV⟩

/-- **Example 4.22.** The horizon outer limit is the zero cone exactly when
the sequence is eventually bounded. -/
theorem horizonOuterSetLimit_eq_singleton_zero_iff_eventuallyBounded
    (C : ℕ → Set E) :
    horizonOuterSetLimit C = ({0} : Set E) ↔ EventuallyBounded C := by
  constructor
  · intro hzero
    by_contra hnot
    simp only [EventuallyBounded] at hnot
    push_neg at hnot
    have hfrequent : ∀ k : ℕ,
        ∃ᶠ n in atTop, ∃ x ∈ C n, (k : ℝ) < ‖x‖ := by
      intro k
      rw [frequently_atTop]
      intro N
      rcases hnot (k : ℝ) N with ⟨n, hnN, hnsub⟩
      rw [Set.not_subset] at hnsub
      rcases hnsub with ⟨x, hxC, hxBall⟩
      refine ⟨n, hnN, x, hxC, ?_⟩
      simpa only [mem_closedBall, dist_zero_right, not_le] using hxBall
    rcases extraction_forall_of_frequently hfrequent with ⟨φ, hφ, hhit⟩
    choose y hyC hyNorm using hhit
    have hyNormTop : Tendsto (fun n ↦ ‖y n‖) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      rcases exists_nat_gt b with ⟨N, hbN⟩
      refine ⟨N, fun n hn ↦ ?_⟩
      exact hbN.le.trans (mod_cast hn) |>.trans (hyNorm n).le
    rcases exists_cosmic_convergent_subsequence y with ⟨p, ψ, hψ, hp⟩
    rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
    · have hyx : Tendsto (y ∘ ψ) atTop (nhds x) :=
        tendsto_cosmicEmbed_iff.1 hp
      exact (not_tendsto_nhds_of_tendsto_atTop
        (hyNormTop.comp hψ.tendsto_atTop) ‖x‖) hyx.norm
    · have huOuterCosmic : cosmicDirection u ∈
          outerSetLimit (ordinaryCosmicSequence C) :=
        mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ ∘ ψ, fun n ↦ cosmicEmbed (y (ψ n)), hφ.comp hψ,
            fun n ↦ (cosmicEmbed_mem_cosmicSet_iff).2 (hyC (ψ n)), hp⟩
      have huZero : (u : E) = 0 := by
        have hu := cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1
          huOuterCosmic
        simpa [hzero] using hu
      have huNorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
      simp [huZero] at huNorm
  · rintro ⟨r, N, hbounded⟩
    apply Set.Subset.antisymm
    · intro w hw
      rcases hw with rfl | ⟨u, huOuter, a, ha, rfl⟩
      · simp
      · have heventual : ∀ᶠ n in atTop,
            ordinaryCosmicSequence C n ⊆
              cosmicSet (closedBall (0 : E) r) ({0} : Set E) := by
          filter_upwards [eventually_ge_atTop N] with n hn
          exact cosmicSet_mono (hbounded n hn) Subset.rfl
        have huClosure : cosmicDirection u ∈
            closure (cosmicSet (closedBall (0 : E) r) ({0} : Set E)) := by
          rw [← outerSetLimit_const]
          exact outerSetLimit_mono_of_eventually heventual huOuter
        rw [closure_cosmicSet_zero_of_isBounded isBounded_closedBall,
          mem_cosmicSet] at huClosure
        rcases huClosure with ⟨x, _, hxu⟩ | ⟨v, hv, hvu⟩
        · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
        · have hv0 : (v : E) = 0 := by simpa using hv
          have hvNorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
          simp [hv0] at hvNorm
    · exact Set.singleton_subset_iff.mpr (isCone_horizonOuterSetLimit C).1

end EventuallyBounded

end RW
