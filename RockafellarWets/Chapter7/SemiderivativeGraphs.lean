/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graphical characterization of semidifferentiability

Theorem 7.21(d) uses the finite graph of the difference quotients restricted
to each closed ball. Uniform bounds on that ball prevent graph heights from
escaping at a direction in its interior.
-/

import RockafellarWets.Chapter7.SemidifferentiabilityCharacterizations
import RockafellarWets.Chapter7.FiniteGraphConvergence

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 7.21(a,d).** On each ball, the difference quotients are
eventually equibounded and their finite graphs converge to a single-valued
real graph. The graphical condition is stated along every sequence of
positive step sizes tending to zero. -/
theorem semidifferentiableAt_iff_graphicalConvergence {f : E → EReal} {x : E}
    (hx : f x ≠ ⊥) (hx' : f x ≠ ⊤) :
    SemidifferentiableAt f x ↔ ∀ ρ : ℝ, 0 < ρ → ∃ g : E → ℝ,
      (∃ M : ℝ, ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ w ∈ closedBall (0 : E) ρ,
        differenceQuotient f x τ w ∈ Icc ((-M : ℝ) : EReal) (M : EReal)) ∧
      ∀ τ : ℕ → ℝ, Tendsto τ atTop (𝓝[>] (0 : ℝ)) →
        GraphicalConvergesOn (fun n ↦ finiteGraphFiber (differenceQuotient f x (τ n)))
          (finiteGraphFiber (fun w ↦ (g w : EReal))) (closedBall (0 : E) ρ) := by
  classical
  constructor
  · intro hs ρ _
    obtain ⟨g, hg, _, hl⟩ := hs.exists_semiderivative
    have hK := isCompact_closedBall (0 : E) ρ
    obtain ⟨M, hM⟩ := (hK.image hg).isBounded.subset_closedBall (0 : ℝ)
    refine ⟨g, ⟨M + 1, ?_⟩, ?_⟩
    · have hu := eventually_forall_mem_of_forall_tendsto hK hg
          (fun w _ ↦ (hl w).1.2.2) (ε := 1) one_pos
      filter_upwards [hu] with τ hτ
      intro w hw
      have hgw : |g w| ≤ M := by
        simpa [Real.dist_eq] using mem_closedBall.mp (hM (mem_image_of_mem g hw))
      obtain ⟨hgw₁, hgw₂⟩ := abs_le.mp hgw
      exact ⟨(EReal.coe_le_coe_iff.mpr (by linarith)).trans (hτ w hw).1.le,
        (hτ w hw).2.le.trans (EReal.coe_le_coe_iff.mpr (by linarith))⟩
    · intro τ hτ w hw
      have hc : ConvergesContinuouslyWithinAt (fun n ↦ differenceQuotient f x (τ n))
          (fun u ↦ (g u : EReal)) (closedBall (0 : E) ρ) w :=
        fun _ _ hz ↦ (hl w).1.2.2.comp (hτ.prodMk hz)
      exact hc.graphicalConvergesWithinAt_finiteGraphFiber hw
  · intro hall w
    let ρ := ‖w‖ + 1
    have hw : w ∈ ball (0 : E) ρ := by simp [ρ]
    obtain ⟨g, ⟨M, hbound⟩, hgraph⟩ := hall ρ (by dsimp [ρ]; positivity)
    refine ⟨(g w : EReal), hx, hx', tendsto_iff_seq_tendsto.mpr ?_⟩
    intro p hp
    let τ := fun n ↦ (p n).1
    let z := fun n ↦ (p n).2
    have hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)) := tendsto_fst.comp hp
    have hz : Tendsto z atTop (𝓝 w) := tendsto_snd.comp hp
    have hb : EventuallyLocallyBoundedWithinAt (fun n ↦ differenceQuotient f x (τ n))
        (closedBall (0 : E) ρ) w :=
      ⟨univ, univ_mem, M, (hτ.eventually hbound).mono fun n hn y hy ↦ hn y hy.2⟩
    have hc := convergesContinuouslyWithinAt_of_finiteGraph_of_eventuallyLocallyBounded
      hb (hgraph τ hτ w (ball_subset_closedBall hw))
    let y := fun n ↦ if z n ∈ closedBall (0 : E) ρ then z n else w
    have hy : ∀ n, y n ∈ closedBall (0 : E) ρ := by
      intro n
      dsimp [y]
      split <;> simp_all [ball_subset_closedBall hw]
    have heq : y =ᶠ[atTop] z :=
      (hz.eventually_mem (isOpen_ball.mem_nhds hw)).mono fun n hn ↦
        if_pos (ball_subset_closedBall hn)
    exact (hc y hy (hz.congr' heq.symm)).congr'
      (heq.mono fun n hn ↦ congrArg (differenceQuotient f x (τ n)) hn)

end RW
