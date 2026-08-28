/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Continuous and Uniform Convergence

Definition 5.41, together with the two identifications the book records
immediately afterwards.

Both are 4.10 in disguise.  Pointwise convergence at a single point is, by
4.10, the pair of `ε`-inclusions between `Sν(x̄)` and `S(x̄)` on every bounded
ball; continuous convergence at `x̄` is the same pair of inclusions between
`Sν(x)` and `S(x̄)`, holding uniformly for `x` in some neighborhood of `x̄`.

The sequential definition and the neighborhood form are reconciled by
spreading a sequence of bad indices out into a single approaching sequence,
the same `Function.extend` device as in 5.33 -- except that here the bad
indices need not be strictly increasing, so `Function.extend` is unfolded by
hand rather than through the injective-case lemma.  That costs nothing: the
redistributed sequence lands on *some* bad argument for the same bad index,
which is all the contradiction needs.

Clause (a) of 5.42 is recorded here too, being 4.7 verbatim.
-/

import RockafellarWets.Chapter4.UniformApproximation
import RockafellarWets.Chapter5.Semicontinuity

open Filter Metric Set Topology

namespace RW

section Definitions

variable {E F : Type*} [PseudoMetricSpace E] [SeminormedAddCommGroup F]

/-- **Definition 5.41**: `Sν` converges continuously to `S` at `x̄` relative to
`X`. -/
def SvConvergesContinuouslyWithinAt (Sseq : ℕ → E → Set F) (S : E → Set F)
    (X : Set E) (x : E) : Prop :=
  ∀ y : ℕ → E, (∀ n, y n ∈ X) → Tendsto y atTop (nhds x) →
    PKConverges (fun n ↦ Sseq n (y n)) (S x)

/-- **Definition 5.41** in the absolute case. -/
def SvConvergesContinuouslyAt (Sseq : ℕ → E → Set F) (S : E → Set F) (x : E) :
    Prop :=
  SvConvergesContinuouslyWithinAt Sseq S univ x

/-- **Definition 5.41**: continuous convergence everywhere. -/
def SvConvergesContinuously (Sseq : ℕ → E → Set F) (S : E → Set F) : Prop :=
  ∀ x, SvConvergesContinuouslyAt Sseq S x

/-- **Definition 5.41**: continuous convergence relative to `X`. -/
def SvConvergesContinuouslyOn (Sseq : ℕ → E → Set F) (S : E → Set F)
    (X : Set E) : Prop :=
  ∀ x ∈ X, SvConvergesContinuouslyWithinAt Sseq S X x

/-- **Definition 5.41**: `Sν` converges uniformly to `S` on `X`. -/
def SvConvergesUniformlyOn (Sseq : ℕ → E → Set F) (S : E → Set F) (X : Set E) :
    Prop :=
  ∀ ε > 0, ∀ ρ > 0, ∀ᶠ n in atTop, ∀ x ∈ X,
    Sseq n x ∩ closedBall 0 ρ ⊆ thickening ε (S x) ∧
      S x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n x)

theorem svConvergesContinuouslyAt_iff_forall_seq {Sseq : ℕ → E → Set F}
    {S : E → Set F} {x : E} :
    SvConvergesContinuouslyAt Sseq S x ↔
      ∀ y : ℕ → E, Tendsto y atTop (nhds x) →
        PKConverges (fun n ↦ Sseq n (y n)) (S x) :=
  ⟨fun h y hy ↦ h y (fun _ ↦ mem_univ _) hy, fun h y _ hy ↦ h y hy⟩

end Definitions

section Extend

variable {E : Type*} [TopologicalSpace E]

/-- A sequence of points converging to `x` can be redistributed along an
arbitrary index sequence, filling the unused indices with `x` itself.  Unlike
in 5.33 the index sequence need not be injective, so `Function.extend` is
unfolded directly. -/
private theorem tendsto_extend_index {m : ℕ → ℕ} {y : ℕ → E} {x : E}
    (hy : Tendsto y atTop (nhds x)) :
    Tendsto (Function.extend m y (fun _ ↦ x)) atTop (nhds x) := by
  classical
  have key : ∀ V ∈ nhds x,
      ∀ᶠ j in atTop, Function.extend m y (fun _ ↦ x) j ∈ V := by
    intro V hV
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hy.eventually_mem hV)
    refine eventually_atTop.2 ⟨(Finset.range K).sup m + 1, fun j hj ↦ ?_⟩
    by_cases h : ∃ k, m k = j
    · rw [Function.extend_def, dif_pos h]
      refine hK _ (le_of_not_gt fun hlt ↦ ?_)
      have hle : m (Classical.choose h) ≤ (Finset.range K).sup m :=
        Finset.le_sup (Finset.mem_range.2 hlt)
      rw [Classical.choose_spec h] at hle
      omega
    · rw [Function.extend_apply' _ _ _ h]
      exact mem_of_mem_nhds hV
  exact fun V hV ↦ key V hV

end Extend

section Identifications

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {x : E}

omit [PseudoMetricSpace E] in
/-- **Theorem 4.10** repackaged: for a closed limit, convergence is the pair
of `ε`-inclusions on every bounded ball, eventually. -/
theorem pkConverges_iff_eventually_inclusions {A : ℕ → Set F} {C : Set F}
    (hC : IsClosed C) :
    PKConverges A C ↔
      ∀ ε > 0, ∀ ρ > 0, ∀ᶠ n in atTop,
        A n ∩ closedBall 0 ρ ⊆ thickening ε C ∧
          C ∩ closedBall 0 ρ ⊆ thickening ε (A n) := by
  rw [pkConverges_iff_eventuallyInnerApproximates_and_eventuallyOuterApproximates hC]
  constructor
  · rintro ⟨hin, hout⟩ ε hε ρ hρ
    exact (hout ρ hρ ε hε).and (hin ρ hρ ε hε)
  · intro h
    exact ⟨fun ρ hρ ε hε ↦ (h ε hε ρ hρ).mono fun _ hn ↦ hn.2,
      fun ρ hρ ε hε ↦ (h ε hε ρ hρ).mono fun _ hn ↦ hn.1⟩

omit [PseudoMetricSpace E] in
/-- The first remark after 5.41: by 4.10, pointwise convergence at a single
point is the pair of `ε`-inclusions between `Sν(x̄)` and `S(x̄)`. -/
theorem pkConverges_apply_iff (hS : IsClosed (S x)) :
    PKConverges (fun n ↦ Sseq n x) (S x) ↔
      ∀ ε > 0, ∀ ρ > 0, ∀ᶠ n in atTop,
        Sseq n x ∩ closedBall 0 ρ ⊆ thickening ε (S x) ∧
          S x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n x) :=
  pkConverges_iff_eventually_inclusions hS

/-- The second remark after 5.41, relative to a set: continuous convergence
at `x̄` is the same pair of inclusions, holding uniformly for `x` in `X` near
`x̄`. -/
theorem svConvergesContinuouslyWithinAt_iff {X : Set E} (hx : x ∈ X)
    (hS : IsClosed (S x)) :
    SvConvergesContinuouslyWithinAt Sseq S X x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V ∩ X,
        Sseq n y ∩ closedBall 0 ρ ⊆ thickening ε (S x) ∧
          S x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n y) := by
  classical
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨ε, hε, ρ, hρ, hbad⟩ := hcon
    -- Collect a bad index and a nearby bad argument of `X` for each `k`.
    have hpick : ∀ k : ℕ, ∃ (n : ℕ) (y : E), k ≤ n ∧ y ∈ X ∧
        dist y x < ((k : ℝ) + 1)⁻¹ ∧
        ¬ (Sseq n y ∩ closedBall 0 ρ ⊆ thickening ε (S x) ∧
            S x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n y)) := by
      intro k
      have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      obtain ⟨n, hn, y, hyV, hybad⟩ :=
        frequently_atTop.1 (hbad (ball x ((k : ℝ) + 1)⁻¹) (ball_mem_nhds x hδ)) k
      exact ⟨n, y, hn, hyV.2, mem_ball.1 hyV.1, not_and.2 hybad⟩
    choose ms ys hms hysX hys hbadk using hpick
    have hysTo : Tendsto ys atTop (nhds x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ (hys k).le) ?_
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    -- Redistribute them into a single sequence in `X` approaching `x̄`.
    set z : ℕ → E := Function.extend ms ys (fun _ ↦ x) with hz
    have hzX : ∀ j, z j ∈ X := by
      intro j
      by_cases hj : ∃ k, ms k = j
      · rw [hz, Function.extend_def, dif_pos hj]
        exact hysX _
      · rw [hz, Function.extend_apply' _ _ _ hj]
        exact hx
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((pkConverges_iff_eventually_inclusions hS).1
        (h z hzX (tendsto_extend_index hysTo)) ε hε ρ hρ)
    have hex : ∃ k, ms k = ms N := ⟨N, rfl⟩
    have hzval : z (ms N) = ys (Classical.choose hex) := by
      rw [hz, Function.extend_def, dif_pos hex]
    refine hbadk (Classical.choose hex) ?_
    rw [Classical.choose_spec hex, ← hzval]
    exact hN (ms N) (hms N)
  · intro h y hyX hy
    refine (pkConverges_iff_eventually_inclusions hS).2 fun ε hε ρ hρ ↦ ?_
    obtain ⟨V, hV, hsub⟩ := h ε hε ρ hρ
    filter_upwards [hsub, hy.eventually_mem hV] with n hn hyn
    exact hn (y n) ⟨hyn, hyX n⟩

/-- The second remark after 5.41, in the absolute case. -/
theorem svConvergesContinuouslyAt_iff (hS : IsClosed (S x)) :
    SvConvergesContinuouslyAt Sseq S x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V,
        Sseq n y ∩ closedBall 0 ρ ⊆ thickening ε (S x) ∧
          S x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n y) := by
  simpa only [inter_univ] using
    svConvergesContinuouslyWithinAt_iff (X := univ) (mem_univ x) hS

end Identifications

section DistanceDescriptions

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {x : E}

omit [PseudoMetricSpace E] in
/-- **Exercise 5.42(a)**: pointwise convergence at `x̄` is convergence of the
distance to `Sν(x̄)` from every point.  Distances are extended-real, as
throughout Chapter 5 (see 5.11), so the empty value is handled by `d(u, ∅) = ∞`
rather than by a truncation. -/
theorem pkConverges_apply_iff_tendsto_infEDist (hS : IsClosed (S x)) :
    PKConverges (fun n ↦ Sseq n x) (S x) ↔
      ∀ u : F, Tendsto (fun n ↦ Metric.infEDist u (Sseq n x)) atTop
        (nhds (Metric.infEDist u (S x))) :=
  pkConverges_iff_tendsto_infEDist hS

end DistanceDescriptions

end RW
