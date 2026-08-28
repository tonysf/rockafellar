/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Uniform Convergence of Monotone Sequences

Theorem 5.48, the set-valued Dini theorem.

The book reduces to 5.43 and then translates the remaining claim -- continuous
convergence relative to `X` -- through 5.42(b) into an inequality argument
about the scalar functions `dν(x) = d(u, Sν(x))`.  As in 5.43, that
translation is unnecessary here: the same argument runs on the `ε`-`ρ`
inclusions, and it is shorter, because in each case one of the two inclusions
is free.

For the increasing case, `Sν(y) ⊂ S(y)`, so the first inclusion is just the
outer semicontinuity of `S` at `x̄` -- no index condition at all.  The second
is the book's argument: pick one index `ν₀` at which `S(x̄)` is already
`ε/2`-approximated by `Sν₀(x̄)`, spread that to nearby `y ∈ X` by the inner
semicontinuity of the *single* mapping `Sν₀`, and ride the monotonicity up to
every `ν ≥ ν₀`.  The decreasing case is the mirror image, with `S(y) ⊂ Sν(y)`
making the second inclusion free and the first one carrying the work.

The book's "there's no loss of generality in assuming `Sν(x)` to be closed
too" is discharged rather than assumed.  In the decreasing case the `Sν` are
osc, hence already closed-valued.  In the increasing case they need not be,
and 5.12(b) does need a closed value to run its finite subcover; the repair is
`SvIscWithinAt.closure` -- inner semicontinuity survives closing the values,
because inner limits are closed -- together with `thickening δ (cl A) =
thickening δ A`, which is what makes the closure invisible in the conclusion.

`X ⊂ dom S` is not needed and is not assumed.
-/

import RockafellarWets.Chapter5.ContinuousVersusUniform

open Filter Metric Set Topology

namespace RW

section Monotonicity

variable {G : Type*} [TopologicalSpace G]

/-- Every term of an increasing convergent sequence sits inside the limit. -/
theorem subset_of_monotone_pkConverges {A : ℕ → Set G} {C : Set G}
    (hmono : Monotone A) (h : PKConverges A C) (n : ℕ) : A n ⊆ C := by
  rw [← h.1]
  intro u hu V hV
  filter_upwards [eventually_ge_atTop n] with k hk
  exact ⟨u, hmono hk hu, mem_of_mem_nhds hV⟩

/-- The limit of a decreasing sequence sits inside every closed term. -/
theorem subset_of_antitone_pkConverges {A : ℕ → Set G} {C : Set G} {n : ℕ}
    (hanti : Antitone A) (h : PKConverges A C) (hclosed : IsClosed (A n)) :
    C ⊆ A n := by
  rw [← h.2]
  intro u hu
  rw [← hclosed.closure_eq]
  refine mem_closure_iff_nhds.2 fun V hV ↦ ?_
  obtain ⟨k, ⟨y, hyA, hyV⟩, hk⟩ :=
    ((hu V hV).and_eventually (eventually_ge_atTop n)).exists
  exact ⟨y, hyV, hanti hk hyA⟩

end Monotonicity

section IscClosure

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
variable {S : E → Set F} {X : Set E} {x : E}

/-- Inner semicontinuity survives closing the values: inner limits are closed,
so an inclusion into one extends to the closure of its source.  This is the
book's "no loss of generality in assuming `Sν(x)` to be closed too". -/
theorem SvIscWithinAt.closure (h : SvIscWithinAt S X x) :
    SvIscWithinAt (fun y ↦ _root_.closure (S y)) X x :=
  (IsClosed.closure_subset_iff (isClosed_innerSetLimitAlong _ _)).2
    (h.trans (innerSetLimitAlong_mono fun _ ↦ subset_closure))

end IscClosure

section Increasing

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E}

/-- **Theorem 5.48(a)**, the substance: an increasing sequence of inner
semicontinuous mappings converging pointwise on `X` to an outer semicontinuous
`S` converges continuously to `S` relative to `X`. -/
theorem svConvergesContinuouslyOn_of_monotone
    (hmono : ∀ x ∈ X, Monotone fun n ↦ Sseq n x)
    (hconv : ∀ x ∈ X, PKConverges (fun n ↦ Sseq n x) (S x))
    (hSosc : SvOscOn S X) (hisc : ∀ n, SvIscOn (Sseq n) X) :
    SvConvergesContinuouslyOn Sseq S X := by
  intro x hx
  have hclx : IsClosed (S x) := SvOscWithinAt.isClosed hx (hSosc x hx)
  refine (svConvergesContinuouslyWithinAt_iff hx hclx).2 fun ε hε ρ hρ ↦ ?_
  obtain ⟨V₁, hV₁, hoscS⟩ :=
    (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset hclx).1 (hSosc x hx)
      ρ hρ ε hε
  obtain ⟨n₀, hn₀⟩ :=
    ((pkConverges_iff_eventually_inclusions hclx).1 (hconv x hx)
      (ε / 2) (by linarith) ρ hρ).exists
  have hclcl : IsClosed (closure (Sseq n₀ x)) := isClosed_closure
  obtain ⟨V₂, hV₂, hiscn⟩ :=
    (svIscWithinAt_iff_exists_nhds_inter_closedBall_subset
      (S := fun y ↦ closure (Sseq n₀ y)) (X := X) (x := x) hclcl).1
      (hisc n₀ x hx).closure (ρ + ε) (by linarith) (ε / 2) (by linarith)
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn y hy
  refine ⟨fun w hw ↦ hoscS y ⟨hy.2, hy.1.1⟩
      ⟨subset_of_monotone_pkConverges (hmono y hy.2) (hconv y hy.2) n hw.1, hw.2⟩, ?_⟩
  have hclose : Sseq n₀ x ∩ closedBall 0 (ρ + ε) ⊆
      thickening (ε / 2) (Sseq n₀ y) := by
    intro w hw
    have := hiscn y ⟨hy.2, hy.1.2⟩ ⟨subset_closure hw.1, hw.2⟩
    rwa [thickening_closure] at this
  have hstep := inter_closedBall_subset_thickening_trans
    (by linarith : ρ + ε / 2 ≤ ρ + ε) hn₀.2 hclose
  rw [add_halves] at hstep
  exact hstep.trans (thickening_subset_of_subset ε (hmono y hy.2 hn))

/-- **Theorem 5.48(a)**: the limit is continuous relative to `X` and the
convergence is uniform on every compact subset of `X`. -/
theorem svContinuousOn_and_svConvergesUniformlyOn_of_monotone
    (hmono : ∀ x ∈ X, Monotone fun n ↦ Sseq n x)
    (hconv : ∀ x ∈ X, PKConverges (fun n ↦ Sseq n x) (S x))
    (hSosc : SvOscOn S X) (hisc : ∀ n, SvIscOn (Sseq n) X) :
    SvContinuousOn S X ∧
      ∀ B ⊆ X, IsCompact B → SvConvergesUniformlyOn Sseq S B := by
  obtain ⟨huni, hcont⟩ := svConvergesContinuouslyOn_iff.1
    (svConvergesContinuouslyOn_of_monotone hmono hconv hSosc hisc)
  exact ⟨hcont, huni⟩

end Increasing

section Decreasing

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E}

/-- **Theorem 5.48(b)**, the substance.  The mirror image of (a): now
`S(y) ⊂ Sν(y)`, so the second inclusion is the inner semicontinuity of `S`,
and the first carries the argument through a single index `ν₀`. -/
theorem svConvergesContinuouslyOn_of_antitone
    (hanti : ∀ x ∈ X, Antitone fun n ↦ Sseq n x)
    (hconv : ∀ x ∈ X, PKConverges (fun n ↦ Sseq n x) (S x))
    (hSisc : SvIscOn S X) (hosc : ∀ n, SvOscOn (Sseq n) X) :
    SvConvergesContinuouslyOn Sseq S X := by
  intro x hx
  have hclx : IsClosed (S x) := by
    rw [← (hconv x hx).2]
    exact isClosed_outerSetLimit _
  refine (svConvergesContinuouslyWithinAt_iff hx hclx).2 fun ε hε ρ hρ ↦ ?_
  obtain ⟨V₁, hV₁, hiscS⟩ :=
    (svIscWithinAt_iff_exists_nhds_inter_closedBall_subset hclx).1 (hSisc x hx)
      ρ hρ ε hε
  obtain ⟨n₀, hn₀⟩ :=
    ((pkConverges_iff_eventually_inclusions hclx).1 (hconv x hx)
      (ε / 2) (by linarith) (ρ + ε) (by linarith)).exists
  obtain ⟨V₂, hV₂, hoscn⟩ :=
    (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset
      (S := Sseq n₀) (X := X) (x := x)
      (SvOscWithinAt.isClosed hx (hosc n₀ x hx))).1 (hosc n₀ x hx)
      ρ hρ (ε / 2) (by linarith)
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn y hy
  refine ⟨?_, fun w hw ↦ thickening_subset_of_subset ε
      (subset_of_antitone_pkConverges (hanti y hy.2) (hconv y hy.2)
        (SvOscWithinAt.isClosed hy.2 (hosc n y hy.2)))
      (hiscS y ⟨hy.2, hy.1.1⟩ hw)⟩
  have hfirst : Sseq n y ∩ closedBall 0 ρ ⊆ thickening (ε / 2) (Sseq n₀ x) :=
    fun w hw ↦ hoscn y ⟨hy.2, hy.1.2⟩ ⟨hanti y hy.2 hn hw.1, hw.2⟩
  have hstep := inter_closedBall_subset_thickening_trans
    (by linarith : ρ + ε / 2 ≤ ρ + ε) hfirst hn₀.1
  rwa [add_halves] at hstep

/-- **Theorem 5.48(b)**. -/
theorem svContinuousOn_and_svConvergesUniformlyOn_of_antitone
    (hanti : ∀ x ∈ X, Antitone fun n ↦ Sseq n x)
    (hconv : ∀ x ∈ X, PKConverges (fun n ↦ Sseq n x) (S x))
    (hSisc : SvIscOn S X) (hosc : ∀ n, SvOscOn (Sseq n) X) :
    SvContinuousOn S X ∧
      ∀ B ⊆ X, IsCompact B → SvConvergesUniformlyOn Sseq S B := by
  obtain ⟨huni, hcont⟩ := svConvergesContinuouslyOn_iff.1
    (svConvergesContinuouslyOn_of_antitone hanti hconv hSisc hosc)
  exact ⟨hcont, huni⟩

end Decreasing

end RW
