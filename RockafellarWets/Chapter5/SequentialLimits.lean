/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Sequences Inside the Limits of Formula 5(1)

Formula 5(1) takes its limits along the neighborhood filter of the base
point, whereas Chapter 4 works with sequences indexed by `atTop`.  Several
results of Chapter 5 -- the sequential criteria 5.6(c)(d) first among them --
are stated in terms of sequences `xν → x̄`, so this file builds the bridge
once and for all.

The transport in one direction is free: a sequence tending to `x̄` pushes
`atTop` forward into the neighborhood filter, and the limits are monotone in
the index filter.  The other direction is a diagonal argument.  It produces
more than one might expect: every point of the *outer* limit along the
neighborhood filter already lies in the *inner* limit along a single suitably
chosen sequence.  That extra strength is what lets Chapter 4's subsequence
compactness be applied afterwards, since inner limits only grow when passing
to a subsequence.
-/

import RockafellarWets.Chapter4.SetConvergenceCompactness
import RockafellarWets.Chapter5.Semicontinuity

open Filter Set Topology

namespace RW

section Transport

variable {ι κ E : Type*} [TopologicalSpace E]

/-- Reindexing a family of sets along `f` is pushing the index filter forward
along `f`. -/
theorem outerSetLimitAlong_comp (l : Filter κ) (f : κ → ι) (C : ι → Set E) :
    outerSetLimitAlong l (C ∘ f) = outerSetLimitAlong (Filter.map f l) C := rfl

/-- Reindexing a family of sets along `f` is pushing the index filter forward
along `f`. -/
theorem innerSetLimitAlong_comp (l : Filter κ) (f : κ → ι) (C : ι → Set E) :
    innerSetLimitAlong l (C ∘ f) = innerSetLimitAlong (Filter.map f l) C := rfl

/-- The sequential outer limit along a sequence drawn from `l` is no larger
than the outer limit along `l` itself. -/
theorem outerSetLimit_comp_subset {l : Filter ι} {C : ι → Set E} {y : ℕ → ι}
    (hy : Tendsto y atTop l) :
    outerSetLimit (C ∘ y) ⊆ outerSetLimitAlong l C := by
  rw [← outerSetLimitAlong_atTop, outerSetLimitAlong_comp]
  exact outerSetLimitAlong_mono_filter hy C

/-- The inner limit along `l` is no larger than the sequential inner limit
along any sequence drawn from `l`. -/
theorem innerSetLimitAlong_subset_innerSetLimit_comp {l : Filter ι}
    {C : ι → Set E} {y : ℕ → ι} (hy : Tendsto y atTop l) :
    innerSetLimitAlong l C ⊆ innerSetLimit (C ∘ y) := by
  rw [← innerSetLimitAlong_atTop, innerSetLimitAlong_comp]
  exact innerSetLimitAlong_mono_filter hy C

end Transport

section Extraction

variable {ι E : Type*} [TopologicalSpace E]

/-- **The diagonal extraction.**  Along a countably generated index filter,
every point of the outer limit lies in the *inner* limit along a single
sequence drawn from that filter.

Pairing an antitone basis of `𝓝 u` with an antitone basis of `l` index by
index turns the frequent hits guaranteed by the outer limit into eventual
hits along the resulting sequence. -/
theorem exists_seq_mem_innerSetLimit [FirstCountableTopology E]
    {l : Filter ι} [l.IsCountablyGenerated] {C : ι → Set E} {u : E}
    (hu : u ∈ outerSetLimitAlong l C) :
    ∃ y : ℕ → ι, Tendsto y atTop l ∧ u ∈ innerSetLimit (C ∘ y) := by
  obtain ⟨W, hW⟩ := (nhds u).exists_antitone_basis
  obtain ⟨U, hU⟩ := l.exists_antitone_basis
  have hpick : ∀ k, ∃ i, i ∈ U k ∧ (C i ∩ W k).Nonempty := by
    intro k
    have hfreq := hu (W k) (hW.toHasBasis.mem_of_mem trivial)
    have hmem : ∀ᶠ i in l, i ∈ U k :=
      Filter.eventually_mem_set.2 (hU.toHasBasis.mem_of_mem trivial)
    obtain ⟨i, hhit, hiU⟩ := (hfreq.and_eventually hmem).exists
    exact ⟨i, hiU, hhit⟩
  choose y hyU hyhit using hpick
  refine ⟨y, hU.tendsto hyU, fun V hV ↦ ?_⟩
  obtain ⟨k, -, hkV⟩ := hW.toHasBasis.mem_iff.1 hV
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (hyhit n).mono
    (inter_subset_inter_right _ ((hW.antitone hn).trans hkV))

/-- The dual extraction.  If a point misses the inner limit along a countably
generated filter, then it misses the outer limit along some single sequence
drawn from that filter. -/
theorem exists_seq_not_mem_outerSetLimit {l : Filter ι}
    [l.IsCountablyGenerated] {C : ι → Set E} {u : E}
    (hu : u ∉ innerSetLimitAlong l C) :
    ∃ y : ℕ → ι, Tendsto y atTop l ∧ u ∉ outerSetLimit (C ∘ y) := by
  obtain ⟨V, hV, hnot⟩ :
      ∃ V ∈ nhds u, ¬ ∀ᶠ i in l, (C i ∩ V).Nonempty := by
    by_contra hcon
    push_neg at hcon
    exact hu fun V hV ↦ hcon V hV
  obtain ⟨y, hy, hyempty⟩ :=
    Filter.exists_seq_forall_of_frequently (Filter.not_eventually.1 hnot)
  refine ⟨y, hy, fun hcon ↦ ?_⟩
  obtain ⟨n, hn⟩ := (hcon V hV).exists
  exact hyempty n hn

end Extraction

section Within

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- A sequence converging to `x` within `X` can be corrected so that *all* of
its terms lie in `X`, without disturbing its tail.  Convergence within `X`
only puts the terms in `X` eventually, whereas the book's sequential criteria
ask for `xν ∈ X` for every `ν`. -/
theorem exists_seq_mem_of_tendsto_nhdsWithin {X : Set E} {x : E} (hx : x ∈ X)
    {y : ℕ → E} (hy : Tendsto y atTop (nhdsWithin x X)) :
    ∃ z : ℕ → E, (∀ n, z n ∈ X) ∧ Tendsto z atTop (nhds x) ∧
      z =ᶠ[atTop] y := by
  classical
  have hy' := tendsto_nhdsWithin_iff.1 hy
  have heq : (fun n ↦ if y n ∈ X then y n else x) =ᶠ[atTop] y := by
    filter_upwards [hy'.2] with n hn
    simp [hn]
  exact ⟨fun n ↦ if y n ∈ X then y n else x,
    fun n ↦ by by_cases h : y n ∈ X <;> simp [h, hx],
    hy'.1.congr' heq.symm, heq⟩

/-- Any sequence in `X` converging to `x` converges to `x` within `X`. -/
theorem tendsto_nhdsWithin_of_forall_mem {X : Set E} {x : E} {y : ℕ → E}
    (hyX : ∀ n, y n ∈ X) (hy : Tendsto y atTop (nhds x)) :
    Tendsto y atTop (nhdsWithin x X) :=
  tendsto_nhdsWithin_iff.2 ⟨hy, .of_forall hyX⟩

/-- Sequential extraction for formula 5(1): a point of the outer limit of `S`
relative to `X` is reached along a single sequence in `X`, and reached in the
strong, inner-limit sense. -/
theorem exists_seq_mem_innerSetLimit_of_mem_svOuterLimitWithin
    [FirstCountableTopology E] [FirstCountableTopology F] {S : E → Set F}
    {X : Set E} {x : E} (hx : x ∈ X) {u : F}
    (hu : u ∈ svOuterLimitWithin S X x) :
    ∃ y : ℕ → E, (∀ n, y n ∈ X) ∧ Tendsto y atTop (nhds x) ∧
      u ∈ innerSetLimit fun n ↦ S (y n) := by
  obtain ⟨y₀, hy₀, hu₀⟩ := exists_seq_mem_innerSetLimit hu
  obtain ⟨y, hyX, hyto, hyeq⟩ := exists_seq_mem_of_tendsto_nhdsWithin hx hy₀
  refine ⟨y, hyX, hyto, fun V hV ↦ ?_⟩
  filter_upwards [hu₀ V hV, hyeq] with n hn hne
  simpa [hne] using hn

/-- The dual sequential extraction: a point missing the inner limit of `S`
relative to `X` misses the outer limit along a single sequence in `X`. -/
theorem exists_seq_not_mem_outerSetLimit_of_not_mem_svInnerLimitWithin
    [FirstCountableTopology E] {S : E → Set F} {X : Set E} {x : E}
    (hx : x ∈ X) {u : F} (hu : u ∉ svInnerLimitWithin S X x) :
    ∃ y : ℕ → E, (∀ n, y n ∈ X) ∧ Tendsto y atTop (nhds x) ∧
      u ∉ outerSetLimit fun n ↦ S (y n) := by
  obtain ⟨y₀, hy₀, hu₀⟩ := exists_seq_not_mem_outerSetLimit hu
  obtain ⟨y, hyX, hyto, hyeq⟩ := exists_seq_mem_of_tendsto_nhdsWithin hx hy₀
  refine ⟨y, hyX, hyto, fun hcon ↦ hu₀ fun V hV ↦ ?_⟩
  exact ((hcon V hV).and_eventually hyeq).mono fun n hn ↦ by
    simpa [Function.comp_def, hn.2] using hn.1

/-- The sequences in `X` converging to `x`, the index set of the two formulas
below. -/
def svApproachSeqs (X : Set E) (x : E) : Set (ℕ → E) :=
  {y | (∀ n, y n ∈ X) ∧ Tendsto y atTop (nhds x)}

@[simp]
theorem mem_svApproachSeqs {X : Set E} {x : E} {y : ℕ → E} :
    y ∈ svApproachSeqs X x ↔ (∀ n, y n ∈ X) ∧ Tendsto y atTop (nhds x) :=
  Iff.rfl

/-- **The outer bridge.**  The outer limit of formula 5(1) relative to `X` is
the union of the Chapter 4 outer limits along all sequences in `X`
approaching `x`. -/
theorem svOuterLimitWithin_eq_iUnion [FirstCountableTopology E]
    [FirstCountableTopology F] (S : E → Set F) {X : Set E} {x : E}
    (hx : x ∈ X) :
    svOuterLimitWithin S X x =
      ⋃ y ∈ svApproachSeqs X x, outerSetLimit fun n ↦ S (y n) := by
  refine Subset.antisymm (fun u hu ↦ ?_) (iUnion₂_subset fun y hy ↦ ?_)
  · obtain ⟨y, hyX, hyto, hmem⟩ :=
      exists_seq_mem_innerSetLimit_of_mem_svOuterLimitWithin hx hu
    exact mem_iUnion₂.2
      ⟨y, ⟨hyX, hyto⟩, innerSetLimit_subset_outerSetLimit _ hmem⟩
  · exact outerSetLimit_comp_subset (tendsto_nhdsWithin_of_forall_mem hy.1 hy.2)

/-- **The inner bridge.**  The inner limit of formula 5(1) relative to `X` is
the intersection of the Chapter 4 inner limits along all sequences in `X`
approaching `x`. -/
theorem svInnerLimitWithin_eq_iInter [FirstCountableTopology E]
    (S : E → Set F) {X : Set E} {x : E} (hx : x ∈ X) :
    svInnerLimitWithin S X x =
      ⋂ y ∈ svApproachSeqs X x, innerSetLimit fun n ↦ S (y n) := by
  refine Subset.antisymm (subset_iInter₂ fun y hy ↦ ?_) fun u hu ↦ ?_
  · exact innerSetLimitAlong_subset_innerSetLimit_comp
      (tendsto_nhdsWithin_of_forall_mem hy.1 hy.2)
  · by_contra hcon
    obtain ⟨y, hyX, hyto, hnot⟩ :=
      exists_seq_not_mem_outerSetLimit_of_not_mem_svInnerLimitWithin hx hcon
    exact hnot (innerSetLimit_subset_outerSetLimit _
      (mem_iInter₂.1 hu y ⟨hyX, hyto⟩))

end Within

end RW
