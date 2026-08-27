/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Set Limits Along a Filter

Chapter 4 develops Painleve--Kuratowski limits for sequences of sets, indexed
along `atTop`.  Formula 5(1) needs the same limits taken as `x → x̄`, so this
file restates Definition 4.1 for an arbitrary index filter and records that
the Chapter 4 notions are exactly the `atTop` case.

The Chapter 4 definitions are left untouched: they are already verified
against fifty numbered results, and the two families agree definitionally, so
nothing is gained by rewriting them in place.
-/

import RockafellarWets.Chapter4.SetLimits

open Filter Set Topology

namespace RW

section Definitions

variable {ι E : Type*} [TopologicalSpace E]

/-- Definition 4.1 along an arbitrary index filter: a point lies in the outer
limit when each of its neighborhoods is hit frequently along `l`. -/
def outerSetLimitAlong (l : Filter ι) (C : ι → Set E) : Set E :=
  {x | ∀ V ∈ nhds x, ∃ᶠ i in l, (C i ∩ V).Nonempty}

/-- Definition 4.1 along an arbitrary index filter: a point lies in the inner
limit when each of its neighborhoods is hit eventually along `l`. -/
def innerSetLimitAlong (l : Filter ι) (C : ι → Set E) : Set E :=
  {x | ∀ V ∈ nhds x, ∀ᶠ i in l, (C i ∩ V).Nonempty}

@[simp]
theorem mem_outerSetLimitAlong {l : Filter ι} {C : ι → Set E} {x : E} :
    x ∈ outerSetLimitAlong l C ↔
      ∀ V ∈ nhds x, ∃ᶠ i in l, (C i ∩ V).Nonempty := Iff.rfl

@[simp]
theorem mem_innerSetLimitAlong {l : Filter ι} {C : ι → Set E} {x : E} :
    x ∈ innerSetLimitAlong l C ↔
      ∀ V ∈ nhds x, ∀ᶠ i in l, (C i ∩ V).Nonempty := Iff.rfl

/-- The Chapter 4 sequential outer limit is the `atTop` case. -/
theorem outerSetLimitAlong_atTop (C : ℕ → Set E) :
    outerSetLimitAlong atTop C = outerSetLimit C := rfl

/-- The Chapter 4 sequential inner limit is the `atTop` case. -/
theorem innerSetLimitAlong_atTop (C : ℕ → Set E) :
    innerSetLimitAlong atTop C = innerSetLimit C := rfl

end Definitions

section BasicProperties

variable {ι E : Type*} [TopologicalSpace E]

/-- Along a nontrivial filter the inner limit sits inside the outer limit. -/
theorem innerSetLimitAlong_subset_outerSetLimitAlong
    {l : Filter ι} [l.NeBot] (C : ι → Set E) :
    innerSetLimitAlong l C ⊆ outerSetLimitAlong l C :=
  fun _ hx V hV ↦ (hx V hV).frequently

/-- Outer limits shrink when the index filter shrinks. -/
theorem outerSetLimitAlong_mono_filter {l₁ l₂ : Filter ι} (h : l₁ ≤ l₂)
    (C : ι → Set E) :
    outerSetLimitAlong l₁ C ⊆ outerSetLimitAlong l₂ C :=
  fun _ hx V hV ↦ (hx V hV).filter_mono h

/-- Inner limits grow when the index filter shrinks. -/
theorem innerSetLimitAlong_mono_filter {l₁ l₂ : Filter ι} (h : l₁ ≤ l₂)
    (C : ι → Set E) :
    innerSetLimitAlong l₂ C ⊆ innerSetLimitAlong l₁ C :=
  fun _ hx V hV ↦ (hx V hV).filter_mono h

/-- Both limits are monotone in the family of sets. -/
theorem outerSetLimitAlong_mono {l : Filter ι} {C D : ι → Set E}
    (h : ∀ i, C i ⊆ D i) :
    outerSetLimitAlong l C ⊆ outerSetLimitAlong l D :=
  fun _ hx V hV ↦ (hx V hV).mono fun i ⟨z, hz, hzV⟩ ↦ ⟨z, h i hz, hzV⟩

theorem innerSetLimitAlong_mono {l : Filter ι} {C D : ι → Set E}
    (h : ∀ i, C i ⊆ D i) :
    innerSetLimitAlong l C ⊆ innerSetLimitAlong l D :=
  fun _ hx V hV ↦ (hx V hV).mono fun i ⟨z, hz, hzV⟩ ↦ ⟨z, h i hz, hzV⟩

private theorem outerSetLimitAlong_subset_of_eventuallyEq {l : Filter ι}
    {C D : ι → Set E} (h : C =ᶠ[l] D) :
    outerSetLimitAlong l C ⊆ outerSetLimitAlong l D :=
  fun _ hx V hV ↦ (hx V hV).mp (h.mono fun _ hi hhit ↦ hi ▸ hhit)

private theorem innerSetLimitAlong_subset_of_eventuallyEq {l : Filter ι}
    {C D : ι → Set E} (h : C =ᶠ[l] D) :
    innerSetLimitAlong l C ⊆ innerSetLimitAlong l D :=
  fun _ hx V hV ↦ (hx V hV).mp (h.mono fun _ hi hhit ↦ hi ▸ hhit)

/-- Both limits only see the eventual behavior of the family. -/
theorem outerSetLimitAlong_congr {l : Filter ι} {C D : ι → Set E}
    (h : C =ᶠ[l] D) : outerSetLimitAlong l C = outerSetLimitAlong l D :=
  Subset.antisymm (outerSetLimitAlong_subset_of_eventuallyEq h)
    (outerSetLimitAlong_subset_of_eventuallyEq h.symm)

/-- Both limits only see the eventual behavior of the family. -/
theorem innerSetLimitAlong_congr {l : Filter ι} {C D : ι → Set E}
    (h : C =ᶠ[l] D) : innerSetLimitAlong l C = innerSetLimitAlong l D :=
  Subset.antisymm (innerSetLimitAlong_subset_of_eventuallyEq h)
    (innerSetLimitAlong_subset_of_eventuallyEq h.symm)

/-- The outer limit is closed, including when some or all sets are empty.
The Chapter 4 proof never mentions the index filter. -/
theorem isClosed_outerSetLimitAlong (l : Filter ι) (C : ι → Set E) :
    IsClosed (outerSetLimitAlong l C) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx V hV
  rcases mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hxU⟩
  rcases mem_closure_iff.1 hx U hUopen hxU with ⟨y, hyU, hyLim⟩
  exact (hyLim U (hUopen.mem_nhds hyU)).mono fun i ⟨z, hzC, hzU⟩ ↦
    ⟨z, hzC, hUV hzU⟩

/-- The inner limit is closed, including when some or all sets are empty. -/
theorem isClosed_innerSetLimitAlong (l : Filter ι) (C : ι → Set E) :
    IsClosed (innerSetLimitAlong l C) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx V hV
  rcases mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hxU⟩
  rcases mem_closure_iff.1 hx U hUopen hxU with ⟨y, hyU, hyLim⟩
  exact (hyLim U (hUopen.mem_nhds hyU)).mono fun i ⟨z, hzC, hzU⟩ ↦
    ⟨z, hzC, hUV hzU⟩

end BasicProperties

end RW
