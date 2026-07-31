/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Set Limits

This file introduces the sequence-specific Painleve--Kuratowski set limits
from Definition 4.1 of Rockafellar--Wets.  The outer limit records frequent
neighborhood hits, while the inner limit records eventual neighborhood hits.
This convention handles empty sets without auxiliary nonemptiness assumptions.
-/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sequences

open Filter Set Topology

namespace RW

section Definitions

variable {E : Type*} [TopologicalSpace E]

/-- **Definition 4.1 (outer set limit).** A point is in the outer limit when
every one of its neighborhoods meets the sets frequently along `atTop`. -/
def outerSetLimit (C : ℕ → Set E) : Set E :=
  {x | ∀ V ∈ nhds x, ∃ᶠ n in atTop, (C n ∩ V).Nonempty}

/-- **Definition 4.1 (inner set limit).** A point is in the inner limit when
every one of its neighborhoods meets the sets eventually along `atTop`. -/
def innerSetLimit (C : ℕ → Set E) : Set E :=
  {x | ∀ V ∈ nhds x, ∀ᶠ n in atTop, (C n ∩ V).Nonempty}

/-- Painleve--Kuratowski convergence of a sequence of sets. -/
def PKConverges (C : ℕ → Set E) (D : Set E) : Prop :=
  innerSetLimit C = D ∧ outerSetLimit C = D

@[simp]
theorem mem_outerSetLimit {C : ℕ → Set E} {x : E} :
    x ∈ outerSetLimit C ↔ ∀ V ∈ nhds x, ∃ᶠ n in atTop, (C n ∩ V).Nonempty :=
  Iff.rfl

@[simp]
theorem mem_innerSetLimit {C : ℕ → Set E} {x : E} :
    x ∈ innerSetLimit C ↔ ∀ V ∈ nhds x, ∀ᶠ n in atTop, (C n ∩ V).Nonempty :=
  Iff.rfl

theorem innerSetLimit_subset_outerSetLimit (C : ℕ → Set E) :
    innerSetLimit C ⊆ outerSetLimit C := by
  intro x hx V hV
  exact (hx V hV).frequently

theorem PKConverges.inner_eq {C : ℕ → Set E} {D : Set E}
    (h : PKConverges C D) :
    innerSetLimit C = D :=
  h.1

theorem PKConverges.outer_eq {C : ℕ → Set E} {D : Set E}
    (h : PKConverges C D) :
    outerSetLimit C = D :=
  h.2

theorem PKConverges.unique {C : ℕ → Set E} {D F : Set E}
    (hD : PKConverges C D) (hF : PKConverges C F) : D = F := by
  rw [← hD.inner_eq, hF.inner_eq]

end Definitions

section ElementaryProperties

variable {E : Type*} [TopologicalSpace E]

theorem outerSetLimit_mono {C D : ℕ → Set E}
    (hCD : ∀ n, C n ⊆ D n) :
    outerSetLimit C ⊆ outerSetLimit D := by
  intro x hx V hV
  exact (hx V hV).mono fun n ⟨y, hyC, hyV⟩ ↦ ⟨y, hCD n hyC, hyV⟩

theorem innerSetLimit_mono {C D : ℕ → Set E}
    (hCD : ∀ n, C n ⊆ D n) :
    innerSetLimit C ⊆ innerSetLimit D := by
  intro x hx V hV
  exact (hx V hV).mono fun n ⟨y, hyC, hyV⟩ ↦ ⟨y, hCD n hyC, hyV⟩

@[simp]
theorem outerSetLimit_const (D : Set E) :
    outerSetLimit (fun _ : ℕ ↦ D) = closure D := by
  ext x
  constructor
  · intro hx
    exact mem_closure_iff_nhds.2 fun V hV ↦ by
      rcases (hx V hV).exists with ⟨n, y, hyD, hyV⟩
      exact ⟨y, hyV, hyD⟩
  · intro hx V hV
    have hhit : (D ∩ V).Nonempty := by
      rcases mem_closure_iff_nhds.1 hx V hV with ⟨y, hyV, hyD⟩
      exact ⟨y, hyD, hyV⟩
    exact Frequently.of_forall fun _ ↦ hhit

@[simp]
theorem innerSetLimit_const (D : Set E) :
    innerSetLimit (fun _ : ℕ ↦ D) = closure D := by
  ext x
  constructor
  · intro hx
    exact mem_closure_iff_nhds.2 fun V hV ↦ by
      rcases (hx V hV).exists with ⟨n, y, hyD, hyV⟩
      exact ⟨y, hyV, hyD⟩
  · intro hx V hV
    have hhit : (D ∩ V).Nonempty := by
      rcases mem_closure_iff_nhds.1 hx V hV with ⟨y, hyV, hyD⟩
      exact ⟨y, hyD, hyV⟩
    exact Eventually.of_forall fun _ ↦ hhit

theorem pkConverges_const (D : Set E) :
    PKConverges (fun _ : ℕ ↦ D) (closure D) := by
  exact ⟨innerSetLimit_const D, outerSetLimit_const D⟩

theorem pkConverges_const_of_isClosed {D : Set E} (hD : IsClosed D) :
    PKConverges (fun _ : ℕ ↦ D) D := by
  simpa [hD.closure_eq] using pkConverges_const D

@[simp]
theorem outerSetLimit_empty :
    outerSetLimit (fun _ : ℕ ↦ (∅ : Set E)) = ∅ := by
  simp only [outerSetLimit_const, closure_empty]

@[simp]
theorem innerSetLimit_empty :
    innerSetLimit (fun _ : ℕ ↦ (∅ : Set E)) = ∅ := by
  simp only [innerSetLimit_const, closure_empty]

@[simp]
theorem outerSetLimit_univ :
    outerSetLimit (fun _ : ℕ ↦ (Set.univ : Set E)) = Set.univ := by
  simp only [outerSetLimit_const, closure_univ]

@[simp]
theorem innerSetLimit_univ :
    innerSetLimit (fun _ : ℕ ↦ (Set.univ : Set E)) = Set.univ := by
  simp only [innerSetLimit_const, closure_univ]

end ElementaryProperties

section Closedness

variable {E : Type*} [TopologicalSpace E]

/-- The outer limit is closed, including when some or all sets are empty. -/
theorem isClosed_outerSetLimit (C : ℕ → Set E) :
    IsClosed (outerSetLimit C) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx V hV
  rcases mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hxU⟩
  rcases mem_closure_iff.1 hx U hUopen hxU with ⟨y, hyU, hyLim⟩
  exact (hyLim U (hUopen.mem_nhds hyU)).mono fun n ⟨z, hzC, hzU⟩ ↦
    ⟨z, hzC, hUV hzU⟩

/-- The inner limit is closed, including when some or all sets are empty. -/
theorem isClosed_innerSetLimit (C : ℕ → Set E) :
    IsClosed (innerSetLimit C) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx V hV
  rcases mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hxU⟩
  rcases mem_closure_iff.1 hx U hUopen hxU with ⟨y, hyU, hyLim⟩
  exact (hyLim U (hUopen.mem_nhds hyU)).mono fun n ⟨z, hzC, hzU⟩ ↦
    ⟨z, hzC, hUV hzU⟩

theorem PKConverges.isClosed {C : ℕ → Set E} {D : Set E}
    (h : PKConverges C D) : IsClosed D := by
  rw [← h.outer_eq]
  exact isClosed_outerSetLimit C

end Closedness

section ClosureInvariance

variable {E : Type*} [TopologicalSpace E]

private theorem open_inter_closure_nonempty_iff {U S : Set E} (hU : IsOpen U) :
    (closure S ∩ U).Nonempty ↔ (S ∩ U).Nonempty :=
  closure_inter_open_nonempty_iff hU

/-- Replacing every term by its closure does not change the outer limit. -/
theorem outerSetLimit_closure (C : ℕ → Set E) :
    outerSetLimit (fun n ↦ closure (C n)) = outerSetLimit C := by
  apply Set.Subset.antisymm
  · intro x hx V hV
    rcases mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hxU⟩
    have hfrequent := hx U (hUopen.mem_nhds hxU)
    exact hfrequent.mono fun n hn ↦ by
      have hn' : (closure (C n) ∩ U).Nonempty := hn
      rcases (open_inter_closure_nonempty_iff hUopen).1 hn' with ⟨y, hyC, hyU⟩
      exact ⟨y, hyC, hUV hyU⟩
  · exact outerSetLimit_mono fun n ↦ subset_closure

/-- Replacing every term by its closure does not change the inner limit. -/
theorem innerSetLimit_closure (C : ℕ → Set E) :
    innerSetLimit (fun n ↦ closure (C n)) = innerSetLimit C := by
  apply Set.Subset.antisymm
  · intro x hx V hV
    rcases mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hxU⟩
    have heventual := hx U (hUopen.mem_nhds hxU)
    exact heventual.mono fun n hn ↦ by
      have hn' : (closure (C n) ∩ U).Nonempty := hn
      rcases (open_inter_closure_nonempty_iff hUopen).1 hn' with ⟨y, hyC, hyU⟩
      exact ⟨y, hyC, hUV hyU⟩
  · exact innerSetLimit_mono fun n ↦ subset_closure

theorem pkConverges_closure_iff (C : ℕ → Set E) (D : Set E) :
    PKConverges (fun n ↦ closure (C n)) D ↔ PKConverges C D := by
  simp only [PKConverges, innerSetLimit_closure, outerSetLimit_closure]

end ClosureInvariance

end RW
