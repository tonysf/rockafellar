/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Feasible-Set Mappings

Example 5.8 studies the mapping that sends a parameter `w` to the feasible
set of the constraint system it indexes:

  `T(w) = {x ∈ X | fᵢ(x, w) ≤ 0 for i ∈ I₁, fᵢ(x, w) = 0 for i ∈ I₂}`

for `w` in a parameter set `W`, and `T(w) = ∅` otherwise.  The point of the
example is that outer semicontinuity of `T` is automatic: `gph T` is cut out
of the closed set `W × X` by inequalities and equations in continuous
functions, so it is closed, and 5.7(a) converts that into osc.

Two features of the printed statement are worth recording.  The functions
`fᵢ` are only assumed continuous *on* `X × W`, so the constraint sets are
merely relatively closed there; closedness of `W × X` is what upgrades them.
And when `W` itself is not closed the conclusion survives at interior points
of `W`, because outer semicontinuity at a point only sees a neighborhood of
that point and `W` may be replaced there by a closed neighborhood.
-/

import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Set Topology

namespace RW

section FeasibleSets

variable {D E ι : Type*}

/-- **Example 5.8**: the feasible-set mapping of a parameterized constraint
system.  Writing the parameter condition `w ∈ W` into the defining predicate
is what makes `T(w) = ∅` for `w ∉ W`. -/
def feasibleSet (X : Set E) (W : Set D) (I₁ I₂ : Set ι) (f : ι → E → D → ℝ) :
    D → Set E :=
  fun w ↦ {x | x ∈ X ∧ w ∈ W ∧ (∀ i ∈ I₁, f i x w ≤ 0) ∧
    ∀ i ∈ I₂, f i x w = 0}

@[simp]
theorem mem_feasibleSet {X : Set E} {W : Set D} {I₁ I₂ : Set ι}
    {f : ι → E → D → ℝ} {w : D} {x : E} :
    x ∈ feasibleSet X W I₁ I₂ f w ↔
      x ∈ X ∧ w ∈ W ∧ (∀ i ∈ I₁, f i x w ≤ 0) ∧ ∀ i ∈ I₂, f i x w = 0 :=
  Iff.rfl

/-- Off the parameter set the feasible set is empty. -/
theorem feasibleSet_eq_empty {X : Set E} {W : Set D} {I₁ I₂ : Set ι}
    {f : ι → E → D → ℝ} {w : D} (hw : w ∉ W) :
    feasibleSet X W I₁ I₂ f w = ∅ := by
  ext x
  simp [feasibleSet, hw]

/-- On the parameter set the feasible set is the constraint system of the
book. -/
theorem feasibleSet_of_mem {X : Set E} {W : Set D} {I₁ I₂ : Set ι}
    {f : ι → E → D → ℝ} {w : D} (hw : w ∈ W) :
    feasibleSet X W I₁ I₂ f w =
      {x ∈ X | (∀ i ∈ I₁, f i x w ≤ 0) ∧ ∀ i ∈ I₂, f i x w = 0} := by
  ext x
  simp [feasibleSet, hw]

/-- Shrinking the parameter set restricts the mapping to that set. -/
theorem feasibleSet_mono_param {X : Set E} {W W' : Set D} {I₁ I₂ : Set ι}
    {f : ι → E → D → ℝ} (hWW : W' ⊆ W) {w : D} (hw : w ∈ W') :
    feasibleSet X W' I₁ I₂ f w = feasibleSet X W I₁ I₂ f w := by
  ext x
  simp [feasibleSet, hw, hWW hw]

/-- **Example 5.8**, last clause: `dom T` consists of the parameters in `W`
for which the constraint system is consistent. -/
theorem svDom_feasibleSet (X : Set E) (W : Set D) (I₁ I₂ : Set ι)
    (f : ι → E → D → ℝ) :
    svDom (feasibleSet X W I₁ I₂ f) =
      {w ∈ W | ∃ x ∈ X, (∀ i ∈ I₁, f i x w ≤ 0) ∧ ∀ i ∈ I₂, f i x w = 0} := by
  ext w
  constructor
  · rintro ⟨x, hxX, hwW, h₁, h₂⟩
    exact ⟨hwW, x, hxX, h₁, h₂⟩
  · rintro ⟨hwW, x, hxX, h₁, h₂⟩
    exact ⟨x, hxX, hwW, h₁, h₂⟩

end FeasibleSets

section Closedness

variable {D E ι : Type*} [TopologicalSpace D] [TopologicalSpace E]
variable {X : Set E} {W : Set D} {I₁ I₂ : Set ι} {f : ι → E → D → ℝ}

/-- Transporting the book's continuity hypothesis on `X × W` to the graph
coordinates, which are ordered parameter-first. -/
private theorem continuousOn_swap
    {g : E × D → ℝ} (hg : ContinuousOn g (X ×ˢ W)) :
    ContinuousOn (fun p : D × E ↦ g (p.2, p.1)) (W ×ˢ X) :=
  hg.comp continuous_swap.continuousOn fun _ hp ↦ ⟨hp.2, hp.1⟩

/-- **Example 5.8**: when both the state set and the parameter set are
closed, the graph of the feasible-set mapping is closed. -/
theorem isClosed_svGraph_feasibleSet (hX : IsClosed X) (hW : IsClosed W)
    (h₁ : ∀ i ∈ I₁, ContinuousOn (fun p : E × D ↦ f i p.1 p.2) (X ×ˢ W))
    (h₂ : ∀ i ∈ I₂, ContinuousOn (fun p : E × D ↦ f i p.1 p.2) (X ×ˢ W)) :
    IsClosed (svGraph (feasibleSet X W I₁ I₂ f)) := by
  have hWX : IsClosed (W ×ˢ X) := hW.prod hX
  have key : svGraph (feasibleSet X W I₁ I₂ f) =
      (W ×ˢ X) ∩
        ((⋂ i ∈ I₁, (W ×ˢ X) ∩ (fun p : D × E ↦ f i p.2 p.1) ⁻¹' Iic 0) ∩
          ⋂ i ∈ I₂, (W ×ˢ X) ∩ (fun p : D × E ↦ f i p.2 p.1) ⁻¹' {0}) := by
    ext p
    simp only [svGraph, mem_setOf_eq, mem_feasibleSet, mem_inter_iff,
      mem_iInter, mem_prod, mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · rintro ⟨hxX, hwW, hi₁, hi₂⟩
      exact ⟨⟨hwW, hxX⟩, fun i hi ↦ ⟨⟨hwW, hxX⟩, hi₁ i hi⟩,
        fun i hi ↦ ⟨⟨hwW, hxX⟩, hi₂ i hi⟩⟩
    · rintro ⟨⟨hwW, hxX⟩, hi₁, hi₂⟩
      exact ⟨hxX, hwW, fun i hi ↦ (hi₁ i hi).2, fun i hi ↦ (hi₂ i hi).2⟩
  rw [key]
  refine hWX.inter (IsClosed.inter (isClosed_iInter fun i ↦ ?_)
    (isClosed_iInter fun i ↦ ?_))
  · exact isClosed_iInter fun hi ↦
      (continuousOn_swap (h₁ i hi)).preimage_isClosed_of_isClosed hWX
        isClosed_Iic
  · exact isClosed_iInter fun hi ↦
      (continuousOn_swap (h₂ i hi)).preimage_isClosed_of_isClosed hWX
        isClosed_singleton

/-- **Example 5.8**: if `W` is closed then `T` is outer semicontinuous. -/
theorem svOsc_feasibleSet (hX : IsClosed X) (hW : IsClosed W)
    (h₁ : ∀ i ∈ I₁, ContinuousOn (fun p : E × D ↦ f i p.1 p.2) (X ×ˢ W))
    (h₂ : ∀ i ∈ I₂, ContinuousOn (fun p : E × D ↦ f i p.1 p.2) (X ×ˢ W)) :
    SvOsc (feasibleSet X W I₁ I₂ f) :=
  isClosed_svGraph_iff_svOsc.1 (isClosed_svGraph_feasibleSet hX hW h₁ h₂)

/-- **Example 5.8**: even when `W` is not closed, `T` is outer semicontinuous
at every interior point of `W`.

Replacing `W` by a closed neighborhood of `w` inside it changes nothing on a
neighborhood of `w`, and outer semicontinuity at a point is a local property.
The closed neighborhood exists in any regular space, `IRᵈ` included. -/
theorem svOscAt_feasibleSet_of_mem_interior [RegularSpace D]
    (hX : IsClosed X) {w : D} (hw : w ∈ interior W)
    (h₁ : ∀ i ∈ I₁, ContinuousOn (fun p : E × D ↦ f i p.1 p.2) (X ×ˢ W))
    (h₂ : ∀ i ∈ I₂, ContinuousOn (fun p : E × D ↦ f i p.1 p.2) (X ×ˢ W)) :
    SvOscAt (feasibleSet X W I₁ I₂ f) w := by
  obtain ⟨N, hN, hNclosed, hNW⟩ :=
    exists_mem_nhds_isClosed_subset (mem_interior_iff_mem_nhds.1 hw)
  have hmono : ∀ i, ContinuousOn (fun p : E × D ↦ f i p.1 p.2) (X ×ˢ W) →
      ContinuousOn (fun p : E × D ↦ f i p.1 p.2) (X ×ˢ N) :=
    fun _ h ↦ h.mono (prod_mono_right hNW)
  have hosc := svOsc_feasibleSet (I₁ := I₁) (I₂ := I₂) (f := f) hX hNclosed
    (fun i hi ↦ hmono i (h₁ i hi)) fun i hi ↦ hmono i (h₂ i hi)
  refine (svOscAt_congr ?_).1 (hosc w)
  filter_upwards [hN] with w' hw'
  exact feasibleSet_mono_param hNW hw'

end Closedness

end RW
